local dispatch = require("../dispatch")
local state = require("../state")
local shared = require("../shared")

local M = {}

-- Reads the obtain_vars grammar list into a flat Lua table.
-- Returns: {{ var: SpannedString, st: UnResFrag? }}
local function readObtainVars(list: ObtainVars): {{ var: SpannedString, st: UnResFrag? }}
    local result = {}
    while true do
        if list._rule == "obtain_vars.last" then
            table.insert(result, { var = list.var, st = list.st })
            break
        elseif list._rule == "obtain_vars.more" then
            table.insert(result, { var = list.var, st = nil })
            list = list.rest
        elseif list._rule == "obtain_vars.more_st" then
            table.insert(result, { var = list.var, st = list.st })
            list = list.rest
        end
    end
    return result
end

-- Recursively applies exists.elim for each variable in items[i..N],
-- splitting conjunctions when an intermediate variable has a st condition.
-- witnesses[j] holds the witness term for item j (populated as we recurse).
-- Returns the updated state after all variables have been obtained and
-- tactic.next has been proven.
local function applyExistsElimChain(
    items: {{ var: SpannedString, st: UnResFrag? }},
    bodySchematics: {Frag},
    i: number,
    nextTactic: Tactic,
    state: state.State,
    witnesses: {Frag}
): state.State
    local item = items[i]

    -- bodySchematics[i] was built with De Bruijn indices for all variables:
    --   var(0) = v_i, var(1) = v_{i-1}, ..., var(i-1) = v_1
    -- Substitute outer witnesses so that only var(0) (= v_i) remains free.
    local body = bodySchematics[i]
    if i > 1 then
        -- subs[1] = var(0) keeps v_i as a placeholder; subs[k+1] = witnesses[i-k]
        local subs = {Frag:var(shared.termCat, 0)}
        for j = i - 1, 1, -1 do
            table.insert(subs, witnesses[j])
        end
        body = body:instantiateVars(subs)
    end

    -- Create the witness term for this variable (body now has only var(0) free)
    local binding = Binding:name(item.var.str, shared.termCat)
    local witness = shared.witnessPattern:instantiateHoles({body, state.goal})
    witness = witness:named(item.var.str)
    witnesses[i] = witness

    -- Bind the witness into scope so subsequent conditions can reference this variable
    state.scope = state.scope:bindFrag(binding, witness)

    -- Concretize the body by substituting the witness for var(0)
    local assumption = body:instantiateVars({witness})

    -- Enter the assumption context
    local subState = state:copy()
    subState.formal = subState.formal:addAssumption(assumption)
    subState.info = subState.info:withLet(binding)
    if i == #items then
        -- the body isn't more existentials but the actual final fact.
        subState.info = subState.info:withDeduce(assumption:fact())
        subState.knowns:set(assumption.formal:fact(), assumption:fact())
    end

    -- If this is an intermediate item with a st condition, the assumption is a
    -- conjunction: cI ∧ ∃v_{i+1}, ...  Split it so both halves are in knowns.
    if item.st ~= nil and i < #items then
        local andMatches = assumption:match(shared.andPattern)
        assert(andMatches ~= nil)
        local condConcrete = andMatches[0]
        local existsNextConcrete = andMatches[1]

        subState.knowns:set(condConcrete.formal:fact(), condConcrete:fact())
        subState.info = subState.info:withDeduce(condConcrete:fact())
        subState.formal = subState.formal:applyTheorem(
            shared.andElimLeftThm, {condConcrete, existsNextConcrete})
        subState.formal = subState.formal:applyTheorem(
            shared.andElimRightThm, {condConcrete, existsNextConcrete})
    end

    -- Recurse or execute the continuation
    if i == #items then
        subState = dispatch.handleTactic(nextTactic, subState)
    else
        subState = applyExistsElimChain(items, bodySchematics, i + 1, nextTactic, subState, witnesses)
    end

    -- Unwind: pop assumption, apply deduction theorem, then exists.elim
    state.formal = subState.formal:popAssumption(state.goal)
    state.formal = state.formal:applyTheorem(shared.deductionThm, {assumption, state.goal})
    local bodyHole = body:instantiateVars({Frag:hole(shared.termCat, 0)})
    state.formal = state.formal:applyTheorem(shared.existsElimThm, {bodyHole, state.goal})
    state.knowns:set(state.goal.formal:fact(), state.goal:fact())
    state.info = state.info:withDeduce(state.goal:fact())

    return state
end

function M.handleObtain(
    tactic: { _span: Span, list: any, just: Justification, next: Tactic },
    state: state.State
): state.State
    local items = readObtainVars(tactic.list)
    local N = #items

    -- Phase 1: Resolve schematic conditions for each item.
    -- For item i (1-indexed), the scope has v_j -> var(i-j) for j=1..i,
    -- so v_i -> var(0) (the binder for ∃v_i) and outer variables at higher indices.
    local condSchematics = {}
    for i = 1, N do
        local item = items[i]
        if item.st ~= nil then
            local itemScope = state.scope
            for j = 1, i do
                itemScope = itemScope:bindFrag(
                    Binding:name(items[j].var.str, shared.termCat),
                    Frag:var(shared.termCat, i - j)
                )
            end
            local cond, diag = item.st:resolve(itemScope)
            if diag ~= nil then diag:withTacticInfo(state.info):report() end
            if cond == nil then return state:error() end
            condSchematics[i] = cond
        end
    end

    -- Phase 2: Build nested existential bodies right-to-left.
    -- bodySchematics[i] = the body inside ∃v_i (has var(0) = v_i, higher indices = outer vars).
    local bodySchematics = {}
    bodySchematics[N] = condSchematics[N]  -- last item: body is just its condition

    for i = N - 1, 1, -1 do
        local existsNext = shared.existsPattern:instantiateHoles({bodySchematics[i + 1]})
        if condSchematics[i] ~= nil then
            bodySchematics[i] = shared.andPattern:instantiateHoles({condSchematics[i], existsNext})
        else
            bodySchematics[i] = existsNext
        end
    end

    -- Phase 3: Prove the outermost existential using the provided justification.
    local outerExists = shared.existsPattern:instantiateHoles({bodySchematics[1]})
    local subState = state:copy()
    subState.goal = outerExists
    subState.info = subState.info:withGoal(outerExists)
    subState = dispatch.handleJustification(tactic.just, subState)
    state.formal = subState.formal

    -- Phase 4: Apply exists.elim for each variable in sequence.
    return applyExistsElimChain(items, bodySchematics, 1, tactic.next, state, {})
end

return M
