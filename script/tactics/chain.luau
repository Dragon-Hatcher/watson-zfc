local dispatch = require("./dispatch")
local state = require("./state")
local shared = require("./shared")

local M = {}

local eqTransThm = Theorem:lookupByName("eq.trans")
assert(eqTransThm ~= nil)

function readChainList(list: ChainList): {{ term: UnResFrag, just: Justification, span: Span }}
    local result = {}
    while true do
        table.insert(result, {
            term = list.term,
            just = list.just,
            span = list._span,
        })
        if list._rule == "chain_list.many" then
            list = list.rest
        else
            break
        end
    end
    return result
end

function M.handleChain(
    tactic: { _span: Span, term: UnResFrag, list: ChainList },
    state: state.State
): state.State
    local steps = readChainList(tactic.list)

    -- Resolve the starting term
    local startTerm, startDiag = tactic.term:resolve(state.scope)
    if startDiag ~= nil then startDiag:withTacticInfo(state.info):report() end
    if startTerm == nil then return state:error() end

    -- Resolve all terms in the chain steps
    local resolvedSteps: {{ term: Frag, just: Justification, span: Span }} = {}
    for _, step in steps do
        local resolved, diag = step.term:resolve(state.scope)
        if diag ~= nil then diag:withTacticInfo(state.info):report() end
        if resolved == nil then return state:error() end
        table.insert(resolvedSteps, { term = resolved, just = step.just, span = step.span })
    end

    -- For each consecutive pair (prev, next), prove prev = next using the justification
    local prev = startTerm
    for _, step in resolvedSteps do
        local eqGoal = shared.eqPattern:instantiateHoles({prev, step.term})

        local subState = state:copy()
        subState.goal = eqGoal
        subState.info = subState.info:withGoal(eqGoal)
        subState = dispatch.handleJustification(step.just, subState)

        state.formal = subState.formal
        state.info = state.info:withDeduce(eqGoal:fact())
        state.knowns:set(eqGoal.formal:fact(), eqGoal:fact())

        prev = step.term
    end

    -- Chain all the equalities together using eq.trans.
    -- After iteration i (1-based), state.formal contains a proof of startTerm = resolvedSteps[i].term.
    -- We use: startTerm = resolvedSteps[i-1].term (from previous) and resolvedSteps[i-1].term = resolvedSteps[i].term (from step i).
    for i = 2, #resolvedSteps do
        local middle = resolvedSteps[i - 1].term
        local nextRight = resolvedSteps[i].term
        state.formal = state.formal:applyTheorem(eqTransThm, {startTerm, middle, nextRight})
    end

    -- Add the overall goal to the output state.
    local overallGoal = shared.eqPattern:instantiateHoles({startTerm, resolvedSteps[#resolvedSteps].term})
    state.info = state.info:withDeduce(overallGoal:fact())
    state.knowns:set(overallGoal.formal:fact(), overallGoal:fact())
    return state
end

return M
