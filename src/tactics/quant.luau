local frag = require("./frag")
local dispatch = require("./dispatch")
local state = require("./state")

local M = {}

local sentenceCat = FormalCat:sentence()
local termCat = FormalCat:get("term")
assert(termCat ~= nil)

local deductionThm = Theorem:lookupByName("deduction")
assert(deductionThm ~= nil)

local existsElimThm = Theorem:lookupByName("exists.elim")
assert(existsElimThm ~= nil)

local existsIntroThm = Theorem:lookupByName("exists.intro")
assert(existsIntroThm ~= nil)

local forallIntroThm = Theorem:lookupByName("forall.intro")
assert(forallIntroThm ~= nil)

local forallElimThm = Theorem:lookupByName("forall.elim")
assert(forallElimThm ~= nil)

local existsPattern = frag.makePattern(
    "∃x, p", sentenceCat, 
    "tactic.obtain",
    {{name = "p", cat = sentenceCat}}
)

local forallPattern = frag.makePattern(
    "∀x, p", sentenceCat, 
    "tactic.obtain",
    {{name = "p", cat = sentenceCat}}
)

local witnessPattern = frag.makePattern(
    "∃ᵉ x, p ⊢ q", termCat,
    "tactic.obtain",
    {
        {name = "p", cat = sentenceCat},
        {name = "q", cat = sentenceCat}
    }
)

function M.handleObtain(
    tactic: { _span: Span, var: SpannedString, st: UnResFrag, just: Justification, next: Tactic },
    state: state.State
): state.State
    -- first we are going to parse the such that with the given name
    local binding = Binding:name(tactic.var.str, termCat)
    local stTerm = Frag:var(termCat, 0) -- the first variable
    local stScope = state.scope:bindFrag(binding, stTerm)

    local st, diag = tactic.st:resolve(stScope)
    if diag ~= nil then diag:withTacticInfo(state.info) end
    if st == nil then return state:error() end

    -- this is the existential we expect to exist to justify obtaining
    -- the new variable
    local existential = existsPattern:instantiateHoles({st})

    -- apply the justification to conclude the existential
    local subState = state:copy()
    subState.goal = existential
    subState.info = subState.info:withGoal(existential)
    subState = dispatch.handleJustification(tactic.just, subState)

    -- Add the existential to the current state
    state.formal = subState.formal

    -- now we construct the witness for the existential. the exists.elim
    -- axiom allows us to reason as if this witness had the desired property.
    local witness = witnessPattern:instantiateHoles({st, state.goal})

    -- bind the witness to the given variable name
    state.scope = state.scope:bindFrag(binding, witness)

    -- now we are going to assume the witness has the property
    local assumption = st:instantiateVars({witness})
    subState = state:copy()
    subState.knowns:set(assumption.formal:fact(), true)
    -- for the info call it a deduction not an assumption because that more
    -- closely matches what it is. We aren't really assuming anything; we know
    -- that the witness exists.
    subState.info = subState.info:withDeduce(assumption:fact())
    subState.formal = subState.formal:addAssumption(assumption)

    -- prove the goal using this assumption
    subState = dispatch.handleTactic(tactic.next, subState)

    -- the assumption proved the goal
    state.formal = subState.formal:popAssumption(state.goal)

    -- convert that to an implication
    state.formal = state.formal:applyTheorem(deductionThm, {assumption, state.goal})

    -- and now we get the goal by exists.elim
    local stHole = st:instantiateVars({Frag:hole(termCat, 0)})
    state.formal = state.formal:applyTheorem(existsElimThm, {stHole, state.goal})
    state.knowns:set(state.goal.formal:fact(), true)
    state.info = state.info:withDeduce(state.goal:fact())

    return state
end

local arbitraryPattern = frag.makePattern(
    "∃ᵉx, ¬p ⊢ ⊥", termCat,
    "tactic.obtain",
    {{name = "p", cat = sentenceCat}}
)

function M.handleArbitrary(
    tactic: { _span: Span, kw: SpannedString, var: SpannedString, next: Tactic },
    state: state.State
): state.State
    -- extract the property we are trying to prove from the goal
    local matches = state.goal:match(forallPattern)
    if matches == nil then
        Diagnostic:new("goal must be a forall statement", tactic.kw.span:label("")):report()
        return state:error()
    end

    local prop = matches[0]
    local propHole = prop:instantiateVars({Frag:hole(termCat, 0)})

    -- this is the variable we want to prove the goal about
    local binding = Binding:name(tactic.var.str, termCat)
    local var = arbitraryPattern:instantiateHoles({prop})

    -- create a sub state with the new goal
    local goal = propHole:instantiateHoles({var})
    local subState = state:copy()
    subState.goal = goal
    subState.info = subState.info:withGoal(goal)

    -- and add the variable to the scope
    subState.scope = subState.scope:bindFrag(binding, var)

    -- now prove the goal in the subState
    subState = dispatch.handleTactic(tactic.next, subState)

    -- now it we simply apply forall.intro to get the original goal
    state.formal = subState.formal:applyTheorem(forallIntroThm, {propHole})
    state.info = state.info:withDeduce(state.goal:fact())
    state.knowns:set(state.goal.formal:fact(), true)

    return state
end

function M.handleUsing(
    just: { _span: Span, kw: SpannedString, use: UnResFrag },
    state: state.State
): state.State
    -- extract the property we are trying to prove from the goal
    local matches = state.goal:match(existsPattern)
    if matches == nil then
        Diagnostic:new("goal must be an exists statement", just.kw.span:label("")):report()
        return state:error()
    end

    local prop = matches[0]
    local propHole = prop:instantiateVars({Frag:hole(termCat, 0)})

    local use, diag = just.use:resolve(state.scope)
    if diag ~= nil then diag:withTacticInfo(state.info):report() end
    if use == nil then return state:error() end

    -- check that we have actually proved the term has the prop
    local propOfUse = prop:instantiateVars({use})
    if not state.knowns:get(propOfUse.formal:fact()) then
        Diagnostic:new("missing proof that `" .. tostring(use) .. "` satisfies goal")
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    -- resolve the goal using exists.intro
    state.formal = state.formal:applyTheorem(existsIntroThm, {propHole, use})
    state.info = state.info:withDeduce(state.goal:fact())
    state.knowns:set(state.goal.formal:fact(), true)

    return state
end

function M.handleSpecializing(
    just: { _span: Span, forall: UnResFrag },
    state: state.State
): state.State
    -- parse the forall statement
    local forall, diag = just.forall:resolve(state.scope)
    if diag ~= nil then diag:withTacticInfo(state.info):report() end
    if forall == nil then return state:error() end

    -- extract the property we are trying to prove from the forall
    local matches = forall:match(forallPattern)
    if matches == nil then
        Diagnostic:new("specialization must be a forall statement", just.forall.span:label(""))
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    local prop = matches[0]
    local propHole = prop:instantiateVars({Frag:hole(termCat, 0)})

    -- now we try to match the goal against the property
    matches = state.goal:match(propHole)
    if matches == nil then
        Diagnostic:new("couldn't specialize forall into goal", just.forall.span:label(""))            
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end
    local term = matches[0]

    -- now the goal should follow by forall.elim
    state.formal = state.formal:applyTheorem(forallElimThm, {propHole, term})
    state.knowns:set(state.goal.formal:fact(), true)
    state.info = state.info:withDeduce(state.goal:fact())

    return state
end


return M