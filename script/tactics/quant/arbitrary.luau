local dispatch = require("../dispatch")
local frag = require("../frag")
local state = require("../state")
local shared = require("../shared")

local M = {}

local arbitraryPattern = shared.arbitraryPattern

function M.handleArbitrary(
    tactic: { _span: Span, kw: SpannedString, var: SpannedString, st: UnResFrag?, next: Tactic },
    state: state.State
): state.State
    -- extract the property we are trying to prove from the goal
    local stateGoal = frag.reduceTop(state.goal):changeBinderNames({})
    local matches = stateGoal:match(shared.forallPattern:changeBinderNames({}))
    if matches == nil then
        Diagnostic:new("goal must be a forall statement", tactic.kw.span:label(""))
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    local prop = matches[0]
    local propHole = prop:instantiateVars({Frag:hole(shared.termCat, 0)})

    -- this is the variable we want to prove the goal about
    local binding = Binding:name(tactic.var.str, shared.termCat)
    local var = arbitraryPattern:instantiateHoles({prop})
    var = var:named(tactic.var.str)

    -- create a sub state with the new goal
    local goal = propHole:instantiateHoles({var})
    local subState = state:copy()
    subState.goal = goal
    subState.info = subState.info:withLet(binding):withGoal(goal)
    subState.scope = subState.scope:bindFrag(binding, var)

    if tactic.st ~= nil then
        -- do the assume logic: match goal as an implication
        local impMatches = frag.reduceTop(goal):match(shared.impPattern)
        if impMatches == nil then
            Diagnostic:new("goal after introducing variable must be an implication", tactic.st.span:label(""))
                :withTacticInfo(subState.info)
                :report()
            return state:error()
        end

        local goalAssumption = impMatches[0]
        local goalConclusion = impMatches[1]

        local parsedAssumption, diag = tactic.st:resolve(subState.scope)
        if diag ~= nil then diag:withTacticInfo(subState.info):report() end
        if parsedAssumption == nil then return state:error() end

        if goalAssumption.formal ~= parsedAssumption.formal then
            Diagnostic:new(
                "stated assumption `" .. tostring(parsedAssumption) .. "` doesn't match goal",
                tactic.st.span:label("")
            )
                :withTacticInfo(subState.info)
                :report()
            return state:error()
        end

        -- prove the conclusion under the assumption
        local subSubState = subState:copy()
        subSubState.formal = subSubState.formal:addAssumption(parsedAssumption)
        subSubState.knowns:set(parsedAssumption.formal:fact(), parsedAssumption:fact())
        subSubState.info = subSubState.info:withAssume(parsedAssumption):withGoal(goalConclusion)
        subSubState.goal = goalConclusion
        subSubState = dispatch.handleTactic(tactic.next, subSubState)

        -- unwind assume: pop assumption then deduction theorem
        subState.formal = subSubState.formal:popAssumption(goalConclusion)
        subState.formal = subState.formal:applyTheorem(shared.deductionThm, {parsedAssumption, goalConclusion})
        subState.knowns:set(goal.formal:fact(), goal:fact())
        subState.info = subState.info:withDeduce(goal:fact())
    else
        subState = dispatch.handleTactic(tactic.next, subState)
    end

    -- unwind arbitrary: forall.intro
    state.formal = subState.formal:applyTheorem(shared.forallIntroThm, {propHole})
    state.info = state.info:withDeduce(state.goal:fact())
    state.knowns:set(state.goal.formal:fact(), state.goal:fact())

    return state
end

return M
