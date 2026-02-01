local dispatch = require("./dispatch")
local state = require("./state")
local shared = require("./shared")

local M = {}

function M.handleAssumeThen(
    tactic: { _span: Span, assumption: UnResFrag, conclusion: UnResFrag, just: Justification, next: Tactic },
    state: state.State
): state.State
    -- Resolve the assumption and the conclusion
    local assumption, d1 = tactic.assumption:resolve(state.scope)
    local conclusion, d2 = tactic.conclusion:resolve(state.scope)
    if d1 ~= nil then d1:withTacticInfo(state.info):report() end
    if d2 ~= nil then d2:withTacticInfo(state.info):report() end
    if assumption == nil or conclusion == nil then return state:error() end

    -- Create a subState whose goal is the conclusion and knowns the assumption
    local subState = state:copy()
    subState.formal = subState.formal:addAssumption(assumption)
    subState.info = subState.info:withAssume(assumption):withGoal(conclusion)
    subState.goal = conclusion
    subState.knowns:set(assumption.formal:fact(), true)

    -- Use the assumption to prove the conclusion
    subState = dispatch.handleJustification(tactic.just, subState)
    subState.formal = subState.formal:popAssumption(conclusion)

    -- We now know assumption |- conclusion. Use the deduction axiom to convert
    -- that to assumption → conclusion
    local implication = shared.deductionThm.conclusion:instantiateTemplates({assumption, conclusion})
    state.formal = subState.formal:applyTheorem(shared.deductionThm, {assumption, conclusion})
    state.info = state.info:withDeduce(implication:fact())
    state.knowns:set(implication.formal:fact(), true)

    return dispatch.handleTactic(tactic.next, state)
end

function M.handleAssume(
    tactic: { _span: Span, kw: SpannedString, assumption: UnResFrag, next: Tactic },
    state: state.State
): state.State
    -- match the goal as an implication
    local matches = state.goal:match(shared.impPattern)
    if matches == nil then
        Diagnostic:new("goal must be an implication", tactic.kw.span:label(""))
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    local goalAssumption = matches[0]
    local goalConclusion = matches[1]

    -- check that the assumption the user made matches the goal
    local parsedAssumption, diag = tactic.assumption:resolve(state.scope)
    if diag ~= nil then diag:withTacticInfo(state.info):report() end
    if parsedAssumption == nil then return state:error() end

    if goalAssumption.formal ~= parsedAssumption.formal then
        Diagnostic:new(
            "stated assumption `" .. tostring(parsedAssumption) .. "` doesn't match goal",
            tactic.assumption.span:label("")
        )
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    -- now we finish the proof
    local subState = state:copy()
    subState.formal = subState.formal:addAssumption(parsedAssumption)
    subState.knowns:set(parsedAssumption.formal:fact(), true)
    subState.info = subState.info:withAssume(parsedAssumption):withGoal(goalConclusion)
    subState.goal = goalConclusion

    -- hand off to the continuation tactic
    subState = dispatch.handleTactic(tactic.next, subState)

    -- now we have assumption |- conclusion
    state.formal = subState.formal:popAssumption(goalConclusion)

    -- convert that to an implication which was the original goal
    state.formal = state.formal:applyTheorem(shared.deductionThm, {parsedAssumption, goalConclusion})
    state.knowns:set(state.goal.formal:fact(), true)
    state.info = state.info:withDeduce(state.goal:fact())

    return state
end

function M.handleAssumeContra(
    tactic: { _span: Span, assumption: UnResFrag, next: Tactic },
    state: state.State
): state.State
    -- Resolve the assumption
    local assumption, diag = tactic.assumption:resolve(state.scope)
    if diag ~= nil then diag:withTacticInfo(state.info):report() end
    if assumption == nil then return state:error() end

    -- Set up a subState with the assumption and the goal of a contradiction
    local subState = state:copy()
    subState.formal = subState.formal:addAssumption(assumption)
    subState.info = subState.info:withAssume(assumption):withGoal(shared.falsum)
    subState.knowns:set(assumption.formal:fact(), true)
    subState.goal = shared.falsum

    -- Use the subproof to derive a contradiction from the assumption
    subState = dispatch.handleTactic(tactic.next, subState)
    subState.formal = subState.formal:popAssumption(shared.falsum)

    -- We now know that assumption |- ⊥ and we want to use that to solve our
    -- original goal. First we convert assumption |- ⊥ to assumption → ⊥, 
    -- aka ¬assumption
    subState.formal = subState.formal:applyTheorem(shared.deductionThm, {assumption, shared.falsum})

    -- There are two possibilities:
    -- 1) Either the goal is exactly ¬assumption and we are done.
    -- 2) The assumption is ¬goal so we have proved ¬¬goal and need to apply
    --    not_not.elim
    local notAssumption = shared.notPattern:instantiateHoles({assumption})
    local notGoal = shared.notPattern:instantiateHoles({state.goal})
    if state.goal.formal == notAssumption.formal then
        -- case 1
        state.formal = subState.formal
        state.info = state.info:withDeduce(notAssumption:fact())
        state.knowns:set(notAssumption.formal:fact(), true)
        return state
    elseif notGoal.formal == assumption.formal then
        -- case 2
        state.formal = subState.formal:applyTheorem(shared.notNotElimThm, {state.goal})
        state.info = state.info:withDeduce(state.goal:fact())
        state.knowns:set(state.goal.formal:fact(), true)
        return state
    else
        -- the assumption isn't related to the goal
        Diagnostic:new(
            "assumption being false does not prove goal",
            tactic.assumption.span:label("")        
        )
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end
end

return M