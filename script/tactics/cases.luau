local dispatch = require("./dispatch")
local state = require("./state")
local shared = require("./shared")
local vampire = require("./vampire")

local M = {}

function readCaseList(case_list: CaseList): {{ sentence: UnResFrag, tactic: Tactic, span: Span }}
    local result = {}
    while true do
        local c = case_list.c
        table.insert(result, {
            sentence = c.sentence,
            tactic = c.tactic,
            span = c._span,
        })
        if case_list._rule == "case_list.many" then
            case_list = case_list.rest
        else
            break
        end
    end
    return result
end

function M.handleCases(
    tactic: { _span: Span, just: Justification, cases: CaseList },
    state: state.State
): state.State
    local rawCases = readCaseList(tactic.cases)

    -- Resolve all case sentences
    local cases: {{ resolved: Frag, tactic: Tactic, span: Span }} = {}
    for _, c in rawCases do
        local resolved, diag = c.sentence:resolve(state.scope)
        if diag ~= nil then diag:withTacticInfo(state.info):report() end
        if resolved == nil then return state:error() end
        table.insert(cases, { resolved = resolved, tactic = c.tactic, span = c.span })
    end

    if #cases == 0 then return state end

    -- Build the disjunction of all case sentences (right-associative)
    local disjunction = cases[#cases].resolved
    for i = #cases - 1, 1, -1 do
        disjunction = shared.orPattern:instantiateHoles({cases[i].resolved, disjunction})
    end

    -- Prove the disjunction using the justification, or Vampire if empty
    local disjState = state:copy()
    disjState.goal = disjunction
    disjState.info = disjState.info:withGoal(disjunction)
    if tactic.just._rule ~= "justification.empty" then
        disjState = dispatch.handleJustification(tactic.just, disjState)
    else
        local disjErr
        disjState, _, disjErr = vampire.handleVampire(disjState)
        if disjErr ~= nil then
            vampire.vampErrToDiag(disjErr, tactic._span)
                :withTacticInfo(state.info)
                :report()
            return state:error()
        end
    end
    state.formal = disjState.formal
    state.knowns:set(disjunction.formal:fact(), disjunction:fact())

    -- For each case, assume the case sentence and run the provided tactic to prove the goal.
    -- Then apply the deduction theorem to get case → goal.
    local goal = state.goal
    for _, c in cases do
        local subState = state:copy()
        subState.formal = subState.formal:addAssumption(c.resolved)
        subState.info = subState.info:withAssume(c.resolved):withGoal(goal)
        subState.goal = goal
        subState.knowns:set(c.resolved.formal:fact(), c.resolved:fact())

        subState = dispatch.handleTactic(c.tactic, subState)
        subState.formal = subState.formal:popAssumption(goal)

        local implication = shared.deductionThm.conclusion:instantiateTemplates({c.resolved, goal})
        state.formal = subState.formal:applyTheorem(shared.deductionThm, {c.resolved, goal})
        state.info = state.info:withDeduce(implication:fact())
        state.knowns:set(implication.formal:fact(), implication:fact())
    end

    -- Now use Vampire to prove the goal from the disjunction and all case implications
    local finalState, _, finalErr = vampire.handleVampire(state:copy())
    if finalErr ~= nil then
        vampire.vampErrToDiag(finalErr, tactic._span)
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    state.formal = finalState.formal
    state.info = state.info:withDeduce(goal:fact())
    state.knowns:set(goal.formal:fact(), goal:fact())

    return state
end

return M
