local dispatch = require("./dispatch")
local state = require("./state")

local M = {}

function M.handleThus(
    tactic: { goal: UnResFact, just: Justification, next: Tactic },
    state: state.State
): state.State
    -- Resolve the goal fact we are trying to prove.
    local goal, d1, d2 = tactic.goal:resolve(state.scope)
    if d1 ~= nil then d1:withTacticInfo(state.info):report() end
    if d2 ~= nil then d2:withTacticInfo(state.info):report() end
    if goal == nil then return state:error() end

    local subState = state:copy()
    subState.info = subState.info:withGoal(goal.conclusion)
    subState.goal = goal.conclusion

    -- Now if there is an assumption add it to the subproof.
    local a = goal.assumption
    if a ~= nil then
        subState.formal = subState.formal:addAssumption(a)
        subState.info = subState.info:withAssume(a)
        subState.knowns:set(a.formal:fact(), a:fact())
    end

    -- Resolve the subproof
    subState = dispatch.handleJustification(tactic.just, subState)

    -- If we added an assumption we need to remove it again.
    if a ~= nil then
        subState.formal = subState.formal:popAssumption(goal.conclusion)
    end

    -- The subproof proved our goal so we can transfer over the formal proof.
    state.formal = subState.formal
    state.info = state.info:withDeduce(goal)
    state.knowns:set(goal.formal, goal)

    return dispatch.handleTactic(tactic.next, state)
end

return M