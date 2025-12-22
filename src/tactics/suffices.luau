local dispatch = require("./dispatch")
local state = require("./state")

local M = {}

function M.handleSuffices(
    tactic: { _span: Span, goal: UnResFrag, just: Justification, next: Tactic },
    state: state.State
): state.State
    -- Resolve the intermediate goal that suffices
    local newGoal, diag = tactic.goal:resolve(state.scope)
    if diag ~= nil then diag:withTacticInfo(state.info):report() end
    if newGoal == nil then return state:error() end

    -- Prove up to the intermediate goal
    local oldGoal = state.goal
    state.info = state.info:withGoal(newGoal)
    state.goal = newGoal
    state = dispatch.handleTactic(tactic.next, state)

    -- Prove from the intermediate goal to the original goal
    state.info = state.info:withGoal(oldGoal)
    state.goal = oldGoal
    return dispatch.handleJustification(tactic.just, state)
end

return M