local state = require("./state")

local M = {}

function M.handleEmpty(
    tactic: { _span: Span },
    state: state.State
): state.State
    -- Check that the goal has been proven
    if not state.knowns:get(state.goal.formal:fact()) then
        Diagnostic:new("goal `" .. tostring(state.goal) .. "` unproven at end of proof")
            :withError("", tactic._span)
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    -- The goal has been proven so we are done
    return state
end

return M