local dispatch = require("./dispatch")
local state = require("./state")

local M = {}

function M.handleDone(
    tactic: { _span: Span, just: Justification, next: Tactic },
    state: state.State
): state.State
    return dispatch.handleJustification(tactic.just, state)
end

return M