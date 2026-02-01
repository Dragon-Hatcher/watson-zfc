local dispatch = require("./dispatch")
local state = require("./state")

local M = {}

function M.handleEmpty(
    tactic: { _span: Span, frag: UnResFrag, next: Tactic },
    state: state.State
): state.State
    local res = tactic.frag:resolve(state.scope)
    if res ~= nil then 
        log(`Normal: {res}`) 
        log(`Formal: {res.formal}`) 
    else
        log("Doesn't parse")
    end

    return dispatch.handleTactic(tactic.next, state)
end

return M