local dispatch = require("./dispatch")
local state = require("./state")

local M = {}

function M.handleHave(
    tactic: { _span: Span, f1: UnResFrag, f2: UnResFrag, next: Tactic },
    state: state.State
): state.State
    -- Resolve the two fragments
    local f1, d1 = tactic.f1:resolve(state.scope)
    local f2, d2 = tactic.f2:resolve(state.scope)
    if d1 ~= nil then d1:withTacticInfo(state.info):report() end
    if d2 ~= nil then d2:withTacticInfo(state.info):report() end
    if f1 == nil or f2 == nil then return state:error() end

    -- Check that the fragments are definitionally equivalent
    if f1.formal ~= f2.formal then
        Diagnostic:new(
            "`" .. tostring(f1) .. "` is not definitionally equal to `" .. tostring(f2) .. "`",
            tactic.f1.span:label(""),
            tactic.f2.span:label("")
        )
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    -- Check that we actually know this fact
    if not state.knowns:get(f2.formal:fact()) then
        Diagnostic:new(
            "`" .. tostring(f2) .. "` isn't already known",
            tactic.f2.span:label("")
        )
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    state.info = state.info:withDeduce(f1:fact())
    state.knowns:set(f1.formal:fact(), true)
    return dispatch.handleTactic(tactic.next, state)
end

return M