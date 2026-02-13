local dispatch = require("./dispatch")
local shared = require("./shared")
local state = require("./state")

local M = {}

function M.handleLetTactic(
    tactic: { _span: Span, name: SpannedString, frag: UnResFrag, next: Tactic },
    state: state.State
): state.State
    local f, d = tactic.frag:resolve(state.scope)
    if d ~= nil then d:withTacticInfo(state.info):report() end
    if f == nil then return state:error() end

    local newState = state:copy()
    local binding = Binding:name(tactic.name.str, shared.termCat)
    newState.info = newState.info:withLet(binding, f)
    newState.scope = newState.scope:bindFrag(binding, f)

    return dispatch.handleTactic(tactic.next, newState)
end

return M