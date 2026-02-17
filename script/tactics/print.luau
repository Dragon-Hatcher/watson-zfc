local dispatch = require("./dispatch")
local state = require("./state")

local M = {}

function M.handleEmpty(
    tactic: { _span: Span, frag: UnResFrag, next: Tactic },
    state: state.State
): state.State
    local res = tactic.frag:resolve(state.scope)
    if res ~= nil then 
        local cur = res
        local prev = nil
        while prev ~= cur do
            if cur.source and cur.source.isLuaApi then
                log(tostring(cur), "(lua)")
            elseif cur.source and cur.source.isDefinitionCmd then
                log(tostring(cur), `(def {cur.source.isDefinitionCmd})`)
            elseif cur.source and cur.source.isSyntaxCmd then
                log(tostring(cur), `(syntax {cur.source.isSyntaxCmd})`)
            elseif cur.source == nil then
                log(tostring(cur), `(formal)`)
            else
                log(tostring(cur), "(other)")
            end
            prev = cur
            cur = cur:reduce()
        end
        log()
    else
        log("Doesn't parse")
    end

    return dispatch.handleTactic(tactic.next, state)
end

return M