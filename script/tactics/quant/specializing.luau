local state = require("../state")
local shared = require("../shared")

local M = {}

function M.handleSpecializing(
    just: { _span: Span, forall: UnResFrag },
    state: state.State
): state.State
    -- parse the forall statement
    local forall, diag = just.forall:resolve(state.scope)
    if diag ~= nil then diag:withTacticInfo(state.info):report() end
    if forall == nil then return state:error() end

    -- extract the property we are trying to prove from the forall
    local matches = forall.formal:match(shared.forallPattern.formal)
    if matches == nil then
        Diagnostic:new("specialization must be a forall statement", just.forall.span:label(""))
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    local prop = matches[0]
    local propHole = prop:instantiateVars({Frag:hole(shared.termCat, 0)})

    -- now we try to match the goal against the property
    matches = state.goal.formal:match(propHole.formal)
    if matches == nil then
        Diagnostic:new("couldn't specialize forall into goal", just.forall.span:label(""))
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end
    local term = matches[0]

    -- now the goal should follow by forall.elim
    state.formal = state.formal:applyTheorem(shared.forallElimThm, {propHole, term})
    state.knowns:set(state.goal.formal:fact(), state.goal:fact())
    state.info = state.info:withDeduce(state.goal:fact())

    return state
end

return M
