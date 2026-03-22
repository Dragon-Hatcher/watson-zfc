local state = require("../state")
local shared = require("../shared")

local M = {}

function M.handleUsing(
    just: { _span: Span, kw: SpannedString, use: UnResFrag },
    state: state.State
): state.State
    -- extract the property we are trying to prove from the goal
    local matches = state.goal.formal:match(shared.existsPattern.formal)
    if matches == nil then
        Diagnostic:new("goal must be an exists statement", just.kw.span:label("")):report()
        return state:error()
    end

    local prop = matches[0]
    local propHole = prop:instantiateVars({Frag:hole(shared.termCat, 0)})

    local use, diag = just.use:resolve(state.scope)
    if diag ~= nil then diag:withTacticInfo(state.info):report() end
    if use == nil then return state:error() end

    -- check that we have actually proved the term has the prop
    local propOfUse = prop:instantiateVars({use})
    if not state.knowns:get(propOfUse.formal:fact()) then
        Diagnostic:new("missing proof that `" .. tostring(use) .. "` satisfies goal")
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    -- resolve the goal using exists.intro
    state.formal = state.formal:applyTheorem(shared.existsIntroThm, {propHole, use})
    state.info = state.info:withDeduce(state.goal:fact())
    state.knowns:set(state.goal.formal:fact(), state.goal:fact())

    return state
end

return M
