local dispatch = require("../dispatch")
local frag = require("../frag")
local state = require("../state")
local shared = require("../shared")

local M = {}

local arbitraryPattern = shared.arbitraryPattern

function M.handleArbitrary(
    tactic: { _span: Span, kw: SpannedString, var: SpannedString, next: Tactic },
    state: state.State
): state.State
    -- extract the property we are trying to prove from the goal
    local stateGoal = frag.reduceTop(state.goal):changeBinderNames({})
    local matches = stateGoal:match(shared.forallPattern:changeBinderNames({}))
    if matches == nil then
        Diagnostic:new("goal must be a forall statement", tactic.kw.span:label(""))
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    local prop = matches[0]
    local propHole = prop:instantiateVars({Frag:hole(shared.termCat, 0)})

    -- this is the variable we want to prove the goal about
    local binding = Binding:name(tactic.var.str, shared.termCat)
    local var = arbitraryPattern:instantiateHoles({prop})
    var = var:named(tactic.var.str)

    -- create a sub state with the new goal
    local goal = propHole:instantiateHoles({var})
    local subState = state:copy()
    subState.goal = goal
    subState.info = subState.info
        :withLet(binding)
        :withGoal(goal)

    -- and add the variable to the scope
    subState.scope = subState.scope:bindFrag(binding, var)

    -- now prove the goal in the subState
    subState = dispatch.handleTactic(tactic.next, subState)

    -- now it we simply apply forall.intro to get the original goal
    state.formal = subState.formal:applyTheorem(shared.forallIntroThm, {propHole})
    state.info = state.info:withDeduce(state.goal:fact())
    state.knowns:set(state.goal.formal:fact(), state.goal:fact())

    return state
end

return M
