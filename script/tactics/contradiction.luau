local state = require("./state")
local shared = require("./shared")

local M = {}

function M.handleContradiction(
    tactic: { _span: Span },
    state: state.State
): state.State
    -- For each fact we know, check if we have not that fact
    for fact, _ in state.knowns :: {[Fact]: boolean} do
        -- Ignore fact with assumptions
        if fact.assumption ~= nil then continue end

        -- Construct the negation of this fact
        local notConclusion = shared.notPattern:instantiateHoles({fact.conclusion})

        if state.knowns:get(notConclusion.formal:fact()) then
            -- We have found the contradiction. Use modus ponens to
            -- derive falsum and then the explosion theorem to derive the goal.
            state.formal = state.formal
                :applyTheorem(shared.mpThm, {fact.conclusion, shared.falsum})
                :applyTheorem(shared.explosionThm, {state.goal})
            state.info = state.info:withDeduce(state.goal:fact())
            state.knowns:set(shared.falsum.formal:fact(), shared.falsum:fact())
            return state
        end
    end

    -- We failed to find the contradiction, so report an error
    Diagnostic:new(
        "could not find contradiction",
        tactic._span:label("")
    )
        :withTacticInfo(state.info)
        :report()
    return state:error()
end

return M