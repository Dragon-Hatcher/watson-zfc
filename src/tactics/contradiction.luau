local frag = require("./frag")
local state = require("./state")

local M = {}

local mpThm = Theorem:lookupByName("modus_ponens")
assert(mpThm ~= nil)

local explosionThm = Theorem:lookupByName("explosion")
assert(explosionThm ~= nil)

local falsum = frag.makePattern(
    "⊥", FormalCat:sentence(), 
    "tactic.contradiction", 
    {}
)

local notPattern = frag.makePattern(
    "¬p", FormalCat:sentence(), 
    "tactic.contradiction",
    {{name = "p", cat = FormalCat:sentence()}}
)

function M.handleContradiction(
    tactic: { _span: Span },
    state: state.State
): state.State
    -- For each fact we know, check if we have not that fact
    for fact, _ in state.knowns :: {[Fact]: boolean} do
        -- Ignore fact with assumptions
        if fact.assumption ~= nil then continue end

        -- Construct the negation of this fact
        local notConclusion = notPattern:instantiateHoles({fact.conclusion})

        if state.knowns:get(notConclusion.formal:fact()) then
            -- We have found the contradiction. Use modus ponens to
            -- derive falsum and then the explosion theorem to derive the goal.
            state.formal = state.formal
                :applyTheorem(mpThm, {fact.conclusion, falsum})
                :applyTheorem(explosionThm, {state.goal})
            state.info = state.info:withDeduce(state.goal:fact())
            state.knowns:set(falsum.formal:fact(), true)
            return state
        end
    end

    -- We failed to find the contradiction, so report an error
    Diagnostic:new("could not find contradiction")
        :withError("", tactic._span)
        :withTacticInfo(state.info)
        :report()
    return state:error()
end

return M