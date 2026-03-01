local dispatch = require("./dispatch")
local state = require("./state")
local shared = require("./shared")
local vampire = require("./vampire")

local M = {}

function vampErrToDiag(err: vampire.VampError, span: Span): Diagnostic
    if err.err == "couldnt_convert_frag" then
        return Diagnostic:new(`Unable to convert \`{err.frag}\` to Vampire`, span:label(""))
    elseif err.err == "unprovable" then
        return Diagnostic:new("Vampire proved there is no contradiction", span:label(""))
    elseif err.err == "could_not_find_proof" then
        return Diagnostic:new("Vampire was unable to find a contradiction", span:label(""))
    else
        assert(false)
    end
end

function proveFromFalsum(falseState: state.State, originalState: state.State): state.State
    -- Otherwise apply explosion to derive the original goal from ⊥.
    originalState.formal = falseState.formal:applyTheorem(shared.explosionThm, {originalState.goal})
    originalState.info = originalState.info:withDeduce(originalState.goal:fact())
    originalState.knowns:set(originalState.goal.formal:fact(), originalState.goal:fact())
    return originalState
end

function M.handleContradiction(
    tactic: { _span: Span, just: Justification },
    state: state.State
): state.State
    -- If a justification is provided, use it to prove ⊥ directly.
    if tactic.just._rule ~= "justification.empty" then
        local subState = state:copy()
        subState.goal = shared.falsum
        subState.info = subState.info:withGoal(shared.falsum)
        subState = dispatch.handleJustification(tactic.just, subState)
        return proveFromFalsum(subState, state)
    end

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

    -- We didn't find a contradiction, so let's try having vampire find one.
    local state2 = state:copy()
    state2.goal = shared.falsum;

    local state3, _vInfo, vErr = vampire.handleVampire(state2)
    if vErr ~= nil then
        vampErrToDiag(vErr, tactic._span)
            :withTacticInfo(state.info)
            :report()
    end

    return state3
end

return M