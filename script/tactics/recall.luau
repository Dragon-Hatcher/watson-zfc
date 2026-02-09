local dispatch = require("./dispatch")
local state = require("./state")
local shared = require("./shared")

-- local quant = require("./quant")
-- local assume = require("./assume")

local M = {}

-- function M.formalRecall(formal: ProofState, goal: Frag, thm: Theorem): ProofState

--     -- Introduce arbitrary variables for each template param
--     local arbitraryCleanups = {}
--     local vars = {}
--     for template in thm.templates do
--         local arb = quant.formalArbitrary(formal, formalGoal)
--         formal = arb.formal
--         formalGoal = arb.goal
--         table.insert(arbitraryCleanups, arb.cleanup)
--         table.insert(vars, arb.var)
--     end

--     if #thm.hypotheses ~= 0 then
--         -- Extract all the hypotheses
--         local assump = assume.formalAssumeThen(formal, )

--     else
--         -- There are no hypotheses, so we can just conclude the theorem now.
--         formal = formal:applyTheorem(thm, vars)
--     end

--     -- Close the scopes of all the arbitrary variables
--     for i = #arbitraryCleanups, 1, -1 do
--         state.formal = quant.formalArbitraryCleanup(state.formal, arbitraryCleanups[i])
--     end

--     return formal
-- end

type RecallError =
    | { err: "non_term_template" }
    | { err: "parameterized_template" }
    | { err: "hyp_with_assumption" }

function M.handleRecall(thm: Theorem, state: state.State): (state.State, RecallError?)
    -- This is the first order statement of the theorem we are trying to
    -- recall.
    local recalledTheorem = shared.holePattern

    -- First add each template as a forall statement.
    local templateInst = {}
    for i = #thm.templates, 1, -1 do
        local template = thm.templates[i]

        -- Our logic is first order so we can't quantify over non-term templates.
        if template.cat ~= shared.termCat then
            return state:error(), { err = "non_term_template" }
        end
    
        -- Or templates with holes in them
        if #template.holes ~= 0 then
            return state:error(), { err = "parameterized_template" }
        end

         -- Try to extract the name from the binding, otherwise just use an index.
        local bindingNames = template.binding.names
        local name = #bindingNames > 0 and bindingNames[1] or `v{i}`

        recalledTheorem = shared.forallPattern
            :changeBinderNames({name})
            :instantiateHoles({recalledTheorem})

        local dbIdx = #thm.templates - i
        local var = Frag:var(shared.termCat, dbIdx):named(name)
        table.insert(templateInst, var)
    end

    local conclusion = thm.conclusion:instantiateTemplates(templateInst)

    -- Next add each of the hypotheses and conclusion
    if #thm.hypotheses ~= 0 then
        local hs = shared.holePattern
        for i, h in thm.hypotheses do
            if h.assumption ~= nil then
                return state:error(), { err = "hyp_with_assumption" }
            end

            local hConclusion = h.conclusion:instantiateTemplates(templateInst)

            if i == #thm.hypotheses then
                hs = hs:instantiateHoles({hConclusion})
            else
                local hAnd = shared.andPattern:instantiateHoles({hConclusion, shared.holePattern})
                hs = hs:instantiateHoles({hAnd})
            end
        end

        local hToC = shared.impPattern:instantiateHoles({hs, conclusion})
        recalledTheorem = recalledTheorem:instantiateHoles({hToC})
    else
        -- No hypotheses. Add the conclusion directly
        recalledTheorem = recalledTheorem:instantiateHoles({conclusion})
    end

    -- Now we can prove the theorem statement using the theorem.
    state.formal = state.formal:applyTodo(recalledTheorem)
    state.info = state.info:withDeduce(recalledTheorem:fact())
    state.knowns:set(recalledTheorem.formal:fact(), recalledTheorem:fact())

    return state, nil
end

function M.recallErrToDiag(err: RecallError, thmNameSpan: Span): Diagnostic
    if err.err == "non_term_template" then
        return Diagnostic:new("cannot recall theorem with non term templates", thmNameSpan:label(""))
    elseif err.err == "parameterized_template" then
        return Diagnostic:new("cannot recall theorem with parameterized templates", thmNameSpan:label(""))
    elseif err.err == "hyp_with_assumption" then
        return Diagnostic:new("cannot recall theorem with assumptions in hypotheses", thmNameSpan:label(""))
    else
        assert(false)
    end
end

function M.handleRecallTactic(
    tactic: { _span: Span, thm: SpannedString, next: Tactic },
    state: state.State
): state.State
    local thm = Theorem:lookupByName(tactic.thm.str)
    if thm == nil then
        Diagnostic:new("unknown theorem `" .. tactic.thm.str .. "`", tactic.thm.span:label(""))
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    local newState, err = M.handleRecall(thm, state)

    if err then
        M.recallErrToDiag(err, tactic.thm.span)
            :withTacticInfo(state.info)
            :report()
    end

    return dispatch.handleTactic(tactic.next, newState)
end

return M