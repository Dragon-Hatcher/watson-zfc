local dispatch = require("./dispatch")
local state = require("./state")
local shared = require("./shared")

local M = {}

function M.handleRecall(
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

    -- This is the first order statement of the theorem we are trying to
    -- recall.
    local recalledTheorem = shared.holePattern

    -- First add each template as a forall statement.
    local templateInst = {}
    for i = #thm.templates, 1, -1 do
        local template = thm.templates[i]

        -- Our logic is first order so we can't quantify over non-term templates.
        if template.cat ~= shared.termCat then
            Diagnostic:new("cannot recall theorem with non term templates", tactic.thm.span:label(""))
                :withTacticInfo(state.info)
                :report()
            return state:error()
        end
    
        -- Or templates with holes in them
        if #template.holes ~= 0 then
            Diagnostic:new("cannot recall theorem with parameterized templates", tactic.thm.span:label(""))
                :withTacticInfo(state.info)
                :report()
            return state:error()
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
                Diagnostic:new("cannot recall theorem with assumptions in hypotheses", tactic.thm.span:label(""))
                    :withTacticInfo(state.info)
                    :report()
                return state:error()
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
    state.info = state.info:withDeduce(recalledTheorem:fact())
    state.knowns:set(recalledTheorem.formal:fact(), true)

    -- TODO: actually formally prove the goal.
    state.formal = state.formal:applyTodo(recalledTheorem)

    return dispatch.handleTactic(tactic.next, state)
end

return M