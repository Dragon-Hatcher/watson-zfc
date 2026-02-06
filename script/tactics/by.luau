local state = require("./state")

local M = {}

function getTemplateInstantiations(tmps: Templates): {Template}
    local instantiations = {}
    while tmps._rule ~= "templates.none" do
        table.insert(instantiations, tmps.tmp)
        tmps = tmps.rest
    end
    return instantiations
end

function addTemplateToScope(scope: Scope, tmp: ThmTemplate): Scope
    for i, binding in tmp.holes do
        scope = scope:bindHole(binding, i - 1)
    end
    return scope
end

function M.handleBy(
    just: { _span: Span, thm: SpannedString, tmps: Templates },
    state: state.State
): state.State
    -- Lookup the theorem we are supposed to be applying
    local thm = Theorem:lookupByName(just.thm.str)
    if thm == nil then
        Diagnostic:new(
            "unknown theorem `" .. just.thm.str .. "`",
            just.thm.span:label("")
        )
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    -- Now collect the template instantiations
    local templates = thm.templates
    local instantiations = getTemplateInstantiations(just.tmps)

    -- The number of instantiations should match the number of templates
    if #templates ~= #instantiations then
        Diagnostic:new(
            "wrong number of template instantiations",
            just.tmps._span:label("expected " .. #templates .. ", found " .. #instantiations)
        )
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end 

    -- Resolve each instantiation
    local resolved = {}
    local resolveError = false
    for i, tmp in templates do 
        local tmpScope = addTemplateToScope(state.scope, tmp)
        local frag, diag = instantiations[i].frag:resolve(tmpScope, tmp.cat)
        if diag ~= nil then
            diag:withTacticInfo(state.info):report()
            resolveError = true
        elseif frag ~= nil then
            table.insert(resolved, frag)
        end
    end

    if resolveError then
        return state:error()
    end

    -- Check that we have all the hypotheses.
    local missingHyp = false
    for i, hyp in thm.hypotheses do
        local inst = hyp:instantiateTemplates(resolved)
        if not state.knowns:get(inst.formal) then
            Diagnostic:new(
                "missing hypothesis `" .. tostring(inst) .. "`",
                just.thm.span:label("while applying theorem `" .. thm.name .. "`")
            )
                :withTacticInfo(state.info)
                :report()
            missingHyp = true
        end
    end

    if missingHyp then
        return state:error()
    end

    -- Instantiate the conclusion to see what we actually proved
    local conclusion = thm.conclusion:instantiateTemplates(resolved)

    -- If the conclusion isn't the goal then this proof doesn't suffice.
    if conclusion.formal ~= state.goal.formal then
        Diagnostic:new(
            "theorem does not solve goal",
            just.thm.span:label("theorem shows `" .. tostring(conclusion) .. "` not `" .. tostring(state.goal) .. "`")
        )
            :withTacticInfo(state.info)
            :report()
        return state:error()
    end

    -- Now we can apply the theorem to our local state
    state.formal = state.formal:applyTheorem(thm, resolved)
    state.info = state.info:withDeduce(conclusion:fact())
    state.knowns:set(conclusion.formal:fact(), conclusion:fact())

    return state
end

return M