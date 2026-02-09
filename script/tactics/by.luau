local recall = require("./recall")
local state = require("./state")
local vampire = require("./vampire")

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

type ByError = 
    | { err: "missing_hyp", hyp: Fact }
    | { err: "wrong_conclusion", conclusion: Frag }

function M.handleBy(thm: Theorem, templates: {Frag}, state: state.State): (state.State, {ByError})
    local errors: {ByError} = {}

    -- Check that we have all the hypotheses.
    for i, hyp in thm.hypotheses do
        local inst = hyp:instantiateTemplates(templates)
        if not state.knowns:get(inst.formal) then
            local err: ByError = { err = "missing_hyp", hyp = inst }
            table.insert(errors, err)
        end
    end

    if #errors > 0 then
        return state:error(), errors
    end

    -- Instantiate the conclusion to see what we actually proved
    local conclusion = thm.conclusion:instantiateTemplates(templates)

    -- If the conclusion isn't the goal then this proof doesn't suffice.
    if conclusion.formal ~= state.goal.formal then
        local err: ByError = { err = "wrong_conclusion", conclusion = conclusion }
        table.insert(errors, err)        
        return state:error(), errors
    end

    -- Now we can apply the theorem to our local state
    state.formal = state.formal:applyTheorem(thm, templates)
    state.info = state.info:withDeduce(conclusion:fact())
    state.knowns:set(conclusion.formal:fact(), conclusion:fact())

    return state, errors
end

function M.byErrorToDiag(err: ByError, goal: Frag, thmName: string, thmNameSpan: Span): Diagnostic
    if err.err == "missing_hyp" then
        return Diagnostic:new(
            `missing hypothesis \`{err.hyp}\``,
            thmNameSpan:label(`while applying theorem \`{thmName}\``)
        )
    elseif err.err == "wrong_conclusion" then
        return Diagnostic:new(
            "theorem does not solve goal",
            thmNameSpan:label(`theorem shows \`{err.conclusion}\` not \`{goal}\``)
        )
    else
        assert(false)
    end
end

function tryManual(    
    just: { _span: Span, thm: SpannedString, tmps: Templates },
    thm: Theorem,
    instantiations: {Template},
    state: state.State
): (state.State, {Diagnostic})
    -- Now collect the template instantiations
    local templates = thm.templates

    -- The number of instantiations should match the number of templates
    if #templates ~= #instantiations then
        local diag = Diagnostic:new(
            "wrong number of template instantiations",
            just.tmps._span:label("expected " .. #templates .. ", found " .. #instantiations)
        )
            :withTacticInfo(state.info)
        return state:error(), {diag}
    end 

    -- Resolve each instantiation
    local resolved = {}
    local resolveErrors = {}
    for i, tmp in templates do 
        local tmpScope = addTemplateToScope(state.scope, tmp)
        local frag, diag = instantiations[i].frag:resolve(tmpScope, tmp.cat)
        if diag ~= nil then
            table.insert(resolveErrors, diag:withTacticInfo(state.info))
        elseif frag ~= nil then
            table.insert(resolved, frag)
        end
    end

    if #resolveErrors > 0 then
        return state:error(), resolveErrors
    end

    -- Check if the resolved hypotheses and theorem solve the goal.
    local newState, errors = M.handleBy(thm, resolved, state)
    local diags = {}

    for i, err in errors do
        diags[i] = M.byErrorToDiag(err, state.goal, just.thm.str, just.thm.span)
            :withTacticInfo(state.info)
    end

    return newState, diags
end

function tryVampire(
    just: { _span: Span, thm: SpannedString, tmps: Templates },
    thm: Theorem,
    state: state.State
): state.State
    -- First, recall the provided theorem
    local state1, rErr = recall.handleRecall(thm, state)
    if rErr ~= nil then 
        recall.recallErrToDiag(rErr, just.thm.span)
            :withTacticInfo(state.info)
            :report()
        return state1
    end

    local state2, vErr = vampire.handleVampire(state)
    if vErr ~= nil then
        vampire.vampErrToDiag(vErr, just.thm.span)
            :withTacticInfo(state1.info)
            :report()
    end

    return state2
end

function M.handleByTactic(
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

    local instantiations = getTemplateInstantiations(just.tmps)
    local newState, diags = tryManual(just, thm, instantiations, state:copy())

    if #instantiations == 0 and #diags > 0 then
        -- try vampire instead
        return tryVampire(just, thm, state)
    else
        -- otherwise report the errors and move on
        for _, diag in diags do
            diag:report()
        end

        return newState
    end
end

return M