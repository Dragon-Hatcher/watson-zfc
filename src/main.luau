local M = {}

local State = {}
State.__index = State

type StateData = {
    formal: ProofState,
    info: TacticInfo,
    scope: Scope,
    knowns: FactMap<boolean>,
    goal: Frag,
}
type State = typeof(setmetatable({} :: StateData, State))

function State.new(formal: ProofState, info: TacticInfo): State
    local self = {}
    self.formal = formal
    self.info = info
    self.scope = formal.theorem.scope
    self.knowns = FactMap:new()
    for _, h in formal.theorem.hypotheses do
        self.knowns:set(h.formal, true)
    end
    self.goal = formal.theorem.conclusion

    return setmetatable(self, State)
end

function State.copy(self: State): State 
    local new = {}
    new.formal = self.formal
    new.info = self.info
    new.scope = self.scope
    new.knowns = self.knowns:copy()
    new.goal = self.goal

    return setmetatable(new, State)
end

function State.solveWithError(self: State)
    self.knowns:set(self.goal.formal:fact(), true)
    self.formal = self.formal:applyError(self.goal)
    self.info = self.info:withDeduce(self.goal:fact())
    return self
end

function handleEmptyTactic(tactic: { _span: Span }, state: State): State
    -- Check if we have proven the goal. If we haven't we should report an 
    -- error.
    if not state.knowns:get(state.goal.formal:fact()) then
        Diagnostic:new("goal `" .. tostring(state.goal) .. "` unproven at end of tactic")
            :withError("", tactic._span)
            :withTacticInfo(state.info)
            :report()
        return state:solveWithError()
    end

    -- We have already proved the goal. Nothing more to do.
    return state
end

function handleTodoTactic(state: State): State
    state.formal = state.formal:applyTodo(state.goal)
    state.knowns:set(state.goal.formal:fact(), true)
    return state
end

function handleHaveTactic(
    tactic: { _span: Span, show: UnResFact, next: Tactic },
    handleSubproof: (State) -> State,
    state: State
): State
    local show, d1, d2 = tactic.show:resolve(state.scope)
    if d1 ~= nil then d1:withTacticInfo(state.info):report() end
    if d2 ~= nil then d2:withTacticInfo(state.info):report() end
    if show == nil then return state:solveWithError() end

    local subproofState = state:copy()
    subproofState.goal = show.conclusion
    subproofState.info = subproofState.info:withGoal(show.conclusion)
    if show.assumption ~= nil then
        subproofState.knowns:set(show.assumption.formal:fact(), true)
        subproofState.formal = subproofState.formal:addAssumption(show.assumption)
        subproofState.info = subproofState.info:withAssume(show.assumption)
        subproofState = handleSubproof(subproofState)
        subproofState.formal = subproofState.formal:popAssumption(show.conclusion)
    else
        subproofState = handleSubproof(subproofState)
    end

    state.knowns:set(show.formal, true)
    state.formal = subproofState.formal
    state.info = state.info:withDeduce(show)
    return handleTactic(tactic.next, state)
end

function getTemplateInstantiations(tmps: Templates): {Template}
    local instantiations = {}
    while tmps._rule ~= "templates.none" do
        table.insert(instantiations, tmps.template)
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

function handleByTactic(
    tactic: { theorem: SpannedString, templates: Templates }, 
    state: State
): State
    local thm = Theorem:lookupByName(tactic.theorem.str)
    if thm == nil then
        Diagnostic:new("unknown theorem `" .. tactic.theorem.str .. "`")
            :withError("", tactic.theorem.span)
            :withTacticInfo(state.info)
            :report()
        return state:solveWithError()
    end

    local templates = thm.templates
    local instantiations = getTemplateInstantiations(tactic.templates)
    if #templates ~= #instantiations then
        Diagnostic:new("wrong number of template instantiations")
            :withError("expected " .. #templates .. ", found " .. #instantiations, tactic.templates._span)
            :withTacticInfo(state.info)
            :report()
        return state:solveWithError()
    end 

    local resolved = {}
    local resolveError = false
    for i, tmp in templates do 
        local tmpScope = addTemplateToScope(state.scope, tmp)
        local f, diag = instantiations[i].inst:resolve(tmpScope, tmp.cat)
        if diag ~= nil then
            diag:withTacticInfo(state.info):report()
            resolveError = true
        else
            table.insert(resolved, f :: Frag)
        end
    end

    if resolveError then
        return state:solveWithError()
    end

    local missingHyp = false
    for i, hyp in thm.hypotheses do
        local inst = hyp:instantiateTemplates(resolved)
        if not state.knowns:get(inst.formal) then
            Diagnostic:new("missing hypothesis `" .. tostring(inst) .. "`")
                :withError("while applying theorem `" .. thm.name .. "`", tactic.theorem.span)
                :withTacticInfo(state.info)
                :report()
            missingHyp = true
        end
    end

    if missingHyp then
        return state:solveWithError()
    end

    local instConclusion = thm.conclusion:instantiateTemplates(resolved)

    if state.goal.formal ~= instConclusion.formal then
        Diagnostic:new("by tactic did not resolve goal")
            :withError("showed `" .. tostring(instConclusion) .. "` instead of goal", tactic.theorem.span)
            :withTacticInfo(state.info)
            :report()
        return state:solveWithError()
    end

    state.knowns:set(instConclusion.formal:fact(), true)
    state.formal = state.formal:applyTheorem(thm, resolved)
    state.info = state.info:withDeduce(instConclusion:fact())
    return state
end

function handleAssumeTactic(
    tactic: { assume: SpannedString, assumption: UnResFrag, next: Tactic }, 
    state: State
): State
    local assumption, diag = tactic.assumption:resolve(state.scope)    
    if diag ~= nil then diag:withTacticInfo(state.info):report() end
    if assumption == nil then return state:solveWithError() end

    local imp, _ = UnResFrag:parse("p → q", FormalCat:sentence())
    assert(imp ~= nil)
    local impPattern, _ = imp:resolve(state.scope
        :bindHole(Binding:name("p", FormalCat:sentence()), 0)
        :bindHole(Binding:name("q", FormalCat:sentence()), 1))
    assert(impPattern ~= nil)
    local match = state.goal:match(impPattern)

    if match == nil then
        Diagnostic:new("goal must be implication but was `" .. tostring(state.goal) .. "`")
            :withError("", tactic.assume.span)
            :report()
        return state:solveWithError()
    end

    local goalAssumption, goalConclusion = match[0], match[1]

    if goalAssumption.formal ~= assumption.formal then
        Diagnostic:new("goal assumption does not match assume assumption")
            :withError("goal assumes `" .. tostring(goalAssumption) .. "`", tactic.assumption.span)
            :report()
        return state:solveWithError()
    end

    local subproofState = state:copy()
    subproofState.goal = goalConclusion
    subproofState.knowns:set(assumption.formal:fact(), true)
    subproofState.info = subproofState.info:withAssume(assumption):withGoal(goalConclusion)
    subproofState.formal = subproofState.formal:addAssumption(assumption)
    subproofState = handleTactic(tactic.next, subproofState)
    subproofState.formal = subproofState.formal:popAssumption(goalConclusion)

    local deductionThm = Theorem:lookupByName("deduction")
    assert(deductionThm ~= nil)

    -- use the deduction theorem to deduce the implication we want
    state.formal = subproofState.formal:applyTheorem(deductionThm, {assumption, goalConclusion})
    state.knowns:set(state.goal.formal:fact(), true)
    state.info = state.info:withDeduce(state.goal:fact())

    return state
end

function handleTactic(tactic: Tactic, state: State): State
    if tactic._rule == "tactic.empty" then
        return handleEmptyTactic(tactic, state)
    elseif tactic._rule == "tactic.have" then
        return handleHaveTactic(
            tactic, 
            function(state) return handleTactic(tactic.subproof, state) :: State end,
            state
        )
    elseif tactic._rule == "tactic.have_by" then
        return handleHaveTactic(
            tactic, 
            function(state) return handleByTactic(tactic, state) end, 
            state
        )
    elseif tactic._rule == "tactic.by" then
        return handleByTactic(tactic, state)
    elseif tactic._rule == "tactic.assume" then
        return handleAssumeTactic(tactic, state)
    elseif tactic._rule == "tactic.todo" then
        return handleTodoTactic(state)
    else
        return "unreachable" :: any
    end
end

function M.handleTactic(tactic: Tactic, proofState: ProofState, tacticInfo: TacticInfo)
    local state = State.new(proofState, tacticInfo)
    return handleTactic(tactic, state).formal
end

return M
