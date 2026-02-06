local State = {}
State.__index = State

type StateData = {
    --- track the formal proof we have completed so far
    formal: ProofState,

    --- info for displaying our current proof state
    info: TacticInfo,

    --- list for tactics of what has been proven
    knowns: FactMap<Fact>,
    --- goal for tactics of what we are trying to prove
    goal: Frag,
    --- scope to resolve fragments in
    scope: Scope
}
export type State = typeof(setmetatable({} :: StateData, State))

function State.new(formal: ProofState, info: TacticInfo): State
    local self = {}
    self.formal = formal
    self.info = info
    self.goal = formal.theorem.conclusion
    self.knowns = FactMap:new()
    self.scope = formal.theorem.scope

    -- We know all the hypotheses to start
    for _, h in formal.theorem.hypotheses do
        self.knowns:set(h.formal, h)
    end

    return setmetatable(self, State)
end

function State.copy(self: State): State 
    local new = {}
    new.formal = self.formal
    new.info = self.info
    new.knowns = self.knowns:copy()
    new.goal = self.goal
    new.scope = self.scope

    return setmetatable(new, State)
end

function State.error(self: State): State
    self.formal = self.formal:applyError(self.goal)
    self.info = self.info:withDeduce(self.goal:fact())
    self.knowns:set(self.goal.formal:fact(), self.goal:fact())
    return self
end

function State.todo(self: State): State
    self.formal = self.formal:applyTodo(self.goal)
    self.info = self.info:withDeduce(self.goal:fact())
    self.knowns:set(self.goal.formal:fact(), self.goal:fact())
    return self
end

return { State = State }