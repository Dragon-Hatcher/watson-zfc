local state = require("./state")
local shared = require("./shared")

local M = {}

local vSymbol = 0
local inPred = VPredicate:new("in", 2)
local vFalse = VPredicate:new("false", 0):with({})
local terms: FragMap<{[number]: VFunction}> = FragMap:new()

function termCacheSet(term: Frag, arity: number, v: VFunction)
    local arities = terms:get(term.formal) 
    if arities == nil then
        terms:set(term.formal, {[arity] = v})
    else
        arities[arity] = v
    end
end

function termCacheGet(term: Frag, arity: number): VFunction?
    local arities = terms:get(term.formal)
    if arities ~= nil then
        return arities[arity]
    else
        return nil
    end
end

type Bindings = {
    stack: {number},
    nextFree: number
}
function newBindings(): Bindings 
    return {
        stack = {},
        nextFree = 0
    }
end

function termToV(term: Frag, bindings: Bindings): VTerm?
    -- If there are more free variables then binding we have a problem
    assert(term.unclosedCount <= #bindings.stack)

    -- Terms can contain sentences so we might encounter them in our recursion.
    -- But we don't handle them so just return nil.
    if term.cat ~= shared.termCat then
        return nil
    end

    if term.formal.varIdx ~= nil then
        -- This is a variable, so return from the bindings stack.
        local vVar = bindings.stack[#bindings.stack - term.formal.varIdx]
        return VTerm:newVar(vVar)
    elseif term.replacement and term.replacement.unclosedCount ~= 0 then
        -- This is notation that contains a variable. TODO: handle
        assert(false)
    end

    -- First we attempt to convert all the children to terms. If we can then
    -- we treat this term as a function for Vampire.
    local children = {}
    for i, child in term.children do
        local vChild = termToV(child, bindings)
        if vChild == nil then children = nil; break end
        children[i] = vChild
    end

    -- If we didn't manage to convert all the children, e.g. if some of the
    -- children are sentences, then we just convert the whole term to a constant
    -- for Vampire.
    if children == nil then
        local cached = termCacheGet(term, 0)
        if cached then return cached:with({}) end

        local constant = VFunction:new(`v{vSymbol}`, 0)
        vSymbol += 1

        -- Update the cache with the new constant.
        termCacheSet(term, 0, constant)
        return constant:with({})
    end

    -- Now we can make a new function symbol
    if term.replacement then
        local fn = termCacheGet(term.replacement, #children)
        if fn == nil then 
            fn = VFunction:new(`v{vSymbol}`, #children)
            vSymbol += 1
            termCacheSet(term.replacement, #children, fn)
        end

        return (fn :: VFunction):with(children)
    else
        -- TODO: templates
        assert(false)
    end
end

function predToV(pred: Frag, bindings: Bindings): VFormula?
    pred = pred:changeBinderNames({})

    local match = pred:match(shared.impPattern)
    if match ~= nil then
        local lhs = predToV(match[0], bindings)
        local rhs = predToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return VFormula:newImp(lhs, rhs)
    end
    
    match = pred:match(shared.iffPattern)
    if match ~= nil then
        local lhs = predToV(match[0], bindings)
        local rhs = predToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return VFormula:newIff(lhs, rhs)
    end

    if pred.formal == shared.falsum.formal then
        return vFalse
    end

    match = pred:match(shared.forallPattern)
    if match ~= nil then
        -- claim the next free variable.
        local var = bindings.nextFree
        bindings.nextFree += 1

        -- push it to the stack before parsing child
        bindings.stack[#bindings.stack + 1] = var
        local p = predToV(match[0], bindings)

        -- now pop from the stack
        bindings.stack[#bindings.stack] = nil

        if not p then return nil end

        return VFormula:newForall(var, p)
    end

    match = pred:match(shared.existsPattern)
    if match ~= nil then
        local var = bindings.nextFree
        bindings.nextFree += 1
        bindings.stack[#bindings.stack + 1] = var
        local p = predToV(match[0], bindings)
        bindings.stack[#bindings.stack] = nil

        if not p then return nil end

        return VFormula:newExists(var, p)
    end

    match = pred:match(shared.andPattern)
    if match ~= nil then
        local lhs = predToV(match[0], bindings)
        local rhs = predToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return VFormula:newAnd(lhs, rhs)
    end

    match = pred:match(shared.orPattern)
    if match ~= nil then
        local lhs = predToV(match[0], bindings)
        local rhs = predToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return VFormula:newOr(lhs, rhs)
    end

    match = pred:match(shared.notPattern)
    if match ~= nil then
        local p = predToV(match[0], bindings)
        if not p then return nil end

        return VFormula:newNot(p)
    end

    -- TODO: we shouldn't need this
    match = pred:match(shared.sentenceParenPattern)
    if match ~= nil then
        return predToV(match[0], bindings)
    end

    match = pred:match(shared.eqPattern)
    if match ~= nil then
        local lhs = termToV(match[0], bindings)
        local rhs = termToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return VFormula:newEq(lhs, rhs)
    end

    match = pred:match(shared.inPattern)
    if match ~= nil then
        local lhs = termToV(match[0], bindings)
        local rhs = termToV(match[1], bindings)
        if not lhs or not rhs then return nil end

        return inPred:with({lhs, rhs})
    end

    if pred.formal.templateIdx ~= nil then
        -- Convert all the children
        local children = {}
        for i, child in pred.formal.children do
            local vChild = termToV(child, bindings)
            if vChild == nil then return nil end
            children[i] = vChild
        end

        local idx = pred.formal.templateIdx
        local vPred = VPredicate:new(`temp{idx}`, #children)
        return vPred:with(children)
    end

    log("can't pred (unknown)", tostring(pred), pred:match(shared.forallPattern))
    return nil
end

local options = VOptions:new()
options:setTimeout(50)

type VampError =
    | { err: "couldnt_convert_frag", frag: Frag }
    | { err: "unprovable" }
    | { err: "could_not_find_proof" }

function M.handleVampire(state: state.State): (state.State, VampError?)
    local problem = VProblem:new(options)
    local fail = nil

    -- Collect all the knowns as axioms for vampire
    for _, fact in state.knowns :: {[Fact]: Fact} do
        -- Ignore assumptions for now. We could handle later but not really important.
        if fact.assumption ~= nil then continue end

        local vPred = predToV(fact.conclusion, newBindings())
        if vPred then problem:addAxiom(vPred) else fail = fact.conclusion end
    end

    -- TODO: shouldn't need this. Should be able to just create a false.
    problem:addAxiom(VFormula:newNot(vFalse))

    -- And we conjecture the goal from the knowns
    local conjecture = predToV(state.goal, newBindings())
    if conjecture then problem:setConjecture(conjecture) else fail = state.goal end

    -- If any of the Vampire conversions failed report that as the error.
    if fail ~= nil then
        return state:error(), { err = "couldnt_convert_frag", frag = fail }
    end

    local solution = problem:solve()

    -- Check if Vampire was able to prove the conjecture
    if solution == "unprovable" then
        return state:error(), { err = "unprovable" }
    elseif solution ~= "proved" then
        return state:error(), { err = "could_not_find_proof" }
    end

    -- Success! We proved the goal
    state.knowns:set(state.goal.formal:fact(), state.goal:fact())
    state.info = state.info:withDeduce(state.goal:fact())

    -- TODO: convert vampire proof to formal proof
    state.formal = state.formal:applyTodo(state.goal)

    return state, nil
end

function M.vampErrToDiag(err: VampError, span: Span): Diagnostic
    if err.err == "couldnt_convert_frag" then
        return Diagnostic:new(`Unable to convert \`{err.frag}\` to Vampire`, span:label(""))
    elseif err.err == "unprovable" then
        return Diagnostic:new("Vampire proved the knowns facts do not imply the goal", span:label(""))
    elseif err.err == "could_not_find_proof" then
        return Diagnostic:new("Vampire was unable to prove the goal", span:label(""))
    else
        assert(false)
    end
end

function M.handleVampireTactic(
    tactic: { _span: Span },
    state: state.State
): state.State
    local newState, err = M.handleVampire(state)

    if err then
        M.vampErrToDiag(err, tactic._span)
            :withTacticInfo(state.info)
            :report()
    end

    return newState
end

return M