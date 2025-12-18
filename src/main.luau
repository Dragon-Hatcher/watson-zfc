local M = {}
    
function M.handleTactic(tactic: Tactic, proofState: ProofState)
    local thm = proofState.theorem
    return proofState:applyTodo(thm.conclusion)
end

return M
