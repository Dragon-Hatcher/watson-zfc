local state = require("./state")

local M: {
    justificationTable: { [string]: (Justification, state.State) -> state.State },
    tacticTable: { [string]: (Tactic, state.State) -> state.State },
    handleJustification: (Justification, state.State) -> state.State,
    handleTactic: (Tactic, state.State) -> state.State,
} = { } :: any

function M.handleJustification(just: Justification, state: state.State): state.State
    return M.justificationTable[just._rule](just, state)
end

function M.handleTactic(tactic: Tactic, state: state.State): state.State
    return M.tacticTable[tactic._rule](tactic, state)
end

return M