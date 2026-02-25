local assume = require("./assume")
local by = require("./by")
local contradiction = require("./contradiction")
local dispatch = require("./dispatch")
local done = require("./done")
local empty = require("./empty")
local have = require("./have")
local let = require("./let")
local state = require("./state")
local suffices = require("./suffices")
local thus = require("./thus")
local quant = require("./quant")
local print = require("./print")
local recall = require("./recall")
local vampire = require("./vampire")

local M = {}

dispatch.justificationTable = {
	["justification.empty"] = empty.handleEmpty,
	["justification.tactic"] = function(sp: { tactic: Tactic }, state: state.State)
		return dispatch.handleTactic(sp.tactic, state)
	end,
	["justification.by"] = by.handleByTactic,
	["justification.by.vampire"] = by.handleVampireByTactic,
	["justification.using"] = quant.handleUsing,
	["justification.specializing"] = quant.handleSpecializing,
	["justification.logically"] = vampire.handleVampireTactic,
	["justification.given"] = vampire.handleVampireTactic,
}

dispatch.tacticTable = {
	["tactic.follows"] = thus.handleThus,
	["tactic.hence"] = thus.handleThus,
	["tactic.thus"] = thus.handleThus,
	["tactic.assume"] = assume.handleAssume,
	["tactic.assume_then"] = assume.handleAssumeThen,
	["tactic.assume_contra"] = assume.handleAssumeContra,
	["tactic.suffices"] = suffices.handleSuffices,
	["tactic.have"] = have.handleHave,
	["tactic.contradiction"] = contradiction.handleContradiction,
	["tactic.obtain"] = quant.handleObtain,
	["tactic.arbitrary"] = quant.handleArbitrary,
	["tactic.recall"] = recall.handleRecallTactic,
	["tactic.vampire"] = vampire.handleVampireTactic,
	["tactic.let"] = let.handleLetTactic,
	["tactic.done"] = done.handleDone,
	["tactic.empty"] = empty.handleEmpty,
	["tactic.todo"] = function(tactic: {}, state: state.State)
		return state:todo()
	end,
	["tactic.print"] = print.handleEmpty,
}

function M.run(tactic: Tactic, formalProof: ProofState, tacticInfo: TacticInfo)
	local state = state.State.new(formalProof, tacticInfo)
	return dispatch.handleTactic(tactic, state).formal
end

return M