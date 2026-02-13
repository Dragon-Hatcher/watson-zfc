local frag = require("./frag")

local M = {}

-- Categories
M.sentenceCat = FormalCat:sentence()
M.termCat = FormalCat:get("term")
assert(M.termCat ~= nil)

-- Theorems
M.deductionThm = Theorem:lookupByName("deduction")
assert(M.deductionThm ~= nil)

M.notNotElimThm = Theorem:lookupByName("not_not.elim")
assert(M.notNotElimThm ~= nil)

M.mpThm = Theorem:lookupByName("modus_ponens")
assert(M.mpThm ~= nil)

M.explosionThm = Theorem:lookupByName("explosion")
assert(M.explosionThm ~= nil)

M.existsElimThm = Theorem:lookupByName("exists.elim")
assert(M.existsElimThm ~= nil)

M.existsIntroThm = Theorem:lookupByName("exists.intro")
assert(M.existsIntroThm ~= nil)

M.forallIntroThm = Theorem:lookupByName("forall.intro")
assert(M.forallIntroThm ~= nil)

M.forallElimThm = Theorem:lookupByName("forall.elim")
assert(M.forallElimThm ~= nil)

M.extensionalityThm = Theorem:lookupByName("zfc.extensionality")
assert(M.extensionalityThm ~= nil)

-- Patterns
local scopeTactic = "dummy"

M.holePattern = frag.makePattern(
    "p", M.sentenceCat,
    scopeTactic,
    {{name = "p", cat = M.sentenceCat}}
)

M.sentenceParenPattern = frag.makePattern(
    "(p)", M.sentenceCat,
    scopeTactic,
    {{name = "p", cat = M.sentenceCat}}
)

M.termParenPattern = frag.makePattern(
    "(t)", M.termCat,
    scopeTactic,
    {{name = "t", cat = M.termCat}}
)

M.andPattern = frag.makePattern(
    "p ∧ q", M.sentenceCat,
    scopeTactic,
    {{name = "p", cat = M.sentenceCat}, {name = "q", cat = M.sentenceCat}}
)

M.orPattern = frag.makePattern(
    "p ∨ q", M.sentenceCat,
    scopeTactic,
    {{name = "p", cat = M.sentenceCat}, {name = "q", cat = M.sentenceCat}}
)

M.impPattern = frag.makePattern(
    "p → q", M.sentenceCat,
    scopeTactic,
    {{name = "p", cat = M.sentenceCat}, {name = "q", cat = M.sentenceCat}}
)

M.iffPattern = frag.makePattern(
    "p ↔ q", M.sentenceCat,
    scopeTactic,
    {{name = "p", cat = M.sentenceCat}, {name = "q", cat = M.sentenceCat}}
)

M.forallPattern = frag.makePattern(
    "∀x, p", M.sentenceCat,
    scopeTactic,
    {{name = "p", cat = M.sentenceCat}}
):changeBinderNames({})

M.existsPattern = frag.makePattern(
    "∃x, p", M.sentenceCat,
    scopeTactic,
    {{name = "p", cat = M.sentenceCat}}
):changeBinderNames({})

M.witnessPattern = frag.makePattern(
    "∃ᵉ x, p ⊢ q", M.termCat,
    scopeTactic,
    {
        {name = "p", cat = M.sentenceCat},
        {name = "q", cat = M.sentenceCat}
    }
)

M.arbitraryPattern = frag.makePattern(
    "∃ᵉx, ¬p ⊢ ⊥", M.termCat,
    scopeTactic,
    {{name = "p", cat = M.sentenceCat}}
)

M.falsum = frag.makePattern(
    "⊥", M.sentenceCat,
    scopeTactic,
    {}
)

M.notPattern = frag.makePattern(
    "¬p", M.sentenceCat,
    scopeTactic,
    {{name = "p", cat = M.sentenceCat}}
)

M.eqPattern = frag.makePattern(
    "a = b", M.sentenceCat,
    scopeTactic,
    {{name = "a", cat = M.termCat}, {name = "b", cat = M.termCat}}
)

M.neqPattern = frag.makePattern(
    "a ≠ b", M.sentenceCat,
    scopeTactic,
    {{name = "a", cat = M.termCat}, {name = "b", cat = M.termCat}}
)

M.inPattern = frag.makePattern(
    "a ∈ b", M.sentenceCat,
    scopeTactic,
    {{name = "a", cat = M.termCat}, {name = "b", cat = M.termCat}}
)

M.ninPattern = frag.makePattern(
    "a ∉ b", M.sentenceCat,
    scopeTactic,
    {{name = "a", cat = M.termCat}, {name = "b", cat = M.termCat}}
)

M.boundedComprehensionPattern = frag.makePattern(
    "{x ∈ a | p}", M.termCat,
    scopeTactic,
    {{name = "a", cat = M.termCat}, {name = "p", cat = M.sentenceCat}}
):changeBinderNames({})

return M
