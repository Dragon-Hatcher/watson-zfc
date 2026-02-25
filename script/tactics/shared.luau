local M = {}

-- Categories
M.sentenceCat = FormalCat:sentence()
M.termCat = FormalCat:get("term")
assert(M.termCat ~= nil)

-- Attributes
M.attributes = AttributeTracker:atEnd()

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

function M.makePattern(
    text: string, cat: FormalCat, 
    vars: {{name: string, cat: FormalCat}}
): Frag
    local scope = Scope:atEnd()
    assert(scope ~= nil, "invalid tactic name")

    for i, var in vars do
        local binding = Binding:name(var.name, var.cat)
        scope = scope:bindHole(binding, i - 1)
    end

    local unresolved = UnResFrag:parse(text, cat)
    assert(unresolved ~= nil, "invalid fragment parse")

    local resolved = unresolved:resolve(scope)
    assert(resolved ~= nil, "can't resolve fragment")

    return resolved
end

-- Patterns
M.holePattern = M.makePattern(
    "p", M.sentenceCat,
    {{name = "p", cat = M.sentenceCat}}
)

M.andPattern = M.makePattern(
    "p ∧ q", M.sentenceCat,
    {{name = "p", cat = M.sentenceCat}, {name = "q", cat = M.sentenceCat}}
)

M.orPattern = M.makePattern(
    "p ∨ q", M.sentenceCat,
    {{name = "p", cat = M.sentenceCat}, {name = "q", cat = M.sentenceCat}}
)

M.impPattern = M.makePattern(
    "p → q", M.sentenceCat,
    {{name = "p", cat = M.sentenceCat}, {name = "q", cat = M.sentenceCat}}
)

M.iffPattern = M.makePattern(
    "p ↔ q", M.sentenceCat,
    {{name = "p", cat = M.sentenceCat}, {name = "q", cat = M.sentenceCat}}
)

M.forallPattern = M.makePattern(
    "∀x, p", M.sentenceCat,
    {{name = "p", cat = M.sentenceCat}}
):changeBinderNames({})

M.existsPattern = M.makePattern(
    "∃x, p", M.sentenceCat,
    {{name = "p", cat = M.sentenceCat}}
):changeBinderNames({})

M.witnessPattern = M.makePattern(
    "∃ᵉ x, p ⊢ q", M.termCat,
    {
        {name = "p", cat = M.sentenceCat},
        {name = "q", cat = M.sentenceCat}
    }
)

M.arbitraryPattern = M.makePattern(
    "∃ᵉx, ¬p ⊢ ⊥", M.termCat,
    {{name = "p", cat = M.sentenceCat}}
)

M.falsum = M.makePattern(
    "⊥", M.sentenceCat,
    {}
)

M.notPattern = M.makePattern(
    "¬p", M.sentenceCat,
    {{name = "p", cat = M.sentenceCat}}
)

M.eqPattern = M.makePattern(
    "a = b", M.sentenceCat,
    {{name = "a", cat = M.termCat}, {name = "b", cat = M.termCat}}
)

M.inPattern = M.makePattern(
    "a ∈ b", M.sentenceCat,
    {{name = "a", cat = M.termCat}, {name = "b", cat = M.termCat}}
)

M.boundedComprehensionPattern = M.makePattern(
    "{x ∈ a | p}", M.termCat,
    {{name = "a", cat = M.termCat}, {name = "p", cat = M.sentenceCat}}
):changeBinderNames({})

return M
