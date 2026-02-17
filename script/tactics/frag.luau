local M = {}

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

return M