local shared = require("./shared")
local M = {}

function shouldReduce(frag: Frag, watch: boolean?): boolean
    local source = frag.source

    if source == nil then return false end
    if source.isLuaApi then return true end

    if source.isDefinitionCmd ~= nil then
        local attrs = shared.attributes:getAttributes(source.isDefinitionCmd)
        for _, attr in attrs do
            if attr._rule == "reducible" then 
                return true 
            end
        end
        return false
    end

    return false
end

function M.reduceTop(frag: Frag): Frag
    while shouldReduce(frag) do
        frag = frag:reduce()
    end
    return frag
end

return M