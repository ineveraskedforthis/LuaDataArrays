local ffi = require("ffi")
PARTY_LOCATION = {}
---@param state data_arrays
local function reserve_generation_array(state)
	state.generation_counter_array_party_location = ffi.new("int32_t[?]", state.size_party_location)
end
---@class party_location_strong_id
---@field internal_id number
---@field generation_counter number

---@param state data_arrays
local function reserve_link_array_party_location_party(state)
	state.data_array_party_location_to_party = ffi.new("int32_t[?]", state.size_party_location)
	state.data_array_party_location_from_party = ffi.new("int32_t[?]", state.size_party)
end
---@param state data_arrays
local function reserve_link_array_party_location_location(state)
	state.data_array_party_location_to_location = ffi.new("int32_t[?]", state.size_party_location)
	state.data_array_party_location_from_location = ffi.new("int32_t[?]", state.size_location)
end
---@param state data_arrays
function PARTY_LOCATION.reserve(state)
	reserve_generation_array(state)
	reserve_link_array_party_location_party(state)
	reserve_link_array_party_location_location(state)
end
