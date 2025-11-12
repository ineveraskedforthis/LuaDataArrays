local ffi = require("ffi")
PARTY = {}
---@param state data_arrays
local function reserve_generation_array(state)
	state.generation_counter_array_party = ffi.new("int32_t[?]", state.size_party)
end
---@class party_strong_id
---@field internal_id number
---@field generation_counter number

---@param state data_arrays
local function reserve_data_array_party_count(state)
	state.data_array_party_count = ffi.new("int16_t[?]", state.size_party)
end
---@param state data_arrays
---@param id party_strong_id
---@returns number
function PARTY.get_count(state, id)
	assert(state.generation_counter_array_party[id.internal_id] == id.generation_counter)
	return state.data_array_party_count[id.internal_id]
end
---@param state data_arrays
---@param id party_strong_id
---@param value number
function PARTY.set_count(state, id, value)
	assert(state.generation_counter_array_party[id.internal_id] == id.generation_counter)
	state.data_array_party_count[id.internal_id] = value
end
---@param state data_arrays
function PARTY.reserve(state)
	reserve_generation_array(state)
	reserve_data_array_party_count(state)
end
