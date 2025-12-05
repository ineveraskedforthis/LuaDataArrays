local ffi = require("ffi")
PARTY = {}
---@param state data_arrays
---@param id party_strong_id
function PARTY.is_valid(state, id)
	local bounded = state.size_party > id.internal_id
	if (not bounded) then return false end
	local is_used = state.used_party_id[id.internal_id] == 1
	local fresh = state.generation_counter_array_party[id.internal_id] == id.generation_counter
	return bounded and is_used and fresh
end
---@param state data_arrays
local function reserve_generation_array(state)
	state.available_party_id = 0
	state.used_party_id = ffi.new("uint8_t[?]", state.size_party)
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
---@param state data_arrays
---@returns party_strong_id
function PARTY.create(state)
	local id = state.available_party_id
	state.used_party_id[id] = 1
	while state.used_party_id[state.available_party_id] ~= 0 do
		assert(state.available_party_id < state.size_party)
		state.available_party_id = state.available_party_id + 1
	end
	---@type party_strong_id
	return ffi.new("struct strong_id", { id, state.generation_counter_array_party[id]  })
end
---@param state data_arrays
---@param id party_strong_id
function PARTY.delete(state, id)
	assert(PARTY.is_valid(state, id))
	state.used_party_id[id.internal_id] = 0
	if (id.internal_id < state.available_party_id) then state.available_party_id = id.internal_id end
end
