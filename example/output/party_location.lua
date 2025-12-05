local ffi = require("ffi")
PARTY_LOCATION = {}
---@param state data_arrays
---@param id party_location_strong_id
function PARTY_LOCATION.is_valid(state, id)
	local bounded = state.size_party_location > id.internal_id
	if (not bounded) then return false end
	local is_used = state.used_party_location_id[id.internal_id] == 1
	local fresh = state.generation_counter_array_party_location[id.internal_id] == id.generation_counter
	return bounded and is_used and fresh
end
---@param state data_arrays
local function reserve_generation_array(state)
	state.available_party_location_id = 0
	state.used_party_location_id = ffi.new("uint8_t[?]", state.size_party_location)
	state.generation_counter_array_party_location = ffi.new("int32_t[?]", state.size_party_location)
end
---@class party_location_strong_id
---@field internal_id number
---@field generation_counter number

---@param state data_arrays
local function reserve_link_array_party_location_location(state)
	state.data_array_party_location_to_location = ffi.new("int32_t[?]", state.size_party_location)
	state.data_array_party_location_one_from_location = ffi.new("int32_t[?]", state.size_location)
end
---@param state data_arrays
local function reserve_link_array_party_location_party(state)
	state.data_array_party_location_to_party = ffi.new("int32_t[?]", state.size_party_location)
	state.data_array_party_location_many_from_party = {}
	for i = 0, state.size_party - 1 do
		state.data_array_party_location_many_from_party[i] = {}
	end
end
---@param state data_arrays
function PARTY_LOCATION.reserve(state)
	reserve_generation_array(state)
	reserve_link_array_party_location_location(state)
	reserve_link_array_party_location_party(state)
end
---@param state data_arrays
---@param location_link location_strong_id
---@param party_link party_strong_id
---@returns party_location_strong_id
function PARTY_LOCATION.create(state, location_link, party_link)
	local id = state.available_party_location_id
	state.used_party_location_id[id] = 1
	assert(LOCATION.is_valid(state, location_link))
	assert(state.data_array_party_location_one_from_location[location_link.internal_id] == 0)
	state.data_array_party_location_to_location[id] = location_link.internal_id
	state.data_array_party_location_one_from_location[location_link.internal_id] = id
	assert(PARTY.is_valid(state, party_link))
	state.data_array_party_location_to_party[id] = party_link.internal_id
	state.data_array_party_location_many_from_party[party_link.internal_id][id] = id
	while state.used_party_location_id[state.available_party_location_id] ~= 0 do
		assert(state.available_party_location_id < state.size_party_location)
		state.available_party_location_id = state.available_party_location_id + 1
	end
	---@type party_location_strong_id
	return ffi.new("struct strong_id", { id, state.generation_counter_array_party_location[id]  })
end
---@param state data_arrays
---@param id party_location_strong_id
function PARTY_LOCATION.delete(state, id)
	assert(PARTY_LOCATION.is_valid(state, id))
	state.used_party_location_id[id.internal_id] = 0
	if (id.internal_id < state.available_party_location_id) then state.available_party_location_id = id.internal_id end
end
