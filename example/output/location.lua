local ffi = require("ffi")
LOCATION = {}
---@param state data_arrays
---@param id location_strong_id
function LOCATION.is_valid(state, id)
	local bounded = state.size_location > id.internal_id
	if (not bounded) then return false end
	local is_used = state.used_location_id[id.internal_id] == 1
	local fresh = state.generation_counter_array_location[id.internal_id] == id.generation_counter
	return bounded and is_used and fresh
end
---@param state data_arrays
local function reserve_generation_array(state)
	state.available_location_id = 0
	state.used_location_id = ffi.new("uint8_t[?]", state.size_location)
	state.generation_counter_array_location = ffi.new("int32_t[?]", state.size_location)
end
---@class location_strong_id
---@field internal_id number
---@field generation_counter number

---@param state data_arrays
local function reserve_data_array_location_danger(state)
	state.data_array_location_danger = ffi.new("float[?]", state.size_location)
end
---@param state data_arrays
---@param id location_strong_id
---@returns number
function LOCATION.get_danger(state, id)
	assert(state.generation_counter_array_location[id.internal_id] == id.generation_counter)
	return state.data_array_location_danger[id.internal_id]
end
---@param state data_arrays
---@param id location_strong_id
---@param value number
function LOCATION.set_danger(state, id, value)
	assert(state.generation_counter_array_location[id.internal_id] == id.generation_counter)
	state.data_array_location_danger[id.internal_id] = value
end
---@param state data_arrays
function LOCATION.reserve(state)
	reserve_generation_array(state)
	reserve_data_array_location_danger(state)
end
---@param state data_arrays
---@returns location_strong_id
function LOCATION.create(state)
	local id = state.available_location_id
	state.used_location_id[id] = 1
	while state.used_location_id[state.available_location_id] ~= 0 do
		assert(state.available_location_id < state.size_location)
		state.available_location_id = state.available_location_id + 1
	end
	---@type location_strong_id
	return ffi.new("struct strong_id", { id, state.generation_counter_array_location[id]  })
end
---@param state data_arrays
---@param id location_strong_id
function LOCATION.delete(state, id)
	assert(LOCATION.is_valid(state, id))
	state.used_location_id[id.internal_id] = 0
	if (id.internal_id < state.available_location_id) then state.available_location_id = id.internal_id end
end
