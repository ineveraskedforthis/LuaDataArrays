local ffi = require("ffi")
LOCATION = {}
---@param state data_arrays
local function reserve_generation_array(state)
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
