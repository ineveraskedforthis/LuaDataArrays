local ffi = require("ffi")
LOCATION = {  }

---@param state data_arrays
function LOCATION.reserve(state)
	state.location_usage = ffi.new("int64_t[?]", state.location_size)
	state.location_generation = ffi.new("int64_t[?]", state.location_size)
	state.location_data_danger = ffi.new("float[?]", state.location_size)
end

---@param state data_arrays
---@param location_id location_strong_id
---@returns boolean
function LOCATION.is_valid(state, location_id)
	if ((location_id % 4294967296 < state.location_size) and (0 <= location_id % 4294967296)) then
		return (((location_id % 4294967296 < state.location_size) and (0 <= location_id % 4294967296)) and ((location_id - location_id % 4294967296) / 4294967296 == state.location_generation[location_id % 4294967296]))
	else
		return false
	end

end

---@param state data_arrays
---@param location_id location_strong_id
---@returns float
function LOCATION.get_danger(state, location_id)
	assert(LOCATION.is_valid(state, location_id))

	return state.location_data_danger[location_id % 4294967296]

end

---@param state data_arrays
---@param location_id location_strong_id
---@param value float
function LOCATION.set_danger(state, location_id, value)
	assert(LOCATION.is_valid(state, location_id))

	state.location_data_danger[location_id % 4294967296] = value
end

---@param state data_arrays
---@returns location_strong_id
function LOCATION.create(state)
	id = state.location_available_id
	state.location_usage[id] = 0
	while (0 < state.location_usage[id]) do
		assert((state.location_available_id < state.location_size))

		state.location_available_id = (state.location_available_id + 1)
	end
	return id + state.location_generation[id] * 4294967296

end

