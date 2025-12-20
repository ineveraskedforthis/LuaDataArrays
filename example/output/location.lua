local ffi = require("ffi")
---@class location_strong_id
---@field is_location boolean
LOCATION = {  }

---@param state data_arrays
function LOCATION.reserve(state)
	state.location_usage = ffi.new("int64_t[?]", state.location_size)
	state.location_generation = ffi.new("int64_t[?]", state.location_size)
	state.location_data_danger = ffi.new("float[?]", state.location_size)
	state.location_referenced_as_one_of_location_in_party_location_table = {  }
end

---@param state data_arrays
---@param location_id location_strong_id
---@return boolean
function LOCATION.is_valid(state, location_id)
	if ((location_id % 4294967296 < state.location_size) and (0 <= location_id % 4294967296)) then
		return (((location_id % 4294967296 < state.location_size) and (0 <= location_id % 4294967296)) and ((location_id - location_id % 4294967296) / 4294967296 == state.location_generation[tonumber(location_id % 4294967296)]))
	else
		return false
	end

end

---@param state data_arrays
---@param location_id location_strong_id
---@return number
function LOCATION.get_danger(state, location_id)
	assert(LOCATION.is_valid(state, location_id))
	return state.location_data_danger[tonumber(location_id % 4294967296)]
end

---@param state data_arrays
---@param location_id location_strong_id
---@param value number
function LOCATION.set_danger(state, location_id, value)
	assert(LOCATION.is_valid(state, location_id))
	state.location_data_danger[tonumber(location_id % 4294967296)] = value
end

---@param state data_arrays
---@return location_strong_id
function LOCATION.create(state)
	---@type number
	local id = state.location_available_id

	state.location_usage[tonumber(id)] = 0
	while (0 < state.location_usage[tonumber(id)]) do
		assert((state.location_available_id < state.location_size))
		state.location_available_id = (state.location_available_id + 1)
	end
	return id + state.location_generation[tonumber(id)] * 4294967296
end

---@param state data_arrays
---@param location_id location_strong_id
function LOCATION.delete(state, location_id)
	assert(LOCATION.is_valid(state, location_id))
	state.location_generation[tonumber(location_id % 4294967296)] = (state.location_generation[tonumber(location_id % 4294967296)] + 1)
	state.location_data_danger[tonumber(location_id % 4294967296)] = 0
	---@type number[]
	local temp_container = {  }

	if state.location_referenced_as_one_of_location_in_party_location_table[tonumber(location_id % 4294967296)] then for _, val in ipairs(state.location_referenced_as_one_of_location_in_party_location_table[tonumber(location_id % 4294967296)]) do table.insert(temp_container, val) end end
	for _, iterator in ipairs(temp_container) do
		PARTY_LOCATION.delete_unsafe(state, iterator)
	end


end

---@param state data_arrays
---@param raw_id number
function LOCATION.delete_unsafe(state, raw_id)
	state.location_generation[tonumber(raw_id)] = (state.location_generation[tonumber(raw_id)] + 1)
	state.location_data_danger[tonumber(raw_id)] = 0
end

