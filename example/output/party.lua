local ffi = require("ffi")
---@class party_strong_id
---@field is_party boolean
PARTY = {  }

---@param state data_arrays
function PARTY.reserve(state)
	state.party_usage = ffi.new("int64_t[?]", state.party_size)
	state.party_generation = ffi.new("int64_t[?]", state.party_size)
	state.party_data_count = ffi.new("int16_t[?]", state.party_size)
	state.party_reference_as_unique_party_in_party_location_table = {  }
end

---@param state data_arrays
---@param party_id party_strong_id
---@return boolean
function PARTY.is_valid(state, party_id)
	if ((party_id % 4294967296 < state.party_size) and (0 <= party_id % 4294967296)) then
		return (((party_id % 4294967296 < state.party_size) and (0 <= party_id % 4294967296)) and ((party_id - party_id % 4294967296) / 4294967296 == state.party_generation[tonumber(party_id % 4294967296)]))
	else
		return false
	end

end

---@param state data_arrays
---@param party_id party_strong_id
---@return number
function PARTY.get_count(state, party_id)
	assert(PARTY.is_valid(state, party_id))
	return state.party_data_count[tonumber(party_id % 4294967296)]
end

---@param state data_arrays
---@param party_id party_strong_id
---@param value number
function PARTY.set_count(state, party_id, value)
	assert(PARTY.is_valid(state, party_id))
	state.party_data_count[tonumber(party_id % 4294967296)] = value
end

---@param state data_arrays
---@return party_strong_id
function PARTY.create(state)
	---@type number
	local id = state.party_available_id

	state.party_usage[tonumber(id)] = 0
	while (0 < state.party_usage[tonumber(id)]) do
		assert((state.party_available_id < state.party_size))
		state.party_available_id = (state.party_available_id + 1)
	end
	return id + state.party_generation[tonumber(id)] * 4294967296
end

---@param state data_arrays
---@param party_id party_strong_id
function PARTY.delete(state, party_id)
	assert(PARTY.is_valid(state, party_id))
	state.party_generation[tonumber(party_id % 4294967296)] = (state.party_generation[tonumber(party_id % 4294967296)] + 1)
	state.party_data_count[tonumber(party_id % 4294967296)] = 0
	PARTY_LOCATION.delete_unsafe(state, state.party_reference_as_unique_party_in_party_location_table[tonumber(party_id % 4294967296)])
end

---@param state data_arrays
---@param raw_id number
function PARTY.delete_unsafe(state, raw_id)
	state.party_generation[tonumber(raw_id)] = (state.party_generation[tonumber(raw_id)] + 1)
	state.party_data_count[tonumber(raw_id)] = 0
end

