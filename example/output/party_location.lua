local ffi = require("ffi")
---@class party_location_strong_id
---@field is_party_location boolean
PARTY_LOCATION = {  }

---@param state data_arrays
function PARTY_LOCATION.reserve(state)
	state.party_location_usage = ffi.new("int64_t[?]", state.party_location_size)
	state.party_location_generation = ffi.new("int64_t[?]", state.party_location_size)
	state.party_location_link_party_from_party_table = ffi.new("int64_t[?]", state.party_location_size)
	state.party_location_link_location_from_location_table = ffi.new("int64_t[?]", state.party_location_size)
end

---@param state data_arrays
---@param party_location_id party_location_strong_id
---@return boolean
function PARTY_LOCATION.is_valid(state, party_location_id)
	if ((party_location_id % 4294967296 < state.party_location_size) and (0 <= party_location_id % 4294967296)) then
		return (((party_location_id % 4294967296 < state.party_location_size) and (0 <= party_location_id % 4294967296)) and ((party_location_id - party_location_id % 4294967296) / 4294967296 == state.party_location_generation[tonumber(party_location_id % 4294967296)]))
	else
		return false
	end

end

---@param state data_arrays
---@param party_as_party party_strong_id
---@param location_as_location location_strong_id
---@return party_location_strong_id
function PARTY_LOCATION.create(state, party_as_party, location_as_location)
	---@type number
	local id = state.party_location_available_id

	state.party_location_usage[tonumber(id)] = 0
	while (0 < state.party_location_usage[tonumber(id)]) do
		assert((state.party_location_available_id < state.party_location_size))
		state.party_location_available_id = (state.party_location_available_id + 1)
	end
	assert(PARTY.is_valid(state, party_as_party))
	if state.party_reference_as_unique_party_in_party_location_table[tonumber(party_as_party % 4294967296)] ~= nil then
		PARTY_LOCATION.delete_unsafe(state, state.party_reference_as_unique_party_in_party_location_table[tonumber(party_as_party % 4294967296)])
	end

	state.party_reference_as_unique_party_in_party_location_table[tonumber(party_as_party % 4294967296)] = id
	state.party_location_link_party_from_party_table[tonumber(id)] = party_as_party % 4294967296

	assert(LOCATION.is_valid(state, location_as_location))
	if state.location_referenced_as_one_of_location_in_party_location_table[location_as_location % 4294967296] then state.location_referenced_as_one_of_location_in_party_location_table[tonumber(location_as_location % 4294967296)][tonumber(id)] = id else state.location_referenced_as_one_of_location_in_party_location_table[tonumber(location_as_location % 4294967296)] = {  }; state.location_referenced_as_one_of_location_in_party_location_table[tonumber(location_as_location % 4294967296)][tonumber(id)] = id; end
	state.party_location_link_location_from_location_table[tonumber(id)] = location_as_location % 4294967296

	return id + state.party_location_generation[tonumber(id)] * 4294967296
end

---@param state data_arrays
---@param party_location_id party_location_strong_id
function PARTY_LOCATION.delete(state, party_location_id)
	assert(PARTY_LOCATION.is_valid(state, party_location_id))
	state.party_location_generation[tonumber(party_location_id % 4294967296)] = (state.party_location_generation[tonumber(party_location_id % 4294967296)] + 1)
	state.party_reference_as_unique_party_in_party_location_table[state.party_location_link_party_from_party_table[tonumber(party_location_id % 4294967296)]] = nil
	state.party_location_link_party_from_party_table[tonumber(party_location_id % 4294967296)] = 0

	if state.location_referenced_as_one_of_location_in_party_location_table[state.party_location_link_location_from_location_table[tonumber(party_location_id % 4294967296)]] then state.location_referenced_as_one_of_location_in_party_location_table[tonumber(state.party_location_link_location_from_location_table[tonumber(party_location_id % 4294967296)])][tonumber(party_location_id % 4294967296)] = nil end
	state.party_location_link_location_from_location_table[tonumber(party_location_id % 4294967296)] = 0

end

---@param state data_arrays
---@param raw_id number
function PARTY_LOCATION.delete_unsafe(state, raw_id)
	state.party_location_generation[tonumber(raw_id)] = (state.party_location_generation[tonumber(raw_id)] + 1)
	state.party_reference_as_unique_party_in_party_location_table[state.party_location_link_party_from_party_table[tonumber(raw_id)]] = nil
	state.party_location_link_party_from_party_table[tonumber(raw_id)] = 0

	if state.location_referenced_as_one_of_location_in_party_location_table[state.party_location_link_location_from_location_table[tonumber(raw_id)]] then state.location_referenced_as_one_of_location_in_party_location_table[tonumber(state.party_location_link_location_from_location_table[tonumber(raw_id)])][tonumber(raw_id)] = nil end
	state.party_location_link_location_from_location_table[tonumber(raw_id)] = 0

end

