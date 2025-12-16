local ffi = require("ffi")
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
---@returns boolean
function PARTY_LOCATION.is_valid(state, party_location_id)
	if ((party_location_id % 4294967296 < state.party_location_size) and (0 <= party_location_id % 4294967296)) then
		return (((party_location_id % 4294967296 < state.party_location_size) and (0 <= party_location_id % 4294967296)) and ((party_location_id - party_location_id % 4294967296) / 4294967296 == state.party_location_generation[party_location_id % 4294967296]))
	else
		return false
	end

end

---@param state data_arrays
---@param party_as_party party_strong_id
---@param location_as_location location_strong_id
---@returns party_location_strong_id
function PARTY_LOCATION.create(state, party_as_party, location_as_location)
	id = state.party_location_available_id
	state.party_location_usage[id] = 0
	while (0 < state.party_location_usage[id]) do
		assert((state.party_location_available_id < state.party_location_size))

		state.party_location_available_id = (state.party_location_available_id + 1)
	end
	assert(PARTY.is_valid(state, party_as_party))

	if state.party_reference_as_unique_party_in_party_location_table[party_as_party % 4294967296] != nil then
		state.party_location_delete_weak(state.party_reference_as_unique_party_in_party_location_table[party_as_party % 4294967296])	end

	state.party_reference_as_unique_party_in_party_location_table[party_as_party % 4294967296] = id
	state.party_location_link_party_from_party_table[id] = party_as_party % 4294967296

	assert(LOCATION.is_valid(state, location_as_location))

	if state.location_reference_as_unique_location_in_party_location_table[Signify key] then state.location_reference_as_unique_location_in_party_location_table[location_as_location % 4294967296][id] = value else state.location_reference_as_unique_location_in_party_location_table[location_as_location % 4294967296] = {  }; state.location_reference_as_unique_location_in_party_location_table[location_as_location % 4294967296][id] = value; end
	state.party_location_link_location_from_location_table[id] = location_as_location % 4294967296

	return id + state.party_location_generation[id] * 4294967296

end

