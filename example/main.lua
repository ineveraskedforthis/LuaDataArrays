print("LLDA test")

print("start")

require "output.location"
require "output.party"
require "output.party_location"

---@type data_arrays
local state = {}

-- move to state creation function
state.location_size = 100
state.party_size = 100
state.party_location_size = 100

state.party_available_id = 0
state.location_available_id = 0
state.party_location_available_id = 0


LOCATION.reserve(state)
PARTY.reserve(state)
PARTY_LOCATION.reserve(state)
print("reserve size")


local new_location = LOCATION.create(state)
local new_party = PARTY.create(state)
local party_location = PARTY_LOCATION.create(state, new_party, new_location)
assert(LOCATION.is_valid(state, new_location))
assert(PARTY.is_valid(state, new_party))
assert(PARTY_LOCATION.is_valid(state, party_location))
print("creation test")


LOCATION.set_danger(state, new_location, 10)
assert(LOCATION.get_danger(state, new_location) == 10)
print("value set test")


LOCATION.delete(state, new_location)
PARTY.delete(state, new_party)
assert(PARTY_LOCATION.is_valid(state, party_location) == false)
print("deletion test")

