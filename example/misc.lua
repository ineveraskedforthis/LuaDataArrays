local ffi = require "ffi"
ffi.cdef[[
typedef struct {
        int32_t internal_id
        int32_t generation_counter
} strong_id;
]]