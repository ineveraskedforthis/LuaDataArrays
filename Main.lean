import LeanLuaDataArrays


-- format description
-- %object_name%
-- %field/link% %field_name% %field_type%

def empty_table : String := "{}"
def tb : String := "\t"

inductive value_t where
  | uint8_t : value_t
  | uint16_t : value_t
  | uint32_t : value_t
  | int8_t : value_t
  | int16_t : value_t
  | int32_t : value_t
  | float : value_t

def value_t.convert_to_string (x: value_t) : String :=
  match x with
  | uint8_t     => "uint8_t"
  | uint16_t    => "uint16_t"
  | uint32_t    => "uint32_t"
  | int8_t      => "int8_t"
  | int16_t     => "int16_t"
  | int32_t     => "int32_t"
  | float       => "float"

instance : ToString value_t where
  toString := value_t.convert_to_string

def value_t.fromString (x: String) : Option value_t :=
  match x with
  | "uint8_t"     => uint8_t
  | "uint16_t"    => uint16_t
  | "uint32_t"    => uint32_t
  | "int8_t"      => int8_t
  | "int16_t"     => int16_t
  | "int32_t"     => int32_t
  | "float"       => float
  | _             => Option.none


inductive lua_type where
  | id : String -> lua_type
  | number : lua_type
  | data_arrays : lua_type

def lua_type.convert_to_string (x : lua_type) : String :=
  match x with
  | id name => name ++ "_strong_id"
  | number => "number"
  | data_arrays => "data_arrays"

instance : ToString lua_type where
  toString := lua_type.convert_to_string

def lua_type.fromString (x: String) : lua_type :=
  match x with
  | "uint8_t"     => number
  | "uint16_t"    => number
  | "uint32_t"    => number
  | "int8_t"      => number
  | "int16_t"     => number
  | "int32_t"     => number
  | "float"       => number
  | s             => id s

structure raw_triple where
  column_type : String
  column_name : String
  column_target : String

structure normal_type where
  ffi_type : Option value_t
  lua_type : Option lua_type

structure field where
  name : String
  column_normal_type : normal_type

structure link where
  name : String
  linked_table : String

inductive column_type where
  | link_one : column_type
  | link_many : column_type
  | field : column_type

def column_type_to_str (a: column_type) : String :=
  match a with
  | column_type.field => "field"
  | column_type.link_one => "link_one"
  | column_type.link_many => "link_many"

instance : ToString column_type where
  toString := column_type_to_str

structure table where
  name : String
  fields : List field
  links_one : List link
  links_many : List link

def validate_triples (x : List String) : IO Prop := do
  if x.length = 0 then
    pure True
  else
    if x.length < 3 then
      IO.println s!"Error: Invalid number of tokens"
      pure False
    else
      validate_triples x.tail.tail.tail

def parse_column_type (a : String) : Option column_type :=
  match a with
  | "field" => column_type.field
  | "link_one" => column_type.link_one
  | "link_many" => column_type.link_many
  | _ => none

def table_append_tokens (target : table) (source : List String) : table :=
  match source with
  | a :: name :: c :: source =>
    let optional_column_type := parse_column_type a
    let optional_value_type := value_t.fromString c
    let optional_lua_type := lua_type.fromString c
    match optional_column_type, optional_value_type with
    | some column_type, value_type =>
      match column_type with
      | .field => table_append_tokens ⟨
          target.name,
          target.fields.concat ⟨ name, ⟨value_type, optional_lua_type⟩ ⟩,
          target.links_one,
          target.links_many
        ⟩ source
      | .link_one => table_append_tokens ⟨
          target.name,
          target.fields,
          target.links_one.concat ⟨ name, c ⟩,
          target.links_many
        ⟩ source
      | .link_many => table_append_tokens ⟨
          target.name,
          target.fields,
          target.links_one.concat ⟨ name, c ⟩,
          target.links_many
        ⟩ source
    | _, _ => target
  | _ => target

def tokens_to_table (name: String) (data : List String) : table :=
  let new_table : table := ⟨
    name,
    [],
    [],
    []
  ⟩

  table_append_tokens new_table data

def string_to_table (name_raw : IO String) (x : IO String) : IO table := do
  let name ← name_raw
  let data ← x
  let tokens := (String.split data Char.isWhitespace).filter
    fun (token : String) ↦ String.length token > 0
  pure (tokens_to_table name tokens)

def namespace_name (x : String) : String := x.toUpper

inductive lua_term where
  | var : String -> lua_term

def lua_term.toString (x : lua_term) :=
  match x with
  | var s => s

inductive lua_callable_term where
  | getter: String -> String -> lua_callable_term
  | setter: String -> String -> lua_callable_term

def lua_callable_term.toString (x : lua_callable_term) : String :=
  match x with
  | getter table field_name => namespace_name table ++ ".get_" ++ field_name
  | setter table field_name => namespace_name table ++ ".set_" ++ field_name

structure lua_variable where
  term : lua_term
  type : lua_type

structure lua_function where
  term : lua_callable_term
  params : List lua_variable
  returns : Option lua_type

def params_annotation (x : List lua_variable) : String :=
  match x with
  | [] => ""
  | var :: next =>
    s!"---@param {var.term.toString} {var.type}\n"
    ++ params_annotation next

def return_annotation (x : lua_type) : String :=
  s!"---@returns {x}\n"

def function_annotation (x : lua_function) : String :=
  match x.returns with
  | some return_type => params_annotation x.params ++ return_annotation return_type
  | none => params_annotation x.params

def params_list (x : List lua_variable) : String :=
  match x with
  | [] => ""
  | [y] => y.term.toString
  | y :: x => y.term.toString ++ ", " ++ params_list x

def function_declaration (x : lua_function) : String :=
  "function " ++ x.term.toString ++ "(" ++ params_list x.params ++ ")"

def function_body (x : lua_function) : String :=
  match x.term with
  | lua_callable_term.getter table field =>
    s!"\tassert(state.generation_counter_array_{table}[id.internal_id] == id.generation_counter)\n" ++
    s!"\treturn state.data_array_{table}_{field}[id.internal_id]\n"
  | lua_callable_term.setter table field =>
    s!"\tassert(state.generation_counter_array_{table}[id.internal_id] == id.generation_counter)\n" ++
    s!"\tstate.data_array_{table}_{field}[id.internal_id] = value\n"

def lua_function.convert_to_string (x : lua_function) : String :=
  ""
  ++ function_annotation x
  ++ function_declaration x ++ "\n"
  ++ function_body x
  ++ "end\n"

instance : ToString lua_function where
  toString := lua_function.convert_to_string

inductive lua_code where
  | parameter_annotation : lua_term -> lua_type -> lua_code

def fields_to_lua (table_name : String) (data : List field) : String :=
  match data with
  | [] => ""
  | f :: x =>
    match f.column_normal_type.lua_type with
    | some ltype =>
      let getter : lua_function := ⟨
        lua_callable_term.getter table_name f.name,
        [
          ⟨ lua_term.var "state", lua_type.data_arrays⟩,
          ⟨ lua_term.var "id", lua_type.id table_name ⟩
        ],
        f.column_normal_type.lua_type
      ⟩
      let setter : lua_function := ⟨
        lua_callable_term.setter table_name f.name,
        [
          ⟨ lua_term.var "state", lua_type.data_arrays⟩,
          ⟨ lua_term.var "id", lua_type.id table_name ⟩,
          ⟨ lua_term.var "value", ltype ⟩
        ],
        none
      ⟩
      (
        match f.column_normal_type.ffi_type with
        | some vtype =>
          s!"---@param state data_arrays\n"++
          s!"local function reserve_data_array_{table_name}_{f.name}(state)\n"++
          s!"{tb}state.data_array_{table_name}_{f.name} = ffi.new(\"{vtype}[?]\", state.size_{table_name})\n"++
          s!"end\n"
        | none =>
          ""
      )
      ++ s!"{getter}{setter}"
      ++ fields_to_lua table_name x
    | none => ""

def link_one_to_lua (table_name : String) (data : List link) : String :=
  match data with
  | [] => ""
  | l :: data =>
    s!"---@param state {lua_type.data_arrays}\n" ++
    s!"local function reserve_link_array_{table_name}_{l.linked_table}(state)\n" ++
    s!"{tb}state.data_array_{table_name}_to_{l.linked_table} = ffi.new(\"int32_t[?]\", state.size_{table_name})\n" ++
    s!"{tb}state.data_array_{table_name}_from_{l.linked_table} = ffi.new(\"int32_t[?]\", state.size_{l.linked_table})\n" ++
    s!"end\n"
    ++ link_one_to_lua table_name data

def reserve_link_one (table_name : String) (data : List link) : String :=
  match data with
  | [] => ""
  | l :: data =>
    s!"{tb}reserve_link_array_{table_name}_{l.linked_table}(state)\n"
    ++ reserve_link_one table_name data

def reserve_field (table_name : String) (data : List field) : String :=
  match data with
  | [] => ""
  | f :: data =>
    s!"{tb}reserve_data_array_{table_name}_{f.name}(state)\n"
    ++ reserve_field table_name data

def table_to_lua (data : IO table) : IO String := do
  let table ← data
  pure (
    "local ffi = require(\"ffi\")\n" ++
    s!"{namespace_name table.name} = " ++ "{}\n"
    ++ s!"---@param state data_arrays\n"
    ++ s!"local function reserve_generation_array(state)\n"
    ++ s!"{tb}state.generation_counter_array_{table.name} = ffi.new(\"int32_t[?]\", state.size_{table.name})\n"
    ++ s!"end\n"
    ++ s!"---@class {(lua_type.id table.name)}\n"
    ++ s!"---@field internal_id number\n"
    ++ s!"---@field generation_counter number\n\n"
    ++ fields_to_lua table.name table.fields
    ++ link_one_to_lua table.name table.links_one
    ++ s!"---@param state data_arrays\n"
    ++ s!"function {namespace_name table.name}.reserve(state)\n"
    ++ s!"{tb}reserve_generation_array(state)\n"
    ++ reserve_field table.name table.fields
    ++ reserve_link_one table.name table.links_one
    ++ "end\n"
  )

def process_command (exitCode : UInt32) (args: List String) : IO UInt32 := do
  match args with
  | table_name_filename :: input_filename :: output_filename :: _ =>
    let table_name := IO.FS.readFile table_name_filename
    let text := IO.FS.readFile input_filename
    let table := table_to_lua (string_to_table table_name text)
    let result ← table
    IO.FS.writeFile ⟨ output_filename⟩ result
    pure exitCode
  | _ =>
    IO.println s!"Error: Wrong arguments count"
    pure 1

def append_state_property_fields (table_name : String) (fields : List field) : String :=
  match fields with
  | f :: fields =>
    s!"---@field data_array_{table_name}_{f.name} number[]\n"
    ++ append_state_property_fields table_name fields
  | _ => ""

def append_state_property_link_one (table_name : String) (links : List link) : String :=
  match links with
  | l :: links =>
    s!"---@field data_array_{table_name}_to_{l.name} number[]\n"++
    s!"---@field data_array_{table_name}_from_{l.name} number[]\n"++
    append_state_property_link_one table_name links
  | _ => ""


def state_fields (args: List String) : IO String := do
  match args with
  | table_name_filename :: input_filename :: args =>
    let table_name := IO.FS.readFile table_name_filename
    let text := IO.FS.readFile input_filename
    let table ← string_to_table table_name text
    let result : String :=
      s!"---@field generation_counter_array_{table.name} number[]\n"++
      s!"---@field size_{table.name} number\n"++
      append_state_property_fields table.name table.fields ++
      append_state_property_link_one table.name table.links_one
    let next_result ← state_fields args
    pure (result ++ next_result)
  | _ =>
    pure ""

def main (args : List String) : IO UInt32 := do
  IO.println s!"Generating Lua code"
  match args with
  | [] =>
    IO.println s!"Error: No file was provided"
    pure 1
  | "table" :: args => process_command 0 args
  | "state" :: output_file :: args =>
    let state_description := "---@class data_arrays\n"
    let fields ← state_fields args
    IO.FS.writeFile ⟨ output_file⟩ (state_description ++ fields)
    pure 0
  | _ =>
    IO.println s!"Error: Invalid arguments sequence"
    pure 1
