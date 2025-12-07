import LeanLuaDataArrays.Language

namespace AnnotatedLuajit

open Language


inductive ffi_type where
  | uint8_t : ffi_type
  | uint16_t : ffi_type
  | uint32_t : ffi_type
  | int8_t : ffi_type
  | int16_t : ffi_type
  | int32_t : ffi_type
  | float : ffi_type
  | bool : ffi_type

def ffi_type.convert_to_string (x: ffi_type) : String :=
  match x with
  | uint8_t     => "uint8_t"
  | uint16_t    => "uint16_t"
  | uint32_t    => "uint32_t"
  | int8_t      => "int8_t"
  | int16_t     => "int16_t"
  | int32_t     => "int32_t"
  | float       => "float"
  | bool        => "bool"


instance : ToString ffi_type where
  toString := ffi_type.convert_to_string

def ffi_type.fromString (x: String) : Option ffi_type :=
  match x with
  | "uint8_t"     => uint8_t
  | "uint16_t"    => uint16_t
  | "uint32_t"    => uint32_t
  | "int8_t"      => int8_t
  | "int16_t"     => int16_t
  | "int32_t"     => int32_t
  | "float"       => float
  | "bool"        => bool
  | _             => Option.none

theorem FFI_string_conversion_is_valid (x : ffi_type) : (ffi_type.fromString x.convert_to_string) = x := by
  cases x
  repeat rfl


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

def ConvertTypeLua (t : SupposedType) : String :=
  match t with
  | SupposedType.index => "number"
  | SupposedType.alias name => name
  | SupposedType.strong_id table => table ++ "_strong_id"
  | SupposedType.pure pure_type =>
    match pure_type with
    | Pure.data_type.bool => "boolean"
    | Pure.data_type.number .. => "number"
    | Pure.data_type.string => "string"
    | Pure.data_type.void => "error_type"

def ConvertTypeFFI (pure_type : Pure.data_type) : Option ffi_type :=
  match pure_type with
  | Pure.data_type.bool => ffi_type.bool
  | Pure.data_type.number interpretation size =>
    match interpretation with
    | Pure.number_interpretation.signed =>
      match size with
      | Pure.word_size.w1 => ffi_type.int8_t
      | Pure.word_size.w2 => ffi_type.int16_t
      | Pure.word_size.w4 => ffi_type.int32_t
    | Pure.number_interpretation.unsigned =>
      match size with
      | Pure.word_size.w1 => ffi_type.uint8_t
      | Pure.word_size.w2 => ffi_type.uint16_t
      | Pure.word_size.w4 => ffi_type.uint32_t
  | Pure.data_type.string => none
  | Pure.data_type.void => none

def ResolveNamespace (n : List String) : String :=
  match n with
  | item :: n => item ++ "." ++ ResolveNamespace n
  | [] => ""

def ResolveName (n : GivenName) : String :=
  match n with
  | GivenName.name namespace_chain name => ResolveNamespace namespace_chain ++ name

def Signify (t : Thing) : String :=
  match t with
  | Thing.and a b => s!"({Signify a} and {Signify b})"
  | Thing.or a b => s!"({Signify a} and {Signify b})"
  | Thing.call f l => s!"{Signify f}({Signify l})"
  | Thing.equal a b => s!"({Signify a} == {Signify b})"
  | Thing.explicit_boolean_value p =>
    match p with
    | Bool.true => "true"
    | Bool.false => "false"
  | Thing.explicit_numerical_value a => s!"{a}"
  | Thing.index a b => s!"{Signify a}[{Signify b}]"
  | Thing.less a b => s!"({Signify a} < {Signify b})"
  | Thing.less_or_equal a b => s!"({Signify a} <= {Signify b})"
  | Thing.list l =>
    match l with
    | [] => ""
    | [a] => s!"{Signify a}"
    | a :: l => s!"{Signify a}, {Signify (Thing.list l)}"
  | Thing.projection a s => s!"{Signify a}.{s}"
  | Thing.term a => ResolveName a

def ResolveParamTypes (params: List (GivenName × SupposedType)) :=
  match params with
  | [] => ""
  | ⟨var, var_t⟩ :: params =>
    (
      match var with
      | GivenName.name _ name => s!"---@param {name} {ConvertTypeLua var_t}\n"
    )
    ++ ResolveParamTypes params

def ResolveParams (params: List (GivenName × SupposedType)) :=
  match params with
  | [] => ""
  | [⟨var, _⟩] =>
    match var with
    | GivenName.name _ name => name
  | ⟨var, _⟩ :: params =>
    match var with
    | GivenName.name _ name => name ++ ", " ++ ResolveParams params

def JoinLines (lines : List String) :=
  match lines with
  | [] => ""
  | line :: lines => s!"{line}\n" ++ JoinLines lines

def Compile (tb : String) (indent : String) (i : Instruction) : String :=
  match i with
  | Instruction.return_value e => s!"{indent}return {Signify e}\n"

  | Instruction.assert e => s!"{indent}assert({Signify e})\n"

  | Instruction.condition a b c =>
    s!"{indent}if {Signify a} then\n"
    ++(Compile tb s!"{indent}{tb}" b)
    ++"{indent}else\n"
    ++(Compile tb s!"{indent}{tb}" c)

  | Instruction.assignment a b => s!"{Signify a} = {Signify b}"

  | Instruction.function_declaration name out_type params body =>
    match out_type with
    | SupposedType.pure Pure.data_type.void =>
      ResolveParamTypes params
      ++ s!"{indent}function {ResolveName name}({ResolveParams params})\n"
      ++ Compile tb s!"{indent}{tb}" body
      ++ s!"end\n"
    | _ =>
      ResolveParamTypes params
      ++ s! "---@returns {ConvertTypeLua out_type}"
      ++ s!"{indent}function {ResolveName name}({ResolveParams params})\n"
      ++ Compile tb s!"{indent}{tb}" body
      ++ s!"end\n"

  | Instruction.program p => JoinLines (p.map (Compile tb indent))

  | Instruction.reserve_pure_array array data_type size =>
    let ffi_type := ConvertTypeFFI data_type
    match ffi_type with
    | none => ""
    | some x =>
      s!"{Signify array} = ffi.new(\"{x}[?]\", {Signify size})"


end AnnotatedLuajit
