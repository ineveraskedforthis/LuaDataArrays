namespace Pure

inductive word_size where
  | w1 : word_size
  | w2 : word_size
  | w4 : word_size

inductive number_interpretation where
  | signed : number_interpretation
  | unsigned : number_interpretation

inductive data_type where
  | string : data_type
  | bool : data_type
  | number : number_interpretation → word_size → data_type
  | void : data_type

def int32_t := data_type.number number_interpretation.signed word_size.w4

end Pure


namespace Table

structure field where
  name : String
  column_normal_type : Pure.data_type

structure link where
  name : String
  linked_table : String

structure reference where
  referenced_as : String
  referenced_in : String

structure table where
  name : String
  fields : List field
  links_one : List link
  links_many : List link
  references : List reference

end Table

namespace Language

def god_object_name := "state"
def validity_check_name := "is_valid"
def id_s := "id"

inductive Notion where
  | validity_checker : String → Notion

def namespace_name (x : String) : String := x.toUpper

inductive SupposedType where
  | pure : Pure.data_type → SupposedType
  | alias : String → SupposedType
  | index : SupposedType
  | strong_id : String → SupposedType

inductive GivenName where
  | name : List String → String → GivenName

inductive Thing where
  | term : GivenName → Thing
  | call : Thing → Thing → Thing
  | index : Thing → Thing -> Thing
  | projection : Thing → String → Thing
  | explicit_numerical_value : Int → Thing
  | explicit_boolean_value : Bool → Thing
  | less_or_equal : Thing → Thing → Thing
  | less : Thing → Thing → Thing
  | equal : Thing → Thing → Thing
  | and : Thing → Thing → Thing
  | or : Thing → Thing → Thing
  | list : List Thing → Thing

structure StrongId (table_name : String) where
  var : GivenName := GivenName.name [] s!"{table_name}_id"
  expr := Thing.term var
  internal_id : Thing := Thing.projection expr "internal_id"
  generation : Thing := Thing.projection expr "generation"
  type := SupposedType.strong_id table_name

def ValueName : GivenName := GivenName.name [] "value"
def ValueExpr : Thing := Thing.term ValueName

inductive Instruction where
  | assert : Thing → Instruction
  | assignment : Thing → Thing → Instruction
  | return_value : Thing → Instruction
  | program : List Instruction → Instruction
  | function_declaration :
    GivenName
    → SupposedType → (List (GivenName × SupposedType))
    → Instruction
    → Instruction
  | condition : Thing → Instruction → Instruction → Instruction
  | reserve_pure_array : Thing → Pure.data_type → Thing → Instruction

def validity_checker (table_name : String) : Thing :=
  Thing.term
  (
    GivenName.name
    [namespace_name table_name]
    validity_check_name
  )

structure DataArrays where
  self
    := GivenName.name [] "state"

  self_t
    := SupposedType.alias "data_arrays"

  expr
    := Thing.term (GivenName.name [] god_object_name)

  size (table : String) : Thing
    := Thing.projection expr s!"{table}_size"

  usage_array (table: String) : Thing
    := Thing.projection expr s!"{table}_usage"

  generation_array (table: String) : Thing
    := Thing.projection expr s!"{table}_generation"

  field_array (table: String) (field : String) : Thing
    := Thing.projection expr s!"{table}_data_{field}"

  usage (table: String) (id : StrongId table) : Thing
    := Thing.index (usage_array table) (id.internal_id)

  generation (table: String) (id : StrongId table) : Thing
    := Thing.index (generation_array table) (id.internal_id)

  field (table: String) (field : String) (id : StrongId table) : Thing
    := Thing.index (field_array table field) (id.internal_id)



def Validity (table_name : String) (id : StrongId table_name) : Thing :=
  Thing.call (validity_checker table_name) (Thing.list [id.expr])

def IsValid (data : DataArrays) (table_name : String) (id : StrongId table_name) : Instruction :=
  let in_bounds := Thing.less id.internal_id (data.size table_name)
  let is_fresh := Thing.equal id.generation (data.generation table_name id)
  Instruction.program [
    Instruction.condition
      in_bounds
      (Instruction.return_value (Thing.and in_bounds is_fresh))
      (Instruction.return_value (Thing.explicit_boolean_value False))
  ]

def IsValidFunc (data : DataArrays) (table_name : String) (id : StrongId table_name) : Instruction :=
  Instruction.function_declaration
    (GivenName.name [namespace_name table_name] validity_check_name)
    (SupposedType.pure Pure.data_type.bool)
    [
      ⟨ data.self, data.self_t ⟩,
      ⟨ id.var, id.type ⟩
    ]
    (IsValid data table_name id)

def AccessFieldFunc (data : DataArrays) (table_name : String) (id : StrongId table_name) (field : Table.field) : Instruction :=
  Instruction.function_declaration
    (GivenName.name [namespace_name table_name] ("get_" ++ field.name))
    (SupposedType.pure field.column_normal_type)
    [
      ⟨ data.self, data.self_t ⟩,
      ⟨ id.var, id.type ⟩
    ]
    (
      Instruction.program
      [
        Instruction.assert (Validity table_name id),
        Instruction.return_value (data.field table_name field.name id)
      ]
    )

def ChangeFieldFunc (data : DataArrays) (table_name : String) (id : StrongId table_name) (field : Table.field) : Instruction :=
  Instruction.function_declaration
    (GivenName.name [namespace_name table_name] ("set_" ++ field.name))
    (SupposedType.pure Pure.data_type.void)
    [
      ⟨ data.self, data.self_t ⟩,
      ⟨ id.var, id.type ⟩,
      ⟨ ValueName, SupposedType.pure field.column_normal_type ⟩
    ]
    (
      Instruction.program
      [
        Instruction.assert (Validity table_name id),
        Instruction.assignment (data.field table_name field.name id) ValueExpr
      ]
    )

def SetSizeFunc (data : DataArrays) (table_name : String) : Instruction :=
  Instruction.function_declaration
    (GivenName.name [namespace_name table_name] ("resize"))
    (SupposedType.pure Pure.data_type.void)
    [
      ⟨ data.self, data.self_t ⟩,
      ⟨ ValueName, SupposedType.pure (Pure.data_type.number Pure.number_interpretation.signed Pure.word_size.w4) ⟩
    ]
    (
      Instruction.program
      [
        Instruction.assignment (data.size table_name) ValueExpr
      ]
    )

def ReserveArraysFunc (data : DataArrays) (table : Table.table) : Instruction :=
  Instruction.function_declaration
    (GivenName.name [namespace_name table.name] ("reserve"))
    (SupposedType.pure Pure.data_type.void)
    [
      ⟨ data.self, data.self_t ⟩
    ]
    (
      Instruction.program
      [
        Instruction.reserve_pure_array (data.usage_array table.name) Pure.int32_t (data.size table.name),
        Instruction.reserve_pure_array (data.generation_array table.name) Pure.int32_t (data.size table.name)
      ]
    )

def Language := (indent : String) → (i : Instruction) → String

def Translate (t: Table.table) (l: Language) : String :=
  let state : DataArrays := {}
  let id : StrongId t.name := {}

  let l' := l ""

  l' (Instruction.program [ReserveArraysFunc state t])
  ++
  l' (Instruction.program [IsValidFunc state t.name id])
  ++
  l' (Instruction.program (t.fields.map (AccessFieldFunc state t.name id)))
  ++
  l' (Instruction.program (t.fields.map (ChangeFieldFunc state t.name id)))

end Language
