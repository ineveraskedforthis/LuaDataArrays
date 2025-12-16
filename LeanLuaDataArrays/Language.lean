namespace Pure

inductive word_size where
  | w1 : word_size
  | w2 : word_size
  | w4 : word_size
  | w8 : word_size

inductive number_interpretation where
  | signed : number_interpretation
  | unsigned : number_interpretation

inductive data_type where
  | string : data_type
  | bool : data_type
  | number : number_interpretation → word_size → data_type
  | void : data_type

def id_raw_type := data_type.number number_interpretation.signed word_size.w8

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
  references_one : List reference
  references_many : List reference

def link_to_reference
  (origin : table) (l : link) : reference :=
  ⟨ l.name, origin.name ⟩

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
  | index : (array : Thing) → (index: Thing) -> Thing
  | projection : Thing → String → Thing
  | explicit_numerical_value : Int → Thing
  | explicit_boolean_value : Bool → Thing
  | less_or_equal : Thing → Thing → Thing
  | less : Thing → Thing → Thing
  | equal : Thing → Thing → Thing
  | and : Thing → Thing → Thing
  | or : Thing → Thing → Thing
  | list : List Thing → Thing
  | inc : Thing → Thing
  | strong_id : (index : Thing) → (generation : Thing) → Thing
  | generation_from_strong_id : (strong_id : Thing) → Thing
  | id_from_strong_id : (strong_id : Thing) → Thing
  | exists_in_one_to_one_map : (map_ref : Thing) → (item : Thing) → Thing
  | retrieve_from_one_to_one_map : (map_ref : Thing) → (item : Thing) → Thing
  | empty_collection : Thing

structure StrongId (table_name : String) (name : String) where
  var : GivenName := GivenName.name [] name
  expr := Thing.term var
  internal_id : Thing := Thing.id_from_strong_id expr
  generation : Thing := Thing.generation_from_strong_id expr
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
  | condition : (condition: Thing) → (then_do: Instruction) → (else_do: Instruction) → Instruction
  | condition_then : (condition: Thing) → (then_do: Instruction) → Instruction
  | reserve_pure_array : Thing → Pure.data_type → Thing → Instruction
  | reserve_one_to_one_id_map : Thing → Instruction
  | reserve_one_to_many_id_map : Thing → Instruction
  | loop_while : (condition : Thing) → (body : Instruction) → Instruction
  | set_one_to_one_map : (map_ref : Thing) → (key : Thing) → (value : Thing) → Instruction
  | set_one_to_many_map : (map_ref : Thing) → (key : Thing) → (value : Thing) → Instruction
  | remove_from_one_to_one_map : (map_ref : Thing) → (key : Thing) → Instruction
  | remove_from_one_to_many_map : (map_ref : Thing) → (key : Thing) → (value : Thing) → Instruction
  | trivial_statement : Thing → Instruction
  | copy_many_map_collection: (target : Thing) → (origin : Thing) → (key : Thing) → Instruction
  | for_each : (collection : Thing) → (iterator : Thing) → (action : Instruction) → Instruction

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

  available_id (table : String) : Thing
    := Thing.projection expr s!"{table}_available_id"

  usage_array (table: String) : Thing
    := Thing.projection expr s!"{table}_usage"

  generation_array (table: String) : Thing
    := Thing.projection expr s!"{table}_generation"

  field_array (table: String) (field : String) : Thing
    := Thing.projection expr s!"{table}_data_{field}"

  link_array (table: String) (link_name : String) (linked_table : String) : Thing
    := Thing.projection expr s!"{table}_link_{link_name}_from_{linked_table}_table"

  reference_one_map (table: String) (ref : Table.reference) : Thing
    := Thing.projection expr s!"{table}_reference_as_unique_{ref.referenced_as}_in_{ref.referenced_in}_table"

  reference_many_map (table: String) (ref : Table.reference) : Thing
    := Thing.projection expr s!"{table}_referenced_as_one_of_{ref.referenced_as}_in_{ref.referenced_in}_table"

  usage (table: String) (id : StrongId table id_name) : Thing
    := Thing.index (usage_array table) (id.internal_id)

  generation (table: String) (id : StrongId table id_name) : Thing
    := Thing.index (generation_array table) (id.internal_id)

  field (table: String) (field : String) (id : StrongId table id_name) : Thing
    := Thing.index (field_array table field) (id.internal_id)

  delete (table: String) : Thing
    := Thing.projection expr s!"{table}_delete"

  delete_weak (table: String) : Thing
    := Thing.projection expr s!"{table}_delete_weak"


def Validity (table_name : String) (id : StrongId table_name id_name) : Thing :=
  Thing.call (validity_checker table_name) (Thing.list [id.expr])

def IsValid (data : DataArrays) (table_name : String) (id : StrongId table_name s!"{table_name}_id") : Instruction :=
  let in_bounds := Thing.and
    (Thing.less id.internal_id (data.size table_name))
    (Thing.less_or_equal (Thing.explicit_numerical_value 0) id.internal_id)
  let is_fresh := Thing.equal id.generation (data.generation table_name id)
  Instruction.program [
    Instruction.condition
      in_bounds
      (Instruction.return_value (Thing.and in_bounds is_fresh))
      (Instruction.return_value (Thing.explicit_boolean_value False))
  ]

def IsValidFunc (data : DataArrays) (table_name : String) (id : StrongId table_name s!"{table_name}_id") : Instruction :=
  Instruction.function_declaration
    (GivenName.name [namespace_name table_name] validity_check_name)
    (SupposedType.pure Pure.data_type.bool)
    [
      ⟨ data.self, data.self_t ⟩,
      ⟨ id.var, id.type ⟩
    ]
    (IsValid data table_name id)

def AccessFieldFunc (data : DataArrays) (table_name : String) (id : StrongId table_name s!"{table_name}_id") (field : Table.field) : Instruction :=
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

def ChangeFieldFunc (data : DataArrays) (table_name : String) (id : StrongId table_name s!"{table_name}_id") (field : Table.field) : Instruction :=
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

def LinkVarName
  (link: Table.link)
    :
  String
    :=
  s! "{link.linked_table}_as_{link.name}"

def ConvertLinkToFuncInput
  (link: Table.link)
    :
  GivenName × SupposedType
    :=
  ⟨ link |> LinkVarName |> GivenName.name [], SupposedType.strong_id link.linked_table ⟩

def DeleteRelationFunc
  (data: DataArrays)
  (table: Table.table)
  (id: StrongId table.name id_name )
    :
  Instruction
    :=
  let gen := data.generation table.name id

  let clear_field
    (field : Table.field)
      :
    Instruction
      :=
    Instruction.assignment (data.field table.name field.name id) (Thing.explicit_numerical_value 0)

  let clear_link_one
    (link : Table.link)
      :
    Instruction
      :=
    let link_array := data.link_array table.name link.name link.linked_table
    let link_array_location := Thing.index link_array id.internal_id
    Instruction.program [
      Instruction.remove_from_one_to_one_map
        (
          data.reference_one_map
            link.linked_table
            (Table.link_to_reference table link)
        )
        link_array_location,
      Instruction.assignment link_array_location (Thing.explicit_numerical_value 0)
    ]

  let clear_link_many
    (link : Table.link)
      :
    Instruction
      :=
    let link_array := data.link_array table.name link.name link.linked_table
    let link_array_location := Thing.index link_array id.internal_id
    Instruction.program [
      Instruction.remove_from_one_to_many_map
        (
          data.reference_one_map
            link.linked_table
            (Table.link_to_reference table link)
        )
        link_array_location
        id.internal_id,
      Instruction.assignment (data.link_array table.name link.name link.linked_table) (Thing.explicit_numerical_value 0)
    ]

  let clear_ref_one
    (ref : Table.reference)
      :
    Instruction
      :=
    let ref_map := data.reference_one_map table.name ref
    let ref_id := Thing.retrieve_from_one_to_one_map ref_map id.internal_id
    Instruction.trivial_statement
      ( Thing.call (data.delete ref.referenced_in) ref_id)

  let clear_ref_many
    (ref : Table.reference)
      :
    Instruction
      :=
    let ref_map := data.reference_many_map table.name ref
    let temp_collection := Thing.term (GivenName.name [] "temp_container")
    let it := Thing.term (GivenName.name [] "iterator")
    Instruction.program [
      Instruction.assignment temp_collection Thing.empty_collection,
      Instruction.copy_many_map_collection temp_collection ref_map id.internal_id,
      Instruction.for_each temp_collection it (
        Instruction.trivial_statement
          ( Thing.call (data.delete_weak ref.referenced_in) it)
      )
    ]


  Instruction.function_declaration
    (GivenName.name [namespace_name table.name] ("delete"))
    (SupposedType.pure Pure.data_type.void)
    [
      ⟨ data.self, data.self_t ⟩,
      ⟨ id.var, id.type ⟩,
    ]
    (
      Instruction.program (
        [
          Instruction.assert (Validity table.name id),
          Instruction.assignment gen (Thing.inc gen)
        ]
        ++ table.fields.map clear_field
        ++ table.links_one.map clear_link_one
        ++ table.links_many.map clear_link_many
        ++ table.references_one.map clear_ref_one
        ++ table.references_many.map clear_ref_many
      )
    )

def CreateRelationFunc
  (data: DataArrays)
  (table: Table.table)
    :
  Instruction
    :=
  let temp_variable := Thing.term (GivenName.name [] "id")
  let available := data.available_id table.name
  let usage_array := data.usage_array table.name
  let generation_array := data.generation_array table.name
  let usage_count := Thing.index usage_array temp_variable
  let generation := Thing.index generation_array temp_variable
  let not_valid_available_index := Thing.less (Thing.explicit_numerical_value 0) usage_count
  let inputs := (table.links_one ++ table.links_many).map ConvertLinkToFuncInput

  let UpdateLinkOneData
    (link: Table.link)
      :
    Instruction
      :=
    let id : StrongId link.linked_table (LinkVarName link) := {}
    let ref := Table.link_to_reference table link
    let ref_map := data.reference_one_map link.linked_table ref
    let link_array := data.link_array table.name link.name link.linked_table
    let link_location_in_array := Thing.index link_array temp_variable
    Instruction.program [
      Instruction.assert (Validity link.linked_table id),
      Instruction.condition_then
        (Thing.exists_in_one_to_one_map ref_map id.internal_id)
        (
          Instruction.trivial_statement
            (Thing.call (data.delete_weak table.name) (Thing.retrieve_from_one_to_one_map ref_map id.internal_id) )
        ),
      Instruction.set_one_to_one_map ref_map id.internal_id temp_variable,
      Instruction.assignment link_location_in_array id.internal_id
    ]

  let UpdateLinkManyData
    (link: Table.link)
      :
    Instruction
      :=
    let id : StrongId link.linked_table (LinkVarName link) := {}
    let ref := Table.link_to_reference table link
    let ref_map := data.reference_one_map link.linked_table ref
    let link_array := data.link_array table.name link.name link.linked_table
    let link_location_in_array := Thing.index link_array temp_variable
    Instruction.program [
      Instruction.assert (Validity link.linked_table id),
      Instruction.set_one_to_many_map ref_map id.internal_id temp_variable,
      Instruction.assignment link_location_in_array id.internal_id
    ]

  Instruction.function_declaration
    (GivenName.name [namespace_name table.name] ("create"))
    (SupposedType.strong_id table.name)
    (
      [
        ⟨ data.self, data.self_t ⟩
      ]
      ++
      inputs
    )
    (
      Instruction.program ([
        -- store index
        Instruction.assignment temp_variable available,
        -- update usage
        Instruction.assignment usage_count (Thing.explicit_numerical_value 0),
        -- update index
        (
          Instruction.loop_while
          not_valid_available_index
          (Instruction.program [
            Instruction.assert (Thing.less available (data.size table.name)),
            Instruction.assignment available (Thing.inc available)
          ])
        ),
      ]
      -- update linked objects
      ++
      table.links_one.map UpdateLinkOneData
      ++
      table.links_many.map UpdateLinkManyData
      ++
      [
        -- return new strong id
        Instruction.return_value (Thing.strong_id temp_variable generation)
      ])
    )

def ReserveField (data : DataArrays) (table : Table.table) (field: Table.field) : Instruction :=
  let field_symbol := data.field_array table.name field.name
  let field_size := data.size table.name
  Instruction.reserve_pure_array field_symbol field.column_normal_type field_size

def ReserveLink (data: DataArrays) (table : Table.table) (link : Table.link) : Instruction :=
  let link_symbol := data.link_array table.name link.name link.linked_table
  Instruction.reserve_pure_array link_symbol Pure.id_raw_type (data.size table.name)

def ReserveLinkedInOne (data: DataArrays) (table : Table.table) (link : Table.reference) : Instruction :=
  let reference_symbol := data.reference_one_map table.name link
  Instruction.reserve_one_to_one_id_map reference_symbol

def ReserveLinkedInMany (data: DataArrays) (table : Table.table) (link : Table.reference) : Instruction :=
  let reference_symbol := data.reference_one_map table.name link
  Instruction.reserve_one_to_many_id_map reference_symbol

def ReserveArraysFunc (data : DataArrays) (table : Table.table) : Instruction :=
  Instruction.function_declaration
    (GivenName.name [namespace_name table.name] ("reserve"))
    (SupposedType.pure Pure.data_type.void)
    [
      ⟨ data.self, data.self_t ⟩
    ]
    (
      Instruction.program
      (
        [
          Instruction.reserve_pure_array
            (data.usage_array table.name)
            Pure.id_raw_type (data.size table.name),
          Instruction.reserve_pure_array (data.generation_array table.name) Pure.id_raw_type (data.size table.name)
        ]
        ++
        table.fields.map (ReserveField data table)
        ++
        table.links_one.map (ReserveLink data table)
        ++
        table.links_many.map (ReserveLink data table)
        ++
        table.references_one.map (ReserveLinkedInOne data table)
        ++
        table.references_many.map (ReserveLinkedInMany data table)
      )
    )

def Language := (indent : String) → (i : Instruction) → String

def Translate (t: Table.table) (l: Language) : String :=
  let state : DataArrays := {}
  let id : StrongId t.name s!"{t.name}_id" := {}

  let l' := l ""

  l' (Instruction.program [ReserveArraysFunc state t])
  ++
  l' (Instruction.program [IsValidFunc state t.name id])
  ++
  l' (Instruction.program (t.fields.map (AccessFieldFunc state t.name id)))
  ++
  l' (Instruction.program (t.fields.map (ChangeFieldFunc state t.name id)))
  ++
  l' (Instruction.program [CreateRelationFunc state t])

end Language
