import Std.Data.HashSet

import LeanLuaDataArrays


def merge_IO_lists (list : List (IO (List α))) : IO (List α) := do
  match list with
  | a :: rest =>
    let a' ← a
    let result' ← merge_IO_lists rest
    pure (a' ++ result')
  | [] =>
    pure []

def commute_IO (list : List (IO α)) : IO (List α) := do
  match list with
  | a :: rest =>
    let a' ← a
    let result' ← commute_IO rest
    pure (a' :: result')
  | [] =>
    pure []

def merge_lists (list : List ((List α))) : (List α) :=
  match list with
  | a :: rest =>
    (a ++ merge_lists rest)
  | [] =>
    []

def append_fields_from_tokens
  (fields : List Table.field)
  (data : List String)
    :
  List Table.field
    :=
  match data with
  | name :: raw_type :: data =>
    match Pure.str_to_data_type raw_type with
    | some pure_type => append_fields_from_tokens (⟨name, pure_type⟩ :: fields) data
    | none => fields
  | _ => fields

def append_links_from_tokens
  (links : List Table.link)
  (data : List String)
    :
  List Table.link
    :=
  match data with
  | name :: foreign_table :: data =>
    append_links_from_tokens (⟨name, foreign_table⟩ :: links) data
  | _ => links

def split_text
  (text : String)
    :
  List String
    :=
  (String.split text Char.isWhitespace).filter fun (token : String) ↦ String.length token > 0

def split_named_text
  (text : String × String)
    :
  String × (List String)
    :=
  ⟨ text.1 , text.2 |> split_text ⟩

def get_text (path : System.FilePath) (file : String) : IO String := do
  let cur_path := path.join file
  let path_exists ← cur_path.pathExists
  match path_exists with
    | Bool.true => IO.FS.readFile cur_path
    | Bool.false => pure ""

def get_text_dir (path : IO.FS.DirEntry) (file : String) : IO (Option (String × String)) := do
  let cur_path := path.path.join file
  let path_exists ← cur_path.pathExists
  match path_exists with
    | Bool.true => do
      let text ← IO.FS.readFile cur_path
      pure (some ⟨ path.fileName, text ⟩)
    | Bool.false => pure none

def get_relevant_references (relevant_table : String) (referenced_in : String) (text: List String) : List Table.reference :=
  match text with
  | name :: table :: data =>
    if table = relevant_table then
      ⟨name, referenced_in⟩ :: get_relevant_references relevant_table referenced_in data
    else
      get_relevant_references relevant_table referenced_in data
  | _ => []

def extract_references_from_list (relevant_table : String) (data : List (String × List String)) : List Table.reference :=
  match data with
  | item :: data => get_relevant_references relevant_table item.1 item.2 ++ extract_references_from_list relevant_table data
  | _ => []

def filter_valid_options (l : List (Option α)) : List α :=
  match l with
  | item :: l =>
    match item with
    | some data => data :: filter_valid_options l
    | none => filter_valid_options l
  | _ => []

def get_table (main_folder : System.FilePath) (current_folder : System.FilePath) : IO (Option Table.table) := do
  let path_exists ← current_folder.pathExists
  match path_exists with
  | Bool.false => pure none
  | Bool.true =>
    match current_folder.fileName with
    | none => pure none
    | some name =>
      let fields_text ← get_text current_folder "fields"
      let link_one_text ← get_text current_folder "link_one"
      let link_many_text ← get_text current_folder "link_many"

      let local_files ← main_folder.readDir
      let reference_one ←
        local_files
        |>.map (get_text_dir . "link_one")
        |>.toList
        |> commute_IO

      let reference_many ←
        local_files
        |>.map (get_text_dir . "link_many")
        |>.toList
        |> commute_IO

      let reference_one_parsed := reference_one |> filter_valid_options |>.map split_named_text
      let reference_many_parsed := reference_many |> filter_valid_options |>.map split_named_text

      ⟨
        name,
        fields_text |> split_text |> append_fields_from_tokens [],
        link_one_text |> split_text |> append_links_from_tokens [],
        link_many_text |> split_text |> append_links_from_tokens [],
        extract_references_from_list name reference_one_parsed,
        extract_references_from_list name reference_many_parsed
      ⟩ |> some |> pure


def process_command (exitCode : UInt32) (args: List String) : IO UInt32 := do
  match args with
  | descriptions_path :: table_name :: target_path :: [] =>
    let main_folder := System.FilePath.mk descriptions_path
    let current_folder := main_folder.join table_name
    let optional_table ← get_table main_folder current_folder
    match optional_table with
    | none =>
      IO.println s!"Error: Wrong arguments count"
      pure 1
    | some table =>
      let text := Language.Translate table AnnotatedLuajit.Compile "\t"
      IO.FS.writeFile ⟨ target_path ⟩ text
      pure exitCode
  | _ =>
    IO.println s!"Error: Wrong arguments count"
    pure 1

def entry_to_table (main_folder : System.FilePath) (entry : IO.FS.DirEntry) : IO (Option Table.table) := do
  -- let entry_good ← entry
  get_table main_folder entry.path

def empty_table (t : Option Table.table) : Bool :=
  match t with
  | none => false
  | some _ => true

def retrieve_field_description (t : IO (Option Table.table)) : IO (List (String × Language.SupposedType)) := do
  let t' ← t
  match t' with
  | none => pure []
  | some table => pure (Language.GodFields table)



def main (args : List String) : IO UInt32 := do
  IO.println s!"Generating Lua code"
  match args with
  | [] =>
    IO.println s!"Error: No file was provided"
    pure 1
  | "table" :: args => process_command 0 args
  | "state" :: main_folder :: target_path :: [] =>
    let folder := System.FilePath.mk main_folder
    let local_files ← folder.readDir
    let god_fields ←
      local_files
      |>.map (entry_to_table main_folder)
      |>.map retrieve_field_description
      |>.toList
      |> merge_IO_lists

    let description := AnnotatedLuajit.Compile "" "" (
      Language.Instruction.structure_definition
        "data_arrays"
        god_fields
    )

    IO.FS.writeFile ⟨ target_path ⟩ (description)
    pure 0
  | _ =>
    IO.println s!"Error: Invalid arguments sequence\n"
    pure 1
