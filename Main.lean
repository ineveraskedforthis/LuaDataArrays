import Std.Data.HashSet

import LeanLuaDataArrays


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

def get_text (path : System.FilePath) (file : String) : IO String := do
  let cur_path := path.join file
  let path_exists ← cur_path.pathExists
  match path_exists with
    | Bool.true => IO.FS.readFile cur_path
    | Bool.false => pure ""

def process_command (exitCode : UInt32) (args: List String) : IO UInt32 := do
  match args with
  | descriptions_path :: table_name :: target_path :: [] =>
    let main_folder := System.FilePath.mk descriptions_path
    let current_folder := main_folder.join table_name

    let fields_text ← get_text current_folder "fields"
    -- let size_text ← get_text current_folder "size"
    let link_one_text ← get_text current_folder "link_one"
    let link_many_text ← get_text current_folder "link_many"

    let table : Table.table := ⟨
      table_name,
      fields_text |> split_text |> append_fields_from_tokens [],
      link_one_text |> split_text |> append_links_from_tokens [],
      link_many_text |> split_text |> append_links_from_tokens [],
      [],
      []
    ⟩

    let text := Language.Translate table AnnotatedLuajit.Compile "\t"
    IO.FS.writeFile ⟨ target_path ⟩ text
    pure exitCode
  | _ =>
    IO.println s!"Error: Wrong arguments count"
    pure 1

def main (args : List String) : IO UInt32 := do
  IO.println s!"Generating Lua code"
  match args with
  | [] =>
    IO.println s!"Error: No file was provided"
    pure 1
  | "table" :: args => process_command 0 args
  | "state" :: output_file :: _ =>
    let state_description := "---@class data_arrays\n"
    -- let fields ← state_fields args
    -- let
    IO.FS.writeFile ⟨ output_file⟩ (state_description)
    pure 0
  | _ =>
    IO.println s!"Error: Invalid arguments sequence\n"
    pure 1
