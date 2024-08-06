Require Import PrimInt63 NArith Ascii List String.

Require Import Vim.Helpers.

Import ListNotations.
Open Scope char_scope.

Inductive error : Type :=
| CouldntReadFile : list ascii -> error
| CouldntWriteToFile : list ascii -> error
| UnsavedFile : error.

Definition string_of_error (e : error) : list ascii :=
  match e with
  | CouldntReadFile file_name =>
      list_ascii_of_string "Couldn't read file " ++ file_name ++ ["."]
  | CouldntWriteToFile file_name =>
      list_ascii_of_string "Couldn't write to file " ++ file_name ++ ["."]
  | UnsavedFile =>
      list_ascii_of_string "There are unsaved changes in your file."
  end.
