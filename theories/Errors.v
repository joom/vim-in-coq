Require Import PrimInt63 NArith Ascii List String.

Require Import Vim.Helpers.

Import ListNotations.
Open Scope char_scope.

Inductive error : Type :=
| NoSuchFile : list ascii -> error
| UnsavedFile : error.

Definition string_of_error (e : error) : list ascii :=
  match e with
  | NoSuchFile file_name =>
      list_ascii_of_string "There is no file named " ++ file_name ++ ["."]
  | UnsavedFile =>
      list_ascii_of_string "There are unsaved changes in your file."
  end.
