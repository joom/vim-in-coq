From CertiCoq.Plugin Require Import CertiCoq.
Require Import PrimInt63 NArith Ascii.

Require Import Vim.Errors.

Axiom N_of_int : int -> N.
Axiom int_of_N : N -> int.

CertiCoq Register [
    N_of_int => "n_of_int" with tinfo,
    int_of_N => "int_of_n" ]
  Include [ "foreign.h" ].

Definition ascii_of_int (i : int) : ascii := ascii_of_N (N_of_int i).
Definition int_of_ascii (a : ascii) : int := int_of_N (N_of_ascii a).
Definition nat_of_int (i : int) : nat := nat_of_N (N_of_int i).
Definition int_of_nat (n : nat) : int := int_of_N (N_of_nat n).

Inductive exit_status :=
| success : exit_status
| failure : exit_status.

Inductive color :=
  black | blue | green | cyan | red | magenta | yellow | white | 
  bright_black | bright_blue | bright_green | bright_cyan | bright_red |
  bright_magenta | bright_yellow | bright_white.

Module Type Effects.
  Parameter M : Type -> Type.
  Parameter pure : forall {A}, A -> M A.
  Parameter bind : forall {A B}, M A -> (A -> M B) -> M B.
  Parameter exit : exit_status -> M unit.
  Parameter window : Type.
  Parameter style : Type.
  Parameter new_window : M window.
  Parameter close_window : window -> M unit.
  Parameter move_cursor : window -> forall (row : int) (col : int), M unit.
  Parameter get_cursor : window -> M (int * int).
  Parameter get_size : window -> M (int * int).
  Parameter print : window -> list ascii -> M unit.
  Parameter make_style : forall (foreground background : color), M style.
  Parameter set_window_default_style : window -> style -> M unit.
  Parameter start_style : style -> M unit.
  Parameter end_style : style -> M unit.
  Parameter refresh : window -> M unit.
  Parameter clear : window -> M unit.
  Parameter get_char : window -> M int.
  Parameter read_file : list ascii -> M (sum error (list ascii)).
  Parameter write_to_file : forall (file_name content : list ascii), M (option error).
End Effects.

Module C <: Effects.
  Axiom window : Type.
  Axiom style : Type.

  CoInductive MI : Type -> Type :=
  | pureI : forall {A}, A -> MI A
  | bindI : forall {A B}, MI A -> (A -> MI B) -> MI B
  | exitI : exit_status -> MI unit
  | new_windowI : MI window
  | close_windowI : window -> MI unit
  | move_cursorI : window -> forall (row : int) (col : int), MI unit
  | get_cursorI : window -> MI (int * int)
  | get_sizeI : window -> MI (int * int)
  | printI : window -> list ascii -> MI unit
  | make_styleI : forall (foreground background : color), MI style
  | set_window_default_styleI : window -> style -> MI unit
  | start_styleI : style -> MI unit
  | end_styleI : style -> MI unit
  | refreshI : window -> MI unit
  | clearI : window -> MI unit
  | get_charI : window -> MI int
  | read_fileI : list ascii -> MI (sum error (list ascii))
  | write_to_fileI : forall (file_name content : list ascii), MI (option error).

  Definition M := MI.
  Definition pure : forall {A}, A -> M A := @pureI.
  Definition bind : forall {A B}, M A -> (A -> M B) -> M B := @bindI.
  Definition exit : exit_status -> M unit := @exitI.
  Definition new_window : M window := @new_windowI.
  Definition close_window : window -> M unit := @close_windowI.
  Definition move_cursor : window -> forall (row : int) (col : int), M unit := @move_cursorI.
  Definition get_cursor : window -> M (int * int) := @get_cursorI.
  Definition get_size : window -> M (int * int) := @get_sizeI.
  Definition print : window -> list ascii -> M unit := @printI.
  Definition make_style : forall (foreground background : color), M style := @make_styleI.
  Definition set_window_default_style : window -> style -> M unit := @set_window_default_styleI.
  Definition start_style : style -> M unit := @start_styleI.
  Definition end_style : style -> M unit := @end_styleI.
  Definition refresh : window -> M unit := @refreshI.
  Definition clear : window -> M unit := @clearI.
  Definition get_char : window -> M int := @get_charI.
  Definition read_file : list ascii -> M (sum error (list ascii)) := @read_fileI.
  Definition write_to_file : forall (file_name content : list ascii), M (option error) := @write_to_fileI.
End C.

Notation "e1 ;; e2" :=
  (@C.bind _ _ e1 (fun _ => e2)) (at level 61, right associativity).
Notation "x <- c1 ;; c2" :=
  (@C.bind _ _ c1 (fun x => c2)) (at level 61, c1 at next level, right associativity).
