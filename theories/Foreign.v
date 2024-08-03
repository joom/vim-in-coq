From CertiCoq.Plugin Require Import CertiCoq.
Require Import PrimInt63 NArith Ascii String.

Axiom N_of_int : int -> N.
Axiom int_of_N : N -> int.

CertiCoq Register [
    N_of_int => "n_of_int" with tinfo,
    int_of_N => "int_of_n" ]
  Include [ "foreign.h" ].

Definition ascii_of_int (i : int) : ascii := ascii_of_N (N_of_int i).
Definition int_of_ascii (a : ascii) : int := int_of_N (N_of_ascii a).

Module Type NCurses.
  Parameter M : Type -> Type.
  Parameter pure : forall {A}, A -> M A.
  Parameter bind : forall {A B}, M A -> (A -> M B) -> M B.
  Parameter window : Type.
  Parameter new_window : M window.
  Parameter close_window : window -> M unit.
  Parameter move_cursor : window -> forall (row : int) (col : int), M unit.
  Parameter get_cursor : window -> M (int * int).
  Parameter get_size : window -> M (int * int).
  Parameter print : window -> string -> M unit.
  Parameter refresh : window -> M unit.
  Parameter clear : window -> M unit.
  Parameter get_char : window -> M int.
End NCurses.

Module C <: NCurses.
  Axiom window : Type.

  Inductive MI : Type -> Type :=
  | pureI : forall {A}, A -> MI A
  | bindI : forall {A B}, MI A -> (A -> MI B) -> MI B
  | new_windowI : MI window
  | close_windowI : window -> MI unit
  | move_cursorI : window -> forall (row : int) (col : int), MI unit
  | get_cursorI : window -> MI (int * int)
  | get_sizeI : window -> MI (int * int)
  | printI : window -> string -> MI unit
  | refreshI : window -> MI unit
  | clearI : window -> MI unit
  | get_charI : window -> MI int.

  Definition M := MI.
  Definition pure : forall {A}, A -> M A := @pureI.
  Definition bind : forall {A B}, M A -> (A -> M B) -> M B := @bindI.
  Definition new_window : M window := @new_windowI.
  Definition close_window : window -> M unit := @close_windowI.
  Definition move_cursor : window -> forall (row : int) (col : int), M unit := @move_cursorI.
  Definition get_cursor : window -> M (int * int) := @get_cursorI.
  Definition get_size : window -> M (int * int) := @get_sizeI.
  Definition print : window -> string -> M unit := @printI.
  Definition refresh : window -> M unit := @refreshI.
  Definition clear : window -> M unit := @clearI.
  Definition get_char : window -> M int := @get_charI.
End C.

Notation "e1 ;; e2" :=
  (@C.bind _ _ e1 (fun _ => e2)) (at level 61, right associativity).
Notation "x <- c1 ;; c2" :=
  (@C.bind _ _ c1 (fun x => c2)) (at level 61, c1 at next level, right associativity).
