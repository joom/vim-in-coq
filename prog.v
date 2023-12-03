From CertiCoq.Plugin Require Import CertiCoq.

Require Import PrimInt63 NArith Ascii String.

Axiom N_of_int : int -> N.
Axiom int_of_N : N -> int.

CertiCoq Register [
    N_of_int => "n_of_int" with tinfo,
    int_of_N => "int_of_n" ]
  Include [ "prims.h" ].

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

Fixpoint split_aux (acc : string) (sep : ascii) (s : string) : list string :=
  match s with
  | String.EmptyString => acc :: nil
  | String.String c s' =>
      if Ascii.eqb sep c
      then acc :: split_aux String.EmptyString sep s'
      else split_aux (acc ++ String.String c String.EmptyString) sep s'
  end.

Definition split (c : ascii) (s : string) : list string :=
  split_aux String.EmptyString c s.

Variant direction := forward | backward.
Fixpoint count_towards (d : direction) (c : ascii) (s : string) (pos : nat) : nat :=
  let fix aux (fuel : nat) (pos : nat) : nat :=
    match get pos s, fuel with
    | None, _ => 0
    | _, 0 => 0
    | Some a, S fuel' =>
        if Ascii.eqb c a then 0
        else S (aux fuel' ((match d with forward => S | backward => pred end) pos))
    end in
  aux (length s) pos.

Variant mode := normal | insert.
Record vim :=
  { vim_mode : mode
  ; vim_text : string
  ; vim_cursor_row : int
  ; vim_cursor_col : int
  ; vim_cursor_in_doc : nat
  }.

Definition newline : ascii :=
  Ascii false true false true false false false false.

Fixpoint render (fuel : nat) (w : C.window) (v : vim) : C.M unit :=
  let fix render_line (l : list string) (row : int) : C.M unit :=
    match l with
    | nil => 
      C.pure tt
    | cons x xs =>
      C.move_cursor w row 0 ;;
      C.print w x ;;
      render_line xs (add 1 row)
    end in
  C.clear w ;;
  size <- C.get_size w ;;
  let '(row, col) := size in
  C.move_cursor w (sub row 1) 0 ;;
  C.print w (match vim_mode v with insert => "INSERT" | normal => "NORMAL" end) ;;
  render_line (split newline (vim_text v)) 0%int63 ;;
  C.move_cursor w (vim_cursor_row v) (vim_cursor_col v) ;;
  C.refresh w.

Definition react (c : int) (v : vim) : vim :=
  match vim_mode v with
  | insert =>
    if PrimInt63.eqb c 27 (* ESC *)
    then {| vim_mode := normal
          ; vim_text := vim_text v
          ; vim_cursor_row := vim_cursor_row v
          ; vim_cursor_col := vim_cursor_col v
          ; vim_cursor_in_doc := vim_cursor_in_doc v
          |}
    else if andb (PrimInt63.leb 32 c) (negb (PrimInt63.leb 126 c))
    then {| vim_mode := insert
          ; vim_text := append (substring 0 (vim_cursor_in_doc v) (vim_text v))
                               (append (String (ascii_of_int c) EmptyString)
                                  (substring (vim_cursor_in_doc v)
                                     (length (vim_text v)) (vim_text v)))
          ; vim_cursor_row := vim_cursor_row v
          ; vim_cursor_col := add (vim_cursor_col v) 1
          ; vim_cursor_in_doc := S (vim_cursor_in_doc v)
          |}
    else if PrimInt63.eqb 10 c (* enter *)
    then {| vim_mode := insert
          ; vim_text := append (substring 0 (vim_cursor_in_doc v) (vim_text v))
                               (append (String newline EmptyString)
                                  (substring (vim_cursor_in_doc v)
                                     (length (vim_text v)) (vim_text v)))
          ; vim_cursor_row := add (vim_cursor_row v) 1
          ; vim_cursor_col := 0
          ; vim_cursor_in_doc := S (vim_cursor_in_doc v)
          |}
    else if orb (PrimInt63.eqb c 8 (* backspace *)) (PrimInt63.eqb c 127 (* delete *))
    then {| vim_mode := insert
          ; vim_text := append (substring 0 (pred (vim_cursor_in_doc v)) (vim_text v))
                          (substring (vim_cursor_in_doc v)
                             (length (vim_text v)) (vim_text v))
          ; vim_cursor_row := vim_cursor_row v
          ; vim_cursor_col := if PrimInt63.eqb (vim_cursor_col v) 0 then 0
                              else sub (vim_cursor_col v) 1
          ; vim_cursor_in_doc := pred (vim_cursor_in_doc v)
          |}
    else v
  | normal =>
    if PrimInt63.eqb c 97 (* a *)
    then {| vim_mode := insert
          ; vim_text := vim_text v
          ; vim_cursor_row := vim_cursor_row v
          ; vim_cursor_col := vim_cursor_col v
          ; vim_cursor_in_doc := vim_cursor_in_doc v
          |}
    else if PrimInt63.eqb c 104 (* h *)
    then {| vim_mode := normal
          ; vim_text := vim_text v
          ; vim_cursor_row := vim_cursor_row v
          ; vim_cursor_col := if PrimInt63.eqb (vim_cursor_col v) 0 then 0
                              else sub (vim_cursor_col v) 1
          ; vim_cursor_in_doc := pred (vim_cursor_in_doc v)
          |}
    else if PrimInt63.eqb c 108 (* l *)
    then match get (S (vim_cursor_in_doc v)) (vim_text v) with
         | None => v
         | Some a => if Ascii.eqb a newline then v else
         {| vim_mode := normal
          ; vim_text := vim_text v
          ; vim_cursor_row := vim_cursor_row v
          ; vim_cursor_col :=
              add (vim_cursor_col v) 1
          ; vim_cursor_in_doc := S (vim_cursor_in_doc v)
          |}
         end
    else if PrimInt63.eqb c 36 (* $ *)
    then let n := pred (count_towards forward newline (vim_text v) (vim_cursor_in_doc v)) in
         {| vim_mode := normal
          ; vim_text := vim_text v
          ; vim_cursor_row := vim_cursor_row v
          ; vim_cursor_col := add (vim_cursor_col v) (int_of_N (N_of_nat n))
          ; vim_cursor_in_doc := vim_cursor_in_doc v + n
          |}
    else if PrimInt63.eqb c 48 (* 0 *)
    then let n := pred (count_towards backward newline (vim_text v) (vim_cursor_in_doc v)) in
         {| vim_mode := normal
          ; vim_text := vim_text v
          ; vim_cursor_row := vim_cursor_row v
          ; vim_cursor_col := 0
          ; vim_cursor_in_doc := vim_cursor_in_doc v - n
          |}
    else v
  end.

Fixpoint loop (fuel : nat) (w : C.window) (v : vim) : C.M unit :=
  match fuel with
  | S fuel' =>
    cur <- C.get_cursor w ;;
    let (y, x) := cur in
    c <- C.get_char w ;;
    let v' := react c v in
    render fuel' w v' ;;
    loop fuel' w v'
  | _ => C.pure tt
  end.

Definition init_vim : vim :=
  {| vim_mode := normal
   ; vim_text := EmptyString
   ; vim_cursor_row := 0
   ; vim_cursor_col := 0
   ; vim_cursor_in_doc := 0
   |}.

Definition prog (fuel : nat) : C.M unit :=
  w <- C.new_window ;;
  render fuel w init_vim ;;
  loop fuel w init_vim ;;
  C.close_window w.

CertiCoq Compile -file "prog" prog.
CertiCoq Generate Glue -file "glue" [ nat, N, ascii, string, C.MI ].
