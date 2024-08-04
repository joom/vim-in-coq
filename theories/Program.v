Require Import PrimInt63 NArith Ascii String.

Require Import Vim.Foreign.
Require Import Vim.TextZipper.

Variant modes := normal | insert.

Record state :=
  { mode : modes
  ; document : text_zipper
  }.

Definition render (fuel : nat) (w : C.window) (s : state) : C.M unit :=
  let fix render_line (l : list (list ascii)) (row : int) : C.M unit :=
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
  C.print w (list_ascii_of_string (match mode s with insert => "INSERT" | normal => "NORMAL" end)) ;;
  render_line (lines (document s)) 0%int63 ;;
  let (row, col) := cursor_position (document s) in
  C.move_cursor w (int_of_nat row) (int_of_nat col) ;;
  C.refresh w.

Definition react (c : int) (s : state) : state :=
  match mode s with
  | insert =>
    if PrimInt63.eqb c 27 (* ESC *)
    then {| mode := normal
          ; document := document s
          |}
    else if andb (PrimInt63.leb 32 c) (negb (PrimInt63.leb 126 c))
    then {| mode := insert
          ; document := insert_char_left (ascii_of_int c) (document s)
          |}
    else if PrimInt63.eqb 10 c (* enter *)
    then {| mode := insert
          ; document := break_line (document s)
          |}
    else if orb (PrimInt63.eqb c 8 (* backspace *)) (PrimInt63.eqb c 127 (* delete *))
    then {| mode := insert
          ; document := delete_char_right (document s) (* TODO left *)
          |}
    else s
  | normal =>
    if PrimInt63.eqb c 97 (* a *)
    then {| mode := insert
          ; document := move_right (document s)
          |}
    else if PrimInt63.eqb c 105 (* i *)
    then {| mode := insert
          ; document := document s
          |}
    else if PrimInt63.eqb c 104 (* h *)
    then {| mode := normal
          ; document := move_left (document s)
          |}
    else if PrimInt63.eqb c 106 (* j *)
    then {| mode := normal
          ; document := move_down (document s)
          |}
    else if PrimInt63.eqb c 107 (* k *)
    then {| mode := normal
          ; document := move_up (document s)
          |}
    else if PrimInt63.eqb c 108 (* l *)
    then {| mode := normal
          ; document := move_right (document s)
          |}
    else if PrimInt63.eqb c 48 (* 0 *)
    then {| mode := normal
          ; document := move_start_of_line (document s)
          |}
    else if PrimInt63.eqb c 36 (* $ *)
    then {| mode := normal
          ; document := move_end_of_line (document s)
          |}
    else if PrimInt63.eqb c 79 (* O *)
    then {| mode := normal
          ; document := insert_new_line_before (document s)
          |}
    else if PrimInt63.eqb c 111 (* o *)
    then {| mode := normal
          ; document := insert_new_line_after (document s)
          |}
    else s
  end.

Fixpoint loop (fuel : nat) (w : C.window) (s : state) : C.M unit :=
  match fuel with
  | S fuel' =>
    cur <- C.get_cursor w ;;
    let (y, x) := cur in
    c <- C.get_char w ;;
    let s' := react c s in
    render fuel' w s' ;;
    loop fuel' w s'
  | _ => C.pure tt
  end.

Definition init_state : state :=
  {| mode := normal
   ; document := initial_text_zipper
   |}.

Definition program (fuel : nat) : C.M unit :=
  w <- C.new_window ;;
  render fuel w init_state ;;
  loop fuel w init_state ;;
  C.close_window w.
