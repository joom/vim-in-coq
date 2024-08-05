Require Import PrimInt63 NArith Ascii List String.

Require Import Vim.Foreign.
Require Import Vim.TextZipper.

Import ListNotations.

Variant modes := normal | insert.

Inductive shortcut_token :=
| number_token : N -> shortcut_token
| ascii_token : ascii -> shortcut_token.

Record state :=
  { mode : modes
  ; document : text_zipper
  ; shortcut : list shortcut_token
  }.

Definition render (w : C.window) (s : state) : C.M unit :=
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
  C.move_cursor w (sub row 2) 0 ;;
  C.print w (list_ascii_of_string (match mode s with insert => "INSERT" | normal => "NORMAL" end)) ;;
  C.move_cursor w (sub row 1) 0 ;;
  C.print w (List.concat (map (fun x => match x with ascii_token c => [c] | _ => [] end) (shortcut s))) ;;
  render_line (lines (document s)) 0%int63 ;;
  let (row, col) := cursor_position (document s) in
  C.move_cursor w (int_of_N row) (int_of_N col) ;;
  C.refresh w.

Definition run_shortcut (s : state) : state :=
  match mode s , shortcut s with
  | normal , [ascii_token "a"] =>
    {| mode := insert
     ; document := move_right (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "i"] =>
    {| mode := insert
     ; document := document s
     ; shortcut := []
     |}
  | normal , [ascii_token "h"] =>
    {| mode := normal
     ; document := move_left (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "j"] =>
    {| mode := normal
     ; document := move_down (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "k"] =>
    {| mode := normal
     ; document := move_up (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "l"] =>
    {| mode := normal
     ; document := move_right (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "0"] =>
    {| mode := normal
     ; document := move_start_of_line (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "$"] =>
    {| mode := normal
     ; document := move_end_of_line (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "O"] =>
    {| mode := normal
     ; document := insert_new_line_before (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "o"] =>
    {| mode := normal
     ; document := insert_new_line_after (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "x"] =>
    {| mode := normal
     ; document := delete_char_right (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "d"; ascii_token "d"] =>
    {| mode := normal
     ; document := delete_current_line (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "r"; ascii_token c] =>
    {| mode := normal
     ; document := replace_char c (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "f"; ascii_token c] =>
    {| mode := normal
     ; document := move_next_occurrence_on_line is_space (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "F"; ascii_token c] =>
    {| mode := normal
     ; document := move_prev_occurrence_on_line is_space (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "w"] =>
    {| mode := normal
     ; document := move_start_of_next_word_on_line (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "b"] =>
    {| mode := normal
     ; document := move_start_of_prev_word_on_line (document s)
     ; shortcut := []
     |}
  | normal , [ascii_token "e"] =>
    {| mode := normal
     ; document := move_end_of_next_word_on_line (document s)
     ; shortcut := []
     |}
  | _ , _ => s
  end.

Definition react (c : int) (s : state) : state :=
  match mode s with
  | insert =>
    if PrimInt63.eqb c 27 (* ESC *)
    then {| mode := normal
          ; document := document s
          ; shortcut := shortcut s
          |}
    else if andb (PrimInt63.leb 32 c) (PrimInt63.leb c 126)
    then {| mode := insert
          ; document := insert_char_left (ascii_of_int c) (document s)
          ; shortcut := shortcut s
          |}
    else if PrimInt63.eqb 10 c (* enter *)
    then {| mode := insert
          ; document := break_line (document s)
          ; shortcut := shortcut s
          |}
    else if orb (PrimInt63.eqb c 8 (* backspace *)) (PrimInt63.eqb c 127 (* delete *))
    then {| mode := insert
          ; document := delete_char_left (document s)
          ; shortcut := shortcut s
          |}
    else s
  | normal =>
    if PrimInt63.eqb c 27 (* ESC *)
    then {| mode := normal
          ; document := document s
          ; shortcut := []
          |}
    else if andb (PrimInt63.leb 48 c) (PrimInt63.leb c 57) (* between 0 and 9 *)
    then {| mode := normal
          ; document := document s
          ; shortcut :=
              match shortcut s with
              | [ascii_token "r"] => (* to replace with the char under cursor *)
                  ascii_token (ascii_of_int c) :: shortcut s
              | [ascii_token "f"] => (* to find in search *)
                  ascii_token (ascii_of_int c) :: shortcut s
              | [ascii_token "F"] => (* to find in search *)
                  ascii_token (ascii_of_int c) :: shortcut s
              | number_token n :: ts =>
                  shortcut s ++ [number_token (10 * n + N_of_int (PrimInt63.sub c 48))]
              | ts =>
                  if PrimInt63.eqb c 48 (* 0 *) then shortcut s ++ [ascii_token "0"] else
                  shortcut s ++ [number_token (N_of_int (PrimInt63.sub c 48))]
              end
          |}
    else if andb (PrimInt63.leb 32 c) (PrimInt63.leb c 126) (* between space and ~ *)
    then {| mode := normal
          ; document := document s
          ; shortcut := shortcut s ++ [ascii_token (ascii_of_int c)]
          |}
    else s
  end.

CoFixpoint loop (w : C.window) (s : state) : C.M unit :=
  cur <- C.get_cursor w ;;
  let (y, x) := cur in
  c <- C.get_char w ;;
  let s' := run_shortcut (react c s) in
  render w s' ;;
  loop w s'.

Definition init_state : state :=
  {| mode := normal
   ; document := initial_text_zipper
   ; shortcut := []
   |}.

Definition main : C.M unit :=
  w <- C.new_window ;;
  render w init_state ;;
  loop w init_state ;;
  C.close_window w.
