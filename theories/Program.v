Require Import PrimInt63 ZArith Ascii List.

Require Import Vim.Helpers
               Vim.Errors
               Vim.Foreign
               Vim.TextZipper.

Import ListNotations.
Open Scope char_scope.

Variant edit_mode :=
| normal : edit_mode
| insert : edit_mode
| visual : forall (start_point : text_zipper), edit_mode
| command : list ascii -> edit_mode
| replace : edit_mode.

Definition string_of_edit_mode (m : edit_mode) : list ascii :=
  match m with
  | normal => ["N";"O";"R";"M";"A";"L"]
  | insert => ["I";"N";"S";"E";"R";"T"]
  | visual _ => ["V";"I";"S";"U";"A";"L"]
  | command _ => ["C";"O";"M";"M";"A";"N";"D"]
  | replace => ["R";"E";"P";"L";"A";"C";"E"]
  end.

Inductive shortcut_token :=
| number_token : nat -> shortcut_token
| ascii_token : ascii -> shortcut_token.

Definition string_of_shortcut_tokens (l : list shortcut_token) : list ascii :=
  List.concat (map (fun x => match x with
                             | ascii_token c => [c]
                             | number_token n => string_of_nat n
                             end) l).

Record state :=
  { mode : edit_mode
  ; document : text_zipper
  ; shortcut : list shortcut_token
  ; has_changes : bool
  ; current_file : option (list ascii)
  ; current_error : option error
  ; screen_row : int (* Screen size in rows *)
  ; screen_col : int (* Screen size in cols *)
  ; offset_row : int (* Hide this many rows from the top of the document *)
  ; offset_col : int (* Hide this many cols from the left side of the document *)
  }.

Definition initial_state : state :=
  {| mode := normal
   ; document := initial_text_zipper
   ; shortcut := []
   ; has_changes := false
   ; current_file := None
   ; current_error := None
   ; screen_row := 0
   ; screen_col := 0
   ; offset_row := 0
   ; offset_col := 0
   |}.

Definition set_mode (new : edit_mode) (s : state) : state :=
  {| mode := new
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := false
   ; current_file := current_file s
   ; current_error := current_error s
   ; screen_row := screen_row s
   ; screen_col := screen_col s
   ; offset_row := offset_row s
   ; offset_col := offset_col s
   |}.

Definition set_document (new : text_zipper) (s : state) : state :=
  {| mode := mode s
   ; document := new
   ; shortcut := shortcut s
   ; has_changes := false
   ; current_file := current_file s
   ; current_error := current_error s
   ; screen_row := screen_row s
   ; screen_col := screen_col s
   ; offset_row := offset_row s
   ; offset_col := offset_col s
   |}.

Definition set_shortcut (new : list shortcut_token) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := new
   ; has_changes := false
   ; current_file := current_file s
   ; current_error := current_error s
   ; screen_row := screen_row s
   ; screen_col := screen_col s
   ; offset_row := offset_row s
   ; offset_col := offset_col s
   |}.

Definition set_has_changes (new : bool) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := new
   ; current_file := current_file s
   ; current_error := current_error s
   ; screen_row := screen_row s
   ; screen_col := screen_col s
   ; offset_row := offset_row s
   ; offset_col := offset_col s
   |}.

Definition set_current_file (new : option (list ascii)) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := has_changes s
   ; current_file := new
   ; current_error := current_error s
   ; screen_row := screen_row s
   ; screen_col := screen_col s
   ; offset_row := offset_row s
   ; offset_col := offset_col s
   |}.

Definition set_current_error (new : option error) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := has_changes s
   ; current_file := current_file s
   ; current_error := new
   ; screen_row := screen_row s
   ; screen_col := screen_col s
   ; offset_row := offset_row s
   ; offset_col := offset_col s
   |}.

Definition set_screen_row (new : int) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := has_changes s
   ; current_file := current_file s
   ; current_error := current_error s
   ; screen_row := new
   ; screen_col := screen_col s
   ; offset_row := offset_row s
   ; offset_col := offset_col s
   |}.

Definition set_screen_col (new : int) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := has_changes s
   ; current_file := current_file s
   ; current_error := current_error s
   ; screen_row := screen_row s
   ; screen_col := new
   ; offset_row := offset_row s
   ; offset_col := offset_row s
   |}.

Definition set_offset_row (new : int) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := has_changes s
   ; current_file := current_file s
   ; current_error := current_error s
   ; screen_row := screen_row s
   ; screen_col := screen_col s
   ; offset_row := new
   ; offset_col := offset_col s
   |}.

Definition set_offset_col (new : int) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := has_changes s
   ; current_file := current_file s
   ; current_error := current_error s
   ; screen_row := screen_row s
   ; screen_col := screen_col s
   ; offset_row := offset_row s
   ; offset_col := new
   |}.

Definition save_file (s : state) : C.M unit :=
  match current_file s with
  | None => C.pure tt
  | Some file_name =>
    C.write_to_file file_name (all_content (document s)) ;;
    C.pure tt
  end.

Definition exit (w : C.window) : C.M unit :=
  C.close_window w ;; C.exit success.

Definition shortcut_view (s : state) : nat * list shortcut_token :=
  match shortcut s with
  | number_token n :: l => (n, l)
  | l => (1, l)
  end.

Definition run_shortcut (w : C.window) (s : state) : C.M state :=
  match mode s , shortcut_view s with
  | normal , (1 , [ascii_token "["; ascii_token "A"]) (* up arrow key *) =>
    C.pure (set_shortcut [] (set_document (move_up (document s)) s))
  | normal , (1 , [ascii_token "["; ascii_token "B"]) (* down arrow key *) =>
    C.pure (set_shortcut [] (set_document (move_down (document s)) s))
  | normal , (1 , [ascii_token "["; ascii_token "D"]) (* left arrow key *) =>
    C.pure (set_shortcut [] (set_document (move_left (document s)) s))
  | normal , (1 , [ascii_token "["; ascii_token "C"]) (* right arrow key *) =>
    C.pure (set_shortcut [] (set_document (move_right (document s)) s))
  | normal , (n , [ascii_token ":"]) =>
    C.pure (set_shortcut [] (set_mode (command []) s))
  | normal , (n , [ascii_token "a"]) =>
    C.pure (set_shortcut [] (set_mode insert (set_document (move_right (document s)) s)))
  | normal , (n , [ascii_token "i"]) =>
    C.pure (set_shortcut [] (set_mode insert (set_document (document s) s)))
  | normal , (n , [ascii_token "h"]) =>
    C.pure (set_shortcut [] (set_document (apply n move_left (document s)) s))
  | normal , (n , [ascii_token "j"]) =>
    C.pure (set_shortcut [] (set_document (apply n move_down (document s)) s))
  | normal , (n , [ascii_token "k"]) =>
    C.pure (set_shortcut [] (set_document (apply n move_up (document s)) s))
  | normal , (n , [ascii_token "l"]) =>
    C.pure (set_shortcut [] (set_document (apply n move_right (document s)) s))
  | normal , (n , [ascii_token "0"]) =>
    C.pure (set_shortcut [] (set_document (move_start_of_line (document s)) s))
  | normal , (n , [ascii_token "$"]) =>
    C.pure (set_shortcut [] (set_document (move_end_of_line (document s)) s))
  | normal , (n , [ascii_token "g"; ascii_token "g"]) =>
    C.pure (set_shortcut [] (set_document (move_start_of_document (document s)) s))
  | normal , (n , [ascii_token "G"]) =>
    C.pure (set_shortcut [] (set_document (move_end_of_document (document s)) s))
  | normal , (n , [ascii_token "O"]) =>
    C.pure (set_shortcut [] (set_mode insert (set_document (insert_new_line_before (document s)) s)))
  | normal , (n , [ascii_token "o"]) =>
    C.pure (set_shortcut [] (set_mode insert (set_document (insert_new_line_after (document s)) s)))
  | normal , (n , [ascii_token "x"]) =>
    C.pure (set_shortcut [] (set_document (apply n delete_char_right (document s)) s))
  | normal , (n , [ascii_token "d"; ascii_token "d"]) =>
    C.pure (set_shortcut [] (set_document (apply n delete_current_line (document s)) s))
  | normal , (n , [ascii_token "g"; ascii_token "J"]) =>
    C.pure (set_shortcut [] (set_document (apply n (join_the_line_below false) (document s)) s))
  | normal , (n , [ascii_token "J"]) =>
    C.pure (set_shortcut [] (set_document (apply n (join_the_line_below true) (document s)) s))
  | normal , (n , [ascii_token "r"; ascii_token c]) =>
    C.pure (set_shortcut [] (set_document (apply_with_sep n move_right (replace_char c) (document s)) s))
  | normal , (n , [ascii_token "R"]) =>
    C.pure (set_shortcut [] (set_mode replace s))
  | normal , (n , [ascii_token "f"; ascii_token c]) =>
    C.pure (set_shortcut [] (set_document (move_next_occurrence_on_line (Ascii.eqb c) (document s)) s))
  | normal , (n , [ascii_token "F"; ascii_token c]) =>
    C.pure (set_shortcut [] (set_document (move_prev_occurrence_on_line (Ascii.eqb c) (document s)) s))
  | normal , (n , [ascii_token "w"]) =>
    C.pure (set_shortcut [] (set_document (apply n move_start_of_next_word_on_line (document s)) s))
  | normal , (n , [ascii_token "b"]) =>
    C.pure (set_shortcut [] (set_document (apply n move_start_of_prev_word_on_line (document s)) s))
  | normal , (n , [ascii_token "e"]) =>
    C.pure (set_shortcut [] (set_document (apply n move_end_of_next_word_on_line (document s)) s))
  | normal , (_ , [ascii_token "Z"; ascii_token "Z"]) =>
    save_file s ;; exit w ;; C.pure s
  | _ , (_ , _) => C.pure s
  end.

Definition run_command (w : C.window) (s : state) : C.M state :=
  match mode s with
  | command ["q"] =>
      exit w ;;
      C.pure s
  | command ["w"] =>
      save_file s ;;
      C.pure s
  | command ["w";"q"] =>
      save_file s ;;
      exit w ;;
      C.pure s
  | _ => C.pure s
  end.

Definition react (c : int) (w : C.window) (s : state) : C.M state :=
  match mode s with
  | insert =>
    if PrimInt63.eqb c 27 (* ESC *)
    then C.pure (set_mode normal s)
    else if andb (PrimInt63.leb 32 c) (PrimInt63.leb c 126)
    then C.pure (set_document (insert_char_left (ascii_of_int c) (document s)) s)
    else if PrimInt63.eqb 10 c (* enter *)
    then C.pure (set_mode insert (set_document (break_line (document s)) s))
    else if orb (PrimInt63.eqb c 8 (* backspace *)) (PrimInt63.eqb c 127 (* delete *))
    then C.pure (set_mode insert (set_document (delete_char_left (document s)) s))
    else C.pure s
  | normal =>
    if PrimInt63.eqb c 27 (* ESC *)
    then C.pure (set_shortcut [] (set_current_error None s))
    else if andb (PrimInt63.leb 48 c) (PrimInt63.leb c 57) (* between 0 and 9 *)
    then C.pure (set_shortcut (
      match shortcut s with
      | [ascii_token "r"] => (* to replace with the char under cursor *)
          ascii_token (ascii_of_int c) :: shortcut s
      | [ascii_token "f"] => (* to find in search *)
          ascii_token (ascii_of_int c) :: shortcut s
      | [ascii_token "F"] => (* to find in search *)
          ascii_token (ascii_of_int c) :: shortcut s
      | [number_token n] =>
          [number_token (10 * n + nat_of_int (PrimInt63.sub c 48))]
      | ts =>
          if PrimInt63.eqb c 48 (* 0 *) then shortcut s ++ [ascii_token "0"] else
          ts ++ [number_token (nat_of_int (PrimInt63.sub c 48))]
      end) s)
    else if andb (PrimInt63.leb 32 c) (PrimInt63.leb c 126) (* between space and ~ *)
    then C.pure (set_shortcut (shortcut s ++ [ascii_token (ascii_of_int c)]) s)
    else C.pure s
  | visual start_point => C.pure s
  | command l =>
    if PrimInt63.eqb 10 c (* enter *)
    then s' <- run_command w s ;;
         C.pure (set_mode normal s')
    else if PrimInt63.eqb 27 c (* ESC *)
    then C.pure (set_mode normal s)
    else if orb (PrimInt63.eqb c 8 (* backspace *)) (PrimInt63.eqb c 127 (* delete *))
    then C.pure (set_mode (match l with [] => normal | _ => command (rev (tail (rev l))) end) s)
    else if andb (PrimInt63.leb 32 c) (PrimInt63.leb c 126)
    then C.pure (set_mode (command (l ++ [ascii_of_int c])) s)
    else C.pure s
  | replace =>
    if PrimInt63.eqb c 27 (* ESC *)
    then C.pure (set_mode normal s)
    else if andb (PrimInt63.leb 32 c) (PrimInt63.leb c 126)
    then C.pure (set_document (insert_char_left (ascii_of_int c) (delete_char_right (document s))) s)
    else if orb (PrimInt63.eqb c 8 (* backspace *)) (PrimInt63.eqb c 127 (* delete *))
    then C.pure (set_document (move_left (document s)) s)
    else C.pure s
  end.

Record style_set :=
  { default_style : C.style
  ; normal_bar_style : C.style
  ; insert_bar_style : C.style
  ; visual_bar_style : C.style
  ; command_bar_style : C.style
  ; replace_bar_style : C.style
  }.

Definition make_styles : C.M style_set :=
  default <- C.make_style white default ;;
  normal <- C.make_style black green ;;
  insert <- C.make_style black yellow ;;
  visual <- C.make_style black magenta ;;
  command <- C.make_style black blue ;;
  replace <- C.make_style black red ;;
  C.pure {| default_style := default
          ; normal_bar_style := normal
          ; insert_bar_style := insert
          ; visual_bar_style := visual
          ; command_bar_style := command
          ; replace_bar_style := replace
          |}.

Definition style_of_mode (styles : style_set) (m : edit_mode) : C.style :=
  match m with
  | normal => normal_bar_style styles
  | insert => insert_bar_style styles
  | visual _ => visual_bar_style styles
  | command _ => command_bar_style styles
  | replace => replace_bar_style styles
  end.

Definition render (w : C.window) (styles : style_set) (s : state)  : C.M state :=
  C.clear w ;;
  size <- C.get_size w ;;
  let '(screen_rows, screen_cols) := size in
  let screen_rows_for_document := PrimInt63.sub screen_rows 3 in

   (* Adjust cursor position relative to the screen *)
  let '(cursor_row, cursor_col) := cursor_position (document s) in
  let cursor_screen_row := PrimInt63.sub cursor_row (offset_row s) in
  let cursor_screen_col := PrimInt63.sub cursor_col (offset_col s) in

  (* Render bottom line for the mode *)
  C.move_cursor w (sub screen_rows 2) 0 ;;
  let mode_style := style_of_mode styles (mode s) in
  C.start_style mode_style ;;
  C.print w (repeat " " (nat_of_int screen_cols)) ;;
  C.move_cursor w (sub screen_rows 2) 0 ;;
  C.print w (string_of_edit_mode (mode s)) ;;
  match current_file s with
  | Some file_name =>
      C.move_cursor w (sub screen_rows 2) (sub screen_cols (int_of_nat (length file_name))) ;;
      C.print w file_name
  | _ => C.pure tt
  end ;;
  C.end_style mode_style ;;

  (* Render bottom line for shortcut and command *)
  C.move_cursor w (sub screen_rows 1) 0 ;;
  match current_error s, mode s with
  | Some e , _ => C.print w (string_of_error e)
  | _ , command l => C.print w (":" :: l)
  | _ , _ => C.print w (string_of_shortcut_tokens (shortcut s))
  end ;;

  (* Render document *)
  let fix render_line
          (l : list (list ascii)) (row : int) : C.M unit :=
    match l with
    | [] =>
      C.pure tt
    | x :: xs =>
      C.move_cursor w row 0 ;;
      C.print w (firstn_int screen_cols (skipn_int (offset_col s) x)) ;;
      render_line xs (PrimInt63.add row 1)
    end in

  let lines_to_show := firstn_int screen_rows_for_document
                         (skipn_int (offset_row s) (lines (document s))) in
  render_line lines_to_show 0%int63 ;;
  C.move_cursor w cursor_screen_row cursor_screen_col ;;
  C.refresh w ;;
  C.pure (set_screen_row screen_rows (set_screen_col screen_cols s)).

Definition int_max (x y : int) :=
  if PrimInt63.ltb x y then y else x.
Definition int_min (x y : int) :=
  if PrimInt63.ltb x y then x else y.

Definition handle_movement (before after : state) : state :=
  (* Unpack cursor positions before and after the movement *)
  let '(before_row, before_col) := cursor_position (document before) in
  let '(after_row, after_col) := cursor_position (document after) in

  (* Determine screen dimensions, accounting for UI elements *)
  let screen_rows := PrimInt63.sub (screen_row after) 4%int63 in
  let screen_cols := PrimInt63.sub (screen_col after) 1%int63 in

  (* Calculate current cursor positions on the screen *)
  let before_screen_row := PrimInt63.sub before_row (offset_row before) in
  let before_screen_col := PrimInt63.sub before_col (offset_col before) in
  let after_screen_row := PrimInt63.sub after_row (offset_row after) in
  let after_screen_col := PrimInt63.sub after_col (offset_col after) in

  (* Adjust horizontal movement *)
  let after :=
    if signed_int_leb screen_cols after_screen_col then
      (* Cursor moved right out of view, adjust the offset *)
      set_offset_col (PrimInt63.sub after_col screen_cols) after
    else if signed_int_leb after_screen_col 0 then
      (* Cursor moved left out of view, adjust the offset *)
      set_offset_col after_col after
    else
      (* Cursor is within bounds; only adjust if it moved left out of view *)
      if signed_int_leb before_screen_col after_screen_col then after else after in

  (* Adjust vertical movement *)
  let after :=
    if signed_int_leb screen_rows after_screen_row then
      (* Cursor moved down out of view, adjust the offset *)
      set_offset_row (PrimInt63.sub after_row screen_rows) after
    else if signed_int_leb after_screen_row 0 then
      (* Cursor moved up out of view, adjust the offset *)
      set_offset_row after_row after
    else
      (* Cursor is within bounds; only adjust if it moved up out of view *)
      if signed_int_leb before_screen_row after_screen_row then after else after in
  after.

CoFixpoint loop (w : C.window) (styles : style_set) (s : state) : C.M unit :=
  cur <- C.get_cursor w ;;
  let (y, x) := cur in
  c <- C.get_char w ;;
  s <- react c w s ;;
  s' <- run_shortcut w s ;;
  let s' := handle_movement s s' in
  s' <- render w styles s' ;;
  loop w styles s'.

Definition main (args : list (list ascii)) : C.M unit :=
  w <- C.new_window ;;
  styles <- make_styles ;;
  C.set_window_default_style w (default_style styles) ;;
  size <- C.get_size w ;;
  let '(screen_rows, screen_cols) := size in
  let s := set_screen_row screen_rows (set_screen_col screen_cols initial_state) in
  match args with
  | [] =>
    s <- render w styles s ;;
    loop w styles s ;;
    C.close_window w
  | file_name :: [] =>
    content' <- C.read_file file_name ;;
    let s :=
      match content' with
      | inl e => set_current_error (Some e) s
      | inr content =>
        let d := text_zipper_of_string content in
        set_current_file (Some file_name) (set_document d s)
      end in
    s <- render w styles s ;;
    loop w styles s ;;
    exit w
  | _ => C.exit failure
  end.
