Require Import PrimInt63 NArith Ascii List.

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
  }.

Definition initial_state : state :=
  {| mode := normal
   ; document := initial_text_zipper
   ; shortcut := []
   ; has_changes := false
   ; current_file := None
   ; current_error := None
   |}.

Definition set_mode (new : edit_mode) (s : state) : state :=
  {| mode := new
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := false
   ; current_file := current_file s
   ; current_error := current_error s
   |}.

Definition set_document (new : text_zipper) (s : state) : state :=
  {| mode := mode s
   ; document := new
   ; shortcut := shortcut s
   ; has_changes := false
   ; current_file := current_file s
   ; current_error := current_error s
   |}.

Definition set_shortcut (new : list shortcut_token) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := new
   ; has_changes := false
   ; current_file := current_file s
   ; current_error := current_error s
   |}.

Definition set_has_changes (new : bool) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := new
   ; current_file := current_file s
   ; current_error := current_error s
   |}.

Definition set_current_file (new : option (list ascii)) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := has_changes s
   ; current_file := new
   ; current_error := current_error s
   |}.

Definition set_current_error (new : option error) (s : state) : state :=
  {| mode := mode s
   ; document := document s
   ; shortcut := shortcut s
   ; has_changes := has_changes s
   ; current_file := current_file s
   ; current_error := new
   |}.

Definition shortcut_view (s : state) : nat * list shortcut_token :=
  match shortcut s with
  | number_token n :: l => (n, l)
  | l => (1, l)
  end.

Definition run_shortcut (s : state) : state :=
  match mode s , shortcut_view s with
  | normal , (1 , [ascii_token "["; ascii_token "A"]) (* up arrow key *) =>
    set_shortcut [] (set_document (move_up (document s)) s)
  | normal , (1 , [ascii_token "["; ascii_token "B"]) (* down arrow key *) =>
    set_shortcut [] (set_document (move_down (document s)) s)
  | normal , (1 , [ascii_token "["; ascii_token "D"]) (* left arrow key *) =>
    set_shortcut [] (set_document (move_left (document s)) s)
  | normal , (1 , [ascii_token "["; ascii_token "C"]) (* right arrow key *) =>
    set_shortcut [] (set_document (move_right (document s)) s)
  | normal , (n , [ascii_token ":"]) =>
    set_shortcut [] (set_mode (command []) s)
  | normal , (n , [ascii_token "a"]) =>
    set_shortcut [] (set_mode insert (set_document (move_right (document s)) s))
  | normal , (n , [ascii_token "i"]) =>
    set_shortcut [] (set_mode insert (set_document (document s) s))
  | normal , (n , [ascii_token "h"]) =>
    set_shortcut [] (set_document (apply n move_left (document s)) s)
  | normal , (n , [ascii_token "j"]) =>
    set_shortcut [] (set_document (apply n move_down (document s)) s)
  | normal , (n , [ascii_token "k"]) =>
    set_shortcut [] (set_document (apply n move_up (document s)) s)
  | normal , (n , [ascii_token "l"]) =>
    set_shortcut [] (set_document (apply n move_right (document s)) s)
  | normal , (n , [ascii_token "0"]) =>
    set_shortcut [] (set_document (move_start_of_line (document s)) s)
  | normal , (n , [ascii_token "$"]) =>
    set_shortcut [] (set_document (move_end_of_line (document s)) s)
  | normal , (n , [ascii_token "O"]) =>
    set_shortcut [] (set_mode insert (set_document (insert_new_line_before (document s)) s))
  | normal , (n , [ascii_token "o"]) =>
    set_shortcut [] (set_mode insert (set_document (insert_new_line_after (document s)) s))
  | normal , (n , [ascii_token "x"]) =>
    set_shortcut [] (set_document (apply n delete_char_right (document s)) s)
  | normal , (n , [ascii_token "d"; ascii_token "d"]) =>
    set_shortcut [] (set_document (apply n delete_current_line (document s)) s)
  | normal , (n , [ascii_token "r"; ascii_token c]) =>
    set_shortcut [] (set_document (apply_with_sep n move_right (replace_char c) (document s)) s)
  | normal , (n , [ascii_token "R"]) =>
    set_shortcut [] (set_mode replace s)
  | normal , (n , [ascii_token "f"; ascii_token c]) =>
    set_shortcut [] (set_document (move_next_occurrence_on_line (Ascii.eqb c) (document s)) s)
  | normal , (n , [ascii_token "F"; ascii_token c]) =>
    set_shortcut [] (set_document (move_prev_occurrence_on_line (Ascii.eqb c) (document s)) s)
  | normal , (n , [ascii_token "w"]) =>
    set_shortcut [] (set_document (apply n move_start_of_next_word_on_line (document s)) s)
  | normal , (n , [ascii_token "b"]) =>
    set_shortcut [] (set_document (apply n move_start_of_prev_word_on_line (document s)) s)
  | normal , (n , [ascii_token "e"]) =>
    set_shortcut [] (set_document (apply n move_end_of_next_word_on_line (document s)) s)
  | _ , (_ , _) => s
  end.

Definition save_file (s : state) : C.M unit :=
  match current_file s with
  | None => C.pure tt
  | Some file_name =>
    C.write_to_file file_name (all_content (document s)) ;;
    C.pure tt
  end.

Definition exit (w : C.window) : C.M unit :=
  C.close_window w ;; C.exit success.

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
  command <- C.make_style black green ;;
  replace <- C.make_style black red ;;
  C.pure  {| default_style := default
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

Definition render (w : C.window) (styles : style_set) (s : state)  : C.M unit :=
  let fix render_line (l : list (list ascii)) (row : int) : C.M unit :=
    match l with
    | [] =>
      C.pure tt
    | x :: xs =>
      C.move_cursor w row 0 ;;
      C.print w x ;;
      render_line xs (add 1 row)
    end in
  C.clear w ;;
  size <- C.get_size w ;;
  let '(screen_rows, screen_cols) := size in
  C.move_cursor w (sub screen_rows 2) 0 ;;
  let mode_style := style_of_mode styles (mode s) in
  C.start_style mode_style ;;
  C.print w (repeat " " (nat_of_int screen_cols)) ;;
  C.move_cursor w (sub screen_rows 2) 0 ;;
  C.print w (string_of_edit_mode (mode s)) ;;
  C.end_style mode_style ;;
  C.move_cursor w (sub screen_rows 1) 0 ;;
  match current_error s, mode s with
  | Some e , _ => C.print w (string_of_error e)
  | _ , command l => C.print w (":" :: l)
  | _ , _ => C.print w (string_of_shortcut_tokens (shortcut s))
  end ;;
  render_line (lines (document s)) 0%int63 ;;
  let (cursor_row, cursor_col) := cursor_position (document s) in
  C.move_cursor w (int_of_N cursor_row) (int_of_N cursor_col) ;;
  C.refresh w.

CoFixpoint loop (w : C.window) (styles : style_set) (s : state) : C.M unit :=
  cur <- C.get_cursor w ;;
  let (y, x) := cur in
  c <- C.get_char w ;;
  s' <- react c w s ;;
  let s' := run_shortcut s' in
  render w styles s' ;;
  loop w styles s'.

Definition main (args : list (list ascii)) : C.M unit :=
  match args with
  | [] =>
    w <- C.new_window ;;
    styles <- make_styles ;;
    C.set_window_default_style w (default_style styles) ;;
    render w styles initial_state ;;
    loop w styles initial_state ;;
    C.close_window w
  | file_name :: [] =>
    content' <- C.read_file file_name ;;
    let s :=
      match content' with
      | inl e => set_current_error (Some e) initial_state
      | inr content =>
        let d := match split newline content with
                 | [] => initial_text_zipper
                 | line :: lines =>
                   {| above := [] ; to_left := [] ; to_right := line ; below := lines |} end in
        set_current_file (Some file_name) (set_document d initial_state)
      end in
    w <- C.new_window ;;
    styles <- make_styles ;;
    C.set_window_default_style w (default_style styles) ;;
    render w styles s ;;
    loop w styles s ;;
    exit w
  | _ => C.exit failure
  end.
