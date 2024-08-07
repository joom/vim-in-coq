Require Import PrimInt63 Ascii List.
Require Import Vim.Helpers.

Import ListNotations.

Local Open Scope char_scope.

(* TODO implement above and to_left as snoc lists *)
Record text_zipper : Type :=
 { above : list (list ascii)
 ; to_left : list ascii
 ; to_right : list ascii
 ; below : list (list ascii)
 }.

Definition initial_text_zipper : text_zipper :=
  {| above := []
   ; to_left := []
   ; to_right := []
   ; below := []
   |}.

Definition cursor_position (tz : text_zipper) : int * int :=
  (length_int (above tz), length_int (to_left tz)).

Definition current_line (tz : text_zipper) : list ascii :=
  to_left tz ++ to_right tz.

Definition lines (tz : text_zipper) : list (list ascii) :=
  above tz ++ [current_line tz] ++ below tz.

Definition all_content (tz : text_zipper) : list ascii :=
  let fix aux (l : list (list ascii)) : list ascii :=
    match l with
    | [] => []
    | [x] => x
    | x :: xs => x ++ [newline] ++ aux xs
    end in
  aux (lines tz).

Definition peek_last {A : Type} (l : list A) : option (list A * A) :=
  match rev l with
  | [] => None
  | x :: xs => Some (rev xs, x)
  end.

Definition peek_under_cursor (tz : text_zipper) : option ascii :=
  match to_right tz with
  | c :: _ => Some c
  | _ => None
  end.

Definition peek_next_cursor (tz : text_zipper) : option ascii :=
  match to_right tz with
  | _ :: c :: _ => Some c
  | _ => None
  end.

Definition peek_prev_cursor (tz : text_zipper) : option ascii :=
  match peek_last (to_left tz) with
  | Some (_, x) => Some x
  | _ => None
  end.

Definition break_line (tz : text_zipper) : text_zipper :=
  {| above := above tz ++ [to_left tz]
   ; to_left := []
   ; to_right := to_right tz
   ; below := below tz
   |}.

Definition insert_char_left (c : ascii) (tz : text_zipper) : text_zipper :=
  if Ascii.eqb c newline then break_line tz else
  {| above := above tz
   ; to_left := to_left tz ++ [c]
   ; to_right := to_right tz
   ; below := below tz
   |}.

Definition insert_char_right (c : ascii) (tz : text_zipper) : text_zipper :=
  if Ascii.eqb c newline then break_line tz else
  {| above := above tz
   ; to_left := to_left tz
   ; to_right := c :: to_right tz
   ; below := below tz
   |}.

Definition move_left (tz : text_zipper) : text_zipper :=
  match peek_last (to_left tz) with
  | Some (xs, x) => {| above := above tz
                     ; to_left := xs
                     ; to_right := x :: to_right tz
                     ; below := below tz
                     |}
  | _ => tz
  end.

Definition move_right (tz : text_zipper) : text_zipper :=
  match to_right tz with
  | x :: xs => {| above := above tz
                ; to_left := to_left tz ++ [x]
                ; to_right := xs
                ; below := below tz
                |}
  | _ => tz
  end.

Definition move_up (tz : text_zipper) : text_zipper :=
  match peek_last (above tz) with
  | Some (xs, x) => {| above := xs
                     ; to_left := []
                     ; to_right := x
                     ; below := current_line tz :: below tz
                     |}
  | _ => tz
  end.

Definition move_down (tz : text_zipper) : text_zipper :=
  match below tz with
  | x :: xs => {| above := above tz ++ [current_line tz]
                ; to_left := []
                ; to_right := x
                ; below := xs
                |}
  | _ => tz
  end.

Definition move_start_of_line (tz : text_zipper) : text_zipper :=
  {| above := above tz
   ; to_left := []
   ; to_right := current_line tz
   ; below := below tz
   |}.

Definition move_end_of_line (tz : text_zipper) : text_zipper :=
  {| above := above tz
   ; to_left := current_line tz
   ; to_right := []
   ; below := below tz
   |}.

Definition move_next_occurrence_on_line (p : ascii -> bool) (tz : text_zipper) : text_zipper :=
  match peek_under_cursor tz, break p (tail (to_right tz)) with
  | Some cur, Some (xs, x, ys) =>
      {| above := above tz
       ; to_left := to_left tz ++ [cur] ++ xs
       ; to_right := x :: ys
       ; below := below tz
       |}
  | _, _ => tz
  end.

Definition move_prev_occurrence_on_line (p : ascii -> bool) (tz : text_zipper) : text_zipper :=
  match break p (rev (to_left tz)) with
  | None => tz
  | Some (ys, x, xs) => {| above := above tz
                         ; to_left := rev xs
                         ; to_right := x :: rev ys ++ to_right tz
                         ; below := below tz
                         |}
  end.

Definition move_start_of_next_word_on_line (tz : text_zipper) : text_zipper :=
  move_next_occurrence_on_line isnt_space (move_next_occurrence_on_line is_space tz).

Definition move_start_of_prev_word_on_line (tz : text_zipper) : text_zipper :=
  match peek_prev_cursor tz with
  | None => tz
  | Some " " => move_right (move_prev_occurrence_on_line is_space
                            (move_prev_occurrence_on_line isnt_space (move_left tz)))
  | _ => move_right (move_prev_occurrence_on_line is_space tz)
  end.

Definition move_end_of_next_word_on_line (tz : text_zipper) : text_zipper :=
  match peek_next_cursor tz with
  | None => tz
  | Some " " => move_left (move_next_occurrence_on_line is_space
                            (move_next_occurrence_on_line isnt_space (move_right tz)))
  | _ => move_left (move_next_occurrence_on_line is_space tz)
  end.

Definition insert_new_line_before (tz : text_zipper) : text_zipper :=
  {| above := above tz
   ; to_left := []
   ; to_right := []
   ; below := current_line tz :: below tz
   |}.

Definition insert_new_line_after (tz : text_zipper) : text_zipper :=
  {| above := above tz ++ [current_line tz]
   ; to_left := []
   ; to_right := []
   ; below := below tz
   |}.

Definition delete_char_left (tz : text_zipper) : text_zipper :=
  match peek_last (to_left tz) with
  | Some (xs, _) => {| above := above tz
                     ; to_left := xs
                     ; to_right := to_right tz
                     ; below := below tz
                     |}
  | _ => tz
  end.

Definition delete_char_right (tz : text_zipper) : text_zipper :=
  match to_right tz with
  | _ :: xs => {| above := above tz
                ; to_left := to_left tz
                ; to_right := xs
                ; below := below tz
                |}
  | _ => tz
  end.

Definition replace_char (c : ascii) (tz : text_zipper) : text_zipper :=
  match to_right tz with
  | _ :: xs => {| above := above tz
                ; to_left := to_left tz
                ; to_right := c :: xs
                ; below := below tz
                |}
  | _ => tz
  end.

Definition delete_current_line (tz : text_zipper) : text_zipper :=
  match below tz with
  | x :: xs => {| above := above tz
                ; to_left := []
                ; to_right := x
                ; below := xs
                |}
  | _ => match peek_last (above tz) with
         | Some (xs , x) => {| above := xs
                             ; to_left := []
                             ; to_right := x
                             ; below := below tz
                             |}
         | None => {| above := above tz
                    ; to_left := []
                    ; to_right := []
                    ; below := below tz
                    |}
         end
  end.

Definition text_zipper_of_string (content : list ascii) : text_zipper :=
  match split newline content with
  | [] => initial_text_zipper
  | line :: lines =>
      {| above := [] ; to_left := [] ; to_right := line ; below := lines |}
  end.

Definition calculate_movement (before after : text_zipper) : int * int :=
  (PrimInt63.sub (length_int (above after)) (length_int (above before)),
   PrimInt63.sub (length_int (to_left after)) (length_int (to_left before))).

Require Import String.

Definition x := text_zipper_of_string (List.concat
                 [(list_ascii_of_string "hi there man"%string)
                 ; [newline]
                 ;(list_ascii_of_string "how are you doing"%string)
                 ; [newline]
                 ;(list_ascii_of_string "I hope you're okay"%string)
                 ]).

Compute x.
Compute (calculate_movement (move_down x) x).
