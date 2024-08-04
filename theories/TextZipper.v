Require Import PrimInt63 NArith Ascii List.

Import ListNotations.

Fixpoint split_aux (acc : list ascii) (sep : ascii) (s : list ascii) : list (list ascii) :=
  match s with
  | [] => acc :: nil
  | c :: s' =>
      if Ascii.eqb sep c
      then acc :: split_aux [] sep s'
      else split_aux (acc ++ [c]) sep s'
  end.

Definition split (c : ascii) (s : list ascii) : list (list ascii) :=
  split_aux [] c s.

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

Definition cursor_position (tz : text_zipper) : nat * nat :=
  (length (above tz), length (to_left tz)).

Definition current_line (tz : text_zipper) : list ascii :=
  to_left tz ++ to_right tz.

Definition lines (tz : text_zipper) : list (list ascii) :=
  above tz ++ [current_line tz] ++ below tz.

Definition under_cursor (tz : text_zipper) : option ascii :=
  match to_right tz with
  | c :: _ => Some c
  | _ => None
  end.

Definition newline : ascii :=
  Ascii false true false true false false false false.

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

Definition peek_last {A : Type} (l : list A) : option (list A * A) :=
  match rev l with
  | [] => None
  | x :: xs => Some (rev xs, x)
  end.

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

Definition delete_char_right (tz : text_zipper) : text_zipper :=
  match to_right tz with
  | _ :: xs => {| above := above tz
                ; to_left := to_left tz
                ; to_right := xs
                ; below := below tz
                |}
  | _ => tz
  end.
