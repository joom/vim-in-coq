Require Import PrimInt63 NArith Ascii List.

Import ListNotations.

Local Open Scope char_scope.

Definition break {A : Type}
           (p : A -> bool) (l : list A) : option (list A * A * list A) :=
  let fix aux (l1 l2 : list A) :=
    match l2 with
    | [] => None
    | x :: xs => if p x
                 then Some (rev l1, x, xs)
                 else aux (x :: l1) xs
    end
  in aux [] l.


Fixpoint Nlength {A : Type} (l : list A) : N :=
  match l with
  | [] => 0%N
  | _ :: l' => N.succ (Nlength l')
  end.

Definition is_space (a : ascii) : bool := Ascii.eqb " " a.
Definition isnt_space (a : ascii) : bool := negb (Ascii.eqb " " a).

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

Definition cursor_position (tz : text_zipper) : N * N :=
  (Nlength (above tz), Nlength (to_left tz)).

Definition current_line (tz : text_zipper) : list ascii :=
  to_left tz ++ to_right tz.

Definition lines (tz : text_zipper) : list (list ascii) :=
  above tz ++ [current_line tz] ++ below tz.

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
