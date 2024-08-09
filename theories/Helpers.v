Require Import PrimInt63 NArith Ascii List.

Import ListNotations.
Open Scope char_scope.

Definition string_of_nat (n : nat) : list ascii :=
  let fix aux (fuel n : nat) (acc : list ascii) : list ascii :=
    let d := match Nat.modulo n 10 with
             | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
             | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
             end in
    let acc' := d :: acc in
    match fuel with
    | 0 => acc'
    | S fuel' =>
      match Nat.div n 10 with
      | 0 => acc'
      | n' => aux fuel' n' acc'
      end
    end in aux n n [].

Definition split (c : ascii) (l : list ascii) : list (list ascii) :=
  let fix aux acc sep l :=
    match l with
    | [] => acc :: nil
    | c :: l' =>
        if Ascii.eqb sep c
        then acc :: aux [] sep l'
        else aux (acc ++ [c]) sep l'
    end in aux [] c l.

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

Definition is_space (a : ascii) : bool := Ascii.eqb " " a.
Definition isnt_space (a : ascii) : bool := negb (Ascii.eqb " " a).

Definition newline : ascii :=
  Ascii false true false true false false false false.

Fixpoint apply {A : Type} (n : nat) (f : A -> A) (a : A) : A :=
  match n with
  | O => a
  | S n' => apply n' f (f a)
  end.

Fixpoint apply_with_sep {A : Type} (n : nat) (sep : A -> A) (f : A -> A) (a : A) : A :=
  match n with
  | O => a
  | S O => f a
  | S ((S _) as n') => apply_with_sep n' sep f (sep (f a))
  end.

Fixpoint length_N {A : Type} (l : list A) : N :=
  match l with
  | [] => 0%N
  | _ :: l' => N.succ (length_N l')
  end.

Fixpoint length_Z {A : Type} (l : list A) : Z :=
  match l with
  | [] => Z0
  | _ :: l' => BinInt.Z.succ (length_Z l')
  end.

Fixpoint length_int {A : Type} (l : list A) : int :=
  match l with
  | [] => 0%int63
  | _ :: l' => PrimInt63.add (length_int l') 1
  end.

Fixpoint firstn_int {A : Type} (i : int) (l : list A) : list A :=
  if PrimInt63.leb i 0 then [] else
  match l with
  | [] => []
  | x :: xs => x :: firstn_int (PrimInt63.sub i 1) xs
  end. 

Fixpoint skipn_int {A : Type} (i : int) (l : list A) : list A :=
  if PrimInt63.leb i 0 then l else
  match l with
  | [] => []
  | x :: xs => skipn_int (PrimInt63.sub i 1) xs
  end. 
