(* logical verification 05-06 practical work week 4 *)

(*
  Martijn Vermaat
  mvermaat
  1362917
*)

Check bool.
Print bool.

(* example : function on booleans,
   two equivalent ways of writing *)

Definition donothinga (b : bool) : bool :=
  match b with
  | true => true
  | false => false
  end.

Definition donothingb : bool -> bool :=
  fun b : bool =>
  match b with
  | true => true
  | false => false
  end.

(* example: definitions of negation *)
Definition nega (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition negb : bool -> bool :=
  fun x : bool =>
  match x with
  | true => false
  | false => true
  end.

Lemma aboutneg : forall b : bool, b = true \/ nega b = true.

Proof.
intro b.
elim b.
(* or instead of intro and elim do induction b . *)
(* or use bool_ind *)

(* case b = true *)
left.
reflexivity.

(* case b = false *)
right.
simpl.
reflexivity.
Qed.

Check nat.
Print nat.

(* example : addition with recursion in the first argument *)
Fixpoint plus (n m : nat) {struct n} : nat :=
  match n with
  | O => m
  | S p => S (plus p m)
  end.

Eval compute in (plus 0 0).

(* example : addition with recursion in the second argument *)
Fixpoint plus2 (n m : nat) {struct m} : nat :=
  match m with
  | O => n
  | S p => S (plus2 n p)
  end.

(*
nat_ind =
fun P : nat -> Prop => nat_rect P
     : forall P : nat -> Prop,
       P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
*)

Lemma plus_n_O : forall n : nat, n = plus n 0.

Proof.
intro n.
elim n.
(* alternative: induction n or use nat_ind *)

(* case n = O *)
simpl.
reflexivity.

(* case n > O *)
intro p.
intro IH.
simpl.
rewrite <- IH.
reflexivity.
Qed.

(* exercise 1 : define multiplication
                with recursion in the first argument *)

Fixpoint mul (n m : nat) { struct n } : nat :=
    match n with
    | 0 => 0
    | S p => plus (mul p m) m
    end.

Eval compute in (mul 4 9).
(*
     = 36
     : nat
*)
Eval compute in (mul (S 0) (S (S 0))).
(*
     = 2
     : nat
*)

(* exercise 2 *)
Lemma mul_n_O : forall n : nat, mul n 0 = 0.

Proof.
induction n.

(* n = 0 *)
simpl.
reflexivity.

(* n = m + 1 *)
simpl.
rewrite -> IHn.
simpl.
reflexivity.
Qed.

(* exercise 3: give an inductive definition of
   the finite lists of natural numbers *)
Print nat.
Inductive natlist : Set :=
    empty : natlist | cons : nat -> natlist -> natlist.

(* exercise 4: define length *)
Fixpoint length (l : natlist) { struct l } : nat :=
    match l with
    | empty => 0
    | cons _ tail => (length tail) + 1
    end.

Eval compute in (length empty).
(*
     = 0
     : nat
*)
Eval compute in (length (cons 4 (cons 2 (cons 8 empty)))).
(*
     = 3
     : nat
*)

(* exercise 5: define append *)
Fixpoint append (a b : natlist) { struct a } : natlist :=
    match a with
    | empty => b
    | cons h t => cons h (append t b)
    end.

Eval compute in (append empty empty).
(*
     = empty
     : natlist
*)
Eval compute in (append (cons 4 empty) (cons 2 empty)).
(*
     = cons 4 (cons 2 empty)
     : natlist
*)
Eval compute in (append (cons 3 (cons 2 empty)) (cons 7 empty)).
(*
     = cons 3 (cons 2 (cons 7 empty))
     : natlist
*)

(* exercise 6 *)
Lemma length_append :
 forall k l : natlist, length (append k l) = plus (length k) (length l).

(*

intro k.
intro l.
induction k.

(* k = nil *)
simpl.
reflexivity.

(* k  = cons *)
simpl.
rewrite -> IHk.
(* hmmm kom hier niet uit, zal wel iets missen ... *)

(*
Femke says: je hebt een beetje
pech met je definitie van length.
Als je had gedaan 
  1 + length tail
of
  S (lenghth tail)
dan was het heel makkelijk geweest. Nu heb 
je iets nodig als
  plus (plus a b) c = plus (plus a c) b
oid en dat is gedoe ...
*)

*)
