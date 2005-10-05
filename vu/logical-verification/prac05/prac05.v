(* logical verification 05-06 practical work week 5 *)

(*
  Martijn Vermaat
  mvermaat
  1362917
*)


Section menu.

Inductive menu : Set :=
| starter : menu
| main_dish : menu
| desert : menu .

Check menu_rec .
Check menu_ind .

End menu .

Section booleans .

Print bool.

Theorem bool_equal : forall b:bool, b = true \/ b = false.

Proof .
intro b.
elim b .
left .
reflexivity .
right. 
reflexivity .
Qed. 

Definition bool_not (b:bool) : bool := 
match b with
| true => false
| false => true
end .

Definition bool_or (b b':bool) := 
match b with
| true => true
| false => b'
end.

Theorem excludedmiddelebool : forall b:bool , (bool_or b (bool_not b)) = true.

Proof .
intro b .
elim b .
simpl .
reflexivity .
simpl .
reflexivity .
Qed.

(* practical work 5 exercise 1) *)

Theorem bool_not_not : forall b:bool , (bool_not (bool_not b))=b.

Proof.
induction b.

(* b = true *)
simpl.
reflexivity.

(* b = false *)
simpl.
reflexivity.

Qed.

(* practical work 5 exercise 2 *)
Definition bool_and (b b': bool) : bool :=
match b with
| true => b'
| false => false
end.

(* practical work 5 exercise 3 *)

Theorem notand : forall b:bool, (bool_and b (bool_not b)) = false. 

Proof.
induction b.

(* b = true *)
simpl.
reflexivity.

(* b = false *)
simpl.
reflexivity.

Qed.

End booleans .

Section naturals.

Print nat .

Inductive even : nat -> Prop :=
| evenO : even O
| evenSS : forall n:nat , even n -> even (S (S n)) .

Theorem evenzero : (even O) .

Proof .
apply evenO .
Qed .

Theorem evenss : forall n:nat , (even n) -> (even (S (S n))) .

Proof.
exact evenSS.
Qed .

(*
alternative proof:

intro n.
intro H .
apply evenSS .
exact H .
Qed .
*)

Theorem eventwo : (even 2 ).

Proof .
apply evenSS .
apply evenO .
Qed .

Check evenO.
Check evenSS .
Check eventwo .
Print eventwo .

Theorem noteven1 : ~(even 1) .

Proof.
unfold not .
intro H .
inversion H .
Qed .

Theorem noteven3 : ~(even 3) .

Proof.
unfold not .
intro H .
inversion H .
exact (noteven1 H1).
Qed .

Inductive ev : nat -> Prop :=
| evO : ev O
| evS : forall n:nat , odd n -> ev (S n)
with odd : nat -> Prop :=
| oddS : forall n:nat , ev n -> odd (S n) .

(* practical work 5 exercise 4a *)

Theorem zero : (ev O). 

Proof.
exact evO.
Qed.

(* practical work 5 exercise 4b *)

Theorem one : (odd 1). 

Proof.
constructor.
constructor.
Qed.

(* practical work 5 exercise 4c *)

Theorem two : (ev 2) .

Proof.
apply evS.
exact one.
Qed.

(* practical work 5 exercise 4d *)
(* use inversion *)

Theorem twoa : ~(odd 2). 

Proof.
unfold not.
intro.
inversion H.
inversion H1.
inversion H3.
Qed.

Theorem evorodd : forall n:nat, ev n \/ odd n .

Proof.
intro n.
induction n.
left.
apply evO.
inversion IHn.
right.
apply oddS.
exact H.
left.
apply evS.
exact H.
Qed.

Inductive le (n:nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m:nat , le n m -> le n (S m) .

Theorem zero_and_zero : le O O . 

Proof .
apply le_n .
Qed .

Theorem zero_and_one  : le 0 1 .

Proof .
apply le_S .
apply le_n .
Qed .

Print zero_and_one .
Check zero_and_one .

Theorem one_and_zero : ~ (le 1 0) .

Proof.
unfold not.
intro H .
inversion H .
Qed .

End naturals .

Section lists .

Inductive natlist : Set :=
| nil : natlist 
| cons : nat -> natlist -> natlist .

Fixpoint natmap (f:nat -> nat)(l:natlist) {struct l} : natlist :=
match l with
| nil => nil 
| cons h t => cons (f h) (natmap f t)
end .

Check (plus 3) .

Eval compute in (natmap (plus 3) (cons O nil)) .
Eval compute in (natmap (plus 3) (cons O (cons 1 (cons 2 nil)))) .

(* practical work 5 exercise 5 *)

Inductive boollist : Set :=
| empty : boollist
| bcons : bool -> boollist -> boollist.


(* practical work 5 exercise 6 *)

Fixpoint boolmap (f : bool -> bool) (l : boollist) {struct l} : boollist :=
  match l with
    | empty => empty
    | bcons h t => bcons (f h) (boolmap f t)
      end.

Eval compute in (boolmap bool_not empty).
(*
     = empty
     : boollist
*)
Eval compute in (boolmap bool_not (bcons true (bcons false empty))).
(*
     = bcons false (bcons true empty)
     : boollist
*)

Inductive sorted : natlist -> Prop :=
| sortedO : sorted nil
| sorted1 : forall n:nat , sorted (cons n nil) 
| sorted2 : forall n h:nat , forall t:natlist ,
            le n h -> sorted (cons h t) -> sorted (cons n (cons h t)) .

Theorem sortednil : sorted nil .

Proof .
apply sortedO .
Qed .

Theorem sortedone : sorted (cons 0 nil) .

Proof .
apply sorted1 .
Qed .

(* practical work 5 exercise 7 *)

Theorem sortedonetwothree : sorted (cons 1 (cons 2 (cons 3 nil))). 

Proof.
constructor.
constructor.
constructor.
constructor.
constructor.
constructor.
constructor.
Qed.

(* practical work 5 exercise 8 *)

Theorem sortedtail :
  forall n:nat , forall l:natlist , 
  sorted (cons n l) -> sorted l. 

Proof.
intro n.
intro l.
intro H.
inversion H.

constructor.

exact H3.

Qed.

(*
  Alternative:

induction l.
intro.
constructor.

intro.
inversion H.
exact H4.
*)


End lists .

Section bintrees .

Inductive bintree : Set := 
| leaf : bintree 
| node : bintree -> bintree -> bintree.

(* practical work 5 exercise 9 *)
(* build 3 different bintrees *)

Definition tree1 := leaf.
Definition tree2 := node leaf leaf.
Definition tree3 := node (node leaf leaf) (node (node leaf leaf) leaf).


Inductive natbintree : Set :=
| natleaf : nat -> natbintree
| natnode : nat -> natbintree -> natbintree -> natbintree .

(* practical work 5 exercise 10 *)
(* not obligatory *)
(* 
  define equality of natural numbers with output a booleanm
  use nested matching
*)

Fixpoint nat_eq_bool (n m : nat) {struct n} : bool :=
  match n with
    | O => match m with
             | O => true
             | _ => false
           end
    | S p => match m with
               | O => false
               | S q => nat_eq_bool p q
             end
  end.
  

(* test *)
Eval compute in (nat_eq_bool 0 0).
(*
     = true
     : bool
*)
Eval compute in (nat_eq_bool 0 1).
(*
     = false
     : bool
*)


(* practical work 5 exercise 11 *)
(* not obligatory *)
(*
  define a function
  presentintree 
  that checks whether a natural number occurs in a natbintree
  the outputtype is bool
*)

Fixpoint presentintree (n: nat) (b: natbintree) {struct b} : bool :=
  match b with
    | natleaf m => nat_eq_bool n m
    | natnode m c d => bool_or (nat_eq_bool n m)
                               (bool_or (presentintree n c)  (presentintree n d))
      end.

Eval compute in (presentintree 3 (natleaf 3)). 
(*
     = true
     : bool
*)
Eval compute in (presentintree 3 (natleaf 1)). 
(*
     = false
     : bool
*)


End bintrees .

Section leibniz .

Inductive eq (A:Set)(x:A) : A -> Prop :=
  refl_equal : eq A x x .

Check (eq nat 3) .
Check (refl_equal nat 3) .

End leibniz .
