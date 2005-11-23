(* logical verification week 11 2005 - 2006 *)

(*
  Martijn Vermaat
  mvermaat
  1362917
*)

Section examples.

(* exercise 1: examples from the course *)

Lemma example1: forall a:Prop, (forall b:Prop, b) -> a.

Lemma example2: forall a:Prop, a -> (forall b:Prop, ((a -> b) -> b)).

Lemma example3: forall a:Prop, (exists b:Prop, a) -> a.

Lemma example4: forall a:Prop, exists b:Prop, ((a -> b) \/ (b -> a)).

Hypothesis classical: forall a:Prop, a \/ ~a.
Lemma example5: forall a b:Prop, ((a -> b) \/ (b -> a)). 

Abort All.

End examples.

(* in prop2 (intuitionistic)
   the logical connectives false, and, or can be defined *)

(* definition of false *)

Definition new_false := forall a:Prop, a.

(* exercise 2:
   prove two theorems that together show the 
   logical equivalence of new_false and False *)

Theorem False_from_new_false: new_false -> False.

Proof.
intro H.
apply H.
Qed.

Theorem new_false_from_False: False -> new_false.

Proof.
intro H.
elim H.
Qed.

(*
Proof.
intro H.
elimtype False.
exact H.
Qed.
*)


(* exercise 3:
   prove the following theorem *)

Theorem ef : forall a:Prop, new_false -> a.

Proof.
intro.
intro H.
apply H.
Qed.

Print ef.

(* definition of and *)
(* "a and b" is valid is everything that can be 
   derived from {a,b} is valid *)

Definition new_and (a b : Prop) := forall c : Prop, (a -> b -> c) -> c.

(* exercise 4 : 
   prove two theorems that together show the 
   equivalence of new_and and /\ *)

Theorem and_from_new_and: forall (a b: Prop), (new_and a b) -> a /\ b.

Proof.
intro a.
intro b.
intro H.
apply conj.
apply H.
intro H'.
intro.
exact H'.
apply H.
intro.
intro H'.
exact H'.
Qed.

Theorem new_and_from_and: forall (a b: Prop), a /\ b -> (new_and a b).

Proof.
intro a.
intro b.
intro H.
intro c.
intro H'.
apply H'.
elim H.
intro H''.
intro.
exact H''.
elim H.
intro.
intro H''.
exact H''.
Qed.

(* exercise 5 :
   find an inhabitant P of type
   forall a b : Prop, a -> b -> new_and a b 
   you can use "Definition" and "Check" *)

Definition P := fun (a b: Prop) (n:a) (m:b) =>
  fun (c:Prop) (d:(a->b->c)) => d n m.
Check P.
Check new_and.

Theorem prove_P: forall a b : Prop, a -> b -> new_and a b.

Proof.
intro a.
intro b.
intro Ha.
intro Hb.
unfold new_and.
intro c.
intro Hand.
apply Hand.
exact Ha.
exact Hb.
Qed.

Print prove_P.

(* ja het is nog dezelfde ook *)

(* "a or b" is valid if everything that follows form
   {a} and follows from {b} is valid *)

(* exercise 6 : complete the following definition of new_or *)

Definition new_or (a b : Prop) := forall (c:Prop), (a->c) -> (b->c) -> c.

(* exercise 7 : 
   prove two theorems that together show the 
   equivalence of new_or and \/ *)  

Theorem or_from_new_or: forall (a b: Prop), (new_or a b) -> a \/ b.

Proof.
intro a.
intro b.
intro H.
apply H.
intro Ha.
left.
exact Ha.
intro Hb.
right.
exact Hb.
Qed.

Theorem new_or_from_or: forall (a b: Prop), a \/ b -> (new_or a b).

Proof.
intro a.
intro b.
intro H.
unfold new_or.
intro c.
intro Hor1.
intro Hor2.
elim H.
exact Hor1.
exact Hor2.
Qed.

(* using polymorphism we can define data-types like
   natural numbers and booleans
   Coq uses inductive definitions because that is 
   more efficient *)

(* booleans *)

Definition new_bool := forall a : Set, a -> a -> a.
Definition t (a : Set) (x y : a) := x.
Definition f (a : Set) (x y : a) := y.

(* exercise 8 
   not obliged, see maybe iti 
   give a definition of new_not : new_bool -> new_bool
   for negation on new_bool
   and test it on two different inputs *)

(*
Definition new_not (b: new_bool) :=
  fun (a:Set) (n m: a) =>
*)

(*
Definition new_not (b : forall a: Set, a -> a -> a) :=
  b    f t.
*)

(* natural numbers *)

Definition new_nat := forall a : Set, a -> (a -> a) -> a. 

(* polymorphic Church numbers *)

Definition zero (a : Set) (z : a) (s : a -> a) := z.
Definition one (a : Set) (z : a) (s : a -> a) := s z.
Definition two (a : Set) (z : a) (s : a -> a) := s (s z).

Check new_nat.

(* exercise 9 
   not obliged, see maybe iti
   give a definition of successor : new_nat -> new_nat
   and check it on two different inputs *)

