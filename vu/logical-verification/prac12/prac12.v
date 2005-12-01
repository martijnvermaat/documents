(* reference: Herman Geuvers webpage *)
(* practical work 12: make a selection of at least 6 exercises *)

(*
  Martijn Vermaat
  mvermaat
  1362917
*)

Section prop1.
Variable A B C : Prop.

(* exercise 1 *)
Theorem prop11 : (A -> B -> C) -> (A -> B) -> A -> C.

Proof.
intro Habc.
intro Hab.
intro Ha.
apply Habc.
exact Ha.
apply Hab.
exact Ha.
Qed.

(* use Print to find see the inhabitant
   correponding to the proof *)

(* try to find inhabitant of (A->B->C)->(A->b)->A->C *)

Definition inh11 :=
  fun (x:(A->B->C)) (y:(A->B)) (z:A) =>
    x z (y z).
Check inh11.

Print prop11.

(* exercise 2 *)
Theorem prop12 : ((A -> B -> A) -> A) -> A.

Proof.
intro H.
apply H.
intro H'.
intro H''.
exact H'.
Qed.

(* use Print to find see the inhabitant
   correponding to the proof *)

(* find inhabitant of ((A->B->A)->A)->A *)

Definition inh12 :=
  fun (x:((A->B->A)->A)) =>
    x (fun (y:A) (z:B) => y).
Check inh12.

Print prop12.

(* exercise 3 *)
(* complete the following simply typed lambda terms *)

Definition prop13 := fun (x : (A->B->C)) (y : (A->B)) (z : A) => x z (y z).
Definition prop14 := fun (x : (A->B->C)) (y : (B->A)) (z : B) => x (y z) z.
Definition prop15 := fun (x : (A->B)->B->C) (y : B) => x (fun z : A => y) y.
Definition prop16 := fun (x : A->B->C) (y : (A->B->C)->A) (z : (A->B->C)->B) => x (y x) (z x).

End prop1.

(* **************************************************************** *)

Section poly_dep.
(* prop representing the propositions is declared as a Set *)
Parameter prop : Set.
(* implication on prop is a binary operator *)
Parameter imp : prop -> prop -> prop. 
(* we can use infix notation => for imp *)
Infix "=>" := imp (right associativity, at level 85).

(* T expresses if a proposion in prop is valid
   if (T p) is inhabited then p is valid 
   if (T p) is not inhabited then p is not valid *)
Parameter T : prop -> Prop.
(* the variable imp_introduction models the introduction rule for imp *)
Parameter imp_introduction : forall p q : prop, (T p -> T q) -> T (p => q).
(* the variable imp_elimination models the elimination rule for imp *)
Parameter imp_elimination : forall p q : prop, T (p => q) -> T p -> T q.

Parameter conjunction : prop -> prop -> prop.
Infix "X" := conjunction (no associativity, at level 90).
Parameter
  conjunction_introduction : forall p q : prop, T p -> T q -> T (p X q).
Parameter conjunction_elimination_l : forall p q : prop, T (p X q) -> T p.
Parameter conjunction_elimination_r : forall p q : prop, T (p X q) -> T q.
Parameter bot : prop.
Parameter botE : forall a : prop, T bot -> T a.
Definition not (p : prop) := p => bot.

Parameter classic : forall a : prop, T (not (not a)) -> T a.

(* exercise 4 *)


Lemma pierce : forall a b : prop, T (((a => b) => a) => a).

Proof.
intros a b.
apply imp_introduction.
intro H.
apply classic.
unfold not.
apply imp_introduction.
intro H'.
apply imp_elimination with a.
exact H'.
apply imp_elimination with (a => b).
exact H.
apply imp_introduction.
intro H''.
apply botE.
apply imp_elimination with a.
exact H'.
exact H''.
Qed.

(* exercise 5 *)

Lemma exd : forall a b : prop, T (a => b) -> T (a => not b) -> T (not a).

Proof.
intros a b.
intro H.
intro H'.
unfold not.
apply imp_introduction.
intro H''.
apply imp_elimination with b.
apply imp_elimination with a.
exact H'.
exact H''.
apply imp_elimination with a.
exact H.
exact H''.
Qed.


(* exercise 6 *)
(* complete the following lambda terms *)
Definition one :=
  fun (l : Set -> Set) (A : Set) (B : Set) (f : l A -> l B) (x : l A) => f x.
Definition two :=
  fun (e : nat -> nat -> Set) (n : nat) => forall m : nat, e n m.

End poly_dep.

(* **************************************************************** *)

Section addition.

Fixpoint plus (n m : nat) {struct n} : nat :=
  match n with
  | O => m
  | S p => S (plus p m)
  end.

(* exercsie 7 *)
Lemma plus_n_O : forall n : nat, n = plus n 0.

(*
Proof.
intro n.
elim n.

simpl.
reflexivity.

intro n0.
simpl.
intro Hn0.
rewrite <- Hn0.
reflexivity.
Qed.
*)

Proof.
intro n.
induction n.

simpl.
reflexivity.

simpl.
rewrite <- IHn.
reflexivity.
Qed.


Lemma plus_n_S : forall n m : nat, S (plus n m) = plus n (S m).

Proof.
intros n m.
induction n.

simpl.
reflexivity.

simpl.
rewrite <- IHn.
reflexivity.
Qed.


(* exercise 8 
   you may wish to use 7 *)
Lemma com : forall n m : nat, plus n m = plus m n.


End addition.

Section natlists.

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist. 

Fixpoint append (l k : natlist) {struct l} : natlist :=
  match l with
  | nil => k
  | cons h t => cons h (append t k)
  end. 

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => 0
  | cons n k => S (length k)
  end. 

(* exercise 9 *)
Lemma length_append :
 forall k l : natlist, length (append k l) = plus (length k) (length l).


(* exercise 10 *)
(* give a definition of reverse on natlist *)


(* exercise 11 *)
Lemma append_nil : forall l : natlist, append l nil = l.


Lemma asso_append :
 forall k l m : natlist, append (append k l) m = append k (append l m).


Lemma rev :
 forall k l : natlist, reverse (append k l) = append (reverse l) (reverse k). 


End natlists.

Section polylists.

(* exercise 12 *) 
(* do the polymorphic variant of the list development *)


End polylists.
