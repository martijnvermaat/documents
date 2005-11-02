(* logical verification 2005 - 2006 week 8 *)

(*
  Martijn Vermaat
  mvermaat
  1362917
*)

Section les.

(* examples *)

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist .

Fixpoint append (k l : natlist) {struct k} : natlist :=
  match k with
  | nil => l
  | cons h t => cons h (append t l)
  end.

Fixpoint reverse (k : natlist) {struct k} : natlist :=
  match k with
  | nil => nil
  | cons h t => append (reverse t) (cons h nil) 
  end.

Fixpoint zeroes (n:nat) : natlist :=
  match n with
  | O => nil
  | S p => cons O (zeroes p)
  end.

Eval compute in (zeroes 0).
Eval compute in (zeroes 1).
Eval compute in (zeroes 2).
Eval compute in (zeroes 10).

Inductive natlist_dep : nat -> Set :=
  | nil_dep : natlist_dep 0
  | cons_dep : forall n : nat, nat -> natlist_dep n -> natlist_dep (S n).

Check (nat -> Set).
Check natlist_dep.
Check cons_dep.
Check nil_dep.

Check nil_dep.
Check cons_dep O 3 nil_dep.
Check cons_dep 1 3 (cons_dep O 4 nil_dep) .

Fixpoint zeroesdep (n:nat) : natlist_dep n := 
  match n return natlist_dep n with
  | O => nil_dep
  | S p => cons_dep p O (zeroesdep p)
  end.

Eval compute in (zeroesdep O).
Eval compute in (zeroesdep 1).
Eval compute in (zeroesdep 2).

Definition length_dep (n : nat) (l : natlist_dep n) := n.

Definition length_dep_b (n : nat) (l : natlist_dep n) : nat :=
  match l with
  | nil_dep => 0
  | cons_dep n h t => S n
  end.

Fixpoint append_dep (n : nat) (k : natlist_dep n) (m : nat)
 (l : natlist_dep m) {struct k} : natlist_dep (n + m) :=
  match k in (natlist_dep n) return (natlist_dep (n + m)) with
  | nil_dep => l
  | cons_dep p h t => cons_dep (p + m) h (append_dep p t m l)
  end.

Eval compute in (append_dep O nil_dep O  nil_dep).
Eval compute in (append_dep 1 (cons_dep O 3 nil_dep) O nil_dep).
Eval compute in (append_dep O nil_dep 1 (cons_dep O 3 nil_dep)).
Eval compute in (append_dep 1 (cons_dep O 3 nil_dep) 1 (cons_dep O 4 nil_dep)).

Fixpoint map_dep (f : nat -> nat) (n : nat) (l : natlist_dep n) {struct l} :
 natlist_dep n :=
  match l in (natlist_dep n) return (natlist_dep n) with
  | nil_dep => nil_dep
  | cons_dep p h t => cons_dep p (f h) (map_dep f p t)
  end.

Parameter Terms:Set.
Parameter P : Terms -> Prop.
Parameter Q : Terms -> Prop.
Parameter A : Prop.

Lemma example_1 : forall x:Terms, 
  (P x -> (forall y:Terms, P y -> A) -> A) .

Proof.
intro x.
intro H.
intro I.
apply I with x.
exact H.
Qed.

Lemma example_2 : (forall x:Terms, P x -> Q x) -> (forall x:Terms, P x) ->
   (forall y:Terms, Q y).

Proof.
intros H I y.
apply H.
apply I.
Qed.
Print example_2.

End les.

Section logic.

(* we encode propositional logic
   source: webpage Herman Geuvers
   handbook article Henk Barendregt *)

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

(* exercise 1 : prove the following lemma *)
Lemma I : forall p : prop, T (p => p).

Proof.
intro.
apply imp_introduction.
intro.
exact H.
Qed.

(* exercise 2 : prove the following lemma *)
Lemma transitivity :
 forall p q r : prop, T (p => q) -> T (q => r) -> T (p => r).

Proof.
intro.
intro.
intro.
intro.
intro.
apply imp_introduction.
intro.
apply imp_elimination with q.
exact H0.
apply imp_elimination with p.
exact H.
exact H1.
Qed.


Parameter conjunction : prop -> prop -> prop.
Infix "X" := conjunction (no associativity, at level 90).

(* exercise 3 : define variables that model the introduction
   rule for conjuction on prop, and both elimination rules *)
Parameter conjunction_introduction : forall p q : prop, T p -> T q -> T (p X q).
Parameter conjunction_elimination_l : forall p q : prop, T (p X q) -> T p.
Parameter conjunction_elimination_r : forall p q : prop, T (p X q) -> T q.

(* exercise 4: prove the following lemma *)
Lemma weak : forall a b c : prop, T (a => c) -> T ((a X b) => c).

Proof.
intros a b c.
intro H.
apply imp_introduction.
intro H'.
apply imp_elimination with a.
exact H.
apply conjunction_elimination_l with b.
exact H'.
Qed.

(* bot represents falsum in prop *)
Parameter bot : prop.
(* not represents negation in prop *)
Definition not (p : prop) := p => bot.

(* exercise 5 : prove the following lemma *)
Lemma contrapositive : forall p q : prop, T (p => q) -> T (not q => not p).

intros p q.
intro H.
unfold not.
apply imp_introduction.
intro H'.
apply imp_introduction.
intro H''.
apply imp_elimination with q.
exact H'.
apply imp_elimination with p.
exact H.
exact H''.
Qed.

End logic.
