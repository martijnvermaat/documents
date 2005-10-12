(* logical verification 05-06 week 6 *)

(*
  Martijn Vermaat
  mvermaat
  1362917
*)

(* EXAMPLE: MIRROR *)

Inductive bintree : Set :=
  | leaf : nat -> bintree
  | node : bintree -> bintree -> bintree.

(* specification *)

Inductive Mirrored : bintree -> bintree -> Prop :=
  | Mirrored_leaf : forall n : nat, Mirrored (leaf n) (leaf n)
  | Mirrored_node :
      forall b b' c c' : bintree,
      Mirrored b b' -> Mirrored c c' -> Mirrored (node b c) (node c' b').

(* implementation *)

Fixpoint mirror (t : bintree) : bintree :=
  match t with
  | leaf n => leaf n
  | node t1 t2 => node (mirror t2) (mirror t1)
  end.

(* correctness *)

Theorem Mirrored_mirror : forall t : bintree, Mirrored t (mirror t).
induction t.
simpl.
apply Mirrored_leaf.
simpl.
apply Mirrored_node.
exact IHt1.
exact IHt2.
Qed.

(* exercise 1: successor *)

Theorem successor:
  forall n:nat, {m:nat | m = S n} .

Proof.
intro.
exists (S n).
reflexivity.
Qed.

Extraction successor.
Extraction "successor" successor.


(*
  type "ocaml" to activate the ocaml toplevel compiler
  this gives a prompt #
  #use "successor.ml" ;;
  makes that the file successor.ml is loaded
  NB: #is not the prompt but #use is the command !
  NB: the " are necessary
  you can use the program by saying for instance
  successor O ;;
  NB: the round thing is capital-o
  NB: every command should end with ;;
  exit with  #quit ;;
  NB: again # is not the prompt, and ;; are necessary
*)

(* exercise 2: predecessor *)

Theorem predecessor :
  forall n:nat, ~(n=O) -> {m:nat | S m = n}. 

Proof.
intro.
intro.
induction n.

elimtype False.
apply H.
reflexivity.

exists n.
reflexivity.

Qed.

Extraction predecessor.
Extraction "predecessor" predecessor.

(* exercise 3: 
   Prove the following theorem WITHOUT using the function mirror 
   and check out the extracted function! 
   Hint: use inversion_clear 
*)

Theorem Mirror : forall t : bintree, {t' : bintree | Mirrored t t'}.

induction t.

exists (leaf n).
constructor.

inversion_clear IHt1.
inversion_clear IHt2.
exists (node x0 x).
constructor.

exact H.
exact H0.

Qed.

Extraction Mirror.
Extraction "mirror" Mirror. 

(* EXAMPLE: SORT *)

Require Import Arith.

Inductive natlist : Set :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(* specification *)

Inductive Sorted : natlist -> Prop :=
  | Sorted_nil : Sorted nil
  | Sorted_one : forall n : nat, Sorted (cons n nil)
  | Sorted_cons :
      forall (n m : nat) (l : natlist),
      n <= m -> Sorted (cons m l) -> Sorted (cons n (cons m l)).

Inductive Inserted (n : nat) : natlist -> natlist -> Prop :=
  | Inserted_front :
      forall l : natlist, Inserted n l (cons n l)
  | Inserted_cons :
      forall (m : nat) (l l' : natlist),
      Inserted n l l' -> Inserted n (cons m l) (cons m l').

Inductive Permutation : natlist -> natlist -> Prop :=
  | Permutation_nil : Permutation nil nil
  | Permutation_cons :
      forall (n : nat) (l l' l'' : natlist),
      Permutation l l' -> Inserted n l' l'' -> Permutation (cons n l) l''.

(* exercise 4: Playing with the definition of Permutation *)
(* hint: use inversion_clear several times *)

Lemma Permutation_neg: 
  ~(Permutation (cons 1 (cons 2 nil)) (cons 2 (cons 3 nil))).

Proof.

unfold not.
intro.
inversion_clear H.
inversion_clear H0.
inversion_clear H.
inversion_clear H1.
inversion_clear H.
inversion_clear H0.

Qed.

(* Hint for proving the following lemmas: Suppose we have a goal with
the form (Permutation (cons n l) l'').  If we apply Permutation_cons
we get an error because it is unknown what l' should be.  In this case
we can use "apply Permutation_cons with ..." and give the missing
argument(s) on the dots. See as an example the first step of the proof. *)

(* exercise 5 *)

Lemma Permutation_123:
  (Permutation (cons 1 (cons 2 (cons 3 nil))) (cons 3 (cons 2 (cons 1 nil)))).

Proof.
apply Permutation_cons with (cons 3 (cons 2 nil)).
apply Permutation_cons with (cons 3 nil).
apply Permutation_cons with (nil).
constructor.
constructor.
constructor.
constructor.
constructor.
constructor.
constructor.
Qed.


(* exercise 6: The following lemma is essential for the extractable proof *)
(* remember the apply Permutation_cons may need "with ...".*)

Lemma Permutation_refl : forall (l : natlist), Permutation l l.

Proof.
induction l.
constructor.
apply Permutation_cons with l.
exact IHl.
constructor.
Qed.


(* auxiliary notion + some lemmas about it *)

Inductive Lowerbound (n : nat) : natlist -> Prop :=
  | Lowerbound_nil : Lowerbound n nil
  | Lowerbound_cons :
      forall (m : nat) (l : natlist),
      n <= m -> Lowerbound n l -> Lowerbound n (cons m l).

(* exercise 7 *)
(* use rewrite in a hypothesis 
   rewrite <- H? in H? 
   where ? should be instantiated according to your environment *)

Lemma Lowerbound_Sorted :
  forall (l : natlist) (n : nat),
    Lowerbound n l -> Sorted l -> Sorted (cons n l).

induction l.
intro n.
constructor.

constructor.
inversion_clear H.
exact H1.

exact H0.
Qed.


(* exercise 8: Prove the following lemma using le_trans 
   proceed by induction on l; use also inversion_clear *)

Check le_trans.



Lemma Sorted_Lowerbound :
  forall (l : natlist) (n : nat), Sorted (cons n l) -> Lowerbound n l.

(* use le_trans with with *)

Proof.

induction l.

intro.
intro.
constructor.

intro.
constructor.
inversion_clear H.
exact H0.

(* here we are *)


Lemma Inserted_Lowerbound :
  forall (l l' : natlist) (n m : nat),
    n <= m -> Inserted m l l' -> Lowerbound n l -> Lowerbound n l'.
induction l.
intros.
inversion_clear H0.
apply Lowerbound_cons.
exact H.
exact H1.
intros k p m H H0 H1. 
inversion_clear H0.
apply Lowerbound_cons.
exact H.
exact H1.
inversion_clear H1.
apply Lowerbound_cons.
exact H0.
apply IHl with m.
exact H.
exact H2.
exact H3.
Qed.

Lemma Permutation_Lowerbound :
  forall (l l' : natlist) (n : nat),
    Permutation l l' -> Lowerbound n l -> Lowerbound n l'.
induction l.
intros k n H H0.
inversion_clear H.
exact H0.
intros k m H H0.
inversion_clear H.
inversion_clear H0.
apply Inserted_Lowerbound with l' n.
exact H.
exact H2.
apply IHl.
exact H1.
exact H3.
Qed.

(* implementation *)

Fixpoint insert (n : nat) (l : natlist) {struct l} : natlist :=
  match l with
  | nil => cons n nil
  | cons m k =>
      match le_lt_dec n m with
      | left _ => cons n (cons m k)
      | right _ => cons m (insert n k)
      end
  end.

Fixpoint sort (l : natlist) : natlist :=
  match l with
  | nil => nil
  | cons m k => insert m (sort k)
  end.

(* correctness *)

Lemma Inserted_insert :
  forall (n : nat) (l : natlist), Inserted n l (insert n l).
induction l.
simpl.
apply Inserted_front.
simpl.
elim (le_lt_dec n n0).
intro.
apply Inserted_front.
intro.
apply Inserted_cons.
exact IHl.
Qed.

Lemma Lowerbound_insert :
  forall (l : natlist) (n m : nat),
  m <= n -> Lowerbound m l -> Lowerbound m (insert n l).
induction l.
intros n m H H0.
simpl.
apply Lowerbound_cons.
exact H.
exact H0.
intros n' m H H0.
simpl.
elim (le_lt_dec n' n).
intro H1.
apply Lowerbound_cons.
exact H.
exact H0.
intro H1.
inversion_clear H0.
apply Lowerbound_cons.
exact H2.
apply IHl.
exact H.
exact H3.
Qed.

Lemma Sorted_insert :
  forall (l : natlist) (n : nat), Sorted l -> Sorted (insert n l).
induction l.
intros n H.
simpl.
apply Sorted_one.
intros m H.
simpl.
elim (le_lt_dec m n).
intro H0.
apply Sorted_cons.
exact H0.
exact H.
intro H0.
apply Lowerbound_Sorted.
apply Lowerbound_insert.
apply lt_le_weak.
exact H0.
apply Sorted_Lowerbound.
exact H.
apply IHl.
inversion_clear H.
apply Sorted_nil.
exact H2.
Qed.

Theorem Permutation_sort :
  forall l : natlist, Permutation l (sort l).
induction l.
simpl.
apply Permutation_nil.
simpl.
apply Permutation_cons with (sort l).
exact IHl.
apply Inserted_insert.
Qed.

Theorem Sorted_sort :
  forall l : natlist, Sorted (sort l).
induction l.
simpl.
apply Sorted_nil.
simpl.
apply Sorted_insert.
exact IHl.
Qed.

(* extractable proofs *)

Lemma Insert :
  forall (l : natlist) (n : nat), Sorted l ->
    {i : natlist | Inserted n l i /\ Sorted i}.
induction l.
intros n H.
exists (cons n nil).
split.
apply Inserted_front.
apply Sorted_one.
intros m H.
elim (le_lt_dec m n).
intro H0.
exists (cons m (cons n l)).
split.
apply Inserted_front.
apply Sorted_cons.
exact H0.
exact H.
intro H0.
elim IHl with m.
intros i' H1.
elim H1.
intros H2 H3.
exists (cons n i').
split.
apply Inserted_cons.
exact H2.
apply Lowerbound_Sorted.
apply Permutation_Lowerbound with (cons m l).
apply Permutation_cons with l.
apply Permutation_refl.
exact H2.
apply Lowerbound_cons.
apply lt_le_weak.
exact H0.
apply Sorted_Lowerbound.
exact H.
exact H3.
inversion_clear H.
apply Sorted_nil.
exact H2.
Qed.

Theorem Sort :
  forall l : natlist, {l' : natlist | Permutation l l' /\ Sorted l'}.
induction l.
exists nil.
split.
apply Permutation_nil.
apply Sorted_nil.
elim IHl.
intros l' H.
elim H.
intros H0 H1.
elim Insert with l' n.
intros i' H2.
elim H2.
intros H3 H4.
exists i'.
split.
apply Permutation_cons with l'.
exact H0.
exact H3.
exact H4.
exact H1.
Qed.

Extraction Insert.
Extraction Sort.
Extraction "insertsort" Sort.

