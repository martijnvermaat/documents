(** Substitution in untyped lambda-calculus with named variables.

   March 2009, Martijn Vermaat <martijn@vermaat.name> *)


Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Recdef.


(** Assume some type for names on which equality is decidable. *)

Parameter name : Set.
Parameter eq_name : forall (x y : name), {x = y} + {x <> y}.

Inductive term : Set :=
  | Var : name -> term
  | Abs : name -> term -> term
  | App : term -> term -> term.

(** A non-capture-avoiding substitution. It could be useful if we maintain
   Barendregt's Variable Convention. *)

Fixpoint subst_naive (s : term) (n : name) (t : term) {struct t} : term :=
  match t with
  | Var x   => if eq_name x n then s else t
  | Abs x b => if eq_name x n then t else Abs x (subst_naive s n b)
  | App f a => App (subst_naive s n f) (subst_naive s n a)
  end.

(** Well-founded measure on terms. *)

Fixpoint size (t : term) : nat :=
  match t with
  | Var _   => 0
  | Abs _ b => S (size b)
  | App f a => S (size f + size a)
  end.

(** Just naively rename n to n'. *)

Fixpoint rename (n m : name) (t : term) {struct t} : term :=
  match t with
  | Var x =>   if eq_name x n then Var m else t
  | Abs x b => Abs (if eq_name x n then m else x) (rename n m b)
  | App f a => App (rename n m f) (rename n m a)
  end.

(** Size is invariant under renaming. *)

Lemma size_rename : forall n m t, size (rename n m t) = size t.
Proof.
induction t as [x | |]; simpl;
  [destruct (eq_name x n); reflexivity | congruence | congruence].
Qed.

(** List all free variable occurences. *)

Fixpoint free_vars (t : term) : list name :=
  match t with
  | Var x   => x :: nil
  | Abs x b => remove eq_name x (free_vars b)
  | App f a => (free_vars f) ++ (free_vars a)
  end.

(** Assume we have some way to generate names... *)

Parameter fresh_name : (list name) -> name.

(** Capture-avoiding substitution by recursion on size. *)

Function subst (s : term) (n : name) (t : term) {measure size t} : term :=
  match t with
  | Var x   => if eq_name x n then s else t
  | Abs x b => let z := fresh_name (n :: (free_vars s) ++ (free_vars b))
               in (** We always rename, this could of course be improved. *)
               Abs z (subst s n (rename x z b))
  | App f a => App (subst s n f) (subst s n a)
  end.
(** Obligation 1. *)
intros.
rewrite size_rename.
auto.
(** Obligation 2. *)
intros.
simpl.
destruct f; omega.
(** Obligation 3. *)
intros.
simpl.
destruct f; omega.
Defined.

(** Apply a list of substitutions to a name. *)

Fixpoint apply_subst (l : list (term*name)) (n : name) {struct l} : term :=
  match l with
  | nil        => Var n
  | (t, x)::l' => if eq_name x n then t else apply_subst l' n
  end.

(** Free variables in substituted terms. *)

Fixpoint free_vars_sub (l : list (term*name)) : list name :=
  match l with
  | nil        => nil
  | (t, _)::l' => (free_vars t) ++ (free_vars_sub l')
  end.

(* Capture-avoiding simultaneous substitution by structural recursion. *)

Fixpoint sim_subst (l : list (term*name)) (t : term) {struct t} : term :=
  match t with
  | Var x =>   apply_subst l x
  | Abs x b => let z := fresh_name ((free_vars_sub l) ++ (free_vars b))
               in
               Abs z (sim_subst ((Var z, x) :: l) b)
  | App f a => App (sim_subst l f) (sim_subst l a)
  end.

(** Simple substitution in terms of simultaneous substitution. *)

Definition subst' (s : term) (n : name) (t : term) : term :=
  sim_subst ((s, n) :: nil) t.

(** Substitution Lemma.

[[
Lemma substitution :
  forall s t u x y,
    x <> y ->
    ~In x (free_vars u) ->
    subst u y (subst t x s) = subst (subst u y t) x (subst u y s).
]]
*)
