(*
  Substitution in untyped lambda-calculus with named variables.
  March 2009, Martijn Vermaat
  Developed with Coq version 8.2 in CoqIDE
*)

Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Recdef.

(* Assume some type for names on which equality is decidable. *)
Parameter name : Set.
Parameter eq_name : forall (x y : name), {x = y} + {x <> y}.

Parameters v1 v2 v3 v4 : name.

Inductive term : Set :=
  | Var : name -> term
  | Abs : name -> term -> term
  | App : term -> term -> term.

(* This is a non-capture-avoiding substitution. It could be useful if
   we maintain Barendregt's Variable Convention. *)
Function subst_naive (t:term) (n:name) (t':term) {struct t'} : term :=
  match t' with
  | Var x =>
      if eq_name x n then t else t'
  | Abs x b => 
      if eq_name x n then t' else Abs x (subst_naive t n b)
  | App f a =>
      App (subst_naive t n f) (subst_naive t n a)
end.

(* Well-founded measure on terms. *)
Fixpoint size (t:term) : nat :=
  match t with
  | Var _   => 0
  | Abs x b => S (size b)
  | App f a => 1 + (size f) + (size a)
end.

(* Just naively rename n to n'. *)
Fixpoint rename (n n':name) (t:term) {struct t} : term :=
  match t with
  | Var x =>
      if eq_name x n then Var n' else t
  | Abs x b =>
      Abs (if eq_name x n then n' else x) (rename n n' b)
  | App f a =>
      App (rename n n' f) (rename n n' a)
end.

(* Size is invariant under renaming. *)
Lemma size_rename : forall (n n':name) (t:term), size (rename n n' t) = size t.
Proof.
unfold size.
unfold rename.
induction t;
  [ (* Var _ *)
    case (eq_name n0 n); intro; trivial
  | (* Abs _ _ *)
    congruence
  | (* App _ _ *)
    congruence].
Qed.

(* List all free variable occurences. *)
Fixpoint free_vars (t:term) : list name :=
  match t with
  | Var x   => x :: nil
  | Abs x b => remove eq_name x (free_vars b)
  | App f a => (free_vars f) ++ (free_vars a)
end.

(* Assume we have some way to generate names... *)
Definition fresh_name (l:list name) : name := v1.

(* Capture-avoiding substitution by recursion on size. *)
Function subst (t:term) (n:name) (t':term) {measure size t'} : term :=
  match t' with
  | Var x =>
      if eq_name x n then t else t'
  | Abs x b =>
      (* We always rename, this could of course be improved. *)
      let z := fresh_name (n :: (free_vars t) ++ (free_vars b))
      in
      Abs z (subst t n (rename x z b))
  | App f a =>
      App (subst t n f) (subst t n a)
end.
(* This leaves us with 3 obligations. *)
Proof.
intros.
rewrite size_rename.
auto.

intros.
unfold size.
inversion f; omega.

intros.
unfold size.
inversion a; omega.
Defined.

(* Apply a list of substitutions to a name. *)
Fixpoint apply_subst (l:list (term*name)) (n:name) {struct l} : term :=
  match l with
  | nil        => Var n
  | (t, x)::l' => if eq_name x n then t else apply_subst l' n
end.

(* Number of free variables in substituted terms. *)
Fixpoint free_vars_sub (l:list (term*name)) : list name :=
  match l with
  | nil        => nil
  | (t, _)::l' => (free_vars t) ++ (free_vars_sub l')
end.

(* Capture-avoiding simultaneous substitution by structural recursion. *)
Fixpoint sim_subst (l:list (term*name)) (t:term) {struct t} : term :=
  match t with
  | Var x =>
      apply_subst l x
  | Abs x b =>
      let z := fresh_name ((free_vars_sub l) ++ (free_vars b))
      in
      Abs z (sim_subst ((Var z, x)::l) b)
  | App f a =>
      App (sim_subst l f) (sim_subst l a)
end.

(* Define simple substitution in terms of simultaneous substitution. *)
Definition subst' (t:term) (n:name) (t':term) : term := sim_subst ((t, n) :: nil) t'.

(* Substitution Lemma. *)
(*Lemma substitution : forall (m t u:term) (x y:name), x <> y -> ~In x (free_vars u) -> subst u y (subst t x m) = subst (subst u y t) x (subst u y m).*)