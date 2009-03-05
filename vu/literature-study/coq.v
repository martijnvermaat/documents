(* Coq version 8.2 *)

Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Recdef.

Parameter name : Set.
Hypothesis eq_name : forall (x y : name), {x = y} + {x <> y}.

Parameters v1 v2 v3 v4 : name.

Inductive term : Set :=
  | Var : name -> term
  | Abs : name -> term -> term
  | App : term -> term -> term.

Fixpoint size (t:term) : nat :=
  match t with
  | Var _   => 0
  | Abs x b => S (size b)
  | App f a => 1 + (size f) + (size a)
end.

Hypothesis size_app1 : forall (f a:term), size f < size (App f a).
Hypothesis size_app2 : forall (f a:term), size a < size (App f a).
(* TODO proof *)

Function subst_naive (t:term) (n:name) (t':term) {struct t'} : term :=
  match t' with
  | Var x =>
      if eq_name x n then t else t'
  | Abs x b => 
      if eq_name x n then t' else Abs x (subst_naive t n b)
  | App f a =>
      App (subst_naive t n f) (subst_naive t n a)
end.

Fixpoint rename (n n':name) (t:term) {struct t} : term :=
  match t with
  | Var x =>
      if eq_name x n then Var n' else t
  | Abs x b =>
      Abs (if eq_name x n then n' else x) (rename n n' b)
  | App f a =>
      App (rename n n' f) (rename n n' a)
end.

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

Fixpoint free_vars (t:term) : list name :=
  match t with
  | Var x   => x :: nil
  | Abs x b => remove eq_name x (free_vars b)
  | App f a => (free_vars f) ++ (free_vars a)
end.

Definition fresh_name (l:list name) : name := v1.

Function subst (t:term) (n:name) (t':term) {measure size t'} : term :=
  match t' with
  | Var x =>
      if eq_name x n then t else t'
  | Abs x b =>
      let z := fresh_name (n :: (free_vars t) ++ (free_vars b))
      in
      Abs z (subst t n (rename x z b))
  | App f a =>
      App (subst t n f) (subst t n a)
end.
Proof.
intros.
rewrite size_rename.
auto.

intros.
apply size_app2.

intros.
apply size_app1.
Defined.
