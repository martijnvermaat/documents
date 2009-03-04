(* Coq version 8.2 *)

Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Recdef.
Require Coq.Program.Wf.

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
  | App f a => 1+ (size f) + (size a)
end.

Function subst_naive (t:term) (n:name) (t':term) {struct t'} : term :=
  match t' with
  | Var x =>
      if eq_name x n then t else t'
  | Abs x b => 
      if eq_name x n then t' else Abs x (subst_naive t n b)
  | App f a =>
      App (subst_naive t n f) (subst_naive t n a)
end.

Fixpoint free_vars (t:term) : list name :=
  match t with
  | Var x   => x :: nil
  | Abs x b => remove eq_name x (free_vars b)
  | App f a => (free_vars f) ++ (free_vars a)
end.

Definition fresh (l:list name) : name := v1.

Program Fixpoint simple_subst (s n:name) (t:term) {measure size t} : term :=
  match t with
  | Var x =>
      if eq_name x n then Var s else t
  | Abs x b =>
      let z := fresh nil in
      Abs z (simple_subst s n (simple_subst z x b))
  | App f a =>
      App (simple_subst s n f) (simple_subst s n a)
end.

Function subst (t:term) (n:name) (t':term) {measure size t'} : term :=
  match t' with
  | Var x =>
      if eq_name x n then t else t'
  | Abs x b =>
      if eq_name x n then t' else Abs x (subst_naive t n b)
      (*Abs x (subst t n (subst (Var x) x b))*)
  | App f a =>
      App (subst t n f) (subst t n a)
end.
Proof.
intros. simpl. omega.
intros. simpl. omega.
intros. simpl. omega.
Defined.

Eval compute in (subst (Var v1) v1 (Var v1)).
