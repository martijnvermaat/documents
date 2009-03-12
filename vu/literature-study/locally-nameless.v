(*
  Substitution in untyped lambda-calculus with a locally-nameless 
  representation.
  March 2009, Martijn Vermaat
  Developed with Coq version 8.2 in CoqIDE
*)

Require Import Arith.

(* Assume some type for names on which equality is decidable. *)
Parameter name : Set.
Parameter eq_name : forall (x y : name), {x = y} + {x <> y}.

Inductive term : Set :=
  | FreeVar  : name -> term
  | BoundVar : nat -> term
  | Abs      : term -> term
  | App      : term -> term -> term.

Fixpoint subst_free (t:term) (x:name) (t':term) {struct t'} : term :=
  match t' with
  | FreeVar y  => if eq_name x y then t else t'
  | BoundVar n => t'
  | Abs b      => Abs (subst_free t x b)
  | App f a    => App (subst_free t x f) (subst_free t x a)
end.

Fixpoint subst_bound (t:term) (n:nat) (t':term) {struct t'} : term :=
  match t' with
  | FreeVar x  => t'
  | BoundVar m => if eq_nat_dec m n then t else t'
  | Abs b      => Abs (subst_bound t (S n) b)
  | App f a    => App (subst_bound t n f) (subst_bound t n a)
end.
