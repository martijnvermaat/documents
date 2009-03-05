(*
  Substitution in untyped lambda-calculus with de-Bruijn indices.
  March 2009, Martijn Vermaat
  Developed with Coq version 8.2 in CoqIDE
*)

Require Import Arith.
Require Import Omega.

Inductive term : Set :=
  | Var : nat -> term
  | Abs : term -> term
  | App : term -> term -> term.

(* Lift indices that are bound by at least l abstractions away. *)
Fixpoint lift (l:nat) (t:term) {struct t} : term :=
  match t with
  | Var n   => Var (if le_lt_dec l n then (S n) else n)
  | Abs u   => Abs (lift (S l) u)
  | App u v => App (lift l u) (lift l v)
end.

(* Capture-avoiding substitution. *)
Fixpoint subst (t:term) (n:nat) (t':term) {struct t'} : term :=
  match t' with
  | Var m   => if eq_nat_dec n m then t else t'
  | Abs u   => Abs (subst (lift 0 t) (S n) u)
  | App u v => App (subst t n u) (subst t n v)
end.
