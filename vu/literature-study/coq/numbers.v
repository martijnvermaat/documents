(** Substitution in untyped lambda-calculus with de-Bruijn indices.

   March 2009, Martijn Vermaat <martijn@vermaat.name> *)


Require Import Arith.


Inductive term : Set :=
  | Var : nat -> term
  | Abs : term -> term
  | App : term -> term -> term.


(** Lift indices that are bound by at least l abstractions away. *)

Fixpoint lift (l : nat) (t : term) {struct t} : term :=
  match t with
  | Var n   => Var (if le_lt_dec l n then (S n) else n)
  | Abs u   => Abs (lift (S l) u)
  | App u v => App (lift l u) (lift l v)
end.

(** Capture-avoiding substitution. *)

Fixpoint subst (s : term) (n : nat) (t : term) {struct t} : term :=
  match t with
  | Var m   => if eq_nat_dec n m then s else t
  | Abs u   => Abs (subst (lift 0 s) (S n) u)
  | App u v => App (subst s n u) (subst s n v)
end.
