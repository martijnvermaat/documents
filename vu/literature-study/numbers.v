(*
  Substitution in untyped lambda-calculus with de-Bruijn indices.
  March 2009, Martijn Vermaat
  Developed with Coq version 8.2 in CoqIDE
*)

Inductive term : Set :=
  | Var : nat -> term
  | Abs : term -> term
  | App : term -> term -> term.
