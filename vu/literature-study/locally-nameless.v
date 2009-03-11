(*
  Substitution in untyped lambda-calculus with a locally-nameless 
  representation.
  March 2009, Martijn Vermaat
  Developed with Coq version 8.2 in CoqIDE
*)

(* Assume some type for names on which equality is decidable. *)
Parameter name : Set.
Parameter eq_name : forall (x y : name), {x = y} + {x <> y}.

Inductive term : Set :=
  | FreeVar  : name -> term
  | BoundVar : nat -> term
  | Abs      : term -> term
  | App      : term -> term -> term.
