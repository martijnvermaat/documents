(** Substitution in untyped lambda-calculus with a locally-nameless
   representation.

   March 2009, Martijn Vermaat <martijn@vermaat.name> *)


Require Import Arith.


Section LocallyNameless.

(** Assume some type for names on which equality is decidable. *)

Variable name : Set.
Hypothesis eq_name : forall (x y : name), {x = y} + {x <> y}.

Inductive term : Set :=
  | FreeVar  : name -> term
  | BoundVar : nat -> term
  | Abs      : term -> term
  | App      : term -> term -> term.

Fixpoint subst_free (s : term) (x : name) (t : term) {struct t} : term :=
  match t with
  | FreeVar y  => if eq_name x y then s else t
  | BoundVar n => t
  | Abs b      => Abs (subst_free s x b)
  | App f a    => App (subst_free s x f) (subst_free s x a)
end.

Fixpoint subst_bound (s : term) (n : nat) (t : term) {struct t} : term :=
  match t with
  | FreeVar x  => t
  | BoundVar m => if eq_nat_dec m n then s else t
  | Abs b      => Abs (subst_bound s (S n) b)
  | App f a    => App (subst_bound s n f) (subst_bound s n a)
end.

Definition freshen (t : term) (x : name) : term := subst_bound (FreeVar x) 0 t.

End LocallyNameless.
