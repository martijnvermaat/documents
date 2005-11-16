(* logical verification week 10 2005 - 2006 *)

(*
  Martijn Vermaat
  mvermaat
  1362917
*)

Definition natid : nat -> nat :=
  fun n : nat => n.

Check (natid O).
Eval compute in (natid O).

Definition boolid: bool -> bool :=
  fun b : bool => b.

Check (boolid true).
Eval compute in (boolid true).

(* exercise 1 *)
(* give the definition of the polymorphic identity polyid *)

Definition polyid (A: Set) : A -> A :=
  fun x : A => x.

(* exercise 2 *)
(* use Check to check the type of the polymorphic identity *)

Check boolid.
Check polyid.
Check (polyid bool).
Check (polyid bool true).

(* exercise 3 *)
(* compute using Eval compute the value of the 
   polymorphic identity applied to O on the domain nat 
   so you provide two arguments *)

Check (polyid _ O).

Eval compute in (polyid _ 0).
Eval compute in (polyid nat 0).

Notation id := (polyid _).

Check (id O).
Check (id true).

Inductive natlist : Set :=
  natnil : natlist
| natcons : nat -> natlist -> natlist.

Inductive natlistdep : nat->Set :=
  natnildep : (natlistdep O) 
| natconsdep : forall n:nat, 
    nat -> (natlistdep n) -> (natlistdep (S n)).

Inductive boollist : Set :=
  boolnil : boollist 
| boolcons : bool -> boollist -> boollist.

(* polymorphic inductive types have parameters 
   that are declared as (X:Set) for example *)

(* exercise 4 *)
(* give the definition of the polymorphic lists polylist *)

Inductive polylist (X:Type) : Type :=
  polynil : polylist X
| polycons : X -> polylist X -> polylist X.

(* exercise 5 *)
(* use Check to see the type of both constructors 
   for the polymorphic lists *)

Check polynil.
Check (polynil bool).
Check polycons.
Check (polycons bool).
Eval compute in (polycons _ true (polycons _ false (polynil _))).

(* exercise 6 *)
(* use Check to see the type of polylist_ind *)

Check (polylist_ind).

(* example *)
(* instead of having a parameter in Set,
   we can use Set -> Set as type of polylist
   but now we get a very strange induction predicate *)

Inductive polylistb : Set -> Type :=
  polynilb : forall X:Set, polylistb X
| polyconsb: forall X:Set, X -> polylistb X -> polylistb X.

Check polylistb_ind.

(* example *)
(* try to define dependent lists with nat as a parameter
   instead of with type nat -> Set 
   remove the comments to see the error message (vernac !) of Coq *)

(*
Inductive natlist_depb (n:nat) : Set :=
  nil_depb : natlist_depb O 
| cons_depb : forall n:nat, nat -> natlist_depb n -> natlist_depb (S n).
*)

(* this is not allowed because if x is a parameter,
   then all occurrences of the defined type must 
   be applied to x
   in polylist this is ok: we have everywhere (polylist X)
   in natlist_depb this is not ok: we have for instance (natlist_depb O) *)

Notation ni := (polynil _).
Notation co := (polycons _).

(* exercise 6.5 *)
(* use Check to check a simple list built using ni and co *)

Check (co 4 (co 2 (co 3 ni))).

Inductive polylistdep (A:Set) : nat -> Set :=
  polynildep : (polylistdep A O)
| polyconsdep : forall n:nat, 
    A -> (polylistdep A n) -> (polylistdep A (S n)).

Check polynildep.
Check polyconsdep.

Inductive polypolylist : Type :=
  polypolynil : polypolylist
| polypolycons : forall A:Set , A -> polypolylist -> polypolylist.

Check polypolycons nat 2 (polypolycons bool true (polypolynil)).
Check polypolycons _ 2 (polypolycons _ true (polypolynil)).

Fixpoint natlength (l:natlist) {struct l} : nat :=
  match l with
    natnil => O 
  | natcons h t => S (natlength t)
  end.

Fixpoint polylength (A:Set)(l:(polylist A)){struct l} : nat :=
  match l with
    polynil => O
  | polycons h t => S (polylength A t)
  end.

Fixpoint natmap 
  (f:nat->nat)(l:natlist) {struct l} : natlist :=
  match l with
    natnil => natnil
  | natcons h t => natcons (f h) (natmap f t)
  end.


(* exercise 7 *)
(* define a polymorphic version polymap of natmap
   and test it on two different inputs *)

Fixpoint polymap (A B:Type) (f:A->B) (l:(polylist A)) {struct l} : (polylist B) :=
  match l with
    polynil => polynil B
    | polycons h t => polycons B (f h) (polymap A B f t)
  end.

Eval compute in (polymap _ _ not (co True (co False ni))).

Definition bnot (b:bool) : bool :=
  match b with
    true => false
    | false => true
  end.

Eval compute in (polymap _ _ bnot (co true (co false ni))).

Fixpoint natfold (f:nat->nat->nat)(z:nat)(l:natlist){struct l} : nat :=
  match l with
    natnil => z
  | natcons h t => f h (natfold f z t)
  end.

Definition sum := natfold plus O.

Fixpoint polyfold (A B:Set)
  (f:A->B->B)(z:B)(l:(polylist A)){struct l} : B :=
  match l with
    polynil => z
  | polycons h t => f h (polyfold A B f z t)
  end.

Definition sum' := polyfold nat nat plus O.


(* exercise 8 *)
(* give the definition natbintree of binary trees
   with natural numbers as labels
   on the nodes and on the leafs *)

Inductive natbintree : Set :=
  leaf : nat -> natbintree
| node : nat -> natbintree -> natbintree -> natbintree.

(* exercise 9 *)
(* give the definition polybintree of 
   polymorphic binary trees with labels
   on the nodes and on the leafs *)

Inductive polybintree (A:Set) : Set :=
  polyleaf : A -> (polybintree A)
| polynode : A -> (polybintree A) -> (polybintree A) -> (polybintree A).

(*
Inductive polypolybintree : Type :=
  polypolyleaf : forall A:Set, A -> polypolybintree
| polypolynode : forall A:Set, A -> polypolybintree -> polypolybintree -> polypolybintree.
*)

(* exercise 10 *)
(* use Check to check the type of the constructor for leafs *)

Check polyleaf.

(* exercise 11 *)
(* instantiate the constructor for leafs to the case of nat 
   and use Check to see its type *)

Check (polyleaf nat).

(* exercise 12 *)
(* instantiate the constructor for leafs to the case of bool
   and use Check to see its type *)

Check (polyleaf bool).

(* exercise 13 *)
(* use Check to check the type of the constructor for nodes *)

Check polynode.

(* exercise 14 *)
(* instantiate the constructor for nodes to the case of nat 
   and use Check to see its type *)

Check (polynode nat).

(* exercise 15 *)
(* instantiate the constructor for nodes to the case of bool
   and use Check to see its type *)

Check (polynode bool).

(* exercise 16 *)
(* use Check to see the induction predicate for polymorphic trees *)

Check polybintree_ind.

Eval compute in (polynode _ true (polynode _ false (polyleaf _ true) (polyleaf _ true)) (polyleaf _ false)).

(* an alternative for polybintree without parameter
   with a more complex induction predicate *)
Inductive polybintreeb : Set -> Type :=
  polyleafb : forall X:Set, X -> polybintreeb X
| polynodeb : forall X:Set, X -> polybintreeb X -> polybintreeb X -> polybintreeb X.

Check polybintreeb_ind.

Eval compute in (polynodeb _ true (polynodeb _ false (polyleafb _ true) (polyleafb _ true)) (polyleafb _ false)).
