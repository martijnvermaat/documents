(* logical verification 05-06 practical work week 3 *)

(*
  Martijn Vermaat
  mvermaat
  1362917
*)

Parameter A B C : Prop.  

(* exercise 1 *)

Lemma permutation : (A -> B -> C) -> B -> A -> C. 

intro x.
intro y.
intro z.
apply x.
exact z.
exact y.
Qed.

Print permutation.
(*
fun (x : A -> B -> C) (y : B) (z : A) => x z y
     : (A -> B -> C) -> B -> A -> C
*)

Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B. 

intro x.
apply x.
intro y.
apply y.
intro z.
apply x.
intro u.
exact z.
Qed.

Print weak_peirce.
(*
fun x : (((A -> B) -> A) -> A) -> B =>
x (fun y : (A -> B) -> A => y (fun z : A => x (fun _ : (A -> B) -> A => z)))
     : ((((A -> B) -> A) -> A) -> B) -> B
*)

(* exercise 2 *)

Definition two_a := fun (x : A) (y : B) => (fun n:A => n) x.
Check two_a.
Eval cbv beta delta in two_a.
(*
     = fun (x : A) (_ : B) => x
     : A -> B -> A
*)

Definition two_b := fun (x: A->B) (y z: A) => x ((fun n:A => z) y).
Check two_b.
Eval cbv beta delta in two_b.
(*
     = fun (x : A -> B) (_ z : A) => x z
*)

(* exercise 3 *)

Lemma notfalse : ~ False.
unfold not.
intro x.
exact x.
Qed.
Print notfalse.
(*
notfalse = fun x : False => x
     : ~ False
*)

Lemma exfalso : False -> A.
intro x.
elim x.
Qed.
Print exfalso.
(*
exfalso = fun x : False => False_ind A x
     : False -> A
*)

Lemma contrapositive : (A -> B) -> ~ B -> ~ A.
unfold not.
intro x.
intro y.
intro z.
apply y.
apply x.
exact z.
Qed.
Print contrapositive.
(*
contrapositive = 
fun (x : A -> B) (y : B -> False) (z : A) => y (x z)
     : (A -> B) -> ~ B -> ~ A
*)

Lemma AnotnotA : A -> ~ ~ A .
unfold not.
intro x.
intro y.
apply y.
exact x.
Qed.
Print AnotnotA.
(*
AnotnotA = fun (x : A) (y : A -> False) => y x
     : A -> ~ ~ A
*)

Lemma notnotnot : ~ ~ ~ A -> ~ A.
unfold not.
intro x.
intro y.
apply x.
intro z.
apply z.
exact y.
Qed.
Print notnotnot.
(*
notnotnot = 
fun (x : ((A -> False) -> False) -> False) (y : A) =>
x (fun z : A -> False => z y)
     : ~ ~ ~ A -> ~ A
*)

Lemma herman : ~ ~ (~ ~ A -> A). 
unfold not.
intro x.
apply x.
intro y.
elimtype False.
apply y.
intro z.
apply x.
intro u.
exact z.
Qed.
Print herman.
(*
herman = 
fun x : (((A -> False) -> False) -> A) -> False =>
x
  (fun y : (A -> False) -> False =>
   False_ind A (y (fun z : A => x (fun _ : (A -> False) -> False => z))))
     : ~ ~ (~ ~ A -> A)
*)

(* exercise 4 *)

Require Import Classical.

Check classic.
Check (classic A).
Check (classic (~ A)).

Lemma double_negation : forall A : Prop, ~ ~ A -> A.  
(* in fact this lemma is in second-order propositional logic *)
(*
  use elim (classic P) if you want to do elimination
  of P \/ ~P
*)
intro D.
unfold not.
intro x.
elim (classic D).
intro y.
exact y.
unfold not.
intro z.
elimtype False.
apply x.
exact z.
Qed.

Lemma peirce : ((A -> B) -> A) -> A.



(*
  use the lemma double_negation
*)

Lemma everything_related : (A -> B) \/ (B -> A).

