(* logical verification 05-06 practical work week 1 *)

(*
  Martijn Vermaat
  mvermaat
  1362917
*)

Parameter A B C : Prop.

Lemma one : (A -> B) -> (A -> C) -> A -> B -> C. 

intro x. 
intro y.
intro z.
intro u.
apply y.
exact z.
Qed.

Lemma two : (A -> B) -> (B -> C) -> A -> C.

intro x.
intro y.
intro z.
apply y.
apply x.
exact z.
Qed.

Lemma three : (A -> B -> C) -> B -> A -> C.

intro x.
intro y.
intro z.
apply x.
apply z.
apply y.
Qed.

Lemma foura : A -> A -> A.

intro x.
intro y.
apply x.
Qed.

Lemma fourb : A -> A -> A.

apply foura.
Qed.

Lemma five : A -> B -> A /\ B. 

intro x.
intro y.
split.
apply x.
apply y.
Qed.

Lemma six : A /\ B -> A. 

intro x.
elim x.
intro y.
intro z.
exact y.
Qed.

Lemma seven : A -> A \/ B.

intro x.
left.
exact x.
Qed.

Lemma eight : A \/ B -> (A -> C) -> (B -> C) -> C.

intro x.
intro y.
intro z.
elim x.
exact y.
exact z.
Qed.
