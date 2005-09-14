(* logical verification 05-06 practical work week 2 *)

(*
  Martijn Vermaat
  mvermaat
  1362917
*)

Variable A B C : Prop.

(* exercise 1 *)

Check fun (x : B->(A->C)) (y : B) (z : A) => x y z.
Check fun (x : B->C) (y : A->B) (z : A) => x (y z).
Check fun (x : A->A->B) (y : A) => x y y.

(* exercise 2 *)

Lemma two_a_1 : (A -> B) -> A -> A -> B.

intro x.
intro y.
exact x.
Qed.
Print two_a_1.
(*
  fun (x : A->B) (_ : A) => x
*)

Lemma two_a_2 : (A -> B) -> A -> A -> B.

intro x.
intro y.
intro z.
apply x.
exact y.
Qed.
Print two_a_2.
(*
  fun (x : A->B) (y _ : A) => x y
*)

Lemma two_b_1 : (A -> A -> A) -> A -> A.

intro x.
intro y.
exact y.
Qed.
Print two_b_1.
(*
  fun (_ : A -> A -> A) (y : A) => y
*)

Lemma two_b_2 : (A -> A -> A) -> A -> A.

intro x.
intro y.
apply x.
exact y.
exact y.
Qed.
Print two_b_2.
(*
  fun (x : A -> A -> A) (y : A) => x y y
*)

Lemma two_c_1 : (A -> B -> C) -> A -> (A -> C) -> B -> C.

intro x.
intro y.
intro z.
apply x.
exact y.
Qed.
Print two_c_1.
(*
  fun (x : A -> B -> C) (y : A) (_ : A -> C) => x y
*)

Lemma two_c_2 : (A -> B -> C) -> A -> (A -> C) -> B -> C.

intro x.
intro y.
intro z.
apply x.
exact y.
Qed.
Print two_c_2.
(*
  fun (x : A -> B -> C) (y : A) (_ : A -> C) => x y
*)

(* exercise 3 *)

Definition three_a := fun (x: A->B) (y: A->C) (z: A) (u: B) => y z.
Check three_a.
(*
  (A -> B) -> (A -> C) -> A -> B -> C
*)

Definition three_b := fun (x: A->B) (y: B->C) (z: A) => y (x z).
Check three_b.
(*
  (A -> B) -> (B -> C) -> A -> C
*)

Definition three_c := fun (x: A->B->C) (y: B) (z: A) => x z y.
Check three_c.
(*
  (A -> B -> C) -> B -> A -> C
*)

Definition three_d_1 := fun (x _: A) => x.
Check three_d_1.
(*
  A -> A -> A
*)

Definition three_d_2 := fun (_ x: A) => x.
Check three_d_2.
(*
  A -> A -> A
*)
