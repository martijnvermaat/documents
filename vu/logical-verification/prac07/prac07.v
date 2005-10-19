(* logical verification 2005 - 2006 week 7 *)

(*
  Martijn Vermaat
  mvermaat
  1362917
*)

Variable Terms : Set.
Variable M : Terms.

(* predicates *)
Variable A : Prop.
Variable P : Terms -> Prop.
Variable Q : Terms -> Prop.
Variable R : Terms -> Terms -> Prop.

(* example 1 *)

Lemma example_1 : 
  (forall x : Terms , P x -> Q x)
  ->
  (forall x : Terms , P x)
  ->
  forall y : Terms , Q y .

Proof.
intro H.
intro I.
intro y.
apply H.
apply I.
Qed.
Print example_1.

Lemma example_2 :
  forall x : Terms , P x -> ~(forall y, ~(P y)) .  

Proof.
intro x.
intro H.
unfold not.
intro I.
apply (I x).
exact H.
Qed.

Lemma example_3 :
  (exists x:Terms, P x \/ Q x) 
  ->
  (exists x:Terms, P x) \/ (exists x:Terms, Q x) .

Proof.
intro H.
elim H.
intro x.
intro I.
elim I.

intro I1.
left.
exists x.
exact I1.

intro I2.
right.
exists x.
exact I2.

Qed.

Variable Domain : Set .
Lemma example_4 : exists x : Domain , True.

Proof.
Abort.

Lemma example_5 :
  forall x:Terms, P x -> forall y, P y.

intros x H y.
Abort.

Lemma example_6 :
  forall x:Terms, (exists x:Terms, P x) ->  P x .

Proof.
intro x.
intro H.
elim H.
intro y.
intro I.
Abort.

(* prove the following six lemma's *)

Lemma one : (forall x : Terms, P x) -> P M.

Proof.
intro.
apply H.
Qed.

Lemma two : A -> forall x : Terms, A.

Proof.
intro.
intro.
exact H.

Lemma three :
 (forall x : Terms, P x -> Q x) ->
 (forall x : Terms, P x) -> forall x : Terms, Q x.

Proof.
intro.
intro.
intro.
apply H.
apply H0.
Qed.

Lemma four : (A -> forall x : Terms, P x) -> forall y : Terms, A -> P y.

Proof.
intro.
intro.
intro.
apply H.
exact H0.
Qed.

Lemma five : (forall x y : Terms, R x y) -> forall x : Terms, R x x.

Proof.
intro.
intro.
apply H.
Qed.

Lemma six : forall x : Terms, P x -> ~ (forall y : Terms, ~ P y).

Proof.
intro.
intro.
unfold not.
intro.
apply (H0 x).
exact H.
Qed.

(* define sym as the proposition stating that
   R is symmetric, that is,
   if x and y are related via R, then y and x are related via R *)

Definition sym := forall x y: Terms, R x y -> R y x.

(* define trans as the proposition stating that
   R is transitive, that is,
   if x and y are related via R, and y and z are related via R,
   then x and z are related via R  *)

Definition trans := forall x y z: Terms, R x y -> R y z -> R x z.

Definition reflif := forall x : Terms, (exists y : Terms, R x y) -> R x x.

(* prove the following lemma and print and inspect the proof term *)

Lemma seven : sym -> trans -> reflif.

Proof.
unfold sym, trans, reflif.
intro.
intro.
intro.
intro.
destruct H1.
apply (H0 x x0).
exact H1.
apply H.
exact H1.
Qed.
