Set Implicit Arguments.

Require Import finite_iso.

Theorem empty_not_unit : Empty_set <> unit.
Proof.
  intro.
  pose proof tt.
  rewrite <- H in H0.
  inversion H0.
Qed.

Theorem unit_not_bool : unit <> bool.
Proof.
  intro.
  assert (forall x y:unit, x = y).
  destruct x, y; auto.
  rewrite H in H0.
  pose proof (H0 true false).
  inversion H1.
Qed.

Theorem unit_not_option : forall A (a:A),
   (unit:Type) <> option A.
Proof.
  unfold not; intros.
  assert (forall x y:unit, x = y).
  destruct x, y; auto.
  rewrite H in H0.
  pose proof (H0 (Some a) None).
  inversion H1.
Qed.

Theorem bool_not_nat : bool <> nat.
Proof.
  intro.
  assert (forall x y z:bool, x = y \/ y = z \/ x = z).
  destruct x, y, z; eauto.
  rewrite H in H0.
  pose proof (H0 0 1 2).
  intuition; match goal with
             | [ H: @eq nat _ _ |- _ ] => inversion H
             end.
Qed.

Section TypeCardinality.

Require Fin.
Require Iso.
Require Import cardinality.

Theorem no_iso_ineq : forall A B,
  (Iso.T A B -> False) ->
  A <> B.
Proof.
  unfold not; intros.
  apply H.
  rewrite H0.
  apply Iso.Refl.
Qed.

Theorem one_cardinality : forall A n m
  (iso_n: cardinality A n)
  (iso_m: cardinality A m),
  n = m.
Proof.
  intros.
  pose proof (Iso.Trans (Iso.Sym iso_n) iso_m).
  apply fin_iso; assumption.
Qed.

Theorem neq_cardinalities : forall (A B:Type) n m,
  cardinality A n ->
  cardinality B m ->
  n <> m ->
  A <> B.
Proof.
  intros.
  intro; subst.
  eauto using one_cardinality.
Qed.

Example unit_neq_bool : (unit:Type) <> bool.
Proof.
  apply neq_cardinalities with (n := 1) (m := 2).
  exact unit_1.
  exact bool_2.
  auto.
Qed.

Theorem powerset_bigger : forall A, Iso.T A (A -> bool) -> False.
Proof.
  destruct 1.
  pose (f := fun x => if (to x x) then false else true).
  assert (to (from f) (from f) = f (from f)) by
    (rewrite to_from; reflexivity).
  destruct (to (from f) (from f)) eqn:?.
  unfold f in *.
  rewrite Heqb in H.
  congruence.

  unfold f in *.
  rewrite Heqb in H.
  congruence.

Restart.
  destruct 1.
  pose (f := fun x => negb (to x x)).
  assert (f (from f) = negb (to (from f) (from f))).
  unfold f.
  rewrite to_from.
  reflexivity.
  rewrite to_from in H.
  eapply Bool.no_fixpoint_negb; eauto.
Qed.

Corollary type_not_powerset : forall A,
  A <> (A -> bool).
Proof.
  intros.
  apply no_iso_ineq.
  apply powerset_bigger.
Qed.

End TypeCardinality.