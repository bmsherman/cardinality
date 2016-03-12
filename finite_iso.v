Require Import Finite.

Set Implicit Arguments.

Lemma iso_fin_0_1 :
  Iso.T (Fin.t 0) (Fin.t 1) ->
  False.
Proof.
  destruct 1.
  pose proof (from Fin.F1).
  inversion H.
Qed.

Lemma iso_fin_0_m : forall n,
  Iso.T (Fin.t 0) (Fin.t (S n)) ->
  False.
Proof.
  destruct 1.
  pose proof (from Fin.F1).
  inversion H.
Qed.

Lemma iso_to_injective : forall A B
  (i: Iso.T A B),
  forall a a', Iso.to i a = Iso.to i a' ->
    a = a'.
Proof.
  destruct i; cbn; intros.
  pose proof (from_to a).
  rewrite H in H0.
  rewrite from_to in H0.
  auto.
Qed.

Lemma iso_from_injective : forall A B
  (i: Iso.T A B),
  forall b b', Iso.from i b = Iso.from i b' ->
    b = b'.
Proof.
  destruct i; cbn; intros.
  pose proof (to_from b).
  rewrite H in H0.
  rewrite to_from in H0.
  auto.
Qed.

Lemma injective_unit_unit_to : forall A B
   (i: Iso.T (unit + A) (unit + B)),
   Iso.to i (inl tt) = inl tt ->
   (forall a, {b : B | Iso.to i (inr a) = inr b }).
Proof.
  intros.
  destruct (Iso.to i (inr a)) eqn:?.
  destruct u.
  rewrite <- H in Heqs.
  pose proof (iso_to_injective _ _ _ Heqs).
  congruence.
  eauto.
Defined.

Lemma injective_unit_unit_from : forall A B
   (i: Iso.T (unit + A) (unit + B)),
   Iso.to i (inl tt) = inl tt ->
   (forall b, {a : A | Iso.from i (inr b) = inr a}).
Proof.
  intros.
  destruct (Iso.from i (inr b)) eqn:?.
  destruct u.
  pose proof (Iso.to_from i (inr b)).
  rewrite Heqs in H0.
  congruence.

  eauto.
Defined.

Theorem injective_plus : forall A B
  (i: Iso.T (unit + A) (unit + B)),
  Iso.T A B.
Proof.
  intros.
  destruct (Iso.to i (inl tt)) eqn:?.
  - destruct u.
    refine ({| Iso.to := fun a => proj1_sig
                                  (injective_unit_unit_to i Heqs a);
               Iso.from := fun b => proj1_sig
                                    (injective_unit_unit_from i Heqs b) |});
      intros.
    case_eq (injective_unit_unit_to i Heqs a); intros; cbn.
    case_eq (injective_unit_unit_from i Heqs x); intros; cbn.
    clear H0.
    rewrite <- e in e0.
    rewrite (Iso.from_to i) in e0.
    congruence.

    case_eq (injective_unit_unit_from i Heqs b); intros; cbn.
    case_eq (injective_unit_unit_to i Heqs x); intros; cbn.
    clear H0.
    rewrite <- e in e0.
    rewrite (Iso.to_from i) in e0.
    congruence.
  - destruct (Iso.from i (inl tt)) eqn:?.
    destruct u.
    rewrite <- Heqs0 in Heqs.
    rewrite (Iso.to_from i) in Heqs.
    congruence.
    refine ({| Iso.to := fun a' =>
                           match Iso.to i (inr a') with
                           | inl tt => b
                           | inr b' => b'
                           end;
               Iso.from := fun b' =>
                             match Iso.from i (inr b') with
                             | inl tt => a
                             | inr a' => a'
                             end |}); intros.
    destruct (Iso.to i (inr a0)) eqn:?.
    destruct u.
    rewrite <- Heqs.
    rewrite (Iso.from_to i).
    rewrite <- Heqs1 in *.
    rewrite (Iso.from_to i) in Heqs0.
    congruence.

    rewrite <- Heqs1.
    now rewrite (Iso.from_to i).

    destruct (Iso.from i (inr b0)) eqn:?.
    destruct u.
    rewrite <- Heqs0.
    rewrite (Iso.to_from i).
    rewrite <- Heqs1 in *.
    rewrite (Iso.to_from i) in Heqs.
    congruence.

    rewrite <- Heqs1.
    now rewrite (Iso.to_from i).
Qed.

Lemma fint_iso_to_fin : forall n m,
    Iso.T (Fin.t n) (Fin.t m) ->
    Iso.T (Fin n) (Fin m).
Proof.
  intros.
  eapply Iso.Trans.
  eapply Iso.Sym.
  apply Finite.finIso.
  eapply Iso.Trans.
  eassumption.
  apply Finite.finIso.
Qed.

Lemma fin_iso_to_fint : forall n m,
    Iso.T (Fin n) (Fin m) ->
    Iso.T (Fin.t n) (Fin.t m).
Proof.
  intros.
  eapply Iso.Trans.
  apply Finite.finIso.
  eapply Iso.Trans.
  eassumption.
  eapply Iso.Sym.
  apply Finite.finIso.
Qed.

Lemma no_smaller_iso : forall n k,
    Iso.T (Fin.t n) (Fin.t (n + S k)) ->
    False.
Proof.
  intros.
  induction n; cbn in *.
  eapply iso_fin_0_m; eauto.
  apply IHn.
  apply fin_iso_to_fint.
  apply injective_plus.
  apply fint_iso_to_fin in H.
  assumption.
Qed.

Lemma no_smaller_iso' : forall n m,
    n < m ->
    Iso.T (Fin.t n) (Fin.t m) ->
    False.
Proof.
  intros.
  rewrite <- (Minus.le_plus_minus_r (S n) m) in H0 by auto.
  cbn in H0.
  rewrite plus_n_Sm in H0.
  eapply no_smaller_iso; eauto.
Qed.

Theorem fin_iso : forall n m,
    Iso.T (Fin.t n) (Fin.t m) ->
    n = m.
Proof.
  intros.
  destruct (Compare_dec.lt_eq_lt_dec n m) as [ [] | ]; auto; exfalso.
  - eapply no_smaller_iso'; eauto.
  - eapply no_smaller_iso'; eauto.
    apply Iso.Sym; auto.
Qed.