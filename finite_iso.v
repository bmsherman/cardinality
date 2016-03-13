(**

Properties of isomorphisms between finite types [Fin.t].

Mostly defines lemmas building up to the main theorem, that if there
is an isomorphism [Iso.T (Fin.t n) (Fin.t m)] then [n = m].

*)

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

(** (Essentially) one direction of the [injective_plus] isomorphism in
the case that the units map to one another, with an extra fact to make
the proofs easier.

The function itself is fairly messy so we define it in a proof. *)

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
(* note that the returned sig captures everything important about the
function's behavior, so we can make the implementation completely
opaque and still reason about the function! *)
Qed.

(** (Essentially) the other direction of the [injective_plus]
isomorphism when the units map to one another.

We use the same hypothesis (the to direction) to make using the
function easy, and take care of deriving the appropriate fact about
[from (inl tt)].  *)
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
Qed.

(** This is the difficult lemma that the main proof is ultimately
based on. It proves that type successor, defined as (unit +), is
injective modulo isomorphism. This really is a successor for the Fin
type, which has a number of isomorphisms defined by Finite. *)
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
    destruct (injective_unit_unit_to i Heqs a); intros; cbn.
    destruct (injective_unit_unit_from i Heqs x); intros; cbn.
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

(** convert from an isomorphism on [Fin.t] to one on [Finite.Fin] *)
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

(** convert from an isomorphism on [Finite.Fin] to one on [Fin.t] *)
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

(** This is the main lemma that gives the result, but all the
difficult work is in the inductive cases, which is proven by
[injective_plus] with the right induction, and in some minor
isomorphism hops to reach the right expression of the types. *)
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

(** Re-express no_smaller_iso in terms of a < proof rather than an
explicit difference, a simple arithmetic fact. *)
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

(** The main lemma of this file is now a simple corollary, with the n
< m and m < n cases symmetrically handled by the above. *)
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