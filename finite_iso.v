(**

Properties of isomorphisms between finite types [Fin.t].

Mostly defines lemmas building up to the main theorem, that if there
is an isomorphism [Iso.T (Fin.t n) (Fin.t m)] then [n = m].

*)

Require Import Finite.

Set Implicit Arguments.

Hint Rewrite @Iso.from_to : iso.
Hint Rewrite @Iso.to_from : iso.

(* helpers for using from_to and to_from with an equality
rather than a syntatic from (to a) or to (from b) *)
Lemma iso_from_to_eq : forall A B {i: Iso.T A B} {a a' b},
  Iso.from i b = a ->
  Iso.to i a' = b ->
  a = a'.
Proof.
  intros; subst; autorewrite with iso; auto.
Qed.

Lemma iso_to_from_eq : forall A B {i: Iso.T A B} {a b b'},
  Iso.to i a = b ->
  Iso.from i b' = a ->
  b = b'.
Proof.
  intros; subst; autorewrite with iso; auto.
Qed.

(* behaves like pose proof pf but does nothing if a proof of the same
fact is in the context *)
Ltac learn pf :=
  let P := type of pf in
  lazymatch goal with
  | [ H: P |- _ ] => fail
  | _ => pose proof pf
  end.

Ltac simplify :=
  (* simplifications *)
  intros; cbn;
  autorewrite with iso in *;
  repeat lazymatch goal with
    | [ u:unit |- _ ] => destruct u
    end;
  (* apply Iso inverse theorems with eq helpers *)
  repeat match goal with
         | [ H: Iso.from ?i ?b = _,
                H': Iso.to ?i _ = ?b |- _ ] =>
           learn (iso_from_to_eq H H')
         | [ H: Iso.to ?i ?a = _,
                H': Iso.from ?i _ = ?a |- _ ] =>
           learn (iso_to_from_eq H H')
         end;
  (* solve simple goals *)
  try congruence;
  eauto.

(* destruct the innermost match in e *)
Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
    destruct_matches_in d
  | _ => case_eq e; intros
  end.

Ltac case_match :=
  match goal with
  | [ |- ?g ] => destruct_matches_in g; simplify
  end.

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
  intros.
  pose proof (Iso.from_to i a).
  rewrite H in H0; simplify.
Qed.

Lemma iso_from_injective : forall A B
  (i: Iso.T A B),
  forall b b', Iso.from i b = Iso.from i b' ->
    b = b'.
Proof.
  intros.
  pose proof (Iso.to_from i b).
  rewrite H in H0; simplify.
Qed.

(** (Essentially) one direction of the [injective_plus] isomorphism in
the case that the units map to one another, with an extra fact to make
the proofs easier.

The function itself is fairly messy so we define it in a proof. *)

Lemma injective_unit_unit_to : forall A B
   (i: Iso.T (option A) (option B)),
   Iso.to i None = None ->
   (forall a, {b : B | Iso.to i (Some a) = Some b }).
Proof.
  intros.
  case_eq (Iso.to i (Some a)); simplify.
  rewrite <- H0 in H.
  apply iso_to_injective in H.
  congruence.
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
   (i: Iso.T (option A) (option B)),
   Iso.to i None = None ->
   (forall b, {a : A | Iso.from i (Some b) = Some a}).
Proof.
  intros.
  case_eq (Iso.from i (Some b)); simplify.
Qed.

(** This is the difficult lemma that the main proof is ultimately
based on. It proves that type successor, defined as (unit +), is
injective modulo isomorphism. This really is a successor for the Fin
type, which has a number of isomorphisms defined by Finite. *)
Theorem injective_plus : forall A B
  (i: Iso.T (option A) (option B)),
  Iso.T A B.
Proof.
  intros.
  case_eq (Iso.to i None); simplify.
  - (* derive from tt = some a *)
    case_eq (Iso.from i None); simplify.
    refine ({| Iso.to := fun a' =>
                           match Iso.to i (Some a') with
                           | None => b
                           | Some b' => b'
                           end;
               Iso.from := fun b' =>
                             match Iso.from i (Some b') with
                             | None => a
                             | Some a' => a'
                             end |});
      simplify;
      repeat case_match.
  - refine ({| Iso.to := fun a => proj1_sig
                                  (injective_unit_unit_to i H a);
               Iso.from := fun b => proj1_sig
                                    (injective_unit_unit_from i H b) |});
      simplify;
      unfold proj1_sig; repeat case_match.
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