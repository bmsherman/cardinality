Require Import List.
Import ListNotations.
Require Fin Vector.

Set Implicit Arguments.

Definition fin_f_Sn A n (f: Fin.t (S n) -> A) : Fin.t n -> A :=
  (fun x => f (Fin.FS x)).

Definition fin_to_vec A n (f: Fin.t n -> A) : Vector.t A n.
Proof.
  induction n.
  (* base case: Vector.nil *)
  apply Vector.nil.
  (* cons *)
  constructor.
  (* element: f 0 *)
  apply (f Fin.F1).
  (* rest of vector comes from recursive call *)
  apply IHn.
  apply (fin_f_Sn f).
Defined.

Definition vec_to_fin A n (v: Vector.t A n) : Fin.t n -> A :=
  (fun x => Vector.nth v x).

Theorem fin_to_vec_inverse : forall A n (f: Fin.t n -> A),
  forall x, vec_to_fin (fin_to_vec f) x = f x.
Proof.
  unfold vec_to_fin.
  induction n; intros.
  - inversion x.
  - induction x; auto.
    apply IHx.
Qed.