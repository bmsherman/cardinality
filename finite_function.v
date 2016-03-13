(**

Isomorphism between functions on [Fin.t n] and [Vector.t A n].

Defines a function to turn a finite function into a vector of its
values. Proves that this function is the inverse (both left and right)
of [Vector.nth], giving an isomorphism.

*)

Require Iso.
Require Fin Vector.
Require Import Program.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Definition fin_f_Sn A n (f: Fin.t (S n) -> A) : Fin.t n -> A :=
  (fun x => f (Fin.FS x)).

(* The main definition: converts a finite function into a vector of
its values. *)
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

(** The inverse of [fin_to_vec] is already defined as [Vector.nth]. *)
Definition vec_to_fin A n (v: Vector.t A n) : Fin.t n -> A :=
  (fun x => Vector.nth v x).

(* One direction of the main [fin_to_vec] correctness proof. *)
Theorem fin_to_vec_inverse : forall A n (f: Fin.t n -> A),
  forall x, vec_to_fin (fin_to_vec f) x = f x.
Proof.
  unfold vec_to_fin.
  induction n; intros.
  - inversion x.
  - induction x; auto.
    apply IHx.
Qed.

(** Add a mapping to a finite function. *)
Definition fin_f_add A n (f: Fin.t n -> A) (a:A) : Fin.t (S n) -> A.
Proof.
  intros.
  inversion H.
  exact a.
  exact (f H1).
Defined.

(** Reduction proof that converting a cons vector is the same as
converting the vector and then adding a single mapping in the sense of
[fin_f_add]. *)
Lemma fin_to_vec_cons : forall A n (v: Vector.t A n) a,
    vec_to_fin (Vector.cons _ a _ v) =
    fin_f_add (vec_to_fin v) a.
Proof.
  intros.
  extensionality x.
  dependent induction x; cbn; auto.
Qed.

(** Reduction proof that converting a function with one more mapping to
a vector is the same as cons'ing the element onto the original
function.

Whereas [fin_to_vec] actually uses (dependent) recursion over n, this
proves equivalence to a recursive definition on the structure of the
vector. *)
Lemma vec_fin_f_add : forall A n (f: Fin.t n -> A) a,
    fin_to_vec (fin_f_add f a) =
    Vector.cons _ a _ (fin_to_vec f).
Proof.
  intros.
  induction n; cbn; auto.
Qed.

(* The other direction of the [fin_to_vec] correctness proof. *)
Theorem vec_to_fin_inverse : forall A n (v: Vector.t A n),
    fin_to_vec (vec_to_fin v) = v.
Proof.
  intros.
  induction v; auto.
  (* the computation fin_to_vec performs results in a hairy use of
  nat_rect, but we can use proofs to reduce this computation in a
  nicer way *)
  rewrite fin_to_vec_cons.
  rewrite vec_fin_f_add.
  rewrite IHv.
  auto.
Qed.

(** Package isomorphism functions and theorems in an [Iso.T]. *)
Definition fin_vec_iso A n : Iso.T (Fin.t n -> A) (Vector.t A n).
Proof.
  refine ({| Iso.to := @fin_to_vec A n;
             Iso.from := @vec_to_fin A n |} ).
  - intros.
    apply functional_extensionality.
    apply fin_to_vec_inverse.
  - apply vec_to_fin_inverse.
Defined.