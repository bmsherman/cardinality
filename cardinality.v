Require Fin.
Require Iso.
Require Import PeanoNat.
Require Import Program.

Definition cardinality A n := Iso.T A (Fin.t n).

Lemma fin0_falso : forall (P:Prop),
  Fin.t 0 -> P.
Proof.
  inversion 1.
Qed.

Ltac dispatch :=
  cbn;
  intros;
  try lazymatch goal with
  | [ H: Fin.t 0 |- _ ] => apply (fin0_falso _ H)
  end;
  auto; try congruence.

Example false_0 : cardinality False 0.
Proof.
  refine (
    {| Iso.to := _
     ; Iso.from := _ |}); dispatch.
  destruct a.

  Grab Existential Variables.
  inversion 1.
  destruct 1.
Defined.

Example unit_1 : cardinality unit 1.
Proof.
  refine (
  {| Iso.to := fun _ => Fin.F1
   ; Iso.from := fun _ => tt |}); dispatch.
  destruct a; reflexivity.
  dependent destruction b.
  reflexivity.
  inversion b.
Defined.

Example bool_2 : cardinality bool 2.
Proof.
  refine (
  {| Iso.to := fun (b:bool) =>
    match b with
    | true => Fin.F1
    | false => Fin.FS Fin.F1
    end
   ; Iso.from := fun x =>
    match x with
    | Fin.F1 => true
    | Fin.FS _ => false
    end |}); dispatch.
  destruct a; auto.
  dependent destruction b; dispatch.
  dependent destruction b; dispatch.
Defined.