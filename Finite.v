Require Finite.Iso.
Require Fin.

Set Asymmetric Patterns.

(** A type family which is isomorphic to Fin.t, but defined in
    terms of simpler types by recursion, and is a little bit
    easier to work with. *)
Fixpoint Fin (n : nat) : Set := match n with
  | 0 => Empty_set
  | S n' => option (Fin n')
  end.

(** Fin and Fin.t are isomorphic for every size. *)
Theorem finIso (n : nat) : Iso.T (Fin.t n) (Fin n).
Proof.
induction n.
- eapply Iso.Build_T.
  intros a. inversion a.
  intros b. inversion b. 
- 
refine (
{| Iso.to := fun x => (match x in Fin.t n'
  return (S n = n') -> Fin (S n) with
   | Fin.F1 _ => fun _ => None
   | Fin.FS n' x' => fun pf => Some (Iso.to IHn (eq_rect n' Fin.t x' _ (eq_sym (eq_add_S _ _ pf))))
   end) eq_refl
 ; Iso.from := fun x => match x with
   | None => Fin.F1
   | Some x' => Fin.FS (Iso.from IHn x')
   end
|}).
intros a.
Require Import Program.
dependent destruction a; simpl.
reflexivity. rewrite Iso.from_to. reflexivity.
intros b. destruct b. 2: reflexivity.
  simpl. rewrite Iso.to_from. reflexivity.
Grab Existential Variables.
intros bot. contradiction.
intros f0. inversion f0.
Defined.

Lemma botNull (A : Type) : Iso.T A (A + Empty_set).
Proof.
refine (
{| Iso.to   := inl
 ; Iso.from := fun x => match x with
    | inl x' => x'
    | inr bot => Empty_set_rect (fun _ => A) bot
   end
|}).
reflexivity.
intros b. destruct b. reflexivity. contradiction.
Defined.

Lemma option_Succ (A : Type) : Iso.T (option A) (unit + A).
Proof.
unshelve eapply (
{| Iso.to := fun x : option A => match x with
  | None => inl tt
  | Some y => inr y
  end
 ; Iso.from := fun y : unit + A => match y with
  | inl tt => None
  | inr x => Some x
  end
|}); intros []; try reflexivity.
destruct u. reflexivity.
Defined.

Fixpoint splitt (m : nat)
  : forall (n : nat), Fin.t (m + n) -> (Fin.t m + Fin.t n).
Proof.
unshelve eapply (
  match m return (forall (n : nat), Fin.t (m + n) -> (Fin.t m + Fin.t n)) with
  | 0 => fun _ => inr
  | S m' => fun n x => (match x as x0 in Fin.t k 
    return forall (pf : k = (S m' + n)), (Fin.t (S m') + Fin.t n) with
    | Fin.F1 _ => fun pf => inl Fin.F1
    | Fin.FS n' x' => fun pf => _
    end) eq_refl
  end).
simpl in pf.
apply eq_add_S in pf.
rewrite pf in x'.
refine (match splitt m' n x' with
  | inl a => inl (Fin.FS a)
  | inr b => inr b
  end).
Defined.

Definition split (m : nat)
  : forall (n : nat), Fin (m + n) -> (Fin m + Fin n).
Proof.
induction m; simpl.
- intros. right. assumption.
- intros. destruct H.
  destruct (IHm _ f).
  + left. apply Some. assumption.
  + right. assumption.
  + left. apply None.
Defined.

Definition FinL {m n} : Fin m -> Fin (m + n).
Proof.
induction m; simpl; intros x.
- induction x.
- induction x.
  + apply Some. apply IHm. assumption.
  + apply None.
Defined.

Definition FinR {m n} : Fin m -> Fin (n + m).
Proof.
induction n; simpl; intros x.
- assumption.
- apply Some. apply IHn. assumption.
Defined.

Lemma splitL : forall {m n : nat} {x : Fin m},
  split m n (FinL x) = inl x.
Proof.
intros m. induction m; intros n x.
- induction x.
- induction x; simpl. 
  + rewrite IHm. reflexivity. 
  + reflexivity.
Qed.

Lemma splitR : forall {m n : nat} {x : Fin n},
  split m n (FinR x) = inr x.
Proof.
intros m. induction m; intros n x; simpl.
- reflexivity.
- rewrite (IHm n x). reflexivity.
Qed.

Lemma splitInj : forall {m n : nat} {x y : Fin (m + n)},
  split m n x = split m n y -> x = y.
Proof.
intros m; induction m; intros n x y Heq.
- inversion Heq. reflexivity.
- induction x; induction y.
  + apply f_equal. simpl in Heq. apply IHm.
    destruct (split m n a) eqn:sx;
    destruct (split m n a0) eqn:sy.
    apply f_equal; congruence.
    congruence. congruence. congruence.
  + simpl in Heq. destruct (split m n a); congruence.
  + simpl in Heq. destruct (split m n a); congruence.
  + reflexivity.
Qed.

Lemma PlusAssoc {A B C}
  : Iso.T (A + (B + C)) ((A + B) + C).
Proof.
unshelve econstructor; intros x.
- destruct x as [? | []]; auto.
- destruct x as [[] | ?]; auto.
- destruct x as [? | []]; auto.
- destruct x as [[] | ?]; auto.
Defined.

Lemma optionCong {A B} (i : Iso.T A B)
  : Iso.T (option A) (option B).
Proof.
unshelve econstructor; intros x.
- destruct x. 
  + apply Some. apply i. assumption. 
  + apply None.
- destruct x.
  + apply Some. apply i. assumption. 
  + apply None.
- destruct x; simpl; auto.
  rewrite Iso.from_to. reflexivity.
- destruct x; simpl; auto.
  rewrite Iso.to_from. reflexivity.
Defined. 

Lemma finPlus1 {m n : nat} :
  Iso.T (Fin m + Fin n) (Fin (m + n)).
Proof.
induction m; simpl.
- eapply Iso.Trans. eapply Iso.PlusComm.
  eapply Iso.Sym.  apply botNull.
- eapply Iso.Trans. eapply Iso.PlusCong.
  eapply option_Succ. apply Iso.Refl.
  eapply Iso.Trans.
  eapply Iso.Sym. eapply PlusAssoc.
  eapply Iso.Trans. eapply Iso.Sym. eapply option_Succ.
  apply optionCong. assumption.
Defined.

Lemma mult_Empty_l {A}
  : Iso.T (Empty_set * A) Empty_set.
Proof.
unshelve econstructor; intros x.
- destruct x. assumption.
- destruct x.
- destruct x as [[] ?].
- destruct x.
Defined.

Lemma mult_plus_distr_l {A B C}
  : Iso.T ((A + B) * C) (A * C + B * C).
Proof.
unshelve econstructor; intros x.
- destruct x as [[? | ?] ?]; auto.
- destruct x as [[? ?] | [? ?]]; auto.
- destruct x as [[? | ?] ?]; auto.
- destruct x as [[? ?] | [? ?]]; auto.
Defined.

Lemma mult_unit_l {A}
  : Iso.T (unit * A) A.
Proof.
unshelve econstructor; intros x.
- destruct x; auto.
- exact (tt, x).
- destruct x as [[] ?]; auto.
- auto.
Defined.

Definition finMult1 {m n : nat}
  : Iso.T (Fin m * Fin n) (Fin (m * n)).
Proof.
induction m; simpl.
- apply mult_Empty_l.
- eapply Iso.Trans. eapply Iso.TimesCong.
  eapply option_Succ. apply Iso.Refl.
  eapply Iso.Trans. apply mult_plus_distr_l.
  eapply Iso.Trans. eapply Iso.PlusCong.
  eapply mult_unit_l. eassumption.
  apply finPlus1.
Defined.

Lemma finPlus {m n : nat} :
  Iso.T (Fin m + Fin n) (Fin (m + n)).
Proof.
unshelve eapply (
{| Iso.to := fun x => match x with
   | inl a => FinL a
   | inr b => FinR b
   end
 ; Iso.from := split m n
|}).
- intros. destruct a; simpl.
  apply splitL. apply splitR.
- intros. simpl. induction m.
  + simpl. reflexivity.
  + induction b. 
    * specialize (IHm a).  simpl.
      destruct (split m n a) eqn:sa.
      simpl. congruence. congruence.
    * simpl. reflexivity.
Defined.

Lemma splittL : forall {m n : nat} {x : Fin.t m},
  splitt m n (Fin.L n x) = inl x.
Proof.
intros m. induction m; intros n x.
- inversion x.
- dependent destruction x; simpl.
  + reflexivity.
  + rewrite (IHm n x). reflexivity.
Qed.

Lemma splittR : forall {m n : nat} {x : Fin.t n},
  splitt m n (Fin.R m x) = inr x.
Proof.
intros m. induction m; intros n x; simpl.
- reflexivity.
- rewrite (IHm n x). reflexivity.
Qed.

Lemma splittInj : forall {m n : nat} {x y : Fin.t (m + n)},
  splitt m n x = splitt m n y -> x = y.
Proof.
intros m; induction m; intros n x y Heq.
- inversion Heq. reflexivity.
- dependent destruction x; dependent destruction y.
  + reflexivity.
  + simpl in Heq. destruct (splitt m n y); inversion Heq.
  + simpl in Heq. destruct (splitt m n x); inversion Heq.
  + apply f_equal. simpl in Heq. apply IHm.
    destruct (splitt m n x) eqn:sx;
    destruct (splitt m n y) eqn:sy.
    apply f_equal. 
    assert (forall (A B : Type) (x y : A), @inl A B x = @inl A B y -> x = y).
    intros A B x0 y0 Heqn. inversion Heqn. reflexivity.
    apply H in Heq. apply Fin.FS_inj in Heq. assumption.
    inversion Heq. inversion Heq. apply f_equal. injection Heq. trivial.
Qed.

Fixpoint splittMult (m : nat)
  : forall (n : nat), Fin.t (m * n) -> (Fin.t m * Fin.t n) 
  := match m return (forall (n : nat), Fin.t (m * n) -> (Fin.t m * Fin.t n)) with
  | 0 => fun _ => Fin.case0 _
  | S m' => fun n x => match splitt n (m' * n) x with
    | inl a => (Fin.F1, a)
    | inr b => match splittMult m' n b with
      | (x, y) => (Fin.FS x, y)
      end
    end
  end.

Lemma fintPlus : forall {m n : nat},
  Iso.T (Fin.t m + Fin.t n) (Fin.t (m + n)).
Proof.
intros m n.
refine (
{| Iso.to := fun x => match x with
   | inl a => Fin.L n a
   | inr b => Fin.R m b
   end
 ; Iso.from := splitt m n
|}).
intros. destruct a; simpl. induction m; simpl.
- inversion t.
Require Import Program.
- dependent destruction t; simpl.
  + reflexivity.
  + rewrite IHm. reflexivity.
- induction m; simpl. reflexivity. rewrite IHm. reflexivity.
- induction m; intros; simpl.
  + reflexivity.
  + dependent destruction b; simpl. reflexivity.
     pose proof (IHm b).
     destruct (splitt m n b) eqn:seqn;
     simpl; rewrite H; reflexivity.
Qed.

Lemma fintMult : forall {m n : nat},
  Iso.T (Fin.t m * Fin.t n) (Fin.t (m * n)).
Proof.
intros m n.
refine (
{| Iso.to := fun x => match x with (a, b) => Fin.depair a b end
 ; Iso.from := splittMult m n
|}).
intros p. destruct p.
induction m; simpl.
- inversion t.
- dependent destruction t; simpl.
  + rewrite splittL. reflexivity.
  + rewrite splittR. rewrite (IHm t). reflexivity.

- induction m; intros b; simpl.
  + inversion b.
  + destruct (splitt n (m * n) b) eqn:seqn.
    * simpl. rewrite <- splittL in seqn. 
      apply splittInj in seqn. symmetry. assumption.
    * pose proof (IHm t). assert (b = Fin.R n t).
      apply (@splittInj n (m * n)). 
      rewrite seqn. symmetry. apply splittR.
      rewrite H0. simpl.
      destruct (splittMult m n t) eqn:smeqn.
      simpl. rewrite <- H. reflexivity.
Defined.

Definition splitMult (m : nat)
  : forall n : nat, Fin (m * n) -> Fin m * Fin n.
Proof.
induction m; intros n x.
- induction x.
- destruct (split _ _ x) as [l | r].
  + exact (None, l).
  + destruct (IHm _ r) as [a b].
    exact (Some a, b).
Defined.

Definition depair {m n : nat}
  : Fin m * Fin n -> Fin (m * n).
Proof.
induction m; simpl; intros x.
- destruct x as [[] ?].
- destruct x as [x y]. destruct x as [l | r].
Abort.

Fixpoint pow (b e : nat) : nat := match e with
  | 0 => 1
  | S e' => b * pow b e'
  end.

Theorem finPow : forall {e b : nat},
  Iso.T (Fin.t (pow b e)) (Fin.t e -> Fin.t b).
Proof.
intros e. induction e; intros n; simpl.
- eapply Iso.Trans. apply finIso. simpl. eapply Iso.Trans.
  eapply option_Succ. eapply Iso.Trans.
  eapply Iso.Sym. apply botNull. eapply Iso.Trans. Focus 2.
  eapply Iso.FuncCong. eapply Iso.Sym. apply finIso. apply Iso.Refl.
  simpl. apply Iso.Sym. apply Iso.FFunc.
- eapply Iso.Trans. eapply Iso.Sym. apply fintMult.
  eapply Iso.Trans. Focus 2. eapply Iso.FuncCong.
  eapply Iso.Sym. apply finIso. apply Iso.Refl.
  simpl. eapply Iso.Trans. Focus 2. eapply Iso.Sym.
  eapply Iso.Trans. eapply Iso.FuncCong. eapply option_Succ.
  eapply Iso.Refl. eapply Iso.Refl. apply Iso.Sym.
  eapply Iso.PlusFunc.
  apply Iso.TFunc. eapply Iso.Trans. eapply Iso.FuncCong.
  eapply Iso.Sym. apply finIso. apply Iso.Refl. eapply Iso.Sym.
  apply IHe.
Qed.

(** A universe of codes for finite types. *)
Inductive U : Set :=
  | U0    : U
  | U1    : U
  | UPlus : U -> U -> U
  | UTimes : U -> U -> U
  | UFunc : U -> U -> U
  | UFint : nat -> U
  | UFin : nat -> U.

(** The types which the codes of U represent. *)
Fixpoint ty (t : U) : Set := match t with
  | U0 => Empty_set
  | U1 => unit
  | UPlus a b => (ty a + ty b)%type
  | UTimes a b => (ty a * ty b)%type
  | UFunc a b => ty a -> ty b
  | UFint n => Fin.t n
  | UFin n => Fin n
  end.

(** For every code for a finite type, we give its cardinality as
    a natural number. *)
Fixpoint Ucard (t : U) : nat := match t with
  | U0 => 0
  | U1 => 1
  | UPlus a b => Ucard a + Ucard b
  | UTimes a b => Ucard a * Ucard b
  | UFunc a b => pow (Ucard b) (Ucard a)
  | UFint n => n
  | UFin n => n
  end.
    
(** Each type in the finite universe is isomorphic to the Fin.t
    family whose size is determined by the cardinality function above. *)
Theorem finChar (t : U) : Iso.T (ty t) (Fin.t (Ucard t)).
Proof.
induction t; simpl.
- apply Iso.Sym. apply (finIso 0).
- apply Iso.Sym. apply (@Iso.Trans _ (Fin 1)). apply (finIso 1).
  simpl. eapply Iso.Trans. apply option_Succ. eapply Iso.Sym. apply botNull.
- eapply Iso.Trans. eapply Iso.PlusCong. eassumption.
  eassumption.
  apply fintPlus.
- eapply Iso.Trans. eapply Iso.TimesCong; try eassumption.
  apply fintMult.
- eapply Iso.Trans. eapply Iso.FuncCong; try eassumption.
  apply Iso.Sym. apply finPow.
- apply Iso.Refl.
- apply Iso.Sym. apply finIso.
Qed.

(** A type for evidence that a type is finite: a type is finite if
    any of the following hold:
    a) it is True
    b) it is False
    c) it is a sum of finite types
    d) it is isomorphic to a finite type

    This is not minimal. We could have replaced b) and c) with the condition
    e) it is the sum of True with a finite type
       (this is the analog of Successor)
    But this definition is simple so I like it.
*)

Inductive T : Type -> Type :=
  | F0 : T Empty_set
  | FS : forall {A}, T A -> T (option A)
  | FIso : forall {A B}, T A -> Iso.T A B -> T B
.

Fixpoint card {A} (fin : T A) := match fin with
  | F0 => 0
  | FS _ n => S (card n)
  | FIso _ _ x iso => card x
  end.

Definition finT (n : nat) : T (Fin.t n).
Proof. eapply FIso. Focus 2. eapply Iso.Sym. eapply finIso.
induction n; simpl.
- apply F0.
- apply FS. assumption.
Defined.

Definition fin (n : nat) : T (Fin n).
Proof.
induction n.
- exact F0.
- apply FS. assumption.
Defined.

Definition finU (A : U) : T (ty A).
Proof. 
eapply FIso. Focus 2. eapply Iso.Sym. apply finChar.
apply finT.
Qed.

Definition iso {A : Type} (fin : T A) : Iso.T A (Fin.t (card fin)).
Proof.
induction fin.
-  apply (finChar U0).
- apply Iso.Sym. eapply Iso.Trans. 
  apply finIso. simpl. eapply Iso.Trans. 
  eapply option_Succ. eapply Iso.Trans. 
  Focus 2. eapply Iso.Sym. eapply option_Succ.
apply Iso.PlusCong. apply Iso.Refl.
  eapply Iso.Trans. eapply Iso.Sym. apply finIso. apply Iso.Sym.
  assumption.
- eapply Iso.Trans. eapply Iso.Sym. eassumption.
  assumption. 
Qed.

Definition true : T unit := finU U1.

Definition plus {A B : Type} (fa : T A) (fb : T B) : T (A + B).
Proof.
eapply (@FIso (Fin.t (card fa + card fb))). apply (finU (UFint _)).
eapply Iso.Trans. eapply Iso.Sym. apply fintPlus.
eapply Iso.PlusCong; eapply Iso.Sym; apply iso.
Qed.

Lemma finiteSig {A : Type} (fa : T A)
  : forall {B : A -> Type}, 
  (forall (x : A), T (B x))
  -> sigT (fun S => (T S * Iso.T (sigT B) S)%type).
Proof.
induction fa; intros b fb.
- exists Empty_set. split. constructor. apply Iso.FSig.
- pose proof (IHfa (fun x => b (Some x)) (fun x => fb (Some x))).
  destruct X. destruct p.
  exists (b None + x)%type. constructor. apply plus. apply fb. 
  assumption.
  eapply Iso.Trans.
  eapply (Iso.sigmaProp (option_Succ A)).
  apply Iso.PlusSig.
  simpl. eapply (@Iso.TSig (fun x0 => b match x0 with
                     | () => None
                     end)).
  assumption.
- pose (Iso.Sym t).
  pose proof (IHfa (fun x => b (Iso.from t0 x))
                   (fun x => fb (Iso.from t0 x))).
  destruct X. destruct p.
  exists x. split. assumption.
  eapply Iso.Trans. Focus 2. apply t2.
  apply Iso.sigmaProp.
Defined.

(** Sigma types are closed under finiteness. *)
Theorem Sig {A : Type} {B : A -> Type} 
  : T A 
  -> (forall (x : A), T (B x))
  -> T (sigT B).
Proof.
intros fA fB.
pose proof (finiteSig fA fB).
destruct X. destruct p.
eapply FIso. apply t.
apply Iso.Sym. assumption.
Defined.

(** Product types are closed under finiteness. *)
Theorem times {A B : Type} : T A -> T B -> T (A * B).
Proof.
intros fa fb.
eapply FIso. Focus 2. eapply Iso.Sym. eapply Iso.sigTimes.
apply Sig. assumption. apply (fun _ => fb).
Defined.

Lemma finiteMapped {A : Type} (fa : T A)
  : forall {B : Type}, T B -> sigT (fun S => (T S * Iso.T (A -> B) S)%type).
Proof.
induction fa.
- intros. exists unit. apply (true, Iso.FFunc).
- intros B fb.
  destruct (IHfa B fb).
  exists (B * x)%type.
  destruct p. split. apply (times fb t).
  eapply Iso.Trans. eapply Iso.FuncCong.
  eapply option_Succ. apply Iso.Refl.
  apply (Iso.PlusFunc Iso.TFunc t0).
- intros B1 fb.
  destruct (IHfa B1 fb).
  destruct p.
  exists x.
  split.
  assumption.  
  eapply Iso.Trans.
  eapply Iso.Sym.
  apply (Iso.FuncCong t (Iso.Refl B1)).
  assumption.
Defined.

(** Functions are closed under finiteness. *)
Theorem func {A B : Type} : T A -> T B -> T (A -> B).
Proof.
intros FA FB.
pose proof (finiteMapped FA FB).
destruct X.
destruct p.
eapply FIso.
eassumption.
apply Iso.Sym.
assumption.
Defined.

(** Any finite type has decidable equality. *)
Theorem eq_dec {A : Type} : T A -> forall a b : A, {a = b} + {a <> b}.
Proof.
intros finite.
induction finite; intros; try (decide equality).
- eapply Iso.eq_dec; eassumption.
Qed.

Fixpoint elementsV {A} (fin : T A) : Vector.t A (card fin) := 
  match fin in T A' return Vector.t A' (card fin) with
  | F0 => Vector.nil Empty_set
  | FS _ n => Vector.cons _ (None) _ (Vector.map Some (elementsV n))
  | FIso _ _ x iso => let xs := elementsV x in
     Vector.map (Iso.to iso) xs
  end.


Theorem fin_dec_subset {A} (fin : T A) {P : A -> Prop}
  : (forall a, {P a} + {~ P a}) -> T (sig P).
Proof.
generalize dependent P. induction fin; intros P decP.
- eapply FIso. apply F0.
  eapply Iso.Trans. apply Iso.iso_true_subset. 
  apply Iso.subsetSelf; firstorder. destruct a.
  destruct b.
- eapply FIso. Focus 2. eapply Iso.Sym.
  eapply Iso.Trans.
  eapply Iso.sig_sigT. eapply Iso.Trans. eapply (Iso.sigmaProp (option_Succ A)).
  eapply Iso.Sym. eapply Iso.Trans. 2: eapply Iso.sig_sigT.
  eapply Iso.Sym. apply Iso.subset_sum_distr.
  destruct (decP None).
  + eapply FIso. Focus 2.
    eapply Iso.PlusCong. apply (Iso.subsetSelf (fun _ => True)); intros; auto.
    destruct a. tauto. destruct p0, q. reflexivity.
    apply proof_irrelevance. apply Iso.Refl.
    eapply FIso. Focus 2. eapply Iso.PlusCong.
    apply Iso.iso_true_subset. apply Iso.Refl.
    eapply FIso. Focus 2. eapply option_Succ.
    apply FS. apply IHfin. intros. apply decP.  
  + eapply FIso. Focus 2.
    eapply Iso.PlusCong. apply (Iso.subsetSelf (fun _ => False)); intros; auto.
    destruct a. tauto. contradiction. destruct b. simpl in p, q. congruence.
    apply Iso.Refl. eapply FIso. Focus 2. eapply Iso.PlusCong.
    apply Iso.iso_false_subset. apply Iso.Refl.
    eapply FIso. Focus 2.
    eapply Iso.Trans. Focus 2. apply Iso.PlusComm.
    apply botNull. apply IHfin. intros; apply decP.
- eapply FIso. apply (IHfin (fun a => P (Iso.to t a))). 
  intros. apply decP. apply Iso.subset with t; firstorder.
  rewrite Iso.to_from. assumption. apply proof_irrelevance.
  apply proof_irrelevance.
Defined.

Require Import Coq.Lists.List.

Import ListNotations.

Fixpoint elements {A} (fin : T A) : list A 
  := match fin in T A'  with
  | F0 => []
  | FS _ n => None :: List.map Some (elements n)
  | FIso _ _ x iso => let xs := elements x in
     List.map (Iso.to iso) xs
  end.

Require Import Coq.Lists.List Coq.Sorting.Permutation.
Require Vector.

Lemma Vto_list_cons : forall A (x : A) n (xs : Vector.t A n),
  Vector.to_list (Vector.cons _ x _ xs)
  = x :: Vector.to_list xs.
Proof.
intros. reflexivity.
Qed.

Lemma Vto_list_map : forall A B n (xs : Vector.t A n) (f : A -> B),
  Vector.to_list (Vector.map f xs) = List.map f (Vector.to_list xs).
Proof.
intros. induction xs; auto.
rewrite Vto_list_cons. simpl. 
rewrite <- IHxs. reflexivity.
Qed.

Lemma injective_NoDup : forall A B xs (f : A -> B),
  (forall x y, f x = f y -> x = y) -> NoDup xs -> NoDup (map f xs).
Proof.
intros. induction xs; simpl.
- constructor.
- inversion H0; clear H0; subst.
  constructor. unfold not; intros contra.
  rewrite in_map_iff in contra.
  destruct contra as (x & fxa & inxxs).
  apply H in fxa. subst.
  contradiction.
  apply IHxs. assumption.
Qed.

Lemma iso_to_NoDup {A B : Type} (t : Iso.T A B)
  (xs : list A)
  (H : NoDup xs)
  : NoDup (map (Iso.to t) xs).
Proof.
apply injective_NoDup. intros. 
rewrite <- (Iso.from_to t x), <- (Iso.from_to t y).
rewrite H0. reflexivity.
assumption.
Qed.

Lemma iso_from_NoDup {A B : Type} (t : Iso.T A B)
  (xs : list B)
  (H : NoDup xs)
  : NoDup (map (Iso.from t) xs).
Proof.
apply (iso_to_NoDup (Iso.Sym t) xs H).
Qed.


Lemma elements_NoDup : forall A (x : T A),
  NoDup (elements x).
Proof.
intros. induction x; simpl; intros.
- constructor.
- constructor. unfold not. intros contra. 
  apply in_map_iff in contra.
  destruct contra as (x0 & contra & _).
  congruence. 
  apply injective_NoDup. intros; congruence.
  unfold elements in IHx.
  apply IHx.
- apply iso_to_NoDup. assumption.
Qed.

Lemma elements_Full : forall A (x : T A) (a : A),
  In a (elements x).
Proof.
intros. induction x.
- contradiction.
- destruct a.
  + right. apply in_map. apply IHx.
  + left. reflexivity.
- simpl. rewrite <- (Iso.to_from t a). apply in_map.
  apply IHx.
Qed.

Lemma elements_Permutation : forall A (x1 x2 : T A),
  Permutation (elements x1) (elements x2).
Proof.
intros. apply NoDup_Permutation; try apply elements_NoDup.
intros; split; intros; apply elements_Full.
Qed.

(* An alternative characterization of finite types *)
Record T' {A : Type} : Type := FI
  { Tcard : nat
  ; Tiso : Iso.T A (Fin Tcard)
  }.

Arguments T' : clear implicits.

Definition toT' {A} (fin : T A) : T' A
  := FI _ (card fin) (Iso.Trans (iso fin) (finIso _)).

Definition fromT' {A} (fn : T' A) : T A.
Proof.
unshelve econstructor.
2: exact (fin (Tcard fn)). apply Iso.Sym. apply fn.
Defined.

Class TC (A : Type) := {TCfin : T' A}.

Fixpoint elements_Fin (n : nat) : list (Fin n) := match n with
  | 0 => []
  | S n' => None :: List.map Some (elements_Fin n')
  end.

Definition elements' {A} (fin : T' A) : list A :=
  List.map (Iso.from (Tiso fin)) (elements_Fin (Tcard fin)).


Lemma elements_Fin_NoDup (n : nat) :
  NoDup (elements_Fin n).
Proof.
intros. induction n; simpl; intros. 
- constructor.
- constructor. unfold not. intros contra. 
  apply in_map_iff in contra.
  destruct contra as (x0 & contra & _).
  congruence. 
  apply injective_NoDup. intros; congruence.
  assumption.
Qed.

Lemma elements_Fin_Full (n : nat) (x : Fin n) :
  In x (elements_Fin n).
Proof.
intros. induction n.
- contradiction.
- destruct x.
  + right. apply in_map. apply IHn.
  + left. reflexivity.
Qed.

Lemma elements'_NoDup : forall A (x : T' A),
  NoDup (elements' x).
Proof.
intros. induction x; simpl.
unfold elements'. apply iso_from_NoDup.
apply elements_Fin_NoDup.
Qed.

Lemma elements'_Full : forall A (x : T' A) (a : A),
  In a (elements' x).
Proof.
intros. induction x.
unfold elements'.
rewrite <- (Iso.from_to Tiso0 a). apply in_map.
simpl. apply elements_Fin_Full.
Qed.

Lemma elements'_Permutation : forall A (x1 x2 : T' A),
  Permutation (elements' x1) (elements' x2).
Proof.
intros. apply NoDup_Permutation; try apply elements'_NoDup.
intros; split; intros; apply elements'_Full.
Qed.

Lemma elements_Fin_same {n}
  : elements_Fin n = elements (fin n). 
Proof.
induction n.
- simpl. reflexivity.
- simpl. repeat f_equal. assumption.
Qed.

Lemma elements_fromT' {A} (F : T' A)
  : elements' F = elements (fromT' F).
Proof.
unfold fromT'. unfold elements'. rewrite elements_Fin_same.
reflexivity.
Qed.

Lemma elements_elements'_Permutation {A} (F : T A) (F' : T' A)
  : Permutation (elements F) (elements' F').
Proof.
rewrite elements_fromT'.
apply elements_Permutation.
Qed.