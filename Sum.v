  Require Import Finite finite_iso
  Coq.Lists.List
  Coq.Sorting.Permutation.
 
Section CommutativeSemiGroup.

Context {R : Type}.
Variable zero : R.
Variable plus : R -> R -> R.

Local Infix "+" := plus.

Axiom plus_comm : forall x y : R, x + y = y + x.
Axiom plus_assoc : forall x y z, x + (y + z) = (x + y) + z.

Definition sum_list : list R -> R := fold_right plus zero.

Lemma sum_list_perm_invariant : forall (xs ys : list R),
  Permutation xs ys 
  -> sum_list xs = sum_list ys.
Proof.
intros. induction H; simpl.
- reflexivity.
- rewrite IHPermutation; reflexivity.
- rewrite !plus_assoc. rewrite (plus_comm y x). reflexivity.
- etransitivity; eassumption.
Qed.

Axiom plus_zero_l : forall x, zero + x = x.

Lemma plus_zero_r : forall x, x + zero = x.
Proof.
intros x. rewrite plus_comm. apply plus_zero_l.
Qed.

Lemma fold_right_sum_list (xs : list R) (c : R)
  : fold_right plus c xs = c + sum_list xs.
Proof.
induction xs; simpl. 
- symmetry. apply plus_zero_r.
- rewrite IHxs. rewrite !plus_assoc.
  f_equal. apply plus_comm.
Qed.

Lemma sum_list_app (xs ys : list R)
  : sum_list (xs ++ ys) = sum_list xs + sum_list ys.
Proof.
unfold sum_list.
rewrite fold_right_app.
rewrite fold_right_sum_list.
apply plus_comm.
Qed.

Fixpoint sum_Fin {n : nat} : (Finite.Fin n -> R) -> R := match n with
  | 0 => fun f => zero
  | S n' => fun f => f None + sum_Fin (fun x => f (Some x))
  end.

Fixpoint last_Fin (k : nat) : Finite.Fin (S k) := match k with
  | 0 => None
  | S k' => Some (last_Fin k')
  end.

Fixpoint lift_Fin {n : nat} : Fin n -> Fin (S n) := match n with
  | 0 => Empty_set_rect _
  | S n' => fun x => match x with
    | None => None
    | Some x' => Some (lift_Fin x')
    end
  end.

Lemma sum_Fin_last {n : nat} (f : Finite.Fin (S n) -> R) :
  sum_Fin f = sum_Fin (fun x : Finite.Fin n => f (lift_Fin x)) + f (last_Fin n).
Proof.
induction n; simpl.
- rewrite plus_zero_r. rewrite plus_zero_l. reflexivity.
- specialize (IHn (fun x => f (Some x))).
  simpl in IHn. rewrite <- !plus_assoc. f_equal. 
  apply IHn.
Qed.

Fixpoint sum_finiteT {A} (F : Finite.T A) 
  : (A -> R) -> R := match F with
  | Finite.F0 => fun _ => zero
  | Finite.FS F' => fun f => f None + sum_finiteT F' (fun x => f (Some x))
  | Finite.FIso F' iso => fun f =>
     sum_finiteT F' (fun i => f (Iso.to iso i))
  end.

Definition sum_finiteT' {A} (F : Finite.T' A)
  (f : A -> R) : R := sum_Fin (fun x => f (Iso.from (Tiso F) x)).

Lemma plus_r : forall x y y', y = y' -> x + y = x + y'.
Proof.
intros. subst. reflexivity.
Qed.

Lemma sum_finiteT_list_same {A} (F : Finite.T A) (f : A -> R)
  : sum_finiteT F f = sum_list (List.map f (Finite.elements F)).
Proof.
induction F; simpl; intros.
- reflexivity.
- apply plus_r. rewrite List.map_map. apply IHF.
- rewrite List.map_map. apply IHF. 
Qed.

Lemma sum_Fin_list_same (n : nat) (f : Fin n -> R)
  : sum_Fin f = sum_list (List.map f (elements_Fin n)).
Proof.
induction n; simpl.
- reflexivity.
- apply plus_r. rewrite List.map_map.
  apply IHn.
Qed.

Lemma sum_list_concat (xs : list (list R))
  : sum_list (concat xs)
  = sum_list (List.map (sum_list) xs).
Proof.
induction xs; simpl.
- reflexivity.
- rewrite sum_list_app. f_equal.
  apply IHxs.
Qed.

Lemma sum_list_dep {A B} (xs : list A) (f : A -> list B) (v : A * B -> R)
  : sum_list (map (fun a => sum_list (map (fun b => v (a, b)) (f a))) xs)
  = sum_list (flat_map (fun a => map (fun b => v (a, b)) (f a)) xs).
Proof.
induction xs; simpl.
- reflexivity.
- rewrite IHxs. rewrite sum_list_app. reflexivity.
Qed.

Lemma sum_finiteT'_list_same {A} (F : Finite.T' A) (f : A -> R)
  : sum_finiteT' F f = sum_list (List.map f (Finite.elements' F)).
Proof.
unfold elements', sum_finiteT'.
rewrite List.map_map.
apply sum_Fin_list_same.
Qed.

Lemma sum_finiteT_well_def {A} (F1 F2 : Finite.T A)
  (f : A -> R)
  : sum_finiteT F1 f = sum_finiteT F2 f.
Proof.
rewrite !sum_finiteT_list_same.
apply sum_list_perm_invariant.
apply Permutation_map.
apply Finite.elements_Permutation.
Qed.

Lemma sum_finiteT'_well_def {A} (F1 F2 : Finite.T' A)
  (f : A -> R)
  : sum_finiteT' F1 f = sum_finiteT' F2 f.
Proof.
rewrite !sum_finiteT'_list_same.
apply sum_list_perm_invariant.
apply Permutation_map.
apply Finite.elements'_Permutation.
Qed.

Lemma sum_finiteT_extensional {A} {F : Finite.T A}
  (f f' : A -> R)
  (H : forall a, f a = f' a)
  : sum_finiteT F f = sum_finiteT F f'.
Proof.
induction F; simpl.
- reflexivity.
- f_equal; auto.
- auto.
Qed.

Lemma sum_Fin_extensional {n : nat}
  (f f' : Fin n -> R)
  (H : forall a, f a = f' a)
  : sum_Fin f = sum_Fin f'.
Proof.
induction n; simpl.
- reflexivity.
- f_equal; auto.
Qed.

Lemma sum_finiteT'_extensional {A} {F : Finite.T' A}
  (f f' : A -> R)
  (H : forall a, f a = f' a)
  : sum_finiteT' F f = sum_finiteT' F f'.
Proof.
induction F. apply sum_Fin_extensional.
simpl. intros. apply H.
Qed.

Lemma sum_Fin_Sum {n k} (f : Fin (n + k) -> R)
  : sum_Fin f = sum_Fin (fun i => f (Iso.to finPlus1 (inl i)))
              + sum_Fin (fun i => f (Iso.to finPlus1 (inr i))).
Proof.
induction n; simpl.
- rewrite plus_zero_l. reflexivity.
- rewrite <- plus_assoc. f_equal.
  apply IHn.
Qed.

Lemma sum_Fin_Prod {n k} (f : Fin (n * k) -> R)
  : sum_Fin f = sum_Fin (fun i => sum_Fin (fun j => f (Iso.to finMult1 (i, j)))).
Proof.
induction n; simpl.
- reflexivity. 
- induction k; simpl.
  + rewrite plus_zero_l. rewrite IHn. simpl. reflexivity. 
  + rewrite <- plus_assoc. f_equal.
    rewrite sum_Fin_Sum. f_equal.
    rewrite IHn. reflexivity.
Qed.

Definition T'_Prod {A B} (FA : Finite.T' A) (FB : Finite.T' B)
  : Finite.T' (A * B).
Proof.
exists (Tcard FA * Tcard FB).
eapply Iso.Trans. eapply Iso.TimesCong.
apply FA. apply FB. apply finMult1.
Defined.

Lemma sum_FiniteT'_Prod {A B} {FA : Finite.T' A} {FB : Finite.T' B}
  (f : A * B -> R)
  : sum_finiteT' (T'_Prod FA FB) f
  = sum_finiteT' FA (fun a => sum_finiteT' FB (fun b => f (a, b))).
Proof.
unfold sum_finiteT'. simpl.
rewrite sum_Fin_Prod. apply sum_Fin_extensional. 
intros i. apply sum_Fin_extensional. intros j.
simpl. rewrite Iso.from_to. reflexivity.
Qed.

End CommutativeSemiGroup.