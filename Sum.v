Require Import Finite finite_iso
  Coq.Lists.List
  Coq.Sorting.Permutation.
 
Section CommutativeSemiGroup.

Variable R : Type.
Variable zero : R.
Variable plus : R -> R -> R.

Local Infix "+" := plus.

Axiom plus_comm : forall x y : R, x + y = y + x.
Axiom plus_assoc : forall x y z, x + (y + z) = (x + y) + z.

Lemma sum_list_perm_invariant : forall (xs ys : list R),
  Permutation xs ys 
  -> fold_right plus zero xs = fold_right plus zero ys.
Proof.
intros. induction H; simpl.
- reflexivity.
- rewrite IHPermutation; reflexivity.
- rewrite !plus_assoc. rewrite (plus_comm y x). reflexivity.
- etransitivity; eassumption.
Qed.

Fixpoint sum_finite {A} (F : Finite.T A) 
  : (A -> R) -> R := match F with
  | Finite.F0 => fun _ => zero
  | Finite.FS F' => fun f => f None + sum_finite F' (fun x => f (Some x))
  | Finite.FIso F' iso => fun f =>
     sum_finite F' (fun i => f (Iso.to iso i))
  end.

Lemma plus_r : forall x y y', y = y' -> x + y = x + y'.
Proof.
intros. subst. reflexivity.
Qed.

Lemma sum_finite_list_same {A} (F : Finite.T A) (f : A -> R)
  : sum_finite F f = fold_right plus zero
  (List.map f (Finite.elements F)).
Proof.
induction F; simpl; intros.
- reflexivity.
- apply plus_r. rewrite List.map_map. apply IHF.
- rewrite List.map_map. apply IHF. 
Qed.

Lemma sum_finite_well_def {A} (F1 F2 : Finite.T A)
  (f : A -> R)
  : sum_finite F1 f = sum_finite F2 f.
Proof.
rewrite !sum_finite_list_same.
apply sum_list_perm_invariant.
apply Permutation_map.
apply Finite.elements_Permutation.
Qed.

End CommutativeSemiGroup.