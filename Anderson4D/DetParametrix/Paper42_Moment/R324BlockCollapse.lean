import Anderson4D.DetParametrix.Core.ReductionEndpointRigidity

/-!
# Fixed-signature block collapse for R-324

Paper §4.2 first identifies a contraction triple `(κ⁺, κ⁻, π)` with a
full pairing of the doubled carrier.  It then fixes the within-half extraction
signature and sums all primitive pairings in each extracted block before
applying Proposition 4.1.

This file starts the exact finite reindexing needed for that argument.  The
first structural fact is that the doubled pairing remembers the entire
contraction triple: no multiplicity is introduced when the contraction sum is
viewed as a sum over full doubled pairings.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Separating the two halves of a moment signature -/

@[simp]
theorem leftMomentIndex_mem_endpointImageUnion_iff
    {m : ℕ} (A B : Finset (Fin m)) (i : Fin m) :
    leftMomentIndex i ∈
        A.image leftMomentIndex ∪
          B.image rightMomentIndex ↔
      i ∈ A := by
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
      exact (leftMomentIndex_injective hji) ▸ hj
    · obtain ⟨j, _hj, hji⟩ := Finset.mem_image.mp hi
      have hval := congrArg Fin.val hji
      simp only [leftMomentIndex, rightMomentIndex] at hval
      have hjlt := j.isLt
      omega
  · intro hi
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

@[simp]
theorem rightMomentIndex_mem_endpointImageUnion_iff
    {m : ℕ} (A B : Finset (Fin m)) (j : Fin m) :
    rightMomentIndex j ∈
        A.image leftMomentIndex ∪
          B.image rightMomentIndex ↔
      j ∈ B := by
  constructor
  · intro hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨i, _hi, hij⟩ := Finset.mem_image.mp hj
      have hval := congrArg Fin.val hij
      simp only [leftMomentIndex, rightMomentIndex] at hval
      have hilt := i.isLt
      omega
    · obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
      exact rightMomentIndex_injective hij ▸ hi
  · intro hj
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

/-- Equality of doubled moment signatures recovers the two ordinary
endpoint signatures separately. -/
theorem reductionEndpointSignatures_eq_of_momentContractionSignature_eq
    {m : ℕ} (e e' : MomentContraction m)
    (hsignature :
      momentContractionSignature e =
        momentContractionSignature e') :
    reductionEndpointSignature e.1 =
        reductionEndpointSignature e'.1 ∧
      reductionEndpointSignature e.2.1 =
        reductionEndpointSignature e'.2.1 := by
  have hleftUnion := congrArg Prod.fst hsignature
  have hrightUnion := congrArg Prod.snd hsignature
  have hleftUnion' :
      (leftEndpoints e.1).image leftMomentIndex ∪
          (leftEndpoints e.2.1).image rightMomentIndex =
        (leftEndpoints e'.1).image leftMomentIndex ∪
          (leftEndpoints e'.2.1).image rightMomentIndex := by
    simpa [momentContractionSignature,
      momentWithinHalfEndpointSignature] using hleftUnion
  have hrightUnion' :
      (rightEndpoints e.1).image leftMomentIndex ∪
          (rightEndpoints e.2.1).image rightMomentIndex =
        (rightEndpoints e'.1).image leftMomentIndex ∪
          (rightEndpoints e'.2.1).image rightMomentIndex := by
    simpa [momentContractionSignature,
      momentWithinHalfEndpointSignature] using hrightUnion
  have hleftP :
      leftEndpoints e.1 = leftEndpoints e'.1 := by
    ext i
    rw [←
      leftMomentIndex_mem_endpointImageUnion_iff
        (leftEndpoints e.1) (leftEndpoints e.2.1) i]
    rw [hleftUnion']
    exact
      leftMomentIndex_mem_endpointImageUnion_iff
        (leftEndpoints e'.1) (leftEndpoints e'.2.1) i
  have hleftM :
      leftEndpoints e.2.1 = leftEndpoints e'.2.1 := by
    ext i
    rw [←
      rightMomentIndex_mem_endpointImageUnion_iff
        (leftEndpoints e.1) (leftEndpoints e.2.1) i]
    rw [hleftUnion']
    exact
      rightMomentIndex_mem_endpointImageUnion_iff
        (leftEndpoints e'.1) (leftEndpoints e'.2.1) i
  have hrightP :
      rightEndpoints e.1 = rightEndpoints e'.1 := by
    ext i
    rw [←
      leftMomentIndex_mem_endpointImageUnion_iff
        (rightEndpoints e.1) (rightEndpoints e.2.1) i]
    rw [hrightUnion']
    exact
      leftMomentIndex_mem_endpointImageUnion_iff
        (rightEndpoints e'.1) (rightEndpoints e'.2.1) i
  have hrightM :
      rightEndpoints e.2.1 = rightEndpoints e'.2.1 := by
    ext i
    rw [←
      rightMomentIndex_mem_endpointImageUnion_iff
        (rightEndpoints e.1) (rightEndpoints e.2.1) i]
    rw [hrightUnion']
    exact
      rightMomentIndex_mem_endpointImageUnion_iff
        (rightEndpoints e'.1) (rightEndpoints e'.2.1) i
  constructor
  · exact Prod.ext hleftP hrightP
  · exact Prod.ext hleftM hrightM

/-- The fixed moment signature makes both signed Green skeletons common
across its whole contraction fibre. -/
theorem renormalizedGreenSkeletons_eq_of_momentContractionSignature_eq
    {m : ℕ} (e e' : MomentContraction m)
    (hsignature :
      momentContractionSignature e =
        momentContractionSignature e') :
    renormalizedGreenSkeleton e.1 =
        renormalizedGreenSkeleton e'.1 ∧
      renormalizedGreenSkeleton e.2.1 =
        renormalizedGreenSkeleton e'.2.1 := by
  obtain ⟨hp, hm⟩ :=
    reductionEndpointSignatures_eq_of_momentContractionSignature_eq
      e e' hsignature
  exact
    ⟨renormalizedGreenSkeleton_eq_of_reductionEndpointSignature_eq
        e.1 e'.1 hp,
      renormalizedGreenSkeleton_eq_of_reductionEndpointSignature_eq
        e.2.1 e'.2.1 hm⟩

/-! ## Splitting a full pairing on the two copies -/

/-- Retain pairs contained in the left copy and turn every cross-copy
endpoint into a single. -/
def momentLeftRestrictionMap
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m)) :
    Fin m → Fin m := fun i =>
  match κ (Sum.inl i) with
  | Sum.inl j => j
  | Sum.inr _ => i

theorem momentLeftRestrictionMap_involutive
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m)) :
    Function.Involutive (momentLeftRestrictionMap κ) := by
  intro i
  generalize hκi : κ (Sum.inl i) = u
  rcases u with j | j
  · have hκj : κ (Sum.inl j) = Sum.inl i := by
      rw [← hκi, κ.apply_apply]
    simp [momentLeftRestrictionMap, hκi, hκj]
  · simp [momentLeftRestrictionMap, hκi]

/-- The partial pairing induced inside the left copy. -/
def momentLeftRestriction
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m)) :
    PartialPairing (Fin m) where
  toFun := momentLeftRestrictionMap κ
  involutive := momentLeftRestrictionMap_involutive κ

/-- Retain pairs contained in the right copy and turn every cross-copy
endpoint into a single. -/
def momentRightRestrictionMap
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m)) :
    Fin m → Fin m := fun j =>
  match κ (Sum.inr j) with
  | Sum.inl _ => j
  | Sum.inr i => i

theorem momentRightRestrictionMap_involutive
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m)) :
    Function.Involutive (momentRightRestrictionMap κ) := by
  intro j
  generalize hκj : κ (Sum.inr j) = u
  rcases u with i | i
  · simp [momentRightRestrictionMap, hκj]
  · have hκi : κ (Sum.inr i) = Sum.inr j := by
      rw [← hκj, κ.apply_apply]
    simp [momentRightRestrictionMap, hκj, hκi]

/-- The partial pairing induced inside the right copy. -/
def momentRightRestriction
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m)) :
    PartialPairing (Fin m) where
  toFun := momentRightRestrictionMap κ
  involutive := momentRightRestrictionMap_involutive κ

@[simp]
theorem momentLeftRestriction_apply_of_left
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    {i j : Fin m} (h : κ (Sum.inl i) = Sum.inl j) :
    momentLeftRestriction κ i = j := by
  simp [momentLeftRestriction, momentLeftRestrictionMap, h]

@[simp]
theorem momentLeftRestriction_apply_of_right
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    {i j : Fin m} (h : κ (Sum.inl i) = Sum.inr j) :
    momentLeftRestriction κ i = i := by
  simp [momentLeftRestriction, momentLeftRestrictionMap, h]

@[simp]
theorem momentRightRestriction_apply_of_left
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    {i j : Fin m} (h : κ (Sum.inr j) = Sum.inl i) :
    momentRightRestriction κ j = j := by
  simp [momentRightRestriction, momentRightRestrictionMap, h]

@[simp]
theorem momentRightRestriction_apply_of_right
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    {i j : Fin m} (h : κ (Sum.inr j) = Sum.inr i) :
    momentRightRestriction κ j = i := by
  simp [momentRightRestriction, momentRightRestrictionMap, h]

/-- For a full pairing, a left index is a single of the within-left
restriction exactly when it is paired across the cut. -/
theorem mem_momentLeftRestriction_singles_iff
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    (hfull : κ.IsFull) (i : Fin m) :
    i ∈ (momentLeftRestriction κ).singles ↔
      ∃ j : Fin m, κ (Sum.inl i) = Sum.inr j := by
  rw [PartialPairing.mem_singles]
  constructor
  · intro hi
    generalize hκi : κ (Sum.inl i) = u
    rcases u with j | j
    · have hji : j = i := by
        simpa [momentLeftRestriction,
          momentLeftRestrictionMap, hκi] using hi
      subst j
      exact False.elim (hfull (Sum.inl i) hκi)
    · exact ⟨j, rfl⟩
  · rintro ⟨j, hκi⟩
    exact momentLeftRestriction_apply_of_right κ hκi

/-- Right-copy counterpart of
`mem_momentLeftRestriction_singles_iff`. -/
theorem mem_momentRightRestriction_singles_iff
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    (hfull : κ.IsFull) (j : Fin m) :
    j ∈ (momentRightRestriction κ).singles ↔
      ∃ i : Fin m, κ (Sum.inr j) = Sum.inl i := by
  rw [PartialPairing.mem_singles]
  constructor
  · intro hj
    generalize hκj : κ (Sum.inr j) = u
    rcases u with i | i
    · exact ⟨i, rfl⟩
    · have hij : i = j := by
        simpa [momentRightRestriction,
          momentRightRestrictionMap, hκj] using hj
      subst i
      exact False.elim (hfull (Sum.inr j) hκj)
  · rintro ⟨i, hκj⟩
    exact momentRightRestriction_apply_of_left κ hκj

/-- The right endpoint paired with a left single in a full sum pairing. -/
def momentCrossRight
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    (hfull : κ.IsFull)
    (i : (momentLeftRestriction κ).singles) : Fin m :=
  Classical.choose
    ((mem_momentLeftRestriction_singles_iff
      κ hfull i.1).mp i.2)

theorem momentCrossRight_spec
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    (hfull : κ.IsFull)
    (i : (momentLeftRestriction κ).singles) :
    κ (Sum.inl i.1) =
      Sum.inr (momentCrossRight κ hfull i) :=
  Classical.choose_spec
    ((mem_momentLeftRestriction_singles_iff
      κ hfull i.1).mp i.2)

theorem momentCrossRight_mem_singles
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    (hfull : κ.IsFull)
    (i : (momentLeftRestriction κ).singles) :
    momentCrossRight κ hfull i ∈
      (momentRightRestriction κ).singles := by
  apply (mem_momentRightRestriction_singles_iff
    κ hfull _).mpr
  refine ⟨i.1, ?_⟩
  rw [← momentCrossRight_spec κ hfull i,
    κ.apply_apply]

/-- The left endpoint paired with a right single in a full sum pairing. -/
def momentCrossLeft
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    (hfull : κ.IsFull)
    (j : (momentRightRestriction κ).singles) : Fin m :=
  Classical.choose
    ((mem_momentRightRestriction_singles_iff
      κ hfull j.1).mp j.2)

theorem momentCrossLeft_spec
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    (hfull : κ.IsFull)
    (j : (momentRightRestriction κ).singles) :
    κ (Sum.inr j.1) =
      Sum.inl (momentCrossLeft κ hfull j) :=
  Classical.choose_spec
    ((mem_momentRightRestriction_singles_iff
      κ hfull j.1).mp j.2)

theorem momentCrossLeft_mem_singles
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    (hfull : κ.IsFull)
    (j : (momentRightRestriction κ).singles) :
    momentCrossLeft κ hfull j ∈
      (momentLeftRestriction κ).singles := by
  apply (mem_momentLeftRestriction_singles_iff
    κ hfull _).mpr
  refine ⟨j.1, ?_⟩
  rw [← momentCrossLeft_spec κ hfull j,
    κ.apply_apply]

/-- The cross-copy pairs of a full sum pairing form an equivalence between
the singles of its two within-copy restrictions. -/
def momentCrossEquiv
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    (hfull : κ.IsFull) :
    (momentLeftRestriction κ).singles ≃
      (momentRightRestriction κ).singles where
  toFun i :=
    ⟨momentCrossRight κ hfull i,
      momentCrossRight_mem_singles κ hfull i⟩
  invFun j :=
    ⟨momentCrossLeft κ hfull j,
      momentCrossLeft_mem_singles κ hfull j⟩
  left_inv i := by
    apply Subtype.ext
    have hright :=
      momentCrossRight_spec κ hfull i
    have hleft :=
      momentCrossLeft_spec κ hfull
        ⟨momentCrossRight κ hfull i,
          momentCrossRight_mem_singles κ hfull i⟩
    have hinv :
        κ (Sum.inr (momentCrossRight κ hfull i)) =
          Sum.inl i.1 := by
      rw [← hright, κ.apply_apply]
    exact Sum.inl.inj (hleft.symm.trans hinv)
  right_inv j := by
    apply Subtype.ext
    have hleft :=
      momentCrossLeft_spec κ hfull j
    have hright :=
      momentCrossRight_spec κ hfull
        ⟨momentCrossLeft κ hfull j,
          momentCrossLeft_mem_singles κ hfull j⟩
    have hinv :
        κ (Sum.inl (momentCrossLeft κ hfull j)) =
          Sum.inr j.1 := by
      rw [← hleft, κ.apply_apply]
    exact Sum.inr.inj (hright.symm.trans hinv)

/-- Splitting a full sum pairing into its two within-copy restrictions and
its cross equivalence, then recombining, returns the original pairing. -/
theorem momentCombinedSumPairing_restrictions
    {m : ℕ} (κ : PartialPairing (Fin m ⊕ Fin m))
    (hfull : κ.IsFull) :
    momentCombinedSumPairing
        (momentLeftRestriction κ)
        (momentRightRestriction κ)
        (momentCrossEquiv κ hfull) =
      κ := by
  apply PartialPairing.ext
  intro x
  change
    momentCombinedSumMap
        (momentLeftRestriction κ)
        (momentRightRestriction κ)
        (momentCrossEquiv κ hfull) x =
      κ x
  rcases x with i | j
  · generalize hκi : κ (Sum.inl i) = u
    rcases u with i' | j'
    · have hiNot :
          i ∉ (momentLeftRestriction κ).singles := by
        rw [PartialPairing.mem_singles]
        intro hi
        have hii' :
            i' = i := by
          exact
            (momentLeftRestriction_apply_of_left
              κ hκi).symm.trans hi
        subst i'
        exact hfull (Sum.inl i) hκi
      change
        (if hi : i ∈ (momentLeftRestriction κ).singles then
          Sum.inr ((momentCrossEquiv κ hfull) ⟨i, hi⟩).1
        else
          Sum.inl (momentLeftRestriction κ i)) =
            Sum.inl i'
      rw [dif_neg hiNot,
        momentLeftRestriction_apply_of_left κ hκi]
    · have hi :
          i ∈ (momentLeftRestriction κ).singles :=
        (mem_momentLeftRestriction_singles_iff
          κ hfull i).mpr ⟨j', hκi⟩
      change
        (if hi' : i ∈ (momentLeftRestriction κ).singles then
          Sum.inr ((momentCrossEquiv κ hfull) ⟨i, hi'⟩).1
        else
          Sum.inl (momentLeftRestriction κ i)) =
            Sum.inr j'
      rw [dif_pos hi]
      change
        Sum.inr (momentCrossRight κ hfull ⟨i, hi⟩) =
          Sum.inr j'
      exact
        (momentCrossRight_spec κ hfull ⟨i, hi⟩).symm.trans
          hκi
  · generalize hκj : κ (Sum.inr j) = u
    rcases u with i' | j'
    · have hj :
          j ∈ (momentRightRestriction κ).singles :=
        (mem_momentRightRestriction_singles_iff
          κ hfull j).mpr ⟨i', hκj⟩
      change
        (if hj' : j ∈ (momentRightRestriction κ).singles then
          Sum.inl ((momentCrossEquiv κ hfull).symm ⟨j, hj'⟩).1
        else
          Sum.inr (momentRightRestriction κ j)) =
            Sum.inl i'
      rw [dif_pos hj]
      change
        Sum.inl (momentCrossLeft κ hfull ⟨j, hj⟩) =
          Sum.inl i'
      exact
        (momentCrossLeft_spec κ hfull ⟨j, hj⟩).symm.trans
          hκj
    · have hjNot :
          j ∉ (momentRightRestriction κ).singles := by
        rw [PartialPairing.mem_singles]
        intro hj
        have hjj' :
            j' = j := by
          exact
            (momentRightRestriction_apply_of_right
              κ hκj).symm.trans hj
        subst j'
        exact hfull (Sum.inr j) hκj
      change
        (if hj : j ∈ (momentRightRestriction κ).singles then
          Sum.inl ((momentCrossEquiv κ hfull).symm ⟨j, hj⟩).1
        else
          Sum.inr (momentRightRestriction κ j)) =
            Sum.inr j'
      rw [dif_neg hjNot,
        momentRightRestriction_apply_of_right κ hκj]

/-- The full doubled pairing determines both within-copy partial pairings. -/
theorem momentCombinedPairing_injective_pairings
    {m : ℕ}
    {κp κm κp' κm' : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {π' : κp'.singles ≃ κm'.singles}
    (hcombined :
      momentCombinedPairing κp κm π =
        momentCombinedPairing κp' κm' π') :
    κp = κp' ∧ κm = κm' := by
  constructor
  · apply PartialPairing.ext
    intro i
    by_cases hi : i ∈ κp.singles
    · have hi' : i ∈ κp'.singles := by
        by_contra hi'
        have h :=
          congrArg (fun κ : PartialPairing (Fin (2 * m)) =>
            κ (leftMomentIndex i)) hcombined
        rw [momentCombinedPairing_left_single κp κm π i hi,
          momentCombinedPairing_left_pair κp' κm' π' i hi'] at h
        have hsum :
            Sum.inr (π ⟨i, hi⟩).1 =
              Sum.inl (κp' i) := by
          simpa using
            congrArg (momentDoubleFinEquiv m).symm h
        cases hsum
      exact (PartialPairing.mem_singles.mp hi).trans
        (PartialPairing.mem_singles.mp hi').symm
    · have hi' : i ∉ κp'.singles := by
        intro hi'
        have h :=
          congrArg (fun κ : PartialPairing (Fin (2 * m)) =>
            κ (leftMomentIndex i)) hcombined
        rw [momentCombinedPairing_left_pair κp κm π i hi,
          momentCombinedPairing_left_single κp' κm' π' i hi'] at h
        have hsum :
            Sum.inl (κp i) =
              Sum.inr (π' ⟨i, hi'⟩).1 := by
          simpa using
            congrArg (momentDoubleFinEquiv m).symm h
        cases hsum
      have h :=
        congrArg (fun κ : PartialPairing (Fin (2 * m)) =>
          κ (leftMomentIndex i)) hcombined
      rw [momentCombinedPairing_left_pair κp κm π i hi,
        momentCombinedPairing_left_pair κp' κm' π' i hi'] at h
      exact leftMomentIndex_injective h
  · apply PartialPairing.ext
    intro j
    by_cases hj : j ∈ κm.singles
    · have hj' : j ∈ κm'.singles := by
        by_contra hj'
        have h :=
          congrArg (fun κ : PartialPairing (Fin (2 * m)) =>
            κ (rightMomentIndex j)) hcombined
        rw [momentCombinedPairing_right_single κp κm π j hj,
          momentCombinedPairing_right_pair κp' κm' π' j hj'] at h
        have hsum :
            Sum.inl (π.symm ⟨j, hj⟩).1 =
              Sum.inr (κm' j) := by
          simpa using
            congrArg (momentDoubleFinEquiv m).symm h
        cases hsum
      exact (PartialPairing.mem_singles.mp hj).trans
        (PartialPairing.mem_singles.mp hj').symm
    · have hj' : j ∉ κm'.singles := by
        intro hj'
        have h :=
          congrArg (fun κ : PartialPairing (Fin (2 * m)) =>
            κ (rightMomentIndex j)) hcombined
        rw [momentCombinedPairing_right_pair κp κm π j hj,
          momentCombinedPairing_right_single κp' κm' π' j hj'] at h
        have hsum :
            Sum.inr (κm j) =
              Sum.inl (π'.symm ⟨j, hj'⟩).1 := by
          simpa using
            congrArg (momentDoubleFinEquiv m).symm h
        cases hsum
      have h :=
        congrArg (fun κ : PartialPairing (Fin (2 * m)) =>
          κ (rightMomentIndex j)) hcombined
      rw [momentCombinedPairing_right_pair κp κm π j hj,
        momentCombinedPairing_right_pair κp' κm' π' j hj'] at h
      exact rightMomentIndex_injective h

/-- The full doubled pairing determines the cross-single equivalence once
the two within-copy partial pairings have been identified. -/
theorem momentCombinedPairing_injective_crossEquiv
    {m : ℕ}
    {κp κm : PartialPairing (Fin m)}
    {π π' : κp.singles ≃ κm.singles}
    (hcombined :
      momentCombinedPairing κp κm π =
        momentCombinedPairing κp κm π') :
    π = π' := by
  apply Equiv.ext
  intro i
  apply Subtype.ext
  have h :=
    congrArg (fun κ : PartialPairing (Fin (2 * m)) =>
      κ (leftMomentIndex i.1)) hcombined
  rw [momentCombinedPairing_left_single κp κm π i.1 i.2,
    momentCombinedPairing_left_single κp κm π' i.1 i.2] at h
  exact rightMomentIndex_injective h

/-- The map from contraction entities to full doubled pairings is injective.
Consequently the passage from (4.18) to a full-pairing sum carries no hidden
multiplicity. -/
theorem momentCombinedPairing_injective
    {m : ℕ} :
    Function.Injective
      (fun e : MomentContraction m =>
        momentCombinedPairing e.1 e.2.1 e.2.2) := by
  intro e e' hcombined
  rcases e with ⟨κp, κm, π⟩
  rcases e' with ⟨κp', κm', π'⟩
  obtain ⟨rfl, rfl⟩ :=
    momentCombinedPairing_injective_pairings hcombined
  have hπ : π = π' :=
    momentCombinedPairing_injective_crossEquiv hcombined
  subst hπ
  rfl

/-! ## Equivalence with full doubled pairings -/

/-- Transport a doubled pairing back to the disjoint-union carrier. -/
def momentSplitSumPairing
    {m : ℕ} (κ : PartialPairing (Fin (2 * m))) :
    PartialPairing (Fin m ⊕ Fin m) :=
  PartialPairing.congr (momentDoubleFinEquiv m).symm κ

theorem momentSplitSumPairing_isFull
    {m : ℕ} {κ : PartialPairing (Fin (2 * m))}
    (hfull : κ.IsFull) :
    (momentSplitSumPairing κ).IsFull :=
  hfull.congr (momentDoubleFinEquiv m).symm

/-- The contraction triple canonically recovered from a full doubled
pairing. -/
def momentContractionOfFull
    {m : ℕ} (κ : PartialPairing (Fin (2 * m)))
    (hfull : κ.IsFull) :
    MomentContraction m :=
  ⟨momentLeftRestriction (momentSplitSumPairing κ),
    momentRightRestriction (momentSplitSumPairing κ),
    momentCrossEquiv (momentSplitSumPairing κ)
      (momentSplitSumPairing_isFull hfull)⟩

/-- Recombining the canonical contraction triple of a full doubled pairing
returns that pairing. -/
theorem momentCombinedPairing_momentContractionOfFull
    {m : ℕ} (κ : PartialPairing (Fin (2 * m)))
    (hfull : κ.IsFull) :
    momentCombinedPairing
        (momentContractionOfFull κ hfull).1
        (momentContractionOfFull κ hfull).2.1
        (momentContractionOfFull κ hfull).2.2 =
      κ := by
  unfold momentContractionOfFull momentCombinedPairing
  rw [momentCombinedSumPairing_restrictions]
  exact
    (PartialPairing.congr (momentDoubleFinEquiv m)).apply_symm_apply κ

/-- Every full pairing of the doubled carrier arises from a unique
contraction triple. -/
theorem momentCombinedPairing_surjective_full
    {m : ℕ} (κ : PartialPairing (Fin (2 * m)))
    (hfull : κ.IsFull) :
    ∃ e : MomentContraction m,
      momentCombinedPairing e.1 e.2.1 e.2.2 = κ :=
  ⟨momentContractionOfFull κ hfull,
    momentCombinedPairing_momentContractionOfFull κ hfull⟩

/-- Exact equivalence used to replace the contraction sum in (4.18) by the
sum over full pairings on the doubled carrier. -/
def momentContractionEquivFullPairing (m : ℕ) :
    MomentContraction m ≃
      {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} where
  toFun e :=
    ⟨momentCombinedPairing e.1 e.2.1 e.2.2,
      momentCombinedPairing_isFull e.1 e.2.1 e.2.2⟩
  invFun κ :=
    momentContractionOfFull κ.1 κ.2
  left_inv e := by
    apply momentCombinedPairing_injective
    exact
      momentCombinedPairing_momentContractionOfFull
        (momentCombinedPairing e.1 e.2.1 e.2.2)
        (momentCombinedPairing_isFull e.1 e.2.1 e.2.2)
  right_inv κ := by
    apply Subtype.ext
    exact
      momentCombinedPairing_momentContractionOfFull κ.1 κ.2

/-! ## Fixed-signature fibres on full pairings -/

/-- The within-half extraction signature, now regarded as data carried by a
full doubled pairing via the canonical inverse contraction. -/
def momentFullPairingSignature
    {m : ℕ}
    (κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull}) :
    Finset (Fin (2 * m)) × Finset (Fin (2 * m)) :=
  momentContractionSignature
    ((momentContractionEquivFullPairing m).symm κ)

@[simp]
theorem momentFullPairingSignature_momentCombinedPairing
    {m : ℕ} (e : MomentContraction m) :
    momentFullPairingSignature
        ⟨momentCombinedPairing e.1 e.2.1 e.2.2,
          momentCombinedPairing_isFull e.1 e.2.1 e.2.2⟩ =
      momentContractionSignature e := by
  unfold momentFullPairingSignature
  change
    momentContractionSignature
        ((momentContractionEquivFullPairing m).symm
          (momentContractionEquivFullPairing m e)) =
      momentContractionSignature e
  rw [Equiv.symm_apply_apply]

/-- Exact equivalence between a fixed contraction-signature fibre and the
corresponding fibre of full doubled pairings.  This is the precise finite
domain on which the primitive block sums must subsequently be factorized. -/
def momentContractionFiberEquivFullPairingFiber
    (m : ℕ)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    {e : MomentContraction m // e ∈ momentContractionFiber m s} ≃
      {κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} //
        momentFullPairingSignature κ = s} :=
  (momentContractionEquivFullPairing m).subtypeEquiv fun e => by
    rw [mem_momentContractionFiber]
    exact
      (momentFullPairingSignature_momentCombinedPairing e).symm ▸
        Iff.rfl

/-- The finite set of full doubled pairings having one fixed within-half
extraction signature. -/
def momentFullPairingFiber
    (m : ℕ)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    Finset {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} :=
  Finset.univ.filter fun κ =>
    momentFullPairingSignature κ = s

@[simp]
theorem mem_momentFullPairingFiber
    {m : ℕ}
    {s : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    {κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull}} :
    κ ∈ momentFullPairingFiber m s ↔
      momentFullPairingSignature κ = s := by
  simp [momentFullPairingFiber]

/-- A signature occurs in the finite signature set exactly when its
contraction fibre is nonempty. -/
theorem momentContractionFiber_nonempty_iff_mem_signatures
    {m : ℕ}
    {s : Finset (Fin (2 * m)) × Finset (Fin (2 * m))} :
    (momentContractionFiber m s).Nonempty ↔
      s ∈ momentContractionSignatures m := by
  constructor
  · rintro ⟨e, he⟩
    exact Finset.mem_image.mpr
      ⟨e, Finset.mem_univ e,
        mem_momentContractionFiber.mp he⟩
  · intro hs
    obtain ⟨e, _he, hes⟩ := Finset.mem_image.mp hs
    exact ⟨e, mem_momentContractionFiber.mpr hes⟩

/-- Two full doubled pairings in one moment-signature fibre have the same
left and right renormalized Green skeletons after applying the canonical
inverse contraction. -/
theorem renormalizedGreenSkeletons_eq_of_mem_momentFullPairingFiber
    {m : ℕ}
    {s : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    {κ κ' : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull}}
    (hκ : κ ∈ momentFullPairingFiber m s)
    (hκ' : κ' ∈ momentFullPairingFiber m s) :
    let e := (momentContractionEquivFullPairing m).symm κ
    let e' := (momentContractionEquivFullPairing m).symm κ'
    renormalizedGreenSkeleton e.1 =
        renormalizedGreenSkeleton e'.1 ∧
      renormalizedGreenSkeleton e.2.1 =
        renormalizedGreenSkeleton e'.2.1 := by
  let e := (momentContractionEquivFullPairing m).symm κ
  let e' := (momentContractionEquivFullPairing m).symm κ'
  have he :
      momentContractionSignature e = s := by
    exact mem_momentFullPairingFiber.mp hκ
  have he' :
      momentContractionSignature e' = s := by
    exact mem_momentFullPairingFiber.mp hκ'
  exact
    renormalizedGreenSkeletons_eq_of_momentContractionSignature_eq
      e e' (he.trans he'.symm)

/-- The image of the original contraction fibre is exactly the full-pairing
fibre, not merely a subset of it. -/
theorem image_momentContractionFiber_eq_momentFullPairingFiber
    (m : ℕ)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    (momentContractionFiber m s).image
        (momentContractionEquivFullPairing m) =
      momentFullPairingFiber m s := by
  ext κ
  constructor
  · intro hκ
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hκ
    rw [mem_momentFullPairingFiber]
    unfold momentFullPairingSignature
    rw [Equiv.symm_apply_apply]
    exact mem_momentContractionFiber.mp he
  · intro hκ
    have hsignature :
        momentContractionSignature
            ((momentContractionEquivFullPairing m).symm κ) =
          s := by
      exact mem_momentFullPairingFiber.mp hκ
    apply Finset.mem_image.mpr
    refine
      ⟨(momentContractionEquivFullPairing m).symm κ,
        mem_momentContractionFiber.mpr hsignature, ?_⟩
    exact Equiv.apply_symm_apply _ κ

/-- Exact finite-sum replacement of a fixed contraction fibre by the
corresponding full-pairing fibre. -/
theorem sum_momentContractionFiber_eq_sum_fullPairingFiber
    {m : ℕ}
    {A : Type*} [AddCommMonoid A]
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (F :
      {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} → A) :
    (∑ e ∈ momentContractionFiber m s,
        F (momentContractionEquivFullPairing m e)) =
      ∑ κ ∈ momentFullPairingFiber m s, F κ := by
  rw [←
    image_momentContractionFiber_eq_momentFullPairingFiber m s]
  exact
    (Finset.sum_image
      (momentContractionEquivFullPairing m).injective.injOn).symm

/-- Exact fixed-signature reindexing onto the corresponding set of full
doubled pairings.  This is the finite-sum form used before the successive
primitive-block collapses; injectivity shows that no fibre cardinality factor
is introduced. -/
theorem sum_momentContractionFiber_eq_sum_doubledPairingImage
    {m : ℕ}
    {A : Type*} [AddCommMonoid A]
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (F : PartialPairing (Fin (2 * m)) → A) :
    (∑ e ∈ momentContractionFiber m s,
        F (momentCombinedPairing e.1 e.2.1 e.2.2)) =
      ∑ κ ∈ (momentContractionFiber m s).image
          (fun e => momentCombinedPairing e.1 e.2.1 e.2.2),
        F κ := by
  exact
    (Finset.sum_image momentCombinedPairing_injective.injOn).symm

/-- Every pairing in the fixed-signature image is full. -/
theorem isFull_of_mem_momentContractionFiber_image
    {m : ℕ}
    {s : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    {κ : PartialPairing (Fin (2 * m))}
    (hκ : κ ∈ (momentContractionFiber m s).image
      (fun e => momentCombinedPairing e.1 e.2.1 e.2.2)) :
    κ.IsFull := by
  obtain ⟨e, _he, rfl⟩ := Finset.mem_image.mp hκ
  exact momentCombinedPairing_isFull e.1 e.2.1 e.2.2

/-! ## Reindexing the actual physical integrand -/

/-- One R-324 physical integrand indexed by the equivalent full doubled
pairing rather than by a contraction triple. -/
def momentFullPairingPhysicalIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull})
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  let e := (momentContractionEquivFullPairing m).symm κ
  deterministicMomentIntegrand ρ ε m α β
    e.1 e.2.1 e.2.2 x y z w v

@[simp]
theorem momentFullPairingPhysicalIntegrand_momentContraction
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (e : MomentContraction m)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    momentFullPairingPhysicalIntegrand ρ ε m α β
        (momentContractionEquivFullPairing m e)
        x y z w v =
      deterministicMomentIntegrand ρ ε m α β
        e.1 e.2.1 e.2.2 x y z w v := by
  unfold momentFullPairingPhysicalIntegrand
  rw [Equiv.symm_apply_apply]

/-- Equation (4.18), with the fixed-signature contraction sum replaced
exactly by its full-pairing fibre. -/
theorem momentSignaturePhysicalIntegrand_eq_sum_fullPairingFiber
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    momentSignaturePhysicalIntegrand ρ ε m α β s x y z w v =
      ∑ κ ∈ momentFullPairingFiber m s,
        momentFullPairingPhysicalIntegrand
          ρ ε m α β κ x y z w v := by
  unfold momentSignaturePhysicalIntegrand
  simpa only
      [momentFullPairingPhysicalIntegrand_momentContraction] using
    (sum_momentContractionFiber_eq_sum_fullPairingFiber
      s
      (fun κ =>
        momentFullPairingPhysicalIntegrand
          ρ ε m α β κ x y z w v))

/-- The Fourier phase common to every contraction in a fixed physical
configuration. -/
def momentFourierPhase
    (α β : Z4) (x y z w : T4) : ℂ :=
  charT4 α x * charT4 β y *
    charT4 (-α) z * charT4 (-β) w

/-- The deterministic R-324 integrand factors through the Green skeletons
of the two within-copy restrictions and the covariance product of the one
full doubled pairing.  This is the algebraic content of the passage to
`κ'` immediately before paper (4.18). -/
theorem deterministicMomentIntegrand_eq_skeletons_mul_fullCovariance
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    deterministicMomentIntegrand ρ ε m α β
        κp κm π x y z w v =
      momentFourierPhase α β x y z w *
        renormalizedGreenSkeleton κp
          (assemble x y fun i => v (leftMomentIndex i)) *
        renormalizedGreenSkeleton κm
          (assemble z w fun i => v (rightMomentIndex i)) *
        (primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing κp κm π) v : ℂ) := by
  have hp :=
    detIntegrand_eq_renormalizedGreenSkeleton_mul_covariance
      ρ ε κp
        (assemble x y fun i => v (leftMomentIndex i))
  have hm :=
    detIntegrand_eq_renormalizedGreenSkeleton_mul_covariance
      ρ ε κm
        (assemble z w fun i => v (rightMomentIndex i))
  have hcov :=
    primitiveCovarianceProduct_momentCombinedPairing
      ρ ε m κp κm π v
  unfold deterministicMomentIntegrand momentFourierPhase
  rw [show
      ((detIntegrand ρ ε m κp
          (assemble x y fun i => v (leftMomentIndex i)) *
        detIntegrand ρ ε m κm
          (assemble z w fun i => v (rightMomentIndex i)) *
        momentCrossCovarianceProduct ρ ε m κp κm π v : ℝ) : ℂ) =
        (detIntegrand ρ ε m κp
          (assemble x y fun i => v (leftMomentIndex i)) : ℂ) *
        (detIntegrand ρ ε m κm
          (assemble z w fun i => v (rightMomentIndex i)) : ℂ) *
        (momentCrossCovarianceProduct ρ ε m κp κm π v : ℂ) by
      push_cast
      rfl,
    hp, hm, hcov]
  unfold detCovarianceFactor
  simp only [assemble_varIdx]
  push_cast
  ring

/-- Full-pairing-indexed form of the preceding factorization. -/
theorem momentFullPairingPhysicalIntegrand_eq_skeletons_mul_covariance
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull})
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    momentFullPairingPhysicalIntegrand
        ρ ε m α β κ x y z w v =
      let e := (momentContractionEquivFullPairing m).symm κ
      momentFourierPhase α β x y z w *
        renormalizedGreenSkeleton e.1
          (assemble x y fun i => v (leftMomentIndex i)) *
        renormalizedGreenSkeleton e.2.1
          (assemble z w fun i => v (rightMomentIndex i)) *
        (primitiveCovarianceProduct ρ ε m κ.1 v : ℂ) := by
  let e := (momentContractionEquivFullPairing m).symm κ
  have hreassemble :
      momentCombinedPairing e.1 e.2.1 e.2.2 = κ.1 := by
    exact
      momentCombinedPairing_momentContractionOfFull κ.1 κ.2
  unfold momentFullPairingPhysicalIntegrand
  dsimp only
  rw [deterministicMomentIntegrand_eq_skeletons_mul_fullCovariance,
    hreassemble]

/-- On a nonempty fixed-signature fibre, both Green skeletons are common
factors.  Consequently the complete primitive-pairing sum is formed before
any absolute-value estimate is applied.  This is the exact algebraic
factorization underlying paper (4.18) and avoids a factorial loss from
termwise bounds. -/
theorem
    momentSignaturePhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentContractionFiber m s)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    momentSignaturePhysicalIntegrand ρ ε m α β s x y z w v =
      momentFourierPhase α β x y z w *
        renormalizedGreenSkeleton e₀.1
          (assemble x y fun i => v (leftMomentIndex i)) *
        renormalizedGreenSkeleton e₀.2.1
          (assemble z w fun i => v (rightMomentIndex i)) *
        ∑ κ ∈ momentFullPairingFiber m s,
          (primitiveCovarianceProduct ρ ε m κ.1 v : ℂ) := by
  rw [momentSignaturePhysicalIntegrand_eq_sum_fullPairingFiber]
  have he₀signature :
      momentContractionSignature e₀ = s :=
    mem_momentContractionFiber.mp he₀
  apply Eq.trans ?_ (Finset.mul_sum _ _ _).symm
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [momentFullPairingPhysicalIntegrand_eq_skeletons_mul_covariance]
  dsimp only
  let e := (momentContractionEquivFullPairing m).symm κ
  have hesignature :
      momentContractionSignature e = s :=
    mem_momentFullPairingFiber.mp hκ
  obtain ⟨hleft, hright⟩ :=
    renormalizedGreenSkeletons_eq_of_momentContractionSignature_eq
      e e₀ (hesignature.trans he₀signature.symm)
  rw [hleft, hright]

/-- Every realized signature admits a representative whose two Green
skeletons can be pulled in front of the complete primitive-pairing sum. -/
theorem
    exists_commonSkeleton_factorization_of_mem_momentContractionSignatures
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ∃ e₀ ∈ momentContractionFiber m s,
      momentSignaturePhysicalIntegrand ρ ε m α β s x y z w v =
        momentFourierPhase α β x y z w *
          renormalizedGreenSkeleton e₀.1
            (assemble x y fun i => v (leftMomentIndex i)) *
          renormalizedGreenSkeleton e₀.2.1
            (assemble z w fun i => v (rightMomentIndex i)) *
          ∑ κ ∈ momentFullPairingFiber m s,
            (primitiveCovarianceProduct ρ ε m κ.1 v : ℂ) := by
  obtain ⟨e₀, he₀⟩ :=
    momentContractionFiber_nonempty_iff_mem_signatures.mpr hs
  exact
    ⟨e₀, he₀,
      momentSignaturePhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
        ρ ε m α β s e₀ he₀ x y z w v⟩

/-- Norm form of the common-skeleton factorization.  Positivity of every
covariance factor removes the absolute value from the complete
primitive-pairing sum, while all Fourier characters have norm one. -/
theorem
    norm_momentSignaturePhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentContractionFiber m s)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ‖momentSignaturePhysicalIntegrand
        ρ ε m α β s x y z w v‖ =
      ‖renormalizedGreenSkeleton e₀.1
          (assemble x y fun i => v (leftMomentIndex i))‖ *
        ‖renormalizedGreenSkeleton e₀.2.1
          (assemble z w fun i => v (rightMomentIndex i))‖ *
        ∑ κ ∈ momentFullPairingFiber m s,
          primitiveCovarianceProduct ρ ε m κ.1 v := by
  rw [
    momentSignaturePhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
      ρ ε m α β s e₀ he₀ x y z w v]
  have hphase :
      ‖momentFourierPhase α β x y z w‖ = 1 := by
    unfold momentFourierPhase
    simp only [norm_mul, norm_charT4, mul_one]
  have hsumNonneg :
      0 ≤ ∑ κ ∈ momentFullPairingFiber m s,
        primitiveCovarianceProduct ρ ε m κ.1 v := by
    exact Finset.sum_nonneg fun κ _hκ =>
      primitiveCovarianceProduct_nonneg ρ ε m κ.1 v
  rw [norm_mul, norm_mul, norm_mul, hphase, one_mul]
  have hcast :
      (∑ κ ∈ momentFullPairingFiber m s,
          (primitiveCovarianceProduct ρ ε m κ.1 v : ℂ)) =
        ((∑ κ ∈ momentFullPairingFiber m s,
          primitiveCovarianceProduct ρ ε m κ.1 v : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hsumNonneg]

/-- Pointwise domination on the four inner physical variables passes to
the canonical fixed-signature density.  The proof also handles exceptional
nonintegrable sections: mathlib's Bochner integral is then zero.  This is
the generic Tonelli bridge used after each concrete block collapse has
produced its nonnegative inner majorant. -/
theorem scaled_momentSignaturePhysicalDensity_le_integral_of_pointwise
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (x : T4) (scale : ℝ) (hscale : 0 ≤ scale)
    (B : R324PhysicalRest m → ℝ)
    (hB : Integrable B (r324PhysicalRestMeasure m))
    (hBnonneg : ∀ r, 0 ≤ B r)
    (hpointwise : ∀ r,
      scale *
          ‖r324Flatten
            (momentSignaturePhysicalIntegrand
              ρ ε m α β s) (x, r)‖ ≤
        B r) :
    scale *
        momentSignaturePhysicalDensity
          ρ ε m α β s x ≤
      ∫ r, B r ∂(r324PhysicalRestMeasure m) := by
  let f : R324PhysicalRest m → ℂ := fun r =>
    r324Flatten
      (momentSignaturePhysicalIntegrand
        ρ ε m α β s) (x, r)
  change
    scale * ‖∫ r, f r ∂(r324PhysicalRestMeasure m)‖ ≤
      ∫ r, B r ∂(r324PhysicalRestMeasure m)
  by_cases hf :
      Integrable f (r324PhysicalRestMeasure m)
  · calc
      scale * ‖∫ r, f r ∂(r324PhysicalRestMeasure m)‖ ≤
          scale *
            ∫ r, ‖f r‖ ∂(r324PhysicalRestMeasure m) :=
        mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm f) hscale
      _ = ∫ r, scale * ‖f r‖
            ∂(r324PhysicalRestMeasure m) := by
        rw [integral_const_mul]
      _ ≤ ∫ r, B r ∂(r324PhysicalRestMeasure m) :=
        integral_mono (hf.norm.const_mul scale) hB hpointwise
  · rw [integral_undef hf, norm_zero, mul_zero]
    exact integral_nonneg hBnonneg

end

end Anderson4D
