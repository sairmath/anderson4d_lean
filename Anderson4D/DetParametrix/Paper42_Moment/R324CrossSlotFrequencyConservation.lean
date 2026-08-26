import Anderson4D.DetParametrix.Paper42_Moment.R324CountableConfigurations

/-!
# Frequency conservation through the cross-contraction slots

For a doubled moment contraction, the only covariance pairs that can
transport Fourier frequency from the left physical copy to the right
physical copy are the pairs created from singles of the left partial
pairing.  This file isolates that statement before any residual-block
collapse is performed.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- A within-copy full pairing contributes no mode to translation of the
left physical copy. -/
theorem r324LeftPairModeContribution_momentCombinedPairing_eq_zero_of_isFull
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hκp : κp.IsFull) (hκm : κm.IsFull)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun i => i < momentCombinedPairing κp κm π i)).card → Z4)
    (j :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun i => i < momentCombinedPairing κp κm π i)).card) :
    r324LeftPairModeContribution
        (momentCombinedPairing κp κm π) q j = 0 := by
  let i :=
    (r324PairFinEquiv (momentCombinedPairing κp κm π) j).1
  change
    (if i.val < m then q j else 0) -
        (if (momentCombinedPairing κp κm π i).val < m then
          q j
        else 0) =
      0
  obtain ⟨s, hs⟩ := (momentDoubleFinEquiv m).surjective i
  rcases s with a | b
  · have hi : i = leftMomentIndex a := by
      simpa using hs.symm
    rw [hi]
    have ha : a ∉ κp.singles := by
      rw [PartialPairing.isFull_iff_singles_eq_empty.mp hκp]
      simp
    rw [momentCombinedPairing_left_pair κp κm π a ha]
    simp only [leftMomentIndex]
    simp
  · have hi : i = rightMomentIndex b := by
      simpa using hs.symm
    rw [hi]
    have hb : b ∉ κm.singles := by
      rw [PartialPairing.isFull_iff_singles_eq_empty.mp hκm]
      simp
    rw [momentCombinedPairing_right_pair κp κm π b hb]
    simp only [rightMomentIndex]
    simp

/-- If both within-copy partial pairings are full, the complete signed
left-mode sum vanishes. -/
theorem r324LeftModeSum_momentCombinedPairing_eq_zero_of_isFull
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hκp : κp.IsFull) (hκm : κm.IsFull)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun i => i < momentCombinedPairing κp κm π i)).card → Z4) :
    r324LeftModeSum (momentCombinedPairing κp κm π) q = 0 := by
  unfold r324LeftModeSum
  apply Finset.sum_eq_zero
  intro j _hj
  exact
    r324LeftPairModeContribution_momentCombinedPairing_eq_zero_of_isFull
      κp κm π hκp hκm q j

/-- A nonzero Fourier configuration built from full pairings in both
copies can occur only at zero external shift. -/
theorem external_add_eq_zero_of_full_full_integral_ne_zero
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hκp : κp.IsFull) (hκm : κm.IsFull)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun i => i < momentCombinedPairing κp κm π i)).card → Z4)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    α + β = 0 := by
  have hconservation :=
    ρ.r324LeftModeSum_eq_neg_external_of_integral_ne_zero
      ε α β
      ⟨momentCombinedPairing κp κm π,
        momentCombinedPairing_isFull κp κm π⟩ q hne
  rw [
    r324LeftModeSum_momentCombinedPairing_eq_zero_of_isFull
      κp κm π hκp hκm q] at hconservation
  exact neg_eq_zero.mp hconservation.symm

/-- A nonzero configuration at nonzero external shift must contain a
cross-copy contraction slot. -/
theorem singles_nonempty_of_external_add_ne_zero_integral_ne_zero
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun i => i < momentCombinedPairing κp κm π i)).card → Z4)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    κp.singles.Nonempty := by
  by_contra hempty
  have hpempty : κp.singles = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hmempty : κm.singles = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hm
    obtain ⟨j, hj⟩ := hm
    let i : κp.singles := π.symm ⟨j, hj⟩
    simpa [hpempty] using i.2
  exact hexternal
    (ρ.external_add_eq_zero_of_full_full_integral_ne_zero
      ε α β κp κm π
      (PartialPairing.isFull_iff_singles_eq_empty.mpr hpempty)
      (PartialPairing.isFull_iff_singles_eq_empty.mpr hmempty)
      q hne)

/-- At nonzero external shift, a configuration with no left cross slot
vanishes identically.  This is the form used to discard the full/full branch
before selecting a marked covariance slot. -/
theorem r324FullPairingFourierIntegral_eq_zero_of_singles_empty
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hsingles : κp.singles = ∅)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun i => i < momentCombinedPairing κp κm π i)).card → Z4) :
    ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q =
      0 := by
  by_contra hne
  have hnonempty :=
    ρ.singles_nonempty_of_external_add_ne_zero_integral_ne_zero
      ε α β κp κm π hexternal q hne
  rw [hsingles] at hnonempty
  simp at hnonempty

/-- Equivalent vanishing statement when fullness of the left partial
pairing is the available hypothesis. -/
theorem r324FullPairingFourierIntegral_eq_zero_of_left_isFull
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hexternal : α + β ≠ 0)
    (hκp : κp.IsFull)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun i => i < momentCombinedPairing κp κm π i)).card → Z4) :
    ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q =
      0 := by
  exact
    ρ.r324FullPairingFourierIntegral_eq_zero_of_singles_empty
      ε α β κp κm π hexternal
      (PartialPairing.isFull_iff_singles_eq_empty.mp hκp) q

/-- The enumerated pair index of the cross-copy pair generated by one
single of the left partial pairing.  This enumerates exactly
`κp.singles`; within-copy covariance pairs are absent. -/
def r324CrossSlotPairIndex
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (i : κp.singles) :
    Fin ((momentCombinedPairing κp κm π).pairSupport.filter
      (fun a => a < momentCombinedPairing κp κm π a)).card :=
  (r324PairFinEquiv (momentCombinedPairing κp κm π)).symm
    ⟨leftMomentIndex i.1, by
      have hsupport :
          (momentCombinedPairing κp κm π).pairSupport =
            Finset.univ :=
        PartialPairing.isFull_iff_pairSupport_eq_univ.mp
          (momentCombinedPairing_isFull κp κm π)
      rw [Finset.mem_filter, hsupport]
      exact
        ⟨Finset.mem_univ _,
          (leftMomentIndex_lt_combined_iff κp κm π i.1).mpr
            (Or.inl i.2)⟩⟩

@[simp]
theorem r324PairFinEquiv_r324CrossSlotPairIndex
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (i : κp.singles) :
    (r324PairFinEquiv (momentCombinedPairing κp κm π)
      (r324CrossSlotPairIndex κp κm π i)).1 =
        leftMomentIndex i.1 := by
  unfold r324CrossSlotPairIndex
  rw [Equiv.apply_symm_apply]

theorem r324CrossSlotPairIndex_injective
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    Function.Injective (r324CrossSlotPairIndex κp κm π) := by
  intro i j hij
  have hendpoint :=
    congrArg
      (fun a =>
        (r324PairFinEquiv (momentCombinedPairing κp κm π) a).1)
      hij
  simp only [r324PairFinEquiv_r324CrossSlotPairIndex] at hendpoint
  apply Subtype.ext
  exact leftMomentIndex_injective hendpoint

/-- At a cross slot, the signed left-copy contribution is the assigned
pair mode with positive sign. -/
@[simp]
theorem r324LeftPairModeContribution_r324CrossSlotPairIndex
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun a => a < momentCombinedPairing κp κm π a)).card → Z4)
    (i : κp.singles) :
    r324LeftPairModeContribution
        (momentCombinedPairing κp κm π) q
        (r324CrossSlotPairIndex κp κm π i) =
      q (r324CrossSlotPairIndex κp κm π i) := by
  unfold r324LeftPairModeContribution
  rw [r324PairFinEquiv_r324CrossSlotPairIndex]
  dsimp only
  rw [momentCombinedPairing_left_single κp κm π i.1 i.2]
  have hleft : (leftMomentIndex i.1).val < m := i.1.isLt
  have hright :
      ¬(rightMomentIndex (π i).1).val < m := by
    simp only [rightMomentIndex]
    omega
  rw [if_pos hleft, if_neg hright, sub_zero]

/-- Every enumerated pair outside the image of the cross-slot
enumeration contributes zero to left-copy translation. -/
theorem r324LeftPairModeContribution_eq_zero_of_not_crossSlot
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun a => a < momentCombinedPairing κp κm π a)).card → Z4)
    (j :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun a => a < momentCombinedPairing κp κm π a)).card)
    (hj :
      ∀ i : κp.singles,
        r324CrossSlotPairIndex κp κm π i ≠ j) :
    r324LeftPairModeContribution
        (momentCombinedPairing κp κm π) q j = 0 := by
  let a :=
    r324PairFinEquiv (momentCombinedPairing κp κm π) j
  have halower :
      a.1 < momentCombinedPairing κp κm π a.1 :=
    (Finset.mem_filter.mp a.2).2
  obtain ⟨s, hs⟩ := (momentDoubleFinEquiv m).surjective a.1
  rcases s with i | i
  · have ha : a.1 = leftMomentIndex i := by
      simpa using hs.symm
    by_cases hi : i ∈ κp.singles
    · have hindex :
          j = r324CrossSlotPairIndex κp κm π ⟨i, hi⟩ := by
        apply
          (r324PairFinEquiv
            (momentCombinedPairing κp κm π)).injective
        apply Subtype.ext
        simpa [a] using ha
      exact False.elim (hj ⟨i, hi⟩ hindex.symm)
    · unfold r324LeftPairModeContribution
      change
        (if a.1.val < m then q j else 0) -
            (if (momentCombinedPairing κp κm π a.1).val < m then
              q j
            else 0) =
          0
      rw [ha, momentCombinedPairing_left_pair κp κm π i hi]
      simp only [leftMomentIndex]
      simp
  · have ha : a.1 = rightMomentIndex i := by
      simpa using hs.symm
    by_cases hi : i ∈ κm.singles
    · rw [ha] at halower
      exact False.elim
        (((rightMomentIndex_lt_combined_iff κp κm π i).mp
          halower).1 hi)
    · unfold r324LeftPairModeContribution
      change
        (if a.1.val < m then q j else 0) -
            (if (momentCombinedPairing κp κm π a.1).val < m then
              q j
            else 0) =
          0
      rw [ha, momentCombinedPairing_right_pair κp κm π i hi]
      simp only [rightMomentIndex]
      simp

/-- The lattice-frequency increment attached to one cross-contraction
slot, with the sign chosen so that the total is the external shift. -/
def r324CrossSlotLatticeIncrement
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun a => a < momentCombinedPairing κp κm π a)).card → Z4)
    (i : κp.singles) : Z4 :=
  -q (r324CrossSlotPairIndex κp κm π i)

/-- Euclidean realization of a cross-contraction-slot increment. -/
def r324CrossSlotIncrement
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun a => a < momentCombinedPairing κp κm π a)).card → Z4)
    (i : κp.singles) :
    EuclideanSpace ℝ (Fin dim) :=
  z4EuclideanFrequency
    (r324CrossSlotLatticeIncrement κp κm π q i)

/-- Cross slots alone carry the entire negative signed left-mode sum.
All within-copy covariance pairs cancel before this equality is used. -/
theorem sum_r324CrossSlotLatticeIncrement
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun a => a < momentCombinedPairing κp κm π a)).card → Z4) :
    (∑ i : κp.singles,
        r324CrossSlotLatticeIncrement κp κm π q i) =
      -r324LeftModeSum (momentCombinedPairing κp κm π) q := by
  let f := r324CrossSlotPairIndex κp κm π
  let S :=
    (Finset.univ : Finset κp.singles).image f
  calc
    (∑ i : κp.singles,
        r324CrossSlotLatticeIncrement κp κm π q i) =
        ∑ i : κp.singles, -q (f i) := by
      rfl
    _ = ∑ j ∈ S, -q j := by
      unfold S
      rw [Finset.sum_image]
      exact
        (r324CrossSlotPairIndex_injective κp κm π).injOn
    _ = ∑ j ∈ S,
        -r324LeftPairModeContribution
          (momentCombinedPairing κp κm π) q j := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hj
      rw [
        r324LeftPairModeContribution_r324CrossSlotPairIndex]
    _ = ∑ j,
        -r324LeftPairModeContribution
          (momentCombinedPairing κp κm π) q j := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _hjuniv hj
      have hnot :
          ∀ i : κp.singles,
            r324CrossSlotPairIndex κp κm π i ≠ j := by
        intro i hij
        apply hj
        exact Finset.mem_image.mpr
          ⟨i, Finset.mem_univ i, hij⟩
      rw [
        r324LeftPairModeContribution_eq_zero_of_not_crossSlot
          κp κm π q j hnot,
        neg_zero]
    _ = -(∑ j,
        r324LeftPairModeContribution
          (momentCombinedPairing κp κm π) q j) := by
      rw [Finset.sum_neg_distrib]
    _ = -r324LeftModeSum (momentCombinedPairing κp κm π) q := by
      rfl

/-- Under the existing nonzero-integral conservation law, the
cross-contraction-slot lattice increments sum to the exact external
Fourier shift. -/
theorem sum_r324CrossSlotLatticeIncrement_eq_external_of_integral_ne_zero
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun a => a < momentCombinedPairing κp κm π a)).card → Z4)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    (∑ i : κp.singles,
        r324CrossSlotLatticeIncrement κp κm π q i) =
      α + β := by
  rw [sum_r324CrossSlotLatticeIncrement]
  rw [
    ρ.r324LeftModeSum_eq_neg_external_of_integral_ne_zero
      ε α β
      ⟨momentCombinedPairing κp κm π,
        momentCombinedPairing_isFull κp κm π⟩ q hne,
    neg_neg]

/-- Euclidean cross-slot increments likewise sum to the exact external
frequency vector. -/
theorem sum_r324CrossSlotIncrement_eq_external_of_integral_ne_zero
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (q :
      Fin ((momentCombinedPairing κp κm π).pairSupport.filter
        (fun a => a < momentCombinedPairing κp κm π a)).card → Z4)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β
        ⟨momentCombinedPairing κp κm π,
          momentCombinedPairing_isFull κp κm π⟩ q ≠ 0) :
    (∑ i : κp.singles,
        r324CrossSlotIncrement κp κm π q i) =
      z4EuclideanFrequency (α + β) := by
  change
    (∑ i : κp.singles,
      z4EuclideanFrequencyAddHom
        (r324CrossSlotLatticeIncrement κp κm π q i)) =
      z4EuclideanFrequencyAddHom (α + β)
  calc
    (∑ i : κp.singles,
      z4EuclideanFrequencyAddHom
        (r324CrossSlotLatticeIncrement κp κm π q i)) =
        z4EuclideanFrequencyAddHom
          (∑ i : κp.singles,
            r324CrossSlotLatticeIncrement κp κm π q i) := by
      rw [map_sum]
    _ = z4EuclideanFrequencyAddHom (α + β) :=
      congrArg z4EuclideanFrequency
        (ρ.sum_r324CrossSlotLatticeIncrement_eq_external_of_integral_ne_zero
          ε α β κp κm π q hne)

end SmoothCutoff

end

end Anderson4D
