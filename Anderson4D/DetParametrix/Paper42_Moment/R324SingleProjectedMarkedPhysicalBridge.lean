import Anderson4D.DetParametrix.Paper42_Moment.R324MarkedResidualPhysicalBridge

/-!
# Exact bridge from one projected cross covariance to the marked residual core

The residual carrier contains three disjoint kinds of lower endpoints:
within-left pairs, within-right pairs, and cross-copy pairs.  A
`R324ResidualCovarianceSlot` indexes only the third kind.  This file keeps
the other two complete physical covariance products explicit and proves
that their product with the single-projected cross factor is exactly the
marker-preserving covariance product on `momentResidualActive`.

No selector fibre is enlarged here.  In particular, this equality is a
pointwise physical-space identity and makes no assertion that a
Fourier-selector fibre constrained by all of its modes is an unrestricted
projected-covariance series.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The three disjoint residual lower-endpoint carriers -/

/-- Lower endpoints of within-left pairs which survive the left reduction. -/
def r324LeftResidualPairLowerEndpoints
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    Finset (Fin (2 * m)) :=
  ((finalActive κp).filter fun i => i < κp i).image
    leftMomentIndex

/-- Lower endpoints of within-right pairs which survive the right
reduction. -/
def r324RightResidualPairLowerEndpoints
    {m : ℕ} (κm : PartialPairing (Fin m)) :
    Finset (Fin (2 * m)) :=
  ((finalActive κm).filter fun i => i < κm i).image
    rightMomentIndex

theorem disjoint_r324LeftResidualPair_right
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    Disjoint
      (r324LeftResidualPairLowerEndpoints κp)
      (r324RightResidualPairLowerEndpoints κm) := by
  unfold r324LeftResidualPairLowerEndpoints
    r324RightResidualPairLowerEndpoints
  exact disjoint_image_leftMomentIndex_rightMomentIndex _ _

theorem disjoint_r324LeftResidualPair_cross
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    Disjoint
      (r324LeftResidualPairLowerEndpoints κp)
      (momentCrossLowerEndpoints κp) := by
  rw [Finset.disjoint_left]
  intro a ha hcross
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hcross
  have hji' : j = i :=
    leftMomentIndex_injective hji
  subst j
  have hiLt := (Finset.mem_filter.mp hi).2
  exact
    (ne_of_lt hiLt)
      (PartialPairing.mem_singles.mp hj).symm

theorem disjoint_r324RightResidualPair_cross
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    Disjoint
      (r324RightResidualPairLowerEndpoints κm)
      (momentCrossLowerEndpoints κp) := by
  unfold r324RightResidualPairLowerEndpoints
  exact
    (disjoint_image_leftMomentIndex_rightMomentIndex
      κp.singles
      ((finalActive κm).filter fun i => i < κm i)).symm

/-- The lower endpoints used by the combined pairing on the residual
carrier are covered exactly once by the within-left, within-right, and
cross-copy carriers. -/
theorem r324ResidualLowerEndpoints_eq_threeWay
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentResidualActive κp κm).filter
        (fun a => a < momentCombinedPairing κp κm π a) =
      r324LeftResidualPairLowerEndpoints κp ∪
        r324RightResidualPairLowerEndpoints κm ∪
          momentCrossLowerEndpoints κp := by
  ext a
  let side := (momentDoubleFinEquiv m).symm a
  have ha :
      momentDoubleFinEquiv m side = a :=
    (momentDoubleFinEquiv m).apply_symm_apply a
  rcases side with i | j
  · have haLeft : leftMomentIndex i = a := by
      exact ha
    rw [← haLeft, Finset.mem_filter,
      leftMomentIndex_mem_momentResidualActive_iff,
      leftMomentIndex_lt_combined_iff]
    simp only [Finset.mem_union]
    constructor
    · rintro ⟨hactive, hsingle | hpair⟩
      · exact Or.inr
          (Finset.mem_image.mpr ⟨i, hsingle, rfl⟩)
      · exact Or.inl (Or.inl
          (Finset.mem_image.mpr
            ⟨i, Finset.mem_filter.mpr
              ⟨hactive, hpair.2⟩, rfl⟩))
    · rintro ((hleft | hright) | hcross)
      · obtain ⟨i', hi', heq⟩ :=
          Finset.mem_image.mp hleft
        have hii : i' = i :=
          leftMomentIndex_injective heq
        subst i'
        exact
          ⟨(Finset.mem_filter.mp hi').1,
            Or.inr
              ⟨by
                intro hsingle
                exact
                  (ne_of_lt
                    (Finset.mem_filter.mp hi').2)
                    (PartialPairing.mem_singles.mp hsingle).symm,
                (Finset.mem_filter.mp hi').2⟩⟩
      · obtain ⟨j', _hj', heq⟩ :=
          Finset.mem_image.mp hright
        have hval := congrArg Fin.val heq
        simp only [leftMomentIndex, rightMomentIndex] at hval
        have hiLt := i.isLt
        omega
      · obtain ⟨i', hi', heq⟩ :=
          Finset.mem_image.mp hcross
        have hii : i' = i :=
          leftMomentIndex_injective heq
        subst i'
        exact
          ⟨singles_subset_finalActive κp hi',
            Or.inl hi'⟩
  · have haRight : rightMomentIndex j = a := by
      exact ha
    rw [← haRight, Finset.mem_filter,
      rightMomentIndex_mem_momentResidualActive_iff,
      rightMomentIndex_lt_combined_iff]
    simp only [Finset.mem_union]
    constructor
    · rintro ⟨hactive, hnotSingle, hlt⟩
      exact Or.inl (Or.inr
        (Finset.mem_image.mpr
          ⟨j, Finset.mem_filter.mpr
            ⟨hactive, hlt⟩, rfl⟩))
    · rintro ((hleft | hright) | hcross)
      · obtain ⟨i, _hi, heq⟩ :=
          Finset.mem_image.mp hleft
        have hval := congrArg Fin.val heq
        simp only [leftMomentIndex, rightMomentIndex] at hval
        have hiLt := i.isLt
        omega
      · obtain ⟨j', hj', heq⟩ :=
          Finset.mem_image.mp hright
        have hjj : j' = j :=
          rightMomentIndex_injective heq
        subst j'
        exact
          ⟨(Finset.mem_filter.mp hj').1,
            by
              intro hsingle
              exact
                (ne_of_lt
                  (Finset.mem_filter.mp hj').2)
                  (PartialPairing.mem_singles.mp hsingle).symm,
            (Finset.mem_filter.mp hj').2⟩
      · obtain ⟨i, _hi, heq⟩ :=
          Finset.mem_image.mp hcross
        have hval := congrArg Fin.val heq
        simp only [leftMomentIndex, rightMomentIndex] at hval
        have hiLt := i.isLt
        omega

/-! ## Exact factor on each carrier -/

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

theorem prod_r324LeftResidualPairLowerEndpoints_marked_eq
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    (∏ a ∈ r324LeftResidualPairLowerEndpoints κp,
        if a = r324ResidualMarkedLowerEndpoint selected then
          ρ.r324ProjectedCovarianceC ε L
            (v a - v (momentCombinedPairing κp κm π a))
        else
          (ρ.etaEpsT4 ε
            (v a - v (momentCombinedPairing κp κm π a)) : ℂ)) =
      (pairingCovarianceProductOn ρ ε κp
        (finalActive κp)
        (fun i => v (leftMomentIndex i)) : ℂ) := by
  unfold r324LeftResidualPairLowerEndpoints
    pairingCovarianceProductOn
  push_cast
  rw [Finset.prod_image leftMomentIndex_injective.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  have hlt : i < κp i :=
    (Finset.mem_filter.mp hi).2
  have hnotSingle : i ∉ κp.singles := by
    intro hsingle
    exact
      (ne_of_lt hlt)
        (PartialPairing.mem_singles.mp hsingle).symm
  have hnotMarked :
      leftMomentIndex i ≠
        r324ResidualMarkedLowerEndpoint selected := by
    intro heq
    have hiSelected : i = selected.1 :=
      leftMomentIndex_injective heq
    subst i
    exact hnotSingle selected.2
  rw [if_neg hnotMarked,
    momentCombinedPairing_left_pair
      κp κm π i hnotSingle]

theorem prod_r324RightResidualPairLowerEndpoints_marked_eq
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    (∏ a ∈ r324RightResidualPairLowerEndpoints κm,
        if a = r324ResidualMarkedLowerEndpoint selected then
          ρ.r324ProjectedCovarianceC ε L
            (v a - v (momentCombinedPairing κp κm π a))
        else
          (ρ.etaEpsT4 ε
            (v a - v (momentCombinedPairing κp κm π a)) : ℂ)) =
      (pairingCovarianceProductOn ρ ε κm
        (finalActive κm)
        (fun i => v (rightMomentIndex i)) : ℂ) := by
  unfold r324RightResidualPairLowerEndpoints
    pairingCovarianceProductOn
  push_cast
  rw [Finset.prod_image rightMomentIndex_injective.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  have hlt : i < κm i :=
    (Finset.mem_filter.mp hi).2
  have hnotSingle : i ∉ κm.singles := by
    intro hsingle
    exact
      (ne_of_lt hlt)
        (PartialPairing.mem_singles.mp hsingle).symm
  have hnotMarked :
      rightMomentIndex i ≠
        r324ResidualMarkedLowerEndpoint selected := by
    intro heq
    have hval := congrArg Fin.val heq
    simp only [rightMomentIndex,
      r324ResidualMarkedLowerEndpoint,
      leftMomentIndex] at hval
    have hselectedLt := selected.1.isLt
    omega
  rw [if_neg hnotMarked,
    momentCombinedPairing_right_pair
      κp κm π i hnotSingle]

theorem prod_momentCrossLowerEndpoints_marked_eq
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    (∏ a ∈ momentCrossLowerEndpoints κp,
        if a = r324ResidualMarkedLowerEndpoint selected then
          ρ.r324ProjectedCovarianceC ε L
            (v a - v (momentCombinedPairing κp κm π a))
        else
          (ρ.etaEpsT4 ε
            (v a - v (momentCombinedPairing κp κm π a)) : ℂ)) =
      ρ.r324SingleProjectedResidualCovarianceProduct
        ε L κp κm π v selected := by
  unfold momentCrossLowerEndpoints
    SmoothCutoff.r324SingleProjectedResidualCovarianceProduct
  rw [Finset.prod_image leftMomentIndex_injective.injOn]
  rw [Finset.prod_subtype κp.singles
    (fun _ => Iff.rfl)]
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases his : i = selected
  · subst i
    simp only [
      SmoothCutoff.r324SingleProjectedResidualCovarianceFactor,
      if_pos, r324ResidualMarkedLowerEndpoint,
      r324ResidualCovarianceDisplacement]
    rw [momentCombinedPairing_left_single
      κp κm π selected.1 selected.2]
  · have hindex :
        leftMomentIndex i ≠
          r324ResidualMarkedLowerEndpoint selected := by
      intro heq
      apply his
      apply Subtype.ext
      exact leftMomentIndex_injective heq
    simp only [hindex, if_false,
      SmoothCutoff.r324SingleProjectedResidualCovarianceFactor,
      his, r324ResidualCovarianceDisplacement]
    rw [momentCombinedPairing_left_single
      κp κm π i.1 i.2]

/-! ## The exact three-factor marked product and signed core -/

/-- The marker-preserving covariance product on the complete residual
carrier is exactly:

1. the complete within-left residual covariance product;
2. the complete within-right residual covariance product; and
3. the cross-copy product with precisely one projected slot.

The equality is pointwise and retains all three factors inside the same
physical integrand. -/
theorem r324MarkedResidualActiveProduct_eq_threeFactor
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ρ.r324MarkedPairingCovarianceProductOn ε L
        (momentCombinedPairing κp κm π)
        (r324ResidualMarkedLowerEndpoint selected)
        (momentResidualActive κp κm) v =
      (pairingCovarianceProductOn ρ ε κp
          (finalActive κp)
          (fun i => v (leftMomentIndex i)) : ℂ) *
        (pairingCovarianceProductOn ρ ε κm
          (finalActive κm)
          (fun i => v (rightMomentIndex i)) : ℂ) *
        ρ.r324SingleProjectedResidualCovarianceProduct
          ε L κp κm π v selected := by
  let f : Fin (2 * m) → ℂ := fun a =>
    if a = r324ResidualMarkedLowerEndpoint selected then
      ρ.r324ProjectedCovarianceC ε L
        (v a - v (momentCombinedPairing κp κm π a))
    else
      (ρ.etaEpsT4 ε
        (v a - v (momentCombinedPairing κp κm π a)) : ℂ)
  have hLR :=
    disjoint_r324LeftResidualPair_right κp κm
  have hLC :=
    disjoint_r324LeftResidualPair_cross κp
  have hRC :=
    disjoint_r324RightResidualPair_cross κp κm
  have hLRC :
      Disjoint
        (r324LeftResidualPairLowerEndpoints κp ∪
          r324RightResidualPairLowerEndpoints κm)
        (momentCrossLowerEndpoints κp) :=
    Finset.disjoint_union_left.mpr ⟨hLC, hRC⟩
  unfold SmoothCutoff.r324MarkedPairingCovarianceProductOn
  change
    (∏ a ∈
        (momentResidualActive κp κm).filter
          (fun a => a < momentCombinedPairing κp κm π a),
      f a) = _
  rw [r324ResidualLowerEndpoints_eq_threeWay κp κm π,
    Finset.prod_union hLRC,
    Finset.prod_union hLR]
  rw [
    ρ.prod_r324LeftResidualPairLowerEndpoints_marked_eq
      ε L κp κm π selected v,
    ρ.prod_r324RightResidualPairLowerEndpoints_marked_eq
      ε L κp κm π selected v,
    ρ.prod_momentCrossLowerEndpoints_marked_eq
      ε L κp κm π selected v]

/-- Signed physical residual core written in the original three-factor
coordinates.  The Green profiles and all covariance factors remain in one
physical-space product. -/
def r324SingleProjectedResidualPhysicalInteriorCore
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) : ℂ :=
  r324RenormalizedInteriorCore κp
      (fun i => v (leftMomentIndex i)) *
    r324RenormalizedInteriorCore κm
      (fun i => v (rightMomentIndex i)) *
    (pairingCovarianceProductOn ρ ε κp
      (finalActive κp)
      (fun i => v (leftMomentIndex i)) : ℂ) *
    (pairingCovarianceProductOn ρ ε κm
      (finalActive κm)
      (fun i => v (rightMomentIndex i)) : ℂ) *
    ρ.r324SingleProjectedResidualCovarianceProduct
      ε L κp κm π v selected

/-- **Exact signed-core bridge.**  The original three residual covariance
factors are literally the marked physical core; no covariance factor is
Fourier-expanded, estimated, or separated from the Green profiles. -/
theorem r324SingleProjectedResidualPhysicalInteriorCore_eq_marked
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ρ.r324SingleProjectedResidualPhysicalInteriorCore
        ε L κp κm π selected v =
      ρ.r324MarkedResidualPhysicalInteriorCore
        ε L κp κm π selected v := by
  unfold r324SingleProjectedResidualPhysicalInteriorCore
    r324MarkedResidualPhysicalInteriorCore
  rw [ρ.r324MarkedResidualActiveProduct_eq_threeFactor
    ε L κp κm π selected v]
  ring

/-- Exact complement ledger for the original three-factor core.  Removing
only the projected edge leaves precisely the already-defined complete
physical complement mass. -/
theorem norm_r324SingleProjectedResidualPhysicalInteriorCore_eq
    {m : ℕ} (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ‖ρ.r324SingleProjectedResidualPhysicalInteriorCore
        ε L κp κm π selected v‖ =
      ‖ρ.r324ProjectedCovarianceC ε L
        (v (r324ResidualMarkedLowerEndpoint selected) -
          v (r324ResidualMarkedUpperEndpoint π selected))‖ *
        ρ.r324MarkedResidualPhysicalComplementMass
          ε κp κm π selected v := by
  rw [
    ρ.r324SingleProjectedResidualPhysicalInteriorCore_eq_marked,
    ρ.norm_r324MarkedResidualPhysicalInteriorCore_eq_projectedEdge]
  unfold r324MarkedResidualPhysicalComplementMass
  ring

end SmoothCutoff

end

end Anderson4D
