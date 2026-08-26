import Anderson4D.Main.External
import Anderson4D.Parametrix.L2NumericalBudget

/-!
# A common small-coupling threshold

The final argument uses three independently selected positive power
constants.  This file chooses one positive coupling threshold which is
simultaneously inside the external Proposition 3.6 range, closes the
second-moment geometric series, and places both good-event ratios below
the fixed boundary ratio.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Set

namespace Prop36Family

/-- A single coupling threshold for the external coefficient input, the
second-moment geometric series, and the two good-event geometric
ratios. -/
noncomputable def mainCouplingThreshold
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ)
    (secondPower goodPower Crenorm : ℝ) : ℝ :=
  let D := goodPower + Crenorm + 1
  min h.couplingThreshold
    (min (1 / (2 * secondPower))
      (min 1 (PartialPairing.boundaryGeometricRatio / D)))

/-- The common threshold is positive whenever its three named power
constants are positive. -/
theorem mainCouplingThreshold_pos
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ)
    {secondPower goodPower Crenorm : ℝ}
    (hsecond : 0 < secondPower)
    (hgood : 0 < goodPower)
    (hCrenorm : 0 < Crenorm) :
    0 < h.mainCouplingThreshold
      secondPower goodPower Crenorm := by
  let D : ℝ := goodPower + Crenorm + 1
  have hD : 0 < D := by
    dsimp only [D]
    linarith
  have hsecondQuot : 0 < 1 / (2 * secondPower) :=
    div_pos zero_lt_one (mul_pos (by norm_num) hsecond)
  have hboundaryQuot :
      0 < PartialPairing.boundaryGeometricRatio / D :=
    div_pos PartialPairing.boundaryGeometricRatio_pos hD
  unfold mainCouplingThreshold
  dsimp only
  exact lt_min h.couplingThreshold_pos
    (lt_min hsecondQuot
      (lt_min zero_lt_one hboundaryQuot))

/-- Every coupling in the common range satisfies all five numerical
requirements used by the final assembly. -/
theorem mainCouplingThreshold_spec
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ)
    {secondPower goodPower Crenorm lam : ℝ}
    (hsecond : 0 < secondPower)
    (hgood : 0 < goodPower)
    (hCrenorm : 0 < Crenorm)
    (hlam :
      lam ∈ Ioo 0
        (h.mainCouplingThreshold
          secondPower goodPower Crenorm)) :
    lam ∈ Ioo 0 h.couplingThreshold ∧
      secondPower * lam < 1 ∧
      lam ≤ 1 ∧
      goodPower * lam ≤
        PartialPairing.boundaryGeometricRatio ∧
      Crenorm * lam ≤
        PartialPairing.boundaryGeometricRatio := by
  let D : ℝ := goodPower + Crenorm + 1
  have hD : 0 < D := by
    dsimp only [D]
    linarith
  have hthreshold :
      lam <
        min h.couplingThreshold
          (min (1 / (2 * secondPower))
            (min 1
              (PartialPairing.boundaryGeometricRatio / D))) := by
    simpa only [mainCouplingThreshold, D] using hlam.2
  have hsplit := lt_min_iff.mp hthreshold
  have hbaseLt : lam < h.couplingThreshold :=
    hsplit.1
  have hsecondLt : lam < 1 / (2 * secondPower) :=
    (lt_min_iff.mp hsplit.2).1
  have htail :=
    (lt_min_iff.mp (lt_min_iff.mp hsplit.2).2)
  have hlamLtOne : lam < 1 :=
    htail.1
  have hlamLtBoundaryQuot :
      lam < PartialPairing.boundaryGeometricRatio / D :=
    htail.2
  have hsecondDen : 0 < 2 * secondPower :=
    mul_pos (by norm_num) hsecond
  have hsecondMul :
      lam * (2 * secondPower) < 1 :=
    (lt_div_iff₀ hsecondDen).mp hsecondLt
  have hsecondRatio : secondPower * lam < 1 := by
    nlinarith
  have hlamNonneg : 0 ≤ lam :=
    hlam.1.le
  have hlamLeOne : lam ≤ 1 :=
    hlamLtOne.le
  have hlamLeBoundaryQuot :
      lam ≤ PartialPairing.boundaryGeometricRatio / D :=
    hlamLtBoundaryQuot.le
  have hDlam :
      D * lam ≤ PartialPairing.boundaryGeometricRatio := by
    have h :=
      (le_div_iff₀ hD).mp hlamLeBoundaryQuot
    simpa only [mul_comm] using h
  have hgoodLeD : goodPower ≤ D := by
    dsimp only [D]
    linarith
  have hCrenormLeD : Crenorm ≤ D := by
    dsimp only [D]
    linarith
  have hgoodRatio :
      goodPower * lam ≤
        PartialPairing.boundaryGeometricRatio :=
    (mul_le_mul_of_nonneg_right hgoodLeD hlamNonneg).trans
      hDlam
  have hCrenormRatio :
      Crenorm * lam ≤
        PartialPairing.boundaryGeometricRatio :=
    (mul_le_mul_of_nonneg_right hCrenormLeD hlamNonneg).trans
      hDlam
  exact
    ⟨⟨hlam.1, hbaseLt⟩, hsecondRatio, hlamLeOne,
      hgoodRatio, hCrenormRatio⟩

/-- The common range is contained in the external Proposition 3.6
range. -/
theorem mem_couplingThreshold_of_mem_mainCouplingThreshold
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ)
    {secondPower goodPower Crenorm lam : ℝ}
    (hsecond : 0 < secondPower)
    (hgood : 0 < goodPower)
    (hCrenorm : 0 < Crenorm)
    (hlam :
      lam ∈ Ioo 0
        (h.mainCouplingThreshold
          secondPower goodPower Crenorm)) :
    lam ∈ Ioo 0 h.couplingThreshold :=
  (h.mainCouplingThreshold_spec
    hsecond hgood hCrenorm hlam).1

/-- The second-moment geometric ratio is strictly subcritical on the
common range. -/
theorem secondPower_mul_lt_one_of_mem_mainCouplingThreshold
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ)
    {secondPower goodPower Crenorm lam : ℝ}
    (hsecond : 0 < secondPower)
    (hgood : 0 < goodPower)
    (hCrenorm : 0 < Crenorm)
    (hlam :
      lam ∈ Ioo 0
        (h.mainCouplingThreshold
          secondPower goodPower Crenorm)) :
    secondPower * lam < 1 :=
  (h.mainCouplingThreshold_spec
    hsecond hgood hCrenorm hlam).2.1

/-- Couplings in the common range are at most one. -/
theorem le_one_of_mem_mainCouplingThreshold
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ)
    {secondPower goodPower Crenorm lam : ℝ}
    (hsecond : 0 < secondPower)
    (hgood : 0 < goodPower)
    (hCrenorm : 0 < Crenorm)
    (hlam :
      lam ∈ Ioo 0
        (h.mainCouplingThreshold
          secondPower goodPower Crenorm)) :
    lam ≤ 1 :=
  (h.mainCouplingThreshold_spec
    hsecond hgood hCrenorm hlam).2.2.1

/-- The good-event power ratio lies below the fixed boundary ratio on
the common range. -/
theorem goodPower_mul_le_boundaryGeometricRatio_of_mem_mainCouplingThreshold
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ)
    {secondPower goodPower Crenorm lam : ℝ}
    (hsecond : 0 < secondPower)
    (hgood : 0 < goodPower)
    (hCrenorm : 0 < Crenorm)
    (hlam :
      lam ∈ Ioo 0
        (h.mainCouplingThreshold
          secondPower goodPower Crenorm)) :
    goodPower * lam ≤
      PartialPairing.boundaryGeometricRatio :=
  (h.mainCouplingThreshold_spec
    hsecond hgood hCrenorm hlam).2.2.2.1

/-- The renormalization ratio lies below the fixed boundary ratio on
the common range. -/
theorem Crenorm_mul_le_boundaryGeometricRatio_of_mem_mainCouplingThreshold
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ)
    {secondPower goodPower Crenorm lam : ℝ}
    (hsecond : 0 < secondPower)
    (hgood : 0 < goodPower)
    (hCrenorm : 0 < Crenorm)
    (hlam :
      lam ∈ Ioo 0
        (h.mainCouplingThreshold
          secondPower goodPower Crenorm)) :
    Crenorm * lam ≤
      PartialPairing.boundaryGeometricRatio :=
  (h.mainCouplingThreshold_spec
    hsecond hgood hCrenorm hlam).2.2.2.2

end Prop36Family

end

end Anderson4D
