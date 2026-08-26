import Anderson4D.Parametrix.L2OneSidedGoodEvent

/-!
# Fourier coefficients of the Fredholm resolvent

The coefficient called `modeHcoeff` in the original coefficient layer is
the totalized Neumann tail.  It agrees with the inverse resolvent only in
a regime where that Neumann expansion is known to converge.  In
particular, Fredholm invertibility of `1 - K` alone does not imply such
convergence.

This file gives the operator-route coefficient which is valid on the
one-sided Fredholm good event.  The normalization is chosen so that it
agrees with `modeHcoeff` whenever the existing norm-small Neumann bridge
does apply:

`Ĥ(α,β) = |T⁴| / λ_ε · ⟪e_{-α}, (G_ε-G)e_β⟫`.

No smallness assumption on `‖K‖` occurs in the Fredholm statements below.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

/-- The true resolvent Fourier coefficient, totalized to zero off the
invertibility locus.  This is the operator-route replacement for using an
unconditionally totalized Neumann series as the definition of the full
resolvent. -/
def fredholmModeHcoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω) : ℂ :=
  ((paperTorusVolume : ℂ) * (lamEps lam ε : ℂ)⁻¹) *
    torusOperatorModeCoeffH M ρ lam ε α β ω

/-- The totalized ring inverse is Borel measurable on the Banach algebra
of torus operators.  It is continuous on the open unit locus and is
identically zero on its closed complement. -/
theorem measurable_ringInverse_torusL2Operator :
    Measurable
      (Ring.inverse :
        (TorusL2 →L[ℂ] TorusL2) →
          (TorusL2 →L[ℂ] TorusL2)) := by
  classical
  let unitsSet : Set (TorusL2 →L[ℂ] TorusL2) :=
    {A | IsUnit A}
  have hunits : MeasurableSet unitsSet :=
    Units.isOpen.measurableSet
  have hinv :
      ContinuousOn
        (Ring.inverse :
          (TorusL2 →L[ℂ] TorusL2) →
            (TorusL2 →L[ℂ] TorusL2))
        unitsSet := by
    intro A hA
    have hcontinuous :=
      NormedRing.inverse_continuousAt hA.unit
    rw [hA.unit_spec] at hcontinuous
    exact hcontinuous.continuousWithinAt
  have hpiece :
      Measurable
        (unitsSet.piecewise Ring.inverse
          (fun _ => (0 : TorusL2 →L[ℂ] TorusL2))) :=
    hinv.measurable_piecewise continuousOn_const hunits
  convert hpiece using 1
  funext A
  by_cases hA : IsUnit A
  · simp [unitsSet, hA]
  · simp [unitsSet, hA, Ring.inverse_non_unit]

/-- A manifestly measurable version of the recentered Fredholm
resolvent.  It uses the preferred measurable realization of the random
potential and is zero off the open invertibility locus. -/
def measurableFredholmRecenteredInverse
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) :
    TorusL2 →L[ℂ] TorusL2 := by
  classical
  exact
    if IsUnit (1 - measurableAndersonK M ρ lam ε ω) then
      Ring.inverse (1 - measurableAndersonK M ρ lam ε ω) *
          greenL2Op -
        greenL2Op
    else 0

theorem measurable_measurableFredholmRecenteredInverse
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) :
    Measurable
      (measurableFredholmRecenteredInverse M ρ lam ε) := by
  classical
  have hA :
      Measurable
        (fun ω : M.Ω =>
          (1 : TorusL2 →L[ℂ] TorusL2) -
            measurableAndersonK M ρ lam ε ω) :=
    ((continuous_const.sub continuous_id).measurable).comp
      (measurable_measurableAndersonK M ρ lam ε)
  have hunits :
      MeasurableSet
        {ω : M.Ω |
          IsUnit
            ((1 : TorusL2 →L[ℂ] TorusL2) -
              measurableAndersonK M ρ lam ε ω)} :=
    Units.isOpen.measurableSet.preimage hA
  unfold measurableFredholmRecenteredInverse
  exact Measurable.ite hunits
    (((continuous_id.mul continuous_const).sub
      continuous_const).measurable.comp
        (measurable_ringInverse_torusL2Operator.comp hA))
    measurable_const

/-- The measurable full Fredholm coefficient. -/
def measurableFredholmModeHcoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω) : ℂ :=
  ((paperTorusVolume : ℂ) * (lamEps lam ε : ℂ)⁻¹) *
    torusFourierMatrixCoeff
      (measurableFredholmRecenteredInverse M ρ lam ε ω)
      α β

theorem measurable_measurableFredholmModeHcoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) :
    Measurable
      (measurableFredholmModeHcoeff
        M ρ lam ε α β) := by
  unfold measurableFredholmModeHcoeff
  exact measurable_const.mul
    ((torusFourierMatrixCoeffCLM α β).measurable.comp
      (measurable_measurableFredholmRecenteredInverse
        M ρ lam ε))

/-- The measurable realization agrees almost surely with the samplewise
Fredholm coefficient at every positive mollification scale. -/
theorem ae_measurableFredholmModeHcoeff_eq_fredholmModeHcoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (α β : Z4) :
    measurableFredholmModeHcoeff M ρ lam ε α β =ᵐ[
        (volume : Measure M.Ω)]
      fredholmModeHcoeff M ρ lam ε α β := by
  classical
  filter_upwards
    [ae_measurableAndersonK_eq_andersonK
      M ρ lam hε] with ω hK
  unfold measurableFredholmModeHcoeff fredholmModeHcoeff
    measurableFredholmRecenteredInverse
    torusOperatorModeCoeffH andersonRecenteredInverse
    torusFourierMatrixCoeff
  rw [hK]
  by_cases hinv :
      LopInvertible greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)
  · have hinvK :
        IsUnit (1 - andersonK M ρ lam ε ω) := by
      simpa [LopInvertible, andersonK] using hinv
    rw [if_pos hinvK, dif_pos hinv]
    unfold inverseGreen
    rw [Ring.inverse_of_isUnit hinvK]
    have hunit : hinvK.unit = hinv.unit := by
      apply Units.ext
      rw [hinvK.unit_spec, hinv.unit_spec]
      rfl
    rw [hunit]
    simp only [coe_torusFourierBasis]
  · have hinvK :
        ¬ IsUnit (1 - andersonK M ρ lam ε ω) := by
      simpa [LopInvertible, andersonK] using hinv
    rw [if_neg hinvK, dif_neg hinv]
    simp

theorem aemeasurable_fredholmModeHcoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (α β : Z4) :
    AEMeasurable
      (fredholmModeHcoeff M ρ lam ε α β)
      (volume : Measure M.Ω) :=
  (measurable_measurableFredholmModeHcoeff
      M ρ lam ε α β).aemeasurable.congr
    (ae_measurableFredholmModeHcoeff_eq_fredholmModeHcoeff
      M ρ lam hε α β)

/-- A finite real Fourier test of the true samplewise Fredholm
resolvent. -/
def fredholmFiniteModeReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) (ω : M.Ω) : ℝ :=
  (∑ j, c j *
    fredholmModeHcoeff M ρ lam ε
      (modes j).1 (modes j).2 ω).re

/-- The manifestly measurable version of the same finite Fourier test. -/
def measurableFredholmFiniteModeReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) (ω : M.Ω) : ℝ :=
  (∑ j, c j *
    measurableFredholmModeHcoeff M ρ lam ε
      (modes j).1 (modes j).2 ω).re

theorem measurable_measurableFredholmFiniteModeReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) :
    Measurable
      (measurableFredholmFiniteModeReal
        M ρ lam ε s modes c) := by
  unfold measurableFredholmFiniteModeReal
  apply Complex.measurable_re.comp
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul
    (measurable_measurableFredholmModeHcoeff
      M ρ lam ε (modes j).1 (modes j).2)

theorem ae_measurableFredholmFiniteModeReal_eq_fredholmFiniteModeReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) :
    measurableFredholmFiniteModeReal
        M ρ lam ε s modes c =ᵐ[(volume : Measure M.Ω)]
      fredholmFiniteModeReal M ρ lam ε s modes c := by
  have hall :
      ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ j : Fin s,
        measurableFredholmModeHcoeff
            M ρ lam ε (modes j).1 (modes j).2 ω =
          fredholmModeHcoeff
            M ρ lam ε (modes j).1 (modes j).2 ω := by
    have hallFinset :=
      (Filter.eventually_all_finset Finset.univ).2
        (fun j _ =>
        ae_measurableFredholmModeHcoeff_eq_fredholmModeHcoeff
          M ρ lam hε (modes j).1 (modes j).2)
    filter_upwards [hallFinset] with ω hω
    intro j
    exact hω j (Finset.mem_univ j)
  filter_upwards [hall] with ω hω
  unfold measurableFredholmFiniteModeReal fredholmFiniteModeReal
  congr 2
  funext j
  rw [hω j]

/-- A signed Fourier matrix coefficient is bounded by the operator norm.
Both Fourier basis vectors have norm one. -/
theorem norm_torusFourierMatrixCoeff_le
    (A : TorusL2 →L[ℂ] TorusL2) (α β : Z4) :
    ‖torusFourierMatrixCoeff A α β‖ ≤ ‖A‖ := by
  calc
    ‖torusFourierMatrixCoeff A α β‖ =
        ‖⟪torusFourierBasis (-α),
          A (torusFourierBasis β)⟫_ℂ‖ := rfl
    _ ≤ ‖torusFourierBasis (-α)‖ *
        ‖A (torusFourierBasis β)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖torusFourierBasis (-α)‖ *
        (‖A‖ * ‖torusFourierBasis β‖) := by
      gcongr
      exact A.le_opNorm _
    _ = ‖A‖ := by
      rw [torusFourierBasis.orthonormal.norm_eq_one,
        torusFourierBasis.orthonormal.norm_eq_one]
      ring

/-- On any invertible sample, `fredholmModeHcoeff` is literally the
normalized matrix coefficient of the selected two-sided inverse.  The
statement is proof-independent because `LopInvertible` is a proposition. -/
theorem fredholmModeHcoeff_eq_inverseGreen
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω)
    (hinv :
      LopInvertible greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)) :
    fredholmModeHcoeff M ρ lam ε α β ω =
      ((paperTorusVolume : ℂ) * (lamEps lam ε : ℂ)⁻¹) *
        torusFourierMatrixCoeff
          (inverseGreen greenL2Op
              (mollifiedPotentialL2Op M ρ lam ε ω) hinv -
            greenL2Op)
          α β := by
  unfold fredholmModeHcoeff torusOperatorModeCoeffH
    andersonRecenteredInverse torusFourierMatrixCoeff
  rw [dif_pos hinv]
  simp only [coe_torusFourierBasis]

/-- In the norm-small regime, where the Neumann tail is genuinely
summable, the Fredholm/operator route agrees with the original
coefficient route.  This is a compatibility theorem, not a hypothesis
used by the one-sided Fredholm bridge. -/
theorem fredholmModeHcoeff_eq_modeHcoeff_of_norm_lt_one
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω)
    (hK : ‖andersonK M ρ lam ε ω‖ < 1)
    (hLam : lamEps lam ε ≠ 0)
    (hAction : ∀ n : ℕ,
      NeumannTermKernelAction M ρ lam ε (n + 1) β ω) :
    fredholmModeHcoeff M ρ lam ε α β ω =
      modeHcoeff M ρ lam ε α β ω := by
  unfold fredholmModeHcoeff
  rw [torusOperatorModeCoeffH_eq_scaled_modeHcoeff
    M ρ lam ε α β ω hK hLam hAction]
  field_simp [hLam, paperTorusVolume_ne_zero]
  simp only [Complex.real_smul, Complex.ofReal_div]
  field_simp [paperTorusVolume_ne_zero]

/-- Operator-norm proximity to a physical parametrix gives the correctly
normalized fixed-mode proximity to the true Fredholm resolvent. -/
theorem norm_parametrixCoeff_sub_fredholmModeHcoeff_le
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω)
    (P : TorusL2 →L[ℂ] TorusL2)
    (hinv :
      LopInvertible greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)) :
    ‖((paperTorusVolume : ℂ) * (lamEps lam ε : ℂ)⁻¹) *
          torusFourierMatrixCoeff (P - greenL2Op) α β -
        fredholmModeHcoeff M ρ lam ε α β ω‖ ≤
      ‖(paperTorusVolume : ℂ) * (lamEps lam ε : ℂ)⁻¹‖ *
        ‖P -
          inverseGreen greenL2Op
            (mollifiedPotentialL2Op M ρ lam ε ω) hinv‖ := by
  rw [fredholmModeHcoeff_eq_inverseGreen
    M ρ lam ε α β ω hinv]
  rw [← mul_sub]
  have hcoeff :
      torusFourierMatrixCoeff (P - greenL2Op) α β -
          torusFourierMatrixCoeff
            (inverseGreen greenL2Op
                (mollifiedPotentialL2Op M ρ lam ε ω) hinv -
              greenL2Op)
            α β =
        torusFourierMatrixCoeff
          (P -
            inverseGreen greenL2Op
              (mollifiedPotentialL2Op M ρ lam ε ω) hinv)
          α β := by
    unfold torusFourierMatrixCoeff
    simp only [sub_apply, inner_sub_right]
    ring
  rw [hcoeff, norm_mul]
  gcongr
  exact norm_torusFourierMatrixCoeff_le _ α β

/-- The normalized positive-order coefficient of the finite physical
parametrix.  This is the single-mode summand used by the moving
truncation, kept here in a parametrix-layer form. -/
def truncatedParametrixModeHcoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (α β : Z4) (ω : M.Ω) : ℂ :=
  (lamEps lam ε : ℂ)⁻¹ *
    ∑ n : Fin A,
      pmCoeff M ρ lam ε (n + 1) α β ω

/-- The finite real Fourier test of the physical parametrix. -/
def truncatedParametrixFiniteModeReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) (ω : M.Ω) : ℝ :=
  (∑ j, c j *
    truncatedParametrixModeHcoeff M ρ lam ε A
      (modes j).1 (modes j).2 ω).re

/-- The finite physical parametrix is `G` plus its canonical
positive-order operator. -/
theorem canonicalPhysicalTruncatedParametrixL2Operator_sub_green
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (ω : M.Ω) :
    canonicalPhysicalTruncatedParametrixL2Operator
          M ρ lam ε A ω -
        greenL2Op =
      canonicalPositiveTruncatedParametrixL2Operator
        M ρ lam ε A ω := by
  rw [PartialPairing.canonicalPhysicalTruncatedParametrixL2Operator_eq]
  unfold canonicalPositiveTruncatedParametrixL2Operator
  abel

/-- Exact normalization ledger between the positive physical operator
and the finite coefficient truncation. -/
theorem scaled_canonicalPhysicalCoeff_eq_truncatedParametrixModeHcoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (α β : Z4) (ω : M.Ω)
    (hcoeff :
      torusFourierMatrixCoeff
          (canonicalPositiveTruncatedParametrixL2Operator
            M ρ lam ε A ω)
          α β =
        (paperTorusVolume : ℂ)⁻¹ *
          ∑ n ∈ Finset.range A,
            pmCoeff M ρ lam ε (n + 1) α β ω) :
    ((paperTorusVolume : ℂ) * (lamEps lam ε : ℂ)⁻¹) *
        torusFourierMatrixCoeff
          (canonicalPhysicalTruncatedParametrixL2Operator
              M ρ lam ε A ω -
            greenL2Op)
          α β =
      truncatedParametrixModeHcoeff
        M ρ lam ε A α β ω := by
  rw [canonicalPhysicalTruncatedParametrixL2Operator_sub_green,
    hcoeff]
  unfold truncatedParametrixModeHcoeff
  rw [Fin.sum_univ_eq_sum_range
    (fun n =>
      pmCoeff M ρ lam ε (n + 1) α β ω)]
  field_simp [paperTorusVolume_ne_zero]

/-- **Fredholm fixed-mode replacement.**  On the paper's one-sided good
event, the normalized finite parametrix coefficient is close to the true
inverse-resolvent coefficient.  The proof uses only the Fredholm inverse
constructed from the small residual; there is no assumption on `‖K‖`.

The coefficient-realization premise is the already-proved almost-sure
output of `canonicalPositiveTruncatedParametrixL2Operator_coeff`; callers
may intersect that full-measure set with the quantitative good event. -/
theorem
    norm_truncatedParametrixModeHcoeff_sub_fredholmModeHcoeff_le_on_good
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ)
    (Qfactor Rleft :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
    (α β : Z4) (ω : M.Ω)
    (hεpos : 0 < ε)
    (hεsmall : 2 * ε ^ 2 ≤ 1)
    (hεpow : ε ^ 28 < 1 / 2)
    (hω : ω ∈ PartialPairing.canonicalOneSidedL2ParametrixGoodEvent
      M ρ lam ε A Qfactor Rleft)
    (hcoeff :
      torusFourierMatrixCoeff
          (canonicalPositiveTruncatedParametrixL2Operator
            M ρ lam ε A ω)
          α β =
        (paperTorusVolume : ℂ)⁻¹ *
          ∑ n ∈ Finset.range A,
            pmCoeff M ρ lam ε (n + 1) α β ω) :
    ‖truncatedParametrixModeHcoeff
          M ρ lam ε A α β ω -
        fredholmModeHcoeff M ρ lam ε α β ω‖ ≤
      ‖(paperTorusVolume : ℂ) *
          (lamEps lam ε : ℂ)⁻¹‖ * ε ^ 12 := by
  let hinv :
      LopInvertible greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω) :=
    PartialPairing.lopInvertible_on_canonicalOneSidedL2ParametrixGoodEvent
      M ρ lam ε A Qfactor Rleft hεpow hω
  have hop :
      ‖canonicalPhysicalTruncatedParametrixL2Operator
            M ρ lam ε A ω -
          inverseGreen greenL2Op
            (mollifiedPotentialL2Op M ρ lam ε ω) hinv‖ ≤
        ε ^ 12 := by
    rw [norm_sub_rev]
    exact
      PartialPairing.norm_inverseGreen_sub_canonicalParametrix_on_oneSidedGoodEvent
        M ρ lam ε A Qfactor Rleft
        hεpos hεsmall hεpow hω
  rw [←
    scaled_canonicalPhysicalCoeff_eq_truncatedParametrixModeHcoeff
      M ρ lam ε A α β ω hcoeff]
  exact
    (norm_parametrixCoeff_sub_fredholmModeHcoeff_le
      M ρ lam ε α β ω
      (canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω)
      hinv).trans
      (mul_le_mul_of_nonneg_left hop (norm_nonneg _))

/-- Finite-family form of the Fredholm replacement estimate. -/
theorem
    norm_truncatedParametrixFiniteModeReal_sub_fredholmFiniteModeReal_le_on_good
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ)
    (Qfactor Rleft :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) (ω : M.Ω)
    (hεpos : 0 < ε)
    (hεsmall : 2 * ε ^ 2 ≤ 1)
    (hεpow : ε ^ 28 < 1 / 2)
    (hω : ω ∈ PartialPairing.canonicalOneSidedL2ParametrixGoodEvent
      M ρ lam ε A Qfactor Rleft)
    (hcoeff :
      ∀ j : Fin s,
        torusFourierMatrixCoeff
            (canonicalPositiveTruncatedParametrixL2Operator
              M ρ lam ε A ω)
            (modes j).1 (modes j).2 =
          (paperTorusVolume : ℂ)⁻¹ *
            ∑ n ∈ Finset.range A,
              pmCoeff M ρ lam ε (n + 1)
                (modes j).1 (modes j).2 ω) :
    ‖truncatedParametrixFiniteModeReal
          M ρ lam ε A s modes c ω -
        fredholmFiniteModeReal
          M ρ lam ε s modes c ω‖ ≤
      ∑ j : Fin s, ‖c j‖ *
        (‖(paperTorusVolume : ℂ) *
            (lamEps lam ε : ℂ)⁻¹‖ * ε ^ 12) := by
  have hmode (j : Fin s) :
      ‖truncatedParametrixModeHcoeff
            M ρ lam ε A (modes j).1 (modes j).2 ω -
          fredholmModeHcoeff
            M ρ lam ε (modes j).1 (modes j).2 ω‖ ≤
        ‖(paperTorusVolume : ℂ) *
            (lamEps lam ε : ℂ)⁻¹‖ * ε ^ 12 :=
    norm_truncatedParametrixModeHcoeff_sub_fredholmModeHcoeff_le_on_good
      M ρ lam ε A Qfactor Rleft
      (modes j).1 (modes j).2 ω
      hεpos hεsmall hεpow hω (hcoeff j)
  let X : ℂ :=
    ∑ j : Fin s, c j *
      truncatedParametrixModeHcoeff
        M ρ lam ε A (modes j).1 (modes j).2 ω
  let Y : ℂ :=
    ∑ j : Fin s, c j *
      fredholmModeHcoeff
        M ρ lam ε (modes j).1 (modes j).2 ω
  change ‖X.re - Y.re‖ ≤ _
  rw [← Complex.sub_re]
  calc
    ‖(X - Y).re‖ ≤ ‖X - Y‖ :=
      Complex.abs_re_le_norm _
    _ =
        ‖∑ j : Fin s, c j *
          (truncatedParametrixModeHcoeff
              M ρ lam ε A (modes j).1 (modes j).2 ω -
            fredholmModeHcoeff
              M ρ lam ε (modes j).1 (modes j).2 ω)‖ := by
      dsimp only [X, Y]
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤
        ∑ j : Fin s, ‖c j *
          (truncatedParametrixModeHcoeff
              M ρ lam ε A (modes j).1 (modes j).2 ω -
            fredholmModeHcoeff
              M ρ lam ε (modes j).1 (modes j).2 ω)‖ :=
      norm_sum_le _ _
    _ =
        ∑ j : Fin s, ‖c j‖ *
          ‖truncatedParametrixModeHcoeff
              M ρ lam ε A (modes j).1 (modes j).2 ω -
            fredholmModeHcoeff
              M ρ lam ε (modes j).1 (modes j).2 ω‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul]
    _ ≤
        ∑ j : Fin s, ‖c j‖ *
          (‖(paperTorusVolume : ℂ) *
              (lamEps lam ε : ℂ)⁻¹‖ * ε ^ 12) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (hmode j) (norm_nonneg (c j))

end

end Anderson4D
