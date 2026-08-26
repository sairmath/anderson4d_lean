import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorCoreProof
import Anderson4D.DetParametrix.Paper42_Moment.R324HighFrequencyProof

/-!
# The interior-core logarithmic budget at the base order (`m = 1`)

The proved keyed `L¹` interface provably cannot reach the
`ε`-uniform interior-core budget: at `m = 1` its marked slot series is
bounded below by `∑ ⟨k⟩⁸‖ρ̂(εk)‖² ≍ ε⁻¹²`.  This file establishes the
budget at the base order `m = 1` through the *physical* route instead:
the interior Green skeleton of a one-vertex copy is the empty product,
so the whole interior `L¹` mass is the covariance mass
`∫∫ η_ε(v₀−v₁) ≤ (2π)⁸`, which is `ε`-uniform because the periodized
covariance has total mass `‖ρ̂(0)‖² ≤ 1` at every scale.

* `integral_etaEpsT4_paper_le_one` — the total covariance mass, read
  off the absolutely convergent Fourier series: only the zero mode
  survives integration, and its coefficient is `⟨2π⟩⁻⁴‖ρ̂(0)‖²·(2π)⁴`.
* `r324InteriorCoreLogBudget_base` — `R324InteriorCoreLogBudget ρ ε 1 C`
  at the explicit `ε`-uniform constant `C = 4·(2π)⁴`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Total `paperMeasure` mass of the torus. -/
theorem paperMeasure_univ :
    paperMeasure (Set.univ : Set T4) =
      ENNReal.ofReal ((2 * Real.pi) ^ (dim : ℕ)) := by
  unfold paperMeasure haarT4
  rw [Measure.smul_apply, Measure.pi_univ]
  simp [measure_univ]

/-- The Lebesgue/probability-Haar normalization identity
`whiteNoiseFourierScale² · (2π)⁴ = 1`, in real form. -/
theorem whiteNoiseFourierScale_sq_mul_pow_dim :
    NoiseModel.whiteNoiseFourierScale ^ 2 *
      (2 * Real.pi) ^ (dim : ℕ) = 1 := by
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : NoiseModel.whiteNoiseFourierScale =
      ((2 * Real.pi) ^ (2 : ℕ))⁻¹ := by
    unfold NoiseModel.whiteNoiseFourierScale
    rw [zpow_neg]
    norm_cast
  rw [h1]
  show (((2 * Real.pi) ^ (2 : ℕ))⁻¹) ^ 2 *
    (2 * Real.pi) ^ (4 : ℕ) = 1
  field_simp

/-- **`ε`-uniform total covariance mass.**  The periodized mollified
covariance integrates to `‖ρ̂(0)‖² ≤ 1` at every scale `0 < ε`: in the
absolutely convergent covariance Fourier series only the zero mode
survives the integration. -/
theorem integral_etaEpsT4_paper_le_one
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, ρ.etaEpsT4 ε z ∂paperMeasure ≤ 1 := by
  set V : ℝ := (2 * Real.pi) ^ (dim : ℕ) with hVdef
  have hV0 : 0 < V := by rw [hVdef]; positivity
  have hint : ∀ k : Z4,
      Integrable
        (fun z : T4 => ρ.covarianceModeCoeff ε k * charT4 k z)
        paperMeasure := by
    intro k
    refine (integrable_const
      ‖ρ.covarianceModeCoeff ε k‖).mono'
      (Continuous.aestronglyMeasurable ?_) ?_
    · exact continuous_const.mul (continuous_charT4 k)
    · filter_upwards with z
      rw [norm_mul, norm_charT4, mul_one]
  have hnormint : ∀ k : Z4,
      (∫ z, ‖ρ.covarianceModeCoeff ε k * charT4 k z‖
        ∂paperMeasure) = V * ‖ρ.covarianceModeCoeff ε k‖ := by
    intro k
    have hfun :
        (fun z : T4 =>
          ‖ρ.covarianceModeCoeff ε k * charT4 k z‖) =
        fun _ : T4 => ‖ρ.covarianceModeCoeff ε k‖ := by
      funext z
      rw [norm_mul, norm_charT4, mul_one]
    rw [hfun, integral_const, measureReal_def, paperMeasure_univ,
      ENNReal.toReal_ofReal hV0.le, smul_eq_mul]
  have hsummable :
      Summable fun k : Z4 =>
        ∫ z, ‖ρ.covarianceModeCoeff ε k * charT4 k z‖
          ∂paperMeasure := by
    refine ((ρ.summable_norm_covarianceModeCoeff hε).mul_left
      V).congr fun k => ?_
    rw [hnormint k]
  have hswap :=
    integral_tsum_of_summable_integral_norm hint hsummable
  have hseries :
      (∫ z : T4,
        ∑' k : Z4, ρ.covarianceModeCoeff ε k * charT4 k z
        ∂paperMeasure) =
      ((∫ z, ρ.etaEpsT4 ε z ∂paperMeasure : ℝ) : ℂ) := by
    rw [show
        (fun z : T4 =>
          ∑' k : Z4, ρ.covarianceModeCoeff ε k * charT4 k z) =
        fun z : T4 => ((ρ.etaEpsT4 ε z : ℝ) : ℂ) from
      funext fun z =>
        ρ.complexFourierCovarianceT4_eq_etaEpsT4 hε z]
    exact integral_ofReal
  have hRHS :
      (∑' k : Z4,
        ∫ z, ρ.covarianceModeCoeff ε k * charT4 k z
          ∂paperMeasure) =
      ρ.covarianceModeCoeff ε 0 * ((V : ℝ) : ℂ) := by
    have hterm : ∀ k : Z4,
        (∫ z, ρ.covarianceModeCoeff ε k * charT4 k z
          ∂paperMeasure) =
        ρ.covarianceModeCoeff ε k *
          (if k = 0 then ((V : ℝ) : ℂ) else 0) := by
      intro k
      rw [integral_const_mul, integral_charT4_paper]
    rw [tsum_congr hterm]
    exact tsum_eq_single 0 fun k hk => by
      rw [if_neg hk, mul_zero]
  have hmass :
      ((∫ z, ρ.etaEpsT4 ε z ∂paperMeasure : ℝ) : ℂ) =
      ((NoiseModel.whiteNoiseFourierScale ^ 2 *
        ‖ρ.symbol ε 0‖ ^ 2 * V : ℝ) : ℂ) := by
    rw [← hseries, ← hswap, hRHS]
    unfold SmoothCutoff.covarianceModeCoeff
    push_cast
    ring
  have hmassR :
      (∫ z, ρ.etaEpsT4 ε z ∂paperMeasure) =
      NoiseModel.whiteNoiseFourierScale ^ 2 *
        ‖ρ.symbol ε 0‖ ^ 2 * V :=
    Complex.ofReal_injective hmass
  rw [hmassR]
  have hsymbol : ‖ρ.symbol ε 0‖ ^ 2 ≤ 1 := by
    have h := ρ.norm_symbol_le_one ε 0
    nlinarith [norm_nonneg (ρ.symbol ε 0)]
  calc
    NoiseModel.whiteNoiseFourierScale ^ 2 *
        ‖ρ.symbol ε 0‖ ^ 2 * V ≤
        NoiseModel.whiteNoiseFourierScale ^ 2 * 1 * V := by
      gcongr
    _ = 1 := by
      rw [mul_one, hVdef]
      exact whiteNoiseFourierScale_sq_mul_pow_dim

/-! ## The base order `m = 1`: structure -/

instance : Subsingleton (PartialPairing (Fin 1)) :=
  ⟨fun a b => PartialPairing.ext fun i => Subsingleton.elim (a i) (b i)⟩

instance : Subsingleton (MomentContraction 1) := by
  constructor
  rintro ⟨κp, κm, π⟩ ⟨κp', κm', π'⟩
  obtain rfl : κp = κp' := Subsingleton.elim _ _
  obtain rfl : κm = κm' := Subsingleton.elim _ _
  have hπ : π = π' := Equiv.ext fun i => Subsingleton.elim _ _
  rw [hπ]

/-- A one-vertex copy has no interior Green edge: its renormalized
interior core is the empty product. -/
theorem r324RenormalizedInteriorCore_one
    (κ : PartialPairing (Fin 1)) (v : Fin 1 → T4) :
    r324RenormalizedInteriorCore κ v = 1 := by
  unfold r324RenormalizedInteriorCore
  have h :
      (((Finset.univ : Finset (Fin (1 + 1))).erase 0).erase
        (Fin.last 1)) = ∅ := by decide
  rw [h, Finset.prod_empty]

/-- On the doubled carrier of the base order, an involution either has
no ordered pair slot or exactly the slot `0 ↦ 1`. -/
theorem pairSlot_classification_two
    (κ : PartialPairing (Fin (2 * 1))) :
    κ.pairSupport.filter (fun i => i < κ i) = ∅ ∨
      (κ.pairSupport.filter (fun i => i < κ i) = {0} ∧ κ 0 = 1) := by
  have hval : ∀ i : Fin (2 * 1), (κ i).val < 2 := fun i => (κ i).isLt
  have hone : ∀ i : Fin (2 * 1), ¬ ((1 : Fin (2 * 1)) < κ i) := by
    intro i hlt
    have h1 : ((1 : Fin (2 * 1)) : ℕ) = 1 := rfl
    have h2 := hval i
    have h3 := Fin.lt_def.mp hlt
    omega
  by_cases h0 : κ 0 = 0
  · left
    refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
    obtain ⟨hp, hlt⟩ := Finset.mem_filter.mp hi
    have hi2 : i.val = 0 ∨ i.val = 1 := by
      have := i.isLt
      omega
    rcases hi2 with h | h
    · have hiz : i = 0 := Fin.ext h
      subst hiz
      rw [h0] at hlt
      exact lt_irrefl _ hlt
    · have hio : i = 1 := Fin.ext h
      subst hio
      exact hone 1 hlt
  · right
    have h01 : κ 0 = 1 := by
      have hv := hval 0
      have h0v : (κ 0).val ≠ 0 := fun h => h0 (Fin.ext h)
      have h1v : ((1 : Fin (2 * 1)) : ℕ) = 1 := rfl
      exact Fin.ext (by omega)
    refine ⟨?_, h01⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_singleton,
      PartialPairing.mem_pairSupport]
    constructor
    · rintro ⟨hp, hlt⟩
      have hi2 : i.val = 0 ∨ i.val = 1 := by
        have := i.isLt
        omega
      rcases hi2 with h | h
      · exact Fin.ext h
      · exact absurd hlt (by
          have hio : i = 1 := Fin.ext h
          subst hio
          exact hone 1)
    · rintro rfl
      refine ⟨fun h => ?_, ?_⟩
      · rw [h01] at h
        exact (by decide : ((1 : Fin (2 * 1)) ≠ 0)) h
      · rw [h01]
        decide

/-- Total mass of the doubled configuration space at the base order. -/
theorem pi_two_paperMeasure_univ :
    (Measure.pi fun _ : Fin (2 * 1) => paperMeasure) Set.univ =
      ENNReal.ofReal ((2 * Real.pi) ^ (dim : ℕ)) ^ (2 : ℕ) := by
  rw [Measure.pi_univ]
  simp only [paperMeasure_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **`ε`-uniform covariance-pair mass on the doubled base carrier.**
For every involution of the two-point carrier, the covariance product
integrates to at most `(2π)⁸`: the empty slot set contributes the raw
volume `(2π)⁸`, and the slot `0 ↦ 1` contributes `(2π)⁴` times the
`ε`-uniform covariance mass. -/
theorem integral_primitiveCovarianceProduct_base_le
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (κ : PartialPairing (Fin (2 * 1))) :
    Integrable
        (fun v : Fin (2 * 1) → T4 =>
          primitiveCovarianceProduct ρ ε 1 κ v)
        (Measure.pi fun _ : Fin (2 * 1) => paperMeasure) ∧
      ∫ v : Fin (2 * 1) → T4,
          primitiveCovarianceProduct ρ ε 1 κ v
          ∂(Measure.pi fun _ : Fin (2 * 1) => paperMeasure) ≤
        (2 * Real.pi) ^ (8 : ℕ) := by
  have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hVtoReal :
      ((Measure.pi fun _ : Fin (2 * 1) => paperMeasure)
        Set.univ).toReal = (2 * Real.pi) ^ (8 : ℕ) := by
    rw [pi_two_paperMeasure_univ, ← ENNReal.ofReal_pow (by positivity),
      ENNReal.toReal_ofReal (by positivity), ← pow_mul]
    norm_num [dim]
  rcases pairSlot_classification_two κ with hS | ⟨hS, hκ0⟩
  · have hfun :
        (fun v : Fin (2 * 1) → T4 =>
          primitiveCovarianceProduct ρ ε 1 κ v) =
        fun _ => (1 : ℝ) := by
      funext v
      unfold primitiveCovarianceProduct
      rw [hS, Finset.prod_empty]
    rw [hfun]
    refine ⟨integrable_const 1, ?_⟩
    rw [integral_const, measureReal_def, hVtoReal, smul_eq_mul, mul_one]
  · have hfun :
        (fun v : Fin (2 * 1) → T4 =>
          primitiveCovarianceProduct ρ ε 1 κ v) =
        fun v : Fin (2 * 1) → T4 =>
          ρ.etaEpsT4 ε (v 0 - v 1) := by
      funext v
      unfold primitiveCovarianceProduct
      rw [hS, Finset.prod_singleton, hκ0]
    rw [hfun]
    obtain ⟨Cη, hCη, hbound⟩ := ρ.exists_pos_etaEpsT4_uniform_bound
    have hmeas : Measurable fun v : Fin (2 * 1) → T4 =>
        ρ.etaEpsT4 ε (v 0 - v 1) :=
      (ρ.measurable_etaEpsT4 ε).comp
        ((measurable_pi_apply 0).sub (measurable_pi_apply 1))
    have hint :
        Integrable
          (fun v : Fin (2 * 1) → T4 => ρ.etaEpsT4 ε (v 0 - v 1))
          (Measure.pi fun _ : Fin (2 * 1) => paperMeasure) := by
      refine (integrable_const (ε⁻¹ ^ (dim : ℕ) * Cη)).mono'
        hmeas.aestronglyMeasurable ?_
      filter_upwards with v
      rw [Real.norm_eq_abs, abs_of_nonneg (ρ.etaEpsT4_nonneg ε _)]
      exact hbound hε hε1 _
    refine ⟨hint, ?_⟩
    have hmassLe := integral_etaEpsT4_paper_le_one ρ hε
    have hmass0 : 0 ≤ ∫ z, ρ.etaEpsT4 ε z ∂paperMeasure :=
      integral_nonneg fun z => ρ.etaEpsT4_nonneg ε z
    have hprodInt :
        Integrable
          (fun p : T4 × T4 => ρ.etaEpsT4 ε (p.1 - p.2))
          (paperMeasure.prod paperMeasure) := by
      refine (integrable_const (ε⁻¹ ^ (dim : ℕ) * Cη)).mono'
        (((ρ.measurable_etaEpsT4 ε).comp
          (measurable_fst.sub measurable_snd)).aestronglyMeasurable) ?_
      filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (ρ.etaEpsT4_nonneg ε _)]
      exact hbound hε hε1 _
    have hpi :
        (∫ v : Fin (2 * 1) → T4, ρ.etaEpsT4 ε (v 0 - v 1)
          ∂(Measure.pi fun _ : Fin (2 * 1) => paperMeasure)) =
        ∫ p : T4 × T4, ρ.etaEpsT4 ε (p.1 - p.2)
          ∂(paperMeasure.prod paperMeasure) :=
      (measurePreserving_piFinTwo
        (fun _ : Fin 2 => paperMeasure)).integral_comp'
        (fun p : T4 × T4 => ρ.etaEpsT4 ε (p.1 - p.2))
    rw [hpi, integral_prod_symm _ hprodInt]
    have hinner : ∀ y : T4,
        (∫ x, ρ.etaEpsT4 ε (x - y) ∂paperMeasure) =
        ∫ z, ρ.etaEpsT4 ε z ∂paperMeasure := by
      intro y
      exact (measurePreserving_sub_paper y).integral_comp
        (MeasurableEquiv.subRight y).measurableEmbedding
        (ρ.etaEpsT4 ε)
    calc
      (∫ y, ∫ x, ρ.etaEpsT4 ε (x - y) ∂paperMeasure ∂paperMeasure) =
          ∫ _y, (∫ z, ρ.etaEpsT4 ε z ∂paperMeasure) ∂paperMeasure := by
        exact integral_congr_ae
          (Filter.Eventually.of_forall fun y => hinner y)
      _ = ((2 * Real.pi) ^ (dim : ℕ)) *
            ∫ z, ρ.etaEpsT4 ε z ∂paperMeasure := by
        rw [integral_const, measureReal_def, paperMeasure_univ,
          ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
      _ ≤ ((2 * Real.pi) ^ (dim : ℕ)) * 1 :=
        mul_le_mul_of_nonneg_left hmassLe (by positivity)
      _ ≤ (2 * Real.pi) ^ (8 : ℕ) := by
        rw [mul_one]
        exact pow_le_pow_right₀ hπ1 (by norm_num [dim])

/-- **The interior-core logarithmic budget at the base order, at an
explicit `ε`-uniform constant.**  `R324InteriorCoreLogBudget ρ ε 1 C`
holds with `C = 4·(2π)⁴`: the base-order interior core has no Green
edge, so its `L¹` mass is a covariance-pair mass, which is `ε`-uniform.
The keyed `L¹` interface, by contrast, has a marked-slot
series bounded below by `≍ ε⁻¹²` at this order. -/
theorem r324InteriorCoreLogBudget_base
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    R324InteriorCoreLogBudget ρ ε 1
      (4 * (2 * Real.pi) ^ (4 : ℕ)) := by
  intro p
  set rep : MomentContraction 1 :=
    r324RefinedScheduleRepresentative p with hrepdef
  set g : (Fin (2 * 1) → T4) → ℝ := fun v =>
    primitiveCovarianceProduct ρ ε 1
      (momentCombinedPairing rep.1 rep.2.1 rep.2.2) v with hgdef
  obtain ⟨hgint, hgle⟩ :=
    integral_primitiveCovarianceProduct_base_le ρ hε hε1
      (momentCombinedPairing rep.1 rep.2.1 rep.2.2)
  have hpoint : ∀ v : Fin (2 * 1) → T4,
      ‖r324RefinedEndpointCore ρ ε 1 p.1.1 p.2.1 rep v‖ ≤ g v := by
    intro v
    unfold r324RefinedEndpointCore
    rw [r324RenormalizedInteriorCore_one,
      r324RenormalizedInteriorCore_one, one_mul, one_mul]
    have hcast :
        (∑ e ∈ momentRefinedContractionFiber 1 p.1.1 p.2.1,
          (primitiveCovarianceProduct ρ ε 1
            (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ)) =
        ((∑ e ∈ momentRefinedContractionFiber 1 p.1.1 p.2.1,
          primitiveCovarianceProduct ρ ε 1
            (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun e _ =>
        primitiveCovarianceProduct_nonneg ρ ε 1 _ v)]
    have hsub :
        momentRefinedContractionFiber 1 p.1.1 p.2.1 ⊆ {rep} :=
      fun e _ => Finset.mem_singleton.mpr (Subsingleton.elim e rep)
    calc
      (∑ e ∈ momentRefinedContractionFiber 1 p.1.1 p.2.1,
          primitiveCovarianceProduct ρ ε 1
            (momentCombinedPairing e.1 e.2.1 e.2.2) v) ≤
          ∑ e ∈ ({rep} : Finset (MomentContraction 1)),
            primitiveCovarianceProduct ρ ε 1
              (momentCombinedPairing e.1 e.2.1 e.2.2) v :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun e _ _ =>
            primitiveCovarianceProduct_nonneg ρ ε 1 _ v)
      _ = g v := by rw [Finset.sum_singleton]
  have hCore :
      r324RefinedInteriorCoreIntegral ρ ε 1 p ≤
        (2 * Real.pi) ^ (8 : ℕ) := by
    unfold r324RefinedInteriorCoreIntegral
    refine le_trans ?_ hgle
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun v => norm_nonneg _)
      hgint (Filter.Eventually.of_forall fun v => hpoint v)
  have hL0 : (0 : ℝ) ≤ |Real.log ε| := abs_nonneg _
  have hCore0 : 0 ≤ r324RefinedInteriorCoreIntegral ρ ε 1 p :=
    r324RefinedInteriorCoreIntegral_nonneg ρ ε 1 p
  calc
    16 * (|Real.log ε| * r324RefinedInteriorCoreIntegral ρ ε 1 p) ≤
        16 * (|Real.log ε| * (2 * Real.pi) ^ (8 : ℕ)) := by
      gcongr
    _ = (4 * (2 * Real.pi) ^ (4 : ℕ)) ^ (2 * 1) *
        |Real.log ε| ^ 1 := by
      ring

/-- **The base-order paper bound from the very-high residue alone.**
At `m = 1` the interior-core budget is discharged unconditionally
above, so the frozen paper (3.24) shape at `ε`-uniform constants
follows from only the very-high-frequency signed residue
(`‖freq(α+β)‖ > truncOrder ε · ε⁻¹`). -/
theorem exists_deterministicMoment_paper_bound_base_of_veryHighFrequency :
    ∃ outerConstant pC : ℝ, 0 < outerConstant ∧ 0 < pC ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (α β : Z4),
        0 ≤ lam → 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        R324VeryHighCentralFrequencySignedBound ρ lam ε 1
          (lamEps lam ε ^ 2 * outerConstant *
            ((16 * pC) * lam) ^ (2 * 1 - 2)) →
        ‖deterministicMomentPairingSum ρ lam ε 1 α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * pC) lam ε 1 α β := by
  have hC : (0 : ℝ) < 4 * (2 * Real.pi) ^ (4 : ℕ) := by positivity
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_logBudget_and_veryHighFrequency
      (supportConstant := 1) hC one_pos
  refine ⟨outerConstant,
    1 / min 1 1 ^ 2 * (4 * (2 * Real.pi) ^ (4 : ℕ)),
    houter, by norm_num [Real.pi_ne_zero]; positivity, ?_⟩
  intro ρ lam ε α β hlam hε hεsmall hlog hveryhigh
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  exact h ρ lam ε 1 α β one_pos hlam hε hεsmall hlog
    (r324InteriorCoreLogBudget_base ρ hε hε1)
    hveryhigh

end

end Anderson4D
