import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorTransport
import Anderson4D.DetParametrix.Paper42_Moment.R324CharacterCosineEstimate
import Anderson4D.Continuum.FourPointFourier
import Anderson4D.Continuum.CellSingular

/-!
# Difference-retaining block estimates for R-324

The order-two interior-core budget fails by
`not_r324InteriorCoreLogBudget_two`: the terminal swap block must be
integrated *jointly* with its renormalizing difference factor
`G(v₁-y) - G(v₀-y)` before any endpoint sup-normalization.

This file proves the scalar ledger of that joint integration:

* `exists_integral_torusDistSq_mul_greenFn_mul_etaEpsT4_le` — the
  second-moment mass `∫ |z̃|² G η_ε` of the block pair coordinate is
  bounded by a constant uniform in `ρ` and `ε`: the quadratic weight
  exactly cancels the Green singularity (`G ≤ C|z̃|⁻²`), leaving only
  the unit covariance mass `∫ η_ε ≤ 1`;
* `norm_r324BlockFrequencyIntegral_le` — the renormalized block
  frequency integral `M(β) = ∫ G η_ε (e^{iβ·z} - 1)` obeys the
  *second-order* bound `|M(β)| ≤ (1/2)|β|² ∫ |z̃|² G η_ε`: the
  first-order term is killed by the parity of `G η_ε` (cosine seam),
  and the remaining cosine defect is quadratic.  Thus the raw block mass
  `∫ G η_ε ≈ ε⁻²` is replaced by the `ε`-uniform bound `O(‖β‖²)`;
* `detIntegrand_pairingFinTwo_assemble`,
  `integral_charT4_mul_detIntegrand_pairingFinTwo`,
  `integral_greenFn_mul_etaEpsT4_mul_charDiff`,
  `integral_pi_twoBlock_u` — exact joint evaluation of the two-block
  half: the difference factor is consumed with the block *before* any
  boundary normalization;
* `norm_r324TwoBlockHalfIntegral_le` — one half of the two-block
  physical integral is bounded by
  `(2π)⁴ (1+|β|²)⁻¹ ‖M(β)‖`, uniformly in `ε` and both modes.

The physical integrand `detIntegrand` (paper (3.6)) retains every extracted
`diffFactor`; the endpoint-first majorant loses the terminal chain edge when
`r324RefinedInteriorCore` separates the sup-normalized endpoint legs.  The
estimate is therefore proved at the level of `r324RefinedPhysicalIntegral`,
before the interior/endpoint split.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The quadratic block mass is `ε`-uniform -/

/-- The periodized covariance is integrable: it is measurable, bounded
(uniformly at fixed scale), and the paper measure is finite. -/
theorem SmoothCutoff.integrable_etaEpsT4_paper
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (ρ.etaEpsT4 ε) paperMeasure := by
  obtain ⟨Cη, _hCη, hbound⟩ := ρ.exists_pos_etaEpsT4_uniform_bound
  refine (integrable_const (ε⁻¹ ^ (dim : ℕ) * Cη)).mono'
    (ρ.measurable_etaEpsT4 ε).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (ρ.etaEpsT4_nonneg ε z)]
  exact hbound hε hε1 z

/-- The quadratically weighted Green--covariance block mass, with its
integrability. -/
theorem integrable_torusDistSq_mul_greenFn_mul_etaEpsT4
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable
      (fun z : T4 =>
        torusDistSq z * (greenFn z * ρ.etaEpsT4 ε z))
      paperMeasure :=
  integrable_torusDistSq_mul_of_integrable
    (integrable_greenFn_mul_etaEpsT4 ρ hε hε1)

/-- **`ε`-uniform quadratic block mass.**  The weight `|z̃|²` cancels
the Green singularity exactly, so only the unit covariance mass
survives: `∫ |z̃|² G η_ε ≤ C`, with `C` independent of the cutoff and
of the scale. -/
theorem exists_integral_torusDistSq_mul_greenFn_mul_etaEpsT4_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ρ : SmoothCutoff) {ε : ℝ}, 0 < ε → ε ≤ 1 →
        (∫ z, torusDistSq z * (greenFn z * ρ.etaEpsT4 ε z)
          ∂paperMeasure) ≤ K := by
  obtain ⟨C, hC, hG⟩ := greenFn_le
  refine ⟨C, hC, ?_⟩
  intro ρ ε hε hε1
  have hae :
      ∀ᵐ z ∂paperMeasure,
        torusDistSq z * (greenFn z * ρ.etaEpsT4 ε z) ≤
          C * ρ.etaEpsT4 ε z := by
    have hnull : paperMeasure {(0 : T4)} = 0 :=
      paperMeasure_singleton 0
    refine (ae_iff.mpr ?_)
    refine measure_mono_null (fun z hz => ?_) hnull
    simp only [Set.mem_setOf_eq, not_le] at hz
    by_contra hz0
    have hzne : torusDistSq z ≠ 0 := by
      intro h0
      exact hz0
        (Set.mem_singleton_iff.mpr
          ((torusDistSq_eq_zero_iff z).mp h0))
    have hbound := hG z hzne
    have hdpos : 0 < torusDistSq z :=
      lt_of_le_of_ne (torusDistSq_nonneg z) (Ne.symm hzne)
    have hkey :
        torusDistSq z * greenFn z ≤ C := by
      have := mul_le_mul_of_nonneg_left hbound hdpos.le
      calc
        torusDistSq z * greenFn z ≤
            torusDistSq z * (C / torusDistSq z) := this
        _ = C := by field_simp
    have :
        torusDistSq z * (greenFn z * ρ.etaEpsT4 ε z) ≤
          C * ρ.etaEpsT4 ε z := by
      calc
        torusDistSq z * (greenFn z * ρ.etaEpsT4 ε z) =
            (torusDistSq z * greenFn z) * ρ.etaEpsT4 ε z := by
          ring
        _ ≤ C * ρ.etaEpsT4 ε z :=
          mul_le_mul_of_nonneg_right hkey (ρ.etaEpsT4_nonneg ε z)
    exact absurd this (not_le.mpr hz)
  have hint :=
    integrable_torusDistSq_mul_greenFn_mul_etaEpsT4 ρ hε hε1
  have hηint : Integrable (fun z => C * ρ.etaEpsT4 ε z) paperMeasure :=
    (ρ.integrable_etaEpsT4_paper hε hε1).const_mul C
  calc
    (∫ z, torusDistSq z * (greenFn z * ρ.etaEpsT4 ε z)
        ∂paperMeasure) ≤
        ∫ z, C * ρ.etaEpsT4 ε z ∂paperMeasure :=
      integral_mono_ae hint hηint hae
    _ = C * ∫ z, ρ.etaEpsT4 ε z ∂paperMeasure :=
      integral_const_mul _ _
    _ ≤ C * 1 :=
      mul_le_mul_of_nonneg_left
        (integral_etaEpsT4_paper_le_one ρ hε) hC.le
    _ = C := mul_one C

/-! ## The renormalized block frequency integral -/

/-- The joint (difference-retained) block frequency integral: the
Green--covariance pair against the renormalizing phase defect. -/
def r324BlockFrequencyIntegral
    (ρ : SmoothCutoff) (ε : ℝ) (b : Z4) : ℂ :=
  ∫ z,
    ((greenFn z * ρ.etaEpsT4 ε z : ℝ) : ℂ) * (charT4 b z - 1)
    ∂paperMeasure

/-- **Second-order bound for the renormalized block.**  Parity of
`G η_ε` kills the first-order phase term (cosine seam), and the cosine
defect is quadratic; the result is `ε`-uniform up to the quadratic
mass, in stark contrast with the raw block mass `∫ G η_ε ≥ c ε⁻²` of
`exists_le_integral_greenFn_mul_etaEpsT4`. -/
theorem norm_r324BlockFrequencyIntegral_le
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (b : Z4) :
    ‖r324BlockFrequencyIntegral ρ ε b‖ ≤
      ((1 / 2 : ℝ) * paperModeNormSq b) *
        ∫ z, torusDistSq z * (greenFn z * ρ.etaEpsT4 ε z)
          ∂paperMeasure := by
  have hJmemE : MemEClassT4 fun z => greenFn z * ρ.etaEpsT4 ε z :=
    greenFn_memE.mul (ρ.etaEpsT4_memE ε)
  have hJint := integrable_greenFn_mul_etaEpsT4 ρ hε hε1
  have hcos :
      Integrable
        (fun z =>
          (greenFn z * ρ.etaEpsT4 ε z) *
            (r324CharacterCos b z - 1))
        paperMeasure := by
    have h :
        Integrable
          (fun z =>
            (r324CharacterCos b z - 1) *
              (greenFn z * ρ.etaEpsT4 ε z))
          paperMeasure := by
      refine hJint.bdd_mul (c := 3)
        (((Complex.measurable_re.comp
          (continuous_charT4 b).measurable).sub
          measurable_const).aestronglyMeasurable) ?_
      filter_upwards with z
      rw [Real.norm_eq_abs]
      exact le_trans (abs_r324CharacterCos_sub_one_le_two b z)
        (by norm_num)
    have heq :
        (fun z =>
          (greenFn z * ρ.etaEpsT4 ε z) *
            (r324CharacterCos b z - 1)) =
          fun z =>
            (r324CharacterCos b z - 1) *
              (greenFn z * ρ.etaEpsT4 ε z) := by
      funext z
      ring
    rw [heq]
    exact h
  have hsin :
      Integrable
        (fun z =>
          (greenFn z * ρ.etaEpsT4 ε z) * r324CharacterSin b z)
        paperMeasure := by
    have h :
        Integrable
          (fun z =>
            r324CharacterSin b z *
              (greenFn z * ρ.etaEpsT4 ε z))
          paperMeasure := by
      refine hJint.bdd_mul (c := 1)
        ((Complex.measurable_im.comp
          (continuous_charT4 b).measurable).aestronglyMeasurable) ?_
      filter_upwards with z
      rw [Real.norm_eq_abs]
      have h := Complex.abs_im_le_norm (charT4 b z)
      rw [norm_charT4] at h
      exact h
    have heq :
        (fun z =>
          (greenFn z * ρ.etaEpsT4 ε z) * r324CharacterSin b z) =
          fun z =>
            r324CharacterSin b z *
              (greenFn z * ρ.etaEpsT4 ε z) := by
      funext z
      ring
    rw [heq]
    exact h
  have hseam :=
    integral_memEClass_mul_characterSubOne_eq_cos
      hJmemE b hcos hsin
  unfold r324BlockFrequencyIntegral
  rw [hseam]
  exact
    norm_integral_mul_r324CharacterCos_sub_one_le_of_abs_le b
      (fun z =>
        le_of_eq
          (abs_of_nonneg
            (mul_nonneg (greenFn_nonneg z) (ρ.etaEpsT4_nonneg ε z))))
      (integrable_torusDistSq_mul_greenFn_mul_etaEpsT4 ρ hε hε1)

/-! ## The two-block renormalized integrand, closed form -/

/-- Characters are multiplicative in the point variable. -/
theorem charT4_point_add (k : Z4) (x z : T4) :
    charT4 k (x + z) = charT4 k x * charT4 k z := by
  unfold charT4
  simp only [Pi.add_apply]
  calc
    (∏ i, fourier (k i) (x i + z i)) =
        ∏ i, (fourier (k i) (x i) *
          fourier (k i) (z i)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [fourier_apply, zsmul_add, AddCircle.toCircle_add,
        Circle.coe_mul]
      rfl
    _ = _ := Finset.prod_mul_distrib

/-- **Closed form of the order-two renormalized swap integrand.**  The
extraction of the unique within-half pair erases the terminal chain
edge and installs the renormalizing difference factor
`G(u₁-y) - G(u₀-y)` in its place; the covariance factor pairs the two
internal vertices. -/
theorem detIntegrand_pairingFinTwo_assemble
    (ρ : SmoothCutoff) (ε : ℝ) (x y : T4) (u : Fin 2 → T4) :
    detIntegrand ρ ε 2 pairingFinTwo (assemble x y u) =
      (greenFn (x - u 0) * greenFn (u 0 - u 1)) *
        (greenFn (u 1 - y) - greenFn (u 0 - y)) *
        ρ.etaEpsT4 ε (u 0 - u 1) := by
  unfold detIntegrand
  rw [pairingFinTwo_extract]
  have hxt1 : assemble x y u (1 : Fin (2 + 2)) = u 0 := by
    have h : (1 : Fin (2 + 2)) = varIdx (0 : Fin 2) := rfl
    rw [h, assemble_varIdx]
  have hxt2 : assemble x y u (2 : Fin (2 + 2)) = u 1 := by
    have h : (2 : Fin (2 + 2)) = varIdx (1 : Fin 2) := rfl
    rw [h, assemble_varIdx]
  have hxt3 : assemble x y u (3 : Fin (2 + 2)) = y := by
    have h : (3 : Fin (2 + 2)) = Fin.last (2 + 1) := rfl
    rw [h, assemble_last]
  have hchain :
      (∏ e : Fin (2 + 1),
        if e.val ∈ [((0 : Fin 2), (1 : Fin 2))].map
            (fun p => p.2.val + 1) then 1
        else greenFn (assemble x y u e.castSucc -
          assemble x y u e.succ)) =
        greenFn (x - u 0) * greenFn (u 0 - u 1) := by
    rw [Fin.prod_univ_three]
    have h0 :
        ((0 : Fin (2 + 1)).val ∈
          [((0 : Fin 2), (1 : Fin 2))].map
            (fun p => p.2.val + 1)) = False := by decide
    have h1 :
        ((1 : Fin (2 + 1)).val ∈
          [((0 : Fin 2), (1 : Fin 2))].map
            (fun p => p.2.val + 1)) = False := by decide
    have h2 :
        ((2 : Fin (2 + 1)).val ∈
          [((0 : Fin 2), (1 : Fin 2))].map
            (fun p => p.2.val + 1)) = True := by decide
    rw [if_neg (by rw [h0]; exact id),
      if_neg (by rw [h1]; exact id),
      if_pos (by rw [h2]; trivial)]
    have hc0 : (0 : Fin (2 + 1)).castSucc = (0 : Fin (2 + 2)) := rfl
    have hs0 : (0 : Fin (2 + 1)).succ = (1 : Fin (2 + 2)) := rfl
    have hc1 : (1 : Fin (2 + 1)).castSucc = (1 : Fin (2 + 2)) := rfl
    have hs1 : (1 : Fin (2 + 1)).succ = (2 : Fin (2 + 2)) := rfl
    rw [hc0, hs0, hc1, hs1, assemble_zero, hxt1, hxt2, mul_one]
  have hdiff :
      ([((0 : Fin 2), (1 : Fin 2))].map
        (diffFactor (assemble x y u))).prod =
        greenFn (u 1 - y) - greenFn (u 0 - y) := by
    rw [List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    unfold diffFactor
    have hv1 : varIdx ((0 : Fin 2), (1 : Fin 2)).2 =
        (2 : Fin (2 + 2)) := rfl
    have hv0 : varIdx ((0 : Fin 2), (1 : Fin 2)).1 =
        (1 : Fin (2 + 2)) := rfl
    have hslot :
        (⟨((0 : Fin 2), (1 : Fin 2)).2.val + 2, by omega⟩ :
          Fin (2 + 2)) = (3 : Fin (2 + 2)) := rfl
    rw [hv1, hv0, hslot, hxt1, hxt2, hxt3]
  have hcov :
      (∏ i ∈ pairingFinTwo.pairSupport.filter
          (fun i => i < pairingFinTwo i),
        ρ.etaEpsT4 ε
          (assemble x y u (varIdx i) -
            assemble x y u (varIdx (pairingFinTwo i)))) =
        ρ.etaEpsT4 ε (u 0 - u 1) := by
    have hset :
        pairingFinTwo.pairSupport.filter
            (fun i => i < pairingFinTwo i) =
          {(0 : Fin 2)} := by decide
    rw [hset, Finset.prod_singleton]
    have hp0 : pairingFinTwo (0 : Fin 2) = 1 := rfl
    rw [hp0, assemble_varIdx, assemble_varIdx]
  rw [hchain, hdiff, hcov]

/-! ## Exact one-variable evaluations -/

/-- Characters against a translated Green factor are integrable. -/
theorem integrable_charT4_mul_greenFn_sub (b : Z4) (z : T4) :
    Integrable
      (fun y : T4 => charT4 b y * ((greenFn (y - z) : ℝ) : ℂ))
      paperMeasure := by
  refine ((integrable_greenFn_sub z).ofReal).bdd_mul (c := 1)
    (continuous_charT4 b).aestronglyMeasurable ?_
  filter_upwards with y
  rw [norm_charT4]

/-- The `y`-integral of one boundary Green factor with its character:
the exact translated Fourier coefficient, in the orientation produced
by the difference factor. -/
theorem integral_charT4_mul_greenFn_shift (b : Z4) (v : T4) :
    (∫ y, charT4 b y * ((greenFn (v - y) : ℝ) : ℂ)
      ∂paperMeasure) =
      charT4 b v * (((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) := by
  have hflip :
      (fun y : T4 => charT4 b y * ((greenFn (v - y) : ℝ) : ℂ)) =
        fun y : T4 => charT4 b y * ((greenFn (y - v) : ℝ) : ℂ) := by
    funext y
    have h : greenFn (v - y) = greenFn (y - v) := by
      rw [show v - y = -(y - v) by abel, greenFn_memE.neg_invariant]
    rw [h]
  rw [hflip]
  have h := translatedGreenMode_eq b v
  unfold translatedGreenMode at h
  rw [h]
  unfold paperModeNormSq
  rfl

/-- Every left-translate of the Green kernel has unit paper mass. -/
theorem integral_greenFn_shift_left (x : T4) :
    (∫ u, greenFn (x - u) ∂paperMeasure) = 1 := by
  have hflip :
      (fun u : T4 => greenFn (x - u)) =
        fun u : T4 => greenFn (u - x) := by
    funext u
    rw [show x - u = -(u - x) by abel, greenFn_memE.neg_invariant]
  rw [hflip]
  exact integral_greenFn_sub x

/-- **Joint block evaluation.**  Integrating the block pair coordinate
against its character difference produces exactly the base-point
character times the renormalized block frequency integral: the
difference factor is consumed *jointly* with the block, never
sup-normalized away. -/
theorem integral_greenFn_mul_etaEpsT4_mul_charDiff
    (ρ : SmoothCutoff) (ε : ℝ) (b : Z4) (u₀ : T4) :
    (∫ u₁,
        ((greenFn (u₀ - u₁) * ρ.etaEpsT4 ε (u₀ - u₁) : ℝ) : ℂ) *
          (charT4 b u₁ - charT4 b u₀)
      ∂paperMeasure) =
      charT4 b u₀ * r324BlockFrequencyIntegral ρ ε b := by
  rw [paperMeasure_eq_volume]
  have hsub :
      (∫ u₁,
          ((greenFn (u₀ - u₁) * ρ.etaEpsT4 ε (u₀ - u₁) : ℝ) : ℂ) *
            (charT4 b u₁ - charT4 b u₀)
        ∂(volume : Measure T4)) =
        ∫ t,
          ((greenFn (u₀ - (t + u₀)) *
              ρ.etaEpsT4 ε (u₀ - (t + u₀)) : ℝ) : ℂ) *
            (charT4 b (t + u₀) - charT4 b u₀)
          ∂(volume : Measure T4) :=
    (integral_add_right_eq_self
      (μ := (volume : Measure T4))
      (fun t : T4 =>
        ((greenFn (u₀ - t) * ρ.etaEpsT4 ε (u₀ - t) : ℝ) : ℂ) *
          (charT4 b t - charT4 b u₀)) u₀).symm
  rw [hsub]
  have hpoint :
      ∀ t : T4,
        ((greenFn (u₀ - (t + u₀)) *
            ρ.etaEpsT4 ε (u₀ - (t + u₀)) : ℝ) : ℂ) *
          (charT4 b (t + u₀) - charT4 b u₀) =
        charT4 b u₀ *
          (((greenFn t * ρ.etaEpsT4 ε t : ℝ) : ℂ) *
            (charT4 b t - 1)) := by
    intro t
    have harg : u₀ - (t + u₀) = -t := by abel
    have hG : greenFn (u₀ - (t + u₀)) = greenFn t := by
      rw [harg, greenFn_memE.neg_invariant]
    have hη : ρ.etaEpsT4 ε (u₀ - (t + u₀)) = ρ.etaEpsT4 ε t := by
      rw [harg, (ρ.etaEpsT4_memE ε).neg_invariant]
    rw [hG, hη, charT4_point_add]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_const_mul]
  rw [← paperMeasure_eq_volume]
  rfl

/-- **Exact `y`-integral of the two-block integrand.**  The external
character integrates the *difference factor jointly with the block*:
the result carries the boundary Fourier coefficient
`(1 + |b|²)⁻¹` and the internal character difference
`charT4 b u₁ - charT4 b u₀`, the physical-side trace of the retained
renormalization. -/
theorem integral_charT4_mul_detIntegrand_pairingFinTwo
    (ρ : SmoothCutoff) (ε : ℝ) (b : Z4) (x : T4)
    (u : Fin 2 → T4) :
    (∫ y, charT4 b y *
        ((detIntegrand ρ ε 2 pairingFinTwo (assemble x y u) : ℝ) : ℂ)
      ∂paperMeasure) =
      ((greenFn (x - u 0) * greenFn (u 0 - u 1) *
          ρ.etaEpsT4 ε (u 0 - u 1) : ℝ) : ℂ) *
        ((((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) *
          (charT4 b (u 1) - charT4 b (u 0))) := by
  have hpoint :
      ∀ y : T4,
        charT4 b y *
          ((detIntegrand ρ ε 2 pairingFinTwo
            (assemble x y u) : ℝ) : ℂ) =
        ((greenFn (x - u 0) * greenFn (u 0 - u 1) *
            ρ.etaEpsT4 ε (u 0 - u 1) : ℝ) : ℂ) *
          (charT4 b y * ((greenFn (u 1 - y) : ℝ) : ℂ) -
            charT4 b y * ((greenFn (u 0 - y) : ℝ) : ℂ)) := by
    intro y
    rw [detIntegrand_pairingFinTwo_assemble]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_const_mul]
  have hsplit :
      (∫ y,
          (charT4 b y * ((greenFn (u 1 - y) : ℝ) : ℂ) -
            charT4 b y * ((greenFn (u 0 - y) : ℝ) : ℂ))
        ∂paperMeasure) =
        (∫ y, charT4 b y * ((greenFn (u 1 - y) : ℝ) : ℂ)
          ∂paperMeasure) -
          ∫ y, charT4 b y * ((greenFn (u 0 - y) : ℝ) : ℂ)
            ∂paperMeasure := by
    apply integral_sub
    · have h :
          (fun y : T4 =>
            charT4 b y * ((greenFn (u 1 - y) : ℝ) : ℂ)) =
            fun y : T4 =>
              charT4 b y * ((greenFn (y - u 1) : ℝ) : ℂ) := by
        funext y
        rw [show u 1 - y = -(y - u 1) by abel,
          greenFn_memE.neg_invariant]
      rw [h]
      exact integrable_charT4_mul_greenFn_sub b (u 1)
    · have h :
          (fun y : T4 =>
            charT4 b y * ((greenFn (u 0 - y) : ℝ) : ℂ)) =
            fun y : T4 =>
              charT4 b y * ((greenFn (y - u 0) : ℝ) : ℂ) := by
        funext y
        rw [show u 0 - y = -(y - u 0) by abel,
          greenFn_memE.neg_invariant]
      rw [h]
      exact integrable_charT4_mul_greenFn_sub b (u 0)
  rw [hsplit, integral_charT4_mul_greenFn_shift,
    integral_charT4_mul_greenFn_shift]
  ring

/-- The character-weighted Green translate has integral of norm at most
one: the boundary leg costs exactly its unit mass. -/
theorem norm_integral_greenFn_shift_mul_charT4_le (b : Z4) (x : T4) :
    ‖∫ u₀, ((greenFn (x - u₀) : ℝ) : ℂ) * charT4 b u₀
        ∂paperMeasure‖ ≤ 1 := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hpoint :
      ∀ u₀ : T4,
        ‖((greenFn (x - u₀) : ℝ) : ℂ) * charT4 b u₀‖ =
          greenFn (x - u₀) := by
    intro u₀
    rw [norm_mul, norm_charT4, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (greenFn_nonneg _)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_greenFn_shift_left]

/-- **Exact evaluation of the two-block internal integral.**  With the
difference factor consumed jointly (previous lemmas), the full internal
double integral collapses to the boundary coefficient times the
renormalized block frequency integral times one unit-mass boundary
leg. -/
theorem integral_pi_twoBlock_u
    (ρ : SmoothCutoff) (ε : ℝ) (b : Z4) (x : T4)
    (hint :
      Integrable
        (fun u : Fin 2 → T4 =>
          ((greenFn (x - u 0) * greenFn (u 0 - u 1) *
              ρ.etaEpsT4 ε (u 0 - u 1) : ℝ) : ℂ) *
            ((((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) *
              (charT4 b (u 1) - charT4 b (u 0))))
        (Measure.pi fun _ : Fin 2 => paperMeasure)) :
    (∫ u : Fin 2 → T4,
        ((greenFn (x - u 0) * greenFn (u 0 - u 1) *
            ρ.etaEpsT4 ε (u 0 - u 1) : ℝ) : ℂ) *
          ((((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) *
            (charT4 b (u 1) - charT4 b (u 0)))
      ∂(Measure.pi fun _ : Fin 2 => paperMeasure)) =
      (((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) *
        (r324BlockFrequencyIntegral ρ ε b *
          ∫ u₀, ((greenFn (x - u₀) : ℝ) : ℂ) * charT4 b u₀
            ∂paperMeasure) := by
  set T' : T4 × T4 → ℂ :=
    fun p =>
      ((greenFn (x - p.1) * greenFn (p.1 - p.2) *
          ρ.etaEpsT4 ε (p.1 - p.2) : ℝ) : ℂ) *
        ((((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) *
          (charT4 b p.2 - charT4 b p.1))
    with hT'def
  have hcomp :
      (fun u : Fin 2 → T4 =>
        ((greenFn (x - u 0) * greenFn (u 0 - u 1) *
            ρ.etaEpsT4 ε (u 0 - u 1) : ℝ) : ℂ) *
          ((((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) *
            (charT4 b (u 1) - charT4 b (u 0)))) =
        fun u : Fin 2 → T4 =>
          T' (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => T4) u) :=
    rfl
  have hpi :=
    (measurePreserving_piFinTwo
      (fun _ : Fin 2 => paperMeasure)).integral_comp' T'
  rw [hcomp, hpi]
  have hT'int :
      Integrable T'
        (paperMeasure.prod paperMeasure) := by
    have hiff :=
      (measurePreserving_piFinTwo
        (fun _ : Fin 2 => paperMeasure)).integrable_comp_emb
        (MeasurableEquiv.piFinTwo
          (fun _ : Fin 2 => T4)).measurableEmbedding
        (g := T')
    exact hiff.mp (by rw [hcomp] at hint; exact hint)
  rw [integral_prod _ hT'int]
  have hinner :
      ∀ u₀ : T4,
        (∫ u₁, T' (u₀, u₁) ∂paperMeasure) =
          (((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) *
            (r324BlockFrequencyIntegral ρ ε b *
              (((greenFn (x - u₀) : ℝ) : ℂ) * charT4 b u₀)) := by
    intro u₀
    have hpt :
        ∀ u₁ : T4,
          T' (u₀, u₁) =
            (((greenFn (x - u₀) : ℝ) : ℂ) *
              (((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ)) *
              (((greenFn (u₀ - u₁) *
                  ρ.etaEpsT4 ε (u₀ - u₁) : ℝ) : ℂ) *
                (charT4 b u₁ - charT4 b u₀)) := by
      intro u₁
      rw [hT'def]
      push_cast
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_const_mul,
      integral_greenFn_mul_etaEpsT4_mul_charDiff]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner),
    integral_const_mul, integral_const_mul]

/-! ## The two-block half integral -/

/-- One complete half of the two-block physical integral, on its flat
product space: external characters against the renormalized swap
integrand. -/
def r324TwoBlockHalfIntegral
    (ρ : SmoothCutoff) (ε : ℝ) (a b : Z4) : ℂ :=
  ∫ p : T4 × (T4 × (Fin 2 → T4)),
    (charT4 a p.1 * charT4 b p.2.1) *
      ((detIntegrand ρ ε 2 pairingFinTwo
        (assemble p.1 p.2.1 p.2.2) : ℝ) : ℂ)
    ∂(paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : Fin 2 => paperMeasure)))

theorem integrable_r324TwoBlockHalfIntegrand
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (a b : Z4) :
    Integrable
      (fun p : T4 × (T4 × (Fin 2 → T4)) =>
        (charT4 a p.1 * charT4 b p.2.1) *
          ((detIntegrand ρ ε 2 pairingFinTwo
            (assemble p.1 p.2.1 p.2.2) : ℝ) : ℂ))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin 2 => paperMeasure))) := by
  refine (integrable_detIntegrand_flat ρ hε hε1 pairingFinTwo).bdd_mul
    (c := 1) ?_ ?_
  · exact
      ((((continuous_charT4 a).measurable.comp measurable_fst).mul
        ((continuous_charT4 b).measurable.comp
          (measurable_fst.comp measurable_snd))).aestronglyMeasurable)
  · filter_upwards with p
    rw [norm_mul, norm_charT4, norm_charT4, mul_one]

/-- **The difference-retaining half-integral bound.**  Uniformly in the
scale and in both external frequencies, one half of the two-block
physical integral is controlled by the boundary coefficient
`(1+|b|²)⁻¹` times the renormalized block frequency integral: the
`ε → 0` divergence of the raw block never appears. -/
theorem norm_r324TwoBlockHalfIntegral_le
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (a b : Z4) :
    ‖r324TwoBlockHalfIntegral ρ ε a b‖ ≤
      (2 * Real.pi) ^ (dim : ℕ) *
        ((1 + paperModeNormSq b)⁻¹ *
          ‖r324BlockFrequencyIntegral ρ ε b‖) := by
  have hpmns : (0 : ℝ) ≤ (1 + paperModeNormSq b)⁻¹ := by
    have := paperModeNormSq_nonneg b
    positivity
  set B : ℝ :=
    (1 + paperModeNormSq b)⁻¹ *
      ‖r324BlockFrequencyIntegral ρ ε b‖ with hBdef
  have hB : 0 ≤ B :=
    mul_nonneg hpmns (norm_nonneg _)
  have hint := integrable_r324TwoBlockHalfIntegrand ρ hε hε1 a b
  unfold r324TwoBlockHalfIntegral
  rw [integral_prod _ hint]
  have hbound :
      ∀ᵐ x ∂paperMeasure,
        ‖∫ q : T4 × (Fin 2 → T4),
            (charT4 a x * charT4 b q.1) *
              ((detIntegrand ρ ε 2 pairingFinTwo
                (assemble x q.1 q.2) : ℝ) : ℂ)
            ∂(paperMeasure.prod
              (Measure.pi fun _ : Fin 2 => paperMeasure))‖ ≤ B := by
    filter_upwards [hint.prod_right_ae] with x hx
    rw [integral_prod_symm _ hx]
    have hyeval :
        ∀ u : Fin 2 → T4,
          (∫ y,
              (charT4 a x * charT4 b y) *
                ((detIntegrand ρ ε 2 pairingFinTwo
                  (assemble x y u) : ℝ) : ℂ)
              ∂paperMeasure) =
            charT4 a x *
              (((greenFn (x - u 0) * greenFn (u 0 - u 1) *
                  ρ.etaEpsT4 ε (u 0 - u 1) : ℝ) : ℂ) *
                ((((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) *
                  (charT4 b (u 1) - charT4 b (u 0)))) := by
      intro u
      have hassoc :
          ∀ y : T4,
            (charT4 a x * charT4 b y) *
              ((detIntegrand ρ ε 2 pairingFinTwo
                (assemble x y u) : ℝ) : ℂ) =
              charT4 a x *
                (charT4 b y *
                  ((detIntegrand ρ ε 2 pairingFinTwo
                    (assemble x y u) : ℝ) : ℂ)) := by
        intro y
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hassoc),
        integral_const_mul,
        integral_charT4_mul_detIntegrand_pairingFinTwo]
    rw [integral_congr_ae (Filter.Eventually.of_forall hyeval),
      integral_const_mul]
    have hTint :
        Integrable
          (fun u : Fin 2 → T4 =>
            ((greenFn (x - u 0) * greenFn (u 0 - u 1) *
                ρ.etaEpsT4 ε (u 0 - u 1) : ℝ) : ℂ) *
              ((((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) *
                (charT4 b (u 1) - charT4 b (u 0))))
          (Measure.pi fun _ : Fin 2 => paperMeasure) := by
      have hIy := hx.integral_prod_right
      have heq :
          (fun u : Fin 2 → T4 =>
            ∫ y,
              (charT4 a x * charT4 b y) *
                ((detIntegrand ρ ε 2 pairingFinTwo
                  (assemble x y u) : ℝ) : ℂ)
              ∂paperMeasure) =
            fun u : Fin 2 → T4 =>
              charT4 a x *
                (((greenFn (x - u 0) * greenFn (u 0 - u 1) *
                    ρ.etaEpsT4 ε (u 0 - u 1) : ℝ) : ℂ) *
                  ((((1 + paperModeNormSq b)⁻¹ : ℝ) : ℂ) *
                    (charT4 b (u 1) - charT4 b (u 0)))) := by
        funext u
        exact hyeval u
      rw [heq] at hIy
      have hunit : IsUnit (charT4 a x) := by
        rw [isUnit_iff_ne_zero]
        intro h0
        have := norm_charT4 a x
        rw [h0, norm_zero] at this
        norm_num at this
      exact (integrable_const_mul_iff hunit _).mp hIy
    rw [integral_pi_twoBlock_u ρ ε b x hTint]
    rw [norm_mul, norm_charT4 a x, one_mul, norm_mul, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpmns]
    rw [hBdef]
    refine mul_le_mul_of_nonneg_left ?_ hpmns
    calc
      ‖r324BlockFrequencyIntegral ρ ε b‖ *
          ‖∫ u₀, ((greenFn (x - u₀) : ℝ) : ℂ) * charT4 b u₀
            ∂paperMeasure‖ ≤
          ‖r324BlockFrequencyIntegral ρ ε b‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (norm_integral_greenFn_shift_mul_charT4_le b x)
          (norm_nonneg _)
      _ = ‖r324BlockFrequencyIntegral ρ ε b‖ := mul_one _
  calc
    ‖∫ x, ∫ q : T4 × (Fin 2 → T4),
        (charT4 a x * charT4 b q.1) *
          ((detIntegrand ρ ε 2 pairingFinTwo
            (assemble x q.1 q.2) : ℝ) : ℂ)
        ∂(paperMeasure.prod
          (Measure.pi fun _ : Fin 2 => paperMeasure))
        ∂paperMeasure‖ ≤
        ∫ _x : T4, B ∂paperMeasure :=
      norm_integral_le_of_norm_le (integrable_const B) hbound
    _ = (2 * Real.pi) ^ (dim : ℕ) * B := by
      rw [integral_const, measureReal_def, paperMeasure_univ,
        ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

end

end Anderson4D
