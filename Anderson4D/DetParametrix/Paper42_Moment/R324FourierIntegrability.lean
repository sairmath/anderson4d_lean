import Anderson4D.DetParametrix.Paper42_Moment.R324CovarianceFourierExpansion

/-!
# Integrating the R-324 Fourier configuration series

This file proves the analytic exchange omitted in the paper's sketch of
§4.2, Step 4.  For a fixed full doubled pairing, the absolutely convergent
covariance Fourier series may be exchanged with the genuine five-group
physical integral.  The proof uses joint integrability of the two
renormalized Green skeletons and a summable coefficient majorant.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## Green-skeleton product integrability -/

/-- Joint integrability of one renormalized Green skeleton in flat
`(x,y,v)` coordinates. -/
theorem integrable_renormalizedGreenSkeleton_flat
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Integrable
      (fun p : T4 × (T4 × (Fin m → T4)) =>
        renormalizedGreenSkeleton κ
          (assemble p.1 p.2.1 p.2.2))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin m => paperMeasure))) := by
  let e := r324FlatAssembleMeasurableEquiv m
  let μ := Measure.pi fun _ : Fin (m + 2) => paperMeasure
  let ν :=
    paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : Fin m => paperMeasure))
  have hp : MeasurePreserving e μ ν :=
    measurePreserving_r324FlatAssembleMeasurableEquiv m
  have hsource :=
    integrable_renormalizedGreenSkeleton κ
  have htarget :
      Integrable
        (fun p : T4 × (T4 × (Fin m → T4)) =>
          renormalizedGreenSkeleton κ (e.symm p))
        ν := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p : T4 × (T4 × (Fin m → T4)) =>
          renormalizedGreenSkeleton κ (e.symm p))
    apply hiff.mp
    convert hsource using 1
    funext x
    simp only [Function.comp_apply, e,
      MeasurableEquiv.symm_apply_apply]
  convert htarget using 1
  funext p
  rcases p with ⟨x, y, v⟩
  exact congrArg (renormalizedGreenSkeleton κ)
    (r324FlatAssembleMeasurableEquiv_symm_apply m x y v).symm

/-- The two independent Green skeletons are jointly integrable on the
actual doubled physical space. -/
theorem integrable_r324Flatten_renormalizedGreenSkeleton_product
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    Integrable
      (r324Flatten
        (fun x y z w v =>
          renormalizedGreenSkeleton κp
              (assemble x y fun i => v (leftMomentIndex i)) *
            renormalizedGreenSkeleton κm
              (assemble z w fun i => v (rightMomentIndex i))))
      (r324PhysicalMeasure m) := by
  let Flat := T4 × (T4 × (Fin m → T4))
  let μflat :=
    paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : Fin m => paperMeasure))
  let fp : Flat → ℂ := fun p =>
    renormalizedGreenSkeleton κp
      (assemble p.1 p.2.1 p.2.2)
  let fm : Flat → ℂ := fun p =>
    renormalizedGreenSkeleton κm
      (assemble p.1 p.2.1 p.2.2)
  have hp : Integrable fp μflat := by
    simpa only [fp, μflat] using
      integrable_renormalizedGreenSkeleton_flat κp
  have hm : Integrable fm μflat := by
    simpa only [fm, μflat] using
      integrable_renormalizedGreenSkeleton_flat κm
  have hprod :
      Integrable
        (fun p : Flat × Flat => fp p.1 * fm p.2)
        (μflat.prod μflat) :=
    hp.mul_prod hm
  let e := r324PhysicalSplitMeasurableEquiv m
  have he :
      MeasurePreserving e
        (r324PhysicalMeasure m) (μflat.prod μflat) := by
    simpa only [e, μflat] using
      measurePreserving_r324PhysicalSplitMeasurableEquiv m
  have hiff :=
    he.integrable_comp_emb e.measurableEmbedding
      (g := fun p : Flat × Flat => fp p.1 * fm p.2)
  have hpull :
      Integrable
        ((fun p : Flat × Flat => fp p.1 * fm p.2) ∘ e)
        (r324PhysicalMeasure m) :=
    hiff.mpr hprod
  convert hpull using 1
  funext p
  simp only [Function.comp_apply, e,
    r324PhysicalSplitMeasurableEquiv_apply, fp, fm,
    r324Flatten]

/-! ## Configuration integrands -/

/-- The nonnegative absolute coefficient of one Fourier assignment. -/
def r324CovarianceConfigurationWeight
    {m : ℕ} (ε : ℝ)
    (κ : PartialPairing (Fin (2 * m)))
    (q :
      Fin (κ.pairSupport.filter (fun i => i < κ i)).card → Z4) :
    ℝ :=
  ∏ j, ‖ρ.covarianceModeCoeff ε (q j)‖

theorem r324CovarianceConfigurationWeight_nonneg
    {m : ℕ} (ε : ℝ)
    (κ : PartialPairing (Fin (2 * m)))
    (q :
      Fin (κ.pairSupport.filter (fun i => i < κ i)).card → Z4) :
    0 ≤ ρ.r324CovarianceConfigurationWeight ε κ q :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

/-- The norm of a configuration is independent of the physical
coordinates: every character has norm one. -/
theorem norm_r324CovarianceFourierConfigurationTerm
    {m : ℕ} (ε : ℝ)
    (κ : PartialPairing (Fin (2 * m)))
    (v : Fin (2 * m) → T4)
    (q :
      Fin (κ.pairSupport.filter (fun i => i < κ i)).card → Z4) :
    ‖ρ.r324CovarianceFourierConfigurationTerm ε κ v q‖ =
      ρ.r324CovarianceConfigurationWeight ε κ q := by
  unfold r324CovarianceFourierConfigurationTerm
    finSeriesAssignmentTerm r324CovarianceConfigurationWeight
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro j _hj
  unfold r324PairModeTerm r324CovarianceModeTerm
  rw [norm_mul, norm_charT4, mul_one]

/-- The configuration weights form a summable nonnegative series. -/
theorem summable_r324CovarianceConfigurationWeight
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (κ : PartialPairing (Fin (2 * m))) :
    Summable (ρ.r324CovarianceConfigurationWeight ε κ) := by
  let v₀ : Fin (2 * m) → T4 := fun _ => 0
  exact
    (ρ.summable_norm_r324CovarianceFourierConfigurationTerm
      hε κ v₀).congr fun q =>
        ρ.norm_r324CovarianceFourierConfigurationTerm
          ε κ v₀ q

/-- A fixed Fourier configuration is measurable in the doubled internal
tuple. -/
theorem measurable_r324CovarianceFourierConfigurationTerm
    {m : ℕ} (ε : ℝ)
    (κ : PartialPairing (Fin (2 * m)))
    (q :
      Fin (κ.pairSupport.filter (fun i => i < κ i)).card → Z4) :
    Measurable fun v : Fin (2 * m) → T4 =>
      ρ.r324CovarianceFourierConfigurationTerm ε κ v q := by
  unfold r324CovarianceFourierConfigurationTerm
    finSeriesAssignmentTerm
  apply Finset.measurable_prod
  intro j _hj
  unfold r324PairModeTerm r324CovarianceModeTerm
  exact measurable_const.mul
    ((continuous_charT4 (q j)).measurable.comp
      ((measurable_pi_apply (r324PairFinEquiv κ j).1).sub
        (measurable_pi_apply
          (κ (r324PairFinEquiv κ j).1))))

/-- One Fourier-configuration summand of the full-pairing physical
integrand. -/
def r324FullPairingFourierIntegrand
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q :
      Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card → Z4)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  let e := (momentContractionEquivFullPairing m).symm κ
  momentFourierPhase α β x y z w *
    renormalizedGreenSkeleton e.1
      (assemble x y fun i => v (leftMomentIndex i)) *
    renormalizedGreenSkeleton e.2.1
      (assemble z w fun i => v (rightMomentIndex i)) *
    ρ.r324CovarianceFourierConfigurationTerm ε κ.1 v q

/-- The full-pairing physical integrand is pointwise the sum of its
Fourier configurations. -/
theorem momentFullPairingPhysicalIntegrand_eq_configuration_tsum
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    momentFullPairingPhysicalIntegrand
        ρ ε m α β κ x y z w v =
      ∑' q,
        ρ.r324FullPairingFourierIntegrand
          ε α β κ q x y z w v := by
  rw [momentFullPairingPhysicalIntegrand_eq_skeletons_mul_covariance]
  rw [ρ.primitiveCovarianceProduct_eq_r324_configuration_tsum
    hε κ.1 v]
  let e := (momentContractionEquivFullPairing m).symm κ
  let P : ℂ :=
    momentFourierPhase α β x y z w *
      renormalizedGreenSkeleton e.1
        (assemble x y fun i => v (leftMomentIndex i)) *
      renormalizedGreenSkeleton e.2.1
        (assemble z w fun i => v (rightMomentIndex i))
  have hsum :=
    ρ.summable_r324CovarianceFourierConfigurationTerm
      hε κ.1 v
  change
    P * (∑' q,
      ρ.r324CovarianceFourierConfigurationTerm ε κ.1 v q) =
      ∑' q,
        P *
          ρ.r324CovarianceFourierConfigurationTerm ε κ.1 v q
  exact (hsum.tsum_mul_left P).symm

/-- Every fixed Fourier configuration is jointly integrable on the
genuine physical product space. -/
theorem integrable_r324Flatten_fullPairingFourierIntegrand
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q :
      Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card → Z4) :
    Integrable
      (r324Flatten
        (ρ.r324FullPairingFourierIntegrand ε α β κ q))
      (r324PhysicalMeasure m) := by
  let e := (momentContractionEquivFullPairing m).symm κ
  let bare : R324PhysicalPoint m → ℂ := fun p =>
    renormalizedGreenSkeleton e.1
        (assemble p.1 p.2.1
          fun i => p.2.2.2.2 (leftMomentIndex i)) *
      renormalizedGreenSkeleton e.2.1
        (assemble p.2.2.1 p.2.2.2.1
          fun i => p.2.2.2.2 (rightMomentIndex i))
  let weight : R324PhysicalPoint m → ℂ := fun p =>
    momentFourierPhase α β
        p.1 p.2.1 p.2.2.1 p.2.2.2.1 *
      ρ.r324CovarianceFourierConfigurationTerm
        ε κ.1 p.2.2.2.2 q
  have hbare : Integrable bare (r324PhysicalMeasure m) := by
    refine
      (integrable_r324Flatten_renormalizedGreenSkeleton_product
        e.1 e.2.1).congr (.of_forall fun p => ?_)
    rfl
  have hx : Measurable fun p : R324PhysicalPoint m => p.1 :=
    measurable_fst
  have hy : Measurable fun p : R324PhysicalPoint m => p.2.1 :=
    measurable_fst.comp measurable_snd
  have hz : Measurable fun p : R324PhysicalPoint m => p.2.2.1 :=
    measurable_fst.comp
      (measurable_snd.comp measurable_snd)
  have hw : Measurable fun p : R324PhysicalPoint m => p.2.2.2.1 :=
    measurable_fst.comp
      (measurable_snd.comp
        (measurable_snd.comp measurable_snd))
  have hv :
      Measurable fun p : R324PhysicalPoint m => p.2.2.2.2 :=
    measurable_snd.comp
      (measurable_snd.comp
        (measurable_snd.comp measurable_snd))
  have hphase :
      Measurable fun p : R324PhysicalPoint m =>
        momentFourierPhase α β
          p.1 p.2.1 p.2.2.1 p.2.2.2.1 := by
    unfold momentFourierPhase
    exact
      ((((continuous_charT4 α).measurable.comp hx).mul
        ((continuous_charT4 β).measurable.comp hy)).mul
        ((continuous_charT4 (-α)).measurable.comp hz)).mul
        ((continuous_charT4 (-β)).measurable.comp hw)
  have hweightMeas : Measurable weight := by
    exact hphase.mul
      ((ρ.measurable_r324CovarianceFourierConfigurationTerm
        ε κ.1 q).comp hv)
  have hweightBound :
      ∀ p : R324PhysicalPoint m,
        ‖weight p‖ ≤
          ρ.r324CovarianceConfigurationWeight ε κ.1 q := by
    intro p
    unfold weight
    rw [norm_mul]
    have hphaseNorm :
        ‖momentFourierPhase α β
          p.1 p.2.1 p.2.2.1 p.2.2.2.1‖ = 1 := by
      unfold momentFourierPhase
      simp only [norm_mul, norm_charT4, mul_one]
    rw [hphaseNorm, one_mul,
      ρ.norm_r324CovarianceFourierConfigurationTerm]
  have hproduct :=
    hbare.mul_bdd hweightMeas.aestronglyMeasurable
      (.of_forall hweightBound)
  convert hproduct using 1
  funext p
  unfold bare weight r324Flatten
    r324FullPairingFourierIntegrand
  dsimp only
  ring

/-- The integrated contribution of one full-pairing Fourier
configuration. -/
def r324FullPairingFourierIntegral
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q :
      Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card → Z4) :
    ℂ :=
  ∫ p,
    r324Flatten
      (ρ.r324FullPairingFourierIntegrand ε α β κ q) p
    ∂(r324PhysicalMeasure m)

/-- The `L¹` norms of all Fourier-configuration integrands are summable. -/
theorem summable_integral_norm_r324FullPairingFourierIntegrand
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    Summable fun q =>
      ∫ p,
        ‖r324Flatten
          (ρ.r324FullPairingFourierIntegrand ε α β κ q) p‖
        ∂(r324PhysicalMeasure m) := by
  let e := (momentContractionEquivFullPairing m).symm κ
  let bare : R324PhysicalPoint m → ℂ := fun p =>
    renormalizedGreenSkeleton e.1
        (assemble p.1 p.2.1
          fun i => p.2.2.2.2 (leftMomentIndex i)) *
      renormalizedGreenSkeleton e.2.1
        (assemble p.2.2.1 p.2.2.2.1
          fun i => p.2.2.2.2 (rightMomentIndex i))
  let B : ℝ :=
    ∫ p, ‖bare p‖ ∂(r324PhysicalMeasure m)
  have hweight :=
    ρ.summable_r324CovarianceConfigurationWeight hε κ.1
  have hscaled :
      Summable fun q =>
        ρ.r324CovarianceConfigurationWeight ε κ.1 q * B :=
    hweight.mul_right B
  refine hscaled.congr fun q => ?_
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  unfold r324Flatten r324FullPairingFourierIntegrand bare
  dsimp only
  simp only [norm_mul]
  have hphaseNorm :
      ‖momentFourierPhase α β
        p.1 p.2.1 p.2.2.1 p.2.2.2.1‖ = 1 := by
    unfold momentFourierPhase
    simp only [norm_mul, norm_charT4, mul_one]
  rw [hphaseNorm, one_mul,
    ρ.norm_r324CovarianceFourierConfigurationTerm]
  ring

/-- The physical integral of one full pairing is exactly the countable
sum of the integrals of its Fourier configurations. -/
theorem integral_momentFullPairingPhysicalIntegrand_eq_configuration_tsum
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    (∫ p,
      r324Flatten
        (momentFullPairingPhysicalIntegrand
          ρ ε m α β κ) p
      ∂(r324PhysicalMeasure m)) =
      ∑' q,
        ρ.r324FullPairingFourierIntegral ε α β κ q := by
  calc
    (∫ p,
      r324Flatten
        (momentFullPairingPhysicalIntegrand
          ρ ε m α β κ) p
      ∂(r324PhysicalMeasure m)) =
        ∫ p,
          ∑' q,
            r324Flatten
              (ρ.r324FullPairingFourierIntegrand
                ε α β κ q) p
          ∂(r324PhysicalMeasure m) := by
      apply integral_congr_ae
      filter_upwards with p
      exact
        ρ.momentFullPairingPhysicalIntegrand_eq_configuration_tsum
          hε α β κ p.1 p.2.1 p.2.2.1 p.2.2.2.1
          p.2.2.2.2
    _ = ∑' q,
        ρ.r324FullPairingFourierIntegral ε α β κ q := by
      exact
        (integral_tsum_of_summable_integral_norm
          (fun q =>
            ρ.integrable_r324Flatten_fullPairingFourierIntegrand
              ε α β κ q)
          (ρ.summable_integral_norm_r324FullPairingFourierIntegrand
            hε α β κ)).symm

end SmoothCutoff

end

end Anderson4D
