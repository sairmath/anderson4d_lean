import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedCoreFourier

/-!
# Integrated Fourier terms for residual-refined R-324 cores

This module turns the pointwise common-increment grouping into the exact
endpoint-first configuration series required by
`R324ConcreteRefinedCoreExpansion`.

The physical product measure is stored in the order `(x,y,z,w,v)`, while
the grouped endpoint term integrates the internal tuple `v` first.  We
therefore construct the actual measure-preserving cyclic permutation and
use joint integrability before changing the order of integration.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Moving the internal tuple in front of the four endpoints -/

/-- The four external variables in their frozen order. -/
abbrev R324EndpointPoint :=
  T4 × (T4 × (T4 × T4))

/-- Product measure on the four external variables. -/
def r324EndpointMeasure : Measure R324EndpointPoint :=
  paperMeasure.prod
    (paperMeasure.prod
      (paperMeasure.prod paperMeasure))

/-- Cyclic permutation
`(x,y,z,w,v) ↦ (v,x,y,z,w)` of the physical product space. -/
def r324InternalFirstMeasurableEquiv (m : ℕ) :
    R324PhysicalPoint m ≃ᵐ
      (Fin (2 * m) → T4) × R324EndpointPoint :=
  let V := Fin (2 * m) → T4
  let e₁ :
      T4 × (T4 × (T4 × (T4 × V))) ≃ᵐ
        T4 × (T4 × (T4 × (V × T4))) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodComm :
            T4 × V ≃ᵐ V × T4)))
  let e₂ :
      T4 × (T4 × (T4 × (V × T4))) ≃ᵐ
        T4 × (T4 × (V × (T4 × T4))) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (r324MoveMiddleMeasurableEquiv T4 V T4))
  let e₃ :
      T4 × (T4 × (V × (T4 × T4))) ≃ᵐ
        T4 × (V × (T4 × (T4 × T4))) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      (r324MoveMiddleMeasurableEquiv
        T4 V (T4 × T4))
  let e₄ :
      T4 × (V × (T4 × (T4 × T4))) ≃ᵐ
        V × (T4 × (T4 × (T4 × T4))) :=
    r324MoveMiddleMeasurableEquiv
      T4 V (T4 × (T4 × T4))
  e₁.trans (e₂.trans (e₃.trans e₄))

@[simp]
theorem r324InternalFirstMeasurableEquiv_apply
    {m : ℕ} (p : R324PhysicalPoint m) :
    r324InternalFirstMeasurableEquiv m p =
      (p.2.2.2.2,
        (p.1, p.2.1, p.2.2.1, p.2.2.2.1)) := by
  rfl

theorem measurePreserving_r324InternalFirstMeasurableEquiv
    (m : ℕ) :
    MeasurePreserving
      (r324InternalFirstMeasurableEquiv m)
      (r324PhysicalMeasure m)
      ((Measure.pi fun _ : Fin (2 * m) => paperMeasure).prod
        r324EndpointMeasure) := by
  let μ : Measure T4 := paperMeasure
  let ν : Measure (Fin (2 * m) → T4) :=
    Measure.pi fun _ : Fin (2 * m) => paperMeasure
  let hp₁ :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl T4)
            (MeasurableEquiv.prodCongr
              (MeasurableEquiv.refl T4)
              (MeasurableEquiv.prodComm :
                T4 × (Fin (2 * m) → T4) ≃ᵐ
                  (Fin (2 * m) → T4) × T4))))
        (μ.prod (μ.prod (μ.prod (μ.prod ν))))
        (μ.prod (μ.prod (μ.prod (ν.prod μ)))) :=
    (MeasurePreserving.id μ).prod
      ((MeasurePreserving.id μ).prod
        ((MeasurePreserving.id μ).prod
          (Measure.measurePreserving_swap
            (μ := μ) (ν := ν))))
  let hp₂ :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl T4)
            (r324MoveMiddleMeasurableEquiv
              T4 (Fin (2 * m) → T4) T4)))
        (μ.prod (μ.prod (μ.prod (ν.prod μ))))
        (μ.prod (μ.prod (ν.prod (μ.prod μ)))) :=
    (MeasurePreserving.id μ).prod
      ((MeasurePreserving.id μ).prod
        (measurePreserving_r324MoveMiddleMeasurableEquiv
          μ ν μ))
  let hp₃ :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (r324MoveMiddleMeasurableEquiv
            T4 (Fin (2 * m) → T4) (T4 × T4)))
        (μ.prod (μ.prod (ν.prod (μ.prod μ))))
        (μ.prod (ν.prod (μ.prod (μ.prod μ)))) :=
    (MeasurePreserving.id μ).prod
      (measurePreserving_r324MoveMiddleMeasurableEquiv
        μ ν (μ.prod μ))
  let hp₄ :
      MeasurePreserving
        (r324MoveMiddleMeasurableEquiv
          T4 (Fin (2 * m) → T4) (T4 × (T4 × T4)))
        (μ.prod (ν.prod (μ.prod (μ.prod μ))))
        (ν.prod (μ.prod (μ.prod (μ.prod μ)))) :=
    measurePreserving_r324MoveMiddleMeasurableEquiv
      μ ν (μ.prod (μ.prod μ))
  change
    MeasurePreserving
      (r324InternalFirstMeasurableEquiv m)
      (μ.prod (μ.prod (μ.prod (μ.prod ν))))
      (ν.prod (μ.prod (μ.prod (μ.prod μ))))
  exact hp₄.comp (hp₃.comp (hp₂.comp hp₁))

/-- Joint integrability licenses the endpoint-first integration order
used by `r324GroupedEndpointConfigurationTerm`. -/
theorem r324_integral_product_eq_internal_first
    {m : ℕ}
    (f : T4 → T4 → T4 → T4 →
      (Fin (2 * m) → T4) → ℂ)
    (hf : Integrable (r324Flatten f)
      (r324PhysicalMeasure m)) :
    (∫ p, r324Flatten f p ∂(r324PhysicalMeasure m)) =
      ∫ v, ∫ x, ∫ y, ∫ z, ∫ w,
        f x y z w v
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  let e := r324InternalFirstMeasurableEquiv m
  let ν := Measure.pi fun _ : Fin (2 * m) => paperMeasure
  let g :
      (Fin (2 * m) → T4) × R324EndpointPoint → ℂ :=
    fun p => f p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 p.1
  have hp :
      MeasurePreserving e
        (r324PhysicalMeasure m)
        (ν.prod r324EndpointMeasure) :=
    measurePreserving_r324InternalFirstMeasurableEquiv m
  have htarget : Integrable g
      (ν.prod r324EndpointMeasure) := by
    have hsource :
        Integrable (g ∘ e)
          (r324PhysicalMeasure m) := by
      convert hf using 1
      funext p
      rfl
    exact hp.integrable_comp_emb e.measurableEmbedding
      |>.mp hsource
  calc
    (∫ p, r324Flatten f p ∂(r324PhysicalMeasure m)) =
        ∫ p, g (e p) ∂(r324PhysicalMeasure m) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by rfl
    _ = ∫ p, g p ∂(ν.prod r324EndpointMeasure) :=
      hp.integral_comp e.measurableEmbedding g
    _ = ∫ v, ∫ x, ∫ y, ∫ z, ∫ w,
          f x y z w v
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure ∂ν := by
      unfold r324EndpointMeasure at htarget ⊢
      rw [integral_prod _ htarget]
      apply integral_congr_ae
      filter_upwards [htarget.prod_right_ae] with v hv
      rw [integral_prod _ hv]
      apply integral_congr_ae
      filter_upwards [hv.prod_right_ae] with x hx
      rw [integral_prod _ hx]
      apply integral_congr_ae
      filter_upwards [hx.prod_right_ae] with y hy
      rw [integral_prod _ hy]

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## Raw refined endpoint configurations -/

/-- Interior core of one ungrouped refined contraction/configuration. -/
def r324RefinedRawEndpointCore
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (v : Fin (2 * m) → T4) : ℂ :=
  let e₀ := r324RefinedScheduleRepresentative p
  r324RenormalizedInteriorCore e₀.1
      (fun i => v (leftMomentIndex i)) *
    r324RenormalizedInteriorCore e₀.2.1
      (fun i => v (rightMomentIndex i)) *
    ρ.r324RefinedRawCovarianceConfiguration hm ε p a v

/-- Endpoint-separated physical integrand of one ungrouped refined
configuration. -/
def r324RefinedRawEndpointIntegrand
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  let e₀ := r324RefinedScheduleRepresentative p
  r324EndpointSeparatedIntegrand α β
    (r324ContractionEndpointAnchors hm e₀ v)
    (r324ContractionEndpointFlags e₀)
    (ρ.r324RefinedRawEndpointCore hm ε p a v)
    x y z w

/-- One raw refined endpoint integrand is exactly the already-integrable
full-pairing Fourier integrand selected by its contraction/configuration
index. -/
theorem r324RefinedRawEndpointIntegrand_eq_fullPairing
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ρ.r324RefinedRawEndpointIntegrand
        hm ε α β p a x y z w v =
      let u := r324NatEquivRefinedContractionConfigurations p a
      let κ := momentContractionEquivFullPairing m u.1.1
      ρ.r324FullPairingFourierIntegrand ε α β κ
        (r324FullConfigurationOfStandard κ
          (r324NatEquivStandardConfigurations hm u.2))
        x y z w v := by
  let u := r324NatEquivRefinedContractionConfigurations p a
  let e : MomentContraction m := u.1.1
  let κ := momentContractionEquivFullPairing m e
  let e₀ := r324RefinedScheduleRepresentative p
  have he :
      e ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1 :=
    u.1.2
  have heSignature :
      momentContractionSignature e = p.1.1 :=
    (mem_momentRefinedContractionFiber.mp he).1
  have he₀Signature :
      momentContractionSignature e₀ = p.1.1 :=
    mem_momentContractionFiber.mp
      (r324RefinedScheduleRepresentative_mem p)
  obtain ⟨hleft, hright⟩ :=
    renormalizedGreenSkeletons_eq_of_momentContractionSignature_eq
      e e₀ (heSignature.trans he₀Signature.symm)
  have hκ :
      (momentContractionEquivFullPairing m).symm κ = e := by
    simp [κ]
  change
    r324EndpointSeparatedIntegrand α β
        (r324ContractionEndpointAnchors hm e₀ v)
        (r324ContractionEndpointFlags e₀)
        (r324RenormalizedInteriorCore e₀.1
            (fun i => v (leftMomentIndex i)) *
          r324RenormalizedInteriorCore e₀.2.1
            (fun i => v (rightMomentIndex i)) *
          ρ.r324NatCovarianceConfigurationTerm
            hm ε κ u.2 v)
        x y z w =
      ρ.r324FullPairingFourierIntegrand ε α β κ
        (r324FullConfigurationOfStandard κ
          (r324NatEquivStandardConfigurations hm u.2))
        x y z w v
  unfold r324FullPairingFourierIntegrand
  dsimp only
  rw [hκ, hleft, hright,
    renormalizedGreenSkeleton_eq_endpointKernels_mul_core
      hm e₀.1 x y (fun i => v (leftMomentIndex i)),
    renormalizedGreenSkeleton_eq_endpointKernels_mul_core
      hm e₀.2.1 z w (fun i => v (rightMomentIndex i))]
  unfold r324EndpointSeparatedIntegrand
    r324NatCovarianceConfigurationTerm
    momentFourierPhase
  simp only [r324ContractionEndpointAnchors_zero,
    r324ContractionEndpointAnchors_one,
    r324ContractionEndpointAnchors_two,
    r324ContractionEndpointAnchors_three,
    r324ContractionEndpointFlags_zero,
    r324ContractionEndpointFlags_one,
    r324ContractionEndpointFlags_two,
    r324ContractionEndpointFlags_three]
  ring

/-- Every raw refined endpoint integrand is jointly integrable on the
genuine five-group physical product space. -/
theorem integrable_r324Flatten_refinedRawEndpointIntegrand
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    Integrable
      (r324Flatten
        (ρ.r324RefinedRawEndpointIntegrand
          hm ε α β p a))
      (r324PhysicalMeasure m) := by
  let u := r324NatEquivRefinedContractionConfigurations p a
  let κ := momentContractionEquivFullPairing m u.1.1
  have hfull :=
    ρ.integrable_r324Flatten_fullPairingFourierIntegrand
      ε α β κ
      (r324FullConfigurationOfStandard κ
        (r324NatEquivStandardConfigurations hm u.2))
  refine hfull.congr ?_
  filter_upwards with q
  exact
    (ρ.r324RefinedRawEndpointIntegrand_eq_fullPairing
      hm ε α β p a
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2).symm

/-- Natural standardized configurations of one full pairing have
summable physical `L¹` masses. -/
private theorem
    summable_integral_norm_r324NatFullPairingFourierIntegrand
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4) (κ : R324FullPairingIndex m) :
    Summable fun a : ℕ =>
      ∫ q,
        ‖r324Flatten
          (ρ.r324FullPairingFourierIntegrand
            ε α β κ
            (r324FullConfigurationOfStandard κ
              (r324NatEquivStandardConfigurations hm a))) q‖
        ∂(r324PhysicalMeasure m) := by
  have horiginal :=
    ρ.summable_integral_norm_r324FullPairingFourierIntegrand
      hε α β κ
  have hstandard :=
    horiginal.comp_injective
      (r324FullConfigurationEquiv κ).injective
  have hnat :=
    hstandard.comp_injective
      (r324NatEquivStandardConfigurations hm).injective
  exact hnat.congr fun a => by rfl

/-- Physical `L¹` mass of one raw refined configuration. -/
def r324RefinedRawEndpointL1
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ) : ℝ :=
  ∫ q,
    ‖r324Flatten
      (ρ.r324RefinedRawEndpointIntegrand
        hm ε α β p a) q‖
    ∂(r324PhysicalMeasure m)

/-- The raw configurations in one whole refined fibre have summable
physical `L¹` masses. -/
theorem summable_r324RefinedRawEndpointL1
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    Summable
      (ρ.r324RefinedRawEndpointL1
        hm ε α β p) := by
  let F :
      R324RefinedContractionIndex p × ℕ → ℝ := fun u =>
    let κ := momentContractionEquivFullPairing m u.1.1
    ∫ q,
      ‖r324Flatten
        (ρ.r324FullPairingFourierIntegrand
          ε α β κ
          (r324FullConfigurationOfStandard κ
            (r324NatEquivStandardConfigurations hm u.2))) q‖
      ∂(r324PhysicalMeasure m)
  have hF : Summable F := by
    rw [summable_prod_of_nonneg
      (fun u => integral_nonneg fun _ => norm_nonneg _)]
    constructor
    · intro e
      exact
        ρ.summable_integral_norm_r324NatFullPairingFourierIntegrand
          hm hε α β
          (momentContractionEquivFullPairing m e.1)
    · exact Summable.of_finite
  have hpre :=
    hF.comp_injective
      (r324NatEquivRefinedContractionConfigurations p).injective
  exact hpre.congr fun a => by
    unfold r324RefinedRawEndpointL1
    apply integral_congr_ae
    filter_upwards with q
    exact congrArg norm
      (ρ.r324RefinedRawEndpointIntegrand_eq_fullPairing
        hm ε α β p a
        q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2).symm

/-! ## Common-increment grouped endpoint integrands -/

/-- An endpoint-separated integrand commutes with a summable fibrewise
`tsum`, because its dependence on the supplied core is linear. -/
theorem r324EndpointSeparatedIntegrand_tsumByKey
    {K : Type*}
    (α β : Z4) (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags)
    (core : ℕ → ℂ) (key : ℕ → K) (k : K)
    (x y z w : T4) :
    r324EndpointSeparatedIntegrand α β anchors flags
        (tsumByKey core key k) x y z w =
      tsumByKey
        (fun a =>
          r324EndpointSeparatedIntegrand α β anchors flags
            (core a) x y z w)
        key k := by
  unfold r324EndpointSeparatedIntegrand tsumByKey
  rw [tsum_mul_left]

/-- The key-grouped endpoint core is the fibrewise `tsum` of the raw
endpoint cores sharing that increment vector. -/
theorem r324KeyGroupedRefinedEndpointCore_eq_tsumByKey
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (v : Fin (2 * m) → T4) :
    ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v =
      tsumByKey
        (ρ.r324RefinedRawEndpointCore hm ε p · v)
        (r324RefinedRawIncrementKey hm p)
        (r324NatEquivStandardConfigurations hm b) := by
  let e₀ := r324RefinedScheduleRepresentative p
  unfold r324KeyGroupedRefinedEndpointCore
    r324KeyGroupedCovarianceConfiguration
    r324RefinedRawEndpointCore
  change
    (r324RenormalizedInteriorCore e₀.1
          (fun i => v (leftMomentIndex i)) *
        r324RenormalizedInteriorCore e₀.2.1
          (fun i => v (rightMomentIndex i))) *
        tsumByKey
          (ρ.r324RefinedRawCovarianceConfiguration
            hm ε p · v)
          (r324RefinedRawIncrementKey hm p)
          (r324NatEquivStandardConfigurations hm b) =
      tsumByKey
        (fun a =>
          (r324RenormalizedInteriorCore e₀.1
              (fun i => v (leftMomentIndex i)) *
            r324RenormalizedInteriorCore e₀.2.1
              (fun i => v (rightMomentIndex i))) *
            ρ.r324RefinedRawCovarianceConfiguration
              hm ε p a v)
        (r324RefinedRawIncrementKey hm p)
        (r324NatEquivStandardConfigurations hm b)
  unfold tsumByKey
  rw [tsum_mul_left]

/-- Endpoint-separated physical integrand of one common-increment group. -/
def r324KeyGroupedRefinedEndpointIntegrand
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  let e₀ := r324RefinedScheduleRepresentative p
  r324EndpointSeparatedIntegrand α β
    (r324ContractionEndpointAnchors hm e₀ v)
    (r324ContractionEndpointFlags e₀)
    (ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v)
    x y z w

/-- Pointwise common-increment grouping.  The complete compatible
primitive fibre is formed inside this `tsum` before any integral or norm. -/
theorem r324KeyGroupedRefinedEndpointIntegrand_eq_tsumByKey
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ρ.r324KeyGroupedRefinedEndpointIntegrand
        hm ε α β p b x y z w v =
      tsumByKey
        (fun a =>
          ρ.r324RefinedRawEndpointIntegrand
            hm ε α β p a x y z w v)
        (r324RefinedRawIncrementKey hm p)
        (r324NatEquivStandardConfigurations hm b) := by
  let e₀ := r324RefinedScheduleRepresentative p
  unfold r324KeyGroupedRefinedEndpointIntegrand
    r324RefinedRawEndpointIntegrand
  rw [ρ.r324KeyGroupedRefinedEndpointCore_eq_tsumByKey
    hm ε p b v]
  exact
    r324EndpointSeparatedIntegrand_tsumByKey
      α β
      (r324ContractionEndpointAnchors hm e₀ v)
      (r324ContractionEndpointFlags e₀)
      (ρ.r324RefinedRawEndpointCore hm ε p · v)
      (r324RefinedRawIncrementKey hm p)
      (r324NatEquivStandardConfigurations hm b)
      x y z w

/-! ## Summable scalar majorants for the grouped series -/

/-- Coordinate-independent absolute covariance weight of one raw
refined configuration. -/
def r324RefinedRawCovarianceWeight
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (a : ℕ) : ℝ :=
  let u := r324NatEquivRefinedContractionConfigurations p a
  let κ := momentContractionEquivFullPairing m u.1.1
  ρ.r324NatCovarianceConfigurationWeight hm ε κ u.2

theorem r324RefinedRawCovarianceWeight_nonneg
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    0 ≤ ρ.r324RefinedRawCovarianceWeight
      hm ε p a := by
  unfold r324RefinedRawCovarianceWeight
    r324NatCovarianceConfigurationWeight
  exact
    ρ.r324CovarianceConfigurationWeight_nonneg ε _ _

theorem norm_r324RefinedRawCovarianceConfiguration
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (v : Fin (2 * m) → T4) :
    ‖ρ.r324RefinedRawCovarianceConfiguration
        hm ε p a v‖ =
      ρ.r324RefinedRawCovarianceWeight hm ε p a := by
  unfold r324RefinedRawCovarianceConfiguration
    r324RefinedRawCovarianceWeight
  exact
    ρ.norm_r324NatCovarianceConfigurationTerm
      hm ε _ _ v

theorem summable_r324RefinedRawCovarianceWeight
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m) :
    Summable
      (ρ.r324RefinedRawCovarianceWeight hm ε p) := by
  let v₀ : Fin (2 * m) → T4 := fun _ => 0
  exact
    (ρ.summable_norm_r324RefinedRawCovarianceConfiguration
      hm hε p v₀).congr fun a =>
        ρ.norm_r324RefinedRawCovarianceConfiguration
          hm ε p a v₀

/-- Common two-skeleton factor of a whole refined fibre. -/
def r324RefinedRepresentativeBare
    {m : ℕ} (p : R324RefinedScheduleIndex m)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  let e₀ := r324RefinedScheduleRepresentative p
  renormalizedGreenSkeleton e₀.1
      (assemble x y fun i => v (leftMomentIndex i)) *
    renormalizedGreenSkeleton e₀.2.1
      (assemble z w fun i => v (rightMomentIndex i))

theorem integrable_r324Flatten_refinedRepresentativeBare
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    Integrable
      (r324Flatten (r324RefinedRepresentativeBare p))
      (r324PhysicalMeasure m) := by
  let e₀ := r324RefinedScheduleRepresentative p
  exact
    integrable_r324Flatten_renormalizedGreenSkeleton_product
      e₀.1 e₀.2.1

/-- Exact pointwise norm separation into the common physical skeleton
and the coordinate-independent covariance weight. -/
theorem norm_r324RefinedRawEndpointIntegrand
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ‖ρ.r324RefinedRawEndpointIntegrand
        hm ε α β p a x y z w v‖ =
      ‖r324RefinedRepresentativeBare p x y z w v‖ *
        ρ.r324RefinedRawCovarianceWeight hm ε p a := by
  let u := r324NatEquivRefinedContractionConfigurations p a
  let e : MomentContraction m := u.1.1
  let κ := momentContractionEquivFullPairing m e
  let e₀ := r324RefinedScheduleRepresentative p
  have he :
      e ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1 :=
    u.1.2
  have heSignature :
      momentContractionSignature e = p.1.1 :=
    (mem_momentRefinedContractionFiber.mp he).1
  have he₀Signature :
      momentContractionSignature e₀ = p.1.1 :=
    mem_momentContractionFiber.mp
      (r324RefinedScheduleRepresentative_mem p)
  obtain ⟨hleft, hright⟩ :=
    renormalizedGreenSkeletons_eq_of_momentContractionSignature_eq
      e e₀ (heSignature.trans he₀Signature.symm)
  have hκ :
      (momentContractionEquivFullPairing m).symm κ = e := by
    simp [κ]
  rw [ρ.r324RefinedRawEndpointIntegrand_eq_fullPairing
    hm ε α β p a x y z w v]
  change
    ‖ρ.r324FullPairingFourierIntegrand ε α β κ
        (r324FullConfigurationOfStandard κ
          (r324NatEquivStandardConfigurations hm u.2))
        x y z w v‖ =
      ‖r324RefinedRepresentativeBare p x y z w v‖ *
        ρ.r324RefinedRawCovarianceWeight hm ε p a
  unfold r324FullPairingFourierIntegrand
    r324RefinedRepresentativeBare
    r324RefinedRawCovarianceWeight
    r324NatCovarianceConfigurationWeight
  dsimp only
  rw [hκ, hleft, hright]
  simp only [norm_mul]
  have hphase :
      ‖momentFourierPhase α β x y z w‖ = 1 := by
    unfold momentFourierPhase
    simp only [norm_mul, norm_charT4, mul_one]
  rw [hphase, one_mul,
    ρ.norm_r324CovarianceFourierConfigurationTerm]

/-! ## Integrability of every common-increment group -/

/-- Scalar covariance budget of one common-increment group. -/
def r324KeyGroupedRefinedCovarianceWeight
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (b : ℕ) : ℝ :=
  tsumByKey
    (ρ.r324RefinedRawCovarianceWeight hm ε p)
    (r324RefinedRawIncrementKey hm p)
    (r324NatEquivStandardConfigurations hm b)

theorem r324KeyGroupedRefinedCovarianceWeight_nonneg
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (b : ℕ) :
    0 ≤ ρ.r324KeyGroupedRefinedCovarianceWeight
      hm ε p b := by
  unfold r324KeyGroupedRefinedCovarianceWeight
    tsumByKey
  exact tsum_nonneg fun a =>
    ρ.r324RefinedRawCovarianceWeight_nonneg
      hm ε p a.1

theorem summable_r324KeyGroupedRefinedCovarianceWeight
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m) :
    Summable
      (ρ.r324KeyGroupedRefinedCovarianceWeight
        hm ε p) := by
  have hkey :
      Summable fun k : Fin m → Z4 =>
        tsumByKey
          (ρ.r324RefinedRawCovarianceWeight hm ε p)
          (r324RefinedRawIncrementKey hm p) k :=
    summable_tsumByKey _ _
      (ρ.summable_r324RefinedRawCovarianceWeight
        hm hε p)
  have hnat :=
    hkey.comp_injective
      (r324NatEquivStandardConfigurations hm).injective
  exact hnat.congr fun b => by rfl

/-- Pointwise norm bound by the common two-skeleton factor and the
scalar weight of the whole increment group. -/
theorem norm_r324KeyGroupedRefinedEndpointIntegrand_le
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ‖ρ.r324KeyGroupedRefinedEndpointIntegrand
        hm ε α β p b x y z w v‖ ≤
      ‖r324RefinedRepresentativeBare p x y z w v‖ *
        ρ.r324KeyGroupedRefinedCovarianceWeight
          hm ε p b := by
  let key : Fin m → Z4 :=
    r324NatEquivStandardConfigurations hm b
  let S :=
    {a : ℕ //
      r324RefinedRawIncrementKey hm p a = key}
  let B : ℝ :=
    ‖r324RefinedRepresentativeBare p x y z w v‖
  have hraw :
      Summable fun a =>
        ‖ρ.r324RefinedRawEndpointIntegrand
          hm ε α β p a x y z w v‖ := by
    have hscaled :=
      (ρ.summable_r324RefinedRawCovarianceWeight
        hm hε p).mul_left B
    exact hscaled.congr fun a =>
      (ρ.norm_r324RefinedRawEndpointIntegrand
        hm ε α β p a x y z w v).symm
  have hsub :
      Summable fun a : S =>
        ‖ρ.r324RefinedRawEndpointIntegrand
          hm ε α β p a.1 x y z w v‖ :=
    hraw.subtype _
  rw [ρ.r324KeyGroupedRefinedEndpointIntegrand_eq_tsumByKey
    hm ε α β p b x y z w v]
  unfold r324KeyGroupedRefinedCovarianceWeight
    tsumByKey
  change
    ‖∑' a : S,
        ρ.r324RefinedRawEndpointIntegrand
          hm ε α β p a.1 x y z w v‖ ≤
      B *
        ∑' a : S,
          ρ.r324RefinedRawCovarianceWeight
            hm ε p a.1
  calc
    ‖∑' a : S,
        ρ.r324RefinedRawEndpointIntegrand
          hm ε α β p a.1 x y z w v‖ ≤
        ∑' a : S,
          ‖ρ.r324RefinedRawEndpointIntegrand
            hm ε α β p a.1 x y z w v‖ :=
      norm_tsum_le_tsum_norm hsub
    _ = ∑' a : S,
          B *
            ρ.r324RefinedRawCovarianceWeight
              hm ε p a.1 := by
      apply tsum_congr
      intro a
      exact
        ρ.norm_r324RefinedRawEndpointIntegrand
          hm ε α β p a.1 x y z w v
    _ = B *
          ∑' a : S,
            ρ.r324RefinedRawCovarianceWeight
              hm ε p a.1 := by
      rw [tsum_mul_left]

/-- Every common-increment group is jointly integrable. -/
theorem integrable_r324Flatten_keyGroupedRefinedEndpointIntegrand
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ) :
    Integrable
      (r324Flatten
        (ρ.r324KeyGroupedRefinedEndpointIntegrand
          hm ε α β p b))
      (r324PhysicalMeasure m) := by
  let W :=
    ρ.r324KeyGroupedRefinedCovarianceWeight
      hm ε p b
  have hbare :=
    integrable_r324Flatten_refinedRepresentativeBare p
  have hbound :
      Integrable
        (fun q : R324PhysicalPoint m =>
          W *
            ‖r324Flatten
              (r324RefinedRepresentativeBare p) q‖)
        (r324PhysicalMeasure m) := by
    simpa only [smul_eq_mul] using
      hbare.norm.const_mul W
  have hmeas :
      AEStronglyMeasurable
        (r324Flatten
          (ρ.r324KeyGroupedRefinedEndpointIntegrand
            hm ε α β p b))
        (r324PhysicalMeasure m) := by
    let key : Fin m → Z4 :=
      r324NatEquivStandardConfigurations hm b
    let S :=
      {a : ℕ //
        r324RefinedRawIncrementKey hm p a = key}
    have hsumMeas :
        AEMeasurable
          (fun q : R324PhysicalPoint m =>
            ∑' a : S,
              r324Flatten
                (ρ.r324RefinedRawEndpointIntegrand
                  hm ε α β p a.1) q)
          (r324PhysicalMeasure m) := by
      exact AEMeasurable.tsum fun a =>
        (ρ.integrable_r324Flatten_refinedRawEndpointIntegrand
          hm ε α β p a.1).aemeasurable
    have heq :
        (r324Flatten
            (ρ.r324KeyGroupedRefinedEndpointIntegrand
              hm ε α β p b)) =ᵐ[
          r324PhysicalMeasure m]
          (fun q : R324PhysicalPoint m =>
            ∑' a : S,
              r324Flatten
                (ρ.r324RefinedRawEndpointIntegrand
                  hm ε α β p a.1) q) := by
      exact Filter.Eventually.of_forall fun q =>
        ρ.r324KeyGroupedRefinedEndpointIntegrand_eq_tsumByKey
          hm ε α β p b
          q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
    exact (hsumMeas.congr heq.symm).aestronglyMeasurable
  apply Integrable.mono' hbound hmeas
  exact Filter.Eventually.of_forall fun q => by
    have h :=
      ρ.norm_r324KeyGroupedRefinedEndpointIntegrand_le
        hm hε α β p b
        q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
    simpa only [W, r324Flatten, mul_comm] using h

end SmoothCutoff

end

end Anderson4D
