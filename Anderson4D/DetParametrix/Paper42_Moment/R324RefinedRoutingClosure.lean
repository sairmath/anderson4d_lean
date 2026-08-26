import Anderson4D.DetParametrix.Paper42_Moment.R324GroupedRoutingClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointFiberClosure

/-!
# Residual-refined countable routing for R-324

The raw full-pairing Fourier series cannot be bounded termwise without
losing the primitive-pairing cancellation.  This file therefore indexes
the final countable series by a genuine residual-refined schedule.  Every
configuration core contains the compatible primitive fibre sum before
the four endpoint variables are integrated and before a norm is taken.

The data structure below records exact expansion and Fubini identities,
not the target estimate.  A separate constructor turns a proved local
configuration estimate into the concrete
`CountableCentralRoutedMomentReductionOutput`; its total endpoint budget
is derived from summability and the explicit endpoint loss.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Finite residual-refined schedules -/

/-- One actually realized within-half signature together with one
actually realized residual-chain signature in its fibre. -/
abbrev R324RefinedScheduleIndex (m : ℕ) :=
  Σ s :
      {s :
        Finset (Fin (2 * m)) × Finset (Fin (2 * m)) //
        s ∈ momentContractionSignatures m},
    {r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)) //
      r ∈ momentResidualChainSignaturesAt m s.1}

/-- Canonical refined schedule, used only to witness nonemptiness of the
finite outer index. -/
def r324CanonicalRefinedSchedule (m : ℕ) :
    R324RefinedScheduleIndex m := by
  let e := SmoothCutoff.r324CanonicalMomentContraction m
  let s := momentContractionSignature e
  have hs : s ∈ momentContractionSignatures m :=
    Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
  let r :=
    momentResidualChainSignature e.1 e.2.1 e.2.2
  have heFiber : e ∈ momentContractionFiber m s := by
    exact mem_momentContractionFiber.mpr rfl
  have hr : r ∈ momentResidualChainSignaturesAt m s :=
    Finset.mem_image.mpr ⟨e, heFiber, rfl⟩
  exact ⟨⟨s, hs⟩, ⟨r, hr⟩⟩

instance instNonemptyR324RefinedScheduleIndex (m : ℕ) :
    Nonempty (R324RefinedScheduleIndex m) :=
  ⟨r324CanonicalRefinedSchedule m⟩

/-- Exact flattening of the finite refined-schedule index and the
natural-number configuration index. -/
def r324NatEquivRefinedScheduleConfigurations (m : ℕ) :
    ℕ ≃ R324RefinedScheduleIndex m × ℕ := by
  classical
  letI : Encodable (R324RefinedScheduleIndex m) :=
    Fintype.toEncodable _
  letI : Denumerable (R324RefinedScheduleIndex m × ℕ) :=
    Denumerable.ofEncodableOfInfinite _
  exact
    (Denumerable.eqv
      (R324RefinedScheduleIndex m × ℕ)).symm

/-! ## Genuine grouped endpoint terms -/

/-- One residual-refined configuration after the four external Fourier
integrations, followed by integration of all internal variables.  The
configuration core is a function of the doubled internal tuple and may
already contain the complete compatible primitive-pairing fibre sum. -/
def r324GroupedEndpointConfigurationTerm
    {m : ℕ} (hm : 0 < m)
    (_ρ : SmoothCutoff) (lam ε : ℝ) (α β : Z4)
    (e : MomentContraction m)
    (core : (Fin (2 * m) → T4) → ℂ) : ℂ :=
  (lamEps lam ε ^ (2 * m) : ℂ) *
    ∫ v : Fin (2 * m) → T4,
      ∫ x, ∫ y, ∫ z, ∫ w,
        r324EndpointSeparatedIntegrand α β
          (r324ContractionEndpointAnchors hm e v)
          (r324ContractionEndpointFlags e)
          (core v) x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

/-- Exact, checkable analytic data at the residual-refined boundary.

`core_tsum_eq` ties the configuration series to the actual grouped core
produced by `momentRefinedPhysicalIntegrand_eq_endpointSeparated`.
`sum_eq` and `summable_term` are the Fubini/reindexing certificates; no
decay estimate or target budget is included in this structure. -/
structure R324RefinedFourierRoutingData
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4) where
  representative :
    R324RefinedScheduleIndex m → MomentContraction m
  representative_mem :
    ∀ p,
      representative p ∈
        momentContractionFiber m p.1.1
  core :
    R324RefinedScheduleIndex m → ℕ →
      (Fin (2 * m) → T4) → ℂ
  summable_core :
    ∀ p v, Summable fun a => core p a v
  core_tsum_eq :
    ∀ p v,
      r324RefinedEndpointCore ρ ε m
          p.1.1 p.2.1 (representative p) v =
        ∑' a, core p a v
  sum_eq :
    deterministicMomentPairingSum ρ lam ε m α β =
      ∑' p : R324RefinedScheduleIndex m × ℕ,
        r324GroupedEndpointConfigurationTerm
          hm ρ lam ε α β (representative p.1)
          (core p.1 p.2)
  summable_term :
    Summable fun p : R324RefinedScheduleIndex m × ℕ =>
      r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β (representative p.1)
        (core p.1 p.2)
  incrementCount :
    R324RefinedScheduleIndex m × ℕ → ℕ
  increment :
    ∀ p,
      Fin (incrementCount p) →
        EuclideanSpace ℝ (Fin dim)
  incrementCount_pos :
    ∀ p, 0 < incrementCount p
  incrementCount_le_trunc :
    ∀ p, incrementCount p ≤ truncOrder ε
  increment_sum :
    ∀ p, (∑ i, increment p i) =
      z4EuclideanFrequency (α + β)

namespace R324RefinedFourierRoutingData

variable
  {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {hm : 0 < m}
  {α β : Z4}

/-- Natural-number flattened grouped term. -/
def natTerm
    (d : R324RefinedFourierRoutingData
      ρ lam ε m hm α β)
    (a : ℕ) : ℂ :=
  let p := r324NatEquivRefinedScheduleConfigurations m a
  r324GroupedEndpointConfigurationTerm
    hm ρ lam ε α β (d.representative p.1)
    (d.core p.1 p.2)

/-- Natural-number flattened increment count. -/
def natIncrementCount
    (d : R324RefinedFourierRoutingData
      ρ lam ε m hm α β)
    (a : ℕ) : ℕ :=
  d.incrementCount
    (r324NatEquivRefinedScheduleConfigurations m a)

/-- Natural-number flattened routed increments. -/
def natIncrement
    (d : R324RefinedFourierRoutingData
      ρ lam ε m hm α β)
    (a : ℕ) (i : Fin (d.natIncrementCount a)) :
    EuclideanSpace ℝ (Fin dim) :=
  d.increment
    (r324NatEquivRefinedScheduleConfigurations m a) i

/-- Endpoint-weighted natural-number route weight.  The factor `16` and
the full `r324EndpointLoss` are explicit and are not assumptions. -/
def natWeight
    (_d : R324RefinedFourierRoutingData
      ρ lam ε m hm α β)
    (baseWeight :
      R324RefinedScheduleIndex m × ℕ → ℝ)
    (a : ℕ) : ℝ :=
  let p := r324NatEquivRefinedScheduleConfigurations m a
  (16 * r324EndpointLoss ε α β) * baseWeight p

/-- A proved local grouped-configuration estimate and a summable
endpoint-free core budget produce the concrete countable central routing
output.  The global endpoint budget is derived here. -/
theorem toCountableCentralRoutedMomentReductionOutput
    (d : R324RefinedFourierRoutingData
      ρ lam ε m hm α β)
    (baseWeight :
      R324RefinedScheduleIndex m × ℕ → ℝ)
    (amplitude : ℝ)
    (hbaseSummable : Summable baseWeight)
    (hbaseNonneg : ∀ p, 0 ≤ baseWeight p)
    (hbaseBudget : (∑' p, baseWeight p) ≤ amplitude)
    (hterm :
      ∀ (p : R324RefinedScheduleIndex m × ℕ)
        (i : Fin (d.incrementCount p)),
        ‖r324GroupedEndpointConfigurationTerm
            hm ρ lam ε α β (d.representative p.1)
            (d.core p.1 p.2)‖ ≤
          ((16 * r324EndpointLoss ε α β) *
              baseWeight p) *
            eighthOrderFrequencyDecay
              ‖d.increment p i‖) :
    CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β
        ((16 * amplitude) *
          r324EndpointLoss ε α β) := by
  let E :=
    r324NatEquivRefinedScheduleConfigurations m
  let scale : ℝ :=
    16 * r324EndpointLoss ε α β
  let weightProduct :
      R324RefinedScheduleIndex m × ℕ → ℝ :=
    fun p => scale * baseWeight p
  have hscale : 0 ≤ scale := by
    dsimp only [scale]
    exact mul_nonneg (by norm_num)
      (r324EndpointLoss_nonneg ε α β)
  have hweightProductNonneg :
      ∀ p, 0 ≤ weightProduct p := by
    intro p
    exact mul_nonneg hscale (hbaseNonneg p)
  have hweightProductSummable :
      Summable weightProduct :=
    hbaseSummable.mul_left scale
  have hnatWeightSummable :
      Summable (d.natWeight baseWeight) := by
    have hpre :
        Summable (weightProduct ∘ E) :=
      E.summable_iff.mpr hweightProductSummable
    exact hpre.congr fun a => by rfl
  have hnatTermSummable :
      Summable d.natTerm := by
    let termProduct :
        R324RefinedScheduleIndex m × ℕ → ℂ := fun p =>
      r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β (d.representative p.1)
        (d.core p.1 p.2)
    have hproduct : Summable termProduct := by
      exact d.summable_term
    have hpre :
        Summable (termProduct ∘ E) :=
      E.summable_iff.mpr hproduct
    exact hpre.congr fun a => by rfl
  refine ⟨{
    term := d.natTerm
    weight := d.natWeight baseWeight
    incrementCount := d.natIncrementCount
    increment := d.natIncrement
    sum_eq := ?_
    summable_term := hnatTermSummable
    summable_weight := hnatWeightSummable
    weight_nonneg := ?_
    incrementCount_pos := ?_
    incrementCount_le_trunc := ?_
    increment_sum := ?_
    term_le_increment_decay := ?_
    tsum_weight_le := ?_
  }⟩
  · rw [d.sum_eq]
    change
      (∑' p : R324RefinedScheduleIndex m × ℕ,
        r324GroupedEndpointConfigurationTerm
          hm ρ lam ε α β (d.representative p.1)
          (d.core p.1 p.2)) =
        ∑' a : ℕ,
          r324GroupedEndpointConfigurationTerm
            hm ρ lam ε α β
            (d.representative (E a).1)
            (d.core (E a).1 (E a).2)
    exact
      (E.tsum_eq fun p =>
        r324GroupedEndpointConfigurationTerm
          hm ρ lam ε α β (d.representative p.1)
          (d.core p.1 p.2)).symm
  · intro a
    exact hweightProductNonneg (E a)
  · intro a
    exact d.incrementCount_pos (E a)
  · intro a
    exact d.incrementCount_le_trunc (E a)
  · intro a
    exact d.increment_sum (E a)
  · intro a i
    exact hterm (E a) i
  · change
      (∑' a : ℕ, weightProduct (E a)) ≤
        (16 * amplitude) *
          r324EndpointLoss ε α β
    rw [E.tsum_eq]
    rw [show (∑' p, weightProduct p) =
        scale * ∑' p, baseWeight p by
      exact hbaseSummable.tsum_mul_left scale]
    calc
      scale * (∑' p, baseWeight p) ≤
          scale * amplitude :=
        mul_le_mul_of_nonneg_left hbaseBudget hscale
      _ = (16 * amplitude) *
          r324EndpointLoss ε α β := by
        dsimp only [scale]
        ring

end R324RefinedFourierRoutingData

end

end Anderson4D
