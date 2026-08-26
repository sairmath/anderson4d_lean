import Anderson4D.DetParametrix.Paper42_Moment.R324RawCasePhysicalBridge
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Corrected endpoint-nonzero routed densities for R-324

The old raw case density groups pointwise internal Fourier cores before
the four endpoint integrations.  At that stage an endpoint-null
configuration need not vanish pointwise, so it cannot be deleted from
the norm.

This file records the paper-faithful order of operations:

1. integrate the complete five-group endpoint term;
2. delete exactly the configurations whose resulting coefficient is
   zero;
3. partition the remaining signed series by its contraction, complete
   increment key, and genuine canonical selector slot;
4. only then take a norm of each routed physical fibre.

The resulting density is a new object depending on the external modes.
No theorem identifies it with `r324RawCaseDensity`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## A local `L¹` completeness lemma -/

/-- A countable family with summable integral norms has an integrable
pointwise sum.  This is used only to certify the genuine signed route
core; no quantitative estimate is hidden in it. -/
private theorem integrable_tsum_of_summable_integral_norm_nonzeroRoute
    {α ι E : Type*} [MeasurableSpace α] [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} (F : ι → α → E)
    (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i => ∫ x, ‖F i x‖ ∂μ) :
    Integrable (fun x => ∑' i, F i x) μ := by
  let F₁ : ι → (α →₁[μ] E) := fun i =>
    (hF_int i).toL1 (F i)
  have hnorm (i : ι) :
      ‖F₁ i‖ = ∫ x, ‖F i x‖ ∂μ := by
    dsimp only [F₁]
    rw [Integrable.norm_toL1]
    rw [integral_norm_eq_lintegral_enorm
      (hF_int i).aestronglyMeasurable]
    simp only [edist_zero_right]
  have hF₁_norm : Summable fun i => ‖F₁ i‖ := by
    exact hF_sum.congr fun i => (hnorm i).symm
  have hF₁_enorm :
      (∑' i, ‖F₁ i‖ₑ) ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hF₁_norm
  have hcoe :
      (⇑(∑' i, F₁ i) : α → E) =ᵐ[μ]
        fun x => ∑' i, F₁ i x :=
    Lp.coeFn_tsum hF₁_enorm
  have hterm :
      ∀ᵐ x ∂μ, ∀ i, F₁ i x = F i x :=
    eventually_countable_forall.2 fun i =>
      (hF_int i).coeFn_toL1
  have heq :
      (⇑(∑' i, F₁ i) : α → E) =ᵐ[μ]
        fun x => ∑' i, F i x := by
    filter_upwards [hcoe, hterm] with x hx hxi
    calc
      (∑' i, F₁ i) x = ∑' i, F₁ i x := hx
      _ = ∑' i, F i x := tsum_congr hxi
  exact (L1.integrable_coeFn (∑' i, F₁ i)).congr heq

/-! ## Endpoint-integrated nonzero configurations -/

/-- Raw refined indices retained only after their complete endpoint and
internal physical integral has been evaluated and found nonzero. -/
abbrev R324RefinedEndpointNonzeroRawConfiguration
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (p : R324RefinedScheduleIndex m) :=
  {a : ℕ //
    ρ.r324RefinedRawFullPairingIntegral
      hm ε α β p a ≠ 0}

/-- The data that must remain common on a corrected physical fibre: the
actual contraction, the complete increment key, and the underlying
genuine cross slot selected by the first-large selector.  Retaining the
contraction prevents equal `Fin m` positions belonging to different
cross edges from being merged. -/
abbrev R324NonzeroRouteLabel (m : ℕ) :=
  MomentContraction m × ((Fin m → Z4) × Fin m)

/-- Route label of one endpoint-nonzero raw configuration.  The second
component is the underlying `Fin m` position of the actual residual
slot; its proof of membership in the contraction's singles set remains
available in `r324RefinedRawSelectedResidualSlot`. -/
def r324RefinedEndpointNonzeroRouteLabel
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (a :
      ρ.R324RefinedEndpointNonzeroRawConfiguration
        hm ε α β p) :
    R324NonzeroRouteLabel m :=
  (r324RefinedRawMomentContraction p a.1,
    (r324RefinedRawIncrementKey hm p a.1,
      (ρ.r324RefinedRawSelectedResidualSlot
        hm ε α β hexternal hε hε1 hmtrunc
        p a.1 a.2).1))

/-- Genuine fibre of endpoint-nonzero configurations having one fixed
complete increment key and one fixed canonical selector slot. -/
abbrev R324RefinedEndpointNonzeroRouteFiber
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :=
  {a :
      ρ.R324RefinedEndpointNonzeroRawConfiguration
        hm ε α β p //
    ρ.r324RefinedEndpointNonzeroRouteLabel
      hm ε α β hexternal hε hε1 hmtrunc p a =
        route}

/-- The integrated raw Fourier term is definitionally represented by
the full-pairing coefficient used for zero deletion. -/
theorem r324RefinedRawFourierIntegral_eq_rawFullPairingIntegral
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    ρ.r324RefinedRawFourierIntegral
        hm ε α β p a =
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a := by
  unfold r324RefinedRawFourierIntegral
  exact
    ρ.integral_r324Flatten_refinedRawEndpointIntegrand_eq_rawFullPairingIntegral
      hm ε α β p a

/-- Full endpoint coefficients in one refined schedule are summable. -/
theorem summable_r324RefinedRawFullPairingIntegral
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    Summable
      (ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p) := by
  exact
    (ρ.summable_r324RefinedRawFourierIntegral
      hm hε α β p).congr fun a =>
        ρ.r324RefinedRawFourierIntegral_eq_rawFullPairingIntegral
          hm ε α β p a

/-- Exact zero deletion at the correct boundary: only coefficients
whose *complete physical integral* is zero are removed. -/
theorem tsum_r324RefinedRawFullPairingIntegral_eq_nonzero
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    (∑' a : ℕ,
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a) =
      ∑' a :
          ρ.R324RefinedEndpointNonzeroRawConfiguration
            hm ε α β p,
        ρ.r324RefinedRawFullPairingIntegral
          hm ε α β p a.1 := by
  exact
    tsum_eq_tsum_nonzero_subtype _
      (ρ.summable_r324RefinedRawFullPairingIntegral
        hm hε α β p)

/-! ## Exact contraction/key/selector partition before norms -/

/-- After zero deletion, the remaining signed coefficient series
partitions exactly by contraction, complete increment key, and actual
selector slot. -/
theorem
    tsum_r324RefinedEndpointNonzero_eq_routeFibres
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) :
    (∑' a :
        ρ.R324RefinedEndpointNonzeroRawConfiguration
          hm ε α β p,
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a.1) =
      ∑' route : R324NonzeroRouteLabel m,
        ∑' a :
            ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc
              p route,
          ρ.r324RefinedRawFullPairingIntegral
            hm ε α β p a.1.1 := by
  let term :
      ρ.R324RefinedEndpointNonzeroRawConfiguration
          hm ε α β p → ℂ :=
    fun a =>
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a.1
  let selected :
      ρ.R324RefinedEndpointNonzeroRawConfiguration
          hm ε α β p →
        R324NonzeroRouteLabel m :=
    ρ.r324RefinedEndpointNonzeroRouteLabel
      hm ε α β hexternal hε hε1 hmtrunc p
  have hterm : Summable term :=
    (ρ.summable_r324RefinedRawFullPairingIntegral
      hm hε α β p).subtype _
  have hfibres :=
    hterm.hasSum.tsum_fiberwise selected
  exact hfibres.tsum_eq.symm

/-! ## Exact selector-restricted physical fibres -/

/-- One genuine selector-restricted physical term on a corrected route
fibre. -/
def r324RefinedEndpointNonzeroRoutePhysicalTerm
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route)
    (q : R324PhysicalPoint m) : ℂ :=
  r324Flatten
    (ρ.r324RefinedRawSelectorRestrictedPhysicalIntegrand
      hm ε α β hexternal hε hε1 hmtrunc
      p a.1.1 a.1.2) q

/-- Signed physical sum of exactly one nonzero contraction/key/selector
fibre.  No
unrestricted projected covariance has been substituted. -/
def r324RefinedEndpointNonzeroRoutePhysicalCore
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (q : R324PhysicalPoint m) : ℂ :=
  ∑' a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route,
    ρ.r324RefinedEndpointNonzeroRoutePhysicalTerm
      hm ε α β hexternal hε hε1 hmtrunc
      p route a q

/-- Membership in a corrected route fibre exposes the actual contraction
whose dependent selector fibre is being used. -/
theorem r324RefinedEndpointNonzeroRouteFiber_contraction
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route) :
    r324RefinedRawMomentContraction p a.1.1 =
      route.1 := by
  exact congrArg Prod.fst a.2

/-- Membership in a corrected route fibre exposes the promised complete
increment key. -/
theorem r324RefinedEndpointNonzeroRouteFiber_key
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route) :
    r324RefinedRawIncrementKey hm p a.1.1 =
      route.2.1 := by
  exact congrArg
    (fun x : R324NonzeroRouteLabel m => x.2.1) a.2

/-- Membership also exposes the underlying genuine selector slot.  The
stronger proof that this position belongs to the actual residual singles
set remains part of `r324RefinedRawSelectedResidualSlot`. -/
theorem r324RefinedEndpointNonzeroRouteFiber_selector
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route) :
    (ρ.r324RefinedRawSelectedResidualSlot
      hm ε α β hexternal hε hε1 hmtrunc
      p a.1.1 a.1.2).1 =
        route.2.2 := by
  exact congrArg
    (fun x : R324NonzeroRouteLabel m => x.2.2) a.2

/-- Every inhabited corrected route key carries the exact external
frequency.  This is the later central-frequency routing input and follows
from endpoint nonvanishing, not from a dummy zero-term route. -/
theorem sum_r324RefinedEndpointNonzeroRouteKey_eq_external
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route) :
    (∑ i,
      z4EuclideanFrequency (route.2.1 i)) =
        z4EuclideanFrequency (α + β) := by
  have hne :
      ρ.r324RefinedRawFourierIntegral
          hm ε α β p a.1.1 ≠ 0 := by
    rw [
      ρ.r324RefinedRawFourierIntegral_eq_rawFullPairingIntegral
        hm ε α β p a.1.1]
    exact a.1.2
  calc
    (∑ i,
        z4EuclideanFrequency (route.2.1 i)) =
        ∑ i,
          z4EuclideanFrequency
            (r324RefinedRawIncrementKey
              hm p a.1.1 i) := by
      rw [
        ρ.r324RefinedEndpointNonzeroRouteFiber_key
          hm ε α β hexternal hε hε1 hmtrunc
          p route a]
    _ = z4EuclideanFrequency (α + β) :=
      ρ.sum_r324RefinedRawIncrementKey_eq_external_of_ne_zero
        hm ε α β p a.1.1 hne

/-! ## Internal signed cores after endpoint-licensed zero deletion -/

/-- One selector-restricted signed internal term in a corrected route
fibre. -/
def r324RefinedEndpointNonzeroRouteInternalTerm
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route)
    (v : Fin (2 * m) → T4) : ℂ :=
  ρ.r324RefinedRawSelectorRestrictedSignedCore
    hm ε α β hexternal hε hε1 hmtrunc
    p a.1.1 a.1.2 v

/-- The signed internal core of a fixed
`(contraction, key, selector)` fibre.  The zero-deletion predicate in
the index type was established only after complete endpoint integration;
the norm has still not been taken. -/
def r324RefinedEndpointNonzeroRouteInternalCore
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (v : Fin (2 * m) → T4) : ℂ :=
  ∑' a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route,
    ρ.r324RefinedEndpointNonzeroRouteInternalTerm
      hm ε α β hexternal hε hε1 hmtrunc
      p route a v

/-- On an endpoint-nonzero member, exposing the selected high mode gives
the actual contraction's two internal Green cores times the original raw
covariance configuration.  The contraction is not replaced by a schedule
representative at this boundary. -/
theorem r324RefinedEndpointNonzeroRouteInternalTerm_eq_actual
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route)
    (v : Fin (2 * m) → T4) :
    ρ.r324RefinedEndpointNonzeroRouteInternalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a v =
      r324RenormalizedInteriorCore
          (r324RefinedRawMomentContraction p a.1.1).1
          (fun i => v (leftMomentIndex i)) *
        r324RenormalizedInteriorCore
          (r324RefinedRawMomentContraction p a.1.1).2.1
          (fun i => v (rightMomentIndex i)) *
        ρ.r324RefinedRawCovarianceConfiguration
          hm ε p a.1.1 v := by
  let u :=
    r324NatEquivRefinedContractionConfigurations p a.1.1
  let e : MomentContraction m := u.1.1
  let κ := momentContractionEquivFullPairing m e
  have hcore :=
    ρ.r324SelectedEndpointCore_eq_selectorRestrictedSignedInteriorMode
      ε α β
      (r324RefinedRawMomentContraction p a.1.1).1
      (r324RefinedRawMomentContraction p a.1.1).2.1
      (r324RefinedRawMomentContraction p a.1.1).2.2
      hexternal hε hε1 hmtrunc
      (ρ.r324RefinedRawSelectedResidualSlot
        hm ε α β hexternal hε hε1 hmtrunc
        p a.1.1 a.1.2)
      (ρ.r324RefinedRawSelectedConfigurationFiber
        hm ε α β hexternal hε hε1 hmtrunc
        p a.1.1 a.1.2)
      v
  have hcore' :
      ρ.r324SelectedEndpointCore
          ε
          (r324RefinedRawMomentContraction p a.1.1).1
          (r324RefinedRawMomentContraction p a.1.1).2.1
          (r324RefinedRawMomentContraction p a.1.1).2.2
          (ρ.r324RefinedRawNonzeroCombinedConfiguration
            hm ε α β p a.1.1 a.1.2).1
          (ρ.r324RefinedRawSelectedResidualSlot
            hm ε α β hexternal hε hε1 hmtrunc
            p a.1.1 a.1.2)
          ‖z4EuclideanFrequency (α + β)‖ v =
        ρ.r324RefinedRawSelectorRestrictedSignedCore
          hm ε α β hexternal hε hε1 hmtrunc
          p a.1.1 a.1.2 v := by
    unfold r324RefinedRawSelectorRestrictedSignedCore
    simpa only [
      r324RefinedRawSelectedResidualSlot,
      r324RefinedRawSelectedConfigurationFiber] using hcore
  have hguard :
      ρ.r324SelectedHighCovarianceConfigurationTerm
          ε ‖z4EuclideanFrequency (α + β)‖
          (r324RefinedRawMomentContraction p a.1.1).1
          (r324RefinedRawMomentContraction p a.1.1).2.1
          (r324RefinedRawMomentContraction p a.1.1).2.2
          (ρ.r324RefinedRawNonzeroCombinedConfiguration
            hm ε α β p a.1.1 a.1.2).1
          (ρ.r324RefinedRawSelectedResidualSlot
            hm ε α β hexternal hε hε1 hmtrunc
            p a.1.1 a.1.2)
          v =
        ρ.r324CovarianceFourierConfigurationTerm ε
          (momentCombinedPairing
            (r324RefinedRawMomentContraction p a.1.1).1
            (r324RefinedRawMomentContraction p a.1.1).2.1
            (r324RefinedRawMomentContraction p a.1.1).2.2)
          v
          (ρ.r324RefinedRawNonzeroCombinedConfiguration
            hm ε α β p a.1.1 a.1.2).1 := by
    simpa only [r324RefinedRawSelectedResidualSlot] using
      ρ.r324SelectedHighCovarianceConfigurationTerm_eq
        ε α β
        (r324RefinedRawMomentContraction p a.1.1).1
        (r324RefinedRawMomentContraction p a.1.1).2.1
        (r324RefinedRawMomentContraction p a.1.1).2.2
        hexternal hε hε1 hmtrunc
        (ρ.r324RefinedRawNonzeroCombinedConfiguration
          hm ε α β p a.1.1 a.1.2)
        v
  unfold r324RefinedEndpointNonzeroRouteInternalTerm
  rw [← hcore']
  unfold r324SelectedEndpointCore
  rw [hguard]
  change
    r324RenormalizedInteriorCore e.1
          (fun i => v (leftMomentIndex i)) *
        r324RenormalizedInteriorCore e.2.1
          (fun i => v (rightMomentIndex i)) *
        ρ.r324NatCovarianceConfigurationTerm
          hm ε κ u.2 v =
      r324RenormalizedInteriorCore e.1
          (fun i => v (leftMomentIndex i)) *
        r324RenormalizedInteriorCore e.2.1
          (fun i => v (rightMomentIndex i)) *
        ρ.r324NatCovarianceConfigurationTerm
          hm ε κ u.2 v
  rfl

/-- Internal `L¹` skeleton mass attached to the actual contraction in a
corrected route. -/
def r324NonzeroRouteInteriorSkeletonL1
    {m : ℕ} (route : R324NonzeroRouteLabel m) : ℝ :=
  ∫ v : Fin (2 * m) → T4,
    r324SelectedInteriorSkeletonNormDensity
      route.1.1 route.1.2.1 v
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

theorem r324NonzeroRouteInteriorSkeletonL1_nonneg
    {m : ℕ} (route : R324NonzeroRouteLabel m) :
    0 ≤ r324NonzeroRouteInteriorSkeletonL1 route :=
  integral_nonneg fun v =>
    r324SelectedInteriorSkeletonNormDensity_nonneg
      route.1.1 route.1.2.1 v

/-- A finite uniform envelope for the internal skeleton masses of every
possible contraction. -/
def r324AllContractionInteriorSkeletonL1 (m : ℕ) : ℝ :=
  ∑ e : MomentContraction m,
    ∫ v : Fin (2 * m) → T4,
      r324SelectedInteriorSkeletonNormDensity
        e.1 e.2.1 v
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

theorem r324AllContractionInteriorSkeletonL1_nonneg
    (m : ℕ) :
    0 ≤ r324AllContractionInteriorSkeletonL1 m := by
  unfold r324AllContractionInteriorSkeletonL1
  exact Finset.sum_nonneg fun e _he =>
    integral_nonneg fun v =>
      r324SelectedInteriorSkeletonNormDensity_nonneg
        e.1 e.2.1 v

theorem r324NonzeroRouteInteriorSkeletonL1_le_all
    {m : ℕ} (route : R324NonzeroRouteLabel m) :
    r324NonzeroRouteInteriorSkeletonL1 route ≤
      r324AllContractionInteriorSkeletonL1 m := by
  unfold r324NonzeroRouteInteriorSkeletonL1
    r324AllContractionInteriorSkeletonL1
  let g : MomentContraction m → ℝ := fun e =>
    ∫ v : Fin (2 * m) → T4,
      r324SelectedInteriorSkeletonNormDensity
        e.1 e.2.1 v
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)
  have hg : ∀ e, 0 ≤ g e := by
    intro e
    exact integral_nonneg fun v =>
      r324SelectedInteriorSkeletonNormDensity_nonneg
        e.1 e.2.1 v
  have hsingle :
      g route.1 ≤ ∑ e : MomentContraction m, g e :=
    Finset.single_le_sum
      (fun e _he => hg e)
      (Finset.mem_univ route.1)
  simpa only [g] using hsingle

/-- Exact coordinate-independent norm ledger for one corrected internal
term. -/
theorem norm_r324RefinedEndpointNonzeroRouteInternalTerm
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route)
    (v : Fin (2 * m) → T4) :
    ‖ρ.r324RefinedEndpointNonzeroRouteInternalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a v‖ =
      r324SelectedInteriorSkeletonNormDensity
          route.1.1 route.1.2.1 v *
        ρ.r324RefinedRawCovarianceWeight
          hm ε p a.1.1 := by
  rw [
    ρ.r324RefinedEndpointNonzeroRouteInternalTerm_eq_actual
      hm ε α β hexternal hε hε1 hmtrunc
      p route a v,
    ρ.r324RefinedEndpointNonzeroRouteFiber_contraction
      hm ε α β hexternal hε hε1 hmtrunc
      p route a]
  unfold r324SelectedInteriorSkeletonNormDensity
  rw [norm_mul, norm_mul,
    ρ.norm_r324RefinedRawCovarianceConfiguration]

/-- Internal terms in a corrected route fibre are summable pointwise. -/
theorem summable_r324RefinedEndpointNonzeroRouteInternalTerm
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (v : Fin (2 * m) → T4) :
    Summable fun a :
        ρ.R324RefinedEndpointNonzeroRouteFiber
          hm ε α β hexternal hε hε1 hmtrunc p route =>
      ρ.r324RefinedEndpointNonzeroRouteInternalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a v := by
  have hweight :
      Summable fun a :
          ρ.R324RefinedEndpointNonzeroRouteFiber
            hm ε α β hexternal hε hε1 hmtrunc p route =>
        ρ.r324RefinedRawCovarianceWeight hm ε p a.1.1 := by
    exact
      ((ρ.summable_r324RefinedRawCovarianceWeight
        hm hε p).subtype
          {a : ℕ |
            ρ.r324RefinedRawFullPairingIntegral
              hm ε α β p a ≠ 0}).subtype
        {a :
            ρ.R324RefinedEndpointNonzeroRawConfiguration
              hm ε α β p |
          ρ.r324RefinedEndpointNonzeroRouteLabel
            hm ε α β hexternal hε hε1 hmtrunc p a =
              route}
  apply Summable.of_norm
  exact
    (hweight.mul_left
      (r324SelectedInteriorSkeletonNormDensity
        route.1.1 route.1.2.1 v)).congr fun a =>
      (ρ.norm_r324RefinedEndpointNonzeroRouteInternalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a v).symm

/-- Integral norm of one corrected internal term. -/
theorem
    integral_norm_r324RefinedEndpointNonzeroRouteInternalTerm
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route) :
    (∫ v,
      ‖ρ.r324RefinedEndpointNonzeroRouteInternalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a v‖
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
      r324NonzeroRouteInteriorSkeletonL1 route *
        ρ.r324RefinedRawCovarianceWeight
          hm ε p a.1.1 := by
  calc
    (∫ v,
        ‖ρ.r324RefinedEndpointNonzeroRouteInternalTerm
          hm ε α β hexternal hε hε1 hmtrunc
          p route a v‖
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
        ∫ v,
          r324SelectedInteriorSkeletonNormDensity
              route.1.1 route.1.2.1 v *
            ρ.r324RefinedRawCovarianceWeight
              hm ε p a.1.1
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v =>
        ρ.norm_r324RefinedEndpointNonzeroRouteInternalTerm
          hm ε α β hexternal hε hε1 hmtrunc
          p route a v
    _ =
        r324NonzeroRouteInteriorSkeletonL1 route *
          ρ.r324RefinedRawCovarianceWeight
            hm ε p a.1.1 := by
      rw [integral_mul_const]
      rfl

/-- The internal integral-norm ledger is summable on each corrected
route fibre. -/
theorem
    summable_integral_norm_r324RefinedEndpointNonzeroRouteInternalTerm
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    Summable fun a :
        ρ.R324RefinedEndpointNonzeroRouteFiber
          hm ε α β hexternal hε hε1 hmtrunc p route =>
      ∫ v,
        ‖ρ.r324RefinedEndpointNonzeroRouteInternalTerm
          hm ε α β hexternal hε hε1 hmtrunc
          p route a v‖
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  have hweight :
      Summable fun a :
          ρ.R324RefinedEndpointNonzeroRouteFiber
            hm ε α β hexternal hε hε1 hmtrunc p route =>
        ρ.r324RefinedRawCovarianceWeight hm ε p a.1.1 := by
    exact
      ((ρ.summable_r324RefinedRawCovarianceWeight
        hm hε p).subtype
          {a : ℕ |
            ρ.r324RefinedRawFullPairingIntegral
              hm ε α β p a ≠ 0}).subtype
        {a :
            ρ.R324RefinedEndpointNonzeroRawConfiguration
              hm ε α β p |
          ρ.r324RefinedEndpointNonzeroRouteLabel
            hm ε α β hexternal hε hε1 hmtrunc p a =
              route}
  have hscaled :=
    hweight.mul_left
      (r324NonzeroRouteInteriorSkeletonL1 route)
  exact hscaled.congr fun a =>
    (ρ.integral_norm_r324RefinedEndpointNonzeroRouteInternalTerm
      hm ε α β hexternal hε hε1 hmtrunc
      p route a).symm

/-- Each corrected internal term has integrable norm. -/
theorem
    integrable_norm_r324RefinedEndpointNonzeroRouteInternalTerm
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route) :
    Integrable
      (fun v : Fin (2 * m) → T4 =>
        ‖ρ.r324RefinedEndpointNonzeroRouteInternalTerm
          hm ε α β hexternal hε hε1 hmtrunc
          p route a v‖)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  let W : ℝ :=
    ρ.r324RefinedRawCovarianceWeight hm ε p a.1.1
  have hskeleton :=
    integrable_r324SelectedInteriorSkeletonNormDensity
      route.1.1 route.1.2.1
  have hmajor :
      Integrable
        (fun v : Fin (2 * m) → T4 =>
          r324SelectedInteriorSkeletonNormDensity
            route.1.1 route.1.2.1 v * W)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    hskeleton.mul_const W
  exact hmajor.congr
      (Filter.Eventually.of_forall fun v =>
      (ρ.norm_r324RefinedEndpointNonzeroRouteInternalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a v).symm)

/-- Each corrected internal term itself is integrable. -/
theorem integrable_r324RefinedEndpointNonzeroRouteInternalTerm
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route) :
    Integrable
      (ρ.r324RefinedEndpointNonzeroRouteInternalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  have hleft :
      Measurable fun v : Fin (2 * m) → T4 =>
        r324RenormalizedInteriorCore route.1.1
          (fun i => v (leftMomentIndex i)) :=
    (measurable_r324RenormalizedInteriorCore route.1.1).comp
      (measurable_pi_lambda _ fun i =>
        measurable_pi_apply (leftMomentIndex i))
  have hright :
      Measurable fun v : Fin (2 * m) → T4 =>
        r324RenormalizedInteriorCore route.1.2.1
          (fun i => v (rightMomentIndex i)) :=
    (measurable_r324RenormalizedInteriorCore route.1.2.1).comp
      (measurable_pi_lambda _ fun i =>
        measurable_pi_apply (rightMomentIndex i))
  have hcov :
      Measurable fun v : Fin (2 * m) → T4 =>
        ρ.r324RefinedRawCovarianceConfiguration
          hm ε p a.1.1 v := by
    unfold r324RefinedRawCovarianceConfiguration
      r324NatCovarianceConfigurationTerm
    dsimp only
    exact
      ρ.measurable_r324CovarianceFourierConfigurationTerm
        ε _ _
  have hactual :
      AEStronglyMeasurable
        (fun v : Fin (2 * m) → T4 =>
          r324RenormalizedInteriorCore route.1.1
              (fun i => v (leftMomentIndex i)) *
            r324RenormalizedInteriorCore route.1.2.1
              (fun i => v (rightMomentIndex i)) *
            ρ.r324RefinedRawCovarianceConfiguration
              hm ε p a.1.1 v)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
    exact ((hleft.mul hright).mul hcov).aestronglyMeasurable
  have hterm :
      AEStronglyMeasurable
        (ρ.r324RefinedEndpointNonzeroRouteInternalTerm
          hm ε α β hexternal hε hε1 hmtrunc
          p route a)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    hactual.congr
      (Filter.Eventually.of_forall fun v => by
        rw [
          ← ρ.r324RefinedEndpointNonzeroRouteFiber_contraction
            hm ε α β hexternal hε hε1 hmtrunc
            p route a]
        exact
          (ρ.r324RefinedEndpointNonzeroRouteInternalTerm_eq_actual
            hm ε α β hexternal hε hε1 hmtrunc
            p route a v).symm)
  exact
    (integrable_norm_iff hterm).mp
      (ρ.integrable_norm_r324RefinedEndpointNonzeroRouteInternalTerm
        hm hε α β hexternal hε1 hmtrunc
        p route a)

/-- The complete signed internal route core is integrable. -/
theorem integrable_r324RefinedEndpointNonzeroRouteInternalCore
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    Integrable
      (ρ.r324RefinedEndpointNonzeroRouteInternalCore
        hm ε α β hexternal hε hε1 hmtrunc
        p route)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  exact
    integrable_tsum_of_summable_integral_norm_nonzeroRoute
      (fun a =>
        ρ.r324RefinedEndpointNonzeroRouteInternalTerm
          hm ε α β hexternal hε hε1 hmtrunc
          p route a)
      (fun a =>
        ρ.integrable_r324RefinedEndpointNonzeroRouteInternalTerm
          hm hε α β hexternal hε1 hmtrunc
          p route a)
      (ρ.summable_integral_norm_r324RefinedEndpointNonzeroRouteInternalTerm
        hm hε α β hexternal hε1 hmtrunc
        p route)

/-- The routed physical term is exactly the original raw endpoint
integrand; only its already-proved selector-restricted factorization has
been exposed. -/
theorem r324RefinedEndpointNonzeroRoutePhysicalTerm_eq_raw
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route)
    (q : R324PhysicalPoint m) :
    ρ.r324RefinedEndpointNonzeroRoutePhysicalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a q =
      r324Flatten
        (ρ.r324RefinedRawEndpointIntegrand
          hm ε α β p a.1.1) q := by
  unfold r324RefinedEndpointNonzeroRoutePhysicalTerm
  exact
    (ρ.r324RefinedRawEndpointIntegrand_eq_selectorPhysical
      hm ε α β hexternal hε hε1 hmtrunc
      p a.1.1 a.1.2
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2).symm

/-- Because the route label retains the actual contraction, every member
of the fibre has the same endpoint anchors and flags. -/
theorem
    r324RefinedEndpointNonzeroRoutePhysicalTerm_eq_endpointSeparated
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ρ.r324RefinedEndpointNonzeroRoutePhysicalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a (x, y, z, w, v) =
      r324EndpointSeparatedIntegrand α β
        (r324ContractionEndpointAnchors hm route.1 v)
        (r324ContractionEndpointFlags route.1)
        (ρ.r324RefinedEndpointNonzeroRouteInternalTerm
          hm ε α β hexternal hε hε1 hmtrunc
          p route a v)
        x y z w := by
  unfold r324RefinedEndpointNonzeroRoutePhysicalTerm
    r324RefinedRawSelectorRestrictedPhysicalIntegrand
    r324RefinedEndpointNonzeroRouteInternalTerm
    r324Flatten
  rw [
    ρ.r324RefinedEndpointNonzeroRouteFiber_contraction
      hm ε α β hexternal hε hε1 hmtrunc
      p route a]

/-- Curried endpoint-separated integrand of a complete corrected route
fibre. -/
def r324RefinedEndpointNonzeroRouteEndpointIntegrand
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  r324EndpointSeparatedIntegrand α β
    (r324ContractionEndpointAnchors hm route.1 v)
    (r324ContractionEndpointFlags route.1)
    (ρ.r324RefinedEndpointNonzeroRouteInternalCore
      hm ε α β hexternal hε hε1 hmtrunc
      p route v)
    x y z w

private theorem r324EndpointSeparatedIntegrand_tsum_route
    {ι : Type*}
    (α β : Z4)
    (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags)
    (core : ι → ℂ)
    (x y z w : T4) :
    r324EndpointSeparatedIntegrand α β anchors flags
        (∑' a, core a) x y z w =
      ∑' a,
        r324EndpointSeparatedIntegrand α β anchors flags
          (core a) x y z w := by
  unfold r324EndpointSeparatedIntegrand
  rw [tsum_mul_left]

/-- The full routed physical core is pointwise exactly the
endpoint-separated integrand of the internal signed route core. -/
theorem
    r324RefinedEndpointNonzeroRoutePhysicalCore_eq_endpointIntegrand
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (q : R324PhysicalPoint m) :
    ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
        hm ε α β hexternal hε hε1 hmtrunc
        p route q =
      r324Flatten
        (ρ.r324RefinedEndpointNonzeroRouteEndpointIntegrand
          hm ε α β hexternal hε hε1 hmtrunc
          p route) q := by
  unfold r324RefinedEndpointNonzeroRoutePhysicalCore
    r324RefinedEndpointNonzeroRouteEndpointIntegrand
    r324RefinedEndpointNonzeroRouteInternalCore
    r324Flatten
  change
    (∑' a :
        ρ.R324RefinedEndpointNonzeroRouteFiber
          hm ε α β hexternal hε hε1 hmtrunc p route,
      ρ.r324RefinedEndpointNonzeroRoutePhysicalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a q) =
      r324EndpointSeparatedIntegrand α β
        (r324ContractionEndpointAnchors hm
          route.1 q.2.2.2.2)
        (r324ContractionEndpointFlags route.1)
        (∑' a :
            ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc p route,
          ρ.r324RefinedEndpointNonzeroRouteInternalTerm
            hm ε α β hexternal hε hε1 hmtrunc
            p route a q.2.2.2.2)
        q.1 q.2.1 q.2.2.1 q.2.2.2.1
  rw [
    r324EndpointSeparatedIntegrand_tsum_route
      α β
      (r324ContractionEndpointAnchors hm
        route.1 q.2.2.2.2)
      (r324ContractionEndpointFlags route.1)
      (fun a =>
        ρ.r324RefinedEndpointNonzeroRouteInternalTerm
          hm ε α β hexternal hε hε1 hmtrunc
          p route a q.2.2.2.2)
      q.1 q.2.1 q.2.2.1 q.2.2.2.1]
  apply tsum_congr
  intro a
  exact
    ρ.r324RefinedEndpointNonzeroRoutePhysicalTerm_eq_endpointSeparated
      hm ε α β hexternal hε hε1 hmtrunc
      p route a
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2

/-- Each member of a corrected route fibre is integrable on the full
five-group physical space. -/
theorem integrable_r324RefinedEndpointNonzeroRoutePhysicalTerm
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (a :
      ρ.R324RefinedEndpointNonzeroRouteFiber
        hm ε α β hexternal hε hε1 hmtrunc p route) :
    Integrable
      (ρ.r324RefinedEndpointNonzeroRoutePhysicalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a)
      (r324PhysicalMeasure m) := by
  exact
    ρ.integrable_r324Flatten_refinedRawSelectorRestrictedPhysicalIntegrand
      hm ε α β hexternal hε hε1 hmtrunc
      p a.1.1 a.1.2

/-- The integral norms in every corrected route fibre are summable. -/
theorem
    summable_integral_norm_r324RefinedEndpointNonzeroRoutePhysicalTerm
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    Summable fun a :
        ρ.R324RefinedEndpointNonzeroRouteFiber
          hm ε α β hexternal hε hε1 hmtrunc p route =>
      ∫ q,
        ‖ρ.r324RefinedEndpointNonzeroRoutePhysicalTerm
          hm ε α β hexternal hε hε1 hmtrunc
          p route a q‖
        ∂(r324PhysicalMeasure m) := by
  have hraw :=
    ρ.summable_r324RefinedRawEndpointL1
      hm hε α β p
  have hsub :=
    (hraw.subtype
      {a : ℕ |
        ρ.r324RefinedRawFullPairingIntegral
          hm ε α β p a ≠ 0}).subtype
      {a :
          ρ.R324RefinedEndpointNonzeroRawConfiguration
            hm ε α β p |
        ρ.r324RefinedEndpointNonzeroRouteLabel
          hm ε α β hexternal hε hε1 hmtrunc p a =
            route}
  exact hsub.congr fun a => by
    unfold r324RefinedRawEndpointL1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => by
      exact congrArg norm
        (ρ.r324RefinedEndpointNonzeroRoutePhysicalTerm_eq_raw
          hm ε α β hexternal hε hε1 hmtrunc
          p route a q).symm

/-- Every signed corrected route core is integrable. -/
theorem integrable_r324RefinedEndpointNonzeroRoutePhysicalCore
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    Integrable
      (ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
        hm ε α β hexternal hε hε1 hmtrunc
        p route)
      (r324PhysicalMeasure m) := by
  exact
    integrable_tsum_of_summable_integral_norm_nonzeroRoute
      (fun a =>
        ρ.r324RefinedEndpointNonzeroRoutePhysicalTerm
          hm ε α β hexternal hε hε1 hmtrunc
          p route a)
      (ρ.integrable_r324RefinedEndpointNonzeroRoutePhysicalTerm
        hm ε α β hexternal hε hε1 hmtrunc p route)
      (ρ.summable_integral_norm_r324RefinedEndpointNonzeroRoutePhysicalTerm
        hm hε α β hexternal hε1 hmtrunc p route)

/-- The endpoint-separated representation of a corrected route is
jointly integrable on the genuine five-group product. -/
theorem
    integrable_r324Flatten_refinedEndpointNonzeroRouteEndpointIntegrand
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    Integrable
      (r324Flatten
        (ρ.r324RefinedEndpointNonzeroRouteEndpointIntegrand
          hm ε α β hexternal hε hε1 hmtrunc
          p route))
      (r324PhysicalMeasure m) := by
  refine
    (ρ.integrable_r324RefinedEndpointNonzeroRoutePhysicalCore
      hm hε α β hexternal hε1 hmtrunc
      p route).congr ?_
  exact Filter.Eventually.of_forall fun q =>
    ρ.r324RefinedEndpointNonzeroRoutePhysicalCore_eq_endpointIntegrand
      hm ε α β hexternal hε hε1 hmtrunc
      p route q

/-- Exact internal-first representation of one corrected route
coefficient. -/
theorem
    integral_r324RefinedEndpointNonzeroRoutePhysicalCore_eq_internalFirst
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    (∫ q,
      ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
        hm ε α β hexternal hε hε1 hmtrunc
        p route q
      ∂(r324PhysicalMeasure m)) =
      ∫ v, ∫ x, ∫ y, ∫ z, ∫ w,
        ρ.r324RefinedEndpointNonzeroRouteEndpointIntegrand
          hm ε α β hexternal hε hε1 hmtrunc
          p route x y z w v
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  calc
    (∫ q,
        ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
          hm ε α β hexternal hε hε1 hmtrunc
          p route q
        ∂(r324PhysicalMeasure m)) =
        ∫ q,
          r324Flatten
            (ρ.r324RefinedEndpointNonzeroRouteEndpointIntegrand
              hm ε α β hexternal hε hε1 hmtrunc
              p route) q
          ∂(r324PhysicalMeasure m) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q =>
        ρ.r324RefinedEndpointNonzeroRoutePhysicalCore_eq_endpointIntegrand
          hm ε α β hexternal hε hε1 hmtrunc
          p route q
    _ =
        ∫ v, ∫ x, ∫ y, ∫ z, ∫ w,
          ρ.r324RefinedEndpointNonzeroRouteEndpointIntegrand
            hm ε α β hexternal hε hε1 hmtrunc
            p route x y z w v
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      exact
        r324_integral_product_eq_internal_first
          (ρ.r324RefinedEndpointNonzeroRouteEndpointIntegrand
            hm ε α β hexternal hε hε1 hmtrunc
            p route)
          (ρ.integrable_r324Flatten_refinedEndpointNonzeroRouteEndpointIntegrand
            hm hε α β hexternal hε1 hmtrunc
            p route)

/-- Four endpoint integrations of a corrected route supply the two
paper fourth-order Fourier decays before the internal norm density is
introduced. -/
theorem
    norm_integral_r324RefinedEndpointNonzeroRoutePhysicalCore_le_fourier
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    ‖∫ q,
      ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
        hm ε α β hexternal hε hε1 hmtrunc
        p route q
      ∂(r324PhysicalMeasure m)‖ ≤
      (16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β) *
        ∫ v,
          ‖ρ.r324RefinedEndpointNonzeroRouteInternalCore
            hm ε α β hexternal hε hε1 hmtrunc
            p route v‖
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  let scale : ℝ :=
    16 * paperFourthOrderModeDecay α *
      paperFourthOrderModeDecay β
  let core : (Fin (2 * m) → T4) → ℂ :=
    ρ.r324RefinedEndpointNonzeroRouteInternalCore
      hm ε α β hexternal hε hε1 hmtrunc
      p route
  let endpointIntegral :
      (Fin (2 * m) → T4) → ℂ := fun v =>
    ∫ x, ∫ y, ∫ z, ∫ w,
      r324EndpointSeparatedIntegrand α β
        (r324ContractionEndpointAnchors hm route.1 v)
        (r324ContractionEndpointFlags route.1)
        (core v) x y z w
      ∂paperMeasure ∂paperMeasure
      ∂paperMeasure ∂paperMeasure
  have hscale : 0 ≤ scale := by
    dsimp only [scale]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β)
  have hcore :
      Integrable (fun v => ‖core v‖)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    (ρ.integrable_r324RefinedEndpointNonzeroRouteInternalCore
      hm hε α β hexternal hε1 hmtrunc
      p route).norm
  have hmajor :
      Integrable (fun v => scale * ‖core v‖)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    hcore.const_mul scale
  have hpoint :
      ∀ v, ‖endpointIntegral v‖ ≤
        scale * ‖core v‖ := by
    intro v
    exact
      norm_integral_r324EndpointSeparatedIntegrand_le_fourierOnly
        α β
        (r324ContractionEndpointAnchors hm route.1 v)
        (r324ContractionEndpointFlags route.1)
        (core v)
  have hintegral :
      ‖∫ v, endpointIntegral v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)‖ ≤
        ∫ v, scale * ‖core v‖
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    norm_integral_le_of_norm_le hmajor
      (Filter.Eventually.of_forall hpoint)
  rw [
    ρ.integral_r324RefinedEndpointNonzeroRoutePhysicalCore_eq_internalFirst
      hm hε α β hexternal hε1 hmtrunc
      p route]
  change
    ‖∫ v, endpointIntegral v
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)‖ ≤
      scale *
        ∫ v, ‖core v‖
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)
  exact hintegral.trans_eq (by rw [integral_const_mul])

/-- Exact Fubini identity for one corrected route fibre. -/
theorem
    integral_r324RefinedEndpointNonzeroRoutePhysicalCore
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    (∫ q,
      ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
        hm ε α β hexternal hε hε1 hmtrunc
        p route q
      ∂(r324PhysicalMeasure m)) =
      ∑' a :
          ρ.R324RefinedEndpointNonzeroRouteFiber
            hm ε α β hexternal hε hε1 hmtrunc p route,
        ρ.r324RefinedRawFullPairingIntegral
          hm ε α β p a.1.1 := by
  calc
    (∫ q,
        ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
          hm ε α β hexternal hε hε1 hmtrunc
          p route q
        ∂(r324PhysicalMeasure m)) =
        ∑' a :
            ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc p route,
          ∫ q,
            ρ.r324RefinedEndpointNonzeroRoutePhysicalTerm
              hm ε α β hexternal hε hε1 hmtrunc
              p route a q
            ∂(r324PhysicalMeasure m) := by
      exact
        (integral_tsum_of_summable_integral_norm
          (ρ.integrable_r324RefinedEndpointNonzeroRoutePhysicalTerm
            hm ε α β hexternal hε hε1 hmtrunc p route)
          (ρ.summable_integral_norm_r324RefinedEndpointNonzeroRoutePhysicalTerm
            hm hε α β hexternal hε1 hmtrunc p route)).symm
    _ =
        ∑' a :
            ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc p route,
          ρ.r324RefinedRawFullPairingIntegral
            hm ε α β p a.1.1 := by
      apply tsum_congr
      intro a
      exact
        ρ.integral_r324Flatten_refinedRawSelectorPhysical_eq_rawFullPairingIntegral
          hm ε α β hexternal hε hε1 hmtrunc
          p a.1.1 a.1.2

/-! ## Exact corrected expansion of the original moment -/

/-- One refined physical integral is exactly the sum of the integrated
selector-restricted route cores.  Zero deletion and all components of the
route label occur before any norm. -/
theorem
    r324RefinedPhysicalIntegral_eq_nonzeroRoutePhysicalCore
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) :
    r324RefinedPhysicalIntegral ρ ε m α β p =
      ∑' route : R324NonzeroRouteLabel m,
        ∫ q,
          ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
            hm ε α β hexternal hε hε1 hmtrunc
            p route q
          ∂(r324PhysicalMeasure m) := by
  calc
    r324RefinedPhysicalIntegral ρ ε m α β p =
        ∑' a : ℕ,
          ρ.r324RefinedRawFourierIntegral
            hm ε α β p a :=
      ρ.r324RefinedPhysicalIntegral_eq_rawFourier_tsum
        hm hε α β p
    _ =
        ∑' a : ℕ,
          ρ.r324RefinedRawFullPairingIntegral
            hm ε α β p a := by
      apply tsum_congr
      intro a
      exact
        ρ.r324RefinedRawFourierIntegral_eq_rawFullPairingIntegral
          hm ε α β p a
    _ =
        ∑' a :
            ρ.R324RefinedEndpointNonzeroRawConfiguration
              hm ε α β p,
          ρ.r324RefinedRawFullPairingIntegral
            hm ε α β p a.1 :=
      ρ.tsum_r324RefinedRawFullPairingIntegral_eq_nonzero
        hm hε α β p
    _ =
        ∑' route : R324NonzeroRouteLabel m,
          ∑' a :
              ρ.R324RefinedEndpointNonzeroRouteFiber
                hm ε α β hexternal hε hε1 hmtrunc
                p route,
            ρ.r324RefinedRawFullPairingIntegral
              hm ε α β p a.1.1 :=
      ρ.tsum_r324RefinedEndpointNonzero_eq_routeFibres
        hm hε α β hexternal hε1 hmtrunc p
    _ =
        ∑' route : R324NonzeroRouteLabel m,
          ∫ q,
            ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
              hm ε α β hexternal hε hε1 hmtrunc
              p route q
            ∂(r324PhysicalMeasure m) := by
      apply tsum_congr
      intro route
      exact
        (ρ.integral_r324RefinedEndpointNonzeroRoutePhysicalCore
          hm hε α β hexternal hε1 hmtrunc
          p route).symm

/-- Paper-facing exact boundary for the complete deterministic moment:
the common coupling remains outside the finite refined-schedule ledger,
and every inner series is first zero-deleted and then route-partitioned.
-/
theorem deterministicMomentPairingSum_eq_nonzeroRoutedPhysical
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    deterministicMomentPairingSum ρ lam ε m α β =
      (lamEps lam ε ^ (2 * m) : ℂ) *
        ∑ p : R324RefinedScheduleIndex m,
          ∑' route : R324NonzeroRouteLabel m,
            ∫ q,
              ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
                hm ε α β hexternal hε hε1 hmtrunc
                p route q
              ∂(r324PhysicalMeasure m) := by
  rw [
    deterministicMomentPairingSum_eq_sum_refinedPhysicalIntegral
      ρ lam hε hε1 α β]
  congr 1
  apply Finset.sum_congr rfl
  intro p _hp
  exact
    ρ.r324RefinedPhysicalIntegral_eq_nonzeroRoutePhysicalCore
      hm hε α β hexternal hε1 hmtrunc p

/-! ## Nonnegative density after exact routing -/

/-- Reciprocal eighth-order cost attached directly to the key component
of a corrected route label. -/
def r324NonzeroRouteSlotCost
    {m : ℕ} (route : R324NonzeroRouteLabel m)
    (i : Fin m) : ℝ :=
  (1 + ‖z4EuclideanFrequency (route.2.1 i)‖ ^ 2) ^ 4

theorem r324NonzeroRouteSlotCost_pos
    {m : ℕ} (route : R324NonzeroRouteLabel m)
    (i : Fin m) :
    0 < r324NonzeroRouteSlotCost route i := by
  unfold r324NonzeroRouteSlotCost
  positivity

theorem one_le_r324NonzeroRouteSlotCost
    {m : ℕ} (route : R324NonzeroRouteLabel m)
    (i : Fin m) :
    1 ≤ r324NonzeroRouteSlotCost route i := by
  unfold r324NonzeroRouteSlotCost
  exact one_le_pow₀ (by
    nlinarith [
      sq_nonneg
        ‖z4EuclideanFrequency (route.2.1 i)‖])

/-- The route cost has the exact reciprocal-decay normalization of the
natural-key cost, but it is attached directly
to the retained route key. -/
theorem r324NonzeroRouteSlotCost_mul_decay
    {m : ℕ} (route : R324NonzeroRouteLabel m)
    (i : Fin m) :
    r324NonzeroRouteSlotCost route i *
        eighthOrderFrequencyDecay
          ‖z4EuclideanFrequency (route.2.1 i)‖ =
      1 := by
  unfold r324NonzeroRouteSlotCost eighthOrderFrequencyDecay
  have h :
      (1 + ‖z4EuclideanFrequency (route.2.1 i)‖ ^ 2) ^ 4 ≠
        0 := by
    positivity
  exact mul_inv_cancel₀ h

/-- When a corrected key is named by the existing natural
enumeration, its slot cost is literally the existing grouped cost. -/
theorem r324NonzeroRouteSlotCost_eq_groupedIncrementCost
    {m : ℕ} (hm : 0 < m)
    (route : R324NonzeroRouteLabel m)
    (b : ℕ)
    (hkey :
      route.2.1 =
        r324NatEquivStandardConfigurations hm b)
    (i : Fin m) :
    r324NonzeroRouteSlotCost route i =
      r324GroupedIncrementCost hm b i := by
  unfold r324NonzeroRouteSlotCost
    r324GroupedIncrementCost
  rw [hkey]

/-- Unweighted nonnegative internal mass of one corrected signed route
fibre.  Endpoint Fourier decay has already been extracted before this
density is consumed. -/
def r324RefinedEndpointNonzeroRouteDensityBase
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (v : Fin (2 * m) → T4) : ℝ :=
  |lamEps lam ε| ^ (2 * m) *
    ‖ρ.r324RefinedEndpointNonzeroRouteInternalCore
      hm ε α β hexternal hε hε1 hmtrunc
      p route v‖

theorem r324RefinedEndpointNonzeroRouteDensityBase_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (v : Fin (2 * m) → T4) :
    0 ≤
      ρ.r324RefinedEndpointNonzeroRouteDensityBase
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route v := by
  unfold r324RefinedEndpointNonzeroRouteDensityBase
  exact
    mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (norm_nonneg _)

theorem integrable_r324RefinedEndpointNonzeroRouteDensityBase
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    Integrable
      (ρ.r324RefinedEndpointNonzeroRouteDensityBase
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  have hcore :=
    (ρ.integrable_r324RefinedEndpointNonzeroRouteInternalCore
      hm hε α β hexternal hε1 hmtrunc p route).norm
  unfold r324RefinedEndpointNonzeroRouteDensityBase
  exact hcore.const_mul
    (|lamEps lam ε| ^ (2 * m))

/-- Direct analytic link from one exact signed route coefficient to its
unweighted nonnegative internal density.  The four endpoint integrations
are performed before the norm is taken and contribute the two explicit
fourth-order Fourier decays. -/
theorem
    norm_integral_r324RefinedEndpointNonzeroRoutePhysicalCore_le_base
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    |lamEps lam ε| ^ (2 * m) *
        ‖∫ q,
          ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
            hm ε α β hexternal hε hε1 hmtrunc
            p route q
          ∂(r324PhysicalMeasure m)‖ ≤
      (16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β) *
        ∫ v,
          ρ.r324RefinedEndpointNonzeroRouteDensityBase
            lam hm ε α β hexternal hε hε1 hmtrunc
            p route v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  have hscalar :
      0 ≤ |lamEps lam ε| ^ (2 * m) :=
    pow_nonneg (abs_nonneg _) _
  have hfourier :=
    ρ.norm_integral_r324RefinedEndpointNonzeroRoutePhysicalCore_le_fourier
      hm hε α β hexternal hε1 hmtrunc p route
  calc
    |lamEps lam ε| ^ (2 * m) *
        ‖∫ q,
          ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
            hm ε α β hexternal hε hε1 hmtrunc
            p route q
          ∂(r324PhysicalMeasure m)‖ ≤
        |lamEps lam ε| ^ (2 * m) *
          ((16 * paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β) *
            ∫ v,
            ‖ρ.r324RefinedEndpointNonzeroRouteInternalCore
              hm ε α β hexternal hε hε1 hmtrunc
              p route v‖
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) := by
      exact mul_le_mul_of_nonneg_left hfourier hscalar
    _ =
        (16 * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) *
          ∫ v,
          ρ.r324RefinedEndpointNonzeroRouteDensityBase
            lam hm ε α β hexternal hε hε1 hmtrunc
            p route v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      unfold r324RefinedEndpointNonzeroRouteDensityBase
      rw [integral_const_mul]
      ring

/-- One honest nonnegative routed density term.  The norm is taken after
all endpoint-nonzero configurations with a common
`(contraction, key, selector)` label have been summed with their signs
intact. -/
def r324RefinedEndpointNonzeroRoutedDensityTerm
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (v : Fin (2 * m) → T4) : ℝ :=
  ρ.r324RefinedEndpointNonzeroRouteDensityBase
      lam hm ε α β hexternal hε hε1 hmtrunc
      p route v *
    r324NonzeroRouteSlotCost route i

theorem r324RefinedEndpointNonzeroRoutedDensityTerm_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (v : Fin (2 * m) → T4) :
    0 ≤
      ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
        lam hm ε α β hexternal hε hε1 hmtrunc
        i p route v := by
  unfold r324RefinedEndpointNonzeroRoutedDensityTerm
  exact
    mul_nonneg
      (ρ.r324RefinedEndpointNonzeroRouteDensityBase_nonneg
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route v)
      (r324NonzeroRouteSlotCost_pos route i).le

theorem
    r324RefinedEndpointNonzeroRouteDensityBase_le_routed
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m)
    (v : Fin (2 * m) → T4) :
    ρ.r324RefinedEndpointNonzeroRouteDensityBase
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route v ≤
      ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
        lam hm ε α β hexternal hε hε1 hmtrunc
        i p route v := by
  unfold r324RefinedEndpointNonzeroRoutedDensityTerm
  exact le_mul_of_one_le_right
    (ρ.r324RefinedEndpointNonzeroRouteDensityBase_nonneg
      lam hm ε α β hexternal hε hε1 hmtrunc
      p route v)
    (one_le_r324NonzeroRouteSlotCost route i)

/-- Qualitative integrability of each corrected routed density term.
Summability over all route labels is intentionally left to the later
high-mode enlargement argument. -/
theorem integrable_r324RefinedEndpointNonzeroRoutedDensityTerm
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    Integrable
      (ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
        lam hm ε α β hexternal hε hε1 hmtrunc
        i p route)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  have hbase :=
    ρ.integrable_r324RefinedEndpointNonzeroRouteDensityBase
      lam hm hε α β hexternal hε1 hmtrunc p route
  unfold r324RefinedEndpointNonzeroRoutedDensityTerm
  exact hbase.mul_const
    (r324NonzeroRouteSlotCost route i)

/-- Triangle inequality in internal `L¹`, still retaining the genuine
signed route fibre on the left. -/
theorem
    integral_norm_r324RefinedEndpointNonzeroRouteInternalCore_le
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    (∫ v,
      ‖ρ.r324RefinedEndpointNonzeroRouteInternalCore
        hm ε α β hexternal hε hε1 hmtrunc
        p route v‖
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) ≤
      ∑' a :
          ρ.R324RefinedEndpointNonzeroRouteFiber
            hm ε α β hexternal hε hε1 hmtrunc p route,
        ∫ v,
          ‖ρ.r324RefinedEndpointNonzeroRouteInternalTerm
            hm ε α β hexternal hε hε1 hmtrunc
            p route a v‖
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  let F :
      ρ.R324RefinedEndpointNonzeroRouteFiber
          hm ε α β hexternal hε hε1 hmtrunc p route →
        (Fin (2 * m) → T4) → ℝ :=
    fun a v =>
      ‖ρ.r324RefinedEndpointNonzeroRouteInternalTerm
        hm ε α β hexternal hε hε1 hmtrunc
        p route a v‖
  have hFint :
      ∀ a, Integrable (F a)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    fun a =>
      ρ.integrable_norm_r324RefinedEndpointNonzeroRouteInternalTerm
        hm hε α β hexternal hε1 hmtrunc p route a
  have hFsum :
      Summable fun a =>
        ∫ v, ‖F a v‖
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
    refine
      (ρ.summable_integral_norm_r324RefinedEndpointNonzeroRouteInternalTerm
        hm hε α β hexternal hε1 hmtrunc p route).congr ?_
    intro a
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hmajor :
      Integrable (fun v => ∑' a, F a v)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    integrable_tsum_of_summable_integral_norm_nonzeroRoute
      F hFint hFsum
  calc
    (∫ v,
        ‖ρ.r324RefinedEndpointNonzeroRouteInternalCore
          hm ε α β hexternal hε hε1 hmtrunc
          p route v‖
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) ≤
        ∫ v, ∑' a, F a v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      exact integral_mono
        (ρ.integrable_r324RefinedEndpointNonzeroRouteInternalCore
          hm hε α β hexternal hε1 hmtrunc p route).norm
        hmajor
        (fun v =>
          norm_tsum_le_tsum_norm
            (ρ.summable_r324RefinedEndpointNonzeroRouteInternalTerm
              hm hε α β hexternal hε1 hmtrunc
              p route v).norm)
    _ =
        ∑' a,
          ∫ v, F a v
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      exact
        (integral_tsum_of_summable_integral_norm
          hFint hFsum).symm

/-- The unweighted internal route density is bounded by the exact raw
covariance masses in that route fibre. -/
theorem
    integral_r324RefinedEndpointNonzeroRouteDensityBase_le_rawFiber
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    (∫ v,
      ρ.r324RefinedEndpointNonzeroRouteDensityBase
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route v
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) ≤
      |lamEps lam ε| ^ (2 * m) *
        (r324NonzeroRouteInteriorSkeletonL1 route *
          ∑' a :
              ρ.R324RefinedEndpointNonzeroRouteFiber
                hm ε α β hexternal hε hε1 hmtrunc p route,
            ρ.r324RefinedRawCovarianceWeight
              hm ε p a.1.1) := by
  have hscalar :
      0 ≤ |lamEps lam ε| ^ (2 * m) :=
    pow_nonneg (abs_nonneg _) _
  calc
    (∫ v,
        ρ.r324RefinedEndpointNonzeroRouteDensityBase
          lam hm ε α β hexternal hε hε1 hmtrunc
          p route v
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
        |lamEps lam ε| ^ (2 * m) *
          ∫ v,
            ‖ρ.r324RefinedEndpointNonzeroRouteInternalCore
              hm ε α β hexternal hε hε1 hmtrunc
              p route v‖
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      unfold r324RefinedEndpointNonzeroRouteDensityBase
      rw [integral_const_mul]
    _ ≤
        |lamEps lam ε| ^ (2 * m) *
          ∑' a :
              ρ.R324RefinedEndpointNonzeroRouteFiber
                hm ε α β hexternal hε hε1 hmtrunc p route,
            ∫ v,
              ‖ρ.r324RefinedEndpointNonzeroRouteInternalTerm
                hm ε α β hexternal hε hε1 hmtrunc
                p route a v‖
              ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
      mul_le_mul_of_nonneg_left
        (ρ.integral_norm_r324RefinedEndpointNonzeroRouteInternalCore_le
          hm hε α β hexternal hε1 hmtrunc p route)
        hscalar
    _ =
        |lamEps lam ε| ^ (2 * m) *
          (r324NonzeroRouteInteriorSkeletonL1 route *
            ∑' a :
                ρ.R324RefinedEndpointNonzeroRouteFiber
                  hm ε α β hexternal hε hε1 hmtrunc p route,
              ρ.r324RefinedRawCovarianceWeight
                hm ε p a.1.1) := by
      congr 1
      calc
        (∑' a :
            ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc p route,
          ∫ v,
            ‖ρ.r324RefinedEndpointNonzeroRouteInternalTerm
              hm ε α β hexternal hε hε1 hmtrunc
              p route a v‖
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
            ∑' a :
                ρ.R324RefinedEndpointNonzeroRouteFiber
                  hm ε α β hexternal hε hε1 hmtrunc p route,
              r324NonzeroRouteInteriorSkeletonL1 route *
                ρ.r324RefinedRawCovarianceWeight
                  hm ε p a.1.1 := by
          apply tsum_congr
          intro a
          exact
            ρ.integral_norm_r324RefinedEndpointNonzeroRouteInternalTerm
              hm ε α β hexternal hε hε1 hmtrunc
              p route a
        _ =
            r324NonzeroRouteInteriorSkeletonL1 route *
              ∑' a :
                  ρ.R324RefinedEndpointNonzeroRouteFiber
                    hm ε α β hexternal hε hε1 hmtrunc p route,
                ρ.r324RefinedRawCovarianceWeight
                  hm ε p a.1.1 := by
          rw [tsum_mul_left]

/-- After summing all marked slots, one corrected route density is
bounded by the raw degree-eight covariance route weights in precisely
that route fibre. -/
theorem
    sum_integral_r324RefinedEndpointNonzeroRoutedDensityTerm_le_rawFiber
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    (∑ i : Fin m,
      ∫ v,
        ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
          lam hm ε α β hexternal hε hε1 hmtrunc
          i p route v
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) ≤
      |lamEps lam ε| ^ (2 * m) *
        (r324NonzeroRouteInteriorSkeletonL1 route *
          ∑' a :
              ρ.R324RefinedEndpointNonzeroRouteFiber
                hm ε α β hexternal hε hε1 hmtrunc p route,
            ρ.r324RefinedRawCovarianceRouteWeight
              hm ε p a.1.1) := by
  let routeCost : ℝ :=
    ∑ i : Fin m, r324NonzeroRouteSlotCost route i
  have hrouteCost :
      0 ≤ routeCost :=
    Finset.sum_nonneg fun i _ =>
      (r324NonzeroRouteSlotCost_pos route i).le
  have hbase :=
    ρ.integral_r324RefinedEndpointNonzeroRouteDensityBase_le_rawFiber
      lam hm hε α β hexternal hε1 hmtrunc p route
  have hraw :
      (∑' a :
          ρ.R324RefinedEndpointNonzeroRouteFiber
            hm ε α β hexternal hε hε1 hmtrunc p route,
        ρ.r324RefinedRawCovarianceRouteWeight
          hm ε p a.1.1) =
        (∑' a :
            ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc p route,
          ρ.r324RefinedRawCovarianceWeight
            hm ε p a.1.1) *
          routeCost := by
    calc
      (∑' a :
          ρ.R324RefinedEndpointNonzeroRouteFiber
            hm ε α β hexternal hε hε1 hmtrunc p route,
        ρ.r324RefinedRawCovarianceRouteWeight
          hm ε p a.1.1) =
          ∑' a :
              ρ.R324RefinedEndpointNonzeroRouteFiber
                hm ε α β hexternal hε hε1 hmtrunc p route,
            ρ.r324RefinedRawCovarianceWeight hm ε p a.1.1 *
              routeCost := by
        apply tsum_congr
        intro a
        unfold r324RefinedRawCovarianceRouteWeight
          r324IncrementKeyCost routeCost
        rw [
          ρ.r324RefinedEndpointNonzeroRouteFiber_key
            hm ε α β hexternal hε hε1 hmtrunc
            p route a]
        rfl
      _ =
          (∑' a :
              ρ.R324RefinedEndpointNonzeroRouteFiber
                hm ε α β hexternal hε hε1 hmtrunc p route,
            ρ.r324RefinedRawCovarianceWeight
              hm ε p a.1.1) *
            routeCost := by
        rw [tsum_mul_right]
  calc
    (∑ i : Fin m,
        ∫ v,
          ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
            lam hm ε α β hexternal hε hε1 hmtrunc
            i p route v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
        (∫ v,
          ρ.r324RefinedEndpointNonzeroRouteDensityBase
            lam hm ε α β hexternal hε hε1 hmtrunc
            p route v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) *
          routeCost := by
      unfold r324RefinedEndpointNonzeroRoutedDensityTerm
        routeCost
      simp_rw [integral_mul_const]
      rw [Finset.mul_sum]
    _ ≤
        (|lamEps lam ε| ^ (2 * m) *
          (r324NonzeroRouteInteriorSkeletonL1 route *
            ∑' a :
                ρ.R324RefinedEndpointNonzeroRouteFiber
                  hm ε α β hexternal hε hε1 hmtrunc p route,
              ρ.r324RefinedRawCovarianceWeight
                hm ε p a.1.1)) *
          routeCost :=
      mul_le_mul_of_nonneg_right hbase hrouteCost
    _ =
        |lamEps lam ε| ^ (2 * m) *
          (r324NonzeroRouteInteriorSkeletonL1 route *
            ∑' a :
                ρ.R324RefinedEndpointNonzeroRouteFiber
                  hm ε α β hexternal hε hε1 hmtrunc p route,
              ρ.r324RefinedRawCovarianceRouteWeight
                hm ε p a.1.1) := by
      rw [hraw]
      ring

/-- Each exact signed route coefficient is controlled by every marked
slot version of its corrected routed density. -/
theorem
    norm_integral_r324RefinedEndpointNonzeroRoutePhysicalCore_le_routed
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    |lamEps lam ε| ^ (2 * m) *
        ‖∫ q,
          ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
            hm ε α β hexternal hε hε1 hmtrunc
            p route q
          ∂(r324PhysicalMeasure m)‖ ≤
      (16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β) *
        ∫ v,
          ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
            lam hm ε α β hexternal hε hε1 hmtrunc
            i p route v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  refine
    (ρ.norm_integral_r324RefinedEndpointNonzeroRoutePhysicalCore_le_base
      lam hm hε α β hexternal hε1 hmtrunc
      p route).trans ?_
  exact mul_le_mul_of_nonneg_left
    (integral_mono
      (ρ.integrable_r324RefinedEndpointNonzeroRouteDensityBase
        lam hm hε α β hexternal hε1 hmtrunc p route)
      (ρ.integrable_r324RefinedEndpointNonzeroRoutedDensityTerm
        lam hm hε α β hexternal hε1 hmtrunc
        i p route)
      (fun v =>
        ρ.r324RefinedEndpointNonzeroRouteDensityBase_le_routed
          lam hm ε α β hexternal hε hε1 hmtrunc
          i p route v))
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β))

/-! ## Direct route terms and their marked-slot budgets -/

/-- The exact contribution of one corrected route to the deterministic
moment expansion. -/
def r324RefinedEndpointNonzeroRouteMomentTerm
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) : ℂ :=
  (lamEps lam ε ^ (2 * m) : ℂ) *
    ∫ q,
      ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
        hm ε α β hexternal hε hε1 hmtrunc
        p route q
      ∂(r324PhysicalMeasure m)

/-- A route pays all marked slots at once.  Consequently any slot may
later be selected by the central-frequency pigeonhole argument without
changing the route enumeration. -/
def r324RefinedEndpointNonzeroRouteWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) : ℝ :=
  (16 * paperFourthOrderModeDecay α *
      paperFourthOrderModeDecay β) *
    ∑ i : Fin m,
      ∫ v,
        ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
          lam hm ε α β hexternal hε hε1 hmtrunc
          i p route v
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

theorem r324RefinedEndpointNonzeroRouteWeight_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    0 ≤
      ρ.r324RefinedEndpointNonzeroRouteWeight
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route := by
  unfold r324RefinedEndpointNonzeroRouteWeight
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β))
    (Finset.sum_nonneg fun i _hi =>
      integral_nonneg fun v =>
        ρ.r324RefinedEndpointNonzeroRoutedDensityTerm_nonneg
          lam hm ε α β hexternal hε hε1 hmtrunc
          i p route v)

/-- Uniform raw majorant for a corrected route.  The only infinite
factor is the genuine fibre sum of the already-proved degree-eight raw
covariance route weights; the skeleton envelope is a finite contraction
sum. -/
def r324RefinedEndpointNonzeroRouteRawMajorant
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) : ℝ :=
  (16 * paperFourthOrderModeDecay α *
      paperFourthOrderModeDecay β) *
    (|lamEps lam ε| ^ (2 * m) *
      (r324AllContractionInteriorSkeletonL1 m *
        ∑' a :
            ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc p route,
          ρ.r324RefinedRawCovarianceRouteWeight
            hm ε p a.1.1))

theorem r324RefinedEndpointNonzeroRouteRawMajorant_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    0 ≤
      ρ.r324RefinedEndpointNonzeroRouteRawMajorant
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route := by
  unfold r324RefinedEndpointNonzeroRouteRawMajorant
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β))
    (mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (mul_nonneg
        (r324AllContractionInteriorSkeletonL1_nonneg m)
        (tsum_nonneg fun a =>
          ρ.r324RefinedRawCovarianceRouteWeight_nonneg
            hm ε p a.1.1)))

theorem
    r324RefinedEndpointNonzeroRouteWeight_le_rawMajorant
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    ρ.r324RefinedEndpointNonzeroRouteWeight
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route ≤
      ρ.r324RefinedEndpointNonzeroRouteRawMajorant
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route := by
  have hscale :
      0 ≤
        16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β :=
    mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β)
  have hscalar :
      0 ≤ |lamEps lam ε| ^ (2 * m) :=
    pow_nonneg (abs_nonneg _) _
  have hfibre :
      0 ≤
        ∑' a :
            ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc p route,
          ρ.r324RefinedRawCovarianceRouteWeight
            hm ε p a.1.1 :=
    tsum_nonneg fun a =>
      ρ.r324RefinedRawCovarianceRouteWeight_nonneg
        hm ε p a.1.1
  unfold r324RefinedEndpointNonzeroRouteWeight
    r324RefinedEndpointNonzeroRouteRawMajorant
  refine mul_le_mul_of_nonneg_left ?_ hscale
  refine
    (ρ.sum_integral_r324RefinedEndpointNonzeroRoutedDensityTerm_le_rawFiber
      lam hm hε α β hexternal hε1 hmtrunc p route).trans ?_
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (r324NonzeroRouteInteriorSkeletonL1_le_all route)
      hfibre)
    hscalar

/-- Qualitative summability of the raw majorants on one refined
schedule, obtained by the exact route-fibre partition of the weighted
raw covariance series. -/
theorem
    summable_r324RefinedEndpointNonzeroRouteRawMajorant
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) :
    Summable fun route : R324NonzeroRouteLabel m =>
      ρ.r324RefinedEndpointNonzeroRouteRawMajorant
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route := by
  let raw :
      ρ.R324RefinedEndpointNonzeroRawConfiguration
          hm ε α β p → ℝ :=
    fun a =>
      ρ.r324RefinedRawCovarianceRouteWeight
        hm ε p a.1
  let selected :
      ρ.R324RefinedEndpointNonzeroRawConfiguration
          hm ε α β p →
        R324NonzeroRouteLabel m :=
    ρ.r324RefinedEndpointNonzeroRouteLabel
      hm ε α β hexternal hε hε1 hmtrunc p
  have hraw : Summable raw :=
    (ρ.summable_r324RefinedRawCovarianceRouteWeight
      hm hε p).subtype _
  have hfibres :
      Summable fun route : R324NonzeroRouteLabel m =>
        ∑' a :
            ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc
              p route,
          ρ.r324RefinedRawCovarianceRouteWeight
            hm ε p a.1.1 := by
    exact (hraw.hasSum.tsum_fiberwise selected).summable
  let scale : ℝ :=
    (16 * paperFourthOrderModeDecay α *
        paperFourthOrderModeDecay β) *
      (|lamEps lam ε| ^ (2 * m) *
        r324AllContractionInteriorSkeletonL1 m)
  exact (hfibres.mul_left scale).congr fun route => by
    unfold r324RefinedEndpointNonzeroRouteRawMajorant
    dsimp only [scale]
    ring

/-- The corrected route weights are independently summable; this is a
theorem of the raw cutoff decay, not a field supplied by phase A. -/
theorem summable_all_r324RefinedEndpointNonzeroRouteWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    Summable fun pr :
        R324RefinedScheduleIndex m × R324NonzeroRouteLabel m =>
      ρ.r324RefinedEndpointNonzeroRouteWeight
        lam hm ε α β hexternal hε hε1 hmtrunc
        pr.1 pr.2 := by
  have hmajor :
      Summable fun pr :
          R324RefinedScheduleIndex m ×
            R324NonzeroRouteLabel m =>
        ρ.r324RefinedEndpointNonzeroRouteRawMajorant
          lam hm ε α β hexternal hε hε1 hmtrunc
          pr.1 pr.2 := by
    rw [summable_prod_of_nonneg
      (fun pr =>
        ρ.r324RefinedEndpointNonzeroRouteRawMajorant_nonneg
          lam hm ε α β hexternal hε hε1 hmtrunc
          pr.1 pr.2)]
    constructor
    · intro p
      exact
        ρ.summable_r324RefinedEndpointNonzeroRouteRawMajorant
          lam hm hε α β hexternal hε1 hmtrunc p
    · exact Summable.of_finite
  exact hmajor.of_nonneg_of_le
    (fun pr =>
      ρ.r324RefinedEndpointNonzeroRouteWeight_nonneg
        lam hm ε α β hexternal hε hε1 hmtrunc
        pr.1 pr.2)
    (fun pr =>
      ρ.r324RefinedEndpointNonzeroRouteWeight_le_rawMajorant
        lam hm hε α β hexternal hε1 hmtrunc
        pr.1 pr.2)

/-- The exact route term is paid by any one of its marked-slot
densities, with the reciprocal eighth-order cost restored as decay. -/
theorem
    norm_r324RefinedEndpointNonzeroRouteMomentTerm_le_slotDecay
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    ‖ρ.r324RefinedEndpointNonzeroRouteMomentTerm
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route‖ ≤
      ((16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β) *
        ∫ v,
          ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
            lam hm ε α β hexternal hε hε1 hmtrunc
            i p route v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) *
        eighthOrderFrequencyDecay
          ‖z4EuclideanFrequency (route.2.1 i)‖ := by
  calc
    ‖ρ.r324RefinedEndpointNonzeroRouteMomentTerm
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route‖ =
        |lamEps lam ε| ^ (2 * m) *
          ‖∫ q,
            ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
              hm ε α β hexternal hε hε1 hmtrunc
              p route q
            ∂(r324PhysicalMeasure m)‖ := by
      simp only [
        r324RefinedEndpointNonzeroRouteMomentTerm,
        norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs]
    _ ≤
        (16 * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) *
          ∫ v,
            ρ.r324RefinedEndpointNonzeroRouteDensityBase
              lam hm ε α β hexternal hε hε1 hmtrunc
              p route v
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
      ρ.norm_integral_r324RefinedEndpointNonzeroRoutePhysicalCore_le_base
        lam hm hε α β hexternal hε1 hmtrunc
        p route
    _ =
        ((16 * paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β) *
          ∫ v,
            ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
              lam hm ε α β hexternal hε hε1 hmtrunc
              i p route v
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) *
          eighthOrderFrequencyDecay
            ‖z4EuclideanFrequency (route.2.1 i)‖ := by
      unfold r324RefinedEndpointNonzeroRoutedDensityTerm
      rw [integral_mul_const]
      have hcost :=
        r324NonzeroRouteSlotCost_mul_decay route i
      let B : ℝ :=
        ∫ v,
          ρ.r324RefinedEndpointNonzeroRouteDensityBase
            lam hm ε α β hexternal hε hε1 hmtrunc
            p route v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)
      let scale : ℝ :=
        16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β
      let cost : ℝ :=
        r324NonzeroRouteSlotCost route i
      let decay : ℝ :=
        eighthOrderFrequencyDecay
          ‖z4EuclideanFrequency (route.2.1 i)‖
      change cost * decay = 1 at hcost
      change scale * B = (scale * (B * cost)) * decay
      calc
        scale * B = scale * (B * 1) := by ring
        _ = scale * (B * (cost * decay)) := by
          rw [hcost]
        _ = (scale * (B * cost)) * decay := by
          ring

/-- Paying the finite sum of all slot densities makes the local decay
estimate uniform in the subsequently selected slot. -/
theorem
    norm_r324RefinedEndpointNonzeroRouteMomentTerm_le_weight_mul_decay
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m)
    (route : R324NonzeroRouteLabel m) :
    ‖ρ.r324RefinedEndpointNonzeroRouteMomentTerm
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route‖ ≤
      ρ.r324RefinedEndpointNonzeroRouteWeight
          lam hm ε α β hexternal hε hε1 hmtrunc
          p route *
        eighthOrderFrequencyDecay
          ‖z4EuclideanFrequency (route.2.1 i)‖ := by
  have hscale :
      0 ≤
        16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β :=
    mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β)
  let g : Fin m → ℝ := fun j =>
    ∫ v,
      ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
        lam hm ε α β hexternal hε hε1 hmtrunc
        j p route v
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)
  have hg : ∀ j, 0 ≤ g j := by
    intro j
    exact integral_nonneg fun v =>
      ρ.r324RefinedEndpointNonzeroRoutedDensityTerm_nonneg
        lam hm ε α β hexternal hε hε1 hmtrunc
        j p route v
  have hi' :
      g i ≤ ∑ j : Fin m, g j :=
    Finset.single_le_sum
      (fun j _hj => hg j)
      (Finset.mem_univ i)
  have hi :
      (∫ v,
          ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
            lam hm ε α β hexternal hε hε1 hmtrunc
            i p route v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) ≤
        ∑ j : Fin m,
          ∫ v,
            ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
              lam hm ε α β hexternal hε hε1 hmtrunc
              j p route v
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
    simpa only [g] using hi'
  refine
    (ρ.norm_r324RefinedEndpointNonzeroRouteMomentTerm_le_slotDecay
      lam hm hε α β hexternal hε1 hmtrunc
      i p route).trans ?_
  unfold r324RefinedEndpointNonzeroRouteWeight
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hi hscale)
    (eighthOrderFrequencyDecay_nonneg _)

/-! ## Exact countable route expansion -/

/-- For one refined schedule, the exact corrected route terms form an
absolutely summable series.  This is inherited from the raw complete
endpoint coefficients and the genuine route-fibre partition. -/
theorem summable_r324RefinedEndpointNonzeroRouteMomentTerm
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) :
    Summable fun route : R324NonzeroRouteLabel m =>
      ρ.r324RefinedEndpointNonzeroRouteMomentTerm
        lam hm ε α β hexternal hε hε1 hmtrunc
        p route := by
  let raw :
      ρ.R324RefinedEndpointNonzeroRawConfiguration
          hm ε α β p → ℂ :=
    fun a =>
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a.1
  let selected :
      ρ.R324RefinedEndpointNonzeroRawConfiguration
          hm ε α β p →
        R324NonzeroRouteLabel m :=
    ρ.r324RefinedEndpointNonzeroRouteLabel
      hm ε α β hexternal hε hε1 hmtrunc p
  have hraw : Summable raw :=
    (ρ.summable_r324RefinedRawFullPairingIntegral
      hm hε α β p).subtype _
  have hfibres :
      Summable fun route : R324NonzeroRouteLabel m =>
        ∑' a :
            ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc
              p route,
          ρ.r324RefinedRawFullPairingIntegral
            hm ε α β p a.1.1 := by
    exact (hraw.hasSum.tsum_fiberwise selected).summable
  have hintegrals :
      Summable fun route : R324NonzeroRouteLabel m =>
        ∫ q,
          ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
            hm ε α β hexternal hε hε1 hmtrunc
            p route q
          ∂(r324PhysicalMeasure m) := by
    exact hfibres.congr fun route =>
      (ρ.integral_r324RefinedEndpointNonzeroRoutePhysicalCore
        hm hε α β hexternal hε1 hmtrunc p route).symm
  exact
    (hintegrals.mul_left
      (lamEps lam ε ^ (2 * m) : ℂ)).congr fun route => by
        rfl

/-- Absolute summability after adjoining the finite refined-schedule
index. -/
theorem summable_all_r324RefinedEndpointNonzeroRouteMomentTerm
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    Summable fun pr :
        R324RefinedScheduleIndex m × R324NonzeroRouteLabel m =>
      ρ.r324RefinedEndpointNonzeroRouteMomentTerm
        lam hm ε α β hexternal hε hε1 hmtrunc
        pr.1 pr.2 := by
  apply Summable.of_norm
  rw [summable_prod_of_nonneg (fun pr => norm_nonneg _)]
  constructor
  · intro p
    exact
      (ρ.summable_r324RefinedEndpointNonzeroRouteMomentTerm
        lam hm hε α β hexternal hε1 hmtrunc p).norm
  · exact Summable.of_finite

/-- The deterministic moment is exactly the `tsum` over the corrected
schedule/route product. -/
theorem deterministicMomentPairingSum_eq_tsum_nonzeroRouteMomentTerm
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε) :
    deterministicMomentPairingSum ρ lam ε m α β =
      ∑' pr :
          R324RefinedScheduleIndex m × R324NonzeroRouteLabel m,
        ρ.r324RefinedEndpointNonzeroRouteMomentTerm
          lam hm ε α β hexternal hε hε1 hmtrunc
          pr.1 pr.2 := by
  let f :
      R324RefinedScheduleIndex m × R324NonzeroRouteLabel m → ℂ :=
    fun pr =>
      ρ.r324RefinedEndpointNonzeroRouteMomentTerm
        lam hm ε α β hexternal hε hε1 hmtrunc
        pr.1 pr.2
  have hf : Summable f :=
    ρ.summable_all_r324RefinedEndpointNonzeroRouteMomentTerm
      lam hm hε α β hexternal hε1 hmtrunc
  calc
    deterministicMomentPairingSum ρ lam ε m α β =
        (lamEps lam ε ^ (2 * m) : ℂ) *
          ∑ p : R324RefinedScheduleIndex m,
            ∑' route : R324NonzeroRouteLabel m,
              ∫ q,
                ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
                  hm ε α β hexternal hε hε1 hmtrunc
                  p route q
                ∂(r324PhysicalMeasure m) :=
      ρ.deterministicMomentPairingSum_eq_nonzeroRoutedPhysical
        lam hm hε α β hexternal hε1 hmtrunc
    _ =
        ∑ p : R324RefinedScheduleIndex m,
          ∑' route : R324NonzeroRouteLabel m,
            f (p, route) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      dsimp only [f,
        r324RefinedEndpointNonzeroRouteMomentTerm]
      rw [tsum_mul_left]
    _ =
        ∑' p : R324RefinedScheduleIndex m,
          ∑' route : R324NonzeroRouteLabel m,
            f (p, route) := by
      rw [tsum_fintype]
    _ =
        ∑' pr :
            R324RefinedScheduleIndex m × R324NonzeroRouteLabel m,
          f pr :=
      hf.tsum_prod.symm

/-- The finite schedule index times the corrected countable route label
is denumerable when `m > 0`. -/
def r324NatEquivRefinedEndpointNonzeroRoutes
    {m : ℕ} (hm : 0 < m) :
    ℕ ≃
      R324RefinedScheduleIndex m × R324NonzeroRouteLabel m := by
  classical
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  letI : Infinite (Fin m → Z4) := inferInstance
  letI :
      Encodable
        (R324RefinedScheduleIndex m ×
          R324NonzeroRouteLabel m) :=
    Encodable.ofCountable _
  letI :
      Denumerable
        (R324RefinedScheduleIndex m ×
          R324NonzeroRouteLabel m) :=
    Denumerable.ofEncodableOfInfinite _
  exact
    (Denumerable.eqv
      (R324RefinedScheduleIndex m ×
        R324NonzeroRouteLabel m)).symm

/-- Nonzero route terms use their genuine complete key.  Zero terms use
a harmless delta route so that frequency conservation remains an
unconditional field of the countable decomposition. -/
def r324RefinedEndpointNonzeroRouteIncrement
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (pr :
      R324RefinedScheduleIndex m × R324NonzeroRouteLabel m)
    (i : Fin m) :
    EuclideanSpace ℝ (Fin dim) :=
  if ρ.r324RefinedEndpointNonzeroRouteMomentTerm
      lam hm ε α β hexternal hε hε1 hmtrunc
      pr.1 pr.2 ≠ 0 then
    z4EuclideanFrequency (pr.2.2.1 i)
  else if i = ⟨0, hm⟩ then
    z4EuclideanFrequency (α + β)
  else
    0

/-- A nonzero corrected route term has an inhabited genuine route
fibre, hence its complete key sums to the external frequency. -/
theorem sum_r324RefinedEndpointNonzeroRouteIncrement
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (pr :
      R324RefinedScheduleIndex m × R324NonzeroRouteLabel m) :
    (∑ i,
      ρ.r324RefinedEndpointNonzeroRouteIncrement
        lam hm ε α β hexternal hε hε1 hmtrunc
        pr i) =
      z4EuclideanFrequency (α + β) := by
  classical
  unfold r324RefinedEndpointNonzeroRouteIncrement
  split_ifs with hterm
  · have hintegral :
        (∫ q,
          ρ.r324RefinedEndpointNonzeroRoutePhysicalCore
            hm ε α β hexternal hε hε1 hmtrunc
            pr.1 pr.2 q
          ∂(r324PhysicalMeasure m)) ≠ 0 := by
        intro hzero
        apply hterm
        unfold r324RefinedEndpointNonzeroRouteMomentTerm
        rw [hzero, mul_zero]
    have hfibre :
        Nonempty
          (ρ.R324RefinedEndpointNonzeroRouteFiber
            hm ε α β hexternal hε hε1 hmtrunc
            pr.1 pr.2) := by
      by_contra hnone
      letI :
          IsEmpty
            (ρ.R324RefinedEndpointNonzeroRouteFiber
              hm ε α β hexternal hε hε1 hmtrunc
              pr.1 pr.2) :=
        ⟨fun a => hnone ⟨a⟩⟩
      apply hintegral
      rw [
        ρ.integral_r324RefinedEndpointNonzeroRoutePhysicalCore
          hm hε α β hexternal hε1 hmtrunc
          pr.1 pr.2]
      simp
    exact
      ρ.sum_r324RefinedEndpointNonzeroRouteKey_eq_external
        hm ε α β hexternal hε hε1 hmtrunc
        pr.1 pr.2 (Classical.choice hfibre)
  · simp only [
      Finset.sum_ite_eq' Finset.univ
        (⟨0, hm⟩ : Fin m)
        (fun _ => z4EuclideanFrequency (α + β)),
      Finset.mem_univ, if_true]

/-- Direct constructor of the central countable routing output from the
route weights. -/
theorem
    countableCentralRoutedMomentReductionOutput_of_nonzeroRoutes
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (weightBudget : ℝ)
    (hbudget :
      (∑' pr :
          R324RefinedScheduleIndex m × R324NonzeroRouteLabel m,
        ρ.r324RefinedEndpointNonzeroRouteWeight
          lam hm ε α β hexternal hε hε1 hmtrunc
          pr.1 pr.2) ≤
        weightBudget) :
    CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β weightBudget := by
  let E := r324NatEquivRefinedEndpointNonzeroRoutes hm
  let routeTerm :
      R324RefinedScheduleIndex m ×
          R324NonzeroRouteLabel m → ℂ :=
    fun pr =>
      ρ.r324RefinedEndpointNonzeroRouteMomentTerm
        lam hm ε α β hexternal hε hε1 hmtrunc
        pr.1 pr.2
  let routeWeight :
      R324RefinedScheduleIndex m ×
          R324NonzeroRouteLabel m → ℝ :=
    fun pr =>
      ρ.r324RefinedEndpointNonzeroRouteWeight
        lam hm ε α β hexternal hε hε1 hmtrunc
        pr.1 pr.2
  refine
    ⟨{ term := routeTerm ∘ E
       weight := routeWeight ∘ E
       incrementCount := fun _ => m
       increment := fun a i =>
         ρ.r324RefinedEndpointNonzeroRouteIncrement
           lam hm ε α β hexternal hε hε1 hmtrunc
           (E a) i
       sum_eq := ?_
       summable_term := ?_
       summable_weight := ?_
       weight_nonneg := ?_
       incrementCount_pos := ?_
       incrementCount_le_trunc := ?_
       increment_sum := ?_
       term_le_increment_decay := ?_
       tsum_weight_le := ?_ }⟩
  · calc
      deterministicMomentPairingSum ρ lam ε m α β =
          ∑' pr :
              R324RefinedScheduleIndex m ×
                R324NonzeroRouteLabel m,
            routeTerm pr := by
        exact
          ρ.deterministicMomentPairingSum_eq_tsum_nonzeroRouteMomentTerm
            lam hm hε α β hexternal hε1 hmtrunc
      _ = ∑' a : ℕ, routeTerm (E a) :=
        (E.tsum_eq routeTerm).symm
  · exact
      E.summable_iff.mpr
        (ρ.summable_all_r324RefinedEndpointNonzeroRouteMomentTerm
          lam hm hε α β hexternal hε1 hmtrunc)
  · exact E.summable_iff.mpr
      (ρ.summable_all_r324RefinedEndpointNonzeroRouteWeight
        lam hm hε α β hexternal hε1 hmtrunc)
  · intro a
    exact
      ρ.r324RefinedEndpointNonzeroRouteWeight_nonneg
        lam hm ε α β hexternal hε hε1 hmtrunc
        (E a).1 (E a).2
  · intro _a
    exact hm
  · intro _a
    exact hmtrunc
  · intro a
    exact
      ρ.sum_r324RefinedEndpointNonzeroRouteIncrement
        lam hm hε α β hexternal hε1 hmtrunc
        (E a)
  · intro a i
    change
      ‖routeTerm (E a)‖ ≤
        routeWeight (E a) *
          eighthOrderFrequencyDecay
            ‖ρ.r324RefinedEndpointNonzeroRouteIncrement
              lam hm ε α β hexternal hε hε1 hmtrunc
              (E a) i‖
    by_cases hterm :
        routeTerm (E a) = 0
    · rw [hterm, norm_zero]
      exact mul_nonneg
        (ρ.r324RefinedEndpointNonzeroRouteWeight_nonneg
          lam hm ε α β hexternal hε hε1 hmtrunc
          (E a).1 (E a).2)
        (eighthOrderFrequencyDecay_nonneg _)
    · have hincrement :
          ρ.r324RefinedEndpointNonzeroRouteIncrement
              lam hm ε α β hexternal hε hε1 hmtrunc
              (E a) i =
            z4EuclideanFrequency ((E a).2.2.1 i) := by
          simp only [
            r324RefinedEndpointNonzeroRouteIncrement,
            routeTerm] at hterm ⊢
          rw [if_pos hterm]
      rw [hincrement]
      exact
        ρ.norm_r324RefinedEndpointNonzeroRouteMomentTerm_le_weight_mul_decay
          lam hm hε α β hexternal hε1 hmtrunc
          i (E a).1 (E a).2
  · calc
      (∑' a : ℕ, routeWeight (E a)) =
          ∑' pr :
              R324RefinedScheduleIndex m ×
                R324NonzeroRouteLabel m,
            routeWeight pr :=
        E.tsum_eq routeWeight
      _ ≤ weightBudget := hbudget

/-! ## The zero external-shift branch -/

/-- Endpoint-free `L¹` weight of a grouped configuration, without any
artificial reciprocal central-frequency cost. -/
def r324ZeroShiftGroupedCoreWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) : ℝ :=
  |lamEps lam ε| ^ (2 * m) *
    ρ.r324GroupedRefinedCoreL1 hm ε p

theorem r324ZeroShiftGroupedCoreWeight_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) :
    0 ≤ ρ.r324ZeroShiftGroupedCoreWeight lam hm ε p := by
  unfold r324ZeroShiftGroupedCoreWeight
  exact mul_nonneg
    (pow_nonneg (abs_nonneg _) _)
    (ρ.r324GroupedRefinedCoreL1_nonneg hm ε p)

/-- Four endpoint integrations applied to the zero-shift grouped term.
There is no eighth-order slot cost because the central decay is exactly
one in this branch. -/
def r324ZeroShiftGroupedWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (p : R324RefinedScheduleIndex m × ℕ) : ℝ :=
  (16 * paperFourthOrderModeDecay α *
      paperFourthOrderModeDecay β) *
    ρ.r324ZeroShiftGroupedCoreWeight lam hm ε p

theorem r324ZeroShiftGroupedWeight_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (p : R324RefinedScheduleIndex m × ℕ) :
    0 ≤ ρ.r324ZeroShiftGroupedWeight
      lam hm ε α β p := by
  unfold r324ZeroShiftGroupedWeight
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β))
    (ρ.r324ZeroShiftGroupedCoreWeight_nonneg
      lam hm ε p)

/-- The no-cost zero-shift core weights are qualitatively summable.  The
degree-eight grouped weights are used only as a summable majorant; the
zero-shift weight itself contains no such cost. -/
theorem summable_r324ZeroShiftGroupedCoreWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    Summable
      (ρ.r324ZeroShiftGroupedCoreWeight lam hm ε) := by
  have hle :
      ∀ p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324ZeroShiftGroupedCoreWeight lam hm ε p ≤
          ρ.r324GroupedRouteBaseWeight lam hm ε p := by
    intro p
    let A : ℝ :=
      ρ.r324ZeroShiftGroupedCoreWeight lam hm ε p
    have hA : 0 ≤ A :=
      ρ.r324ZeroShiftGroupedCoreWeight_nonneg
        lam hm ε p
    have hslot :
        1 ≤ r324GroupedIncrementCost hm p.2 ⟨0, hm⟩ := by
      unfold r324GroupedIncrementCost
      exact one_le_pow₀ (by
        nlinarith [
          sq_nonneg
            ‖z4EuclideanFrequency
              (r324NatEquivStandardConfigurations
                hm p.2 ⟨0, hm⟩)‖])
    have hsum :
        1 ≤ ∑ i : Fin m,
          r324GroupedIncrementCost hm p.2 i := by
      exact hslot.trans
        (Finset.single_le_sum
          (fun i _hi =>
            (r324GroupedIncrementCost_pos hm p.2 i).le)
          (Finset.mem_univ (⟨0, hm⟩ : Fin m)))
    unfold r324GroupedRouteBaseWeight
    change A ≤ A *
      ∑ i : Fin m, r324GroupedIncrementCost hm p.2 i
    exact le_mul_of_one_le_right hA hsum
  exact
    (ρ.summable_r324GroupedRouteBaseWeight_signed
      lam hm hε).of_nonneg_of_le
      (ρ.r324ZeroShiftGroupedCoreWeight_nonneg
        lam hm ε)
      hle

theorem summable_r324ZeroShiftGroupedWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4) :
    Summable
      (ρ.r324ZeroShiftGroupedWeight
        lam hm ε α β) := by
  unfold r324ZeroShiftGroupedWeight
  exact
    (ρ.summable_r324ZeroShiftGroupedCoreWeight
      lam hm hε).mul_left
        (16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β)

/-- Local endpoint Fourier estimate for a grouped configuration, with
no central-frequency cost. -/
theorem
    norm_r324GroupedEndpointConfigurationTerm_le_zeroShiftWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m × ℕ)
    (hcore :
      Integrable
        (fun v : Fin (2 * m) → T4 =>
          ‖ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p.1 p.2 v‖)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure)) :
    ‖r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p.1)
        (ρ.r324KeyGroupedRefinedEndpointCore
          hm ε p.1 p.2)‖ ≤
      ρ.r324ZeroShiftGroupedWeight
        lam hm ε α β p := by
  let scale : ℝ :=
    16 * paperFourthOrderModeDecay α *
      paperFourthOrderModeDecay β
  let scalar : ℝ :=
    |lamEps lam ε| ^ (2 * m)
  let core :
      (Fin (2 * m) → T4) → ℂ :=
    ρ.r324KeyGroupedRefinedEndpointCore
      hm ε p.1 p.2
  let endpointIntegral :
      (Fin (2 * m) → T4) → ℂ := fun v =>
    ∫ x, ∫ y, ∫ z, ∫ w,
      r324EndpointSeparatedIntegrand α β
        (r324ContractionEndpointAnchors hm
          (r324RefinedScheduleRepresentative p.1) v)
        (r324ContractionEndpointFlags
          (r324RefinedScheduleRepresentative p.1))
        (core v) x y z w
      ∂paperMeasure ∂paperMeasure
      ∂paperMeasure ∂paperMeasure
  have hscale : 0 ≤ scale := by
    dsimp only [scale]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (paperFourthOrderModeDecay_nonneg α))
      (paperFourthOrderModeDecay_nonneg β)
  have hscalar : 0 ≤ scalar := by
    dsimp only [scalar]
    positivity
  have hmajor :
      Integrable (fun v => scale * ‖core v‖)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    hcore.const_mul scale
  have hpoint :
      ∀ v, ‖endpointIntegral v‖ ≤
        scale * ‖core v‖ := by
    intro v
    exact
      norm_integral_r324EndpointSeparatedIntegrand_le_fourierOnly
        α β
        (r324ContractionEndpointAnchors hm
          (r324RefinedScheduleRepresentative p.1) v)
        (r324ContractionEndpointFlags
          (r324RefinedScheduleRepresentative p.1))
        (core v)
  have hintegral :
      ‖∫ v, endpointIntegral v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)‖ ≤
        ∫ v, scale * ‖core v‖
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    norm_integral_le_of_norm_le hmajor
      (Filter.Eventually.of_forall hpoint)
  unfold r324GroupedEndpointConfigurationTerm
    r324ZeroShiftGroupedWeight
    r324ZeroShiftGroupedCoreWeight
  change
    ‖(lamEps lam ε ^ (2 * m) : ℂ) *
        ∫ v, endpointIntegral v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)‖ ≤
      scale *
        (scalar *
          ρ.r324GroupedRefinedCoreL1 hm ε p)
  rw [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs]
  calc
    |lamEps lam ε| ^ (2 * m) *
          ‖∫ v, endpointIntegral v
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)‖ ≤
        scalar *
          ∫ v, scale * ‖core v‖
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
      mul_le_mul_of_nonneg_left hintegral hscalar
    _ =
        scale *
          (scalar *
            ρ.r324GroupedRefinedCoreL1 hm ε p) := by
      rw [integral_const_mul]
      unfold r324GroupedRefinedCoreL1
      dsimp only [scalar, scale, core]
      ring

/-- Honest countable central decomposition when the external shift is
zero.  No first-large selector is invoked: all routed increments are
zero, so every central decay factor is exactly one. -/
theorem
    countableCentralRoutedMomentReductionOutput_of_zeroShift
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (hshift : α + β = 0)
    (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (weightBudget : ℝ)
    (hbudget :
      (∑' p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324ZeroShiftGroupedWeight
          lam hm ε α β p) ≤
        weightBudget) :
    CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β weightBudget := by
  let E := r324NatEquivRefinedScheduleConfigurations m
  let d :=
    ρ.r324ConcreteRefinedCoreExpansion
      lam hm hε hmtrunc α β
  let routed :=
    d.toRefinedFourierRoutingData hε hε1
  let groupedTerm :
      R324RefinedScheduleIndex m × ℕ → ℂ :=
    fun p =>
      r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p.1)
        (ρ.r324KeyGroupedRefinedEndpointCore
          hm ε p.1 p.2)
  let groupedWeight :
      R324RefinedScheduleIndex m × ℕ → ℝ :=
    ρ.r324ZeroShiftGroupedWeight
      lam hm ε α β
  refine
    ⟨{ term := groupedTerm ∘ E
       weight := groupedWeight ∘ E
       incrementCount := fun _ => m
       increment := fun _ _ => 0
       sum_eq := ?_
       summable_term := ?_
       summable_weight := ?_
       weight_nonneg := ?_
       incrementCount_pos := ?_
       incrementCount_le_trunc := ?_
       increment_sum := ?_
       term_le_increment_decay := ?_
       tsum_weight_le := ?_ }⟩
  · calc
      deterministicMomentPairingSum ρ lam ε m α β =
          ∑' p : R324RefinedScheduleIndex m × ℕ,
            groupedTerm p := by
        exact routed.sum_eq
      _ = ∑' a : ℕ, groupedTerm (E a) :=
        (E.tsum_eq groupedTerm).symm
  · exact E.summable_iff.mpr
      (ρ.summable_all_r324KeyGroupedEndpointConfigurationTerm
        lam hm hε α β)
  · exact E.summable_iff.mpr
      (ρ.summable_r324ZeroShiftGroupedWeight
        lam hm hε α β)
  · intro a
    exact
      ρ.r324ZeroShiftGroupedWeight_nonneg
        lam hm ε α β (E a)
  · intro _a
    exact hm
  · intro _a
    exact hmtrunc
  · intro _a
    rw [Finset.sum_const_zero]
    rw [hshift]
    exact z4EuclideanFrequencyAddHom.map_zero.symm
  · intro a _i
    change
      ‖groupedTerm (E a)‖ ≤
        groupedWeight (E a) *
          eighthOrderFrequencyDecay ‖(0 :
            EuclideanSpace ℝ (Fin dim))‖
    have hlocal :=
      ρ.norm_r324GroupedEndpointConfigurationTerm_le_zeroShiftWeight
        lam hm ε α β (E a)
        (ρ.integrable_norm_r324KeyGroupedRefinedEndpointCore
          hm hε (E a).1 (E a).2)
    have hdecay :
        eighthOrderFrequencyDecay
          ‖(0 : EuclideanSpace ℝ (Fin dim))‖ = 1 := by
      norm_num [eighthOrderFrequencyDecay]
    rw [hdecay, mul_one]
    exact hlocal
  · calc
      (∑' a : ℕ, groupedWeight (E a)) =
          ∑' p : R324RefinedScheduleIndex m × ℕ,
            groupedWeight p :=
        E.tsum_eq groupedWeight
      _ ≤ weightBudget := hbudget

/-- Corrected density of one actual endpoint-reduction pattern.  The
endpoint-null deletion and endpoint Fourier integrations have already
been completed, so this density lives only on the internal variables. -/
def r324EndpointNonzeroRoutedCaseDensity
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : Fin m)
    (cases : R324EndpointReductionPattern)
    (v : Fin (2 * m) → T4) : ℝ :=
  ∑ p : R324RefinedScheduleIndex m,
    if r324RefinedEndpointReductionCase p = cases then
      ∑' route : R324NonzeroRouteLabel m,
        ρ.r324RefinedEndpointNonzeroRoutedDensityTerm
          lam hm ε α β hexternal hε hε1 hmtrunc
          i p route v
    else
      0

theorem r324EndpointNonzeroRoutedCaseDensity_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (i : Fin m)
    (cases : R324EndpointReductionPattern)
    (v : Fin (2 * m) → T4) :
    0 ≤
      ρ.r324EndpointNonzeroRoutedCaseDensity
        lam hm ε α β hexternal hε hε1 hmtrunc
        i cases v := by
  unfold r324EndpointNonzeroRoutedCaseDensity
  exact Finset.sum_nonneg fun p _hp => by
    split_ifs
    · exact tsum_nonneg fun route =>
        ρ.r324RefinedEndpointNonzeroRoutedDensityTerm_nonneg
          lam hm ε α β hexternal hε hε1 hmtrunc
          i p route v
    · exact le_rfl

/-! ## Honest downstream enlargement / phase-A interface -/

/-- Output expected from the later high-mode enlargement and physical
phase-A collapse.

The first inequality enlarges the genuine selector-restricted internal
density; the second collapses its internal integral to one surviving
relative variable.  The two endpoint Fourier decays were already
extracted before this interface.  This interface has no field involving
`r324RawCaseDensity` and therefore cannot silently revive the invalid
pre-endpoint zero deletion. -/
structure R324EndpointNonzeroDensityPhaseAOutput
    (lam ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (primitiveConstant supportConstant : ℝ) : Type where
  enlargedDensity :
    Fin m → R324EndpointReductionPattern →
      (Fin (2 * m) → T4) → ℝ
  enlargedDensity_integrable :
    ∀ (i : Fin m) (cases : R324EndpointReductionPattern),
      Integrable
        (enlargedDensity i cases)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure)
  correctedDensity_le_enlargedDensity :
    ∀ (i : Fin m) (cases : R324EndpointReductionPattern)
      (v : Fin (2 * m) → T4),
      ρ.r324EndpointNonzeroRoutedCaseDensity
          lam hm ε α β hexternal hε hε1 hmtrunc
          i cases v ≤
        enlargedDensity i cases v
  reducedDensity :
    Fin m → R324EndpointReductionPattern → T4 → ℝ
  reducedDensity_nonneg :
    ∀ (i : Fin m) (cases : R324EndpointReductionPattern)
      (z : T4),
      0 ≤ reducedDensity i cases z
  reducedDensity_integrable :
    ∀ (i : Fin m) (cases : R324EndpointReductionPattern),
      Integrable (reducedDensity i cases) paperMeasure
  enlarged_integral_le_reduced_integral :
    ∀ (i : Fin m) (cases : R324EndpointReductionPattern),
      (∫ v,
        enlargedDensity i cases v
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) ≤
        ∫ z, reducedDensity i cases z ∂paperMeasure
  pointwise_reduced_le_caseAdjustedMajorant :
    ∀ (i : Fin m) (cases : R324EndpointReductionPattern)
      (z : T4),
      reducedDensity i cases z ≤
        r324EndpointPatternAdjustedPrimitiveMajorant
          ε cases primitiveConstant lam supportConstant m z

end SmoothCutoff

end

end Anderson4D
