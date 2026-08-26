import Anderson4D.DetParametrix.Paper42_Moment.R324RawCaseDensityGrouping
import Anderson4D.DetParametrix.Paper42_Moment.R324SelectorRestrictedSignedBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324MarkedResidualPhysicalModeIntegration

/-!
# Exact physical representation boundary for the raw R-324 case density

The routed raw density is formed from norms of complete common-increment
groups.  The canonical high-mode selector, by contrast, is available
only for Fourier configurations whose full endpoint integral is
nonzero.  This file records the exact overlap between those two
representations and keeps the complementary endpoint-null series
explicit.

No unrestricted projected covariance, primitive majorant, or total
routed budget is introduced here.  In particular, the endpoint-null
remainder is not silently discarded when a norm has already been taken.
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

/-! ## Concrete data carried by one raw refined index -/

/-- The actual contraction selected by one raw refined natural index. -/
def r324RefinedRawMomentContraction
    {m : ℕ} (p : R324RefinedScheduleIndex m) (a : ℕ) :
    MomentContraction m :=
  (r324NatEquivRefinedContractionConfigurations p a).1.1

/-- The natural covariance-configuration number carried by one raw
refined index. -/
def r324RefinedRawConfigurationNumber
    {m : ℕ} (p : R324RefinedScheduleIndex m) (a : ℕ) : ℕ :=
  (r324NatEquivRefinedContractionConfigurations p a).2

/-- The full doubled pairing attached to one raw refined index. -/
def r324RefinedRawFullPairing
    {m : ℕ} (p : R324RefinedScheduleIndex m) (a : ℕ) :
    R324FullPairingIndex m :=
  momentContractionEquivFullPairing m
    (r324RefinedRawMomentContraction p a)

/-- The actual dependent Fourier assignment attached to one raw refined
index. -/
def r324RefinedRawCombinedConfiguration
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    R324CombinedFourierConfiguration
      (r324RefinedRawMomentContraction p a).1
      (r324RefinedRawMomentContraction p a).2.1
      (r324RefinedRawMomentContraction p a).2.2 :=
  r324FullConfigurationOfStandard
    (r324RefinedRawFullPairing p a)
    (r324NatEquivStandardConfigurations hm
      (r324RefinedRawConfigurationNumber p a))

/-- The endpoint-integrated Fourier coefficient of one raw refined
configuration. -/
def r324RefinedRawFullPairingIntegral
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ) : ℂ :=
  ρ.r324FullPairingFourierIntegral ε α β
    (r324RefinedRawFullPairing p a)
    (r324RefinedRawCombinedConfiguration hm p a)

/-- Package an endpoint-nonzero raw member in the exact subtype used by
the canonical high-mode selector. -/
def r324RefinedRawNonzeroCombinedConfiguration
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a ≠ 0) :
    R324NonzeroCombinedFourierConfiguration
      ρ ε α β
      (r324RefinedRawMomentContraction p a).1
      (r324RefinedRawMomentContraction p a).2.1
      (r324RefinedRawMomentContraction p a).2.2 :=
  ⟨r324RefinedRawCombinedConfiguration hm p a, hne⟩

/-- The canonical selected residual slot of an endpoint-nonzero raw
member. -/
def r324RefinedRawSelectedResidualSlot
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a ≠ 0) :
    R324ResidualCovarianceSlot
      (r324RefinedRawMomentContraction p a).1 :=
  ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
    ε α β
    (r324RefinedRawMomentContraction p a).1
    (r324RefinedRawMomentContraction p a).2.1
    (r324RefinedRawMomentContraction p a).2.2
    hexternal hε hε1 hmtrunc
    (ρ.r324RefinedRawNonzeroCombinedConfiguration
      hm ε α β p a hne)

/-- The same raw member, now carrying the proof that it belongs to the
genuine fibre of its canonical selector. -/
def r324RefinedRawSelectedConfigurationFiber
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a ≠ 0) :
    R324SelectedCrossSlotConfigurationFiber
      ρ ε α β
      (r324RefinedRawMomentContraction p a).1
      (r324RefinedRawMomentContraction p a).2.1
      (r324RefinedRawMomentContraction p a).2.2
      hexternal hε hε1 hmtrunc
      (ρ.r324RefinedRawSelectedResidualSlot
        hm ε α β hexternal hε hε1 hmtrunc p a hne) := by
  refine
    ⟨ρ.r324RefinedRawNonzeroCombinedConfiguration
      hm ε α β p a hne, ?_⟩
  simp [r324RefinedRawSelectedResidualSlot]

/-- The genuine selector-restricted signed physical core carried by one
endpoint-nonzero raw member. -/
def r324RefinedRawSelectorRestrictedSignedCore
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a ≠ 0)
    (v : Fin (2 * m) → T4) : ℂ :=
  ρ.r324SelectorRestrictedSignedInteriorMode
    ε α β
    (r324RefinedRawMomentContraction p a).1
    (r324RefinedRawMomentContraction p a).2.1
    (r324RefinedRawMomentContraction p a).2.2
    hexternal hε hε1 hmtrunc
    (ρ.r324RefinedRawSelectedResidualSlot
      hm ε α β hexternal hε hε1 hmtrunc p a hne)
    (ρ.r324RefinedRawSelectedConfigurationFiber
      hm ε α β hexternal hε hε1 hmtrunc p a hne)
    v

/-! ## Exact local selector representation -/

/-- Every endpoint-nonzero raw refined Fourier integrand is literally
its canonically selected high-mode physical integrand.  This is the
first point at which the existing selector bridge applies. -/
theorem r324RefinedRawEndpointIntegrand_eq_selectedHigh
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a ≠ 0)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ρ.r324RefinedRawEndpointIntegrand
        hm ε α β p a x y z w v =
      ρ.r324SelectedHighFullPairingFourierIntegrand
        ε α β
        (r324RefinedRawMomentContraction p a).1
        (r324RefinedRawMomentContraction p a).2.1
        (r324RefinedRawMomentContraction p a).2.2
        hexternal hε hε1 hmtrunc
        (ρ.r324RefinedRawNonzeroCombinedConfiguration
          hm ε α β p a hne)
        x y z w v := by
  rw [
    ρ.r324RefinedRawEndpointIntegrand_eq_fullPairing
      hm ε α β p a x y z w v]
  exact
    (ρ.r324SelectedHighFullPairingFourierIntegrand_eq
      ε α β
      (r324RefinedRawMomentContraction p a).1
      (r324RefinedRawMomentContraction p a).2.1
      (r324RefinedRawMomentContraction p a).2.2
      hexternal hε hε1 hmtrunc
      (ρ.r324RefinedRawNonzeroCombinedConfiguration
        hm ε α β p a hne)
      x y z w v).symm

/-- Endpoint-separated form of the preceding equality.  The supplied
core is the actual restricted signed physical mode, not an unrestricted
single-projected covariance product. -/
theorem
    r324RefinedRawEndpointIntegrand_eq_selectorRestrictedSigned
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a ≠ 0)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ρ.r324RefinedRawEndpointIntegrand
        hm ε α β p a x y z w v =
      r324EndpointSeparatedIntegrand α β
        (r324ContractionEndpointAnchors hm
          (r324RefinedRawMomentContraction p a) v)
        (r324ContractionEndpointFlags
          (r324RefinedRawMomentContraction p a))
        (ρ.r324RefinedRawSelectorRestrictedSignedCore
          hm ε α β hexternal hε hε1 hmtrunc
          p a hne v)
        x y z w := by
  rw [
    ρ.r324RefinedRawEndpointIntegrand_eq_selectedHigh
      hm ε α β hexternal hε hε1 hmtrunc
      p a hne x y z w v,
    ρ.r324SelectedHighFullPairingFourierIntegrand_eq_endpointSeparated
      hm ε α β
      (r324RefinedRawMomentContraction p a).1
      (r324RefinedRawMomentContraction p a).2.1
      (r324RefinedRawMomentContraction p a).2.2
      hexternal hε hε1 hmtrunc
      (ρ.r324RefinedRawNonzeroCombinedConfiguration
        hm ε α β p a hne)
      x y z w v]
  have he :
      r324SelectedMomentContraction
          (r324RefinedRawMomentContraction p a).1
          (r324RefinedRawMomentContraction p a).2.1
          (r324RefinedRawMomentContraction p a).2.2 =
        r324RefinedRawMomentContraction p a := by
    rcases h :
        r324RefinedRawMomentContraction p a with
      ⟨κp, κm, π⟩
    rfl
  rw [he]
  unfold r324RefinedRawSelectorRestrictedSignedCore
  have hcore :=
    ρ.r324SelectedEndpointCore_eq_selectorRestrictedSignedInteriorMode
      ε α β
      (r324RefinedRawMomentContraction p a).1
      (r324RefinedRawMomentContraction p a).2.1
      (r324RefinedRawMomentContraction p a).2.2
      hexternal hε hε1 hmtrunc
      (ρ.r324RefinedRawSelectedResidualSlot
        hm ε α β hexternal hε hε1 hmtrunc p a hne)
      (ρ.r324RefinedRawSelectedConfigurationFiber
        hm ε α β hexternal hε hε1 hmtrunc p a hne)
      v
  have hcore' :
      ρ.r324SelectedEndpointCore
          ε
          (r324RefinedRawMomentContraction p a).1
          (r324RefinedRawMomentContraction p a).2.1
          (r324RefinedRawMomentContraction p a).2.2
          (ρ.r324RefinedRawNonzeroCombinedConfiguration
            hm ε α β p a hne).1
          (ρ.r324RefinedRawSelectedResidualSlot
            hm ε α β hexternal hε hε1 hmtrunc p a hne)
          ‖z4EuclideanFrequency (α + β)‖ v =
        ρ.r324SelectorRestrictedSignedInteriorMode
          ε α β
          (r324RefinedRawMomentContraction p a).1
          (r324RefinedRawMomentContraction p a).2.1
          (r324RefinedRawMomentContraction p a).2.2
          hexternal hε hε1 hmtrunc
          (ρ.r324RefinedRawSelectedResidualSlot
            hm ε α β hexternal hε hε1 hmtrunc p a hne)
          (ρ.r324RefinedRawSelectedConfigurationFiber
            hm ε α β hexternal hε hε1 hmtrunc p a hne)
          v := by
    simpa only [
      r324RefinedRawSelectedResidualSlot,
      r324RefinedRawSelectedConfigurationFiber] using hcore
  have hselected :
      ρ.r324FirstLargeCrossSlotForNonzeroConfiguration
          ε α β
          (r324RefinedRawMomentContraction p a).1
          (r324RefinedRawMomentContraction p a).2.1
          (r324RefinedRawMomentContraction p a).2.2
          hexternal hε hε1 hmtrunc
          (ρ.r324RefinedRawNonzeroCombinedConfiguration
            hm ε α β p a hne) =
        ρ.r324RefinedRawSelectedResidualSlot
          hm ε α β hexternal hε hε1 hmtrunc
          p a hne := by
    rfl
  rw [hselected, hcore']

/-- Named physical integrand supplied by the exact local selector
representation. -/
def r324RefinedRawSelectorRestrictedPhysicalIntegrand
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a ≠ 0)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  r324EndpointSeparatedIntegrand α β
    (r324ContractionEndpointAnchors hm
      (r324RefinedRawMomentContraction p a) v)
    (r324ContractionEndpointFlags
      (r324RefinedRawMomentContraction p a))
    (ρ.r324RefinedRawSelectorRestrictedSignedCore
      hm ε α β hexternal hε hε1 hmtrunc
      p a hne v)
    x y z w

theorem r324RefinedRawEndpointIntegrand_eq_selectorPhysical
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a ≠ 0)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ρ.r324RefinedRawEndpointIntegrand
        hm ε α β p a x y z w v =
      ρ.r324RefinedRawSelectorRestrictedPhysicalIntegrand
        hm ε α β hexternal hε hε1 hmtrunc
        p a hne x y z w v := by
  exact
    ρ.r324RefinedRawEndpointIntegrand_eq_selectorRestrictedSigned
      hm ε α β hexternal hε hε1 hmtrunc
      p a hne x y z w v

theorem
    integrable_r324Flatten_refinedRawSelectorRestrictedPhysicalIntegrand
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a ≠ 0) :
    Integrable
      (r324Flatten
        (ρ.r324RefinedRawSelectorRestrictedPhysicalIntegrand
          hm ε α β hexternal hε hε1 hmtrunc
          p a hne))
      (r324PhysicalMeasure m) := by
  refine
    (ρ.integrable_r324Flatten_refinedRawEndpointIntegrand
      hm ε α β p a).congr ?_
  filter_upwards with q
  exact
    ρ.r324RefinedRawEndpointIntegrand_eq_selectorPhysical
      hm ε α β hexternal hε hε1 hmtrunc
      p a hne
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2

/-- Genuine five-group Fubini identity for the local
selector-restricted physical integrand. -/
theorem
    integral_r324Flatten_refinedRawSelectorRestrictedPhysical_eq_five
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a ≠ 0) :
    (∫ q,
      r324Flatten
        (ρ.r324RefinedRawSelectorRestrictedPhysicalIntegrand
          hm ε α β hexternal hε hε1 hmtrunc
          p a hne) q
      ∂(r324PhysicalMeasure m)) =
      ∫ x, ∫ y, ∫ z, ∫ w,
        ∫ v,
          ρ.r324RefinedRawSelectorRestrictedPhysicalIntegrand
            hm ε α β hexternal hε hε1 hmtrunc
            p a hne x y z w v
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure := by
  exact r324_integral_product_eq_five _
    (ρ.integrable_r324Flatten_refinedRawSelectorRestrictedPhysicalIntegrand
      hm ε α β hexternal hε hε1 hmtrunc p a hne)

/-- The physical integral of a raw refined member is exactly the
coefficient used to decide selector eligibility. -/
theorem
    integral_r324Flatten_refinedRawEndpointIntegrand_eq_rawFullPairingIntegral
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    (∫ q,
      r324Flatten
        (ρ.r324RefinedRawEndpointIntegrand
          hm ε α β p a) q
      ∂(r324PhysicalMeasure m)) =
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a := by
  unfold r324RefinedRawFullPairingIntegral
    r324FullPairingFourierIntegral
  apply integral_congr_ae
  filter_upwards with q
  exact
    ρ.r324RefinedRawEndpointIntegrand_eq_fullPairing
      hm ε α β p a
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2

/-- The selector-restricted physical representative has exactly the
same full physical integral as its original raw member. -/
theorem
    integral_r324Flatten_refinedRawSelectorPhysical_eq_rawFullPairingIntegral
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a ≠ 0) :
    (∫ q,
      r324Flatten
        (ρ.r324RefinedRawSelectorRestrictedPhysicalIntegrand
          hm ε α β hexternal hε hε1 hmtrunc
          p a hne) q
      ∂(r324PhysicalMeasure m)) =
      ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a := by
  calc
    (∫ q,
        r324Flatten
          (ρ.r324RefinedRawSelectorRestrictedPhysicalIntegrand
            hm ε α β hexternal hε hε1 hmtrunc
            p a hne) q
        ∂(r324PhysicalMeasure m)) =
        ∫ q,
          r324Flatten
            (ρ.r324RefinedRawEndpointIntegrand
              hm ε α β p a) q
          ∂(r324PhysicalMeasure m) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q =>
        (ρ.r324RefinedRawEndpointIntegrand_eq_selectorPhysical
          hm ε α β hexternal hε hε1 hmtrunc
          p a hne
          q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2).symm
    _ =
        ρ.r324RefinedRawFullPairingIntegral
          hm ε α β p a :=
      ρ.integral_r324Flatten_refinedRawEndpointIntegrand_eq_rawFullPairingIntegral
        hm ε α β p a

/-! ## The separate unrestricted marked-physical expansion -/

/-- Once an unrestricted single-projected residual core has genuinely
been constructed, the existing physical representation chain is exact:
it is the `tsum` of modes of the one marked residual covariance.

This theorem intentionally has no selector-fibre argument.  It must not
be used to identify a restricted selector series with the unrestricted
single-projected product. -/
theorem
    r324SingleProjectedResidualPhysicalInteriorCore_eq_tsum_markedModes
    {m : ℕ} {ε : ℝ} (hε : 0 < ε) (L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ρ.r324SingleProjectedResidualPhysicalInteriorCore
        ε L κp κm π selected v =
      ∑' k : Z4,
        ρ.r324MarkedResidualPhysicalInteriorModeTerm
          ε L κp κm π selected v k := by
  rw [
    ρ.r324SingleProjectedResidualPhysicalInteriorCore_eq_marked,
    ρ.r324MarkedResidualPhysicalInteriorCore_eq_tsum_modes
      hε]

/-! ## Exact selector-eligible / endpoint-null split of one key group -/

/-- Raw natural configurations sharing one complete increment key. -/
abbrev R324RefinedRawIncrementKeyFiber
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (b : ℕ) :=
  {a : ℕ //
    r324RefinedRawIncrementKey hm p a =
      r324NatEquivStandardConfigurations hm b}

/-- Members of one key fibre on which the canonical physical selector is
actually defined. -/
def r324RefinedRawEndpointNonzeroKeySet
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ) :
    Set (R324RefinedRawIncrementKeyFiber hm p b) :=
  {a |
    ρ.r324RefinedRawFullPairingIntegral
      hm ε α β p a.1 ≠ 0}

/-- Signed internal key core consisting only of endpoint-nonzero raw
members. -/
def r324RefinedRawSelectorEligibleKeyCore
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (v : Fin (2 * m) → T4) : ℂ :=
  ∑' a :
      ↥(ρ.r324RefinedRawEndpointNonzeroKeySet
        hm ε α β p b),
    ρ.r324RefinedRawEndpointCore hm ε p a.1.1 v

/-- The complementary signed internal key core.  Its full endpoint
integral vanishes termwise, but its pointwise internal values need not
vanish and therefore cannot be deleted after taking a norm. -/
def r324RefinedRawEndpointNullKeyCore
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (v : Fin (2 * m) → T4) : ℂ :=
  ∑' a :
      ↥((ρ.r324RefinedRawEndpointNonzeroKeySet
        hm ε α β p b)ᶜ),
    ρ.r324RefinedRawEndpointCore hm ε p a.1.1 v

/-- Sum of the genuine restricted physical integrals in the
selector-eligible part of one increment-key fibre. -/
def r324RefinedRawSelectorEligibleKeyPhysicalIntegral
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (b : ℕ) : ℂ :=
  ∑' a :
      ↥(ρ.r324RefinedRawEndpointNonzeroKeySet
        hm ε α β p b),
    ∫ q,
      r324Flatten
        (ρ.r324RefinedRawSelectorRestrictedPhysicalIntegrand
          hm ε α β hexternal hε hε1 hmtrunc
          p a.1.1 a.2) q
      ∂(r324PhysicalMeasure m)

/-- Exact key-fibre regrouping of the genuine selector-restricted
physical integrals. -/
theorem
    r324RefinedRawSelectorEligibleKeyPhysicalIntegral_eq_tsum_raw
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (hexternal : α + β ≠ 0)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (p : R324RefinedScheduleIndex m) (b : ℕ) :
    ρ.r324RefinedRawSelectorEligibleKeyPhysicalIntegral
        hm ε α β hexternal hε hε1 hmtrunc p b =
      ∑' a :
          ↥(ρ.r324RefinedRawEndpointNonzeroKeySet
            hm ε α β p b),
        ρ.r324RefinedRawFullPairingIntegral
          hm ε α β p a.1.1 := by
  unfold r324RefinedRawSelectorEligibleKeyPhysicalIntegral
  apply tsum_congr
  intro a
  exact
    ρ.integral_r324Flatten_refinedRawSelectorPhysical_eq_rawFullPairingIntegral
      hm ε α β hexternal hε hε1 hmtrunc
      p a.1.1 a.2

/-- Endpoint-null members vanish only after the complete physical
integration. -/
theorem
    integral_r324Flatten_refinedRawEndpointIntegrand_eq_zero_of_null
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (a :
      ↥((ρ.r324RefinedRawEndpointNonzeroKeySet
        hm ε α β p b)ᶜ)) :
    (∫ q,
      r324Flatten
        (ρ.r324RefinedRawEndpointIntegrand
          hm ε α β p a.1.1) q
      ∂(r324PhysicalMeasure m)) = 0 := by
  rw [
    ρ.integral_r324Flatten_refinedRawEndpointIntegrand_eq_rawFullPairingIntegral
      hm ε α β p a.1.1]
  have hnot :
      ¬ρ.r324RefinedRawFullPairingIntegral
        hm ε α β p a.1.1 ≠ 0 := by
    simpa only [
      r324RefinedRawEndpointNonzeroKeySet,
      Set.mem_compl_iff, Set.mem_setOf_eq] using a.2
  exact not_ne_iff.mp hnot

theorem summable_r324RefinedRawEndpointCore
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) :
    Summable
      (ρ.r324RefinedRawEndpointCore hm ε p · v) := by
  let e₀ := r324RefinedScheduleRepresentative p
  have hcov :=
    ρ.summable_r324RefinedRawCovarianceConfiguration
      hm hε p v
  unfold r324RefinedRawEndpointCore
  exact hcov.mul_left
    (r324RenormalizedInteriorCore e₀.1
        (fun i => v (leftMomentIndex i)) *
      r324RenormalizedInteriorCore e₀.2.1
        (fun i => v (rightMomentIndex i)))

/-- A full common-increment core is exactly the sum of its
selector-eligible and endpoint-null parts.  No triangle inequality is
used and the null part remains signed. -/
theorem r324KeyGroupedRefinedEndpointCore_eq_selectorEligible_add_null
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (v : Fin (2 * m) → T4) :
    ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v =
      ρ.r324RefinedRawSelectorEligibleKeyCore
          hm ε α β p b v +
        ρ.r324RefinedRawEndpointNullKeyCore
          hm ε α β p b v := by
  rw [
    ρ.r324KeyGroupedRefinedEndpointCore_eq_tsumByKey
      hm ε p b v]
  unfold tsumByKey
  have hkey :
      Summable fun
          a : R324RefinedRawIncrementKeyFiber hm p b =>
        ρ.r324RefinedRawEndpointCore hm ε p a.1 v :=
    (ρ.summable_r324RefinedRawEndpointCore
      hm hε p v).subtype _
  have hsplit :=
    hkey.tsum_subtype_add_tsum_subtype_compl
      (ρ.r324RefinedRawEndpointNonzeroKeySet
        hm ε α β p b)
  exact hsplit.symm

/-- Exact raw-density term after exposing the first missing physical
representation boundary.  The endpoint-null remainder is deliberately
inside the same norm as the selector-eligible core. -/
theorem r324RawCaseDensityTerm_eq_selectorEligible_add_null
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (i : Fin m) (cases : R324EndpointReductionPattern)
    (p : R324RefinedScheduleIndex m × ℕ)
    (v : Fin (2 * m) → T4) :
    ρ.r324RawCaseDensityTerm
        lam hm ε i cases p v =
      if r324RefinedEndpointReductionCase p.1 = cases then
        |lamEps lam ε| ^ (2 * m) *
          ‖ρ.r324RefinedRawSelectorEligibleKeyCore
              hm ε α β p.1 p.2 v +
            ρ.r324RefinedRawEndpointNullKeyCore
              hm ε α β p.1 p.2 v‖ *
          r324GroupedIncrementCost hm p.2 i
      else
        0 := by
  unfold r324RawCaseDensityTerm
  rw [
    ρ.r324KeyGroupedRefinedEndpointCore_eq_selectorEligible_add_null
      hm hε α β p.1 p.2 v]

/-- Patternwise raw density with the exact selector/null split exposed
under the original countable sum. -/
theorem r324RawCaseDensity_eq_tsum_selectorEligible_add_null
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (i : Fin m) (cases : R324EndpointReductionPattern)
    (v : Fin (2 * m) → T4) :
    ρ.r324RawCaseDensity lam hm ε i cases v =
      ∑' p : R324RefinedScheduleIndex m × ℕ,
        if r324RefinedEndpointReductionCase p.1 = cases then
          |lamEps lam ε| ^ (2 * m) *
            ‖ρ.r324RefinedRawSelectorEligibleKeyCore
                hm ε α β p.1 p.2 v +
              ρ.r324RefinedRawEndpointNullKeyCore
                hm ε α β p.1 p.2 v‖ *
            r324GroupedIncrementCost hm p.2 i
        else
          0 := by
  unfold r324RawCaseDensity
  apply tsum_congr
  intro p
  exact
    ρ.r324RawCaseDensityTerm_eq_selectorEligible_add_null
      lam hm hε α β i cases p v

/-- The preceding patternwise identity survives integration on the full
internal product space.  This is the exact Fubini boundary seen by the
raw case output; the endpoint-null core has not been removed. -/
theorem integral_r324RawCaseDensity_eq_integral_tsum_selector_add_null
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (i : Fin m) (cases : R324EndpointReductionPattern) :
    (∫ v,
      ρ.r324RawCaseDensity lam hm ε i cases v
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
      ∫ v,
        (∑' p : R324RefinedScheduleIndex m × ℕ,
          if r324RefinedEndpointReductionCase p.1 = cases then
            |lamEps lam ε| ^ (2 * m) *
              ‖ρ.r324RefinedRawSelectorEligibleKeyCore
                  hm ε α β p.1 p.2 v +
                ρ.r324RefinedRawEndpointNullKeyCore
                  hm ε α β p.1 p.2 v‖ *
              r324GroupedIncrementCost hm p.2 i
          else
            0)
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v =>
    ρ.r324RawCaseDensity_eq_tsum_selectorEligible_add_null
      lam hm hε α β i cases v

end SmoothCutoff

end

end Anderson4D
