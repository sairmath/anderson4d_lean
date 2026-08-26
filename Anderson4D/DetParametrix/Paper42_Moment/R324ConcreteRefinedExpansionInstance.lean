import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedFourierExpansionClosure

/-!
# Concrete exact refined Fourier expansion

This module instantiates the exact structural fields of
`R324ConcreteRefinedCoreExpansion` with the common-increment grouped
cores.  It contains no decay estimate and no target budget.
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

/-! ## The raw series is the genuine refined physical integral -/

/-- The raw endpoint cores sum exactly to the actual complete refined
core. -/
theorem tsum_r324RefinedRawEndpointCore
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) :
    (∑' a,
      ρ.r324RefinedRawEndpointCore
        hm ε p a v) =
      r324RefinedEndpointCore ρ ε m
        p.1.1 p.2.1
        (r324RefinedScheduleRepresentative p) v := by
  let e₀ := r324RefinedScheduleRepresentative p
  unfold r324RefinedRawEndpointCore
    r324RefinedEndpointCore
  change
    (∑' a,
      (r324RenormalizedInteriorCore e₀.1
          (fun i => v (leftMomentIndex i)) *
        r324RenormalizedInteriorCore e₀.2.1
          (fun i => v (rightMomentIndex i))) *
        ρ.r324RefinedRawCovarianceConfiguration
          hm ε p a v) =
      (r324RenormalizedInteriorCore e₀.1
          (fun i => v (leftMomentIndex i)) *
        r324RenormalizedInteriorCore e₀.2.1
          (fun i => v (rightMomentIndex i))) *
        ∑ e ∈ momentRefinedContractionFiber
            m p.1.1 p.2.1,
          (primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ)
  rw [tsum_mul_left]
  rw [ρ.tsum_r324RefinedRawCovarianceConfiguration
    hm hε p v]

/-- Endpoint separation commutes with an ordinary summable series of
cores. -/
theorem r324EndpointSeparatedIntegrand_tsum
    (α β : Z4) (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags)
    (core : ℕ → ℂ) (x y z w : T4) :
    r324EndpointSeparatedIntegrand α β anchors flags
        (∑' a, core a) x y z w =
      ∑' a,
        r324EndpointSeparatedIntegrand α β anchors flags
          (core a) x y z w := by
  unfold r324EndpointSeparatedIntegrand
  rw [tsum_mul_left]

/-- The genuine refined physical integrand is pointwise the complete raw
Fourier series. -/
theorem momentRefinedPhysicalIntegrand_eq_rawEndpoint_tsum
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    momentRefinedPhysicalIntegrand
        ρ ε m α β p.1.1 p.2.1 x y z w v =
      ∑' a,
        ρ.r324RefinedRawEndpointIntegrand
          hm ε α β p a x y z w v := by
  let e₀ := r324RefinedScheduleRepresentative p
  rw [momentRefinedPhysicalIntegrand_eq_endpointSeparated
    ρ ε m hm α β p.1.1 p.2.1 e₀
    (r324RefinedScheduleRepresentative_mem p)
    x y z w v]
  rw [← ρ.tsum_r324RefinedRawEndpointCore
    hm hε p v]
  exact
    r324EndpointSeparatedIntegrand_tsum
      α β
      (r324ContractionEndpointAnchors hm e₀ v)
      (r324ContractionEndpointFlags e₀)
      (ρ.r324RefinedRawEndpointCore hm ε p · v)
      x y z w

/-- The actual refined physical integral is exactly the raw refined
Fourier-integral series. -/
theorem r324RefinedPhysicalIntegral_eq_rawFourier_tsum
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    r324RefinedPhysicalIntegral ρ ε m α β p =
      ∑' a,
        ρ.r324RefinedRawFourierIntegral
          hm ε α β p a := by
  have hFint :
      ∀ a : ℕ,
        Integrable
          (r324Flatten
            (ρ.r324RefinedRawEndpointIntegrand
              hm ε α β p a))
          (r324PhysicalMeasure m) := fun a =>
    ρ.integrable_r324Flatten_refinedRawEndpointIntegrand
      hm ε α β p a
  have hFnorm :
      Summable fun a =>
        ∫ q,
          ‖r324Flatten
            (ρ.r324RefinedRawEndpointIntegrand
              hm ε α β p a) q‖
          ∂(r324PhysicalMeasure m) :=
    ρ.summable_r324RefinedRawEndpointL1
      hm hε α β p
  unfold r324RefinedPhysicalIntegral
  calc
    (∫ q,
      r324Flatten
        (momentRefinedPhysicalIntegrand
          ρ ε m α β p.1.1 p.2.1) q
      ∂(r324PhysicalMeasure m)) =
        ∫ q,
          ∑' a,
            r324Flatten
              (ρ.r324RefinedRawEndpointIntegrand
                hm ε α β p a) q
          ∂(r324PhysicalMeasure m) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q =>
        ρ.momentRefinedPhysicalIntegrand_eq_rawEndpoint_tsum
          hm hε α β p
          q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
    _ = ∑' a,
          ∫ q,
            r324Flatten
              (ρ.r324RefinedRawEndpointIntegrand
                hm ε α β p a) q
            ∂(r324PhysicalMeasure m) :=
      (integral_tsum_of_summable_integral_norm
        hFint hFnorm).symm
    _ = ∑' a,
          ρ.r324RefinedRawFourierIntegral
            hm ε α β p a := by
      rfl

/-! ## Regrouping the exact integrated series -/

/-- The grouped endpoint terms in one refined schedule are summable. -/
theorem summable_r324KeyGroupedEndpointConfigurationTerm
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    Summable fun b =>
      r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p)
        (ρ.r324KeyGroupedRefinedEndpointCore
          hm ε p b) := by
  have hkey :
      Summable fun k : Fin m → Z4 =>
        tsumByKey
          (ρ.r324RefinedRawFourierIntegral
            hm ε α β p)
          (r324RefinedRawIncrementKey hm p) k :=
    summable_tsumByKey _ _
      (ρ.summable_r324RefinedRawFourierIntegral
        hm hε α β p)
  have hnat :=
    hkey.comp_injective
      (r324NatEquivStandardConfigurations hm).injective
  have hscaled :=
    hnat.mul_left (lamEps lam ε ^ (2 * m) : ℂ)
  exact hscaled.congr fun b =>
    (ρ.r324GroupedEndpointConfigurationTerm_keyGrouped_eq_tsumByKey
      lam hm hε α β p b).symm

/-- Exact per-schedule Fubini/regrouping identity required by the concrete
refined expansion structure. -/
theorem r324RefinedPhysicalIntegral_eq_keyGroupedEndpoint_tsum
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    (lamEps lam ε ^ (2 * m) : ℂ) *
        r324RefinedPhysicalIntegral ρ ε m α β p =
      ∑' b,
        r324GroupedEndpointConfigurationTerm
          hm ρ lam ε α β
          (r324RefinedScheduleRepresentative p)
          (ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p b) := by
  let scalar : ℂ :=
    (lamEps lam ε ^ (2 * m) : ℂ)
  let raw : ℕ → ℂ :=
    ρ.r324RefinedRawFourierIntegral
      hm ε α β p
  let key : ℕ → (Fin m → Z4) :=
    r324RefinedRawIncrementKey hm p
  calc
    scalar *
        r324RefinedPhysicalIntegral ρ ε m α β p =
        scalar * ∑' a, raw a := by
      rw [ρ.r324RefinedPhysicalIntegral_eq_rawFourier_tsum
        hm hε α β p]
    _ = scalar *
        ∑' k : Fin m → Z4,
          tsumByKey raw key k := by
      rw [tsum_tsumByKey raw key
        (ρ.summable_r324RefinedRawFourierIntegral
          hm hε α β p)]
    _ = scalar *
        ∑' b : ℕ,
          tsumByKey raw key
            (r324NatEquivStandardConfigurations hm b) := by
      rw [(r324NatEquivStandardConfigurations hm).tsum_eq]
    _ = ∑' b : ℕ,
          scalar *
            tsumByKey raw key
              (r324NatEquivStandardConfigurations hm b) := by
      rw [tsum_mul_left]
    _ = ∑' b,
        r324GroupedEndpointConfigurationTerm
          hm ρ lam ε α β
          (r324RefinedScheduleRepresentative p)
          (ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p b) := by
      apply tsum_congr
      intro b
      exact
        (ρ.r324GroupedEndpointConfigurationTerm_keyGrouped_eq_tsumByKey
          lam hm hε α β p b).symm

/-! ## Frequency conservation and the concrete structure -/

/-- The raw refined integral is the existing natural full-pairing
Fourier term selected by its decoded contraction/configuration. -/
theorem r324RefinedRawFourierIntegral_eq_natFullPairingFourierTerm
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    ρ.r324RefinedRawFourierIntegral
        hm ε α β p a =
      let u := r324NatEquivRefinedContractionConfigurations p a
      let κ := momentContractionEquivFullPairing m u.1.1
      ρ.r324NatFullPairingFourierTerm
        hm ε α β κ u.2 := by
  unfold r324RefinedRawFourierIntegral
    r324NatFullPairingFourierTerm
    r324FullPairingFourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q =>
    ρ.r324RefinedRawEndpointIntegrand_eq_fullPairing
      hm ε α β p a
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2

/-- Every nonzero raw refined integral has the exact external increment
sum. -/
theorem sum_r324RefinedRawIncrementKey_eq_external_of_ne_zero
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (hne :
      ρ.r324RefinedRawFourierIntegral
        hm ε α β p a ≠ 0) :
    (∑ i,
      z4EuclideanFrequency
        (r324RefinedRawIncrementKey hm p a i)) =
      z4EuclideanFrequency (α + β) := by
  let u := r324NatEquivRefinedContractionConfigurations p a
  let κ := momentContractionEquivFullPairing m u.1.1
  have hnat :
      ρ.r324NatFullPairingFourierTerm
        hm ε α β κ u.2 ≠ 0 := by
    rw [←
      ρ.r324RefinedRawFourierIntegral_eq_natFullPairingFourierTerm
        hm ε α β p a]
    exact hne
  have hsum :=
    ρ.sum_r324NatFullPairingIncrement_eq_external_of_ne_zero
      hm ε α β κ u.2 hnat
  simpa only [
    z4EuclideanFrequency_r324RefinedRawIncrementKey]
    using hsum

/-- A nonzero grouped endpoint term contains a nonzero raw integral in
its common-increment fibre. -/
theorem exists_rawFourierIntegral_ne_zero_of_grouped_ne_zero
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (hne :
      r324GroupedEndpointConfigurationTerm
          hm ρ lam ε α β
          (r324RefinedScheduleRepresentative p)
          (ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p b) ≠ 0) :
    ∃ a : ℕ,
      r324RefinedRawIncrementKey hm p a =
          r324NatEquivStandardConfigurations hm b ∧
        ρ.r324RefinedRawFourierIntegral
          hm ε α β p a ≠ 0 := by
  let key : Fin m → Z4 :=
    r324NatEquivStandardConfigurations hm b
  let raw : ℕ → ℂ :=
    ρ.r324RefinedRawFourierIntegral hm ε α β p
  have hgroup :
      tsumByKey raw
          (r324RefinedRawIncrementKey hm p) key ≠ 0 := by
    intro hz
    apply hne
    rw [
      ρ.r324GroupedEndpointConfigurationTerm_keyGrouped_eq_tsumByKey
        lam hm hε α β p b,
      hz,
      mul_zero]
  let S :=
    {a : ℕ //
      r324RefinedRawIncrementKey hm p a = key}
  have hex : ∃ a : S, raw a.1 ≠ 0 := by
    by_contra hnone
    have hall : ∀ a : S, raw a.1 = 0 := by
      intro a
      by_contra ha
      exact hnone ⟨a, ha⟩
    apply hgroup
    unfold tsumByKey
    simp only [hall, tsum_zero]
  obtain ⟨a, ha⟩ := hex
  exact ⟨a.1, a.2, ha⟩

/-- Every nonzero common-increment group has the exact external
increment sum. -/
theorem sum_keyGroupedIncrement_eq_external_of_ne_zero
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (hne :
      r324GroupedEndpointConfigurationTerm
          hm ρ lam ε α β
          (r324RefinedScheduleRepresentative p)
          (ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p b) ≠ 0) :
    (∑ i,
      z4EuclideanFrequency
        (r324NatEquivStandardConfigurations hm b i)) =
      z4EuclideanFrequency (α + β) := by
  obtain ⟨a, hakey, hane⟩ :=
    ρ.exists_rawFourierIntegral_ne_zero_of_grouped_ne_zero
      lam hm hε α β p b hne
  calc
    (∑ i,
      z4EuclideanFrequency
        (r324NatEquivStandardConfigurations hm b i)) =
        ∑ i,
          z4EuclideanFrequency
            (r324RefinedRawIncrementKey hm p a i) := by
      rw [hakey]
    _ = z4EuclideanFrequency (α + β) :=
      ρ.sum_r324RefinedRawIncrementKey_eq_external_of_ne_zero
        hm ε α β p a hane

/-- Routed increment of one concrete group.  Nonzero terms use their
actual shared Fourier key.  A zero term uses a harmless delta route so
that frequency conservation remains unconditional. -/
def r324ConcreteRefinedIncrement
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m × ℕ)
    (i : Fin m) :
    EuclideanSpace ℝ (Fin dim) :=
  if r324GroupedEndpointConfigurationTerm
      hm ρ lam ε α β
      (r324RefinedScheduleRepresentative p.1)
      (ρ.r324KeyGroupedRefinedEndpointCore
        hm ε p.1 p.2) ≠ 0 then
    z4EuclideanFrequency
      (r324NatEquivStandardConfigurations hm p.2 i)
  else if i = ⟨0, hm⟩ then
    z4EuclideanFrequency (α + β)
  else 0

theorem sum_r324ConcreteRefinedIncrement
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m × ℕ) :
    (∑ i,
      ρ.r324ConcreteRefinedIncrement
        lam hm ε α β p i) =
      z4EuclideanFrequency (α + β) := by
  classical
  unfold r324ConcreteRefinedIncrement
  split_ifs with hterm
  · exact
      ρ.sum_keyGroupedIncrement_eq_external_of_ne_zero
        lam hm hε α β p.1 p.2 hterm
  · simp only [Finset.sum_ite_eq' Finset.univ
      (⟨0, hm⟩ : Fin m)
      (fun _ => z4EuclideanFrequency (α + β)),
      Finset.mem_univ, if_true]

/-- Summability over all refined schedules and grouped configurations. -/
theorem summable_all_r324KeyGroupedEndpointConfigurationTerm
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4) :
    Summable fun p : R324RefinedScheduleIndex m × ℕ =>
      r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p.1)
        (ρ.r324KeyGroupedRefinedEndpointCore
          hm ε p.1 p.2) := by
  apply Summable.of_norm
  rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
  constructor
  · intro p
    exact
      (ρ.summable_r324KeyGroupedEndpointConfigurationTerm
        lam hm hε α β p).norm
  · exact Summable.of_finite

/-- Fully concrete exact refined Fourier expansion.  The remaining
primitive-collapse/local-decay estimate is deliberately not a field of
this structure. -/
def r324ConcreteRefinedCoreExpansion
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (hmtrunc : m ≤ truncOrder ε)
    (α β : Z4) :
    R324ConcreteRefinedCoreExpansion
      ρ lam ε m hm α β where
  core := fun p b =>
    ρ.r324KeyGroupedRefinedEndpointCore
      hm ε p b
  summable_core := fun p v =>
    ρ.summable_r324KeyGroupedRefinedEndpointCore
      hm hε p v
  core_tsum_eq := fun p v =>
    (ρ.tsum_r324KeyGroupedRefinedEndpointCore
      hm hε p v).symm
  refinedIntegral_eq_tsum := fun p =>
    ρ.r324RefinedPhysicalIntegral_eq_keyGroupedEndpoint_tsum
      lam hm hε α β p
  summable_term :=
    ρ.summable_all_r324KeyGroupedEndpointConfigurationTerm
      lam hm hε α β
  incrementCount := fun _ => m
  increment := fun p =>
    ρ.r324ConcreteRefinedIncrement
      lam hm ε α β p
  incrementCount_pos := fun _ => hm
  incrementCount_le_trunc := fun _ => hmtrunc
  increment_sum := fun p =>
    ρ.sum_r324ConcreteRefinedIncrement
      lam hm hε α β p

end SmoothCutoff

end

end Anderson4D
