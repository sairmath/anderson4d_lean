import Anderson4D.DetParametrix.Paper42_Moment.R324ConcreteRoutingClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324NatCovarianceConfigurations

/-!
# Fourier expansion of a residual-refined R-324 core

For one realized residual schedule, the primitive-pairing fibre remains
inside the core.  We first enumerate its finite contraction fibre times
the absolutely convergent covariance configurations.  We then group that
series by the common `Fin m → ℤ⁴` vector of signed left-translation
increments.  Thus every final grouped term has one shared increment list,
while the primitive fibre sum is formed before taking a norm.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## Enumerating one finite refined fibre times its configurations -/

abbrev R324RefinedContractionIndex
    {m : ℕ} (p : R324RefinedScheduleIndex m) :=
  {e : MomentContraction m //
    e ∈ momentRefinedContractionFiber m p.1.1 p.2.1}

theorem r324RefinedContractionIndex_nonempty
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    Nonempty (R324RefinedContractionIndex p) := by
  obtain ⟨e, he, her⟩ :=
    Finset.mem_image.mp p.2.2
  refine ⟨⟨e, ?_⟩⟩
  exact mem_momentRefinedContractionFiber.mpr
    ⟨mem_momentContractionFiber.mp he, her⟩

/-- Natural enumeration of a refined contraction entity together with
one natural-number covariance configuration. -/
def r324NatEquivRefinedContractionConfigurations
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    ℕ ≃ R324RefinedContractionIndex p × ℕ := by
  classical
  letI : Nonempty (R324RefinedContractionIndex p) :=
    r324RefinedContractionIndex_nonempty p
  letI : Encodable (R324RefinedContractionIndex p) :=
    Fintype.toEncodable _
  letI : Denumerable
      (R324RefinedContractionIndex p × ℕ) :=
    Denumerable.ofEncodableOfInfinite _
  exact
    (Denumerable.eqv
      (R324RefinedContractionIndex p × ℕ)).symm

/-- One raw covariance Fourier configuration in a refined fibre. -/
def r324RefinedRawCovarianceConfiguration
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (v : Fin (2 * m) → T4) : ℂ :=
  let u := r324NatEquivRefinedContractionConfigurations p a
  let κ := momentContractionEquivFullPairing m u.1.1
  ρ.r324NatCovarianceConfigurationTerm
    hm ε κ u.2 v

/-- Shared lattice increment key of a raw refined configuration. -/
def r324RefinedRawIncrementKey
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    Fin m → Z4 :=
  let u := r324NatEquivRefinedContractionConfigurations p a
  let κ := momentContractionEquivFullPairing m u.1.1
  r324NatCovarianceIncrementKey hm κ u.2

@[simp]
theorem z4EuclideanFrequency_r324RefinedRawIncrementKey
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ)
    (i : Fin m) :
    z4EuclideanFrequency
        (r324RefinedRawIncrementKey hm p a i) =
      let u := r324NatEquivRefinedContractionConfigurations p a
      let κ := momentContractionEquivFullPairing m u.1.1
      r324NatFullPairingIncrement hm κ u.2 i := by
  rfl

theorem summable_norm_r324RefinedRawCovarianceConfiguration
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) :
    Summable fun a =>
      ‖ρ.r324RefinedRawCovarianceConfiguration
        hm ε p a v‖ := by
  let f :
      R324RefinedContractionIndex p × ℕ → ℝ := fun u =>
    let κ := momentContractionEquivFullPairing m u.1.1
    ‖ρ.r324NatCovarianceConfigurationTerm
      hm ε κ u.2 v‖
  have hf : Summable f := by
    rw [summable_prod_of_nonneg (fun u => norm_nonneg _)]
    constructor
    · intro e
      let κ := momentContractionEquivFullPairing m e.1
      exact
        ρ.summable_norm_r324NatCovarianceConfigurationTerm
          hm hε κ v
    · exact Summable.of_finite
  have hpre :=
    ((r324NatEquivRefinedContractionConfigurations p).summable_iff).2
      hf
  exact hpre.congr fun a => by rfl

theorem summable_r324RefinedRawCovarianceConfiguration
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) :
    Summable
      (ρ.r324RefinedRawCovarianceConfiguration
        hm ε p · v) :=
  Summable.of_norm
    (ρ.summable_norm_r324RefinedRawCovarianceConfiguration
      hm hε p v)

/-- The natural configurations attached to one fixed contraction in a
refined fibre sum to its complete covariance product. -/
private theorem tsum_r324RefinedConfigurationAt
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    {p : R324RefinedScheduleIndex m}
    (e : R324RefinedContractionIndex p)
    (v : Fin (2 * m) → T4) :
    (∑' a,
      ρ.r324NatCovarianceConfigurationTerm
        hm ε
        (momentContractionEquivFullPairing m e.1)
        a v) =
      (primitiveCovarianceProduct ρ ε m
        (momentCombinedPairing e.1.1
          e.1.2.1 e.1.2.2) v : ℂ) := by
  let κ := momentContractionEquivFullPairing m e.1
  calc
    (∑' a,
      ρ.r324NatCovarianceConfigurationTerm
        hm ε κ a v) =
        (primitiveCovarianceProduct
          ρ ε m κ.1 v : ℂ) :=
      ρ.tsum_r324NatCovarianceConfigurationTerm
        hm hε κ v
    _ = (primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing e.1.1
            e.1.2.1 e.1.2.2) v : ℂ) := by
      rfl

/-- The raw natural series is exactly the covariance-product sum of the
whole refined contraction fibre. -/
theorem tsum_r324RefinedRawCovarianceConfiguration
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) :
    (∑' a,
      ρ.r324RefinedRawCovarianceConfiguration
        hm ε p a v) =
      ∑ e ∈ momentRefinedContractionFiber m p.1.1 p.2.1,
        (primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ) := by
  let f :
      R324RefinedContractionIndex p × ℕ → ℂ := fun u =>
    let κ := momentContractionEquivFullPairing m u.1.1
    ρ.r324NatCovarianceConfigurationTerm
      hm ε κ u.2 v
  have hf : Summable f := by
    apply Summable.of_norm
    rw [summable_prod_of_nonneg (fun u => norm_nonneg _)]
    constructor
    · intro e
      exact
        ρ.summable_norm_r324NatCovarianceConfigurationTerm
          hm hε
          (momentContractionEquivFullPairing m e.1) v
    · exact Summable.of_finite
  calc
    (∑' a,
      ρ.r324RefinedRawCovarianceConfiguration
        hm ε p a v) =
        ∑' u : R324RefinedContractionIndex p × ℕ,
          f u := by
      exact
        (r324NatEquivRefinedContractionConfigurations p).tsum_eq
          f
    _ = ∑' e : R324RefinedContractionIndex p,
          ∑' a : ℕ, f (e, a) :=
      hf.tsum_prod
    _ = ∑ e : R324RefinedContractionIndex p,
          (primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing e.1.1
              e.1.2.1 e.1.2.2) v : ℂ) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro e _he
      exact
        ρ.tsum_r324RefinedConfigurationAt
          hm hε e v
    _ = ∑ e ∈ momentRefinedContractionFiber m p.1.1 p.2.1,
          (primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ) := by
      rw [←
        (momentRefinedContractionFiber m p.1.1 p.2.1).sum_attach,
        Finset.attach_eq_univ]

/-! ## General summable grouping by a shared key -/

/-- Fibrewise `tsum` of a summable series under an arbitrary key map. -/
def tsumByKey
    {A K : Type*} [AddCommMonoid A] [TopologicalSpace A]
    (f : ℕ → A) (key : ℕ → K) (k : K) : A :=
  ∑' a : {a : ℕ // key a = k}, f a.1

theorem summable_tsumByKey
    {A K : Type*} [NormedAddCommGroup A] [CompleteSpace A]
    (f : ℕ → A) (key : ℕ → K)
    (hf : Summable f) :
    Summable (tsumByKey f key) := by
  exact (hf.hasSum.tsum_fiberwise key).summable

theorem tsum_tsumByKey
    {A K : Type*} [NormedAddCommGroup A] [CompleteSpace A]
    (f : ℕ → A) (key : ℕ → K)
    (hf : Summable f) :
    (∑' k, tsumByKey f key k) = ∑' a, f a := by
  exact (hf.hasSum.tsum_fiberwise key).tsum_eq

/-! ## Increment-key grouped refined cores -/

/-- Covariance configurations in a refined fibre, grouped by a common
signed left-increment vector. -/
def r324KeyGroupedCovarianceConfiguration
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (v : Fin (2 * m) → T4) : ℂ :=
  tsumByKey
    (ρ.r324RefinedRawCovarianceConfiguration hm ε p · v)
    (r324RefinedRawIncrementKey hm p)
    (r324NatEquivStandardConfigurations hm b)

theorem summable_r324KeyGroupedCovarianceConfiguration
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) :
    Summable fun b =>
      ρ.r324KeyGroupedCovarianceConfiguration hm ε p b v := by
  have hkey :
      Summable fun k : Fin m → Z4 =>
        tsumByKey
          (ρ.r324RefinedRawCovarianceConfiguration hm ε p · v)
          (r324RefinedRawIncrementKey hm p) k :=
    summable_tsumByKey _ _
      (ρ.summable_r324RefinedRawCovarianceConfiguration
        hm hε p v)
  exact
    ((r324NatEquivStandardConfigurations hm).summable_iff).2
      hkey

theorem tsum_r324KeyGroupedCovarianceConfiguration
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) :
    (∑' b,
      ρ.r324KeyGroupedCovarianceConfiguration
        hm ε p b v) =
      ∑ e ∈ momentRefinedContractionFiber m p.1.1 p.2.1,
        (primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ) := by
  calc
    (∑' b,
      ρ.r324KeyGroupedCovarianceConfiguration
        hm ε p b v) =
        ∑' k : Fin m → Z4,
          tsumByKey
            (ρ.r324RefinedRawCovarianceConfiguration hm ε p · v)
            (r324RefinedRawIncrementKey hm p) k := by
      exact
        (r324NatEquivStandardConfigurations hm).tsum_eq
          (fun k : Fin m → Z4 =>
            tsumByKey
              (ρ.r324RefinedRawCovarianceConfiguration hm ε p · v)
              (r324RefinedRawIncrementKey hm p) k)
    _ = ∑' a,
          ρ.r324RefinedRawCovarianceConfiguration
            hm ε p a v :=
      tsum_tsumByKey _ _
        (ρ.summable_r324RefinedRawCovarianceConfiguration
          hm hε p v)
    _ = _ :=
      ρ.tsum_r324RefinedRawCovarianceConfiguration
        hm hε p v

/-- Full grouped internal core: the common interior Green factors times
the covariance configurations sharing one increment vector. -/
def r324KeyGroupedRefinedEndpointCore
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (v : Fin (2 * m) → T4) : ℂ :=
  let e₀ := r324RefinedScheduleRepresentative p
  r324RenormalizedInteriorCore e₀.1
      (fun i => v (leftMomentIndex i)) *
    r324RenormalizedInteriorCore e₀.2.1
      (fun i => v (rightMomentIndex i)) *
    ρ.r324KeyGroupedCovarianceConfiguration hm ε p b v

theorem summable_r324KeyGroupedRefinedEndpointCore
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) :
    Summable fun b =>
      ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v := by
  let e₀ := r324RefinedScheduleRepresentative p
  exact
    (ρ.summable_r324KeyGroupedCovarianceConfiguration
      hm hε p v).mul_left
      (r324RenormalizedInteriorCore e₀.1
          (fun i => v (leftMomentIndex i)) *
        r324RenormalizedInteriorCore e₀.2.1
          (fun i => v (rightMomentIndex i)))

theorem tsum_r324KeyGroupedRefinedEndpointCore
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) :
    (∑' b,
      ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v) =
      r324RefinedEndpointCore ρ ε m
        p.1.1 p.2.1
        (r324RefinedScheduleRepresentative p) v := by
  let e₀ := r324RefinedScheduleRepresentative p
  unfold r324KeyGroupedRefinedEndpointCore
    r324RefinedEndpointCore
  change
    (∑' b,
      (r324RenormalizedInteriorCore e₀.1
          (fun i => v (leftMomentIndex i)) *
        r324RenormalizedInteriorCore e₀.2.1
          (fun i => v (rightMomentIndex i))) *
        ρ.r324KeyGroupedCovarianceConfiguration
          hm ε p b v) =
      (r324RenormalizedInteriorCore e₀.1
          (fun i => v (leftMomentIndex i)) *
        r324RenormalizedInteriorCore e₀.2.1
          (fun i => v (rightMomentIndex i))) *
        ∑ e ∈ momentRefinedContractionFiber
            m p.1.1 p.2.1,
          (primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ)
  rw [tsum_mul_left]
  rw [ρ.tsum_r324KeyGroupedCovarianceConfiguration
    hm hε p v]

end SmoothCutoff

end

end Anderson4D
