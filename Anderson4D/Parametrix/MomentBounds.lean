import Anderson4D.DetParametrix.Core.MomentReduction
import Anderson4D.DetParametrix.Paper42_Moment.R324PhysicalFiber
import Anderson4D.Probability.ComplexWickRegroup
import Anderson4D.Parametrix.WickAtBridge

/-!
# Probabilistic second-moment reduction for the parametrix coefficients

This file isolates the probabilistic content of Deng--Shen (3.24) from the
deterministic R-324 estimate.

There are two genuinely upstream analytic inputs:

* `WickAtSecondMomentLaw` is the specialization of P-wick to the two Wick
  products occurring in the two copies of the order-`m` kernel.  Its right
  side uses the exact `κp.singles ≃ κm.singles` representation consumed by
  `deterministicMomentPairingSum`.
* `PmCoeffMomentFubiniOutput` records only the Fubini/integrability output
  needed to flatten the square of the iterated, junk-totalized coefficient.
  In particular it does not contain a deterministic bound or the desired
  second-moment equality.

From those inputs we prove the exact identity

`E ‖pmCoeff m α β‖² = deterministicMomentPairingSum ρ λ ε m α β`,

with the real expectation coerced to `ℂ`.  The final theorems then consume
the existing P-3.5b-det interface and expose both `MemLp 2` and the squared
geometric form expected by `Main/GeometricTruncation.lean`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ComplexConjugate
open scoped BigOperators

/-- The contribution of one within-copy partial pairing to the Fourier
coefficient.  This is deliberately expressed with the already frozen
`randRI`, so the only operation hidden here is the two external integrals. -/
def pmPairingCoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) (ω : M.Ω) : ℂ :=
  ∫ x, ∫ y,
    charT4 α x * charT4 β y *
      (randRI M ρ lam ε m κ x y ω : ℂ)
    ∂paperMeasure ∂paperMeasure

/-- The two Wick factors evaluated on the left and right copies of the
doubled internal carrier. -/
def pairedWickProduct
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κp κm : PartialPairing (Fin m))
    (x y z w : T4) (v : Fin (2 * m) → T4) (ω : M.Ω) : ℝ :=
  wickAt M ρ ε κp
      (assemble x y fun i => v (leftMomentIndex i)) ω *
    wickAt M ρ ε κm
      (assemble z w fun i => v (rightMomentIndex i)) ω

/-- The random part of one doubled contraction after expectation, but before
the cross-single Wick contractions are expanded. -/
def expectedWickMomentIntegrand
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m))
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  charT4 α x * charT4 β y * charT4 (-α) z * charT4 (-β) w *
    (((detIntegrand ρ ε m κp
          (assemble x y fun i => v (leftMomentIndex i)) *
        detIntegrand ρ ε m κm
          (assemble z w fun i => v (rightMomentIndex i))) *
      ∫ ω, pairedWickProduct M ρ ε m κp κm x y z w v ω
        ∂(volume : Measure M.Ω) : ℝ) : ℂ)

/-- The flattened expected contribution of one pair `(κp, κm)`, including
the common coupling `λ_ε^(2m)`. -/
def expectedWickMomentPairingTerm
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m)) : ℂ :=
  (lamEps lam ε ^ (2 * m) : ℂ) *
    ∫ x, ∫ y, ∫ z, ∫ w,
      ∫ v : Fin (2 * m) → T4,
        expectedWickMomentIntegrand M ρ ε m α β κp κm x y z w v
        ∂(Measure.pi fun _ => paperMeasure)
      ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure

/-- A stronger nested-integrability condition.  It is useful for local
algebra but is not required by the public second-moment
interface: exceptional Green diagonals prevent constructing these fields
uniformly at every fixed outer point. -/
structure NestedMomentIntegrable {m : ℕ}
    (f : T4 → T4 → T4 → T4 → (Fin (2 * m) → T4) → ℂ) : Prop where
  internal : ∀ x y z w,
    Integrable (f x y z w) (Measure.pi fun _ => paperMeasure)
  w : ∀ x y z,
    Integrable
      (fun w =>
        ∫ v, f x y z w v ∂(Measure.pi fun _ => paperMeasure))
      paperMeasure
  z : ∀ x y,
    Integrable
      (fun z => ∫ w,
        ∫ v, f x y z w v ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure)
      paperMeasure
  y : ∀ x,
    Integrable
      (fun y => ∫ z, ∫ w,
        ∫ v, f x y z w v ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure)
      paperMeasure
  x :
    Integrable
      (fun x => ∫ y, ∫ z, ∫ w,
        ∫ v, f x y z w v ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure ∂paperMeasure)
      paperMeasure

/-- A finite sum may be moved through the frozen five-fold spatial integral
under the all-sections condition. -/
theorem integral_five_finsetSum
    {ι : Type*} {m : ℕ} (s : Finset ι)
    (f : ι → T4 → T4 → T4 → T4 → (Fin (2 * m) → T4) → ℂ)
    (hf : ∀ i ∈ s, NestedMomentIntegrable (f i)) :
    (∫ x, ∫ y, ∫ z, ∫ w,
        ∫ v, ∑ i ∈ s, f i x y z w v
          ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure) =
      ∑ i ∈ s, ∫ x, ∫ y, ∫ z, ∫ w,
        ∫ v, f i x y z w v
          ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure := by
  simp_rw [integral_finsetSum _ fun i hi => (hf i hi).internal _ _ _ _]
  simp_rw [integral_finsetSum _ fun i hi => (hf i hi).w _ _ _]
  simp_rw [integral_finsetSum _ fun i hi => (hf i hi).z _ _]
  simp_rw [integral_finsetSum _ fun i hi => (hf i hi).y _]
  exact integral_finsetSum _ fun i hi => (hf i hi).x

/-- Correct joint-product-space version of the preceding finite-sum
Fubini lemma.  It makes no assertion about exceptional fixed sections. -/
theorem integral_five_finsetSum_joint
    {ι : Type*} {m : ℕ} (s : Finset ι)
    (f : ι → T4 → T4 → T4 → T4 →
      (Fin (2 * m) → T4) → ℂ)
    (hf :
      ∀ i ∈ s,
        Integrable (r324Flatten (f i))
          (r324PhysicalMeasure m)) :
    (∫ x, ∫ y, ∫ z, ∫ w,
        ∫ v, ∑ i ∈ s, f i x y z w v
          ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure) =
      ∑ i ∈ s, ∫ x, ∫ y, ∫ z, ∫ w,
        ∫ v, f i x y z w v
          ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure := by
  let total :
      T4 → T4 → T4 → T4 →
        (Fin (2 * m) → T4) → ℂ :=
    fun x y z w v => ∑ i ∈ s, f i x y z w v
  have htotal :
      Integrable (r324Flatten total)
        (r324PhysicalMeasure m) := by
    change
      Integrable
        (fun p => ∑ i ∈ s, r324Flatten (f i) p)
        (r324PhysicalMeasure m)
    exact integrable_finsetSum s hf
  calc
    (∫ x, ∫ y, ∫ z, ∫ w,
        ∫ v, ∑ i ∈ s, f i x y z w v
          ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure) =
      ∫ p, r324Flatten total p
        ∂(r324PhysicalMeasure m) := by
          exact
            (r324_integral_product_eq_five
              total htotal).symm
    _ =
      ∑ i ∈ s,
        ∫ p, r324Flatten (f i) p
          ∂(r324PhysicalMeasure m) := by
            change
              (∫ p, ∑ i ∈ s,
                  r324Flatten (f i) p
                ∂(r324PhysicalMeasure m)) =
                _
            exact integral_finsetSum s hf
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact r324_integral_product_eq_five
        (f i) (hf i hi)

/-- **The missing P-wick specialization.**

This is strictly a noise-law statement: it has no Green kernels, spatial
integrals, Fourier characters, coupling constants, or target bounds.  The
expectation of the two Wick polynomials is the sum over bijections between
their single sets.  Unequal chaos orders give the empty `Equiv` sum. -/
structure WickAtSecondMomentLaw
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) : Prop where
  integrable :
    ∀ (κp κm : PartialPairing (Fin m)) (x y z w : T4)
      (v : Fin (2 * m) → T4),
      Integrable
        (pairedWickProduct M ρ ε m κp κm x y z w v)
        (volume : Measure M.Ω)
  expectation :
    ∀ (κp κm : PartialPairing (Fin m)) (x y z w : T4)
      (v : Fin (2 * m) → T4),
      (∫ ω, pairedWickProduct M ρ ε m κp κm x y z w v ω
          ∂(volume : Measure M.Ω)) =
        crossSinglesEquivCovarianceSum κp κm
          (fun i j =>
            ρ.etaEpsT4 ε
              (v (leftMomentIndex i.val) -
                v (rightMomentIndex j.val)))

/-- The right side of `WickAtSecondMomentLaw.expectation` is definitionally
the finite cross-contraction sum used by the deterministic moment kernel. -/
theorem crossSinglesEquivCovarianceSum_eq_momentCrossCovarianceSum
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κp κm : PartialPairing (Fin m))
    (v : Fin (2 * m) → T4) :
    crossSinglesEquivCovarianceSum κp κm
        (fun i j =>
          ρ.etaEpsT4 ε
            (v (leftMomentIndex i.val) -
              v (rightMomentIndex j.val))) =
      ∑ π : κp.singles ≃ κm.singles,
        momentCrossCovarianceProduct ρ ε m κp κm π v := by
  rfl

/-- Purely analytic output needed to flatten the square of `pmCoeff`.

The last field licenses the finite cross-contraction sum exchanges after
P-wick is applied.  No field mentions `deterministicMomentPairingSum`, its
norm, `deterministicMomentRHS`, or a second-moment bound. -/
structure PmCoeffMomentFubiniOutput
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) : Prop where
  coefficient_expansion :
    pmCoeff M ρ lam ε m α β =ᵐ[
        (volume : Measure M.Ω)]
      fun ω =>
        ∑ κ : PartialPairing (Fin m),
          pmPairingCoeff M ρ lam ε m α β κ ω
  pairingCoeff_aestronglyMeasurable :
    ∀ κ : PartialPairing (Fin m),
      AEStronglyMeasurable
        (pmPairingCoeff M ρ lam ε m α β κ)
        (volume : Measure M.Ω)
  pairingProduct_integrable :
    ∀ κp κm : PartialPairing (Fin m),
      Integrable
        (fun ω =>
          pmPairingCoeff M ρ lam ε m α β κp ω *
            conj (pmPairingCoeff M ρ lam ε m α β κm ω))
        (volume : Measure M.Ω)
  pairingProduct_fubini :
    ∀ κp κm : PartialPairing (Fin m),
      (∫ ω,
          pmPairingCoeff M ρ lam ε m α β κp ω *
            conj (pmPairingCoeff M ρ lam ε m α β κm ω)
          ∂(volume : Measure M.Ω)) =
        expectedWickMomentPairingTerm M ρ lam ε m α β κp κm
  deterministic_joint_integrable :
    ∀ (κp κm : PartialPairing (Fin m))
      (π : κp.singles ≃ κm.singles),
      Integrable
        (r324Flatten
          (deterministicMomentIntegrand
            ρ ε m α β κp κm π))
        (r324PhysicalMeasure m)

/-- P-wick turns one flattened random pairing term into the sum of all its
deterministic cross-single contractions. -/
theorem expectedWickMomentPairingTerm_eq_sum
    {M : NoiseModel} {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (hwick : WickAtSecondMomentLaw M ρ ε m)
    (hjoint :
      ∀ (κp κm : PartialPairing (Fin m))
        (π : κp.singles ≃ κm.singles),
        Integrable
          (r324Flatten
            (deterministicMomentIntegrand
              ρ ε m α β κp κm π))
          (r324PhysicalMeasure m))
    (κp κm : PartialPairing (Fin m)) :
    expectedWickMomentPairingTerm M ρ lam ε m α β κp κm =
      (lamEps lam ε ^ (2 * m) : ℂ) *
        ∑ π : κp.singles ≃ κm.singles,
          deterministicMomentPairingTerm ρ ε m α β κp κm π := by
  unfold expectedWickMomentPairingTerm
  congr 1
  calc
    (∫ x, ∫ y, ∫ z, ∫ w,
        ∫ v,
          expectedWickMomentIntegrand M ρ ε m α β κp κm x y z w v
          ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure) =
      ∫ x, ∫ y, ∫ z, ∫ w,
        ∫ v,
          ∑ π : κp.singles ≃ κm.singles,
            deterministicMomentIntegrand ρ ε m α β κp κm π x y z w v
          ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with y
      apply integral_congr_ae
      filter_upwards with z
      apply integral_congr_ae
      filter_upwards with w
      apply integral_congr_ae
      filter_upwards with v
      rw [expectedWickMomentIntegrand, hwick.expectation,
        crossSinglesEquivCovarianceSum_eq_momentCrossCovarianceSum]
      simp_rw [deterministicMomentIntegrand]
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.mul_sum]
      rw [Complex.ofReal_sum]
    _ = ∑ π : κp.singles ≃ κm.singles,
        deterministicMomentPairingTerm ρ ε m α β κp κm π := by
      rw [integral_five_finsetSum_joint Finset.univ
        (fun π =>
          deterministicMomentIntegrand ρ ε m α β κp κm π)]
      · rfl
      · intro π _hπ
        exact hjoint κp κm π

/-- Every single pairing coefficient is in `L²` once all pairwise products
in the Fubini output are integrable. -/
theorem PmCoeffMomentFubiniOutput.memLp_pairingCoeff
    {M : NoiseModel} {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (h : PmCoeffMomentFubiniOutput M ρ lam ε m α β)
    (κ : PartialPairing (Fin m)) :
    MemLp (pmPairingCoeff M ρ lam ε m α β κ) 2
      (volume : Measure M.Ω) := by
  rw [memLp_two_iff_integrable_sq_norm
    (h.pairingCoeff_aestronglyMeasurable κ)]
  have hp := (h.pairingProduct_integrable κ κ).norm
  refine hp.congr ?_
  filter_upwards with ω
  simp [pow_two]

/-- The complete coefficient is in `L²`; no `MemLp` premise is required by
the final P-3.5b theorem. -/
theorem PmCoeffMomentFubiniOutput.memLp_pmCoeff
    {M : NoiseModel} {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (h : PmCoeffMomentFubiniOutput M ρ lam ε m α β) :
    MemLp (pmCoeff M ρ lam ε m α β) 2
      (volume : Measure M.Ω) := by
  have hsum :
      MemLp
        (fun ω =>
          ∑ κ : PartialPairing (Fin m),
            pmPairingCoeff M ρ lam ε m α β κ ω)
        2 (volume : Measure M.Ω) := by
    exact memLp_finsetSum Finset.univ
      (fun κ _hκ => h.memLp_pairingCoeff κ)
  exact hsum.ae_eq
    h.coefficient_expansion.symm

/-- Exact complex-valued second-moment identity.  The left side is real but
is coerced to `ℂ` so that it can be identified without discarding the
Fourier phases in the deterministic pairing sum. -/
theorem integral_norm_sq_pmCoeff_eq_deterministicMomentPairingSum
    {M : NoiseModel} {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (hfubini : PmCoeffMomentFubiniOutput M ρ lam ε m α β)
    (hwick : WickAtSecondMomentLaw M ρ ε m) :
    ((∫ ω, ‖pmCoeff M ρ lam ε m α β ω‖ ^ 2
        ∂(volume : Measure M.Ω) : ℝ) : ℂ) =
      deterministicMomentPairingSum ρ lam ε m α β := by
  have hpairInt :
      ∀ κp κm : PartialPairing (Fin m),
        Integrable
          (fun ω =>
            pmPairingCoeff M ρ lam ε m α β κp ω *
              conj (pmPairingCoeff M ρ lam ε m α β κm ω))
          (volume : Measure M.Ω) :=
    hfubini.pairingProduct_integrable
  calc
    ((∫ ω, ‖pmCoeff M ρ lam ε m α β ω‖ ^ 2
        ∂(volume : Measure M.Ω) : ℝ) : ℂ) =
      ∫ ω, ((‖pmCoeff M ρ lam ε m α β ω‖ ^ 2 : ℝ) : ℂ)
        ∂(volume : Measure M.Ω) := by
      exact integral_complex_ofReal.symm
    _ =
      ∫ ω,
        pmCoeff M ρ lam ε m α β ω *
          conj (pmCoeff M ρ lam ε m α β ω)
        ∂(volume : Measure M.Ω) := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [Complex.mul_conj, Complex.sq_norm]
    _ = ∫ ω,
        (∑ κp : PartialPairing (Fin m),
          pmPairingCoeff M ρ lam ε m α β κp ω) *
        conj
          (∑ κm : PartialPairing (Fin m),
            pmPairingCoeff M ρ lam ε m α β κm ω)
        ∂(volume : Measure M.Ω) := by
      apply integral_congr_ae
      filter_upwards
        [hfubini.coefficient_expansion] with ω hω
      rw [hω]
    _ = ∫ ω,
        ∑ κp : PartialPairing (Fin m),
          ∑ κm : PartialPairing (Fin m),
            pmPairingCoeff M ρ lam ε m α β κp ω *
              conj (pmPairingCoeff M ρ lam ε m α β κm ω)
        ∂(volume : Measure M.Ω) := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro κp _hκp
      rw [Finset.mul_sum]
    _ = ∑ κp : PartialPairing (Fin m),
        ∑ κm : PartialPairing (Fin m),
          ∫ ω,
            pmPairingCoeff M ρ lam ε m α β κp ω *
              conj (pmPairingCoeff M ρ lam ε m α β κm ω)
            ∂(volume : Measure M.Ω) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro κp _hκp
        rw [integral_finsetSum]
        intro κm _hκm
        exact hpairInt κp κm
      · intro κp _hκp
        exact integrable_finsetSum _ fun κm _ => hpairInt κp κm
    _ = ∑ κp : PartialPairing (Fin m),
        ∑ κm : PartialPairing (Fin m),
          expectedWickMomentPairingTerm M ρ lam ε m α β κp κm := by
      apply Finset.sum_congr rfl
      intro κp _hκp
      apply Finset.sum_congr rfl
      intro κm _hκm
      exact hfubini.pairingProduct_fubini κp κm
    _ = ∑ κp : PartialPairing (Fin m),
        ∑ κm : PartialPairing (Fin m),
          (lamEps lam ε ^ (2 * m) : ℂ) *
            ∑ π : κp.singles ≃ κm.singles,
              deterministicMomentPairingTerm ρ ε m α β κp κm π := by
      apply Finset.sum_congr rfl
      intro κp _hκp
      apply Finset.sum_congr rfl
      intro κm _hκm
      exact expectedWickMomentPairingTerm_eq_sum hwick
        hfubini.deterministic_joint_integrable κp κm
    _ = deterministicMomentPairingSum ρ lam ε m α β := by
      rw [deterministicMomentPairingSum_eq_nested_terms]
      simp_rw [Finset.mul_sum]

/-- Real presentation of the exact second moment. -/
theorem integral_norm_sq_pmCoeff_eq_re_deterministicMomentPairingSum
    {M : NoiseModel} {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (hfubini : PmCoeffMomentFubiniOutput M ρ lam ε m α β)
    (hwick : WickAtSecondMomentLaw M ρ ε m) :
    (∫ ω, ‖pmCoeff M ρ lam ε m α β ω‖ ^ 2
        ∂(volume : Measure M.Ω)) =
      (deterministicMomentPairingSum ρ lam ε m α β).re := by
  exact congrArg Complex.re
    (integral_norm_sq_pmCoeff_eq_deterministicMomentPairingSum
      hfubini hwick)

/-- **P-3.5b / paper (3.24).**

Once the exact P-wick and Fubini outputs are available, the only numerical
premise is precisely the existing P-3.5b-det estimate on the frozen
deterministic pairing sum.  The conclusion simultaneously provides the
`MemLp 2` fact required downstream and the exact second absolute moment
bound. -/
theorem parametrix_coeff_memLp_and_second_moment_bound
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (hfubini : PmCoeffMomentFubiniOutput M ρ lam ε m α β)
    (hwick : WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        deterministicMomentRHS
          outerConstant powerConstant lam ε m α β) :
    MemLp (pmCoeff M ρ lam ε m α β) 2
        (volume : Measure M.Ω) ∧
      (∫ ω, ‖pmCoeff M ρ lam ε m α β ω‖ ^ 2
          ∂(volume : Measure M.Ω)) ≤
        deterministicMomentRHS
          outerConstant powerConstant lam ε m α β := by
  refine ⟨hfubini.memLp_pmCoeff, ?_⟩
  rw [integral_norm_sq_pmCoeff_eq_re_deterministicMomentPairingSum
    hfubini hwick]
  exact (Complex.re_le_norm _).trans hdet

/-- Blueprint endpoint P-3.5b. -/
theorem parametrix_coeff_bound
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (hfubini : PmCoeffMomentFubiniOutput M ρ lam ε m α β)
    (hwick : WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        deterministicMomentRHS
          outerConstant powerConstant lam ε m α β) :
    MemLp (pmCoeff M ρ lam ε m α β) 2
        (volume : Measure M.Ω) ∧
      (∫ ω, ‖pmCoeff M ρ lam ε m α β ω‖ ^ 2
          ∂(volume : Measure M.Ω)) ≤
        deterministicMomentRHS
          outerConstant powerConstant lam ε m α β :=
  parametrix_coeff_memLp_and_second_moment_bound hfubini hwick hdet

/-- **Complete orderwise (3.24) closure from the entity-level R-324
interfaces.**

The constants are chosen in the same order as in
`exists_deterministicMoment_bound_of_reductions`.  The only remaining
mathematical premises are the two strictly upstream deterministic reduction
outputs, the P-wick law, and the analytic Fubini output; no estimate is
assumed at the random level. -/
theorem exists_parametrix_coeff_bound_of_reductions
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
        (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| → 1 ≤ m →
        PmCoeffMomentFubiniOutput M ρ lam ε m α β →
        WickAtSecondMomentLaw M ρ ε m →
        MomentUniformReductionOutputAt ρ lam ε m α β
          primitiveConstant supportConstant →
        RoutedMomentReductionOutput ρ lam ε m α β
          (lamEps lam ε ^ 2 * outerConstant *
            (primitiveConstant * lam) ^ (2 * m - 2)) →
        MemLp (pmCoeff M ρ lam ε m α β) 2
            (volume : Measure M.Ω) ∧
          (∫ ω, ‖pmCoeff M ρ lam ε m α β ω‖ ^ 2
              ∂(volume : Measure M.Ω)) ≤
            deterministicMomentRHS outerConstant primitiveConstant
              lam ε m α β := by
  obtain ⟨outerConstant, houter, hdet⟩ :=
    exists_deterministicMoment_bound_of_reductions
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro M ρ lam ε m α β hε hεsmall hlog hm
    hfubini hwick huniform hrouted
  exact parametrix_coeff_memLp_and_second_moment_bound
    hfubini hwick
      (hdet ρ lam ε m α β hε hεsmall hlog hm
        huniform hrouted)

/-- The deterministic right side of (3.24) is bounded by the square of its
natural geometric `L²` scale.  This is the normalization expected by the
second-moment adapter in `Main/GeometricTruncation.lean`. -/
theorem deterministicMomentRHS_le_geometric_sq
    {outerConstant powerConstant lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hm : 1 ≤ m) :
    deterministicMomentRHS
        outerConstant powerConstant lam ε m α β ≤
      (‖(lamEps lam ε : ℂ)‖ * Real.sqrt outerConstant *
        (powerConstant * lam) ^ (m - 1)) ^ 2 := by
  have hq : 0 ≤ powerConstant * lam :=
    mul_nonneg hpower hlam
  have hmin :
      min 1 (deterministicMomentDecay ε α β) ≤ 1 :=
    min_le_left _ _
  have hexp : 2 * m - 2 = 2 * (m - 1) := by omega
  unfold deterministicMomentRHS
  calc
    lamEps lam ε ^ 2 * outerConstant *
          (powerConstant * lam) ^ (2 * m - 2) *
          min 1 (deterministicMomentDecay ε α β)
        ≤ lamEps lam ε ^ 2 * outerConstant *
          (powerConstant * lam) ^ (2 * m - 2) := by
      exact mul_le_of_le_one_right
        (mul_nonneg
          (mul_nonneg (sq_nonneg _) houter)
          (pow_nonneg hq _))
        hmin
    _ = (‖(lamEps lam ε : ℂ)‖ * Real.sqrt outerConstant *
          (powerConstant * lam) ^ (m - 1)) ^ 2 := by
      rw [hexp]
      have hpow :
          (powerConstant * lam) ^ (2 * (m - 1)) =
            ((powerConstant * lam) ^ (m - 1)) ^ 2 := by
        rw [show 2 * (m - 1) = (m - 1) * 2 by omega, ← pow_mul]
      have hsqrt :
          Real.sqrt outerConstant ^ 2 = outerConstant :=
        Real.sq_sqrt houter
      have hlamNorm :
          ‖(lamEps lam ε : ℂ)‖ ^ 2 = lamEps lam ε ^ 2 := by
        simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [hpow]
      calc
        lamEps lam ε ^ 2 * outerConstant *
              ((powerConstant * lam) ^ (m - 1)) ^ 2 =
            ‖(lamEps lam ε : ℂ)‖ ^ 2 *
              Real.sqrt outerConstant ^ 2 *
              ((powerConstant * lam) ^ (m - 1)) ^ 2 := by
          rw [hlamNorm, hsqrt]
        _ = (‖(lamEps lam ε : ℂ)‖ * Real.sqrt outerConstant *
              (powerConstant * lam) ^ (m - 1)) ^ 2 := by
          ring

/-- Directly consumable squared form of (3.24).  Taking
`K = sqrt outerConstant` and `q = powerConstant * lam` gives exactly the
premise shape of
`Prop36.tendsto_fullParametrixChar_of_geometric_second_moment_bound`. -/
theorem parametrix_coeff_geometric_second_moment_bound
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (hfubini : PmCoeffMomentFubiniOutput M ρ lam ε m α β)
    (hwick : WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        deterministicMomentRHS
          outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hm : 1 ≤ m) :
    MemLp (pmCoeff M ρ lam ε m α β) 2
        (volume : Measure M.Ω) ∧
      (∫ ω, ‖pmCoeff M ρ lam ε m α β ω‖ ^ 2
          ∂(volume : Measure M.Ω)) ≤
        (‖(lamEps lam ε : ℂ)‖ * Real.sqrt outerConstant *
          (powerConstant * lam) ^ (m - 1)) ^ 2 := by
  have hbase :=
    parametrix_coeff_memLp_and_second_moment_bound
      hfubini hwick hdet
  exact ⟨hbase.1, hbase.2.trans
    (deterministicMomentRHS_le_geometric_sq
      houter hpower hlam hm)⟩

end

end Anderson4D
