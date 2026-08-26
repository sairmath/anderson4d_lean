import Anderson4D.Parametrix.PairingMeasurability
import Anderson4D.Parametrix.MomentBounds

/-!
# Finite-pairing expansion of parametrix coefficients

The pointwise identity `parametrixP = ∑ κ, randRI κ` only becomes an
identity after the two external Bochner integrals once each summand is
integrable in the corresponding nested order.  This file records exactly
that minimal spatial condition and proves the finite-sum and expectation
algebra above it.  No singular-integral estimate is assumed implicitly.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ComplexConjugate
open scoped BigOperators

/-- The Fourier integrand belonging to one within-copy partial pairing. -/
def pmPairingFourierIntegrand
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m))
    (ω : M.Ω) (x y : T4) : ℂ :=
  charT4 α x * charT4 β y *
    (randRI M ρ lam ε m κ x y ω : ℂ)

/-- Minimal joint spatial hypothesis needed to move the finite pairing
sum through the two external integrals defining `pmCoeff`.

The product-space formulation is essential: it yields integrable sections
almost everywhere by Fubini without incorrectly requiring every fixed
Green-diagonal section to be integrable. -/
structure PairingCoefficientSpatialIntegrable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) : Prop where
  joint :
    ∀ (κ : PartialPairing (Fin m)),
      ∀ᵐ ω ∂(volume : Measure M.Ω),
      Integrable
        (fun p : T4 × T4 =>
          pmPairingFourierIntegrand
            M ρ lam ε m α β κ ω p.1 p.2)
        (paperMeasure.prod paperMeasure)

/-- One pairing coefficient is the nested integral of its named Fourier
integrand. -/
theorem pmPairingCoeff_eq_integral
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) (ω : M.Ω) :
    pmPairingCoeff M ρ lam ε m α β κ ω =
      ∫ x, ∫ y,
        pmPairingFourierIntegrand
          M ρ lam ε m α β κ ω x y
        ∂paperMeasure ∂paperMeasure :=
  rfl

/-- The coefficient of the finite pairing sum is the finite sum of the
individual pairing coefficients. -/
theorem pmCoeff_eq_sum_pmPairingCoeff
    {M : NoiseModel} {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (hspatial :
      PairingCoefficientSpatialIntegrable M ρ lam ε m α β) :
    pmCoeff M ρ lam ε m α β =ᵐ[
        (volume : Measure M.Ω)]
      fun ω =>
        ∑ κ : PartialPairing (Fin m),
          pmPairingCoeff M ρ lam ε m α β κ ω := by
  have hall :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ∀ κ : PartialPairing (Fin m),
          Integrable
            (fun p : T4 × T4 =>
              pmPairingFourierIntegrand
                M ρ lam ε m α β κ ω p.1 p.2)
            (paperMeasure.prod paperMeasure) :=
    Filter.eventually_all.2 hspatial.joint
  filter_upwards [hall] with ω hω
  unfold pmCoeff parametrixP
  change
    (∫ x, ∫ y,
        charT4 α x * charT4 β y *
          ((∑ κ : PartialPairing (Fin m),
            randRI M ρ lam ε m κ x y ω : ℝ) : ℂ)
        ∂paperMeasure ∂paperMeasure) =
      ∑ κ : PartialPairing (Fin m),
        ∫ x, ∫ y,
          pmPairingFourierIntegrand
            M ρ lam ε m α β κ ω x y
          ∂paperMeasure ∂paperMeasure
  calc
    (∫ x, ∫ y,
        charT4 α x * charT4 β y *
          ((∑ κ : PartialPairing (Fin m),
            randRI M ρ lam ε m κ x y ω : ℝ) : ℂ)
        ∂paperMeasure ∂paperMeasure) =
      ∫ x, ∫ y,
        ∑ κ : PartialPairing (Fin m),
          pmPairingFourierIntegrand
            M ρ lam ε m α β κ ω x y
        ∂paperMeasure ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with y
      rw [Complex.ofReal_sum, Finset.mul_sum]
      rfl
    _ =
      ∫ p : T4 × T4,
        ∑ κ : PartialPairing (Fin m),
          pmPairingFourierIntegrand
            M ρ lam ε m α β κ ω p.1 p.2
        ∂(paperMeasure.prod paperMeasure) := by
      symm
      rw [integral_prod]
      exact integrable_finsetSum Finset.univ
        (fun κ _hκ => hω κ)
    _ = ∑ κ : PartialPairing (Fin m),
        ∫ p : T4 × T4,
          pmPairingFourierIntegrand
            M ρ lam ε m α β κ ω p.1 p.2
          ∂(paperMeasure.prod paperMeasure) := by
      rw [integral_finsetSum]
      intro κ _hκ
      exact hω κ
    _ = ∑ κ : PartialPairing (Fin m),
        ∫ x, ∫ y,
          pmPairingFourierIntegrand
            M ρ lam ε m α β κ ω x y
          ∂paperMeasure ∂paperMeasure := by
      apply Finset.sum_congr rfl
      intro κ _hκ
      exact integral_prod _ (hω κ)

/-- Diagonal pairing-product integrability gives `L²` membership of one
pairing coefficient. -/
theorem memLp_pmPairingCoeff_of_pairingProduct_integrable
    {M : NoiseModel} {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (hprod :
      ∀ κp κm : PartialPairing (Fin m),
        Integrable
          (fun ω =>
            pmPairingCoeff M ρ lam ε m α β κp ω *
              conj (pmPairingCoeff M ρ lam ε m α β κm ω))
          (volume : Measure M.Ω))
    (κ : PartialPairing (Fin m)) :
    MemLp (pmPairingCoeff M ρ lam ε m α β κ) 2
      (volume : Measure M.Ω) := by
  rw [memLp_two_iff_integrable_sq_norm
    (M.aestronglyMeasurable_pmPairingCoeff
      ρ lam ε m α β κ)]
  have hp := (hprod κ κ).norm
  refine hp.congr ?_
  filter_upwards with ω
  simp [pow_two]

/-- The complete coefficient is in `L²` once the minimal spatial expansion
condition and all pairwise expectation integrability conditions hold. -/
theorem memLp_pmCoeff_of_pairingProduct_integrable
    {M : NoiseModel} {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (hspatial :
      PairingCoefficientSpatialIntegrable M ρ lam ε m α β)
    (hprod :
      ∀ κp κm : PartialPairing (Fin m),
        Integrable
          (fun ω =>
            pmPairingCoeff M ρ lam ε m α β κp ω *
              conj (pmPairingCoeff M ρ lam ε m α β κm ω))
          (volume : Measure M.Ω)) :
    MemLp (pmCoeff M ρ lam ε m α β) 2
      (volume : Measure M.Ω) := by
  have hsum :
      MemLp
        (fun ω =>
          ∑ κ : PartialPairing (Fin m),
            pmPairingCoeff M ρ lam ε m α β κ ω)
        2 (volume : Measure M.Ω) := by
    exact memLp_finsetSum Finset.univ
      (fun κ _hκ =>
        memLp_pmPairingCoeff_of_pairingProduct_integrable hprod κ)
  exact hsum.ae_eq
    (pmCoeff_eq_sum_pmPairingCoeff hspatial).symm

/-- Pure finite-sum expectation algebra: after coefficient expansion, the
squared norm expectation is the double sum of pairing-product
expectations.  No spatial Fubini exchange occurs in this theorem. -/
theorem integral_norm_sq_pmCoeff_eq_sum_pairingProducts
    {M : NoiseModel} {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (hspatial :
      PairingCoefficientSpatialIntegrable M ρ lam ε m α β)
    (hprod :
      ∀ κp κm : PartialPairing (Fin m),
        Integrable
          (fun ω =>
            pmPairingCoeff M ρ lam ε m α β κp ω *
              conj (pmPairingCoeff M ρ lam ε m α β κm ω))
          (volume : Measure M.Ω)) :
    ((∫ ω, ‖pmCoeff M ρ lam ε m α β ω‖ ^ 2
        ∂(volume : Measure M.Ω) : ℝ) : ℂ) =
      ∑ κp : PartialPairing (Fin m),
        ∑ κm : PartialPairing (Fin m),
          ∫ ω,
            pmPairingCoeff M ρ lam ε m α β κp ω *
              conj (pmPairingCoeff M ρ lam ε m α β κm ω)
            ∂(volume : Measure M.Ω) := by
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
        [pmCoeff_eq_sum_pmPairingCoeff hspatial] with
          ω hω
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
        exact hprod κp κm
      · intro κp _hκp
        exact integrable_finsetSum _ fun κm _ =>
          hprod κp κm

/-- Constructor for the full Fubini output that discharges its coefficient
expansion and measurability fields from explicit constructions.  The
remaining arguments are precisely the unresolved absolute-integrability,
spatial Fubini, and deterministic joint-integrability obligations. -/
theorem pmCoeffMomentFubiniOutput_of_spatial
    {M : NoiseModel} {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (hspatial :
      PairingCoefficientSpatialIntegrable M ρ lam ε m α β)
    (hprod :
      ∀ κp κm : PartialPairing (Fin m),
        Integrable
          (fun ω =>
            pmPairingCoeff M ρ lam ε m α β κp ω *
              conj (pmPairingCoeff M ρ lam ε m α β κm ω))
          (volume : Measure M.Ω))
    (hfubini :
      ∀ κp κm : PartialPairing (Fin m),
        (∫ ω,
            pmPairingCoeff M ρ lam ε m α β κp ω *
              conj (pmPairingCoeff M ρ lam ε m α β κm ω)
            ∂(volume : Measure M.Ω)) =
          expectedWickMomentPairingTerm
            M ρ lam ε m α β κp κm)
    (hjoint :
      ∀ (κp κm : PartialPairing (Fin m))
        (π : κp.singles ≃ κm.singles),
        Integrable
          (r324Flatten
            (deterministicMomentIntegrand
              ρ ε m α β κp κm π))
          (r324PhysicalMeasure m)) :
    PmCoeffMomentFubiniOutput M ρ lam ε m α β where
  coefficient_expansion :=
    pmCoeff_eq_sum_pmPairingCoeff hspatial
  pairingCoeff_aestronglyMeasurable :=
    M.aestronglyMeasurable_pmPairingCoeff ρ lam ε m α β
  pairingProduct_integrable := hprod
  pairingProduct_fubini := hfubini
  deterministic_joint_integrable := hjoint

end

end Anderson4D
