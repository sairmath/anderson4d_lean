import Anderson4D.DetParametrix.Paper42_Moment.R324DetIntegrability
import Anderson4D.Parametrix.PairingMomentClosure

/-!
# Global integrability of random pairing profiles

At positive mollification scale, every deterministic pairing profile is
jointly integrable in both endpoints and all internal variables.  On a
continuous noise sample its Wick factor is uniformly bounded, so the full
random pairing profile is jointly integrable as well.  This is the global
analytic input needed to turn the pointwise ledgers in Proposition 3.4 into
almost-everywhere endpoint statements.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- On every continuous mollified-noise sample, one complete random
pairing profile is jointly integrable in both external endpoints and all
internal variables. -/
theorem NoiseModel.integrable_randIntegrand_flat
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (κ : PartialPairing (Fin m))
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    Integrable
      (fun p : PairingHalfPhysicalPoint m =>
        (randIntegrand M ρ ε κ
          (assemble p.1 p.2.1 p.2.2) ω : ℂ))
      (pairingHalfPhysicalMeasure m) := by
  obtain ⟨B, hB0, hwickBound⟩ :=
    M.exists_uniform_norm_wickAt_bound_of_continuous
      ρ hε hε1 κ ω hξ
  let wickWeight : PairingHalfPhysicalPoint m → ℂ :=
    fun p =>
      (wickAt M ρ ε κ
        (pairingHalfFixedTupleMap M m ω p).2
        (pairingHalfFixedTupleMap M m ω p).1 : ℂ)
  have hwickMeas :
      AEStronglyMeasurable wickWeight
        (pairingHalfPhysicalMeasure m) := by
    apply Measurable.aestronglyMeasurable
    exact
      Complex.measurable_ofReal.comp
        ((M.measurable_wickAt_joint ρ ε κ).comp
          (measurable_pairingHalfFixedTupleMap M m ω))
  have hwickBound' :
      ∀ᵐ p ∂(pairingHalfPhysicalMeasure m),
        ‖wickWeight p‖ ≤ B :=
    Filter.Eventually.of_forall fun p => by
      unfold wickWeight pairingHalfFixedTupleMap
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hwickBound _
  have hproduct :=
    (integrable_detIntegrand_flat ρ hε hε1 κ).mul_bdd
      hwickMeas hwickBound'
  have hproduct' :
      Integrable
        (fun p : PairingHalfPhysicalPoint m =>
          (detIntegrand ρ ε m κ
            (assemble p.1 p.2.1 p.2.2) : ℂ) *
              wickWeight p)
        (pairingHalfPhysicalMeasure m) := by
    simpa only [pairingHalfPhysicalMeasure] using hproduct
  refine hproduct'.congr ?_
  filter_upwards with p
  unfold randIntegrand wickWeight pairingHalfFixedTupleMap
  push_cast
  ring

/-- Global integrability supplies the correct almost-everywhere
fixed-endpoint internal-integrability statement.  No assertion is made on
the exceptional endpoint diagonal. -/
theorem NoiseModel.ae_ae_integrable_randIntegrand
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (κ : PartialPairing (Fin m))
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      Integrable
        (fun v : Fin m → T4 =>
          (randIntegrand M ρ ε κ
            (assemble x y v) ω : ℂ))
        (Measure.pi fun _ : Fin m => paperMeasure) := by
  have hglobal :=
    M.integrable_randIntegrand_flat
      ρ hε hε1 m κ ω hξ
  unfold pairingHalfPhysicalMeasure at hglobal
  filter_upwards [hglobal.prod_right_ae] with x hx
  exact hx.prod_right_ae

/-- The preceding endpoint statement holds simultaneously for the finite
family of all partial pairings at a fixed order. -/
theorem NoiseModel.ae_ae_integrable_randIntegrand_all
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      ∀ κ : PartialPairing (Fin m),
        Integrable
          (fun v : Fin m → T4 =>
            (randIntegrand M ρ ε κ
              (assemble x y v) ω : ℂ))
          (Measure.pi fun _ : Fin m => paperMeasure) := by
  have hallX :
      ∀ᵐ x ∂paperMeasure,
        ∀ κ : PartialPairing (Fin m),
          ∀ᵐ y ∂paperMeasure,
            Integrable
              (fun v : Fin m → T4 =>
                (randIntegrand M ρ ε κ
                  (assemble x y v) ω : ℂ))
              (Measure.pi fun _ : Fin m => paperMeasure) :=
    Filter.eventually_all.2 fun κ =>
      M.ae_ae_integrable_randIntegrand
        ρ hε hε1 m κ ω hξ
  filter_upwards [hallX] with x hx
  exact Filter.eventually_all.2 fun κ => hx κ

end

end Anderson4D
