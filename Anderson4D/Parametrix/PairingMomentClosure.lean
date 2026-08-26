import Anderson4D.Parametrix.PairingCoefficientExpansion
import Anderson4D.Parametrix.PairingMomentFubini

/-!
# Closing the analytic interfaces in the parametrix second moment

The low-level noise--space Fubini theorem reduces the random calculation to
deterministic joint integrability.  This file packages that reduction into
the exact `PmCoeffMomentFubiniOutput` consumed by P-3.5b.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Flat product measure for one copy of an order-`m` parametrix profile. -/
def pairingHalfPhysicalMeasure (m : ℕ) :
    Measure (T4 × (T4 × (Fin m → T4))) :=
  paperMeasure.prod
    (paperMeasure.prod
      (Measure.pi fun _ : Fin m => paperMeasure))

instance instSFinitePairingHalfPhysicalMeasure (m : ℕ) :
    SFinite (pairingHalfPhysicalMeasure m) := by
  unfold pairingHalfPhysicalMeasure
  infer_instance

/-- Spatial carrier for one flat deterministic profile. -/
abbrev PairingHalfPhysicalPoint (m : ℕ) :=
  T4 × (T4 × (Fin m → T4))

/-- Insert a fixed noise sample into one flat physical profile. -/
def pairingHalfFixedTupleMap
    (M : NoiseModel) (m : ℕ) (ω : M.Ω) :
    PairingHalfPhysicalPoint m →
      M.Ω × (Fin (m + 2) → T4) :=
  fun p => (ω, assemble p.1 p.2.1 p.2.2)

theorem measurable_pairingHalfFixedTupleMap
    (M : NoiseModel) (m : ℕ) (ω : M.Ω) :
    Measurable (pairingHalfFixedTupleMap M m ω) := by
  exact measurable_const.prodMk (measurable_assemble_prod m)

/-- Unit-modulus Fourier phase times the Wick factor at a fixed sample. -/
def pairingHalfWickWeight
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) (ω : M.Ω)
    (p : PairingHalfPhysicalPoint m) : ℂ :=
  charT4 α p.1 * charT4 β p.2.1 *
    (wickAt M ρ ε κ
      (pairingHalfFixedTupleMap M m ω p).2
      (pairingHalfFixedTupleMap M m ω p).1 : ℂ)

theorem NoiseModel.measurable_pairingHalfWickWeight
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) (ω : M.Ω) :
    Measurable
      (pairingHalfWickWeight M ρ ε m α β κ ω) := by
  have hphase :
      Measurable fun p : PairingHalfPhysicalPoint m =>
        charT4 α p.1 * charT4 β p.2.1 :=
    ((continuous_charT4 α).measurable.comp measurable_fst).mul
      ((continuous_charT4 β).measurable.comp
        (measurable_fst.comp measurable_snd))
  have hwick :
      Measurable fun p : PairingHalfPhysicalPoint m =>
        (wickAt M ρ ε κ
          (pairingHalfFixedTupleMap M m ω p).2
          (pairingHalfFixedTupleMap M m ω p).1 : ℂ) :=
    Complex.measurable_ofReal.comp
      ((M.measurable_wickAt_joint ρ ε κ).comp
        (measurable_pairingHalfFixedTupleMap M m ω))
  have h :
      Measurable fun p : PairingHalfPhysicalPoint m =>
        (charT4 α p.1 * charT4 β p.2.1) *
          (wickAt M ρ ε κ
            (pairingHalfFixedTupleMap M m ω p).2
            (pairingHalfFixedTupleMap M m ω p).1 : ℂ) :=
    hphase.mul hwick
  change
    Measurable fun p : PairingHalfPhysicalPoint m =>
      charT4 α p.1 * charT4 β p.2.1 *
        (wickAt M ρ ε κ
          (pairingHalfFixedTupleMap M m ω p).2
          (pairingHalfFixedTupleMap M m ω p).1 : ℂ)
  exact h

/-- A deterministic flat-profile integrability theorem yields the minimal
spatial hypothesis needed for the finite pairing expansion, on the
almost-sure event where the mollified noise is continuous. -/
theorem pairingCoefficientSpatialIntegrable_of_detIntegrand_flat
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (α β : Z4)
    (hdet :
      ∀ κ : PartialPairing (Fin m),
        Integrable
          (fun p : T4 × (T4 × (Fin m → T4)) =>
            (detIntegrand ρ ε m κ
              (assemble p.1 p.2.1 p.2.2) : ℂ))
          (pairingHalfPhysicalMeasure m)) :
    PairingCoefficientSpatialIntegrable
      M ρ lam ε m α β where
  joint κ := by
    filter_upwards [M.ae_continuous_xiEps ρ hε] with ω hξ
    obtain ⟨B, hB0, hwickBound⟩ :=
      M.exists_uniform_norm_wickAt_bound_of_continuous
        ρ hε hε1 κ ω hξ
    let weight :
        PairingHalfPhysicalPoint m → ℂ :=
      pairingHalfWickWeight M ρ ε m α β κ ω
    have hweightMeas :
        AEStronglyMeasurable weight
          (pairingHalfPhysicalMeasure m) := by
      exact
        (M.measurable_pairingHalfWickWeight
          ρ ε m α β κ ω).aestronglyMeasurable
    have hweightBound :
        ∀ᵐ p ∂(pairingHalfPhysicalMeasure m),
          ‖weight p‖ ≤ B :=
      Filter.Eventually.of_forall fun p => by
        unfold weight pairingHalfWickWeight
        rw [norm_mul, norm_mul, norm_charT4, norm_charT4,
          one_mul, Complex.norm_real, Real.norm_eq_abs]
        simpa only [one_mul, pairingHalfFixedTupleMap] using
          hwickBound (assemble p.1 p.2.1 p.2.2)
    have hflat :
        Integrable
          (fun p : T4 × (T4 × (Fin m → T4)) =>
            pairingHalfIntegrand
              M ρ ε m α β κ ω p.1 p.2.1 p.2.2)
          (pairingHalfPhysicalMeasure m) := by
      have hproduct :=
        (hdet κ).mul_bdd hweightMeas hweightBound
      convert hproduct using 1
      funext p
      unfold pairingHalfIntegrand weight pairingHalfWickWeight
        pairingHalfFixedTupleMap randIntegrand
      push_cast
      ring
    let μV := Measure.pi fun _ : Fin m => paperMeasure
    have hassoc :
        MeasurePreserving
          (MeasurableEquiv.prodAssoc :
            (T4 × T4) × (Fin m → T4) ≃ᵐ
              T4 × (T4 × (Fin m → T4)))
          ((paperMeasure.prod paperMeasure).prod μV)
          (pairingHalfPhysicalMeasure m) := by
      simpa only [pairingHalfPhysicalMeasure, μV] using
        (measurePreserving_prodAssoc
          paperMeasure paperMeasure μV)
    have hleftAssoc :
        Integrable
          (fun p : (T4 × T4) × (Fin m → T4) =>
            pairingHalfIntegrand
              M ρ ε m α β κ ω p.1.1 p.1.2 p.2)
          ((paperMeasure.prod paperMeasure).prod μV) := by
      exact hassoc.integrable_comp_of_integrable hflat
    have hinter :
        Integrable
          (fun p : T4 × T4 =>
            ∫ v : Fin m → T4,
              pairingHalfIntegrand
                M ρ ε m α β κ ω p.1 p.2 v
              ∂μV)
          (paperMeasure.prod paperMeasure) :=
      hleftAssoc.integral_prod_left
    have hscaled :=
      hinter.const_mul (lamEps lam ε ^ m : ℂ)
    refine hscaled.congr ?_
    filter_upwards with p
    unfold pmPairingFourierIntegrand randRI
      pairingHalfIntegrand
    rw [integral_const_mul, integral_complex_ofReal]
    push_cast
    ring

/-- Complete P-3.5b Fubini output from deterministic flat and doubled
integrability.  No random-level estimate is assumed. -/
theorem pmCoeffMomentFubiniOutput_of_deterministic_integrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (α β : Z4)
    (hhalf :
      ∀ κ : PartialPairing (Fin m),
        Integrable
          (fun p : T4 × (T4 × (Fin m → T4)) =>
            (detIntegrand ρ ε m κ
              (assemble p.1 p.2.1 p.2.2) : ℂ))
          (pairingHalfPhysicalMeasure m))
    (hbare :
      ∀ κp κm : PartialPairing (Fin m),
        Integrable
          (r324Flatten
            (pairingMomentDeterministicFactor
              ρ ε m α β κp κm))
          (r324PhysicalMeasure m))
    (hcross :
      ∀ (κp κm : PartialPairing (Fin m))
        (π : κp.singles ≃ κm.singles),
        Integrable
          (r324Flatten
            (deterministicMomentIntegrand
              ρ ε m α β κp κm π))
          (r324PhysicalMeasure m)) :
    PmCoeffMomentFubiniOutput M ρ lam ε m α β := by
  let hspatial :=
    pairingCoefficientSpatialIntegrable_of_detIntegrand_flat
      M ρ lam hε hε1 m α β hhalf
  apply pmCoeffMomentFubiniOutput_of_spatial hspatial
  · intro κp κm
    exact pairingProduct_integrable_of_raw
      M ρ lam ε m α β κp κm
        (pairingMomentRawIntegrable_of_deterministic
          M ρ hε hε1 m α β κp κm (hbare κp κm))
  · intro κp κm
    exact pairingProduct_fubini_of_raw
      M ρ lam ε m α β κp κm
        (pairingMomentRawIntegrable_of_deterministic
          M ρ hε hε1 m α β κp κm (hbare κp κm))
  · exact hcross

end

end Anderson4D
