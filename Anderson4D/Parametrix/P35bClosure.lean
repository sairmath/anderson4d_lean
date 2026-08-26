import Anderson4D.DetParametrix.Paper42_Moment.R324DetIntegrability
import Anderson4D.Parametrix.PairingMomentClosure
import Anderson4D.Parametrix.MollifiedWickSecondMoment

/-!
# Constructive closure of Proposition 3.5(b)

This file removes the qualitative interfaces from the proof of paper
(3.24).  Joint spatial integrability is supplied by the increasing-tree
proof in `R324DetIntegrability`, while the exact noise contraction law is
the concrete mollified Wick theorem.

Two genuinely quantitative parts of paper §4.2 remain explicit in the final
theorem:

* pointwise domination of each constructed fixed-signature physical density
  by the Proposition 4.1 inserted majorant;
* construction of the finite routed frequency decomposition from Step 4.

They are stated directly, rather than hidden in a new output structure.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Qualitative R-324 and Wick closure -/

/-- The four unit-modulus Fourier characters do not affect joint
integrability of the bare doubled deterministic profile. -/
theorem integrable_r324Flatten_pairingMomentDeterministicFactor
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (α β : Z4)
    (κp κm : PartialPairing (Fin m)) :
    Integrable
      (r324Flatten
        (pairingMomentDeterministicFactor
          ρ ε m α β κp κm))
      (r324PhysicalMeasure m) := by
  have hbare :=
    integrable_r324Flatten_detIntegrand_product
      ρ hε hε1 κp κm
  let phase : R324PhysicalPoint m → ℂ := fun p =>
    charT4 α p.1 *
      charT4 β p.2.1 *
      charT4 (-α) p.2.2.1 *
      charT4 (-β) p.2.2.2.1
  have hx : Measurable fun p : R324PhysicalPoint m => p.1 :=
    measurable_fst
  have hy : Measurable fun p : R324PhysicalPoint m => p.2.1 :=
    measurable_fst.comp measurable_snd
  have hz : Measurable fun p : R324PhysicalPoint m => p.2.2.1 :=
    measurable_fst.comp
      (measurable_snd.comp measurable_snd)
  have hw : Measurable fun p : R324PhysicalPoint m => p.2.2.2.1 :=
    measurable_fst.comp
      (measurable_snd.comp
        (measurable_snd.comp measurable_snd))
  have hphaseMeas : Measurable phase := by
    exact
      ((((continuous_charT4 α).measurable.comp hx).mul
        ((continuous_charT4 β).measurable.comp hy)).mul
        ((continuous_charT4 (-α)).measurable.comp hz)).mul
        ((continuous_charT4 (-β)).measurable.comp hw)
  have hphaseBound :
      ∀ p : R324PhysicalPoint m, ‖phase p‖ ≤ 1 := by
    intro p
    simp only [phase, norm_mul, norm_charT4, mul_one,
      le_refl]
  have hproduct :=
    hbare.mul_bdd hphaseMeas.aestronglyMeasurable
      (.of_forall hphaseBound)
  convert hproduct using 1
  funext p
  unfold r324Flatten pairingMomentDeterministicFactor phase
  push_cast
  ring

/-- The complete Fubini output for one order and mode pair follows from the
constructed R-324 integrability theorems; no analytic output predicate is
assumed. -/
theorem pmCoeffMomentFubiniOutput_of_r324
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (α β : Z4) :
    PmCoeffMomentFubiniOutput M ρ lam ε m α β := by
  apply pmCoeffMomentFubiniOutput_of_deterministic_integrability
    M ρ lam hε hε1 m α β
  · intro κ
    simpa only [pairingHalfPhysicalMeasure] using
      integrable_detIntegrand_flat ρ hε hε1 κ
  · intro κp κm
    exact
      integrable_r324Flatten_pairingMomentDeterministicFactor
        ρ hε hε1 m α β κp κm
  · intro κp κm π
    exact
      integrable_r324Flatten_deterministicMomentIntegrand
        ρ hε hε1 α β κp κm π

/-- Exact second-moment identity with both the Fubini and Wick inputs
instantiated by their concrete constructions. -/
theorem integral_norm_sq_pmCoeff_eq_deterministicMomentPairingSum_of_r324
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (α β : Z4) :
    ((∫ ω, ‖pmCoeff M ρ lam ε m α β ω‖ ^ 2
        ∂(volume : Measure M.Ω) : ℝ) : ℂ) =
      deterministicMomentPairingSum ρ lam ε m α β :=
  integral_norm_sq_pmCoeff_eq_deterministicMomentPairingSum
    (pmCoeffMomentFubiniOutput_of_r324
      M ρ lam hε hε1 m α β)
    (M.wickAtSecondMomentLaw ρ hε m)

/-- Concrete qualitative half of P-3.5(b): every coefficient belongs to
`L²`, without assuming a Fubini or random-integrability interface. -/
theorem memLp_pmCoeff_of_r324
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (α β : Z4) :
    MemLp (pmCoeff M ρ lam ε m α β) 2
      (volume : Measure M.Ω) :=
  (pmCoeffMomentFubiniOutput_of_r324
    M ρ lam hε hε1 m α β).memLp_pmCoeff

/-! ## Quantitative P-3.5(b) closure -/

/-- P-3.5(b) with every qualitative premise discharged and only the two
literal missing estimates from §4.2 left as hypotheses.

The first hypothesis is exactly the pointwise block-collapse estimate
needed by `MomentPhysicalFiberReductionData.toMomentFiberReductionData`.
The second is the concrete finite frequency-routing output of Step 4.
No bound on `pmCoeff` or on `deterministicMomentPairingSum` is assumed. -/
theorem exists_parametrix_coeff_bound_of_physical_r324_and_routing
    {blockConstant supportConstant : ℝ}
    (hblock : 0 < blockConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
        (m : ℕ) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| → 1 ≤ m →
        (∀ s ∈ momentContractionSignatures m,
          ∀ x,
            |lamEps lam ε| ^ (2 * m) *
                momentSignaturePhysicalDensity
                  ρ ε m α β s x ≤
              primitiveInsertedMajorant
                blockConstant lam ε supportConstant m x) →
        RoutedMomentReductionOutput ρ lam ε m α β
          (lamEps lam ε ^ 2 * outerConstant *
            ((4 * blockConstant) * lam) ^ (2 * m - 2)) →
        MemLp (pmCoeff M ρ lam ε m α β) 2
            (volume : Measure M.Ω) ∧
          (∫ ω, ‖pmCoeff M ρ lam ε m α β ω‖ ^ 2
              ∂(volume : Measure M.Ω)) ≤
            deterministicMomentRHS outerConstant
              (4 * blockConstant) lam ε m α β := by
  have hfourBlock : 0 < 4 * blockConstant :=
    mul_pos (by norm_num) hblock
  obtain ⟨outerConstant, houter, hclose⟩ :=
    exists_parametrix_coeff_bound_of_reductions
      hfourBlock hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro M ρ lam ε m α β hlam hε hεsmall hlog hm
    hcollapse hrouted
  have hε1 : ε ≤ 1 :=
    hεsmall.trans (by norm_num)
  let physical :=
    momentPhysicalFiberReductionData
      ρ ε m α β
        (r324MomentIntegrable_all ρ hε hε1 α β)
  have hcollapse' :
      ∀ s ∈ momentContractionSignatures m,
        ∀ x,
          |lamEps lam ε| ^ (2 * m) *
              physical.density s x ≤
            primitiveInsertedMajorant
              blockConstant lam ε supportConstant m x := by
    intro s hs x
    rw [physical.density_eq s hs]
    exact hcollapse s hs x
  let fiber :=
    physical.toMomentFiberReductionData hcollapse'
  have huniform :
      MomentUniformReductionOutputAt ρ lam ε m α β
        (4 * blockConstant) supportConstant :=
    fiber.toMomentUniformReductionOutputAt hblock.le hlam
  exact hclose M ρ lam ε m α β
    hε hεsmall hlog hm
    (pmCoeffMomentFubiniOutput_of_r324
      M ρ lam hε hε1 m α β)
    (M.wickAtSecondMomentLaw ρ hε m)
    huniform hrouted

end

end Anderson4D
