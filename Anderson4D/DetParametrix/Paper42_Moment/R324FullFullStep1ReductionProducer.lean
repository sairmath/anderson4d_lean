import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingGroupedHalfTerminalBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfIntegrable
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperIteration
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTraceIntegrable
import Anderson4D.DetParametrix.Paper42_Moment.R324Prop41ProviderAtTruncation

/-!
# The full/full endpoint half at the Step-1 terminal seam

This module closes the exact finite-sum, endpoint-Fubini, and proper-prefix
trace part of the full/full branch.  Starting from the complete endpoint
signature fibre, the coupling-weighted half is transported to the retained
terminal raw-local block of the certified Proposition 4.1 trace.

The terminal trace carries *scaled* edge kernels.  The final conversion to
`R324Step1Reduction` therefore additionally requires an exact normalization
ledger for those edges; the declarations below deliberately expose that seam
without replacing it by a target-shaped estimate.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

namespace R324WithinHalfStopBeforeLastTrace

variable {rho : SmoothCutoff} {lam eps : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {terminal : R322ExtractionStep m}

/-- Root integrability propagates through a trace stopped immediately before
its retained terminal block, discharging the unit-outer-factor premise used
by the exact proper-prefix iteration. -/
theorem weightedIntegrableAlong_one_of_integrable
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace : R324WithinHalfStopBeforeLastTrace terminal res scale)
    (x y : T4)
    (hroot :
      Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand rho eps x y
            (res.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure)) :
    trace.WeightedIntegrableAlong x y (fun _ => (1 : ℂ)) := by
  induction trace with
  | stop => trivial
  | step current head tail hremaining scale internal nextScale
      nextCertificate next ih =>
      refine ⟨?_, ih ?_⟩
      · simpa using hroot
      · exact
          integrable_residualIntegrand_afterHead current head tail
            hremaining x y hroot internal.internal

/-- The same root premise gives honest integrability of the stopped residual
section needed by the terminal coordinate split. -/
theorem integrable_stopPrefix_residualIntegrand_of_integrable
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace : R324WithinHalfStopBeforeLastTrace terminal res scale)
    (x y : T4)
    (hroot :
      Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand rho eps x y
            (res.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun v : trace.stopPrefix.SurvivingCoordinate → T4 =>
        (trace.stopPrefix.residualIntegrand rho eps x y
          (trace.stopPrefix.reconstruct v) : ℂ))
      (Measure.pi fun _ => paperMeasure) := by
  induction trace with
  | stop => exact hroot
  | step current head tail hremaining scale internal nextScale
      nextCertificate next ih =>
      exact ih
        (integrable_residualIntegrand_afterHead current head tail
          hremaining x y hroot internal.internal)

end R324WithinHalfStopBeforeLastTrace

/-! ## The complete endpoint fibre as one grouped root integral -/

/-- The finite endpoint-signature sum may be moved under the genuine joint
half integral before any norm is taken.  Pointwise, the resulting signed sum
is exactly the grouped initial residual consumed by the certified trace. -/
theorem sum_deterministicFullHalfIntegral_eq_integral_initialGroupedResidual
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1)
    (lam : ℝ) (q : ℕ) (alpha beta : Z4)
    (kappa : PartialPairing (Fin (2 * q))) (hkappa : kappa.IsFull) :
    (∑ tau : ReductionEndpointFiberAt kappa,
        deterministicFullHalfIntegral
          rho eps (2 * q) alpha beta tau.1) =
      ∫ p : T4 × (T4 × (Fin (2 * q) → T4)),
        charT4 alpha p.1 * charT4 beta p.2.1 *
          (((initial rho lam eps kappa).residualIntegrand
            rho eps p.1 p.2.1 p.2.2 : ℝ) : ℂ)
        ∂(paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin (2 * q) => paperMeasure))) := by
  simp_rw [deterministicFullHalfIntegral]
  rw [← integral_finsetSum Finset.univ]
  · apply integral_congr_ae
    filter_upwards with p
    rw [← Finset.mul_sum]
    apply congrArg
      (fun z : ℂ => charT4 alpha p.1 * charT4 beta p.2.1 * z)
    exact
      R324FullPairingBudgetTerminalAdapter.sum_endpointFiber_detIntegrand_eq_initialGroupedResidual
        (ρ := rho) (lam := lam) (ε := eps) hkappa p.1 p.2.1 p.2.2
  · intro tau _htau
    exact deterministicFullHalfIntegrable_all
      rho heps heps1 alpha beta tau.1

namespace R324FullPairingBudgetTerminalAdapter

variable {rho : SmoothCutoff} {C lam eps K A : ℝ}
    {q : ℕ} {kappa : PartialPairing (Fin (2 * q))}
    {budget :
      R324FullPairingBudgetStopTrace
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) (A := A) kappa}

/-- The literal terminal raw-local Fourier integral left after all proper
within-half blocks have been consumed.  The empty post-terminal coordinate
integral is retained exactly as in the certified Fubini theorem. -/
def terminalRawLocalFourierIntegral
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (alpha beta : Z4) : ℂ :=
  ∫ p : T4 × T4,
    charT4 alpha p.1 * charT4 beta p.2 *
      ((lamEps lam eps : ℂ) ^
          (2 * residualBlockOrder
            data.geometry.terminalData.terminal.2) *
        (∫ t :
            Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2) →
              T4,
          ∫ _v :
              (data.geometry.trace.stopPrefix.afterHead
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton)
                  |>.SurvivingCoordinate →
                T4,
            ((data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).rawLocalIntegrand
                rho eps (p.1 - p.2) (fun j => t j - p.2) : ℂ)
            ∂Measure.pi fun _ => paperMeasure
          ∂Measure.pi fun _ => paperMeasure))
    ∂(paperMeasure.prod paperMeasure)

/-- **Exact full-half terminal producer.**

The complete endpoint-signature half sum, with its full coupling weight,
is exactly the Fourier integral of the retained terminal raw-local block.
All finite grouping and every Fubini premise are discharged from the proved
joint integrability of the original deterministic half. -/
theorem lamEps_pow_sum_deterministicFullHalfIntegral_eq_terminalRawLocal
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hkappa : kappa.IsFull)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (alpha beta : Z4) :
    (lamEps lam eps : ℂ) ^ (2 * q) *
        (∑ tau : ReductionEndpointFiberAt kappa,
          deterministicFullHalfIntegral
            rho eps (2 * q) alpha beta tau.1) =
      data.terminalRawLocalFourierIntegral alpha beta := by
  let muV : Measure (Fin (2 * q) → T4) :=
    Measure.pi fun _ => paperMeasure
  let f : T4 × (T4 × (Fin (2 * q) → T4)) → ℂ := fun p =>
    charT4 alpha p.1 * charT4 beta p.2.1 *
      (((initial rho lam eps kappa).residualIntegrand
        rho eps p.1 p.2.1 p.2.2 : ℝ) : ℂ)
  have hf :
      Integrable f
        (paperMeasure.prod (paperMeasure.prod muV)) := by
    have hsum :
        Integrable
          (fun p : T4 × (T4 × (Fin (2 * q) → T4)) =>
            ∑ tau : ReductionEndpointFiberAt kappa,
              charT4 alpha p.1 * charT4 beta p.2.1 *
                (detIntegrand rho eps (2 * q) tau.1
                  (assemble p.1 p.2.1 p.2.2) : ℂ))
          (paperMeasure.prod (paperMeasure.prod muV)) := by
      apply integrable_finsetSum
      intro tau _htau
      change
        DeterministicFullHalfIntegrable
          rho eps (2 * q) alpha beta tau.1
      exact
        deterministicFullHalfIntegrable_all
          rho heps heps1 alpha beta tau.1
    apply hsum.congr
    filter_upwards with p
    dsimp only [f]
    rw [← Finset.mul_sum]
    apply congrArg
      (fun z : ℂ => charT4 alpha p.1 * charT4 beta p.2.1 * z)
    exact
      sum_endpointFiber_detIntegrand_eq_initialGroupedResidual
        (ρ := rho) (lam := lam) (ε := eps)
        hkappa p.1 p.2.1 p.2.2
  let assoc :
      (T4 × T4) × (Fin (2 * q) → T4) ≃ᵐ
        T4 × (T4 × (Fin (2 * q) → T4)) :=
    MeasurableEquiv.prodAssoc
  have hassoc :
      MeasurePreserving assoc
        ((paperMeasure.prod paperMeasure).prod muV)
        (paperMeasure.prod (paperMeasure.prod muV)) := by
    simpa only [assoc] using
      (measurePreserving_prodAssoc paperMeasure paperMeasure muV)
  have hfAssoc :
      Integrable
        (fun p : (T4 × T4) × (Fin (2 * q) → T4) =>
          f (p.1.1, p.1.2, p.2))
        ((paperMeasure.prod paperMeasure).prod muV) := by
    exact hassoc.integrable_comp_of_integrable hf
  have hFubini :
      (∫ p, f p
          ∂(paperMeasure.prod (paperMeasure.prod muV))) =
        ∫ p : T4 × T4,
          ∫ v : Fin (2 * q) → T4,
            f (p.1, p.2, v) ∂muV
          ∂(paperMeasure.prod paperMeasure) := by
    calc
      (∫ p, f p
          ∂(paperMeasure.prod (paperMeasure.prod muV))) =
          ∫ p : (T4 × T4) × (Fin (2 * q) → T4),
            f (assoc p)
            ∂((paperMeasure.prod paperMeasure).prod muV) :=
        (hassoc.integral_comp' f).symm
      _ =
          ∫ p : (T4 × T4) × (Fin (2 * q) → T4),
            f (p.1.1, p.1.2, p.2)
            ∂((paperMeasure.prod paperMeasure).prod muV) := by
        rfl
      _ = _ := by
        rw [integral_prod _ hfAssoc]
  have hroot :=
    eventually_integrable_initial_residualIntegrand
      rho lam heps heps1 kappa
  rw [
    sum_deterministicFullHalfIntegral_eq_integral_initialGroupedResidual
      rho heps heps1 lam q alpha beta kappa hkappa]
  change
    (lamEps lam eps : ℂ) ^ (2 * q) *
        (∫ p, f p
          ∂(paperMeasure.prod (paperMeasure.prod muV))) = _
  rw [hFubini, ← integral_const_mul]
  unfold terminalRawLocalFourierIntegral
  apply integral_congr_ae
  filter_upwards [hroot] with p hp
  have hweighted :=
    data.geometry.trace.weightedIntegrableAlong_one_of_integrable
      p.1 p.2 hp
  have hstop :=
    data.geometry.trace.integrable_stopPrefix_residualIntegrand_of_integrable
      p.1 p.2 hp
  have hcollapse :=
    data.lamEps_pow_integral_initialGroupedResidual_eq_terminalRawLocal
      hkappa p.1 p.2 hweighted hstop
  dsimp only [f]
  rw [integral_const_mul]
  calc
    (lamEps lam eps : ℂ) ^ (2 * q) *
          (charT4 alpha p.1 * charT4 beta p.2 *
            ∫ v : Fin (2 * q) → T4,
              (((initial rho lam eps kappa).residualIntegrand
                rho eps p.1 p.2 v : ℝ) : ℂ)
              ∂muV) =
        charT4 alpha p.1 * charT4 beta p.2 *
          ((lamEps lam eps : ℂ) ^ (2 * q) *
            ∫ v : Fin (2 * q) → T4,
              (((initial rho lam eps kappa).residualIntegrand
                rho eps p.1 p.2 v : ℝ) : ℂ)
              ∂muV) := by ring
    _ = _ := by rw [hcollapse]

/-! ## Uniform construction of the exact terminal producer -/

/-- Proposition 4.1 at the paper truncation constructs the complete adapter
and the preceding exact identity uniformly.  Thus no finite-sum, Fubini, or
proper-prefix hypothesis remains in the full-pairing half. -/
theorem exists_fullPairing_terminalRawLocal_producer
    (rho : SmoothCutoff) :
    ∃ supportConstant C K A : ℝ,
      0 < supportConstant ∧ 0 < C ∧ 0 < K ∧ 1 ≤ A ∧
        ∀ (lam eps : ℝ) (q : ℕ)
          (kappa : PartialPairing (Fin (2 * q))),
          0 < lam → 0 < eps → eps ≤ 1 →
          1 ≤ |Real.log eps| → q ≤ truncOrder eps →
          1 ≤ q → kappa.IsFull →
          ∃ budget :
              R324FullPairingBudgetStopTrace
                (ρ := rho) (C := C) (lam := lam)
                (ε := eps) (K := K) (A := A) kappa,
            ∃ data : R324FullPairingBudgetTerminalAdapter budget,
              ∀ alpha beta : Z4,
                (lamEps lam eps : ℂ) ^ (2 * q) *
                    (∑ tau : ReductionEndpointFiberAt kappa,
                      deterministicFullHalfIntegral
                        rho eps (2 * q) alpha beta tau.1) =
                  data.terminalRawLocalFourierIntegral alpha beta := by
  obtain ⟨supportConstant, C, K, A,
      hsupport, hC, hK, hA, hprovider⟩ :=
    exists_r324FullPairingBudgetTerminalAdapter_at_truncation rho
  refine ⟨supportConstant, C, K, A,
    hsupport, hC, hK, hA, ?_⟩
  intro lam eps q kappa hlam heps heps1 hlog hqtrunc hq hkappa
  obtain ⟨budget, ⟨data⟩⟩ :=
    hprovider lam eps q kappa
      hlam heps heps1 hlog hqtrunc hq hkappa
  exact ⟨budget, data, fun alpha beta =>
    data.lamEps_pow_sum_deterministicFullHalfIntegral_eq_terminalRawLocal
      hkappa heps heps1 alpha beta⟩

/-! ## The sole remaining representation seam -/

/-- The literal statement that the scaled terminal trace is represented by
the successive-removal vocabulary of `R324PaperIteration`.

This is deliberately an equality to `r324RemovalAmplitude`, together with
the structural and integrability facts consumed by that construction.  It
does not assume a bound on the desired half sum. -/
def TerminalRemovalRepresentation
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (Citer : ℝ) (alpha beta : Z4) : Prop :=
  ∃ (p : ℕ) (hp : 1 ≤ p)
    (Gp : Fin (2 * p - 1) → T4 → ℝ)
    (Is : Fin (2 * p - 1) → List R324RemovedInterval),
      p = residualBlockOrder
          data.geometry.terminalData.terminal.2 ∧
      2 * p ≤ 2 * q ∧
      p ≤ truncOrder eps ∧
      (∑ j, r324RemovedSites (Is j)) = 2 * q - 2 * p ∧
      IsAdmissiblePrimitiveInput p Gp ∧
      (∀ j, Measurable (Gp j)) ∧
      (∀ j, ∀ I ∈ Is j, I.order ≤ truncOrder eps) ∧
      (∀ j, R324RemovalIntegrable rho lam eps (Gp j) (Is j)) ∧
      data.terminalRawLocalFourierIntegral alpha beta =
        r324RemovalAmplitude
          rho lam eps Citer p hp alpha beta Gp Is

/-- Once the terminal edge state has the literal successive-removal
representation, the exact producer above and the proved §4.1 iteration close
`R324Step1Reduction` without any further analytic estimate. -/
theorem exists_step1Reduction_of_terminalRemovalRepresentation
    (rho : SmoothCutoff) :
    ∃ Citer : ℝ, 0 < Citer ∧
      ∀ {C lam eps K A : ℝ} {q : ℕ}
        {kappa : PartialPairing (Fin (2 * q))}
        {budget :
          R324FullPairingBudgetStopTrace
            (ρ := rho) (C := C) (lam := lam)
            (ε := eps) (K := K) (A := A) kappa}
        (data : R324FullPairingBudgetTerminalAdapter budget),
        0 < lam → 0 < eps → eps ≤ 1 →
        1 ≤ |Real.log eps| → kappa.IsFull →
        ∀ alpha beta : Z4,
          data.TerminalRemovalRepresentation Citer alpha beta →
          R324Step1Reduction rho lam eps (2 * q) alpha beta Citer
            ((lamEps lam eps : ℂ) ^ (2 * q) *
              ∑ tau : ReductionEndpointFiberAt kappa,
                deterministicFullHalfIntegral
                  rho eps (2 * q) alpha beta tau.1) := by
  obtain ⟨Citer, hCiter, hiteration⟩ :=
    exists_r324Step1Reduction_of_removal rho
  refine ⟨Citer, hCiter, ?_⟩
  intro C lam eps K A q kappa budget data
    hlam heps heps1 hlog hkappa alpha beta hrepresentation
  obtain ⟨p, hp, Gp, Is, _hpterminal, hpambient, hptrunc,
      hsites, hGp, hGpmeas, hItrunc, hIintegrable, hterminal⟩ :=
    hrepresentation
  have hremoval :
      R324Step1Reduction rho lam eps (2 * q) alpha beta Citer
        (r324RemovalAmplitude
          rho lam eps Citer p hp alpha beta Gp Is) :=
    hiteration lam eps (2 * q) p hp alpha beta Gp Is
      hlam heps heps1 hlog hpambient hptrunc hsites hGp
      hGpmeas hItrunc hIintegrable
  have hproducer :=
    data.lamEps_pow_sum_deterministicFullHalfIntegral_eq_terminalRawLocal
      hkappa heps heps1 alpha beta
  rw [hproducer, hterminal]
  exact hremoval

end R324FullPairingBudgetTerminalAdapter

end R324WithinHalfResidualPrefix

end

end Anderson4D
