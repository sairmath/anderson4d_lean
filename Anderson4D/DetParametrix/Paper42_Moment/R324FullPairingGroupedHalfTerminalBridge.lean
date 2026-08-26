import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingIntegratedTerminal
import Anderson4D.DetParametrix.Paper42_Moment.R324InitialTwoHalfRootIntegrability

/-!
# Exact grouped-half bridge to the full-pairing terminal block

The certified within-half trace acts on the complete primitive-pairing
fibre grouped by the extraction blocks of a full pairing.  It therefore
starts from `R324WithinHalfResidualPrefix.initial`, whose primitive factor
is a product of finite primitive-pairing sums, rather than from one fixed
`detIntegrand` summand.

This module records the smallest exact analytic bridge needed after that
finite grouping.  It reindexes the standard `Fin (2 * q)` carrier to the
initial sparse carrier, runs every proper block with the exact `lamEps`
ledger, and then applies Fubini once at the singleton terminal stop.  The
result is the genuine signed terminal `rawLocalIntegrand`; no norm or
estimate is taken.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

namespace R324FullPairingBudgetTerminalAdapter

variable {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    {budget :
      R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ}

/-! ## Honest finite grouping of the frozen half terms -/

/-- A full endpoint-signature fibre of frozen `detIntegrand` summands is
pointwise exactly the initial grouped residual consumed by the trace.

This is the necessary finite grouping before Proposition 4.1 is applied:
the theorem does not identify one fixed summand with the grouped residual. -/
theorem sum_endpointFiber_detIntegrand_eq_initialGroupedResidual
    (hκ : κ.IsFull) (x y : T4)
    (v : Fin (2 * q) → T4) :
    (∑ τ : ReductionEndpointFiberAt κ,
        (detIntegrand ρ ε (2 * q) τ.1
          (assemble x y v) : ℂ)) =
      ((R324WithinHalfResidualPrefix.initial
        ρ lam ε κ).residualIntegrand ρ ε x y v : ℂ) := by
  rw [initial_residualIntegrand_complex_eq]
  have hcovariance :
      ∀ τ : ReductionEndpointFiberAt κ,
        detCovarianceFactor ρ ε τ.1 (assemble x y v) =
          (primitiveCovarianceProduct ρ ε q τ.1 v : ℂ) := by
    intro τ
    unfold detCovarianceFactor primitiveCovarianceProduct
    simp only [assemble_varIdx]
  calc
    (∑ τ : ReductionEndpointFiberAt κ,
        (detIntegrand ρ ε (2 * q) τ.1
          (assemble x y v) : ℂ)) =
      ∑ τ : ReductionEndpointFiberAt κ,
        renormalizedGreenSkeleton τ.1 (assemble x y v) *
          (primitiveCovarianceProduct ρ ε q τ.1 v : ℂ) := by
            apply Finset.sum_congr rfl
            intro τ _hτ
            rw [
              detIntegrand_eq_renormalizedGreenSkeleton_mul_covariance,
              hcovariance τ]
    _ = ∑ τ : ReductionEndpointFiberAt κ,
        renormalizedGreenSkeleton κ (assemble x y v) *
          (primitiveCovarianceProduct ρ ε q τ.1 v : ℂ) := by
            apply Finset.sum_congr rfl
            intro τ _hτ
            rw [
              renormalizedGreenSkeleton_eq_of_reductionEndpointSignature_eq
                τ.1 κ τ.2]
    _ = renormalizedGreenSkeleton κ (assemble x y v) *
        ∑ τ : ReductionEndpointFiberAt κ,
          (primitiveCovarianceProduct ρ ε q τ.1 v : ℂ) := by
            rw [Finset.mul_sum]
    _ = renormalizedGreenSkeleton κ (assemble x y v) *
        ((∑ τ : ReductionEndpointFiberAt κ,
          primitiveCovarianceProduct ρ ε q τ.1 v : ℝ) : ℂ) := by
            push_cast
            rfl
    _ = renormalizedGreenSkeleton κ (assemble x y v) *
        ((∏ B : ExtractionBlockIndex κ,
          ∑ σ :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder B.1)) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder B.1)},
            extractionBlockPrimitiveCovarianceFactor
              ρ ε κ B σ v : ℝ) : ℂ) := by
            rw [
              sum_endpointFiber_primitiveCovarianceProduct_eq_prod_primitiveSums
                ρ ε q κ hκ v]
    _ = _ := by congr 1

/-- Integral form of the finite grouping.  The hypotheses are exactly the
termwise Bochner-integrability premises required to commute the finite sum
with the internal integral. -/
theorem sum_endpointFiber_integral_detIntegrand_eq_integral_initialGroupedResidual
    (hκ : κ.IsFull) (x y : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q) → T4 =>
            (detIntegrand ρ ε (2 * q) τ.1
              (assemble x y v) : ℂ))
          (Measure.pi fun _ => paperMeasure)) :
    (∑ τ : ReductionEndpointFiberAt κ,
      ∫ v : Fin (2 * q) → T4,
        (detIntegrand ρ ε (2 * q) τ.1
          (assemble x y v) : ℂ)
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ v : Fin (2 * q) → T4,
        ((R324WithinHalfResidualPrefix.initial
          ρ lam ε κ).residualIntegrand ρ ε x y v : ℂ)
        ∂Measure.pi fun _ => paperMeasure := by
  rw [← integral_finsetSum Finset.univ (by
    intro τ _hτ
    exact hint τ)]
  apply integral_congr_ae
  filter_upwards with v
  exact
    sum_endpointFiber_detIntegrand_eq_initialGroupedResidual
      (ρ := ρ) (lam := lam) (ε := ε) hκ x y v

/-! ## Proper-prefix and terminal bridges -/

/-- For a full pairing, the initial grouped residual carries exactly the
ambient perturbative order `q`. -/
theorem initial_remainingOrder_eq
    (hκ : κ.IsFull) :
    (R324WithinHalfResidualPrefix.initial
      ρ lam ε κ).remainingOrder = q := by
  unfold R324WithinHalfResidualPrefix.remainingOrder
    R324WithinHalfResidualPrefix.initial
  exact sum_r322AnalyticSchedule_blockOrders_of_full κ hκ

/-- Exact proper-prefix iteration from the standard internal carrier to
the singleton terminal stop.

The hypothesis is precisely the weighted integrability consumed by the
certified trace.  The terminal residual itself is left untouched. -/
theorem lamEps_pow_integral_initialGroupedResidual_eq_stopResidual
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hκ : κ.IsFull) (x y : T4)
    (hweighted :
      data.geometry.trace.WeightedIntegrableAlong x y
        (fun _ => (1 : ℂ))) :
    (lamEps lam ε : ℂ) ^ (2 * q) *
        (∫ v : Fin (2 * q) → T4,
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κ).residualIntegrand ρ ε x y v : ℂ)
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder
            data.geometry.terminalData.terminal.2) *
        (∫ v :
            data.geometry.trace.stopPrefix.SurvivingCoordinate → T4,
          (data.geometry.trace.stopPrefix.residualIntegrand
              ρ ε x y
              (data.geometry.trace.stopPrefix.reconstruct v) : ℂ)
          ∂Measure.pi fun _ => paperMeasure) := by
  let initial :=
    R324WithinHalfResidualPrefix.initial ρ lam ε κ
  let e := initialPiMeasurableEquiv ρ lam ε κ
  have hp :
      MeasurePreserving e
        (Measure.pi fun _ : initial.SurvivingCoordinate =>
          paperMeasure)
        (Measure.pi fun _ : Fin (2 * q) =>
          paperMeasure) := by
    simpa only [initial, e] using
      measurePreserving_initialPiMeasurableEquiv
        ρ lam ε κ
  have hreindex :
      (∫ v : Fin (2 * q) → T4,
          (initial.residualIntegrand ρ ε x y v : ℂ)
          ∂Measure.pi fun _ => paperMeasure) =
        ∫ v : initial.SurvivingCoordinate → T4,
          (initial.residualIntegrand ρ ε x y
            (initial.reconstruct v) : ℂ)
          ∂Measure.pi fun _ => paperMeasure := by
    have hreconstruct :
        (fun v : initial.SurvivingCoordinate → T4 =>
          initial.reconstruct v) = e := by
      funext v
      simpa only [initial, e] using
        initial_reconstruct_eq ρ lam ε κ v
    calc
      (∫ v : Fin (2 * q) → T4,
          (initial.residualIntegrand ρ ε x y v : ℂ)
          ∂Measure.pi fun _ => paperMeasure) =
          ∫ v : initial.SurvivingCoordinate → T4,
            (initial.residualIntegrand ρ ε x y (e v) : ℂ)
            ∂Measure.pi fun _ => paperMeasure :=
        (hp.integral_comp'
          (fun v : Fin (2 * q) → T4 =>
            (initial.residualIntegrand ρ ε x y v : ℂ))).symm
      _ = _ := by rw [← hreconstruct]
  rw [hreindex]
  have htrace :=
    data.geometry.trace.lamEps_pow_integral_mul_stopOuter_eq_stop
      x y (fun _ => (1 : ℂ)) hweighted
  rw [initial_remainingOrder_eq (ρ := ρ) (lam := lam)
    (ε := ε) hκ] at htrace
  rw [data.geometry.trace.stopPrefix_remainingOrder_eq] at htrace
  simpa only [mul_one] using htrace

/-- Exact terminal Fubini normal form.  The only additional premise is the
honest integrability of the stopped residual section needed to split its
surviving coordinates.  The post-terminal coordinate integral is retained
literally (its carrier is empty), so this theorem makes no hidden
probability-measure simplification. -/
theorem lamEps_pow_integral_initialGroupedResidual_eq_terminalRawLocal
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hκ : κ.IsFull) (x y : T4)
    (hweighted :
      data.geometry.trace.WeightedIntegrableAlong x y
        (fun _ => (1 : ℂ)))
    (hstop :
      Integrable
        (fun v :
            data.geometry.trace.stopPrefix.SurvivingCoordinate → T4 =>
          (data.geometry.trace.stopPrefix.residualIntegrand
              ρ ε x y
              (data.geometry.trace.stopPrefix.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 * q) *
        (∫ v : Fin (2 * q) → T4,
          ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κ).residualIntegrand ρ ε x y v : ℂ)
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
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
                ρ ε (x - y) (fun j => t j - y) : ℂ)
            ∂Measure.pi fun _ => paperMeasure
          ∂Measure.pi fun _ => paperMeasure) := by
  rw [
    data.lamEps_pow_integral_initialGroupedResidual_eq_stopResidual
      hκ x y hweighted]
  apply congrArg
    (fun a : ℂ =>
      (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder
            data.geometry.terminalData.terminal.2) * a)
  rw [
    data.geometry.trace.stopPrefix.integral_splitSurviving
      data.geometry.terminalData.terminal []
      data.geometry.stop_remaining_eq_singleton _ hstop]
  apply integral_congr_ae
  filter_upwards with t
  apply integral_congr_ae
  filter_upwards with v
  exact_mod_cast
    data.geometry.terminal_residualIntegrand_reconstruct_split_eq_rawLocal
      x y t v

/-- The complete fixed-endpoint bridge from the honest finite sum of frozen
half terms to the signed terminal raw-local density.  This is the closest
valid analogue of a bridge for one `detIntegrand`: Proposition 4.1 acts only
after the endpoint-signature fibre has been grouped. -/
theorem lamEps_pow_sum_endpointFiber_integral_detIntegrand_eq_terminalRawLocal
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hκ : κ.IsFull) (x y : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q) → T4 =>
            (detIntegrand ρ ε (2 * q) τ.1
              (assemble x y v) : ℂ))
          (Measure.pi fun _ => paperMeasure))
    (hweighted :
      data.geometry.trace.WeightedIntegrableAlong x y
        (fun _ => (1 : ℂ)))
    (hstop :
      Integrable
        (fun v :
            data.geometry.trace.stopPrefix.SurvivingCoordinate → T4 =>
          (data.geometry.trace.stopPrefix.residualIntegrand
              ρ ε x y
              (data.geometry.trace.stopPrefix.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 * q) *
        (∑ τ : ReductionEndpointFiberAt κ,
          ∫ v : Fin (2 * q) → T4,
            (detIntegrand ρ ε (2 * q) τ.1
              (assemble x y v) : ℂ)
            ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
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
                ρ ε (x - y) (fun j => t j - y) : ℂ)
            ∂Measure.pi fun _ => paperMeasure
          ∂Measure.pi fun _ => paperMeasure) := by
  rw [
    sum_endpointFiber_integral_detIntegrand_eq_integral_initialGroupedResidual
      (ρ := ρ) (lam := lam) (ε := ε) hκ x y hint]
  exact
    data.lamEps_pow_integral_initialGroupedResidual_eq_terminalRawLocal
      hκ x y hweighted hstop

end R324FullPairingBudgetTerminalAdapter

end R324WithinHalfResidualPrefix

end

end Anderson4D
