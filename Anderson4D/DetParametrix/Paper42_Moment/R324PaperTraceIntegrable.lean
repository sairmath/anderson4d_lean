import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalJointIntegrability

/-!
# The weighted trace integrability, discharged at the unit outer factor

Paper: R-324 — §4.2 — weighted trace integrability along a removal

`WeightedIntegrableAlong` is the analytic premise of the proved
within-half iteration `lamEps_pow_integral_mul_terminalOuter_eq_terminal`:
at every nonterminal state of a certified analytic trace, the current
residual integrand times the carried outer factor must be integrable on
the current surviving carrier.

At the unit outer factor it is not an assumption.  Two proved facts
close it by induction along the trace:

* `integrable_residualIntegrand_afterHead` — integrability is preserved by
  one literal head collapse, given the head's internal Fubini evidence;
* that evidence is carried by the trace itself, in the `internal` field of
  its `step` constructor.

So the whole premise reduces to integrability at the *root* state, which
for the all-Green initial state is the fixed-scale integrability recipe in
`docs/R324_PAPER_PROOF.md` (bounded covariance × integrable Green chain).
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

namespace R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- **The weighted trace premise at the unit outer factor, discharged.**

Root integrability propagates along the whole certified trace, so
`WeightedIntegrableAlong x y 1` needs nothing beyond integrability of the
residual integrand at the state the trace starts from. -/
theorem weightedIntegrableAlong_one
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace : R324WithinHalfCertifiedAnalyticTrace res scale)
    (x y : T4) :
    Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y (res.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure) →
      trace.WeightedIntegrableAlong x y (fun _ => (1 : ℂ)) := by
  induction trace with
  | terminal _r _s _hr _c =>
      intro _
      trivial
  | step current head tail hremaining _scale internal _nextScale
      _nextCertificate next ih =>
      intro hres
      refine ⟨?_, ih ?_⟩
      · simpa using hres
      · exact
          integrable_residualIntegrand_afterHead current head tail
            hremaining x y hres internal.internal

/-- The same statement for any outer factor that is constant. -/
theorem weightedIntegrableAlong_const
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace : R324WithinHalfCertifiedAnalyticTrace res scale)
    (x y : T4) (c : ℂ) :
    Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y (res.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure) →
      trace.WeightedIntegrableAlong x y (fun _ => c) := by
  induction trace with
  | terminal _r _s _hr _c =>
      intro _
      trivial
  | step current head tail hremaining _scale internal _nextScale
      _nextCertificate next ih =>
      intro hres
      refine ⟨?_, ih ?_⟩
      · exact hres.mul_const c
      · exact
          integrable_residualIntegrand_afterHead current head tail
            hremaining x y hres internal.internal

end R324WithinHalfCertifiedAnalyticTrace

/-! ## The root state: the all-Green initial residual -/

/-- Root integrability at almost every endpoint pair.

`integrable_initial_residualIntegrand_pair` gives joint `L¹` of the initial
within-half residual in its two endpoints *and* all initial sparse
coordinates; Fubini turns that into integrability of the fixed-endpoint
section at almost every endpoint pair.  Almost-everywhere is the honest
form: fixed-endpoint Green sections do fail on exceptional diagonals. -/
theorem eventually_integrable_initial_residualIntegrand
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    ∀ᵐ p : T4 × T4 ∂(paperMeasure.prod paperMeasure),
      Integrable
        (fun v : (initial ρ lam ε κ).SurvivingCoordinate → T4 =>
          ((initial ρ lam ε κ).residualIntegrand ρ ε p.1 p.2
            ((initial ρ lam ε κ).reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure) := by
  have h :
      Integrable
        (fun p : (T4 × T4) ×
            ((initial ρ lam ε κ).SurvivingCoordinate → T4) =>
          (((initial ρ lam ε κ).residualIntegrand ρ ε p.1.1 p.1.2
            ((initial ρ lam ε κ).reconstruct p.2) : ℝ) : ℂ))
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ => paperMeasure)) :=
    (integrable_initial_residualIntegrand_pair ρ lam hε hε1 κ).ofReal
  filter_upwards [h.prod_right_ae] with p hp using hp

/-- **The weighted trace premise, discharged from the all-Green root.**

For a certified analytic trace starting at the initial state — the state
paper §4.2 Step 2(5) starts from, before any subinterval has been removed —
the premise `WeightedIntegrableAlong x y c` of the proved within-half
iteration holds at almost every endpoint pair, for every constant outer
factor.  Nothing beyond Proposition 4.1 and the boundedness of `η_ε` at a
fixed scale is used. -/
theorem eventually_weightedIntegrableAlong_const_initial
    {ρ : SmoothCutoff} {lam ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace
        (initial ρ lam ε pairing) scale)
    (c : ℂ) :
    ∀ᵐ p : T4 × T4 ∂(paperMeasure.prod paperMeasure),
      trace.WeightedIntegrableAlong p.1 p.2 (fun _ => c) := by
  filter_upwards
      [eventually_integrable_initial_residualIntegrand ρ lam hε hε1 pairing]
    with p hp
  exact trace.weightedIntegrableAlong_const p.1 p.2 c hp

end R324WithinHalfResidualPrefix

end

end Anderson4D

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix
namespace R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- **Root integrability propagates to the terminal state.**

`integrable_residualIntegrand_afterHead` moves integrability through one
literal head collapse, and the head's internal Fubini evidence is carried
by the trace itself.  Iterating along the trace lands on the terminal
prefix, where every fully paired subinterval of the half has been removed. -/
theorem integrable_terminalPrefix_residualIntegrand
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace : R324WithinHalfCertifiedAnalyticTrace res scale)
    (x y : T4) :
    Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y (res.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure) →
      Integrable
        (fun v : trace.terminalPrefix.SurvivingCoordinate → T4 =>
          (trace.terminalPrefix.residualIntegrand ρ ε x y
            (trace.terminalPrefix.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure) := by
  induction trace with
  | terminal _r _s _hr _c =>
      intro h
      exact h
  | step current head tail hremaining _scale internal _nextScale
      _nextCertificate next ih =>
      intro hres
      exact
        ih
          (integrable_residualIntegrand_afterHead current head tail
            hremaining x y hres internal.internal)

end R324WithinHalfCertifiedAnalyticTrace
end R324WithinHalfResidualPrefix

end

end Anderson4D
