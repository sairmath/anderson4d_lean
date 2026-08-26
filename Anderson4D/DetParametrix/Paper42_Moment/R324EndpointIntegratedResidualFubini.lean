import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointIntegratedResidualBridge

/-!
# Global endpoint/internal Fubini bridge for R-324

The frozen doubled moment term has the four external variables outside the
terminal internal coordinate integral.  The fixed-internal-coordinate
identity in `R324EndpointIntegratedResidualBridge` may therefore be used only
after an honest global Fubini interchange.

This file performs precisely that interchange.  Its hypothesis is joint
Bochner integrability of the exact signed
`externalModeResidualSumIntegrand` on

```
(x, (y, (z, w))) × (left terminal coordinates × right terminal coordinates).
```

No norm and no termwise absolute value are introduced, so the complete
primitive covariance sum remains grouped.  Establishing the displayed joint
integrability from the initial root and the certified within-half traces is a
separate analytic obligation.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)

/-! ## Fourfold endpoint-product normal form -/

/-- Fubini expansion of the explicitly right-associated product of the four
endpoint measures.  Keeping this lemma local makes the association used by
the global joint-integrability hypothesis visible in the theorem below. -/
theorem integral_fourEndpoints
    (f : T4 → T4 → T4 → T4 → ℂ)
    (hf :
      Integrable
        (fun e : T4 × (T4 × (T4 × T4)) =>
          f e.1 e.2.1 e.2.2.1 e.2.2.2)
        (paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod paperMeasure)))) :
    (∫ e : T4 × (T4 × (T4 × T4)),
        f e.1 e.2.1 e.2.2.1 e.2.2.2
        ∂(paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod paperMeasure)))) =
      ∫ x, ∫ y, ∫ z, ∫ w, f x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure := by
  have hx :
      ∀ᵐ x ∂paperMeasure,
        Integrable
          (fun e : T4 × (T4 × T4) =>
            f x e.1 e.2.1 e.2.2)
          (paperMeasure.prod
            (paperMeasure.prod paperMeasure)) :=
    hf.prod_right_ae
  calc
    _ =
        ∫ x, ∫ e : T4 × (T4 × T4),
          f x e.1 e.2.1 e.2.2
          ∂(paperMeasure.prod
            (paperMeasure.prod paperMeasure))
          ∂paperMeasure :=
      integral_prod _ hf
    _ =
        ∫ x, ∫ y, ∫ e : T4 × T4,
          f x y e.1 e.2
          ∂(paperMeasure.prod paperMeasure)
          ∂paperMeasure ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards [hx] with x hfx
      exact integral_prod _ hfx
    _ =
        ∫ x, ∫ y, ∫ z, ∫ w, f x y z w
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards [hx] with x hfx
      apply integral_congr_ae
      filter_upwards [hfx.prod_right_ae] with y hfxy
      exact integral_prod _ hfxy

/-- Reusable four-endpoint/internal Fubini substitution.  The endpoint
evaluation is supplied as one exact signed identity for each internal
coordinate; this theorem introduces neither a norm nor a termwise sum. -/
theorem integral_fourEndpoints_with_internal_swap
    {P : Type*} [MeasurableSpace P]
    (μ : Measure P) [SFinite μ]
    (f : P → T4 → T4 → T4 → T4 → ℂ)
    (g : P → ℂ)
    (hjoint :
      Integrable
        (fun ep : (T4 × (T4 × (T4 × T4))) × P =>
          f ep.2 ep.1.1 ep.1.2.1 ep.1.2.2.1 ep.1.2.2.2)
        ((paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod paperMeasure))).prod μ))
    (heval :
      ∀ p,
        (∫ x, ∫ y, ∫ z, ∫ w, f p x y z w
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure) = g p) :
    (∫ x, ∫ y, ∫ z, ∫ w,
        ∫ p, f p x y z w ∂μ
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure) =
      ∫ p, g p ∂μ := by
  let endpointMeasure : Measure (T4 × (T4 × (T4 × T4))) :=
    paperMeasure.prod
      (paperMeasure.prod
        (paperMeasure.prod paperMeasure))
  let jointDensity :
      (T4 × (T4 × (T4 × T4))) × P → ℂ :=
    fun ep => f ep.2 ep.1.1 ep.1.2.1 ep.1.2.2.1 ep.1.2.2.2
  have hjoint' :
      Integrable jointDensity (endpointMeasure.prod μ) := by
    simpa only [endpointMeasure, jointDensity] using hjoint
  have hinter :
      Integrable
        (fun e : T4 × (T4 × (T4 × T4)) =>
          ∫ p, f p e.1 e.2.1 e.2.2.1 e.2.2.2 ∂μ)
        endpointMeasure := by
    simpa only [jointDensity] using hjoint'.integral_prod_left
  calc
    _ =
        ∫ e : T4 × (T4 × (T4 × T4)),
          ∫ p, f p e.1 e.2.1 e.2.2.1 e.2.2.2 ∂μ
          ∂endpointMeasure := by
      symm
      simpa only [endpointMeasure] using
        integral_fourEndpoints
          (fun x y z w => ∫ p, f p x y z w ∂μ)
          hinter
    _ =
        ∫ p,
          ∫ e : T4 × (T4 × (T4 × T4)),
            f p e.1 e.2.1 e.2.2.1 e.2.2.2
            ∂endpointMeasure
          ∂μ := by
      simpa only [jointDensity] using
        integral_integral_swap hjoint'
    _ = ∫ p, g p ∂μ := by
      apply integral_congr_ae
      filter_upwards [hjoint'.prod_left_ae] with p hp
      calc
        (∫ e : T4 × (T4 × (T4 × T4)),
            f p e.1 e.2.1 e.2.2.1 e.2.2.2
            ∂endpointMeasure) =
            ∫ x, ∫ y, ∫ z, ∫ w, f p x y z w
              ∂paperMeasure ∂paperMeasure
              ∂paperMeasure ∂paperMeasure := by
          simpa only [endpointMeasure, jointDensity] using
            integral_fourEndpoints
              (fun x y z w => f p x y z w) hp
        _ = g p := heval p

/-! ## Honest global endpoint/internal interchange -/

/-- Global Fubini substitution in the exact order required before passing
from the signed expression (4.18) to the endpoint estimates of §4.2,
Steps 3--4.

The left side is the frozen order: `x`, then `y`, then `z`, then `w`, with
the terminal product coordinate innermost.  The hypothesis is joint
integrability on the corresponding endpoint product, followed by the
terminal product measure.  The right side has the terminal coordinate
outside and all four endpoint integrations already evaluated by
`integral_externalModeResidualSumIntegrand`.

The complete residual primitive sum is never split and no norm is taken. -/
theorem integral_externalModeResidualSumIntegrand_fubini
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (hjoint :
      Integrable
        (fun ep :
          (T4 × (T4 × (T4 × T4))) ×
            ((terminal.left.SurvivingCoordinate → T4) ×
              (terminal.right.SurvivingCoordinate → T4)) =>
          terminal.externalModeResidualSumIntegrand
            π α β ep.2 ep.1.1 ep.1.2.1
              ep.1.2.2.1 ep.1.2.2.2)
        ((paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod paperMeasure))).prod
          ((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure)))) :
    (∫ x, ∫ y, ∫ z, ∫ w,
        ∫ p,
          terminal.externalModeResidualSumIntegrand
            π α β p x y z w
          ∂((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure))
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure) =
      ∫ p,
        terminal.endpointIntegratedResidualDensity
          π hleft hright α β p
        ∂((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate => paperMeasure)) := by
  let endpointMeasure : Measure (T4 × (T4 × (T4 × T4))) :=
    paperMeasure.prod
      (paperMeasure.prod
        (paperMeasure.prod paperMeasure))
  let internalMeasure :
      Measure
        ((terminal.left.SurvivingCoordinate → T4) ×
          (terminal.right.SurvivingCoordinate → T4)) :=
    (Measure.pi fun _ :
        terminal.left.SurvivingCoordinate => paperMeasure).prod
      (Measure.pi fun _ :
        terminal.right.SurvivingCoordinate => paperMeasure)
  let jointDensity :
      (T4 × (T4 × (T4 × T4))) ×
          ((terminal.left.SurvivingCoordinate → T4) ×
            (terminal.right.SurvivingCoordinate → T4)) → ℂ :=
    fun ep =>
      terminal.externalModeResidualSumIntegrand
        π α β ep.2 ep.1.1 ep.1.2.1
          ep.1.2.2.1 ep.1.2.2.2
  have hjoint' :
      Integrable jointDensity
        (endpointMeasure.prod internalMeasure) := by
    simpa only [endpointMeasure, internalMeasure, jointDensity] using hjoint
  have hinter :
      Integrable
        (fun e : T4 × (T4 × (T4 × T4)) =>
          ∫ p,
            terminal.externalModeResidualSumIntegrand
              π α β p e.1 e.2.1 e.2.2.1 e.2.2.2
            ∂internalMeasure)
        endpointMeasure := by
    simpa only [jointDensity] using hjoint'.integral_prod_left
  calc
    _ =
        ∫ e : T4 × (T4 × (T4 × T4)),
          ∫ p,
            terminal.externalModeResidualSumIntegrand
              π α β p e.1 e.2.1 e.2.2.1 e.2.2.2
            ∂internalMeasure
          ∂endpointMeasure := by
      symm
      simpa only [endpointMeasure, internalMeasure] using
        integral_fourEndpoints
          (fun x y z w =>
            ∫ p,
              terminal.externalModeResidualSumIntegrand
                π α β p x y z w
              ∂internalMeasure)
          hinter
    _ =
        ∫ p,
          ∫ e : T4 × (T4 × (T4 × T4)),
            terminal.externalModeResidualSumIntegrand
              π α β p e.1 e.2.1 e.2.2.1 e.2.2.2
            ∂endpointMeasure
          ∂internalMeasure := by
      simpa only [jointDensity] using
        integral_integral_swap hjoint'
    _ =
        ∫ p,
          terminal.endpointIntegratedResidualDensity
            π hleft hright α β p
          ∂internalMeasure := by
      apply integral_congr_ae
      filter_upwards [hjoint'.prod_left_ae] with p hp
      calc
        (∫ e : T4 × (T4 × (T4 × T4)),
            terminal.externalModeResidualSumIntegrand
              π α β p e.1 e.2.1 e.2.2.1 e.2.2.2
            ∂endpointMeasure) =
            ∫ x, ∫ y, ∫ z, ∫ w,
              terminal.externalModeResidualSumIntegrand
                π α β p x y z w
              ∂paperMeasure ∂paperMeasure
              ∂paperMeasure ∂paperMeasure := by
          simpa only [endpointMeasure, jointDensity] using
            integral_fourEndpoints
              (fun x y z w =>
                terminal.externalModeResidualSumIntegrand
                  π α β p x y z w)
              hp
        _ =
            terminal.endpointIntegratedResidualDensity
              π hleft hright α β p :=
          terminal.integral_externalModeResidualSumIntegrand
            π hleft hright α β p

/-- The global Fubini identity followed by the already proved
measure-preserving transport to the literal initial nested-cross carrier. -/
theorem integral_externalModeResidualSumIntegrand_fubini_eq_initialNested
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (hjoint :
      Integrable
        (fun ep :
          (T4 × (T4 × (T4 × T4))) ×
            ((terminal.left.SurvivingCoordinate → T4) ×
              (terminal.right.SurvivingCoordinate → T4)) =>
          terminal.externalModeResidualSumIntegrand
            π α β ep.2 ep.1.1 ep.1.2.1
              ep.1.2.2.1 ep.1.2.2.2)
        ((paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod paperMeasure))).prod
          ((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure)))) :
    (∫ x, ∫ y, ∫ z, ∫ w,
        ∫ p,
          terminal.externalModeResidualSumIntegrand
            π α β p x y z w
          ∂((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure))
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure) =
      ∫ v,
        terminal.initialNestedEndpointIntegratedResidualDensity
          π hleft hright α β v
        ∂(Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure) := by
  calc
    _ =
        ∫ p,
          terminal.endpointIntegratedResidualDensity
            π hleft hright α β p
          ∂((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure)) :=
      terminal.integral_externalModeResidualSumIntegrand_fubini
        π hleft hright α β hjoint
    _ = _ :=
      terminal.integral_endpointIntegratedResidualDensity_eq_initialNested
        π hleft hright α β

end R324TwoHalfTerminalData

end

end Anderson4D
