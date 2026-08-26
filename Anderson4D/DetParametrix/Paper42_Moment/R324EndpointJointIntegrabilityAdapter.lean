import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointIntegratedResidualFubini

/-!
# Joint-integrability adapter for the R-324 endpoint bridge

The global endpoint/internal Fubini theorem requires joint integrability of
the character-decorated terminal residual-sum density.  The four Fourier
characters are bounded measurable multipliers of norm one, so the exact
upstream analytic obligation is instead joint integrability of the
*unphased* `terminalResidualSumPhysicalCore`.

This file isolates that obligation and proves that it produces the exact
`hjoint` hypothesis, without splitting the complete residual primitive sum
or taking a termwise norm.  It also supplies direct composition theorems for
the two Fubini conclusions.

The predicate below packages the unphased joint-integrability hypothesis.
The theorems in this file show that it suffices for the character-decorated
Fubini conclusions without splitting the signed primitive sum.
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

/-- The exact unphased analytic certificate for the global endpoint/internal
Fubini bridge. Its endpoint association agrees literally
with `integral_externalModeResidualSumIntegrand_fubini`. -/
def TerminalResidualSumJointIntegrable
    (π : κp.singles ≃ κm.singles) : Prop :=
  Integrable
    (fun ep :
      (T4 × (T4 × (T4 × T4))) ×
        ((terminal.left.SurvivingCoordinate → T4) ×
          (terminal.right.SurvivingCoordinate → T4)) =>
      terminal.terminalResidualSumPhysicalCore
        π ep.1.1 ep.1.2.1 ep.1.2.2.1 ep.1.2.2.2 ep.2)
    ((paperMeasure.prod
        (paperMeasure.prod
          (paperMeasure.prod paperMeasure))).prod
      ((Measure.pi fun _ :
          terminal.left.SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ :
          terminal.right.SurvivingCoordinate => paperMeasure)))

/-- The unphased terminal certificate produces the exact `hjoint`
hypothesis of the global Fubini theorem.  Only multiplication by the four
unit-norm characters is used; the grouped residual primitive sum remains
inside `terminalResidualSumPhysicalCore`. -/
theorem integrable_externalModeResidualSumIntegrand_of_terminal
    (π : κp.singles ≃ κm.singles)
    (α β : Z4)
    (hterminal :
      terminal.TerminalResidualSumJointIntegrable π) :
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
            terminal.right.SurvivingCoordinate => paperMeasure))) := by
  let phase :
      ((T4 × (T4 × (T4 × T4))) ×
        ((terminal.left.SurvivingCoordinate → T4) ×
          (terminal.right.SurvivingCoordinate → T4))) → ℂ :=
    fun ep =>
      charT4 α ep.1.1 *
        charT4 β ep.1.2.1 *
        charT4 (-α) ep.1.2.2.1 *
        charT4 (-β) ep.1.2.2.2
  have he :
      Measurable fun ep :
          (T4 × (T4 × (T4 × T4))) ×
            ((terminal.left.SurvivingCoordinate → T4) ×
              (terminal.right.SurvivingCoordinate → T4)) =>
        ep.1 :=
    measurable_fst
  have hx :
      Measurable fun ep :
          (T4 × (T4 × (T4 × T4))) ×
            ((terminal.left.SurvivingCoordinate → T4) ×
              (terminal.right.SurvivingCoordinate → T4)) =>
        ep.1.1 :=
    measurable_fst.comp he
  have hy :
      Measurable fun ep :
          (T4 × (T4 × (T4 × T4))) ×
            ((terminal.left.SurvivingCoordinate → T4) ×
              (terminal.right.SurvivingCoordinate → T4)) =>
        ep.1.2.1 :=
    measurable_fst.comp (measurable_snd.comp he)
  have hz :
      Measurable fun ep :
          (T4 × (T4 × (T4 × T4))) ×
            ((terminal.left.SurvivingCoordinate → T4) ×
              (terminal.right.SurvivingCoordinate → T4)) =>
        ep.1.2.2.1 :=
    measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp he))
  have hw :
      Measurable fun ep :
          (T4 × (T4 × (T4 × T4))) ×
            ((terminal.left.SurvivingCoordinate → T4) ×
              (terminal.right.SurvivingCoordinate → T4)) =>
        ep.1.2.2.2 :=
    measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp he))
  have hphaseMeas : Measurable phase := by
    exact
      ((((continuous_charT4 α).measurable.comp hx).mul
        ((continuous_charT4 β).measurable.comp hy)).mul
        ((continuous_charT4 (-α)).measurable.comp hz)).mul
        ((continuous_charT4 (-β)).measurable.comp hw)
  have hphaseBound :
      ∀ ep, ‖phase ep‖ ≤ 1 := by
    intro ep
    simp only [phase, norm_mul, norm_charT4, mul_one, le_refl]
  have hproduct :=
    hterminal.mul_bdd hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hphaseBound)
  apply hproduct.congr
  filter_upwards with ep
  unfold externalModeResidualSumIntegrand phase
  ring

/-- The unphased terminal certificate discharges the global Fubini premise
and evaluates all four endpoint integrations before the terminal internal
integral. -/
theorem integral_externalModeResidualSumIntegrand_fubini_of_terminal
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (hterminal :
      terminal.TerminalResidualSumJointIntegrable π) :
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
            terminal.right.SurvivingCoordinate => paperMeasure)) :=
  terminal.integral_externalModeResidualSumIntegrand_fubini
    π hleft hright α β
    (terminal.integrable_externalModeResidualSumIntegrand_of_terminal
      π α β hterminal)

/-- The preceding Fubini evaluation followed by the exact
measure-preserving transport to the literal initial nested-cross carrier. -/
theorem
    integral_externalModeResidualSumIntegrand_fubini_eq_initialNested_of_terminal
    (π : κp.singles ≃ κm.singles)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (hterminal :
      terminal.TerminalResidualSumJointIntegrable π) :
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
          terminal.NestedCoordinate π => paperMeasure) :=
  terminal.integral_externalModeResidualSumIntegrand_fubini_eq_initialNested
    π hleft hright α β
    (terminal.integrable_externalModeResidualSumIntegrand_of_terminal
      π α β hterminal)

end R324TwoHalfTerminalData

end

end Anderson4D
