import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointRouteCases

/-!
# Parameterized direct/direct half splice

This is the only parameter-carrier composition not already named in
`R324PaperEndpointTwoHalfSplice`.  The complete alternating transport is
performed sectionwise while the expression is signed.  Its multiplier is
then moved back inside the terminal coefficient, and the two free endpoint
variables are Fourier-integrated by
`integral_singleParameter_incomingPhasedResidualDensity_eq_directOutgoing`.
No norm occurs.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix
namespace R324WithinHalfAlternatingTransport

variable {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}

/-- Complete signed `DD` operation with one arbitrary untouched parameter.
The parameter is the already completed opposite half in the `4 x 4`
assembly. -/
theorem
    lamEps_pow_integral_initialResidual_eq_singleParameter_directDirect
    (transport : R324WithinHalfAlternatingTransport
      (R324WithinHalfResidualPrefix.initial rho lam eps pairing))
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (red : U -> (transport.final.SurvivingCoordinate -> T4) -> Complex)
    (incomingMode outgoingMode : Z4)
    (hcurrent :
      Integrable
        (fun q : (T4 × U) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate -> T4) =>
          (R324WithinHalfResidualPrefix.initial rho lam eps pairing
            |>.incomingPhasedResidualDensity
              (charT4 outgoingMode q.1.1 *
                red q.1.2 (transport.projection q.2))
              incomingMode rho eps 0 q.1.1 q.2))
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure)))
    (hactive : transport.final.state.active.Nonempty)
    (hedge :
      transport.final.state.edges
          (transport.final.terminalOutgoingEdgeSlot hactive) = greenFn)
    (hterminal :
      Integrable
        (fun q : (T4 × U) ×
              (transport.final.SurvivingCoordinate -> T4) =>
          transport.final.incomingPhasedResidualDensity
            (charT4 outgoingMode q.1.1 *
              (transport.multiplier incomingMode * red q.1.2 q.2))
            incomingMode rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod muU).prod
          (Measure.pi fun _ => paperMeasure))) :
    (lamEps lam eps : Complex) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) *
        (∫ q : (T4 × U) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate -> T4),
          (R324WithinHalfResidualPrefix.initial rho lam eps pairing
            |>.incomingPhasedResidualDensity
              (charT4 outgoingMode q.1.1 *
                red q.1.2 (transport.projection q.2))
              incomingMode rho eps 0 q.1.1 q.2)
          ∂((paperMeasure.prod muU).prod
            (Measure.pi fun _ => paperMeasure))) =
      ∫ u : U,
        ∫ v : transport.final.SurvivingCoordinate -> T4,
          (transport.multiplier incomingMode * red u v) *
            charT4 incomingMode
              (transport.final.terminalIncomingAnchor
                (transport.final.reconstruct v)) *
            ((transport.final.endpointErasedSignedChain
              hactive 0 0 (transport.final.reconstruct v) : Real) : Complex) *
            translatedGreenMode outgoingMode
              (transport.final.terminalOutgoingAnchor hactive
                (transport.final.reconstruct v))
          ∂Measure.pi fun _ => paperMeasure
        ∂muU := by
  let initial := R324WithinHalfResidualPrefix.initial rho lam eps pairing
  let muInitial :=
    Measure.pi fun _ : initial.SurvivingCoordinate => paperMeasure
  let muFinal :=
    Measure.pi fun _ : transport.final.SurvivingCoordinate => paperMeasure
  let terminalIntegrand :
      (T4 × U) ×
        (transport.final.SurvivingCoordinate -> T4) -> Complex :=
    fun q =>
      transport.final.incomingPhasedResidualDensity
        (charT4 outgoingMode q.1.1 *
          (transport.multiplier incomingMode * red q.1.2 q.2))
        incomingMode rho eps 0 q.1.1 q.2
  have htransport :
      (lamEps lam eps : Complex) ^ (2 * initial.remainingOrder) *
          (∫ q : (T4 × U) ×
                (initial.SurvivingCoordinate -> T4),
            initial.incomingPhasedResidualDensity
              (charT4 outgoingMode q.1.1 *
                red q.1.2 (transport.projection q.2))
              incomingMode rho eps 0 q.1.1 q.2
            ∂((paperMeasure.prod muU).prod muInitial)) =
        ∫ q : T4 × U,
          ∫ v : transport.final.SurvivingCoordinate -> T4,
            terminalIntegrand (q, v) ∂muFinal
          ∂(paperMeasure.prod muU) := by
    rw [integral_prod _ hcurrent, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hcurrent.prod_right_ae] with q hq
    have hsection :=
      transport.lamEps_pow_integral_incomingPhasedResidualDensity_eq_multiplier_mul_final
        0 q.1 incomingMode
        (fun v => charT4 outgoingMode q.1 * red q.2 v) hq
    calc
      (lamEps lam eps : Complex) ^ (2 * initial.remainingOrder) *
            (∫ w : initial.SurvivingCoordinate -> T4,
              initial.incomingPhasedResidualDensity
                (charT4 outgoingMode q.1 *
                  red q.2 (transport.projection w))
                incomingMode rho eps 0 q.1 w ∂muInitial) =
          transport.multiplier incomingMode *
            ∫ v : transport.final.SurvivingCoordinate -> T4,
              transport.final.incomingPhasedResidualDensity
                (charT4 outgoingMode q.1 * red q.2 v)
                incomingMode rho eps 0 q.1 v ∂muFinal := hsection
      _ = ∫ v : transport.final.SurvivingCoordinate -> T4,
            terminalIntegrand (q, v) ∂muFinal := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with v
        dsimp only [terminalIntegrand]
        rw [← transport.final.incomingPhasedResidualDensity_const_mul]
        congr 1
        ring
  calc
    (lamEps lam eps : Complex) ^
          (2 * (R324WithinHalfResidualPrefix.initial
            rho lam eps pairing).remainingOrder) *
        (∫ q : (T4 × U) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate -> T4),
          (R324WithinHalfResidualPrefix.initial rho lam eps pairing
            |>.incomingPhasedResidualDensity
              (charT4 outgoingMode q.1.1 *
                red q.1.2 (transport.projection q.2))
              incomingMode rho eps 0 q.1.1 q.2)
          ∂((paperMeasure.prod muU).prod
            (Measure.pi fun _ => paperMeasure))) =
        ∫ q : T4 × U,
          ∫ v : transport.final.SurvivingCoordinate -> T4,
            terminalIntegrand (q, v) ∂muFinal
          ∂(paperMeasure.prod muU) := by
      simpa only [initial, muInitial] using htransport
    _ = ∫ q : (T4 × U) ×
          (transport.final.SurvivingCoordinate -> T4),
        terminalIntegrand q
        ∂((paperMeasure.prod muU).prod muFinal) := by
      rw [integral_prod _ hterminal]
    _ = _ := by
      simpa only [terminalIntegrand, muFinal] using
        integral_singleParameter_incomingPhasedResidualDensity_eq_directOutgoing
          transport.final transport.final_remaining hactive hedge
          muU
          (fun u v => transport.multiplier incomingMode * red u v)
          outgoingMode incomingMode hterminal

end R324WithinHalfAlternatingTransport
end R324WithinHalfResidualPrefix

end

end Anderson4D
