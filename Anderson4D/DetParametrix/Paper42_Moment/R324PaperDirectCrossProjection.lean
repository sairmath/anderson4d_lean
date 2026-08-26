import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointRoutes
import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualSumTerminalProjection

/-!
# Cross-factor projection for a direct incoming half

These are the two coordinate identities used by the direct-incoming
branches of paper Step 4(A).  The residual primitive factor is supported on
final singles, so it is unchanged first by the complete alternating
transport and, in the retained-outgoing case, by the endpoint stop followed
by removal of the terminal block.

No integral, norm, or estimate occurs here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}

/-- A complete alternating transport of the left initial carrier preserves
the cross primitive factor. -/
theorem r324ResidualPrimitiveSumProduct_eq_leftDirectDriverProjection
    (transport : R324WithinHalfAlternatingTransport
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP))
    (pi : kappaP.singles ≃ kappaM.singles)
    (vl : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4)
    (vr : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).SurvivingCoordinate → T4) :
    r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          (vl, vr)) =
      r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          transport.final
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          (transport.projection vl, vr)) := by
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro q hq
  by_cases hqLeft : q.val < m
  · obtain ⟨i, hiFinal, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive hq hqLeft
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_leftMomentIndex]
    let iFinal : transport.final.SurvivingCoordinate :=
      ⟨i, by
        rw [transport.final_active_eq_finalActive]
        exact hiFinal⟩
    exact transport.reconstruct_projection vl iFinal
  · obtain ⟨i, _hiFinal, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive hq (by omega)
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_rightMomentIndex]

/-- A retained outgoing terminal of the left direct-incoming half preserves
the cross primitive factor after both its stop projection and its terminal
tuple split. -/
theorem r324ResidualPrimitiveSumProduct_eq_leftDirectOutgoingTerminalPost
    (outgoing : R324PaperOutgoingEndpointTerminal
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP))
    (pi : kappaP.singles ≃ kappaM.singles)
    (vl : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4)
    (vr : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).SurvivingCoordinate → T4) :
    r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          (vl, vr)) =
      r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          outgoing.terminalPost
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            outgoing.terminalData.terminal []
            outgoing.endpoint.stop_remaining
            (outgoing.endpoint.projection vl)).2, vr)) := by
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro q hq
  by_cases hqLeft : q.val < m
  · obtain ⟨i, hiFinal, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive hq hqLeft
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_leftMomentIndex]
    have hiStop : i ∈ outgoing.endpoint.stop.state.active :=
      outgoing.endpoint.finalActive_subset_stop_active hiFinal
    have hiPost : i ∈ outgoing.terminalPost.state.active := by
      rw [outgoing.terminalPost_active_eq_finalActive]
      exact hiFinal
    let iStop : outgoing.endpoint.stop.SurvivingCoordinate := ⟨i, hiStop⟩
    let iPost : outgoing.terminalPost.SurvivingCoordinate := ⟨i, hiPost⟩
    let iStopFromPost : outgoing.endpoint.stop.SurvivingCoordinate :=
      outgoing.endpoint.stop.postSurvivingCoordinate
        outgoing.terminalData.terminal []
        outgoing.endpoint.stop_remaining iPost
    calc
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP).reconstruct
          vl i =
        outgoing.endpoint.stop.reconstruct
          (outgoing.endpoint.projection vl) i :=
        outgoing.endpoint.reconstruct_projection vl iStop
      _ = outgoing.endpoint.projection vl iStop :=
        outgoing.endpoint.stop.reconstruct_surviving
          (outgoing.endpoint.projection vl) iStop
      _ = outgoing.endpoint.projection vl iStopFromPost := by
        apply congrArg (outgoing.endpoint.projection vl)
        apply Subtype.ext
        rfl
      _ =
          (outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            outgoing.terminalData.terminal []
            outgoing.endpoint.stop_remaining
            (outgoing.endpoint.projection vl)).2 iPost := by
        exact
          (outgoing.endpoint.stop
            |>.splitSurvivingPiMeasurableEquiv_apply_snd
              outgoing.terminalData.terminal []
              outgoing.endpoint.stop_remaining
              (outgoing.endpoint.projection vl) iPost).symm
      _ = outgoing.terminalPost.reconstruct
          ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            outgoing.terminalData.terminal []
            outgoing.endpoint.stop_remaining
            (outgoing.endpoint.projection vl)).2) i := by
        exact
          (outgoing.terminalPost.reconstruct_surviving
            ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
              outgoing.terminalData.terminal []
              outgoing.endpoint.stop_remaining
              (outgoing.endpoint.projection vl)).2) iPost).symm
  · obtain ⟨i, _hiFinal, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive hq (by omega)
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_rightMomentIndex]

end R324WithinHalfResidualPrefix

end

end Anderson4D
