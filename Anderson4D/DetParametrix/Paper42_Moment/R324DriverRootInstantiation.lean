import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingPhasedTrace
import Anderson4D.DetParametrix.Paper42_Moment.R324AlternatingDriver
import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalBoundaryLegFourier

/-!
# Driver instantiation at the genuine refined physical root

The alternating driver transports the incoming phased residual density
from any reachable residual prefix to a terminal prefix with empty
remaining list, accumulating one collapsed-head factor per exceptional
stop into its multiplier.  This module instantiates the driver at the
genuine refined physical root: the after-head prefix produced by the
seam-2 endpoint is transported a.e. in the root parameter, with the
refined-root outer coefficient factored through the driver's terminal
projection.

Unlike the phased-trace endpoint, no `OrdinaryAlong` hypothesis is
taken: slot-zero-fed heads inside the after-head suffix are absorbed by
the driver's exceptional collapse and appear as factors of the terminal
multiplier.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

/-! ## Terminal evaluation of the residual factors -/

section Terminal

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)

/-- No outgoing production slots remain at a terminal prefix. -/
theorem remainingOutgoingSlots_of_remaining_nil
    (hnil : res.remaining = []) :
    res.remainingOutgoingSlots = [] := by
  unfold remainingOutgoingSlots
  rw [hnil]
  rfl

/-- The signed-difference product of a terminal prefix is one. -/
theorem residualDifferenceProduct_of_remaining_nil
    (hnil : res.remaining = [])
    (x y : T4) (v : Fin m → T4) :
    res.residualDifferenceProduct x y v = 1 := by
  unfold residualDifferenceProduct
  rw [hnil]
  rfl

/-- The primitive covariance product of a terminal prefix is one. -/
theorem residualPrimitiveProduct_of_remaining_nil
    (hnil : res.remaining = [])
    (ρ' : SmoothCutoff) (ε' : ℝ) (v : Fin m → T4) :
    res.residualPrimitiveProduct ρ' ε' v = 1 := by
  unfold residualPrimitiveProduct
  haveI : IsEmpty (Fin res.remaining.length) := by
    rw [hnil]
    exact Fin.isEmpty'
  exact Finset.prod_of_isEmpty _

/-- At a terminal prefix every ordinary sparse-chain factor is the named
edge at its displacement on active slots and one elsewhere: no slot is
reserved for a remaining signed difference. -/
theorem residualChainEdgeFactor_of_remaining_nil
    (hnil : res.remaining = [])
    (x y : T4) (v : Fin m → T4)
    (edge : Fin (m + 1)) :
    res.residualChainEdgeFactor x y v edge =
      if edge ∈ res.activeEdgeSlots then
        res.state.edges edge
          (res.edgeDisplacement x y v edge)
      else 1 := by
  unfold residualChainEdgeFactor
  rw [res.remainingOutgoingSlots_of_remaining_nil hnil]
  simp only [List.not_mem_nil, if_false]

/-- The slot-zero-erased chain product of a nonempty completed
half-chain is the outgoing boundary factor times the endpoint-erased
interior product. -/
theorem incomingErasedResidualChainProduct_eq_outgoing_mul_endpointErased
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : Fin m → T4) :
    res.incomingErasedResidualChainProduct x y v =
      res.outgoingBoundaryFactor hactive x y v *
        res.endpointErasedSignedChain hactive x y v := by
  unfold incomingErasedResidualChainProduct
  calc
    (∏ edge ∈
        (Finset.univ : Finset (Fin (m + 1))).erase 0,
      res.residualChainEdgeFactor x y v edge) =
        ∏ edge ∈ res.activeEdgeSlots.erase 0,
          res.residualChainEdgeFactor x y v edge := by
      symm
      apply Finset.prod_subset
        (Finset.erase_subset_erase 0
          (Finset.subset_univ _))
      intro edge hedgeUniv hedge
      have hnotActive : edge ∉ res.activeEdgeSlots := by
        intro hmem
        exact hedge
          (Finset.mem_erase.mpr
            ⟨(Finset.mem_erase.mp hedgeUniv).1, hmem⟩)
      unfold residualChainEdgeFactor
      rw [if_neg hnotActive]
    _ =
        res.residualChainEdgeFactor x y v
            (res.terminalOutgoingEdgeSlot hactive) *
          ∏ edge ∈
              res.endpointErasedActiveEdgeSlots hactive,
            res.residualChainEdgeFactor x y v edge := by
      have houtMem :
          res.terminalOutgoingEdgeSlot hactive ∈
            res.activeEdgeSlots.erase 0 :=
        Finset.mem_erase.mpr
          ⟨res.terminalOutgoingEdgeSlot_ne_zero hactive,
            res.terminalOutgoingEdgeSlot_mem_activeEdgeSlots
              hactive⟩
      exact
        (Finset.mul_prod_erase
          (res.activeEdgeSlots.erase 0)
          (fun edge =>
            res.residualChainEdgeFactor x y v edge)
          houtMem).symm
    _ = _ := rfl

/-- **Terminal form of the slot-zero-erased residual core.**  At a
terminal prefix with nonempty active carrier, the difference and
primitive products are exhausted and only the surviving signed chain
remains: the outgoing boundary Green factor times the endpoint-erased
interior pair product. -/
theorem terminal_incomingErasedResidualIntegrand_eq
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4) (v : Fin m → T4) :
    res.incomingErasedResidualIntegrand ρ' ε' x y v =
      res.outgoingBoundaryFactor hactive x y v *
        res.endpointErasedSignedChain hactive x y v := by
  unfold incomingErasedResidualIntegrand
  rw [res.residualDifferenceProduct_of_remaining_nil hnil,
    res.residualPrimitiveProduct_of_remaining_nil hnil,
    mul_one, mul_one,
    res.incomingErasedResidualChainProduct_eq_outgoing_mul_endpointErased
      hactive]

/-- With a nonempty active carrier the incoming phase anchor is the
endpoint-independent first surviving internal point. -/
theorem incomingPhaseAnchor_eq_terminalIncomingAnchor
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : res.SurvivingCoordinate → T4) :
    res.incomingPhaseAnchor x y v =
      res.terminalIncomingAnchor (res.reconstruct v) := by
  unfold incomingPhaseAnchor
  exact
    res.assemble_edgeSuccessor_zero_eq_terminalIncomingAnchor
      hactive x y (res.reconstruct v)

/-- **Terminal evaluation of the incoming phased residual density.**  At
a terminal prefix with nonempty active carrier the density is the
coefficient, the incoming character at the endpoint-independent first
surviving internal point, and the explicit product of the surviving
outgoing Green boundary factor with the endpoint-erased interior signed
chain. -/
theorem terminal_incomingPhasedResidualDensity_eq
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (coefficient : ℂ) (k : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ) (x y : T4)
    (v : res.SurvivingCoordinate → T4) :
    res.incomingPhasedResidualDensity
        coefficient k ρ' ε' x y v =
      coefficient *
        charT4 k
          (res.terminalIncomingAnchor (res.reconstruct v)) *
        ((res.outgoingBoundaryFactor hactive x y
            (res.reconstruct v) *
          res.endpointErasedSignedChain hactive x y
            (res.reconstruct v) : ℝ) : ℂ) := by
  unfold incomingPhasedResidualDensity
  rw [res.incomingPhaseAnchor_eq_terminalIncomingAnchor
      hactive,
    res.terminal_incomingErasedResidualIntegrand_eq
      hnil hactive]

/-- With an empty active carrier the incoming edge points directly at
the outgoing external endpoint. -/
theorem edgeSuccessor_zero_eq_last_of_active_empty
    (hempty : res.state.active = ∅) :
    res.edgeSuccessor 0 = Fin.last (m + 1) := by
  have hmem := res.edgeSuccessor_mem_candidates 0
  rw [edgeSuccessorCandidates, hempty] at hmem
  simpa using hmem

/-- With an empty active carrier only the incoming production slot is
active. -/
theorem activeEdgeSlots_of_active_empty
    (hempty : res.state.active = ∅) :
    res.activeEdgeSlots = {0} := by
  unfold activeEdgeSlots
  rw [hempty]
  simp

/-- With an empty active carrier the slot-zero-erased chain product is
one. -/
theorem incomingErasedResidualChainProduct_of_active_empty
    (hempty : res.state.active = ∅)
    (x y : T4) (v : Fin m → T4) :
    res.incomingErasedResidualChainProduct x y v = 1 := by
  unfold incomingErasedResidualChainProduct
  apply Finset.prod_eq_one
  intro edge hedge
  have hnotActive : edge ∉ res.activeEdgeSlots := by
    rw [res.activeEdgeSlots_of_active_empty hempty]
    intro hmem
    exact (Finset.mem_erase.mp hedge).1
      (Finset.mem_singleton.mp hmem)
  unfold residualChainEdgeFactor
  rw [if_neg hnotActive]

/-- **Degenerate terminal evaluation.**  At a terminal prefix whose
active carrier is empty, every interior factor is exhausted and the
phased density is the coefficient times the incoming character read
directly at the outgoing external endpoint. -/
theorem terminal_incomingPhasedResidualDensity_eq_of_active_empty
    (hnil : res.remaining = [])
    (hempty : res.state.active = ∅)
    (coefficient : ℂ) (k : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ) (x y : T4)
    (v : res.SurvivingCoordinate → T4) :
    res.incomingPhasedResidualDensity
        coefficient k ρ' ε' x y v =
      coefficient * charT4 k y := by
  unfold incomingPhasedResidualDensity incomingPhaseAnchor
  rw [res.edgeSuccessor_zero_eq_last_of_active_empty
      hempty,
    assemble_last]
  unfold incomingErasedResidualIntegrand
  rw [res.residualDifferenceProduct_of_remaining_nil hnil,
    res.residualPrimitiveProduct_of_remaining_nil hnil,
    res.incomingErasedResidualChainProduct_of_active_empty
      hempty]
  simp

/-- **Fourier evaluation of the terminal outgoing leg.**  Integrating
the terminal phased density against an outgoing character in the free
outgoing endpoint produces the translated Green mode at the last
surviving internal point; the incoming character and the
endpoint-erased interior chain are endpoint-independent and factor out.
This is the identity consumed by the endpoint branch summation once the
outgoing character has been split off the root coefficient. -/
theorem integral_char_mul_terminal_incomingPhasedResidualDensity_eq
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge :
      res.state.edges
          (res.terminalOutgoingEdgeSlot hactive) =
        greenFn)
    (coefficient : ℂ) (k β : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ) (x : T4)
    (v : res.SurvivingCoordinate → T4) :
    (∫ y : T4,
        charT4 β y *
          res.incomingPhasedResidualDensity
            coefficient k ρ' ε' x y v
        ∂paperMeasure) =
      coefficient *
        charT4 k
          (res.terminalIncomingAnchor (res.reconstruct v)) *
        ((res.endpointErasedSignedChain hactive 0 0
          (res.reconstruct v) : ℝ) : ℂ) *
        translatedGreenMode β
          (res.terminalOutgoingAnchor hactive
            (res.reconstruct v)) := by
  have hpt :
      ∀ y : T4,
        charT4 β y *
            res.incomingPhasedResidualDensity
              coefficient k ρ' ε' x y v =
          (coefficient *
              charT4 k
                (res.terminalIncomingAnchor
                  (res.reconstruct v)) *
              ((res.endpointErasedSignedChain hactive 0 0
                (res.reconstruct v) : ℝ) : ℂ)) *
            (charT4 β y *
              (res.outgoingBoundaryFactor hactive x y
                (res.reconstruct v) : ℂ)) := by
    intro y
    rw [res.terminal_incomingPhasedResidualDensity_eq
        hnil hactive coefficient k ρ' ε' x y v,
      res.endpointErasedSignedChain_eq_zeroEndpoints
        hactive x y]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul,
    res.integral_char_mul_outgoingBoundaryFactor_eq
      hnil hactive hedge β x (res.reconstruct v)]

end Terminal

namespace R324WithinHalfAlternatingTransport

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- The driver's terminal prefix has consumed the whole analytic
schedule: an empty remaining list forces the processed list to be the
literal schedule. -/
theorem final_processed_eq_schedule
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    (t : R324WithinHalfAlternatingTransport res) :
    t.final.state.processed = r322AnalyticSchedule pairing := by
  have h := t.final.schedule_eq
  rw [t.final_remaining, List.append_nil] at h
  exact h.symm

/-- The driver-terminal active carrier is the final active set of the
frozen pairing: the branch dichotomy (nonempty against empty) for the
terminal evaluation is decided by the pairing combinatorics alone. -/
theorem final_active_eq_finalActive
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    (t : R324WithinHalfAlternatingTransport res) :
    t.final.state.active = finalActive pairing :=
  t.final.active_eq_finalActive_of_processed_eq_schedule
    t.final_processed_eq_schedule

/-- Reconstruction at every driver-terminal coordinate is unchanged by
the driver projection. -/
theorem reconstruct_projection
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    (t : R324WithinHalfAlternatingTransport res)
    (v : res.SurvivingCoordinate → T4)
    (i : t.final.SurvivingCoordinate) :
    res.reconstruct v i.1 =
      t.final.reconstruct (t.projection v) i.1 := by
  calc
    res.reconstruct v i.1 =
        res.reconstruct v (t.embedding i).1 := by
      exact congrArg (res.reconstruct v)
        (t.embedding_val i).symm
    _ = v (t.embedding i) :=
      res.reconstruct_surviving v (t.embedding i)
    _ = t.projection v i :=
      (t.projection_apply v i).symm
    _ =
        t.final.reconstruct (t.projection v) i.1 :=
      (t.final.reconstruct_surviving
        (t.projection v) i).symm

end R324WithinHalfAlternatingTransport

namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- The alternating transport of the complete after-head suffix, built
from the local block provider and the certificate transported to the
exceptional stop.  Later slot-zero-fed heads are
absorbed into the driver multiplier. -/
def afterHeadAlternatingTransport
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κp) :
    R324WithinHalfAlternatingTransport
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq) :=
  R324WithinHalfAlternatingTransport.of_localBlockProvider
    hε hε1 provider
    (data.trace.stopPrefix.afterHead
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq)
    (r324WithinHalfUpdatedEdgeScale
      data.stopContext data.stopScale C lam K)
    (provider data.trace.stopPrefix
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      data.stopScale data.stopCertificate).2

/-- The untouched refined-root outer functional read on the terminal
carrier of an alternating transport of the after-head prefix: the
retained endpoint characters, the untouched right initial residual, and
the cross-cut primitive factor reconstructed from the driver-terminal
prefix. -/
def incomingExceptionalRefinedRootDriverPostOuter
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (t :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm)
    (u :
      t.final.SurvivingCoordinate → T4) : ℂ :=
  charT4 β ω.1.1 *
    charT4 (-α) ω.1.2.1 *
    charT4 (-β) ω.1.2.2 *
    (((R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).residualIntegrand
      ρ ε ω.1.2.1 ω.1.2.2
      ((R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).reconstruct ω.2) : ℂ) *
      (r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        (r324TwoHalfRootDoubledReconstruct
          t.final
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κm)
          (u, ω.2)) : ℂ))

/-- **Driver-terminal factorization of the refined-root outer
functional.**  The cross-cut primitive factor reads only coordinates on
the doubled residual carrier, all of which survive to the driver's
terminal prefix; hence the whole refined-root outer functional factors
through the projection of any alternating transport of the after-head
prefix. -/
theorem incomingExceptionalRefinedRootPostOuter_eq_driverProjection
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (t :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) :
    data.incomingExceptionalRefinedRootPostOuter
        α β π ω v =
      data.incomingExceptionalRefinedRootDriverPostOuter
        t α β π ω (t.projection v) := by
  have hsum :
      r324ResidualPrimitiveSumProduct
          ρ ε κp κm π
          (r324TwoHalfRootDoubledReconstruct
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq)
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm)
            (v, ω.2)) =
        r324ResidualPrimitiveSumProduct
          ρ ε κp κm π
          (r324TwoHalfRootDoubledReconstruct
            t.final
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm)
            (t.projection v, ω.2)) := by
    apply r324ResidualPrimitiveSumProduct_congr_on_active
    intro j hj
    by_cases hleft : j.val < m
    · obtain ⟨i, hi, hji⟩ :=
        exists_leftMomentIndex_of_mem_momentResidualActive
          hj hleft
      subst j
      let i' : t.final.SurvivingCoordinate :=
        ⟨i, by
          rw [
            t.final.active_eq_finalActive_of_processed_eq_schedule
              t.final_processed_eq_schedule]
          exact hi⟩
      unfold r324TwoHalfRootDoubledReconstruct
      rw [momentDoubleFinEquiv_symm_leftMomentIndex]
      exact t.reconstruct_projection v i'
    · obtain ⟨i, hi, hji⟩ :=
        exists_rightMomentIndex_of_mem_momentResidualActive
          hj (by omega)
      subst j
      unfold r324TwoHalfRootDoubledReconstruct
      rw [momentDoubleFinEquiv_symm_rightMomentIndex]
  unfold incomingExceptionalRefinedRootPostOuter
    incomingExceptionalRefinedRootDriverPostOuter
  rw [hsum]

/-- The collapsed-head coefficient of the genuine refined root, read on
the driver's terminal carrier: squared second-order decay, primitive
Step-4 defect of the exceptional head, and the driver-terminal form of
the untouched refined outer functional. -/
def incomingExceptionalRefinedRootDriverCoefficient
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (t :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm)
    (u :
      t.final.SurvivingCoordinate → T4) : ℂ :=
  (paperSecondOrderModeDecay α : ℂ) ^ 2 *
    incomingExceptionalPrimitiveDefect ρ lam ε
      (residualBlockOrder data.terminal.2)
      data.stopContext.one_le_blockOrder
      data.stopContext.internalEdges α *
    data.incomingExceptionalRefinedRootDriverPostOuter
      t α β π ω u

/-- The collapsed-head refined-root coefficient factors through the
projection of any alternating transport of the after-head prefix. -/
theorem incomingExceptionalPostCoefficient_refinedRoot_eq_driverProjection
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (t :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) :
    data.incomingExceptionalPostCoefficient
        α
        (data.incomingExceptionalRefinedRootPostOuter
          α β π)
        ω v =
      data.incomingExceptionalRefinedRootDriverCoefficient
        t α β π ω (t.projection v) := by
  unfold incomingExceptionalPostCoefficient
    incomingExceptionalRefinedRootDriverCoefficient
  rw [
    data.incomingExceptionalRefinedRootPostOuter_eq_driverProjection
      t α β π ω v]

/-- At a fixed root parameter, the after-head phased integrand of the
genuine refined root is the after-head phased density whose coefficient
is the driver-terminal refined coefficient read through the driver
projection. -/
theorem incomingExceptionalAfterHeadPhasedIntegrand_refinedRoot_driver_section_eq
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (t :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm) :
    (fun v :
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4 =>
      data.incomingExceptionalAfterHeadPhasedIntegrand
        α
        (fun ω' :
            R324IncomingExceptionalRootParameter
              ρ lam ε κm =>
          ω'.1.1)
        (data.incomingExceptionalRefinedRootPostOuter
          α β π)
        (ω, v)) =
      fun v =>
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).incomingPhasedResidualDensity
          (data.incomingExceptionalRefinedRootDriverCoefficient
            t α β π ω
            (t.projection v))
          α ρ ε 0 ω.1.1 v := by
  funext v
  show
    (data.trace.stopPrefix.afterHead
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq).incomingPhasedResidualDensity
        (data.incomingExceptionalPostCoefficient
          α
          (data.incomingExceptionalRefinedRootPostOuter
            α β π)
          ω v)
        α ρ ε 0 ω.1.1 v =
      _
  rw [
    data.incomingExceptionalPostCoefficient_refinedRoot_eq_driverProjection
      t α β π ω v]

/-- **Driver instantiation at the genuine refined root.**  The weighted
single-fibre refined physical integral, with the exceptional head
absorbed by the base case and the whole after-head suffix absorbed by
the alternating driver: the right-hand side integrates the
driver-terminal phased density over the root parameter and the terminal
coordinates, with the driver multiplier times the collapsed-head refined
coefficient read on the terminal carrier.  No ordinariness hypothesis is
taken. -/
theorem lamEps_pow_r324RefinedPhysicalIntegral_eq_driverTerminal
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (t :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (α β : Z4) :
    (lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        r324RefinedPhysicalIntegral
          ρ ε m α β p =
      ∫ ω :
          R324IncomingExceptionalRootParameter
            ρ lam ε e₀.2.1,
        (∫ u :
            t.final.SurvivingCoordinate → T4,
          t.final.incomingPhasedResidualDensity
            (t.multiplier α *
              data.incomingExceptionalRefinedRootDriverCoefficient
                t α β e₀.2.2 ω u)
            α ρ ε 0 ω.1.1 u
          ∂Measure.pi fun _ => paperMeasure)
        ∂r324IncomingExceptionalRootParameterMeasure
          ρ lam ε e₀.2.1 := by
  have hjoint :=
    data.integrable_incomingExceptionalRefinedRootAfterHeadPhasedIntegrand
      p e₀ he₀ hm hε hε1 hG hint α β
  refine
    (data.lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingExceptionalAfterHead
      p e₀ he₀ hm hε hε1 hG hint α β).trans ?_
  rw [integral_prod _ hjoint, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hjoint.prod_right_ae] with ω hω
  rw [data.incomingExceptionalAfterHeadPhasedIntegrand_refinedRoot_driver_section_eq
    t α β e₀.2.2 ω] at hω ⊢
  exact
    t.transport 0 ω.1.1 α
      (fun u =>
        data.incomingExceptionalRefinedRootDriverCoefficient
          t α β e₀.2.2 ω u)
      hω

/-- The driver instantiation with the transport built directly from the
local block provider and the stop certificate: the complete root
endgame equation with every after-head hypothesis discharged from the
provider. -/
theorem lamEps_pow_r324RefinedPhysicalIntegral_eq_afterHeadDriverTerminal
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K e₀.1)
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (α β : Z4) :
    (lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        r324RefinedPhysicalIntegral
          ρ ε m α β p =
      ∫ ω :
          R324IncomingExceptionalRootParameter
            ρ lam ε e₀.2.1,
        (∫ u :
            (data.afterHeadAlternatingTransport
              hε hε1 provider).final.SurvivingCoordinate → T4,
          (data.afterHeadAlternatingTransport
            hε hε1 provider).final.incomingPhasedResidualDensity
            ((data.afterHeadAlternatingTransport
                hε hε1 provider).multiplier α *
              data.incomingExceptionalRefinedRootDriverCoefficient
                (data.afterHeadAlternatingTransport
                  hε hε1 provider)
                α β e₀.2.2 ω u)
            α ρ ε 0 ω.1.1 u
          ∂Measure.pi fun _ => paperMeasure)
        ∂r324IncomingExceptionalRootParameterMeasure
          ρ lam ε e₀.2.1 :=
  data.lamEps_pow_r324RefinedPhysicalIntegral_eq_driverTerminal
    p e₀ he₀
    (data.afterHeadAlternatingTransport hε hε1 provider)
    hm hε hε1 hG hint α β

/-- **Driver-terminal integrability at the genuine refined root.**  For
almost every root parameter, the driver-terminal phased density with the
multiplier-weighted refined terminal coefficient is integrable over the
terminal coordinates. -/
theorem eventually_integrable_incomingExceptionalRefinedRootDriverTerminal
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (t :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (α β : Z4) :
    ∀ᵐ ω ∂(r324IncomingExceptionalRootParameterMeasure
        ρ lam ε e₀.2.1),
      Integrable
        (fun u :
            t.final.SurvivingCoordinate → T4 =>
          t.final.incomingPhasedResidualDensity
            (t.multiplier α *
              data.incomingExceptionalRefinedRootDriverCoefficient
                t α β e₀.2.2 ω u)
            α ρ ε 0 ω.1.1 u)
        (Measure.pi fun _ => paperMeasure) := by
  have hjoint :=
    data.integrable_incomingExceptionalRefinedRootAfterHeadPhasedIntegrand
      p e₀ he₀ hm hε hε1 hG hint α β
  filter_upwards [hjoint.prod_right_ae] with ω hω
  rw [data.incomingExceptionalAfterHeadPhasedIntegrand_refinedRoot_driver_section_eq
    t α β e₀.2.2 ω] at hω
  exact
    t.integrable 0 ω.1.1 α
      (fun u =>
        data.incomingExceptionalRefinedRootDriverCoefficient
          t α β e₀.2.2 ω u)
      hω

end R324IncomingExceptionalStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
