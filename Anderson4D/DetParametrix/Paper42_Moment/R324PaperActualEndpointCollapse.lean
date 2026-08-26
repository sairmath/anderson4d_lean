import Anderson4D.DetParametrix.Paper42_Moment.R324DirectIncomingPhysicalRootBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperDirectCrossProjection
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightDirectIncomingSourceBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfExactCompose
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfWeightedExit

/-!
# The actual Step 4(A) endpoint collapse

This module connects the genuine refined physical root to the four literal
endpoint routes.  It follows paper §4.2: the right initial residual and the
primitive cross factor remain one signed coefficient while the two endpoint
operations of the left half are performed; the completed left density then
remains one signed coefficient while the right half is performed.

The declarations below name only that canonical coefficient and its two
direct-incoming projection identities.  No endpoint norm is taken here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}

/-- The untouched variables opposite the left endpoint half: the two right
boundary points and the right initial residual carrier. -/
abbrev R324PaperLeftOuterParameter
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaM : PartialPairing (Fin m)) :=
  (T4 × T4) ×
    ((R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).SurvivingCoordinate → T4)

/-- Product Haar on the untouched opposite-half variables. -/
def r324PaperLeftOuterParameterMeasure
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaM : PartialPairing (Fin m)) :
    Measure (R324PaperLeftOuterParameter rho lam eps kappaM) :=
  (paperMeasure.prod paperMeasure).prod
    (Measure.pi fun _ :
      (R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate => paperMeasure)

instance instSFiniteR324PaperLeftOuterParameterMeasure
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaM : PartialPairing (Fin m)) :
    SFinite (r324PaperLeftOuterParameterMeasure rho lam eps kappaM) := by
  unfold r324PaperLeftOuterParameterMeasure
  infer_instance

/-- Reassociate the physical root parameter as the free left outgoing
endpoint followed by the untouched opposite-half parameter. -/
def r324PaperLeftOuterParameterMeasurableEquiv
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaM : PartialPairing (Fin m))
    (L : Type*) [MeasurableSpace L] :
    R324IncomingExceptionalRootParameter rho lam eps kappaM × L ≃ᵐ
      (T4 × R324PaperLeftOuterParameter rho lam eps kappaM) × L :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodAssoc
      (α := T4) (β := T4 × T4)
      (γ := (R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate → T4))
    (MeasurableEquiv.refl L)

@[simp]
theorem r324PaperLeftOuterParameterMeasurableEquiv_apply
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaM : PartialPairing (Fin m))
    {L : Type*} [MeasurableSpace L]
    (q : R324IncomingExceptionalRootParameter rho lam eps kappaM × L) :
    r324PaperLeftOuterParameterMeasurableEquiv
        rho lam eps kappaM L q =
      ((q.1.1.1, (q.1.1.2, q.1.2)), q.2) := by
  rfl

/-- The reassociation preserves the literal product Haar measure. -/
theorem measurePreserving_r324PaperLeftOuterParameterMeasurableEquiv
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaM : PartialPairing (Fin m))
    {L : Type*} [MeasurableSpace L]
    (muL : Measure L) [SFinite muL] :
    MeasurePreserving
      (r324PaperLeftOuterParameterMeasurableEquiv
        rho lam eps kappaM L)
      ((r324IncomingExceptionalRootParameterMeasure
        rho lam eps kappaM).prod muL)
      ((paperMeasure.prod
        (r324PaperLeftOuterParameterMeasure
          rho lam eps kappaM)).prod muL) := by
  unfold r324PaperLeftOuterParameterMeasurableEquiv
    r324IncomingExceptionalRootParameterMeasure
    r324PaperLeftOuterParameterMeasure
  exact
    (measurePreserving_prodAssoc paperMeasure
      (paperMeasure.prod paperMeasure)
      (Measure.pi fun _ :
        (R324WithinHalfResidualPrefix.initial
          rho lam eps kappaM).SurvivingCoordinate => paperMeasure)).prod
      (MeasurePreserving.id muL)

/-- The literal coefficient carried through the left half: the two right
characters, the right initial residual, and the still-signed primitive
cross factor read on the current left carrier. -/
def r324PaperLeftCanonicalCoefficient
    (left : R324WithinHalfResidualPrefix rho lam eps kappaP)
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (s : R324PaperLeftOuterParameter rho lam eps kappaM)
    (v : left.SurvivingCoordinate → T4) : Complex :=
  charT4 (-alpha) s.1.1 *
    charT4 (-beta) s.1.2 *
    (((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).residualIntegrand
      rho eps s.1.1 s.1.2
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).reconstruct s.2) : Complex) *
      (r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct left
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          (v, s.2)) : Complex))

/-- The direct-incoming left source in the parameter order consumed by the
one-half endpoint transform. -/
def r324PaperLeftDirectInitialSourceDensity
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (q : (T4 × R324PaperLeftOuterParameter rho lam eps kappaM) ×
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaP).SurvivingCoordinate → T4)) : Complex :=
  (R324WithinHalfResidualPrefix.initial rho lam eps kappaP
    |>.incomingPhasedResidualDensity
      (charT4 beta q.1.1 *
        ((paperSecondOrderModeDecay alpha : Complex) *
          r324PaperLeftCanonicalCoefficient
            (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
            alpha beta pi q.1.2 q.2))
      alpha rho eps 0 q.1.1 q.2)

/-- Before any left transport, the genuine root outer factor is exactly the
free left outgoing character times the canonical untouched coefficient. -/
theorem directIncomingRefinedRootOuter_eq_char_mul_leftCanonical
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (y : T4) (s : R324PaperLeftOuterParameter rho lam eps kappaM)
    (v : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4) :
    directIncomingRefinedRootOuter rho lam eps kappaP kappaM
        alpha beta pi ((y, (s.1.1, s.1.2)), s.2) v =
      charT4 beta y *
        r324PaperLeftCanonicalCoefficient
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
          alpha beta pi s v := by
  unfold directIncomingRefinedRootOuter r324PaperLeftCanonicalCoefficient
  ring

/-- Reindexing the genuine direct-incoming source gives exactly the
parameterized left source above.  Joint integrability is transported at the
same time, so later endpoint operations need no new Fubini assumption. -/
theorem integrable_and_integral_directIncomingSource_eq_leftInitial
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (hsource : Integrable
      (directIncomingRefinedInitialSourceDensity
        rho lam eps kappaP kappaM alpha beta pi)
      ((r324IncomingExceptionalRootParameterMeasure
        rho lam eps kappaM).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            rho lam eps kappaP).SurvivingCoordinate => paperMeasure))) :
    Integrable
        (r324PaperLeftDirectInitialSourceDensity
          (rho := rho) (lam := lam) (eps := eps)
          (kappaP := kappaP) (kappaM := kappaM) alpha beta pi)
        ((paperMeasure.prod
          (r324PaperLeftOuterParameterMeasure
            rho lam eps kappaM)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps kappaP).SurvivingCoordinate => paperMeasure)) ∧
      (∫ q,
          directIncomingRefinedInitialSourceDensity
            rho lam eps kappaP kappaM alpha beta pi q
          ∂((r324IncomingExceptionalRootParameterMeasure
            rho lam eps kappaM).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).SurvivingCoordinate => paperMeasure))) =
        ∫ q,
          r324PaperLeftDirectInitialSourceDensity
            (rho := rho) (lam := lam) (eps := eps)
            (kappaP := kappaP) (kappaM := kappaM) alpha beta pi q
          ∂((paperMeasure.prod
            (r324PaperLeftOuterParameterMeasure
              rho lam eps kappaM)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).SurvivingCoordinate => paperMeasure)) := by
  let Left :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4
  let muLeft : Measure Left := Measure.pi fun _ => paperMeasure
  let e := r324PaperLeftOuterParameterMeasurableEquiv
    rho lam eps kappaM Left
  let F := directIncomingRefinedInitialSourceDensity
    rho lam eps kappaP kappaM alpha beta pi
  let G := r324PaperLeftDirectInitialSourceDensity
    (rho := rho) (lam := lam) (eps := eps)
    (kappaP := kappaP) (kappaM := kappaM) alpha beta pi
  have he : MeasurePreserving e
      ((r324IncomingExceptionalRootParameterMeasure
        rho lam eps kappaM).prod muLeft)
      ((paperMeasure.prod
        (r324PaperLeftOuterParameterMeasure
          rho lam eps kappaM)).prod muLeft) :=
    measurePreserving_r324PaperLeftOuterParameterMeasurableEquiv
      rho lam eps kappaM muLeft
  have hpoint (q : R324IncomingExceptionalRootParameter
      rho lam eps kappaM × Left) : F q = G (e q) := by
    simp only [F, G, e,
      r324PaperLeftOuterParameterMeasurableEquiv_apply,
      directIncomingRefinedInitialSourceDensity,
      r324PaperLeftDirectInitialSourceDensity]
    rw [directIncomingRefinedRootOuter_eq_char_mul_leftCanonical
      alpha beta pi q.1.1.1 (q.1.1.2, q.1.2) q.2]
    congr 1
    ring
  have hG : Integrable G
      ((paperMeasure.prod
        (r324PaperLeftOuterParameterMeasure
          rho lam eps kappaM)).prod muLeft) := by
    refine (he.integrable_comp_emb e.measurableEmbedding).mp ?_
    apply hsource.congr
    filter_upwards with q
    exact hpoint q
  refine ⟨by simpa only [G, muLeft, Left] using hG, ?_⟩
  calc
    (∫ q, F q
        ∂((r324IncomingExceptionalRootParameterMeasure
          rho lam eps kappaM).prod muLeft)) =
      ∫ q, G (e q)
        ∂((r324IncomingExceptionalRootParameterMeasure
          rho lam eps kappaM).prod muLeft) := by
        apply integral_congr_ae
        filter_upwards with q
        exact hpoint q
    _ = ∫ q, G q
        ∂((paperMeasure.prod
          (r324PaperLeftOuterParameterMeasure
            rho lam eps kappaM)).prod muLeft) :=
      he.integral_comp e.measurableEmbedding G
    _ = _ := by
      rfl

/-- Direct-incoming physical-root entrance in the exact parameter order of
the left one-half transform. -/
theorem integrable_and_r324RefinedPhysicalIntegral_eq_leftDirectInitial
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (alpha beta : Z4) :
    Integrable
        (r324PaperLeftDirectInitialSourceDensity
          (rho := rho) (lam := lam) (eps := eps)
          (kappaP := e0.1) (kappaM := e0.2.1)
          alpha beta e0.2.2)
        ((paperMeasure.prod
          (r324PaperLeftOuterParameterMeasure
            rho lam eps e0.2.1)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps e0.1).SurvivingCoordinate => paperMeasure)) ∧
      r324RefinedPhysicalIntegral rho eps m alpha beta p =
        ∫ q,
          r324PaperLeftDirectInitialSourceDensity
            (rho := rho) (lam := lam) (eps := eps)
            (kappaP := e0.1) (kappaM := e0.2.1)
            alpha beta e0.2.2 q
          ∂((paperMeasure.prod
            (r324PaperLeftOuterParameterMeasure
              rho lam eps e0.2.1)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps e0.1).SurvivingCoordinate => paperMeasure)) := by
  obtain ⟨hsource, hphysical⟩ :=
    integrable_and_r324RefinedPhysicalIntegral_eq_directIncomingSource
      (rho := rho) (lam := lam) (eps := eps)
      p e0 he0 heps heps1 alpha beta
  obtain ⟨hleft, hreindex⟩ :=
    integrable_and_integral_directIncomingSource_eq_leftInitial
      (rho := rho) (lam := lam) (eps := eps)
      (kappaP := e0.1) (kappaM := e0.2.1)
      alpha beta e0.2.2 hsource
  exact ⟨hleft, hphysical.trans hreindex⟩

/-- In a `DD` left half the same coefficient is read on the terminal driver
carrier through its coordinate projection. -/
theorem directIncomingRefinedRootOuter_eq_char_mul_leftDirectDriver
    (transport : R324WithinHalfAlternatingTransport
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP))
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (y : T4) (s : R324PaperLeftOuterParameter rho lam eps kappaM)
    (v : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4) :
    directIncomingRefinedRootOuter rho lam eps kappaP kappaM
        alpha beta pi ((y, (s.1.1, s.1.2)), s.2) v =
      charT4 beta y *
        r324PaperLeftCanonicalCoefficient transport.final
          alpha beta pi s (transport.projection v) := by
  have hcross :=
    r324ResidualPrimitiveSumProduct_eq_leftDirectDriverProjection
      transport pi v s.2
  unfold directIncomingRefinedRootOuter r324PaperLeftCanonicalCoefficient
  rw [hcross]
  ring

/-- In a `DE` left half the same coefficient is read on the post-terminal
carrier after the endpoint projection and literal terminal-tuple split. -/
theorem directIncomingRefinedRootOuter_eq_char_mul_leftDirectOutgoing
    (outgoing : R324PaperOutgoingEndpointTerminal
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaP))
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (y : T4) (s : R324PaperLeftOuterParameter rho lam eps kappaM)
    (v : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4) :
    directIncomingRefinedRootOuter rho lam eps kappaP kappaM
        alpha beta pi ((y, (s.1.1, s.1.2)), s.2) v =
      charT4 beta y *
        r324PaperLeftCanonicalCoefficient outgoing.terminalPost
          alpha beta pi s
          ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            outgoing.terminalData.terminal []
            outgoing.endpoint.stop_remaining
            (outgoing.endpoint.projection v)).2) := by
  have hcross :=
    r324ResidualPrimitiveSumProduct_eq_leftDirectOutgoingTerminalPost
      outgoing pi v s.2
  unfold directIncomingRefinedRootOuter r324PaperLeftCanonicalCoefficient
  rw [hcross]
  ring

end R324WithinHalfResidualPrefix

end

end Anderson4D
