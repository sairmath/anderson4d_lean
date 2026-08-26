import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointPhasedJointIntegrability

/-!
# The R-324 alternating driver

The phased construction transports the incoming residual density
along ordinary heads (nonzero sparse predecessor slot) and collapses the
first exceptional head at the refined physical root through two steps:

1. **General-state exceptional integral collapse.**  At an arbitrary
   reachable residual prefix whose literal head is fed by slot zero, the
   phased density integral collapses its retained head block: the
   perturbative power drops by twice the head block order, the phase
   re-anchors after the head with one paper second-order decay, and the
   primitive Step-4 defect of the head is absorbed into the coefficient.
   Unlike the root-anchored seam, no measured parameter is present and the
   collapse holds at arbitrary Fourier-evaluated endpoints; the incoming
   Fourier decay of the root has already been extracted once and for all,
   so the interior collapse contributes exactly one decay, not two.

2. **The alternating driver.**  By strong induction on the remaining list,
   every reachable residual prefix transports to a terminal prefix with
   empty remaining list: the longest ordinary run is consumed by the
   certified stop-before-step trace, the slot-zero-fed head at the run
   boundary is collapsed by the general-state exceptional step, and the
   strictly shorter after-head suffix recurses.  All per-head Proposition
   4.1 charge data is consumed from the stored edge certificates; no
   external charge hypothesis is taken.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-! ## Scalar linearity of the phased density -/

/-- The incoming phased residual density is linear in its coefficient. -/
theorem incomingPhasedResidualDensity_const_mul
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (a coefficient : ℂ) (k : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ) (x y : T4)
    (v : res.SurvivingCoordinate → T4) :
    res.incomingPhasedResidualDensity
        (a * coefficient) k ρ' ε' x y v =
      a *
        res.incomingPhasedResidualDensity
          coefficient k ρ' ε' x y v := by
  unfold incomingPhasedResidualDensity
  ring

/-! ## The outgoing Fourier section of an arbitrary head -/

/-- The outgoing edge of the literal remaining head is still the free
Green function, so its Fourier section against the head character is
integrable at every translation. -/
theorem integrable_char_mul_headOutgoing_sub
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (k : Z4) (a : T4) :
    Integrable
      (fun q : T4 =>
        charT4 k q *
          (res.state.edges
            (res.headContext
              head tail hremaining).outgoingSlot
            (q - a) : ℂ))
      paperMeasure := by
  have hout :
      res.state.edges
          (res.headContext
            head tail hremaining).outgoingSlot =
        greenFn :=
    res.state_edges_head_outgoing_eq_greenFn
      head tail hremaining
  rw [hout]
  exact
    (integrable_greenFn_sub a).ofReal.bdd_mul
      (c := 1)
      (continuous_charT4 k).measurable.aestronglyMeasurable
      (.of_forall fun q => by
        rw [norm_charT4])

/-! ## The internal collapse of the phased density at fixed gap and first -/

/-- Fixed after-head coordinates, fixed gap, and fixed first endpoint: the
phased density at a slot-zero-fed head integrates in its internal primitive
coordinates to the ordinary `primitiveKernelDiff`, with the head character
and the outgoing edge difference still exact. -/
theorem lamEps_pow_integral_incomingPhasedResidualDensity_internal_eq_of_eq_zero
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (coefficient : ℂ) (k : Z4) (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4)
    (gap first : T4)
    (hint :
      ∀ κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder head.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder head.2)},
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder head.2)
              κB.1
              (res.headContext
                head tail hremaining).internalEdges
              (primitiveAssemble
                (residualBlockOrder head.2)
                (res.headContext
                  head tail hremaining).one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hG :
      ∀ j, MemEClassT4
        ((res.headContext
          head tail hremaining).internalEdges j)) :
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder head.2) *
        (∫ r :
            Fin (2 * residualBlockOrder head.2 - 2) → T4,
          res.incomingPhasedResidualDensity
            coefficient k ρ ε x y
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm
              (primitiveAssemble
                (residualBlockOrder head.2)
                (res.headContext
                  head tail hremaining).one_le_blockOrder
                first (first + gap) r, v))
          ∂Measure.pi fun _ => paperMeasure) =
      charT4 k first *
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder
          (res.headContext
            head tail hremaining).internalEdges gap : ℂ) *
        ((res.state.edges
            (res.headContext
              head tail hremaining).outgoingSlot
            ((first + gap) -
              res.headSuccessorPoint
                head tail hremaining x y v) -
          res.state.edges
            (res.headContext
              head tail hremaining).outgoingSlot
            (first -
              res.headSuccessorPoint
                head tail hremaining x y v) : ℝ) : ℂ) *
        (coefficient *
          (res.headOuterFactor
            head tail hremaining ρ ε x y v : ℂ)) := by
  let a : T4 :=
    res.headSuccessorPoint head tail hremaining x y v
  let outer : ℂ :=
    coefficient *
      (res.headOuterFactor
        head tail hremaining ρ ε x y v : ℂ)
  let core :
      (Fin (2 * residualBlockOrder head.2 - 2) → T4) → ℂ :=
    fun r =>
      (res.headContext
        head tail hremaining).incomingErasedTranslatedRawLocalCore
        ρ ε a
        (primitiveAssemble
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder
          first (first + gap) r)
  have hpoint
      (r : Fin (2 * residualBlockOrder head.2 - 2) → T4) :
      res.incomingPhasedResidualDensity
          coefficient k ρ ε x y
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm
            (primitiveAssemble
              (residualBlockOrder head.2)
              (res.headContext
                head tail hremaining).one_le_blockOrder
              first (first + gap) r, v)) =
        charT4 k first * core r * outer := by
    rw [
      res.incomingPhasedResidualDensity_reconstruct_split_of_eq_zero
        head tail hremaining hpred coefficient k ρ ε x y _ v]
    simp only [primitiveAssemble_zero]
    rfl
  have hcore :
      (lamEps lam ε : ℂ) ^
            (2 * residualBlockOrder head.2) *
          (∫ r :
              Fin (2 * residualBlockOrder head.2 - 2) → T4,
            core r
            ∂Measure.pi fun _ => paperMeasure) =
        ((primitiveKernelDiff ρ lam ε
            (residualBlockOrder head.2)
            (res.headContext
              head tail hremaining).one_le_blockOrder
            (res.headContext
              head tail hremaining).internalEdges
            (first - (first + gap)) *
          (res.state.edges
              (res.headContext
                head tail hremaining).outgoingSlot
              ((first + gap) - a) -
            res.state.edges
              (res.headContext
                head tail hremaining).outgoingSlot
              (first - a)) : ℝ) : ℂ) :=
    (res.headContext
      head tail hremaining).lamEps_pow_integral_incomingErasedTranslatedRawLocalCore_eq
      ρ lam ε a first (first + gap) hint
  have hJ :
      MemEClassT4
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder
          (res.headContext
            head tail hremaining).internalEdges) :=
    primitiveKernelDiff_memE ρ lam ε
      (residualBlockOrder head.2)
      (res.headContext
        head tail hremaining).one_le_blockOrder
      (res.headContext
        head tail hremaining).internalEdges hG
  have hgap :
      primitiveKernelDiff ρ lam ε
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder
          (res.headContext
            head tail hremaining).internalEdges
          (first - (first + gap)) =
        primitiveKernelDiff ρ lam ε
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder
          (res.headContext
            head tail hremaining).internalEdges gap := by
    have hsub : first - (first + gap) = -gap := by
      abel
    rw [hsub, hJ.neg_invariant]
  calc
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder head.2) *
        (∫ r :
            Fin (2 * residualBlockOrder head.2 - 2) → T4,
          res.incomingPhasedResidualDensity
            coefficient k ρ ε x y
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm
              (primitiveAssemble
                (residualBlockOrder head.2)
                (res.headContext
                  head tail hremaining).one_le_blockOrder
                first (first + gap) r, v))
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder head.2) *
        (∫ r :
            Fin (2 * residualBlockOrder head.2 - 2) → T4,
          charT4 k first * core r * outer
          ∂Measure.pi fun _ => paperMeasure) := by
        apply congrArg
          (fun z : ℂ =>
            (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder head.2) * z)
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
    _ =
      charT4 k first *
        ((lamEps lam ε : ℂ) ^
            (2 * residualBlockOrder head.2) *
          ∫ r :
              Fin (2 * residualBlockOrder head.2 - 2) → T4,
            core r
            ∂Measure.pi fun _ => paperMeasure) *
        outer := by
      rw [integral_mul_const, integral_const_mul]
      ring
    _ = _ := by
      rw [hcore, hgap]
      dsimp only [a, outer]
      push_cast
      ring

/-! ## The reindexed head collapse to transported mode and defect -/

/-- The reindexed `(gap, first, internal)` double integral of the phased
density collapses to the transported outgoing Fourier mode times the
single ordinary primitive defect, with the coefficient and the head outer
factor untouched. -/
theorem integral_gap_first_lamEps_pow_incomingPhasedResidualDensity_eq_transportedMode_mul_defect
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (coefficient : ℂ) (k : Z4) (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4)
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder head.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder head.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder head.2)
              κB.1
              (res.headContext
                head tail hremaining).internalEdges
              (primitiveAssemble
                (residualBlockOrder head.2)
                (res.headContext
                  head tail hremaining).one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hG :
      ∀ j, MemEClassT4
        ((res.headContext
          head tail hremaining).internalEdges j)) :
    (∫ gap : T4,
        ∫ first : T4,
          (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder head.2) *
            (∫ r :
                Fin (2 * residualBlockOrder head.2 - 2) → T4,
              res.incomingPhasedResidualDensity
                coefficient k ρ ε x y
                ((res.splitSurvivingPiMeasurableEquiv
                  head tail hremaining).symm
                  (primitiveAssemble
                    (residualBlockOrder head.2)
                    (res.headContext
                      head tail hremaining).one_le_blockOrder
                    first (first + gap) r, v))
              ∂Measure.pi fun _ => paperMeasure)
          ∂paperMeasure
        ∂paperMeasure) =
      incomingExceptionalTransportedMode k
          (res.headSuccessorPoint
            head tail hremaining x y v)
          (res.state.edges
            (res.headContext
              head tail hremaining).outgoingSlot) *
        incomingExceptionalPrimitiveDefect ρ lam ε
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder
          (res.headContext
            head tail hremaining).internalEdges k *
        (coefficient *
          (res.headOuterFactor
            head tail hremaining ρ ε x y v : ℂ)) := by
  let a : T4 :=
    res.headSuccessorPoint head tail hremaining x y v
  let H : T4 → ℝ :=
    res.state.edges
      (res.headContext head tail hremaining).outgoingSlot
  let J : T4 → ℝ :=
    primitiveKernelDiff ρ lam ε
      (residualBlockOrder head.2)
      (res.headContext
        head tail hremaining).one_le_blockOrder
      (res.headContext
        head tail hremaining).internalEdges
  let outer : ℂ :=
    coefficient *
      (res.headOuterFactor
        head tail hremaining ρ ε x y v : ℂ)
  have hfiber (gap first : T4) :
      (lamEps lam ε : ℂ) ^
            (2 * residualBlockOrder head.2) *
          (∫ r :
              Fin (2 * residualBlockOrder head.2 - 2) → T4,
            res.incomingPhasedResidualDensity
              coefficient k ρ ε x y
              ((res.splitSurvivingPiMeasurableEquiv
                head tail hremaining).symm
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (res.headContext
                    head tail hremaining).one_le_blockOrder
                  first (first + gap) r, v))
            ∂Measure.pi fun _ => paperMeasure) =
        charT4 k first * (J gap : ℂ) *
          ((H ((first + gap) - a) -
            H (first - a) : ℝ) : ℂ) *
          outer :=
    res.lamEps_pow_integral_incomingPhasedResidualDensity_internal_eq_of_eq_zero
      head tail hremaining hpred coefficient k x y v
      gap first (hint gap first) hG
  have hbase :
      Integrable
        (fun w : T4 =>
          charT4 k w * (H (w - a) : ℂ))
        paperMeasure :=
    res.integrable_char_mul_headOutgoing_sub
      head tail hremaining k a
  have htransport :
      (∫ gap : T4,
          (J gap : ℂ) *
            (∫ first : T4,
              charT4 k first *
                ((H ((first + gap) - a) -
                  H (first - a) : ℝ) : ℂ)
              ∂paperMeasure)
          ∂paperMeasure) =
        incomingExceptionalTransportedMode k a H *
          ∫ gap : T4,
            (J gap : ℂ) * (charT4 (-k) gap - 1)
            ∂paperMeasure :=
    integral_kernel_mul_char_outgoingDifference_eq_transportedMode_mul_defect
      k a H J hbase
  calc
    (∫ gap : T4,
        ∫ first : T4,
          (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder head.2) *
            (∫ r :
                Fin (2 * residualBlockOrder head.2 - 2) → T4,
              res.incomingPhasedResidualDensity
                coefficient k ρ ε x y
                ((res.splitSurvivingPiMeasurableEquiv
                  head tail hremaining).symm
                  (primitiveAssemble
                    (residualBlockOrder head.2)
                    (res.headContext
                      head tail hremaining).one_le_blockOrder
                    first (first + gap) r, v))
              ∂Measure.pi fun _ => paperMeasure)
          ∂paperMeasure
        ∂paperMeasure) =
      ∫ gap : T4,
        ∫ first : T4,
          charT4 k first * (J gap : ℂ) *
            ((H ((first + gap) - a) -
              H (first - a) : ℝ) : ℂ) *
            outer
          ∂paperMeasure
        ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with gap
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (hfiber gap)
    _ =
      ∫ gap : T4,
        ((J gap : ℂ) *
            (∫ first : T4,
              charT4 k first *
                ((H ((first + gap) - a) -
                  H (first - a) : ℝ) : ℂ)
              ∂paperMeasure)) *
          outer
        ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with gap
          calc
            (∫ first : T4,
                charT4 k first * (J gap : ℂ) *
                  ((H ((first + gap) - a) -
                    H (first - a) : ℝ) : ℂ) *
                  outer
                ∂paperMeasure) =
              ∫ first : T4,
                (J gap : ℂ) *
                  (charT4 k first *
                    ((H ((first + gap) - a) -
                      H (first - a) : ℝ) : ℂ)) *
                  outer
                ∂paperMeasure := by
                  apply integral_congr_ae
                  filter_upwards with first
                  ring
            _ = _ := by
              rw [integral_mul_const, integral_const_mul]
    _ =
      (∫ gap : T4,
        (J gap : ℂ) *
          (∫ first : T4,
            charT4 k first *
              ((H ((first + gap) - a) -
                H (first - a) : ℝ) : ℂ)
            ∂paperMeasure)
        ∂paperMeasure) *
        outer := by
          rw [integral_mul_const]
    _ =
      (incomingExceptionalTransportedMode k a H *
          ∫ gap : T4,
            (J gap : ℂ) * (charT4 (-k) gap - 1)
            ∂paperMeasure) *
        outer := by
          rw [htransport]
    _ = _ := by
      dsimp only [a, H, J, outer]
      unfold incomingExceptionalPrimitiveDefect
      ring

/-! ## The general-state collapsed-head coefficient -/

/-- The scalar produced by collapsing one slot-zero-fed head of the phased
density: one paper second-order decay from the transported outgoing Green
mode and the primitive Step-4 defect of the head internal edges.  The
second decay of the root-anchored collapse came from the incoming Fourier
evaluation of the root, which happens only once; the general-state
interior collapse contributes exactly this factor. -/
def incomingExceptionalHeadCollapseFactor
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (k : Z4) : ℂ :=
  (paperSecondOrderModeDecay k : ℂ) *
    incomingExceptionalPrimitiveDefect ρ lam ε
      (residualBlockOrder head.2)
      (res.headContext
        head tail hremaining).one_le_blockOrder
      (res.headContext
        head tail hremaining).internalEdges k

/-- General-state analogue of the seam-2 post coefficient: the collapsed
head factor times a genuinely coordinate-dependent after-head coefficient. -/
def incomingExceptionalGeneralPostCoefficient
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (k : Z4)
    (postCoefficient :
      ((res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) → ℂ)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) : ℂ :=
  res.incomingExceptionalHeadCollapseFactor
      head tail hremaining k *
    postCoefficient v

/-- General-state analogue of the seam-2 after-head phased integrand: the
after-head phased residual density carrying the collapsed head as its
coordinate-dependent coefficient, at arbitrary endpoints. -/
def incomingExceptionalGeneralAfterHeadPhasedIntegrand
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (k : Z4) (x y : T4)
    (postCoefficient :
      ((res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) → ℂ)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) : ℂ :=
  (res.afterHead
    head tail hremaining).incomingPhasedResidualDensity
      (res.incomingExceptionalGeneralPostCoefficient
        head tail hremaining k postCoefficient v)
      k ρ ε x y v

/-! ## The head-section collapse at fixed after-head coordinates -/

/-- Fixed after-head coordinates: integrating the retained head tuple of
the phased density at a slot-zero-fed head produces exactly the after-head
phased density with the collapsed-head coefficient. -/
theorem lamEps_pow_integral_incomingPhasedResidualDensity_head_section_eq_afterHead_of_eq_zero
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (x y : T4)
    (postCoefficient :
      ((res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) → ℂ)
    (k : Z4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4)
    (hhead :
      Integrable
        (fun t :
            Fin (2 * residualBlockOrder head.2) → T4 =>
          res.incomingPhasedResidualDensity
            (postCoefficient v) k ρ ε x y
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v)))
        (Measure.pi fun _ => paperMeasure))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder head.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder head.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder head.2)
              κB.1
              (res.headContext
                head tail hremaining).internalEdges
              (primitiveAssemble
                (residualBlockOrder head.2)
                (res.headContext
                  head tail hremaining).one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hG :
      ∀ j, MemEClassT4
        ((res.headContext
          head tail hremaining).internalEdges j)) :
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder head.2) *
        (∫ t :
            Fin (2 * residualBlockOrder head.2) → T4,
          res.incomingPhasedResidualDensity
            (postCoefficient v) k ρ ε x y
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))
          ∂Measure.pi fun _ => paperMeasure) =
      res.incomingExceptionalGeneralAfterHeadPhasedIntegrand
        head tail hremaining k x y postCoefficient v := by
  have hreindex :=
    integral_standardBlock_eq_integral_gap_first_internal
      (residualBlockOrder head.2)
      (res.headContext
        head tail hremaining).one_le_blockOrder
      (fun t :
          Fin (2 * residualBlockOrder head.2) → T4 =>
        res.incomingPhasedResidualDensity
          (postCoefficient v) k ρ ε x y
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
      hhead
  calc
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder head.2) *
        (∫ t :
            Fin (2 * residualBlockOrder head.2) → T4,
          res.incomingPhasedResidualDensity
            (postCoefficient v) k ρ ε x y
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder head.2) *
        (∫ gap : T4,
          ∫ first : T4,
            ∫ r :
                Fin (2 * residualBlockOrder head.2 - 2) → T4,
              res.incomingPhasedResidualDensity
                (postCoefficient v) k ρ ε x y
                ((res.splitSurvivingPiMeasurableEquiv
                  head tail hremaining).symm
                  (primitiveAssemble
                    (residualBlockOrder head.2)
                    (res.headContext
                      head tail hremaining).one_le_blockOrder
                    first (first + gap) r, v))
              ∂Measure.pi fun _ => paperMeasure
            ∂paperMeasure
          ∂paperMeasure) := by
        exact congrArg
          (fun z : ℂ =>
            (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder head.2) * z)
          hreindex
    _ =
      ∫ gap : T4,
        ∫ first : T4,
          (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder head.2) *
            (∫ r :
                Fin (2 * residualBlockOrder head.2 - 2) → T4,
              res.incomingPhasedResidualDensity
                (postCoefficient v) k ρ ε x y
                ((res.splitSurvivingPiMeasurableEquiv
                  head tail hremaining).symm
                  (primitiveAssemble
                    (residualBlockOrder head.2)
                    (res.headContext
                      head tail hremaining).one_le_blockOrder
                    first (first + gap) r, v))
              ∂Measure.pi fun _ => paperMeasure)
          ∂paperMeasure
        ∂paperMeasure := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with gap
          rw [← integral_const_mul]
    _ =
      incomingExceptionalTransportedMode k
          (res.headSuccessorPoint
            head tail hremaining x y v)
          (res.state.edges
            (res.headContext
              head tail hremaining).outgoingSlot) *
        incomingExceptionalPrimitiveDefect ρ lam ε
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder
          (res.headContext
            head tail hremaining).internalEdges k *
        (postCoefficient v *
          (res.headOuterFactor
            head tail hremaining ρ ε x y v : ℂ)) :=
      res.integral_gap_first_lamEps_pow_incomingPhasedResidualDensity_eq_transportedMode_mul_defect
        head tail hremaining hpred
        (postCoefficient v) k x y v hint hG
    _ = _ := by
      rw [
        res.incomingExceptionalTransportedMode_eq_decay_mul_afterHead_anchor
          head tail hremaining hpred k x y v]
      unfold incomingExceptionalGeneralAfterHeadPhasedIntegrand
        incomingExceptionalGeneralPostCoefficient
        incomingExceptionalHeadCollapseFactor
        incomingPhasedResidualDensity
      rw [
        res.afterHead_incomingErasedResidualIntegrand_of_eq_zero
          head tail hremaining hpred ρ ε x y v]
      ring

/-! ## The general-state exceptional collapse at the integral level -/

section IntegralCollapse

variable (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)

/-- **General-state exceptional head absorption.**  At a slot-zero-fed
head the weighted phased density integral collapses its retained head
tuple: the perturbative power drops by twice the head block order and the
integrand becomes exactly the after-head phased density with the
collapsed-head coefficient, at arbitrary endpoints. -/
theorem lamEps_pow_integral_incomingPhasedResidualDensity_eq_afterHead_of_eq_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (x y : T4)
    (postCoefficient :
      ((res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) → ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (postCoefficient
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2)
            k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder head.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder head.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder head.2)
              κB.1
              (res.headContext
                head tail hremaining).internalEdges
              (primitiveAssemble
                (residualBlockOrder head.2)
                (res.headContext
                  head tail hremaining).one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hG :
      ∀ j, MemEClassT4
        ((res.headContext
          head tail hremaining).internalEdges j)) :
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ w : res.SurvivingCoordinate → T4,
          res.incomingPhasedResidualDensity
            (postCoefficient
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2)
            k ρ ε x y w
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 *
            (res.afterHead
              head tail hremaining).remainingOrder) *
        (∫ v :
            (res.afterHead
              head tail hremaining).SurvivingCoordinate → T4,
          res.incomingExceptionalGeneralAfterHeadPhasedIntegrand
            head tail hremaining k x y postCoefficient v
          ∂Measure.pi fun _ => paperMeasure) := by
  let post :=
    res.afterHead head tail hremaining
  let split :=
    res.splitSurvivingPiMeasurableEquiv
      head tail hremaining
  let μPre : Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μHead :
      Measure (Fin (2 * residualBlockOrder head.2) → T4) :=
    Measure.pi fun _ => paperMeasure
  let μPost : Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let g :
      ((Fin (2 * residualBlockOrder head.2) → T4) ×
        (post.SurvivingCoordinate → T4)) → ℂ :=
    fun p =>
      res.incomingPhasedResidualDensity
        (postCoefficient p.2) k ρ ε x y
        (split.symm p)
  have hcomp : Integrable (g ∘ split) μPre := by
    apply hfull.congr
    filter_upwards with w
    dsimp only [Function.comp_apply, g]
    rw [split.symm_apply_apply]
  have hg : Integrable g (μHead.prod μPost) :=
    (res.measurePreserving_splitSurvivingPiMeasurableEquiv
      head tail hremaining).integrable_comp_emb
        split.measurableEmbedding |>.mp hcomp
  have hexponent :
      2 * res.remainingOrder =
        2 * post.remainingOrder +
          2 * residualBlockOrder head.2 := by
    have horder :=
      res.remainingOrder_head head tail hremaining
    dsimp only [post]
    omega
  calc
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ w : res.SurvivingCoordinate → T4,
          res.incomingPhasedResidualDensity
            (postCoefficient
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2)
            k ρ ε x y w
          ∂μPre) =
      (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ w : res.SurvivingCoordinate → T4,
          g (split w) ∂μPre) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with w
        dsimp only [g]
        rw [split.symm_apply_apply]
    _ =
      (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ p, g p ∂(μHead.prod μPost)) := by
        congr 1
        exact
          (res.measurePreserving_splitSurvivingPiMeasurableEquiv
            head tail hremaining).integral_comp
            split.measurableEmbedding g
    _ =
      (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ v, (∫ t, g (t, v) ∂μHead) ∂μPost) := by
        congr 1
        exact integral_prod_symm g hg
    _ =
      (lamEps lam ε : ℂ) ^ (2 * post.remainingOrder) *
        (∫ v,
          (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder head.2) *
            (∫ t, g (t, v) ∂μHead)
          ∂μPost) := by
        rw [integral_const_mul, hexponent, pow_add]
        ring
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg.prod_left_ae] with v hv
      exact
        res.lamEps_pow_integral_incomingPhasedResidualDensity_head_section_eq_afterHead_of_eq_zero
          head tail hremaining hpred x y
          postCoefficient k v hv hint hG

/-- **General-state integrability handover.**  The after-head phased
density with the collapsed-head coefficient is integrable over the
after-head coordinates.  This is the recursion seam feeding the next
ordinary run of the alternating driver. -/
theorem integrable_afterHead_incomingPhasedResidualDensity_of_eq_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (x y : T4)
    (postCoefficient :
      ((res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) → ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (postCoefficient
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2)
            k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder head.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder head.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder head.2)
              κB.1
              (res.headContext
                head tail hremaining).internalEdges
              (primitiveAssemble
                (residualBlockOrder head.2)
                (res.headContext
                  head tail hremaining).one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hG :
      ∀ j, MemEClassT4
        ((res.headContext
          head tail hremaining).internalEdges j)) :
    Integrable
      (fun v :
          (res.afterHead
            head tail hremaining).SurvivingCoordinate → T4 =>
        res.incomingExceptionalGeneralAfterHeadPhasedIntegrand
          head tail hremaining k x y postCoefficient v)
      (Measure.pi fun _ => paperMeasure) := by
  let post :=
    res.afterHead head tail hremaining
  let split :=
    res.splitSurvivingPiMeasurableEquiv
      head tail hremaining
  let μPre : Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μHead :
      Measure (Fin (2 * residualBlockOrder head.2) → T4) :=
    Measure.pi fun _ => paperMeasure
  let μPost : Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let g :
      ((Fin (2 * residualBlockOrder head.2) → T4) ×
        (post.SurvivingCoordinate → T4)) → ℂ :=
    fun p =>
      res.incomingPhasedResidualDensity
        (postCoefficient p.2) k ρ ε x y
        (split.symm p)
  have hcomp : Integrable (g ∘ split) μPre := by
    apply hfull.congr
    filter_upwards with w
    dsimp only [Function.comp_apply, g]
    rw [split.symm_apply_apply]
  have hg : Integrable g (μHead.prod μPost) :=
    (res.measurePreserving_splitSurvivingPiMeasurableEquiv
      head tail hremaining).integrable_comp_emb
        split.measurableEmbedding |>.mp hcomp
  have hmarg := hg.integral_prod_right
  have hscaled :=
    hmarg.const_mul
      ((lamEps lam ε : ℂ) ^
        (2 * residualBlockOrder head.2))
  apply hscaled.congr
  filter_upwards [hg.prod_left_ae] with v hv
  exact
    res.lamEps_pow_integral_incomingPhasedResidualDensity_head_section_eq_afterHead_of_eq_zero
      head tail hremaining hpred x y
      postCoefficient k v hv hint hG

end IntegralCollapse

/-! ## Parameter-carrying exceptional head -/

/-- Joint integrability crosses one slot-zero-fed head while all external
endpoint parameters remain outside the signed head integral. -/
theorem integrable_joint_afterHead_incomingPhasedResidualDensity_of_eq_zero
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν]
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (hpred : r324WithinHalfPredecessorSlot res.state head = 0)
    (x y : Y → T4)
    (postCoefficient : Y →
      ((res.afterHead head tail hremaining).SurvivingCoordinate → T4) →
        ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun p : Y × (res.SurvivingCoordinate → T4) =>
          res.incomingPhasedResidualDensity
            (postCoefficient p.1
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining p.2).2)
            k ρ ε (x p.1) (y p.1) p.2)
        (ν.prod (Measure.pi fun _ => paperMeasure)))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder head.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder head.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder head.2) κB.1
              (res.headContext head tail hremaining).internalEdges
              (primitiveAssemble
                (residualBlockOrder head.2)
                (res.headContext head tail hremaining).one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hG : ∀ j, MemEClassT4
      ((res.headContext head tail hremaining).internalEdges j)) :
    Integrable
      (fun p : Y ×
          ((res.afterHead head tail hremaining).SurvivingCoordinate → T4) =>
        res.incomingExceptionalGeneralAfterHeadPhasedIntegrand
          head tail hremaining k (x p.1) (y p.1)
          (postCoefficient p.1) p.2)
      (ν.prod (Measure.pi fun _ => paperMeasure)) := by
  let post := res.afterHead head tail hremaining
  let split := res.splitSurvivingPiMeasurableEquiv head tail hremaining
  let μPre := Measure.pi fun _ : res.SurvivingCoordinate => paperMeasure
  let μHead := Measure.pi fun _ : Fin (2 * residualBlockOrder head.2) =>
    paperMeasure
  let μPost := Measure.pi fun _ : post.SurvivingCoordinate => paperMeasure
  let splitWithParameter :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl Y) split
  have hsplit : MeasurePreserving splitWithParameter
      (ν.prod μPre) (ν.prod (μHead.prod μPost)) :=
    (MeasurePreserving.id ν).prod
      (res.measurePreserving_splitSurvivingPiMeasurableEquiv
        head tail hremaining)
  let f : Y ×
      ((Fin (2 * residualBlockOrder head.2) → T4) ×
        (post.SurvivingCoordinate → T4)) → ℂ :=
    fun q => res.incomingPhasedResidualDensity
      (postCoefficient q.1 q.2.2) k ρ ε (x q.1) (y q.1)
      (split.symm q.2)
  have hf : Integrable f (ν.prod (μHead.prod μPost)) := by
    refine (hsplit.integrable_comp_emb
      splitWithParameter.measurableEmbedding).mp ?_
    apply hfull.congr
    filter_upwards with p
    rcases p with ⟨parameter, coordinates⟩
    change _ = res.incomingPhasedResidualDensity
      (postCoefficient parameter (split coordinates).2) k ρ ε
      (x parameter) (y parameter) (split.symm (split coordinates))
    rw [split.symm_apply_apply]
  let pull := r324IncomingExceptionalHeadPullMeasurableEquiv
    Y (Fin (2 * residualBlockOrder head.2) → T4)
      (post.SurvivingCoordinate → T4)
  have hpull : MeasurePreserving pull
      (ν.prod (μHead.prod μPost)) (μHead.prod (ν.prod μPost)) :=
    measurePreserving_r324IncomingExceptionalHeadPullMeasurableEquiv
      ν μHead μPost
  let g : (Fin (2 * residualBlockOrder head.2) → T4) ×
      (Y × (post.SurvivingCoordinate → T4)) → ℂ :=
    fun q => res.incomingPhasedResidualDensity
      (postCoefficient q.2.1 q.2.2) k ρ ε
      (x q.2.1) (y q.2.1) (split.symm (q.1, q.2.2))
  have hg : Integrable g (μHead.prod (ν.prod μPost)) := by
    refine (hpull.integrable_comp_emb pull.measurableEmbedding).mp ?_
    apply hf.congr
    filter_upwards with q
    rcases q with ⟨parameter, headTuple, postTuple⟩
    rfl
  have hmarg := hg.integral_prod_right
  have hscaled := hmarg.const_mul
    ((lamEps lam ε : ℂ) ^ (2 * residualBlockOrder head.2))
  apply hscaled.congr
  filter_upwards [hg.prod_left_ae] with q hq
  rcases q with ⟨parameter, postTuple⟩
  exact
    res.lamEps_pow_integral_incomingPhasedResidualDensity_head_section_eq_afterHead_of_eq_zero
      head tail hremaining hpred (x parameter) (y parameter)
      (postCoefficient parameter) k postTuple hq hint hG

/-! ## The two-phase combinator at the packaged next exceptional stop

One ordinary run followed by one exceptional head collapse, with every
Proposition 4.1 charge consumed from the edge certificate stored in the
certified stop-before-step trace. -/

namespace R324WithinHalfNextExceptionalStop

variable {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}

/-- The detJ charges of the retained head are supplied pointwise by the
stop certificate transported along the consumed ordinary run. -/
theorem stopCertificate_hint
    (data : R324WithinHalfNextExceptionalStop res scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
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
            κB.1
            (data.trace.stopPrefix.headContext
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).internalEdges
            (primitiveAssemble
              (residualBlockOrder data.terminal.2)
              (data.trace.stopPrefix.headContext
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).one_le_blockOrder
              first (first + gap) r))
        (Measure.pi fun _ => paperMeasure) :=
  fun gap first κB =>
    R324WithinHalfEdgeCertificate.integrable_stepClosedIntegrand_section
      (ctx :=
        data.trace.stopPrefix.headContext
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)
      data.trace.stopCertificate hε hε1 κB first (first + gap)

/-- The internal edges of the retained head lie in the paper's symmetry
class, again by the transported stop certificate. -/
theorem stopCertificate_memE
    (data : R324WithinHalfNextExceptionalStop res scale) :
    ∀ j, MemEClassT4
      ((data.trace.stopPrefix.headContext
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).internalEdges j) :=
  fun j =>
    data.trace.stopCertificate.memE
      ((data.trace.stopPrefix.headContext
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).internalSlot j)

/-- **Two-phase combinator.**  The ordinary run is consumed by the phased
stop transport and the slot-zero-fed head at the run boundary is collapsed
by the general-state exceptional step: the weighted phased integral at the
starting prefix equals the weighted after-head phased integral with the
collapsed-head coefficient.  All charges come from the stored certificate. -/
theorem lamEps_pow_integral_incomingPhasedResidualDensity_eq_afterHead
    (data : R324WithinHalfNextExceptionalStop res scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x y : T4)
    (postCoefficient :
      ((data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) → ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (postCoefficient
              (data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq
                (data.trace.stopProjection w)).2)
            k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ w : res.SurvivingCoordinate → T4,
          res.incomingPhasedResidualDensity
            (postCoefficient
              (data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq
                (data.trace.stopProjection w)).2)
            k ρ ε x y w
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 *
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).remainingOrder) *
        (∫ v :
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
              T4,
          data.trace.stopPrefix.incomingExceptionalGeneralAfterHeadPhasedIntegrand
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq
            k x y postCoefficient v
          ∂Measure.pi fun _ => paperMeasure) := by
  have h1 :=
    data.trace.lamEps_pow_integral_incomingPhasedResidualDensity_eq_stop
      x y data.ordinary
      (fun w =>
        postCoefficient
          (data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq w).2)
      k hfull
  have hstop :=
    data.trace.integrable_stop_incomingPhasedResidualDensity
      x y data.ordinary
      (fun w =>
        postCoefficient
          (data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq w).2)
      k hfull
  have h2 :=
    data.trace.stopPrefix.lamEps_pow_integral_incomingPhasedResidualDensity_eq_afterHead_of_eq_zero
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      data.predecessorSlot_eq_zero
      x y postCoefficient k hstop
      (data.stopCertificate_hint hε hε1)
      data.stopCertificate_memE
  exact h1.trans h2

/-- Integrability handover of the two-phase combinator: the after-head
phased density with the collapsed-head coefficient is integrable. -/
theorem integrable_afterHead_incomingPhasedResidualDensity
    (data : R324WithinHalfNextExceptionalStop res scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x y : T4)
    (postCoefficient :
      ((data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) → ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (postCoefficient
              (data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq
                (data.trace.stopProjection w)).2)
            k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun v :
          (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4 =>
        data.trace.stopPrefix.incomingExceptionalGeneralAfterHeadPhasedIntegrand
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq
          k x y postCoefficient v)
      (Measure.pi fun _ => paperMeasure) := by
  have hstop :=
    data.trace.integrable_stop_incomingPhasedResidualDensity
      x y data.ordinary
      (fun w =>
        postCoefficient
          (data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq w).2)
      k hfull
  exact
    data.trace.stopPrefix.integrable_afterHead_incomingPhasedResidualDensity_of_eq_zero
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      data.predecessorSlot_eq_zero
      x y postCoefficient k hstop
      (data.stopCertificate_hint hε hε1)
      data.stopCertificate_memE

/-- Joint version of the ordinary-run-plus-exceptional-head handover.  The
external parameter represents the untouched opposite half in paper Step
4(A); it is never normed or summed during the signed elimination. -/
theorem integrable_joint_afterHead_incomingPhasedResidualDensity
    {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν]
    (data : R324WithinHalfNextExceptionalStop res scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x y : Y → T4)
    (postCoefficient : Y →
      ((data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4) →
          ℂ)
    (k : Z4)
    (hfull :
      Integrable
        (fun p : Y × (res.SurvivingCoordinate → T4) =>
          res.incomingPhasedResidualDensity
            (postCoefficient p.1
              (data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq
                (data.trace.stopProjection p.2)).2)
            k ρ ε (x p.1) (y p.1) p.2)
        (ν.prod (Measure.pi fun _ => paperMeasure))) :
    Integrable
      (fun p : Y ×
          ((data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4) =>
        data.trace.stopPrefix.incomingExceptionalGeneralAfterHeadPhasedIntegrand
          data.terminal data.suffix data.trace.stopPrefix_remaining_eq
          k (x p.1) (y p.1) (postCoefficient p.1) p.2)
      (ν.prod (Measure.pi fun _ => paperMeasure)) := by
  have hstop :=
    data.trace.integrable_joint_stop_incomingPhasedResidualDensity
      ν data.ordinary x y
      (fun parameter stop =>
        postCoefficient parameter
          (data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq stop).2)
      k hfull
  exact
    data.trace.stopPrefix
      |>.integrable_joint_afterHead_incomingPhasedResidualDensity_of_eq_zero
        ν data.terminal data.suffix data.trace.stopPrefix_remaining_eq
        data.predecessorSlot_eq_zero x y postCoefficient k hstop
        (data.stopCertificate_hint hε hε1)
        data.stopCertificate_memE

end R324WithinHalfNextExceptionalStop

/-! ## The alternating transport package -/

/-- Complete phased transport from a reachable residual prefix to a
terminal prefix with empty remaining list.  The multiplier accumulates one
collapsed-head factor per exceptional stop crossed by the alternation; the
projection restricts a surviving tuple along the value-preserving
coordinate embedding.  The transport and integrability fields hold at
every pair of Fourier-evaluated endpoints, every incoming mode, and every
terminal-coordinate-dependent coefficient. -/
structure R324WithinHalfAlternatingTransport
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing) where
  final : R324WithinHalfResidualPrefix ρ lam ε pairing
  final_remaining : final.remaining = []
  embedding :
    final.SurvivingCoordinate → res.SurvivingCoordinate
  embedding_val : ∀ i, (embedding i).1 = i.1
  projection :
    (res.SurvivingCoordinate → T4) →
      (final.SurvivingCoordinate → T4)
  projection_apply :
    ∀ (v : res.SurvivingCoordinate → T4)
      (i : final.SurvivingCoordinate),
      projection v i = v (embedding i)
  multiplier : Z4 → ℂ
  transport :
    ∀ (x y : T4) (k : Z4)
      (coefficient :
        (final.SurvivingCoordinate → T4) → ℂ),
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (coefficient (projection w)) k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure) →
      (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
          (∫ w : res.SurvivingCoordinate → T4,
            res.incomingPhasedResidualDensity
              (coefficient (projection w)) k ρ ε x y w
            ∂Measure.pi fun _ => paperMeasure) =
        ∫ u : final.SurvivingCoordinate → T4,
          final.incomingPhasedResidualDensity
            (multiplier k * coefficient u) k ρ ε x y u
          ∂Measure.pi fun _ => paperMeasure
  integrable :
    ∀ (x y : T4) (k : Z4)
      (coefficient :
        (final.SurvivingCoordinate → T4) → ℂ),
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (coefficient (projection w)) k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure) →
      Integrable
        (fun u : final.SurvivingCoordinate → T4 =>
          final.incomingPhasedResidualDensity
            (multiplier k * coefficient u) k ρ ε x y u)
        (Measure.pi fun _ => paperMeasure)
  /-- Parameter-carrying integrability required by the paper's delayed
  Fubini step.  No absolute value is taken before both halves are
  eliminated. -/
  integrable_joint :
    ∀ {Y : Type} [MeasurableSpace Y]
      (ν : Measure Y) [SFinite ν]
      (x y : Y → T4) (k : Z4)
      (coefficient :
        Y → (final.SurvivingCoordinate → T4) → ℂ),
      Integrable
        (fun p : Y × (res.SurvivingCoordinate → T4) =>
          res.incomingPhasedResidualDensity
            (coefficient p.1 (projection p.2))
            k ρ ε (x p.1) (y p.1) p.2)
        (ν.prod (Measure.pi fun _ => paperMeasure)) →
      Integrable
        (fun p : Y × (final.SurvivingCoordinate → T4) =>
          final.incomingPhasedResidualDensity
            (multiplier k * coefficient p.1 p.2)
            k ρ ε (x p.1) (y p.1) p.2)
        (ν.prod (Measure.pi fun _ => paperMeasure))

/-! ## Base case: the all-ordinary run -/

namespace R324WithinHalfCertifiedAnalyticTrace

/-- A certified analytic trace ordinary along its whole remaining list is
already a complete alternating transport, with trivial multiplier. -/
def alternatingTransport
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale)
    (hordinary : trace.OrdinaryAlong) :
    R324WithinHalfAlternatingTransport res where
  final := trace.terminalPrefix
  final_remaining := trace.terminalPrefix_remaining_eq_nil
  embedding := trace.terminalCoordinateEmbedding
  embedding_val := fun i =>
    trace.terminalCoordinateEmbedding_val i
  projection := trace.terminalProjection
  projection_apply := fun v i =>
    trace.terminalProjection_apply v i
  multiplier := fun _ => 1
  transport := by
    intro x y k coefficient hfull
    have h :=
      trace.lamEps_pow_integral_incomingPhasedResidualDensity_eq_trace_end
        x y hordinary coefficient k hfull
    have hzero :
        trace.terminalPrefix.remainingOrder = 0 := by
      unfold R324WithinHalfResidualPrefix.remainingOrder
      rw [trace.terminalPrefix_remaining_eq_nil]
      rfl
    rw [hzero, Nat.mul_zero, pow_zero, one_mul] at h
    simpa only [one_mul] using h
  integrable := by
    intro x y k coefficient hfull
    have h :=
      trace.integrable_trace_end_incomingPhasedResidualDensity
        x y hordinary coefficient k hfull
    simpa only [one_mul] using h
  integrable_joint := by
    intro Y _ ν _ x y k coefficient hfull
    have h :=
      trace.integrable_joint_trace_end_incomingPhasedResidualDensity
        ν hordinary x y coefficient k hfull
    simpa only [one_mul] using h

end R324WithinHalfCertifiedAnalyticTrace

/-! ## Recursion step: one exceptional stop, then an arbitrary transport -/

namespace R324WithinHalfNextExceptionalStop

/-- A packaged next exceptional stop composed with an alternating
transport of its after-head prefix is an alternating transport of the
starting prefix.  The multiplier gains the collapsed-head factor of the
retained head. -/
def alternatingTransport
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (data : R324WithinHalfNextExceptionalStop res scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (sub :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)) :
    R324WithinHalfAlternatingTransport res where
  final := sub.final
  final_remaining := sub.final_remaining
  embedding := fun i =>
    data.trace.stopCoordinateEmbedding
      (data.trace.stopPrefix.postSurvivingCoordinate
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        (sub.embedding i))
  embedding_val := by
    intro i
    rw [data.trace.stopCoordinateEmbedding_val]
    exact sub.embedding_val i
  projection := fun v =>
    sub.projection
      ((data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        (data.trace.stopProjection v)).2)
  projection_apply := by
    intro v i
    simp only [sub.projection_apply,
      splitSurvivingPiMeasurableEquiv_apply_snd,
      R324WithinHalfStopBeforeStepTrace.stopProjection_apply]
  multiplier := fun k =>
    sub.multiplier k *
      data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq k
  transport := by
    intro x y k coefficient hfull
    have h1 :=
      data.lamEps_pow_integral_incomingPhasedResidualDensity_eq_afterHead
        hε hε1 x y
        (fun v => coefficient (sub.projection v)) k hfull
    have hpost :=
      data.integrable_afterHead_incomingPhasedResidualDensity
        hε hε1 x y
        (fun v => coefficient (sub.projection v)) k hfull
    have h2 :=
      sub.transport x y k
        (fun u =>
          data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq k *
            coefficient u)
        hpost
    have h3 :
        (∫ u : sub.final.SurvivingCoordinate → T4,
          sub.final.incomingPhasedResidualDensity
            (sub.multiplier k *
              (data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq k *
                coefficient u))
            k ρ ε x y u
          ∂Measure.pi fun _ => paperMeasure) =
        ∫ u : sub.final.SurvivingCoordinate → T4,
          sub.final.incomingPhasedResidualDensity
            ((sub.multiplier k *
              data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq k) *
              coefficient u)
            k ρ ε x y u
          ∂Measure.pi fun _ => paperMeasure := by
      apply integral_congr_ae
      filter_upwards with u
      rw [mul_assoc]
    exact (h1.trans h2).trans h3
  integrable := by
    intro x y k coefficient hfull
    have hpost :=
      data.integrable_afterHead_incomingPhasedResidualDensity
        hε hε1 x y
        (fun v => coefficient (sub.projection v)) k hfull
    have h :=
      sub.integrable x y k
        (fun u =>
          data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq k *
            coefficient u)
        hpost
    apply h.congr
    filter_upwards with u
    simp only [mul_assoc]
  integrable_joint := by
    intro Y _ ν _ x y k coefficient hfull
    have hpost :=
      data.integrable_joint_afterHead_incomingPhasedResidualDensity
        ν hε hε1 x y
        (fun parameter v => coefficient parameter (sub.projection v))
        k hfull
    have h :=
      sub.integrable_joint ν x y k
        (fun parameter u =>
          data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq k *
            coefficient parameter u)
        hpost
    apply h.congr
    filter_upwards with p
    simp only [mul_assoc]

end R324WithinHalfNextExceptionalStop

/-! ## The alternating driver -/

/-- The order ledger of the alternation: the retained suffix past the next
exceptional stop is strictly shorter than the remaining list, because the
consumed ordinary run and the retained head are genuinely dropped. -/
theorem R324WithinHalfNextExceptionalStop.suffix_length_lt
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (data : R324WithinHalfNextExceptionalStop res scale) :
    data.suffix.length < res.remaining.length := by
  have hlen := congrArg List.length data.remaining_eq
  simp only [List.length_append, List.length_cons] at hlen
  omega

namespace R324WithinHalfAlternatingTransport

/-- **The alternating driver.**  By strong induction on the remaining
list: the longest ordinary run either exhausts the remaining list and the
certified analytic trace finishes the transport, or it stops at a
slot-zero-fed head, which the general-state exceptional collapse absorbs
before the strictly shorter after-head suffix recurses.  Every ordinary
Fubini charge and every exceptional Proposition 4.1 charge is consumed
from the certificates produced by the local block provider; no external
charge hypothesis is taken. -/
def of_localBlockProvider
    {C K : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing)
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale) :
    R324WithinHalfAlternatingTransport res :=
  if hrun :
      r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining =
        res.remaining.length then
    let trace :=
      R324WithinHalfCertifiedAnalyticTrace.of_localBlockProvider
        hε hε1 provider res scale certificate
    trace.alternatingTransport
      (trace.ordinaryAlong_of_ordinaryRunLength_eq_length
        hrun)
  else
    have hlt :
        r324WithinHalfOrdinaryRunLength
            res.state.processed res.remaining <
          res.remaining.length :=
      lt_of_le_of_ne
        (r324WithinHalfOrdinaryRunLength_le_length
          res.state.processed res.remaining) hrun
    have data : R324WithinHalfNextExceptionalStop res scale :=
      (nonempty_r324WithinHalfNextExceptionalStop_of_lt_length
        hε hε1 provider res scale certificate hlt).some
    data.alternatingTransport hε hε1
      (of_localBlockProvider hε hε1 provider
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)
        (r324WithinHalfUpdatedEdgeScale
          (data.trace.stopPrefix.headContext
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq)
          data.trace.stopScale C lam K)
        (provider data.trace.stopPrefix
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq
          data.trace.stopScale
          data.trace.stopCertificate).2)
termination_by res.remaining.length
decreasing_by
  simp only [R324WithinHalfResidualPrefix.afterHead_remaining]
  exact
    R324WithinHalfResidualPrefix.R324WithinHalfNextExceptionalStop.suffix_length_lt
      _

/-- Consumer form of the driver transport with the accumulated multiplier
outside the terminal integral. -/
theorem lamEps_pow_integral_incomingPhasedResidualDensity_eq_multiplier_mul_final
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    (t : R324WithinHalfAlternatingTransport res)
    (x y : T4) (k : Z4)
    (coefficient :
      (t.final.SurvivingCoordinate → T4) → ℂ)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (coefficient (t.projection w)) k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ w : res.SurvivingCoordinate → T4,
          res.incomingPhasedResidualDensity
            (coefficient (t.projection w)) k ρ ε x y w
          ∂Measure.pi fun _ => paperMeasure) =
      t.multiplier k *
        ∫ u : t.final.SurvivingCoordinate → T4,
          t.final.incomingPhasedResidualDensity
            (coefficient u) k ρ ε x y u
          ∂Measure.pi fun _ => paperMeasure := by
  rw [t.transport x y k coefficient hfull,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  exact
    t.final.incomingPhasedResidualDensity_const_mul
      (t.multiplier k) (coefficient u) k ρ ε x y u

end R324WithinHalfAlternatingTransport

end R324WithinHalfResidualPrefix

end

end Anderson4D
