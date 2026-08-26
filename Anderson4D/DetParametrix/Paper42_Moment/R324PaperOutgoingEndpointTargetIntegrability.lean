import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointTwoHalfSplice

/-!
# Signed integrability after a retained outgoing terminal

This lower-level file supplies the exact signed Fubini license used after a
retained outgoing terminal in paper Step 4(A).  No endpoint norm or positive
majorant is introduced.
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
    {alpha beta : Z4}

namespace R324PaperOutgoingEndpointTerminal

/-! ## Signed Fubini license for a retained outgoing terminal -/

/-- Joint integrability survives the retained outgoing terminal operation
with an arbitrary measured parameter outside.  The proof follows the exact
paper coordinates `(first, gap, internal, outgoing endpoint)`: it transports
the given stop density by measure-preserving equivalences and then takes the
three signed marginals exposed by
`integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect`.

This is an integrability statement only.  It neither bounds nor replaces the
signed defect density by a positive majorant. -/
theorem integrable_parameter_outgoingEndpointDefectDensity
    {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.terminalPost.state.active.Nonempty)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U) [SFinite muU]
    (coefficient : U ->
      (data.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (incomingMode outgoingMode : Z4)
    (x : U -> T4)
    (hsource :
      Integrable
        (fun q : U ×
            (T4 × (data.endpoint.stop.SurvivingCoordinate -> T4)) =>
          data.endpoint.stop.incomingPhasedResidualDensity
            (coefficient q.1
              ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
                data.terminalData.terminal [] data.endpoint.stop_remaining
                q.2.2).2))
            incomingMode rho eps (x q.1) q.2.1 q.2.2)
        (muU.prod (paperMeasure.prod
          (Measure.pi fun _ : data.endpoint.stop.SurvivingCoordinate =>
            paperMeasure))))
    (hint :
      forall (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder
                data.terminalData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.terminalData.terminal.2 - 2) -> T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder
                data.terminalData.terminal.2)
              kappaB.1 data.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun q : U ×
          (data.terminalPost.SurvivingCoordinate -> T4) =>
        ∫ first : T4,
          data.outgoingEndpointDefectDensity
            (coefficient q.1) incomingMode outgoingMode (x q.1)
            q.2 first
          ∂paperMeasure)
      (muU.prod (Measure.pi fun _ :
        data.terminalPost.SurvivingCoordinate => paperMeasure)) := by
  let n := residualBlockOrder data.terminalData.terminal.2
  let Tuple := Fin (2 * n) -> T4
  let Internal := Fin (2 * n - 2) -> T4
  let Stop := data.endpoint.stop.SurvivingCoordinate -> T4
  let Post := data.terminalPost.SurvivingCoordinate -> T4
  let muTuple : Measure Tuple := Measure.pi fun _ => paperMeasure
  let muInternal : Measure Internal := Measure.pi fun _ => paperMeasure
  let muStop : Measure Stop := Measure.pi fun _ => paperMeasure
  let muPost : Measure Post := Measure.pi fun _ => paperMeasure
  let split := data.endpoint.stop.splitSurvivingPiMeasurableEquiv
    data.terminalData.terminal [] data.endpoint.stop_remaining
  have hsplit : MeasurePreserving split muStop (muTuple.prod muPost) := by
    dsimp only [split, muStop, muTuple, muPost, Tuple, Stop, Post, n]
    exact data.endpoint.stop
      |>.measurePreserving_splitSurvivingPiMeasurableEquiv
        data.terminalData.terminal [] data.endpoint.stop_remaining
  let primitive :=
    r324PrimitiveHeadFirstOutgoingGapMeasurableEquiv
      n data.terminalContext.one_le_blockOrder
  have hprimitive : MeasurePreserving primitive muTuple
      ((paperMeasure.prod paperMeasure).prod muInternal) := by
    dsimp only [primitive, muTuple, muInternal, Tuple, Internal, n]
    exact
      measurePreserving_r324PrimitiveHeadFirstOutgoingGapMeasurableEquiv
        (residualBlockOrder data.terminalData.terminal.2)
        data.terminalContext.one_le_blockOrder
  let stopRegroup : T4 × Stop ≃ᵐ Post × (Tuple × T4) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl T4) split).trans
      (r324OutgoingTerminalJointRegroupMeasurableEquiv
        T4 Tuple Post)
  have hstopRegroup : MeasurePreserving stopRegroup
      (paperMeasure.prod muStop)
      (muPost.prod (muTuple.prod paperMeasure)) := by
    exact
      (measurePreserving_r324OutgoingTerminalJointRegroupMeasurableEquiv
          paperMeasure muTuple muPost).comp
        ((MeasurePreserving.id paperMeasure).prod hsplit)
  let headOrder : ((T4 × T4) × Internal) × T4 ≃ᵐ
      T4 × (T4 × (Internal × T4)) :=
    (MeasurableEquiv.prodAssoc
      (α := T4 × T4) (β := Internal) (γ := T4)).trans
      (MeasurableEquiv.prodAssoc
        (α := T4) (β := T4) (γ := Internal × T4))
  have hheadOrder : MeasurePreserving headOrder
      ((((paperMeasure.prod paperMeasure).prod muInternal).prod paperMeasure))
      (paperMeasure.prod
        (paperMeasure.prod (muInternal.prod paperMeasure))) := by
    exact
      (measurePreserving_prodAssoc paperMeasure paperMeasure
        (muInternal.prod paperMeasure)).comp
      (measurePreserving_prodAssoc
        (paperMeasure.prod paperMeasure) muInternal paperMeasure)
  let reindexHead : Tuple × T4 ≃ᵐ
      T4 × (T4 × (Internal × T4)) :=
    (MeasurableEquiv.prodCongr primitive
      (MeasurableEquiv.refl T4)).trans headOrder
  have hreindexHead : MeasurePreserving reindexHead
      (muTuple.prod paperMeasure)
      (paperMeasure.prod
        (paperMeasure.prod (muInternal.prod paperMeasure))) := by
    exact hheadOrder.comp
      (hprimitive.prod (MeasurePreserving.id paperMeasure))
  let regroupHead : U × (Post × (Tuple × T4)) ≃ᵐ
      U × (Post × (T4 × (T4 × (Internal × T4)))) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl U)
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Post) reindexHead)
  have hregroupHead : MeasurePreserving regroupHead
      (muU.prod (muPost.prod (muTuple.prod paperMeasure)))
      (muU.prod (muPost.prod
        (paperMeasure.prod
          (paperMeasure.prod (muInternal.prod paperMeasure))))) := by
    exact (MeasurePreserving.id muU).prod
      ((MeasurePreserving.id muPost).prod hreindexHead)
  let Rest := T4 × (Internal × T4)
  let muRest : Measure Rest :=
    paperMeasure.prod (muInternal.prod paperMeasure)
  let finalAssoc : U × (Post × (T4 × Rest)) ≃ᵐ
      (U × (Post × T4)) × Rest :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl U)
      (MeasurableEquiv.prodAssoc
        (α := Post) (β := T4) (γ := Rest)).symm).trans
      (MeasurableEquiv.prodAssoc
        (α := U) (β := Post × T4) (γ := Rest)).symm
  have hfinalAssoc : MeasurePreserving finalAssoc
      (muU.prod (muPost.prod (paperMeasure.prod muRest)))
      ((muU.prod (muPost.prod paperMeasure)).prod muRest) := by
    exact
      (measurePreserving_prodAssoc muU (muPost.prod paperMeasure)
        muRest).symm.comp
      ((MeasurePreserving.id muU).prod
        (measurePreserving_prodAssoc muPost paperMeasure muRest).symm)
  let total : U × (T4 × Stop) ≃ᵐ
      (U × (Post × T4)) × Rest :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl U)
      stopRegroup).trans (regroupHead.trans finalAssoc)
  have htotal : MeasurePreserving total
      (muU.prod (paperMeasure.prod muStop))
      ((muU.prod (muPost.prod paperMeasure)).prod muRest) := by
    exact hfinalAssoc.comp
      (hregroupHead.comp
        ((MeasurePreserving.id muU).prod hstopRegroup))
  have total_apply (q : U × (T4 × Stop)) :
      total q =
        ((q.1,
            ((split q.2.2).2,
              (primitive (split q.2.2).1).1.1)),
          ((primitive (split q.2.2).1).1.2,
            ((primitive (split q.2.2).1).2, q.2.1))) := by
    rfl
  let source : U × (T4 × Stop) -> Complex := fun q =>
    charT4 outgoingMode q.2.1 *
      data.endpoint.stop.incomingPhasedResidualDensity
        (coefficient q.1 (split q.2.2).2)
        incomingMode rho eps (x q.1) q.2.1 q.2.2
  have hphaseMeas : Measurable
      (fun q : U × (T4 × Stop) => charT4 outgoingMode q.2.1) :=
    (continuous_charT4 outgoingMode).measurable.comp
      (measurable_fst.comp measurable_snd)
  have hsourcePhase : Integrable source
      (muU.prod (paperMeasure.prod muStop)) := by
    have hmul := hsource.bdd_mul hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by rw [norm_charT4])
    apply hmul.congr
    filter_upwards with q
    unfold source
    ring
  let raw : ((U × (Post × T4)) × Rest) -> Complex := fun q =>
    charT4 outgoingMode q.2.2.2 *
      data.endpoint.stop.incomingPhasedResidualDensity
        (coefficient q.1.1 q.1.2.1)
        incomingMode rho eps (x q.1.1) q.2.2.2
        (split.symm
          (primitive.symm ((q.1.2.2, q.2.1), q.2.2.1), q.1.2.1))
  have hraw : Integrable raw
      ((muU.prod (muPost.prod paperMeasure)).prod muRest) := by
    refine (htotal.integrable_comp_emb total.measurableEmbedding).mp ?_
    apply hsourcePhase.congr
    filter_upwards with q
    show source q = raw (total q)
    rw [total_apply]
    unfold source raw
    dsimp only
    rw [MeasurableEquiv.symm_apply_apply]
    rw [Prod.eta (split q.2.2), MeasurableEquiv.symm_apply_apply]
  have hmarg := hraw.integral_prod_left
  have hscaled := hmarg.const_mul
    ((lamEps lam eps : Complex) ^ (2 * n))
  have hdefect : Integrable
      (fun q : U × (Post × T4) =>
        data.outgoingEndpointDefectDensity
          (coefficient q.1) incomingMode outgoingMode (x q.1)
          q.2.1 q.2.2)
      (muU.prod (muPost.prod paperMeasure)) := by
    apply hscaled.congr
    filter_upwards [hraw.prod_right_ae] with q hq
    change
      (lamEps lam eps : Complex) ^ (2 * n) *
          (∫ r : Rest, raw (q, r) ∂muRest) = _
    calc
      (lamEps lam eps : Complex) ^ (2 * n) *
          (∫ r : Rest, raw (q, r) ∂muRest) =
        ∫ gap : T4,
          (lamEps lam eps : Complex) ^ (2 * n) *
            (∫ p : Internal × T4, raw (q, (gap, p))
              ∂(muInternal.prod paperMeasure))
          ∂paperMeasure := by
            rw [integral_prod _ hq, ← integral_const_mul]
      _ = ∫ gap : T4,
          (lamEps lam eps : Complex) ^ (2 * n) *
            (∫ internal : Internal,
              ∫ y : T4, raw (q, (gap, internal, y))
                ∂paperMeasure
              ∂muInternal)
          ∂paperMeasure := by
            apply integral_congr_ae
            filter_upwards [hq.prod_right_ae] with gap hgap
            rw [integral_prod _ hgap]
      _ = ∫ gap : T4,
          (lamEps lam eps : Complex) ^ (2 * n) *
            (∫ internal : Internal,
              ∫ y : T4,
                charT4 outgoingMode y *
                  ((data.terminalContext.rawLocalIntegrand rho eps
                    (data.terminalPredecessorPoint (x q.1) q.2.1 - y)
                    (fun j =>
                      primitiveAssemble n
                        data.terminalContext.one_le_blockOrder
                        q.2.2 (q.2.2 - gap) internal j - y) : Complex) *
                    data.terminalSplitOuter
                      (coefficient q.1) incomingMode (x q.1) q.2.1)
                ∂paperMeasure
              ∂muInternal)
          ∂paperMeasure := by
            apply integral_congr_ae
            filter_upwards with gap
            apply congrArg
            apply integral_congr_ae
            filter_upwards with internal
            apply integral_congr_ae
            filter_upwards with y
            simp only [raw, primitive,
              r324PrimitiveHeadFirstOutgoingGapMeasurableEquiv_symm_apply,
              n, Internal]
            rw [data.incomingPhasedResidualDensity_terminal_split_eq_rawLocal_mul_outer
              hpred hactive (coefficient q.1) incomingMode (x q.1) y]
      _ = data.outgoingEndpointDefectDensity
          (coefficient q.1) incomingMode outgoingMode (x q.1)
          q.2.1 q.2.2 := by
            simpa only [n, Internal,
              R324PaperOutgoingEndpointTerminal.outgoingEndpointDefectDensity,
              incomingExceptionalPrimitiveDefect] using
              data.integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
                outgoingMode
                (data.terminalPredecessorPoint (x q.1) q.2.1)
                q.2.2
                (data.terminalSplitOuter
                  (coefficient q.1) incomingMode (x q.1) q.2.1)
                (hint · q.2.2)
  let assoc : U × (Post × T4) ≃ᵐ (U × Post) × T4 :=
    (MeasurableEquiv.prodAssoc
      (α := U) (β := Post) (γ := T4)).symm
  have hassoc : MeasurePreserving assoc
      (muU.prod (muPost.prod paperMeasure))
      ((muU.prod muPost).prod paperMeasure) :=
    (measurePreserving_prodAssoc muU muPost paperMeasure).symm
  let finalRaw : (U × Post) × T4 -> Complex := fun q =>
    data.outgoingEndpointDefectDensity
      (coefficient q.1.1) incomingMode outgoingMode (x q.1.1)
      q.1.2 q.2
  have hfinalRaw : Integrable finalRaw
      ((muU.prod muPost).prod paperMeasure) := by
    refine (hassoc.integrable_comp_emb assoc.measurableEmbedding).mp ?_
    apply hdefect.congr
    filter_upwards with q
    rfl
  simpa only [Post, muPost, finalRaw] using hfinalRaw.integral_prod_left

/-- Transport the signed target integrability across equality of retained
outgoing-terminal presentations.  This is useful for the `DE` geometry,
whose canonical presentation is propositionally (not definitionally) the
route presentation. -/
theorem integrable_parameter_outgoingEndpointDefectDensity_transport
    {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    {left right : R324PaperOutgoingEndpointTerminal res}
    (h : left = right)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U)
    (coefficient : U →
      (right.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4)
    (x : U → T4)
    (hintegrable : Integrable
      (fun q : U ×
          (left.terminalPost.SurvivingCoordinate → T4) =>
        ∫ first : T4,
          left.outgoingEndpointDefectDensity
            (Eq.mp
              (congrArg
                (fun data : R324PaperOutgoingEndpointTerminal res =>
                  (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
                h).symm
              (coefficient q.1))
            incomingMode outgoingMode (x q.1) q.2 first
          ∂paperMeasure)
      (muU.prod (Measure.pi fun _ :
        left.terminalPost.SurvivingCoordinate => paperMeasure))) :
    Integrable
      (fun q : U ×
          (right.terminalPost.SurvivingCoordinate → T4) =>
        ∫ first : T4,
          right.outgoingEndpointDefectDensity
            (coefficient q.1) incomingMode outgoingMode (x q.1)
            q.2 first
          ∂paperMeasure)
      (muU.prod (Measure.pi fun _ :
        right.terminalPost.SurvivingCoordinate => paperMeasure)) := by
  cases h
  exact hintegrable

end R324PaperOutgoingEndpointTerminal

end R324WithinHalfResidualPrefix

end

end Anderson4D
