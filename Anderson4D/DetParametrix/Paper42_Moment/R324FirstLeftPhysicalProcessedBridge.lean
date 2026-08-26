import Anderson4D.DetParametrix.Paper42_Moment.R324FirstLeftPhysicalRouting
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfProcessedFubini

/-!
# Physical coordinates at an R-324 first-left processed step

The first-left routing theorem exposes the actual selected coordinates of
the original deterministic moment fibre.  The collapse theorem, on the
other hand, is written in a standard `Fin (2n)` coordinate with the active
successor translated to zero.  This file supplies that coordinate bridge.

No unintegrated original integrand is identified with a state after an
earlier block has already been integrated.  The pointwise statements below
only reconstruct the current, still unintegrated block.  State replacement
is performed only under the corresponding spatial integral.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The selected physical tuple -/

/-- The left-copy spatial tuple inside the doubled moment coordinate. -/
def r324LeftPhysicalTuple
    {m : ℕ} (v : Fin (2 * m) → T4) : Fin m → T4 :=
  fun i => v (leftMomentIndex i)

/-- The canonical standard tuple of the genuine first-left block. -/
def r324FirstLeftPhysicalBlockTuple
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (v : Fin (2 * m) → T4) :
    Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4 :=
  fun i =>
    v (leftMomentIndex
      ((residualPrimitiveBlockOrderIso e₀.1
        (selectedExtractionBlock e₀.1 Finset.univ hleft)
        (selectRel_isRelFullyPaired
          e₀.1 Finset.univ hleft).isFullyPairedOn i).1))

/-- Reassemble a doubled physical tuple from a fixed complementary tuple
and a canonical standard tuple on the genuine first-left block. -/
def r324FirstLeftPhysicalReconstruct
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4) :
    Fin (2 * m) → T4 :=
  (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (2 * m) => T4)
      (r324FirstLeftSelected e₀ hleft)).symm
    (r324FirstLeftSelectedTupleMeasurableEquiv e₀ hleft t, vC)

/-- Actual coordinate reconstruction reads the supplied standard tuple
back on the genuine first-left block. -/
@[simp]
theorem r324FirstLeftPhysicalBlockTuple_reconstruct
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (vC :
      (i : {i : Fin (2 * m) //
        ¬r324FirstLeftSelected e₀ hleft i}) → T4)
    (t :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4) :
    r324FirstLeftPhysicalBlockTuple e₀ hleft
        (r324FirstLeftPhysicalReconstruct e₀ hleft vC t) =
      t := by
  funext i
  unfold r324FirstLeftPhysicalBlockTuple
    r324FirstLeftPhysicalReconstruct
  let j :=
    r324FirstLeftSelectedCoordinateEquiv e₀ hleft i
  have hj :
      (j : Fin (2 * m)) =
        leftMomentIndex
          ((residualPrimitiveBlockOrderIso e₀.1
            (selectedExtractionBlock e₀.1 Finset.univ hleft)
            (selectRel_isRelFullyPaired
              e₀.1 Finset.univ hleft).isFullyPairedOn i).1) := by
    exact r324FirstLeftSelectedCoordinateEquiv_apply_val
      e₀ hleft i
  rw [← hj]
  let split :=
    MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin (2 * m) => T4)
      (r324FirstLeftSelected e₀ hleft)
  have hsplit :=
    congrArg (fun p => p.1 j)
      (split.apply_symm_apply
        (r324FirstLeftSelectedTupleMeasurableEquiv
          e₀ hleft t, vC))
  exact hsplit.trans
    (r324FirstLeftSelectedTupleMeasurableEquiv_apply
      e₀ hleft t i)

/-! ## Literal production-chain coordinates -/

/-- The canonical increasing enumeration of the genuine first-left interval
is the literal affine enumeration from its selected left endpoint. -/
theorem r324FirstLeft_residualOrderIso_apply_val
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (j : Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft))) :
    (residualPrimitiveBlockOrderIso e₀.1
        (selectedExtractionBlock e₀.1 Finset.univ hleft)
        (selectRel_isRelFullyPaired
          e₀.1 Finset.univ hleft).isFullyPairedOn j).1.val =
      (selectRel e₀.1 Finset.univ hleft).1.val + j.val := by
  let B :=
    selectedExtractionBlock e₀.1 Finset.univ hleft
  let p := selectRel e₀.1 Finset.univ hleft
  let hfull : IsFullyPairedOn e₀.1 B :=
    (selectRel_isRelFullyPaired
      e₀.1 Finset.univ hleft).isFullyPairedOn
  let hcard : B.card = 2 * residualBlockOrder B :=
    (Nat.two_mul_div_two_of_even
      (residualBlock_card_even e₀.1 B hfull)).symm
  let f : Fin (2 * residualBlockOrder B) → Fin m :=
    fun i =>
      ⟨p.1.val + i.val, by
        have hi := i.isLt
        have hspan := r324FirstLeft_endpoint_span e₀ hleft
        have hb := p.2.isLt
        dsimp only [B, p] at hi hspan hb ⊢
        omega⟩
  have hfmem : ∀ i, f i ∈ B := by
    intro i
    dsimp only [B]
    rw [r324FirstLeft_selectedBlock_eq_Icc]
    apply Finset.mem_Icc.mpr
    constructor
    · exact Fin.mk_le_mk.mpr (Nat.le_add_right _ _)
    · apply Fin.mk_le_mk.mpr
      have hi := i.isLt
      have hspan := r324FirstLeft_endpoint_span e₀ hleft
      have hab :=
        (selectRel_isRelFullyPaired
          e₀.1 Finset.univ hleft).le
      change
        p.2.val + 1 - p.1.val =
          2 * residualBlockOrder B at hspan
      change i.val < 2 * residualBlockOrder B at hi
      change p.1.val + i.val ≤ p.2.val
      omega
  have hfmono : StrictMono f := by
    intro i k hik
    apply Fin.mk_lt_mk.mpr
    exact Nat.add_lt_add_left hik _
  have henum :
      f = B.orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard hfmem hfmono
  change
    ((B.orderIsoOfFin _ j : B).1.val =
      p.1.val + j.val)
  rw [Finset.coe_orderIsoOfFin_apply]
  rw [← congrFun henum j]

/-- The physical block tuple is exactly the selected carrier tuple in the
assembled production Green chain. -/
theorem r324FirstLeftCarrierTuple_assemble_eq_physicalBlockTuple
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4) :
    r324FirstLeftCarrierTuple e₀ hleft
        (assemble x y (r324LeftPhysicalTuple v)) =
      r324FirstLeftPhysicalBlockTuple e₀ hleft v := by
  funext i
  unfold r324FirstLeftCarrierTuple
    r324FirstLeftPhysicalBlockTuple r324LeftPhysicalTuple
  rw [← assemble_varIdx x y
    (fun k => v (leftMomentIndex k))
    ((residualPrimitiveBlockOrderIso e₀.1
      (selectedExtractionBlock e₀.1 Finset.univ hleft)
      (selectRel_isRelFullyPaired
        e₀.1 Finset.univ hleft).isFullyPairedOn i).1)]
  congr 1
  apply Fin.ext
  simp only [varIdx_val]
  rw [r324FirstLeft_residualOrderIso_apply_val]
  omega

/-! ## The honest empty-prefix state -/

/-- The genuine selected block as a certified step from the all-Green
initial state, in the branch where it is the analytic head. -/
def r324FirstLeftInitialStepContext
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (tail : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule e₀.1 =
        r324FirstLeftSelectedStep e₀ hleft :: tail) :
    R324WithinHalfStepContext e₀.1 where
  state := r324InitialWithinHalfEdgeState m
  step := r324FirstLeftSelectedStep e₀ hleft
  suffix := tail
  schedule_eq := by
    simpa [r324InitialWithinHalfEdgeState] using hschedule

/-- The actual production-chain point immediately after the selected
first-left block. -/
def r324FirstLeftPhysicalSuccessor
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4) : T4 :=
  assemble x y (r324LeftPhysicalTuple v)
    (r324FirstLeftOutgoingEdge e₀ hleft).succ

/-- The actual production-chain point immediately before the selected
first-left block. -/
def r324FirstLeftPhysicalPredecessor
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4) : T4 :=
  assemble x y (r324LeftPhysicalTuple v)
    (r324FirstLeftPredecessorEdge e₀ hleft).castSucc

/-- Translation-normalized physical first-left tuple. -/
def r324FirstLeftTranslatedPhysicalBlockTuple
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4) :
    Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4 :=
  fun i =>
    r324FirstLeftPhysicalBlockTuple e₀ hleft v i -
      r324FirstLeftPhysicalSuccessor e₀ hleft x y v

/-! ## Complex outer factors -/

namespace R324WithinHalfStepContext

variable {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)

/-- The real processed collapse may carry the complex outer factor of the
physical moment integrand.  The state changes only under the local spatial
integral. -/
theorem rawLocalSpatialIntegral_mul_complexOuter_eq_absorb
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (u : T4) (outer : ℂ)
    (hstandard :
      Integrable (ctx.localIntegrand ρ ε u)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder ctx.step.2)
                κB.1 ctx.internalEdges
                (primitiveAssemble
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε ^
          (2 * residualBlockOrder ctx.step.2) : ℂ) *
        (∫ t : Fin (2 * residualBlockOrder ctx.step.2) → T4,
          (ctx.rawLocalIntegrand ρ ε u t : ℂ) * outer
          ∂Measure.pi fun _ => paperMeasure) =
      ((ctx.absorb ρ lam ε).edges
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step) u : ℂ) * outer := by
  have hreal :
      lamEps lam ε ^
            (2 * residualBlockOrder ctx.step.2) *
          (∫ t : Fin (2 * residualBlockOrder ctx.step.2) → T4,
            ctx.rawLocalIntegrand ρ ε u t
            ∂Measure.pi fun _ => paperMeasure) =
        (ctx.absorb ρ lam ε).edges
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step) u := by
    simp_rw [ctx.rawLocalIntegrand_eq_localIntegrand]
    exact ctx.localSpatialIntegral_eq_absorb_predecessor
      ρ lam ε u hstandard hinternal
  have hcast := congrArg (fun a : ℝ => (a : ℂ)) hreal
  push_cast at hcast
  rw [integral_mul_const]
  rw [integral_complex_ofReal]
  rw [← mul_assoc]
  rw [hcast]

/-- Outer-Fubini form of the complex physical update. -/
theorem integral_outer_rawLocalIntegrand_complex_eq_absorb
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (u : Ω → T4) (outer : Ω → ℂ)
    (hstandard :
      ∀ᵐ ω ∂ν,
        Integrable (ctx.localIntegrand ρ ε (u ω))
          (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder ctx.step.2)
                κB.1 ctx.internalEdges
                (primitiveAssemble
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    (∫ ω,
        (lamEps lam ε ^
            (2 * residualBlockOrder ctx.step.2) : ℂ) *
          (∫ t :
              Fin (2 * residualBlockOrder ctx.step.2) → T4,
            (ctx.rawLocalIntegrand ρ ε (u ω) t : ℂ) *
              outer ω
            ∂Measure.pi fun _ => paperMeasure)
        ∂ν) =
      ∫ ω,
        ((ctx.absorb ρ lam ε).edges
            (r324WithinHalfPredecessorSlot
              ctx.state ctx.step) (u ω) : ℂ) *
          outer ω
        ∂ν := by
  apply integral_congr_ae
  filter_upwards [hstandard] with ω hω
  exact ctx.rawLocalSpatialIntegral_mul_complexOuter_eq_absorb
    ρ lam ε (u ω) (outer ω) hω hinternal

end R324WithinHalfStepContext

end

end Anderson4D
