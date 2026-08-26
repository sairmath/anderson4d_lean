import Anderson4D.DetParametrix.Paper42_Moment.R324NestedCrossResidualState
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticReachableIntegrability

/-!
# Exact and quantitative nested cross steps for R-324

Paper §4.2 Step 3 removes the surviving cross-cut primitive blocks from
inside to outside.  This file attaches all data used by one such removal to
the same proof-relevant head context:

* the literal residual prefix and its next suffix;
* the canonical increasing reindexing of the current sparse block;
* the two indices carrying the moving central-gap numerator in (4.20);
* a measure-preserving split of the current surviving coordinates into the
  current block and the next suffix;
* the exact central-gap primitive term and its domination by the inserted
  Proposition 4.1 term; and
* the exact perturbative-order and numerical scale ledgers after the head is
  removed.

The endpoint routing of paper Step 4 is deliberately not folded into this
state.  Its direct and shortcut branches have different terminal
majorants.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## One literal nonterminal/terminal cross head -/

/-- All structural data of one literal head in the nested cross schedule. -/
structure R324NestedCrossStepContext
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) where
  residual : R324NestedCrossResidualPrefix κp κm π
  head : R324NestedCrossBlock κp κm π
  tail : List (R324NestedCrossBlock κp κm π)
  remaining_eq : residual.remaining = head :: tail

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- The literal suffix after deleting the current inside-most head. -/
def next
    (ctx : R324NestedCrossStepContext κp κm π) :
    R324NestedCrossResidualPrefix κp κm π :=
  ctx.residual.afterHead ctx.head ctx.tail ctx.remaining_eq

/-- The exact perturbative order of the current sparse block. -/
def order
    (ctx : R324NestedCrossStepContext κp κm π) : ℕ :=
  residualBlockOrder ctx.head.carrier

theorem one_le_order
    (ctx : R324NestedCrossStepContext κp κm π) :
    1 ≤ ctx.order :=
  ctx.head.one_le_order

/-- Membership of the current head in the original, possibly-empty block
schedule. -/
theorem collapseMem
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.head.carrier ∈
      momentResidualCollapseBlocks κp κm π :=
  (mem_nonemptyMomentResidualCollapseBlocks.mp
    ctx.head.mem_schedule).1

/-- Closure of the current head under the combined moment pairing. -/
theorem fullyPaired
    (ctx : R324NestedCrossStepContext κp κm π) :
    IsFullyPairedOn
      (momentCombinedPairing κp κm π)
      ctx.head.carrier :=
  momentResidualCollapseBlock_isFullyPairedOn_of_mem
    κp κm π ctx.head.carrier ctx.collapseMem

/-- Relative primitivity of the current head. -/
theorem relativelyPrimitive
    (ctx : R324NestedCrossStepContext κp κm π) :
    IsRelPrimitiveOn
      (momentCombinedPairing κp κm π)
      ctx.head.carrier :=
  momentResidualCollapseBlock_isRelPrimitiveOn_of_mem
    κp κm π ctx.head.carrier ctx.collapseMem

/-- Canonical increasing coordinates on the current sparse head. -/
def blockOrderIso
    (ctx : R324NestedCrossStepContext κp κm π) :
    Fin (2 * ctx.order) ≃o ctx.head.carrier :=
  residualPrimitiveBlockOrderIso
    (momentCombinedPairing κp κm π)
    ctx.head.carrier ctx.fullyPaired

/-- Canonical primitive full pairing transported to standard block
coordinates. -/
def blockPairing
    (ctx : R324NestedCrossStepContext κp κm π) :
    PartialPairing (Fin (2 * ctx.order)) :=
  residualPrimitiveBlockPairing
    (momentCombinedPairing κp κm π)
    ctx.head.carrier ctx.fullyPaired

theorem blockPairing_mem
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.blockPairing ∈ primitiveFullPairings ctx.order := by
  exact
    residualPrimitiveBlockPairing_mem
      (momentCombinedPairing κp κm π)
      ctx.head.carrier ctx.fullyPaired
      ctx.relativelyPrimitive

/-- Standard block index of the last current left coordinate. -/
def leftGapIndex
    (ctx : R324NestedCrossStepContext κp κm π) :
    Fin (2 * ctx.order) :=
  ctx.blockOrderIso.symm
    ⟨ctx.head.leftGap, ctx.head.leftGap_mem⟩

/-- Standard block index of the first current right coordinate. -/
def rightGapIndex
    (ctx : R324NestedCrossStepContext κp κm π) :
    Fin (2 * ctx.order) :=
  ctx.blockOrderIso.symm
    ⟨ctx.head.rightGap, ctx.head.rightGap_mem⟩

theorem blockOrderIso_leftGapIndex
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.blockOrderIso ctx.leftGapIndex =
      ⟨ctx.head.leftGap, ctx.head.leftGap_mem⟩ :=
  ctx.blockOrderIso.apply_symm_apply _

theorem blockOrderIso_rightGapIndex
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.blockOrderIso ctx.rightGapIndex =
      ⟨ctx.head.rightGap, ctx.head.rightGap_mem⟩ :=
  ctx.blockOrderIso.apply_symm_apply _

theorem leftGapIndex_lt_rightGapIndex
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.leftGapIndex < ctx.rightGapIndex := by
  apply ctx.blockOrderIso.lt_iff_lt.mp
  rw [ctx.blockOrderIso_leftGapIndex,
    ctx.blockOrderIso_rightGapIndex]
  change ctx.head.leftGap < ctx.head.rightGap
  exact ctx.head.leftGap_lt_rightGap

theorem leftGapIndex_ne_rightGapIndex
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.leftGapIndex ≠ ctx.rightGapIndex :=
  ne_of_lt ctx.leftGapIndex_lt_rightGapIndex

/-! ## Exact coordinate split and Fubini -/

/-- Coordinates still present at the current cross prefix. -/
def SurvivingCoordinate
    (ctx : R324NestedCrossStepContext κp κm π) : Type :=
  {i : Fin (2 * m) // i ∈ ctx.residual.activeCarrier}

noncomputable instance survivingCoordinateFintype
    (ctx : R324NestedCrossStepContext κp κm π) :
    Fintype ctx.SurvivingCoordinate :=
  show Fintype
    {i : Fin (2 * m) //
      i ∈ ctx.residual.activeCarrier} from
    inferInstance

/-- Coordinates still present after the current head is deleted. -/
def PostCoordinate
    (ctx : R324NestedCrossStepContext κp κm π) : Type :=
  {i : Fin (2 * m) // i ∈ ctx.next.activeCarrier}

noncomputable instance postCoordinateFintype
    (ctx : R324NestedCrossStepContext κp κm π) :
    Fintype ctx.PostCoordinate :=
  show Fintype
    {i : Fin (2 * m) //
      i ∈ ctx.next.activeCarrier} from
    inferInstance

theorem head_subset_activeCarrier
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.head.carrier ⊆ ctx.residual.activeCarrier := by
  intro i hi
  rw [ctx.residual.activeCarrier_head
    ctx.head ctx.tail ctx.remaining_eq]
  exact Finset.mem_union_left _ hi

/-- Ambiently labelled coordinates of the current head. -/
abbrev HeadCoordinate
    (ctx : R324NestedCrossStepContext κp κm π) : Type :=
  {i : ctx.SurvivingCoordinate // i.1 ∈ ctx.head.carrier}

/-- Coordinates outside the current head. -/
abbrev OuterCoordinate
    (ctx : R324NestedCrossStepContext κp κm π) : Type :=
  {i : ctx.SurvivingCoordinate // i.1 ∉ ctx.head.carrier}

/-- The ambiently labelled head is exactly the canonical standard primitive
coordinate type. -/
def headCoordinateEquivStandard
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.HeadCoordinate ≃ Fin (2 * ctx.order) where
  toFun i :=
    ctx.blockOrderIso.symm ⟨i.1.1, i.2⟩
  invFun j :=
    let i := ctx.blockOrderIso j
    ⟨⟨i.1, ctx.head_subset_activeCarrier i.2⟩, i.2⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have h :=
      ctx.blockOrderIso.apply_symm_apply
        ⟨i.1.1, i.2⟩
    exact congrArg Subtype.val h
  right_inv j :=
    ctx.blockOrderIso.symm_apply_apply j

/-- The complement of the current head is exactly the next suffix carrier. -/
def outerCoordinateEquivPost
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.OuterCoordinate ≃ ctx.PostCoordinate where
  toFun i := by
    refine ⟨i.1.1, ?_⟩
    have hcarrier :=
      ctx.residual.activeCarrier_head
        ctx.head ctx.tail ctx.remaining_eq
    have hmem :=
      congrArg (fun B : Finset (Fin (2 * m)) =>
        i.1.1 ∈ B) hcarrier
    have hactive :
        i.1.1 ∈
          ctx.head.carrier ∪ ctx.next.activeCarrier :=
      hmem.mp i.1.2
    exact (Finset.mem_union.mp hactive).resolve_left i.2
  invFun i := by
    refine ⟨⟨i.1, ?_⟩, ?_⟩
    · have hcarrier :=
        ctx.residual.activeCarrier_head
          ctx.head ctx.tail ctx.remaining_eq
      have hmem :=
        congrArg (fun B : Finset (Fin (2 * m)) =>
          i.1 ∈ B) hcarrier
      apply hmem.mpr
      exact Finset.mem_union_right _ i.2
    · have hdisjoint :=
        ctx.residual.head_disjoint_afterHead_activeCarrier
          ctx.head ctx.tail ctx.remaining_eq
      intro hi
      exact (Finset.disjoint_left.mp hdisjoint) hi i.2
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

/-- Exact partition of the current carrier into the standard current block
and the next literal suffix. -/
def survivingCoordinateEquivHeadSumPost
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.SurvivingCoordinate ≃
      Fin (2 * ctx.order) ⊕ ctx.PostCoordinate :=
  (Equiv.sumCompl
      (fun i : ctx.SurvivingCoordinate =>
        i.1 ∈ ctx.head.carrier)).symm.trans
    (Equiv.sumCongr
      ctx.headCoordinateEquivStandard
      ctx.outerCoordinateEquivPost)

/-- The measure-theoretic coordinate split used by the Step 3 Fubini
iteration. -/
def splitSurvivingPiMeasurableEquiv
    (ctx : R324NestedCrossStepContext κp κm π) :
    (ctx.SurvivingCoordinate → T4) ≃ᵐ
      (Fin (2 * ctx.order) → T4) ×
        (ctx.PostCoordinate → T4) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : ctx.SurvivingCoordinate => T4)
      ctx.survivingCoordinateEquivHeadSumPost.symm).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin (2 * ctx.order) ⊕
        ctx.PostCoordinate => T4))

/-- The current surviving coordinate corresponding to a standard head
coordinate. -/
def headSurvivingCoordinate
    (ctx : R324NestedCrossStepContext κp κm π)
    (j : Fin (2 * ctx.order)) :
    ctx.SurvivingCoordinate :=
  let i := ctx.blockOrderIso j
  ⟨i.1, ctx.head_subset_activeCarrier i.2⟩

/-- A next-suffix coordinate regarded as a current surviving coordinate. -/
def postSurvivingCoordinate
    (ctx : R324NestedCrossStepContext κp κm π)
    (i : ctx.PostCoordinate) :
    ctx.SurvivingCoordinate :=
  ⟨i.1, by
    rw [ctx.residual.activeCarrier_head
      ctx.head ctx.tail ctx.remaining_eq]
    exact Finset.mem_union_right _ i.2⟩

@[simp]
theorem splitSurvivingPiMeasurableEquiv_apply_fst
    (ctx : R324NestedCrossStepContext κp κm π)
    (v : ctx.SurvivingCoordinate → T4)
    (j : Fin (2 * ctx.order)) :
    (ctx.splitSurvivingPiMeasurableEquiv v).1 j =
      v (ctx.headSurvivingCoordinate j) := by
  rfl

@[simp]
theorem splitSurvivingPiMeasurableEquiv_apply_snd
    (ctx : R324NestedCrossStepContext κp κm π)
    (v : ctx.SurvivingCoordinate → T4)
    (i : ctx.PostCoordinate) :
    (ctx.splitSurvivingPiMeasurableEquiv v).2 i =
      v (ctx.postSurvivingCoordinate i) := by
  rfl

@[simp]
theorem splitSurvivingPiMeasurableEquiv_symm_head
    (ctx : R324NestedCrossStepContext κp κm π)
    (t : Fin (2 * ctx.order) → T4)
    (v : ctx.PostCoordinate → T4)
    (j : Fin (2 * ctx.order)) :
    ctx.splitSurvivingPiMeasurableEquiv.symm (t, v)
        (ctx.headSurvivingCoordinate j) =
      t j := by
  have h :=
    ctx.splitSurvivingPiMeasurableEquiv.apply_symm_apply (t, v)
  exact congrFun (congrArg Prod.fst h) j

@[simp]
theorem splitSurvivingPiMeasurableEquiv_symm_post
    (ctx : R324NestedCrossStepContext κp κm π)
    (t : Fin (2 * ctx.order) → T4)
    (v : ctx.PostCoordinate → T4)
    (i : ctx.PostCoordinate) :
    ctx.splitSurvivingPiMeasurableEquiv.symm (t, v)
        (ctx.postSurvivingCoordinate i) =
      v i := by
  have h :=
    ctx.splitSurvivingPiMeasurableEquiv.apply_symm_apply (t, v)
  exact congrFun (congrArg Prod.snd h) i

/-- Reconstruct an ambient doubled tuple from exactly the current surviving
coordinates.  Coordinates outside the current residual carrier are set to
zero. -/
def reconstruct
    (ctx : R324NestedCrossStepContext κp κm π)
    (v : ctx.SurvivingCoordinate → T4) :
    Fin (2 * m) → T4 :=
  fun i =>
    if hi : i ∈ ctx.residual.activeCarrier then
      v ⟨i, hi⟩
    else 0

@[simp]
theorem reconstruct_surviving
    (ctx : R324NestedCrossStepContext κp κm π)
    (v : ctx.SurvivingCoordinate → T4)
    (i : ctx.SurvivingCoordinate) :
    ctx.reconstruct v i.1 = v i := by
  unfold reconstruct
  rw [dif_pos i.2]
  congr

@[simp]
theorem reconstruct_split_symm_block
    (ctx : R324NestedCrossStepContext κp κm π)
    (t : Fin (2 * ctx.order) → T4)
    (v : ctx.PostCoordinate → T4)
    (j : Fin (2 * ctx.order)) :
    ctx.reconstruct
        (ctx.splitSurvivingPiMeasurableEquiv.symm (t, v))
        (ctx.blockOrderIso j).1 =
      t j := by
  let i := ctx.headSurvivingCoordinate j
  have hi : i.1 = (ctx.blockOrderIso j).1 := rfl
  rw [← hi, ctx.reconstruct_surviving]
  exact ctx.splitSurvivingPiMeasurableEquiv_symm_head t v j

/-- Under the exact Fubini split, the physical (4.20) numerator is
literally the gap between the two canonical standard block indices. -/
theorem centralGapNumerator_reconstruct_split
    (ctx : R324NestedCrossStepContext κp κm π)
    (t : Fin (2 * ctx.order) → T4)
    (v : ctx.PostCoordinate → T4) :
    ctx.head.centralGapNumerator
        (ctx.reconstruct
          (ctx.splitSurvivingPiMeasurableEquiv.symm (t, v))) =
      torusDistSq
        (t ctx.leftGapIndex - t ctx.rightGapIndex) := by
  unfold R324NestedCrossBlock.centralGapNumerator
  have hleft :
      ctx.head.leftGap =
        (ctx.blockOrderIso ctx.leftGapIndex).1 := by
    exact congrArg Subtype.val
      ctx.blockOrderIso_leftGapIndex.symm
  have hright :
      ctx.head.rightGap =
        (ctx.blockOrderIso ctx.rightGapIndex).1 := by
    exact congrArg Subtype.val
      ctx.blockOrderIso_rightGapIndex.symm
  rw [hleft, hright,
    ctx.reconstruct_split_symm_block,
    ctx.reconstruct_split_symm_block]

/-- The exact cross-head coordinate split preserves the paper product Haar
measure. -/
theorem measurePreserving_splitSurvivingPiMeasurableEquiv
    (ctx : R324NestedCrossStepContext κp κm π) :
    MeasurePreserving ctx.splitSurvivingPiMeasurableEquiv
      (Measure.pi fun _ : ctx.SurvivingCoordinate =>
        paperMeasure)
      ((Measure.pi fun _ : Fin (2 * ctx.order) =>
          paperMeasure).prod
        (Measure.pi fun _ : ctx.PostCoordinate =>
          paperMeasure)) := by
  have hcongr :=
    (measurePreserving_piCongrLeft
      (fun _ : ctx.SurvivingCoordinate => paperMeasure)
      ctx.survivingCoordinateEquivHeadSumPost.symm).symm
  have hsum :=
    measurePreserving_sumPiEquivProdPi
      (fun _ : Fin (2 * ctx.order) ⊕
        ctx.PostCoordinate => paperMeasure)
  exact hsum.comp hcongr

/-- Genuine Fubini with the current cross head on the inside and the next
literal suffix on the outside. -/
theorem integral_splitSurviving_post_first
    (ctx : R324NestedCrossStepContext κp κm π)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ctx.SurvivingCoordinate → T4) → E)
    (hf :
      Integrable f
        (Measure.pi fun _ : ctx.SurvivingCoordinate =>
          paperMeasure)) :
    (∫ w : ctx.SurvivingCoordinate → T4, f w
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ v : ctx.PostCoordinate → T4,
        ∫ t : Fin (2 * ctx.order) → T4,
          f (ctx.splitSurvivingPiMeasurableEquiv.symm (t, v))
          ∂Measure.pi fun _ => paperMeasure
        ∂Measure.pi fun _ => paperMeasure := by
  let e := ctx.splitSurvivingPiMeasurableEquiv
  let μ :=
    Measure.pi fun _ : ctx.SurvivingCoordinate => paperMeasure
  let μhead :=
    Measure.pi fun _ : Fin (2 * ctx.order) => paperMeasure
  let μpost :=
    Measure.pi fun _ : ctx.PostCoordinate => paperMeasure
  have hp : MeasurePreserving e μ (μhead.prod μpost) :=
    ctx.measurePreserving_splitSurvivingPiMeasurableEquiv
  have hf' :
      Integrable (fun p => f (e.symm p))
        (μhead.prod μpost) := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    convert hf using 1
    funext w
    simp only [Function.comp_apply, e.symm_apply_apply]
  calc
    (∫ w, f w ∂μ) =
        ∫ p, f (e.symm p) ∂(μhead.prod μpost) := by
      simpa only [Function.comp_apply,
        e.symm_apply_apply] using
        hp.integral_comp' (fun p => f (e.symm p))
    _ =
        ∫ v, ∫ t, f (e.symm (t, v))
          ∂μhead ∂μpost :=
      integral_prod_symm _ hf'
    _ = _ := rfl

/-! ## The exact inserted cross-gap primitive term -/

/-- The moving (4.20) numerator multiplying the genuine primitive
integrand on the canonical standard head coordinates. -/
def crossGapPrimitiveIntegrand
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (x : Fin (2 * ctx.order) → T4) : ℝ :=
  torusDistSq
      (x ctx.leftGapIndex - x ctx.rightGapIndex) *
    primitiveIntegrand ρ ε ctx.order ctx.one_le_order
      G ctx.blockPairing x

/-- One concrete central-gap pairing term, including the exact coupling
power.  The two outermost standard block coordinates are held at `z,w`. -/
def crossGapPrimitiveTerm
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (z w : T4) : ℝ :=
  lamEps lam ε ^ (2 * ctx.order) *
    ∫ v : Fin (2 * ctx.order - 2) → T4,
      ctx.crossGapPrimitiveIntegrand ρ ε G
        (primitiveAssemble
          ctx.order ctx.one_le_order z w v)
      ∂(Measure.pi fun _ => paperMeasure)

theorem crossGapPrimitiveIntegrand_nonneg
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z)
    (x : Fin (2 * ctx.order) → T4) :
    0 ≤ ctx.crossGapPrimitiveIntegrand ρ ε G x := by
  unfold crossGapPrimitiveIntegrand
  exact mul_nonneg (torusDistSq_nonneg _)
    (primitiveIntegrand_nonneg
      ρ ε ctx.order ctx.one_le_order G hG
      ctx.blockPairing x)

/-- The actual moving gap is no larger than the diameter insertion in
Proposition 4.1. -/
theorem crossGapPrimitiveIntegrand_le_inserted
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z)
    (x : Fin (2 * ctx.order) → T4) :
    ctx.crossGapPrimitiveIntegrand ρ ε G x ≤
      primitiveInsertedIntegrand
        ρ ε ctx.order ctx.one_le_order
        G ctx.blockPairing x := by
  have hcard : 0 < 2 * ctx.order := by
    have horder := ctx.one_le_order
    omega
  letI : Nonempty (Fin (2 * ctx.order)) :=
    ⟨⟨0, hcard⟩⟩
  have hgap :
      torusDistSq
          (x ctx.leftGapIndex - x ctx.rightGapIndex) ≤
        ε ^ 2 + torusTupleDiameterSq x :=
    (torusDistSq_sub_le_torusTupleDiameterSq
      x ctx.leftGapIndex ctx.rightGapIndex).trans
      (le_add_of_nonneg_left (sq_nonneg ε))
  unfold crossGapPrimitiveIntegrand
    primitiveInsertedIntegrand
  exact mul_le_mul_of_nonneg_right hgap
    (primitiveIntegrand_nonneg
      ρ ε ctx.order ctx.one_le_order G hG
      ctx.blockPairing x)

/-- Finite tuple diameter is measurable whenever all tuple coordinates are
measurable. -/
theorem measurable_r324TorusTupleDiameterSq
    {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι]
    (x : Ω → ι → T4)
    (hx : ∀ i, Measurable fun ω => x ω i) :
    Measurable fun ω => torusTupleDiameterSq (x ω) := by
  unfold torusTupleDiameterSq
  have hinner (i : ι) :
      Measurable fun ω =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun j => torusDistSq (x ω i - x ω j)) := by
    have h :=
      Finset.measurable_sup' Finset.univ_nonempty
        (f := fun j ω =>
          torusDistSq (x ω i - x ω j))
        (fun j _hj =>
          measurable_torusDistSq.comp
            ((hx i).sub (hx j)))
    convert h using 1
    funext ω
    exact
      (Finset.sup'_apply Finset.univ_nonempty
        (fun j ω =>
          torusDistSq (x ω i - x ω j)) ω).symm
  have h :=
    Finset.measurable_sup' Finset.univ_nonempty
      (f := fun i ω =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun j => torusDistSq (x ω i - x ω j)))
      (fun i _hi => hinner i)
  convert h using 1
  funext ω
  exact
    (Finset.sup'_apply Finset.univ_nonempty
      (fun i ω =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun j => torusDistSq (x ω i - x ω j))) ω).symm

/-- Uniform compact-torus bound for every finite tuple diameter. -/
theorem r324TorusTupleDiameterSq_le_four_pi_sq
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → T4) :
    torusTupleDiameterSq x ≤ 4 * Real.pi ^ 2 := by
  unfold torusTupleDiameterSq
  apply Finset.sup'_le
  intro i _hi
  apply Finset.sup'_le
  intro j _hj
  exact torusDistSq_le (x i - x j)

/-- Absolute integrability of the ordinary canonical head summand follows
from the proved R-51 estimate (with the zero-dimensional order-one case
handled separately). -/
theorem integrable_primitiveIntegrand_blockAssemble
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hinput : IsAdmissiblePrimitiveInput ctx.order G)
    (z w : T4) :
    Integrable
      (fun v : Fin (2 * ctx.order - 2) → T4 =>
        primitiveIntegrand
          ρ ε ctx.order ctx.one_le_order G
          ctx.blockPairing
          (primitiveAssemble
            ctx.order ctx.one_le_order z w v))
      (Measure.pi fun _ => paperMeasure) := by
  apply
    integrable_primitiveIntegrand_assemble_of_scaled_offDiagonal
      ρ hε hε1 ctx.one_le_order G
        (fun _ => 1) hGmeas
        (fun _ => zero_lt_one)
        hinput.1
        (fun j u _hu => by
          simpa only [one_mul] using hinput.2 j u)
        ⟨ctx.blockPairing, ctx.blockPairing_mem⟩ z w

/-- Absolute integrability of the inserted canonical head summand is
derived, rather than assumed: the tuple diameter is a bounded measurable
multiplier of the ordinary R-51 summand. -/
theorem integrable_primitiveInsertedIntegrand_blockAssemble
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hinput : IsAdmissiblePrimitiveInput ctx.order G)
    (z w : T4) :
    Integrable
      (fun v : Fin (2 * ctx.order - 2) → T4 =>
        primitiveInsertedIntegrand
          ρ ε ctx.order ctx.one_le_order G
          ctx.blockPairing
          (primitiveAssemble
            ctx.order ctx.one_le_order z w v))
      (Measure.pi fun _ => paperMeasure) := by
  have hcard : 0 < 2 * ctx.order := by
    have horder := ctx.one_le_order
    omega
  letI : Nonempty (Fin (2 * ctx.order)) :=
    ⟨⟨0, hcard⟩⟩
  let assemble :=
    fun v : Fin (2 * ctx.order - 2) → T4 =>
      primitiveAssemble
        ctx.order ctx.one_le_order z w v
  have hassemble : Measurable assemble :=
    measurable_primitiveAssemble
      ctx.order ctx.one_le_order z w
  have hdiamMeas :
      Measurable fun v =>
        ε ^ 2 + torusTupleDiameterSq (assemble v) :=
    measurable_const.add
      (measurable_r324TorusTupleDiameterSq
        assemble fun i =>
          (measurable_pi_apply i).comp hassemble)
  have hdiamBound :
      ∀ᵐ v ∂(Measure.pi fun _ :
          Fin (2 * ctx.order - 2) => paperMeasure),
        ‖ε ^ 2 + torusTupleDiameterSq (assemble v)‖ ≤
          ε ^ 2 + 4 * Real.pi ^ 2 := by
    filter_upwards with v
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (add_nonneg (sq_nonneg ε)
          (torusTupleDiameterSq_nonneg (assemble v)))]
    exact add_le_add (le_refl _)
      (r324TorusTupleDiameterSq_le_four_pi_sq
        (assemble v))
  have hordinary :=
    ctx.integrable_primitiveIntegrand_blockAssemble
      ρ hε hε1 G hGmeas hinput z w
  have hmul :=
    hordinary.bdd_mul hdiamMeas.aestronglyMeasurable
      hdiamBound
  simpa only [assemble, primitiveInsertedIntegrand] using hmul

/-- Absolute integrability of the exact central-gap summand follows from
the same ordinary R-51 summand and the uniform torus-distance bound. -/
theorem integrable_crossGapPrimitiveIntegrand_blockAssemble
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hinput : IsAdmissiblePrimitiveInput ctx.order G)
    (z w : T4) :
    Integrable
      (fun v : Fin (2 * ctx.order - 2) → T4 =>
        ctx.crossGapPrimitiveIntegrand ρ ε G
          (primitiveAssemble
            ctx.order ctx.one_le_order z w v))
      (Measure.pi fun _ => paperMeasure) := by
  let assemble :=
    fun v : Fin (2 * ctx.order - 2) → T4 =>
      primitiveAssemble
        ctx.order ctx.one_le_order z w v
  have hassemble : Measurable assemble :=
    measurable_primitiveAssemble
      ctx.order ctx.one_le_order z w
  have hgapMeas :
      Measurable fun v =>
        torusDistSq
          (assemble v ctx.leftGapIndex -
            assemble v ctx.rightGapIndex) :=
    measurable_torusDistSq.comp
      (((measurable_pi_apply ctx.leftGapIndex).comp
        hassemble).sub
      ((measurable_pi_apply ctx.rightGapIndex).comp
        hassemble))
  have hgapBound :
      ∀ᵐ v ∂(Measure.pi fun _ :
          Fin (2 * ctx.order - 2) => paperMeasure),
        ‖torusDistSq
          (assemble v ctx.leftGapIndex -
            assemble v ctx.rightGapIndex)‖ ≤
          4 * Real.pi ^ 2 := by
    filter_upwards with v
    rw [Real.norm_eq_abs,
      abs_of_nonneg (torusDistSq_nonneg _)]
    exact torusDistSq_le _
  have hordinary :=
    ctx.integrable_primitiveIntegrand_blockAssemble
      ρ hε hε1 G hGmeas hinput z w
  have hmul :=
    hordinary.bdd_mul hgapMeas.aestronglyMeasurable
      hgapBound
  simpa only [assemble, crossGapPrimitiveIntegrand] using hmul

/-- The exact cross-gap term is nonnegative for the nonnegative dominating
edge family used after Step 2 takes absolute values. -/
theorem crossGapPrimitiveTerm_nonneg
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z)
    (z w : T4) :
    0 ≤ ctx.crossGapPrimitiveTerm ρ lam ε G z w := by
  unfold crossGapPrimitiveTerm
  exact mul_nonneg
    ((even_two_mul ctx.order).pow_nonneg _)
    (integral_nonneg fun v =>
      ctx.crossGapPrimitiveIntegrand_nonneg ρ ε G hG _)

/-- Quantitative one-head comparison: the exact moving-gap term is bounded
by the actual inserted pairing term used by Proposition 4.1. -/
theorem crossGapPrimitiveTerm_le_insertedTerm
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hinput : IsAdmissiblePrimitiveInput ctx.order G)
    (hG : ∀ j z, 0 ≤ G j z)
    (z w : T4) :
    ctx.crossGapPrimitiveTerm ρ lam ε G z w ≤
      primitivePairingKernelInsertedTerm
        ρ lam ε ctx.order ctx.one_le_order
        G ctx.blockPairing z w := by
  unfold crossGapPrimitiveTerm
    primitivePairingKernelInsertedTerm
  apply mul_le_mul_of_nonneg_left
  · exact integral_mono
      (ctx.integrable_crossGapPrimitiveIntegrand_blockAssemble
        ρ hε hε1 G hGmeas hinput z w)
      (ctx.integrable_primitiveInsertedIntegrand_blockAssemble
        ρ hε hε1 G hGmeas hinput z w)
      (fun v =>
        ctx.crossGapPrimitiveIntegrand_le_inserted
          ρ ε G hG
          (primitiveAssemble
            ctx.order ctx.one_le_order z w v))
  · exact (even_two_mul ctx.order).pow_nonneg _

/-! ## Exact heterogeneous scale extraction -/

/-- Scaling every current chain edge extracts exactly the product of the
named scales from the cross-gap integrand. -/
theorem crossGapPrimitiveIntegrand_family_mul
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (A : Fin (2 * ctx.order - 1) → ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (x : Fin (2 * ctx.order) → T4) :
    ctx.crossGapPrimitiveIntegrand ρ ε
        (fun j u => A j * G j u) x =
      (∏ j, A j) *
        ctx.crossGapPrimitiveIntegrand ρ ε G x := by
  unfold crossGapPrimitiveIntegrand
  rw [primitiveIntegrand_family_mul]
  ring

/-- Exact term-level scale ledger for one actual cross head. -/
theorem crossGapPrimitiveTerm_family_mul
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : Fin (2 * ctx.order - 1) → ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (z w : T4) :
    ctx.crossGapPrimitiveTerm ρ lam ε
        (fun j u => A j * G j u) z w =
      (∏ j, A j) *
        ctx.crossGapPrimitiveTerm ρ lam ε G z w := by
  unfold crossGapPrimitiveTerm
  simp_rw [ctx.crossGapPrimitiveIntegrand_family_mul
    ρ ε A G, integral_const_mul]
  ring

/-- The product of nonnegative current edge scales is nonnegative. -/
theorem edgeScaleProduct_nonneg
    (ctx : R324NestedCrossStepContext κp κm π)
    (A : Fin (2 * ctx.order - 1) → ℝ)
    (hA : ∀ j, 0 ≤ A j) :
    0 ≤ ∏ j, A j :=
  Finset.prod_nonneg fun j _hj => hA j

/-! ## Proposition 4.1 on every literal nested cross head -/

/-- The constants from the proved Proposition 4.1 control the exact moving
central-gap term for every literal cross head.  The comparison is proved
through the genuine inserted pairing term; neither the desired R-324
density bound nor a target-shaped reduction interface is assumed. -/
theorem exists_r324NestedCross_headTerm_le_majorant
    (ρ : SmoothCutoff) :
    ∃ orderConstant supportConstant C : ℝ,
      0 < orderConstant ∧
      0 < supportConstant ∧
      0 < C ∧
      ∀ {m : ℕ} (κp κm : PartialPairing (Fin m))
        (π : κp.singles ≃ κm.singles)
        (ctx : R324NestedCrossStepContext κp κm π)
        (lam ε : ℝ)
        (G : Fin (2 * ctx.order - 1) → T4 → ℝ),
        PrimitiveEstimateRegime ctx.order lam ε
            orderConstant supportConstant C →
        (∀ j, Measurable (G j)) →
        IsAdmissiblePrimitiveInput ctx.order G →
        (∀ j z, 0 ≤ G j z) →
        ∀ z : T4,
          0 ≤ ctx.crossGapPrimitiveTerm
              ρ lam ε G z 0 ∧
          ctx.crossGapPrimitiveTerm
              ρ lam ε G z 0 ≤
            primitiveInsertedMajorant
              C lam ε supportConstant ctx.order z := by
  obtain ⟨orderConstant, supportConstant, C,
      horder, hsupport, hC, hbound⟩ :=
    exists_momentResidualCollapseBlock_term_bounds ρ
  refine
    ⟨orderConstant, supportConstant, C,
      horder, hsupport, hC, ?_⟩
  intro m κp κm π ctx lam ε G
    hreg hGmeas hinput hG z
  have htermNonneg :=
    ctx.crossGapPrimitiveTerm_nonneg
      ρ lam ε G hG z 0
  have htermLe :=
    ctx.crossGapPrimitiveTerm_le_insertedTerm
      ρ lam hreg.2.1 hreg.2.2.1
      G hGmeas hinput hG z 0
  have hpairBound :=
    (hbound κp κm π
      ctx.head.carrier ctx.collapseMem
      lam ε G hreg hinput hG z).2
  refine ⟨htermNonneg, htermLe.trans ?_⟩
  exact (le_abs_self _).trans hpairBound

/-- Heterogeneous nonnegative edge scales are charged exactly once, as
their product, in the quantitative one-head update. -/
theorem exists_r324NestedCross_scaledHeadTerm_le_majorant
    (ρ : SmoothCutoff) :
    ∃ orderConstant supportConstant C : ℝ,
      0 < orderConstant ∧
      0 < supportConstant ∧
      0 < C ∧
      ∀ {m : ℕ} (κp κm : PartialPairing (Fin m))
        (π : κp.singles ≃ κm.singles)
        (ctx : R324NestedCrossStepContext κp κm π)
        (lam ε : ℝ)
        (A : Fin (2 * ctx.order - 1) → ℝ)
        (G : Fin (2 * ctx.order - 1) → T4 → ℝ),
        PrimitiveEstimateRegime ctx.order lam ε
            orderConstant supportConstant C →
        (∀ j, 0 ≤ A j) →
        (∀ j, Measurable (G j)) →
        IsAdmissiblePrimitiveInput ctx.order G →
        (∀ j z, 0 ≤ G j z) →
        ∀ z : T4,
          ctx.crossGapPrimitiveTerm ρ lam ε
              (fun j u => A j * G j u) z 0 ≤
            (∏ j, A j) *
              primitiveInsertedMajorant
                C lam ε supportConstant ctx.order z := by
  obtain ⟨orderConstant, supportConstant, C,
      horder, hsupport, hC, hhead⟩ :=
    exists_r324NestedCross_headTerm_le_majorant ρ
  refine
    ⟨orderConstant, supportConstant, C,
      horder, hsupport, hC, ?_⟩
  intro m κp κm π ctx lam ε A G
    hreg hA hGmeas hinput hG z
  rw [ctx.crossGapPrimitiveTerm_family_mul
    ρ lam ε A G z 0]
  exact mul_le_mul_of_nonneg_left
    (hhead κp κm π ctx lam ε G
      hreg hGmeas hinput hG z).2
    (ctx.edgeScaleProduct_nonneg A hA)

/-! ## Prefix and suffix budget recurrences -/

theorem next_processedOrder
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.next.processedOrder =
      ctx.residual.processedOrder + ctx.order := by
  unfold next
    R324NestedCrossResidualPrefix.processedOrder
    order
  simp [R324NestedCrossResidualPrefix.afterHead]

theorem next_processed_length
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.next.processed.length =
      ctx.residual.processed.length + 1 := by
  unfold next R324NestedCrossResidualPrefix.afterHead
  simp

theorem remainingOrder_eq_order_add_next
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.residual.remainingOrder =
      ctx.order + ctx.next.remainingOrder := by
  exact
    ctx.residual.remainingOrder_head
      ctx.head ctx.tail ctx.remaining_eq

theorem remaining_eq_head_cons
    (ctx : R324NestedCrossStepContext κp κm π) :
    ctx.residual.remaining =
      ctx.head :: ctx.next.remaining := by
  simpa only [next,
    R324NestedCrossResidualPrefix.afterHead_remaining] using
    ctx.remaining_eq

/-- Numerical budget accumulated by the already processed cross prefix.
`K` is the uniform integration cost of one completed cross head. -/
def processedBudget
    (res : R324NestedCrossResidualPrefix κp κm π)
    (C lam K : ℝ) : ℝ :=
  (C * lam) ^ (2 * res.processedOrder) *
    K ^ res.processed.length

/-- Numerical budget still carried by the literal remaining suffix. -/
def remainingBudget
    (res : R324NestedCrossResidualPrefix κp κm π)
    (C lam K : ℝ) : ℝ :=
  (C * lam) ^ (2 * res.remainingOrder) *
    K ^ res.remaining.length

/-- Exact forward update of the accumulated budget after deleting one
literal head. -/
theorem processedBudget_next
    (ctx : R324NestedCrossStepContext κp κm π)
    (C lam K : ℝ) :
    processedBudget ctx.next C lam K =
      processedBudget ctx.residual C lam K *
        ((C * lam) ^ (2 * ctx.order) * K) := by
  unfold processedBudget
  rw [ctx.next_processedOrder,
    ctx.next_processed_length]
  rw [show
      2 * (ctx.residual.processedOrder + ctx.order) =
        2 * ctx.residual.processedOrder +
          2 * ctx.order by omega,
    pow_add, pow_succ]
  ring

/-- Exact backward factorization of the budget carried by a nonempty
remaining suffix. -/
theorem remainingBudget_eq_head_mul_next
    (ctx : R324NestedCrossStepContext κp κm π)
    (C lam K : ℝ) :
    remainingBudget ctx.residual C lam K =
      ((C * lam) ^ (2 * ctx.order) * K) *
        remainingBudget ctx.next C lam K := by
  unfold remainingBudget
  rw [ctx.remainingOrder_eq_order_add_next,
    ctx.remaining_eq_head_cons]
  simp only [List.length_cons, pow_succ]
  rw [show
      2 * (ctx.order + ctx.next.remainingOrder) =
        2 * ctx.order +
          2 * ctx.next.remainingOrder by omega,
    pow_add]
  ring

end R324NestedCrossStepContext

end

end Anderson4D
