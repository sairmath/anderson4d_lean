import Anderson4D.Continuum.PrimitiveR51Assembly
import Anderson4D.DetParametrix.Paper42_Moment.R324ConcretePhaseATraceAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324FourierIntegrability

/-!
# Root integrability for the initial two-half R-324 density

The certified within-half iteration starts from the literal all-Green
residual prefixes.  This file establishes the root input: joint
integrability of the genuine marked physical density on the full
five-group product space.  Any later passage to endpoint sections must use
Fubini and therefore be stated almost everywhere; fixed-endpoint Green
sections need not be integrable on exceptional diagonals.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

/-! ## The initial sparse carrier and the standard internal carrier -/

/-- Before any within-half block is removed, the sparse carrier is exactly
the ordinary internal index type. -/
def initialEquivSurviving
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m)) :
    Fin m ≃
      (initial ρ lam ε pairing).SurvivingCoordinate where
  toFun i :=
    ⟨i, by
      simp [initial, R324WithinHalfEdgeState.active,
        r324InitialWithinHalfEdgeState]⟩
  invFun i := i.1
  left_inv _ := rfl
  right_inv i := by
    apply Subtype.ext
    rfl

/-- Measurable reindex from the initial sparse tuple to the standard
`Fin m` tuple. -/
def initialPiMeasurableEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m)) :
    ((initial ρ lam ε pairing).SurvivingCoordinate → T4) ≃ᵐ
      (Fin m → T4) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ :
      (initial ρ lam ε pairing).SurvivingCoordinate =>
        T4)
    (initialEquivSurviving ρ lam ε pairing)).symm

/-- The initial carrier reindex preserves product Haar measure. -/
theorem measurePreserving_initialPiMeasurableEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m)) :
    MeasurePreserving
      (initialPiMeasurableEquiv ρ lam ε pairing)
      (Measure.pi fun _ :
        (initial ρ lam ε pairing).SurvivingCoordinate =>
          paperMeasure)
      (Measure.pi fun _ : Fin m => paperMeasure) := by
  simpa only [initialPiMeasurableEquiv] using
    (measurePreserving_piCongrLeft
      (fun _ :
        (initial ρ lam ε pairing).SurvivingCoordinate =>
          paperMeasure)
      (initialEquivSurviving ρ lam ε pairing)).symm

@[simp]
theorem initialPiMeasurableEquiv_apply
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (v :
      (initial ρ lam ε pairing).SurvivingCoordinate → T4)
    (i : Fin m) :
    initialPiMeasurableEquiv ρ lam ε pairing v i =
      v (initialEquivSurviving ρ lam ε pairing i) :=
  rfl

/-- The sparse reconstruction is literally the standard tuple at the
all-active initial state. -/
theorem initial_reconstruct_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (v :
      (initial ρ lam ε pairing).SurvivingCoordinate → T4) :
    (initial ρ lam ε pairing).reconstruct v =
      initialPiMeasurableEquiv ρ lam ε pairing v := by
  funext i
  rw [initialPiMeasurableEquiv_apply]
  exact
    (initial ρ lam ε pairing).reconstruct_surviving
      v (initialEquivSurviving ρ lam ε pairing i)

/-! ## Pointwise form of the initial within-half residual -/

/-- Every production edge is active in the all-Green initial state. -/
theorem initial_activeEdgeSlots
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m)) :
    (initial ρ lam ε pairing).activeEdgeSlots =
      Finset.univ := by
  ext edge
  simp only [Finset.mem_univ, iff_true]
  by_cases hzero : edge.val = 0
  · have hedge : edge = 0 := Fin.ext hzero
    rw [hedge]
    exact (initial ρ lam ε pairing).zero_mem_activeEdgeSlots
  · let i : Fin m :=
      ⟨edge.val - 1, by
        have hedge := edge.isLt
        omega⟩
    have hi :
        i ∈
          (initial ρ lam ε pairing).state.active := by
      simp [initial, R324WithinHalfEdgeState.active,
        r324InitialWithinHalfEdgeState]
    have hslot :
        r324InternalVertexEdgeSlot i = edge := by
      apply Fin.ext
      change edge.val - 1 + 1 = edge.val
      omega
    rw [← hslot]
    exact
      (initial ρ lam ε pairing)
        |>.internalVertexEdgeSlot_mem_activeEdgeSlots i hi

/-- At the all-active initial state, every production edge has its ordinary
adjacent successor. -/
theorem initial_edgeSuccessor
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (edge : Fin (m + 1)) :
    (initial ρ lam ε pairing).edgeSuccessor edge =
      edge.succ := by
  let res := initial ρ lam ε pairing
  unfold edgeSuccessor
  rw [Finset.min'_eq_iff]
  constructor
  · rw [edgeSuccessorCandidates]
    by_cases hlast : edge.val = m
    · apply Finset.mem_union_left
      have hedge :
          edge.succ = Fin.last (m + 1) := by
        apply Fin.ext
        change edge.val + 1 = m + 1
        omega
      simpa only [hedge] using
        (Finset.mem_singleton_self (Fin.last (m + 1)))
    · let i : Fin m := ⟨edge.val, by omega⟩
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · simp [initial, R324WithinHalfEdgeState.active,
          r324InitialWithinHalfEdgeState]
      · change edge.val < edge.val + 1
        omega
      · apply Fin.ext
        rfl
  · intro candidate hcandidate
    rw [edgeSuccessorCandidates] at hcandidate
    rcases Finset.mem_union.mp hcandidate with hlast | hinter
    · have hc :
          candidate = Fin.last (m + 1) := by
        simpa using hlast
      rw [hc]
      exact Fin.le_last _
    · obtain ⟨i, hi, rfl⟩ :=
        Finset.mem_image.mp hinter
      have hlt := (Finset.mem_filter.mp hi).2
      change edge.val < i.val + 1 at hlt
      change edge.val + 1 ≤ i.val + 1
      omega

/-- The initial reserved outgoing slots are precisely the extraction right
edges, independently of the analytic reordering. -/
theorem initial_mem_remainingOutgoingSlots_iff
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (edge : Fin (m + 1)) :
    edge ∈
        (initial ρ lam ε pairing).remainingOutgoingSlots ↔
      edge ∈ extractedRightEdges pairing := by
  have hp :=
    (r322AnalyticSchedule_endpoints_perm_extract pairing).map
      extractedRightEdge
  have hp' :
      List.Perm
        ((r322AnalyticSchedule pairing).map
          (fun step =>
            r324InternalVertexEdgeSlot step.1.2))
        ((extract pairing).map extractedRightEdge) := by
    have heq :
        (r322AnalyticSchedule pairing).map
            (fun step =>
              r324InternalVertexEdgeSlot step.1.2) =
          (r322AnalyticSchedule pairing).map
            (fun step => extractedRightEdge step.1) := by
      apply List.map_congr_left
      intro step _hstep
      apply Fin.ext
      rfl
    rw [heq]
    simpa only [List.map_map, Function.comp_def] using hp
  unfold remainingOutgoingSlots initial extractedRightEdges
  rw [List.mem_toFinset]
  exact hp'.mem_iff

/-- One initial sparse chain factor is the corresponding ordinary Green
edge unless that edge is reserved for an extracted difference. -/
theorem initial_residualChainEdgeFactor_complex_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (x y : T4) (v : Fin m → T4)
    (edge : Fin (m + 1)) :
    (((initial ρ lam ε pairing).residualChainEdgeFactor
        x y v edge : ℝ) : ℂ) =
      if edge ∈ extractedRightEdges pairing then
        1
      else
        originalGreenEdge (assemble x y v) edge := by
  have hactive :
      edge ∈
        (initial ρ lam ε pairing).activeEdgeSlots := by
    rw [initial_activeEdgeSlots]
    exact Finset.mem_univ edge
  unfold residualChainEdgeFactor
  rw [if_pos hactive]
  by_cases hreserved :
      edge ∈
        (initial ρ lam ε pairing).remainingOutgoingSlots
  · have hextracted :
        edge ∈ extractedRightEdges pairing :=
      (initial_mem_remainingOutgoingSlots_iff
        ρ lam ε pairing edge).mp hreserved
    simp only [hreserved, hextracted, if_true]
    norm_num
  · have hextracted :
        edge ∉ extractedRightEdges pairing :=
      fun h =>
        hreserved
          ((initial_mem_remainingOutgoingSlots_iff
            ρ lam ε pairing edge).mpr h)
    simp only [hreserved, hextracted, if_false]
    unfold R324WithinHalfResidualPrefix.edgeDisplacement
      originalGreenEdge
    rw [initial_edgeSuccessor ρ lam ε pairing edge]
    rfl

/-- The complete initial sparse chain is the ordinary chain part of the
renormalized Green skeleton. -/
theorem initial_residualChainProduct_complex_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (x y : T4) (v : Fin m → T4) :
    (((initial ρ lam ε pairing).residualChainProduct
        x y v : ℝ) : ℂ) =
      ∏ edge : Fin (m + 1),
        if edge ∈ extractedRightEdges pairing then
          1
        else
          originalGreenEdge (assemble x y v) edge := by
  unfold residualChainProduct
  push_cast
  apply Finset.prod_congr rfl
  intro edge _hedge
  exact
    initial_residualChainEdgeFactor_complex_eq
      ρ lam ε pairing x y v edge

/-- One initial residual difference is the literal extracted Green
difference attached to its endpoint pair. -/
theorem initial_residualStepDifference_complex_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (x y : T4) (v : Fin m → T4)
    (step : R322ExtractionStep m) :
    (((initial ρ lam ε pairing).residualStepDifference
        x y v step : ℝ) : ℂ) =
      originalGreenEdge (assemble x y v)
          (extractedRightEdge step.1) -
        (greenFn
          (assemble x y v (varIdx step.1.1) -
            assemble x y v
              (extractedRightEdge step.1).succ) : ℂ) := by
  unfold residualStepDifference
  change
    ((((initial ρ lam ε pairing).state.edges
        (r324InternalVertexEdgeSlot step.1.2)
        (assemble x y v (varIdx step.1.2) -
          assemble x y v
            ((initial ρ lam ε pairing).edgeSuccessor
              (r324InternalVertexEdgeSlot step.1.2))) -
      (initial ρ lam ε pairing).state.edges
        (r324InternalVertexEdgeSlot step.1.2)
        (assemble x y v (varIdx step.1.1) -
          assemble x y v
            ((initial ρ lam ε pairing).edgeSuccessor
              (r324InternalVertexEdgeSlot step.1.2))) : ℝ) : ℂ)) =
      _
  rw [initial_edgeSuccessor ρ lam ε pairing
    (r324InternalVertexEdgeSlot step.1.2)]
  change
    (((greenFn
        (assemble x y v (varIdx step.1.2) -
          assemble x y v
            (r324InternalVertexEdgeSlot step.1.2).succ) -
      greenFn
        (assemble x y v (varIdx step.1.1) -
          assemble x y v
            (r324InternalVertexEdgeSlot step.1.2).succ) : ℝ) : ℂ)) =
      _
  unfold originalGreenEdge
  rw [extractedRightEdge_castSucc]
  push_cast
  rfl

/-- The complete initial residual-difference product is the extraction-list
factor in the renormalized Green skeleton. -/
theorem initial_residualDifferenceProduct_complex_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (x y : T4) (v : Fin m → T4) :
    (((initial ρ lam ε pairing).residualDifferenceProduct
        x y v : ℝ) : ℂ) =
      ((extract pairing).map fun p =>
        originalGreenEdge (assemble x y v)
            (extractedRightEdge p) -
          (greenFn
            (assemble x y v (varIdx p.1) -
              assemble x y v
                (extractedRightEdge p).succ) : ℂ)).prod := by
  let f : (Fin m × Fin m) → ℂ :=
    fun p =>
      originalGreenEdge (assemble x y v)
          (extractedRightEdge p) -
        (greenFn
          (assemble x y v (varIdx p.1) -
            assemble x y v
              (extractedRightEdge p).succ) : ℂ)
  unfold residualDifferenceProduct
  calc
    (((initial ρ lam ε pairing).remaining.map
        ((initial ρ lam ε pairing).residualStepDifference
          x y v)).prod : ℝ) =
        ((initial ρ lam ε pairing).remaining.map
        (fun step =>
          (((initial ρ lam ε pairing).residualStepDifference
            x y v step : ℝ) : ℂ))).prod := by
      change
        Complex.ofRealHom
            (((initial ρ lam ε pairing).remaining.map
              ((initial ρ lam ε pairing).residualStepDifference
                x y v)).prod) =
          _
      rw [map_list_prod, List.map_map]
      rfl
    _ =
        ((r322AnalyticSchedule pairing).map
          (fun step => f step.1)).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro step _hstep
      exact
        initial_residualStepDifference_complex_eq
          ρ lam ε pairing x y v step
    _ = ((extract pairing).map f).prod := by
      simpa only [List.map_map, Function.comp_def] using
        ((r322AnalyticSchedule_endpoints_perm_extract pairing).map f).prod_eq

/-- At the initial state, the remaining-block coordinate is the canonical
analytic-schedule block coordinate. -/
theorem initial_remainingBlockIndex_eq_analyticBlockEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (j : Fin (r322AnalyticSchedule pairing).length) :
    (initial ρ lam ε pairing).remainingBlockIndex j =
      r322AnalyticBlockEquiv pairing j := by
  apply Subtype.ext
  change
    ((r322AnalyticSchedule pairing).get j).2 =
      (r322AnalyticBlockEquiv pairing j).1
  exact (r322AnalyticBlockEquiv_apply_val pairing j).symm

/-- The initial primitive product contains every extraction block exactly
once. -/
theorem initial_residualPrimitiveProduct_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (v : Fin m → T4) :
    (initial ρ lam ε pairing).residualPrimitiveProduct
        ρ ε v =
      ∏ B : ExtractionBlockIndex pairing,
        r322ExtractionBlockPrimitiveSum ρ ε pairing B v := by
  unfold residualPrimitiveProduct
  rw [extractionBlock_prod_eq_analyticSchedule]
  apply Finset.prod_congr rfl
  intro j _hj
  rw [initial_remainingBlockIndex_eq_analyticBlockEquiv]

/-- Exact pointwise form of the genuine initial within-half residual:
renormalized Green skeleton times all complete primitive block sums. -/
theorem initial_residualIntegrand_complex_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (x y : T4) (v : Fin m → T4) :
    (((initial ρ lam ε pairing).residualIntegrand
        ρ ε x y v : ℝ) : ℂ) =
      renormalizedGreenSkeleton pairing (assemble x y v) *
        ((∏ B : ExtractionBlockIndex pairing,
          r322ExtractionBlockPrimitiveSum
            ρ ε pairing B v : ℝ) : ℂ) := by
  have hprimitiveCast :
      (((∏ B : ExtractionBlockIndex pairing,
        r322ExtractionBlockPrimitiveSum
          ρ ε pairing B v : ℝ) : ℂ)) =
        ∏ B : ExtractionBlockIndex pairing,
          (r322ExtractionBlockPrimitiveSum
            ρ ε pairing B v : ℂ) := by
    change
      Complex.ofRealHom
          (∏ B : ExtractionBlockIndex pairing,
            r322ExtractionBlockPrimitiveSum
              ρ ε pairing B v) =
        _
    rw [map_prod]
    rfl
  unfold residualIntegrand renormalizedGreenSkeleton
  push_cast
  rw [
    initial_residualChainProduct_complex_eq,
    initial_residualDifferenceProduct_complex_eq,
    initial_residualPrimitiveProduct_eq]
  rw [hprimitiveCast]

end R324WithinHalfResidualPrefix

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## Bounded covariance factors -/

/-- One complete primitive block sum is measurable in the ambient
within-half tuple. -/
theorem measurable_r322ExtractionBlockPrimitiveSum
    (ε : ℝ) {m : ℕ}
    (pairing : PartialPairing (Fin m))
    (B : ExtractionBlockIndex pairing) :
    Measurable
      (r322ExtractionBlockPrimitiveSum
        ρ ε pairing B) := by
  unfold r322ExtractionBlockPrimitiveSum
  apply Finset.measurable_sum
  intro σ _hσ
  unfold extractionBlockPrimitiveCovarianceFactor
  exact
    (measurable_primitiveCovarianceProduct ρ ε
      (residualBlockOrder B.1) σ.1).comp
      (measurable_pi_lambda _ fun i =>
        measurable_pi_apply
          ((residualPrimitiveBlockOrderIso pairing B.1
            (extractionBlock_isFullyPairedOn_of_mem
              pairing B.1 B.2) i).1))

/-- At positive scale, one complete primitive block sum has a uniform
pointwise norm bound. -/
theorem exists_norm_r322ExtractionBlockPrimitiveSum_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (pairing : PartialPairing (Fin m))
    (B : ExtractionBlockIndex pairing) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ v : Fin m → T4,
        ‖r322ExtractionBlockPrimitiveSum
          ρ ε pairing B v‖ ≤ bound := by
  obtain ⟨Cη, hCη, hcovariance⟩ :=
    exists_primitiveCovarianceProduct_uniform_bound ρ
  let n := residualBlockOrder B.1
  let A : ℝ := (ε⁻¹ ^ (dim : ℕ) * Cη) ^ n
  let bound : ℝ :=
    ((primitiveFullPairings n).card : ℝ) * A
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  refine
    ⟨bound,
      mul_nonneg (Nat.cast_nonneg _) hA,
      ?_⟩
  intro v
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (Finset.sum_nonneg fun σ _ =>
        primitiveCovarianceProduct_nonneg
          ρ ε n σ.1
          (fun i =>
            v ((residualPrimitiveBlockOrderIso
              pairing B.1
              (extractionBlock_isFullyPairedOn_of_mem
                pairing B.1 B.2) i).1)))]
  calc
    r322ExtractionBlockPrimitiveSum
        ρ ε pairing B v ≤
        ∑ _σ :
            {τ : PartialPairing (Fin (2 * n)) //
              τ ∈ primitiveFullPairings n},
          A := by
      unfold r322ExtractionBlockPrimitiveSum
        extractionBlockPrimitiveCovarianceFactor
      apply Finset.sum_le_sum
      intro σ _hσ
      exact
        hcovariance n σ.1
          (mem_primitiveFullPairings.mp σ.2).1
          hε hε1 _
    _ = bound := by
      simp [bound]

/-- The product of all complete primitive block sums is measurable. -/
theorem measurable_r324InitialPrimitiveBlockProduct
    (ε : ℝ) {m : ℕ}
    (pairing : PartialPairing (Fin m)) :
    Measurable fun v : Fin m → T4 =>
      ∏ B : ExtractionBlockIndex pairing,
        r322ExtractionBlockPrimitiveSum
          ρ ε pairing B v := by
  apply Finset.measurable_prod
  intro B _hB
  exact
    ρ.measurable_r322ExtractionBlockPrimitiveSum
      ε pairing B

/-- The finite product of all complete primitive block sums has a uniform
pointwise norm bound. -/
theorem exists_norm_r324InitialPrimitiveBlockProduct_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (pairing : PartialPairing (Fin m)) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ v : Fin m → T4,
        ‖∏ B : ExtractionBlockIndex pairing,
          r322ExtractionBlockPrimitiveSum
            ρ ε pairing B v‖ ≤ bound := by
  choose blockBound hblockBoundNonneg hblockBound using
    fun B : ExtractionBlockIndex pairing =>
      ρ.exists_norm_r322ExtractionBlockPrimitiveSum_le
        hε hε1 pairing B
  let bound : ℝ :=
    ∏ B : ExtractionBlockIndex pairing, blockBound B
  refine
    ⟨bound,
      Finset.prod_nonneg fun B _ => hblockBoundNonneg B,
      ?_⟩
  intro v
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact
    Finset.prod_le_prod
      (fun B _ => abs_nonneg _)
      (fun B _ => by
        simpa only [Real.norm_eq_abs] using
          hblockBound B v)

/-- The projected covariance series is measurable in its spatial
displacement. -/
theorem measurable_r324ProjectedCovarianceC
    (ε L : ℝ) :
    Measurable (ρ.r324ProjectedCovarianceC ε L) := by
  unfold r324ProjectedCovarianceC
  apply Measurable.tsum
  intro k
  by_cases hk : k ∈ r324HighModeSet ε L
  · simp only [r324HighCovarianceModeTerm,
      Set.indicator_of_mem hk, r324CovarianceModeTerm]
    exact
      measurable_const.mul
        (continuous_charT4 k).measurable
  · simp [r324HighCovarianceModeTerm, hk]

/-- Absolute covariance-coefficient mass at one fixed mollification
scale. -/
def r324CovarianceNormBudget (ε : ℝ) : ℝ :=
  ∑' k : Z4, ‖ρ.covarianceModeCoeff ε k‖

theorem r324CovarianceNormBudget_nonneg
    (ε : ℝ) :
    0 ≤ ρ.r324CovarianceNormBudget ε :=
  tsum_nonneg fun _ => norm_nonneg _

/-- The high-mode projection is bounded by the full absolutely summable
covariance Fourier mass. -/
theorem norm_r324ProjectedCovarianceC_le_budget
    {ε : ℝ} (hε : 0 < ε) (L : ℝ) (z : T4) :
    ‖ρ.r324ProjectedCovarianceC ε L z‖ ≤
      ρ.r324CovarianceNormBudget ε := by
  have hhigh :=
    ρ.summable_r324HighCovarianceModeTerm hε L z
  unfold r324ProjectedCovarianceC
    r324CovarianceNormBudget
  calc
    ‖∑' k : Z4,
        ρ.r324HighCovarianceModeTerm ε L z k‖ ≤
        ∑' k : Z4,
          ‖ρ.r324HighCovarianceModeTerm ε L z k‖ :=
      norm_tsum_le_tsum_norm hhigh.norm
    _ ≤ ∑' k : Z4,
        ‖ρ.covarianceModeCoeff ε k‖ :=
      hhigh.norm.tsum_le_tsum
        (fun k => by
          by_cases hk : k ∈ r324HighModeSet ε L
          · simp [r324HighCovarianceModeTerm, hk,
              ρ.norm_r324CovarianceModeTerm]
          · simp [r324HighCovarianceModeTerm, hk])
        (ρ.summable_norm_covarianceModeCoeff hε)

/-- A marked covariance product on a fixed active carrier is measurable. -/
theorem measurable_r324MarkedPairingCovarianceProductOn
    (ε L : ℝ) {n : ℕ}
    (pairing : PartialPairing (Fin n))
    (marked : Fin n) (B : Finset (Fin n)) :
    Measurable
      (ρ.r324MarkedPairingCovarianceProductOn
        ε L pairing marked B) := by
  unfold r324MarkedPairingCovarianceProductOn
  apply Finset.measurable_prod
  intro i _hi
  by_cases himarked : i = marked
  · subst i
    simp only [↓reduceIte]
    exact
      (ρ.measurable_r324ProjectedCovarianceC ε L).comp
        ((measurable_pi_apply marked).sub
          (measurable_pi_apply (pairing marked)))
  · simp only [himarked, ↓reduceIte]
    exact
      (ρ.measurable_etaEpsT4 ε).complex_ofReal.comp
        ((measurable_pi_apply i).sub
          (measurable_pi_apply (pairing i)))

/-- At positive scale, a fixed marked covariance product is uniformly
bounded.  The estimate is intentionally coarse; only integrability is used
at this stage. -/
theorem exists_norm_r324MarkedPairingCovarianceProductOn_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (L : ℝ) {n : ℕ}
    (pairing : PartialPairing (Fin n))
    (marked : Fin n) (B : Finset (Fin n)) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ v : Fin n → T4,
        ‖ρ.r324MarkedPairingCovarianceProductOn
          ε L pairing marked B v‖ ≤ bound := by
  obtain ⟨Cη, hCη, heta⟩ :=
    ρ.exists_pos_etaEpsT4_uniform_bound
  let A : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη
  let P : ℝ := ρ.r324CovarianceNormBudget ε
  let D : ℝ := 1 + A + P
  let bound : ℝ := D ^ n
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hP : 0 ≤ P :=
    ρ.r324CovarianceNormBudget_nonneg ε
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith
  refine
    ⟨bound, pow_nonneg (zero_le_one.trans hD) _, ?_⟩
  intro v
  unfold r324MarkedPairingCovarianceProductOn
  rw [norm_prod]
  calc
    (∏ i ∈ B.filter (fun i => i < pairing i),
      ‖if i = marked then
          ρ.r324ProjectedCovarianceC ε L
            (v i - v (pairing i))
        else
          (ρ.etaEpsT4 ε
            (v i - v (pairing i)) : ℂ)‖) ≤
        ∏ _i ∈ B.filter (fun i => i < pairing i), D := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact norm_nonneg _
      · intro i _hi
        by_cases himarked : i = marked
        · simp only [himarked, ↓reduceIte]
          exact
            (ρ.norm_r324ProjectedCovarianceC_le_budget
              hε L _).trans (by
                dsimp only [D, P]
                linarith)
        · simp only [himarked, ↓reduceIte,
            Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg
              (ρ.etaEpsT4_nonneg ε
                (v i - v (pairing i)))]
          exact
            (heta hε hε1
              (v i - v (pairing i))).trans (by
                dsimp only [D, A]
                linarith)
    _ = D ^ (B.filter
        (fun i => i < pairing i)).card := by
      simp
    _ ≤ D ^ n := by
      apply pow_le_pow_right₀ hD
      exact
        (by
          simpa using
            (Finset.card_le_univ
              (B.filter fun i => i < pairing i)))
    _ = bound := rfl

/-! ## The genuine marked root density -/

/-- The uncollapsed two-half physical density at the literal all-Green
within-half roots, with exactly the selected residual cross covariance
Fourier-projected. -/
def r324InitialTwoHalfMarkedPhysicalCore
    (lam ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  ((R324WithinHalfResidualPrefix.initial
      ρ lam ε κp).residualIntegrand
        ρ ε x y (fun i => v (leftMomentIndex i)) : ℝ) *
    (((R324WithinHalfResidualPrefix.initial
      ρ lam ε κm).residualIntegrand
        ρ ε z w (fun i => v (rightMomentIndex i)) : ℝ) *
      ρ.r324MarkedPairingCovarianceProductOn
        ε L (momentCombinedPairing κp κm π)
        (r324ResidualMarkedLowerEndpoint selected)
        (momentResidualActive κp κm) v)

/-- The genuine marked initial root density is jointly integrable on the
full five-group physical space. -/
theorem integrable_r324Flatten_initialTwoHalfMarkedPhysicalCore
    {lam ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) :
    Integrable
      (r324Flatten
        (ρ.r324InitialTwoHalfMarkedPhysicalCore
          lam ε κp κm π selected L))
      (r324PhysicalMeasure m) := by
  have hbare :=
    integrable_r324Flatten_renormalizedGreenSkeleton_product
      κp κm
  obtain ⟨Bp, hBp, hpBound⟩ :=
    ρ.exists_norm_r324InitialPrimitiveBlockProduct_le
      hε hε1 κp
  obtain ⟨Bm, hBm, hmBound⟩ :=
    ρ.exists_norm_r324InitialPrimitiveBlockProduct_le
      hε hε1 κm
  obtain ⟨Bc, hBc, hcrossBound⟩ :=
    ρ.exists_norm_r324MarkedPairingCovarianceProductOn_le
      hε hε1 L (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (momentResidualActive κp κm)
  let weight : R324PhysicalPoint m → ℂ :=
    fun p =>
      ((∏ B : ExtractionBlockIndex κp,
        r322ExtractionBlockPrimitiveSum ρ ε κp B
          (fun i => p.2.2.2.2 (leftMomentIndex i)) : ℝ) : ℂ) *
      (((∏ B : ExtractionBlockIndex κm,
        r322ExtractionBlockPrimitiveSum ρ ε κm B
          (fun i => p.2.2.2.2 (rightMomentIndex i)) : ℝ) : ℂ) *
        ρ.r324MarkedPairingCovarianceProductOn
          ε L (momentCombinedPairing κp κm π)
          (r324ResidualMarkedLowerEndpoint selected)
          (momentResidualActive κp κm) p.2.2.2.2)
  have hv :
      Measurable fun p : R324PhysicalPoint m =>
        p.2.2.2.2 :=
    measurable_snd.comp
      (measurable_snd.comp
        (measurable_snd.comp measurable_snd))
  have hleftMeas :
      Measurable fun p : R324PhysicalPoint m =>
        ∏ B : ExtractionBlockIndex κp,
          r322ExtractionBlockPrimitiveSum ρ ε κp B
            (fun i => p.2.2.2.2 (leftMomentIndex i)) :=
    (ρ.measurable_r324InitialPrimitiveBlockProduct
      ε κp).comp
        (measurable_pi_lambda _ fun i =>
          (measurable_pi_apply
            (leftMomentIndex i)).comp hv)
  have hrightMeas :
      Measurable fun p : R324PhysicalPoint m =>
        ∏ B : ExtractionBlockIndex κm,
          r322ExtractionBlockPrimitiveSum ρ ε κm B
            (fun i => p.2.2.2.2 (rightMomentIndex i)) :=
    (ρ.measurable_r324InitialPrimitiveBlockProduct
      ε κm).comp
        (measurable_pi_lambda _ fun i =>
          (measurable_pi_apply
            (rightMomentIndex i)).comp hv)
  have hcrossMeas :
      Measurable fun p : R324PhysicalPoint m =>
        ρ.r324MarkedPairingCovarianceProductOn
          ε L (momentCombinedPairing κp κm π)
          (r324ResidualMarkedLowerEndpoint selected)
          (momentResidualActive κp κm) p.2.2.2.2 :=
    (ρ.measurable_r324MarkedPairingCovarianceProductOn
      ε L (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (momentResidualActive κp κm)).comp hv
  have hweightMeas : Measurable weight := by
    exact
      hleftMeas.complex_ofReal.mul
        (hrightMeas.complex_ofReal.mul hcrossMeas)
  have hweightBound :
      ∀ p : R324PhysicalPoint m,
        ‖weight p‖ ≤ Bp * (Bm * Bc) := by
    intro p
    dsimp only [weight]
    rw [norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real]
    have hp :=
      hpBound
        (fun i => p.2.2.2.2 (leftMomentIndex i))
    have hm :=
      hmBound
        (fun i => p.2.2.2.2 (rightMomentIndex i))
    have hc := hcrossBound p.2.2.2.2
    gcongr
  have hproduct :
      Integrable
        (fun p =>
          r324Flatten
            (fun x y z w v =>
              renormalizedGreenSkeleton κp
                  (assemble x y
                    (fun i => v (leftMomentIndex i))) *
                renormalizedGreenSkeleton κm
                  (assemble z w
                    (fun i => v (rightMomentIndex i))))
            p * weight p)
        (r324PhysicalMeasure m) :=
    hbare.mul_bdd hweightMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hweightBound)
  apply hproduct.congr
  filter_upwards with p
  unfold r324Flatten
    r324InitialTwoHalfMarkedPhysicalCore
  rw [
    R324WithinHalfResidualPrefix.initial_residualIntegrand_complex_eq,
    R324WithinHalfResidualPrefix.initial_residualIntegrand_complex_eq]
  dsimp only [weight]
  ring

end SmoothCutoff

end

end Anderson4D
