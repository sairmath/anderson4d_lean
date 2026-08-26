import Anderson4D.Continuum.PrimitiveCopiedCell

/-!
# Sum-level periodic reduction for the primitive copied cells

The boundary-safe cell estimate produces `primitivePeriodicReductionWeight`,
not the ordinary Euclidean `reductionWeight`.  A pointwise comparison of
their edge factors with a mesh-independent constant is false across the
fundamental-domain cut.

This file records the strongest comparison available from the existing
period-lift machinery without such a false hypothesis:

* arbitrary endpoint filters are retained through the lossless copied-label
  reindexing;
* the periodic chain is identified with the centre-preserving unwrapped
  Euclidean chain;
* the copied diameter is bounded in the genuine finite canonical box;
* the resulting unwrapped sum enters the already proved primitive-across
  lattice machine, with every finite-box and winding loss displayed.

Thus no boundary loss is hidden in a pointwise `PeriodicCellEdgeComparison`.
The displayed mesh-dependent factors show that this fallback does not provide
the uniform sum-level estimate required by Proposition 4.1.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators ENNReal

/-! ## Diameter and exact unwrapped-chain ledgers -/

/-- Every nonempty lattice tuple has diameter bracket at least one. -/
theorem one_le_primitiveTupleDiameterBracketSq
    {m : ℕ} (hm : 0 < m) (y : Fin m → Z4) :
    1 ≤ primitiveTupleDiameterBracketSq hm y := by
  have h :=
    latticeBracketSq_le_primitiveTupleDiameterBracketSq
      hm y (⟨0, hm⟩ : Fin m) ⟨0, hm⟩
  simpa [latticeBracketSq, znorm] using h

/-- The diameter bracket of a tuple in `[-M,M]⁴` is bounded by the same
finite-box base used by the winding-sector module. -/
theorem primitiveTupleDiameterBracketSq_le_windingBoxBase
    {m M : ℕ} (hm : 0 < m) {y : Fin m → Z4}
    (hy : y ∈ rdec_boundedTuples M m) :
    primitiveTupleDiameterBracketSq hm y ≤ windingBoxBase M := by
  rw [rdec_mem_boundedTuples] at hy
  unfold primitiveTupleDiameterBracketSq
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  exact latticeBracketSq_le_windingBoxBase (hy i) (hy j)

/-- Exact division-free relation between the periodic copied statistic and
the ordinary reduction statistic of its centre-preserving unwrapped path.
Only the tuple diameter changes. -/
theorem primitivePeriodicCopiedWeight_mul_unwrappedDiameter
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    primitivePeriodicCopiedWeight ε n hn y *
        primitiveTupleDiameterBracketSq (by omega)
          (primitiveUnwrappedReductionTuple ε n hn y) =
      primitiveTupleDiameterBracketSq (by omega)
          (primitiveCopiedReductionTuple n hn y) *
        reductionWeight (2 * n - 1)
          (primitiveUnwrappedReductionTuple ε n hn y) := by
  rw [primitiveUnwrappedReductionWeight_eq,
    primitiveUnwrappedTerminalWeight_eq_periodicCopied hε]
  unfold primitivePeriodicCopiedWeight
  ring

/-- Pointwise comparison to the unwrapped ordinary statistic with only the
literal copied diameter as loss.  This is valid across the torus cut. -/
theorem primitivePeriodicCopiedWeight_le_diameter_mul_unwrapped
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    primitivePeriodicCopiedWeight ε n hn y ≤
      primitiveTupleDiameterBracketSq (by omega)
          (primitiveCopiedReductionTuple n hn y) *
        reductionWeight (2 * n - 1)
          (primitiveUnwrappedReductionTuple ε n hn y) := by
  let Dc :=
    primitiveTupleDiameterBracketSq (by omega)
      (primitiveCopiedReductionTuple n hn y)
  let Du :=
    primitiveTupleDiameterBracketSq (by omega)
      (primitiveUnwrappedReductionTuple ε n hn y)
  let W :=
    periodicTerminalPathWeight (compatibleMeshSize ε)
      (primitiveFirstCell n hn y)
      (primitiveLastCell n hn y)
      (primitiveInternalCellLabels n hn y)
  have hDc : 0 ≤ Dc := by
    dsimp only [Dc]
    exact primitiveTupleDiameterBracketSq_nonneg (by omega) _
  have hDu : 1 ≤ Du := by
    dsimp only [Du]
    exact one_le_primitiveTupleDiameterBracketSq (by omega) _
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact periodicTerminalPathWeight_nonneg _ _ _ _
  have hperiodic :
      primitivePeriodicCopiedWeight ε n hn y = Dc * W := by
    rfl
  have hunwrapped :
      reductionWeight (2 * n - 1)
          (primitiveUnwrappedReductionTuple ε n hn y) =
        Du * W := by
    rw [primitiveUnwrappedReductionWeight_eq,
      primitiveUnwrappedTerminalWeight_eq_periodicCopied hε]
  rw [hperiodic, hunwrapped]
  calc
    Dc * W = Dc * (1 * W) := by ring
    _ ≤ Dc * (Du * W) := by
      gcongr

/-- Canonical-box specialization of the preceding comparison. -/
theorem primitivePeriodicCopiedWeight_le_boxBase_mul_unwrapped
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    {κ : PartialPairing (Fin (2 * n))}
    {y : Fin (2 * n) → Z4}
    (hy : y ∈ primitiveCanonicalCellCarrier ε n κ) :
    primitivePeriodicCopiedWeight ε n hn y ≤
      windingBoxBase (primitiveCopiedBoxRadius ε) *
        reductionWeight (2 * n - 1)
          (primitiveUnwrappedReductionTuple ε n hn y) := by
  have hybox :
      y ∈ rdec_boundedTuples
        (primitiveCopiedBoxRadius ε) (2 * n) :=
    primitiveCanonicalCellCarrier_mem_bounded hε hy
  have hD :
      primitiveTupleDiameterBracketSq (by omega)
          (primitiveCopiedReductionTuple n hn y) ≤
        windingBoxBase (primitiveCopiedBoxRadius ε) := by
    rw [← primitiveCopiedCellDiameter_eq_reductionDiameter n hn y]
    exact primitiveTupleDiameterBracketSq_le_windingBoxBase
      (by omega) hybox
  have hR :
      0 ≤ reductionWeight (2 * n - 1)
        (primitiveUnwrappedReductionTuple ε n hn y) :=
    reductionWeight_nonneg _ _
  exact
    (primitivePeriodicCopiedWeight_le_diameter_mul_unwrapped
      hε n hn y).trans
      (mul_le_mul_of_nonneg_right hD hR)

/-! ## Arbitrarily filtered copied-label sums -/

/-- Real periodic reduction sum on the exact bounded copied-label carrier,
with an arbitrary endpoint/support predicate retained. -/
def primitivePeriodicReductionFilteredRealSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] : ℝ :=
  ∑ u ∈
      ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
          ((2 * n - 1) + 1)).filter
        (RespectsPairing
          (primitiveReductionPairing n hn κ))).filter P,
    primitivePeriodicReductionWeight ε n hn u

/-- Extended-real version consumed directly by the cell-integral layer. -/
def primitivePeriodicReductionFilteredSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] : ENNReal :=
  ∑ u ∈
      ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
          ((2 * n - 1) + 1)).filter
        (RespectsPairing
          (primitiveReductionPairing n hn κ))).filter P,
    ENNReal.ofReal (primitivePeriodicReductionWeight ε n hn u)

theorem primitivePeriodicReductionFilteredSum_eq_ofReal
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    primitivePeriodicReductionFilteredSum ε n hn κ P =
      ENNReal.ofReal
        (primitivePeriodicReductionFilteredRealSum ε n hn κ P) := by
  unfold primitivePeriodicReductionFilteredSum
    primitivePeriodicReductionFilteredRealSum
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro u hu
  exact primitivePeriodicReductionWeight_nonneg ε n hn u

/-- Exact lossless reindexing back to canonical copied labels, retaining
the support predicate. -/
theorem primitivePeriodicReductionFilteredRealSum_eq_copied
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    primitivePeriodicReductionFilteredRealSum ε n hn κ P =
      ∑ y ∈ (primitiveCanonicalCellCarrier ε n κ).filter
          (fun y => P (primitiveCopiedReductionTuple n hn y)),
        primitivePeriodicCopiedWeight ε n hn y := by
  symm
  unfold primitivePeriodicReductionFilteredRealSum
  simpa only [primitivePeriodicReductionWeight_reductionTuple] using
    sum_copiedLabels_filter_eq_boundedPairing_filter
      hε n hn κ P
        (primitivePeriodicReductionWeight ε n hn)

/-- Sum-level periodic-to-unwrapped comparison.  It is valid for every
endpoint filter, and the filter is discarded only after nonnegativity has
been used. -/
theorem primitivePeriodicReductionFilteredRealSum_le_unwrapped
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    primitivePeriodicReductionFilteredRealSum ε n hn κ P ≤
      windingBoxBase (primitiveCopiedBoxRadius ε) *
        primitiveUnwrappedReductionCellRealSum ε n hn κ := by
  rw [primitivePeriodicReductionFilteredRealSum_eq_copied
    hε n hn κ P]
  let S := primitiveCanonicalCellCarrier ε n κ
  let B := windingBoxBase (primitiveCopiedBoxRadius ε)
  let F : (Fin (2 * n) → Z4) → ℝ := fun y =>
    reductionWeight (2 * n - 1)
      (primitiveUnwrappedReductionTuple ε n hn y)
  calc
    (∑ y ∈ S.filter
        (fun y => P (primitiveCopiedReductionTuple n hn y)),
        primitivePeriodicCopiedWeight ε n hn y) ≤
      ∑ y ∈ S.filter
          (fun y => P (primitiveCopiedReductionTuple n hn y)),
        B * F y := by
      apply Finset.sum_le_sum
      intro y hy
      exact primitivePeriodicCopiedWeight_le_boxBase_mul_unwrapped
        hε n hn (Finset.mem_filter.mp hy).1
    _ ≤ ∑ y ∈ S, B * F y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
      intro y hyS hyfilter
      exact mul_nonneg (windingBoxBase_pos _).le
        (reductionWeight_nonneg _ _)
    _ = B * primitiveUnwrappedReductionCellRealSum ε n hn κ := by
      simp only [S, B, F, primitiveUnwrappedReductionCellRealSum,
        Finset.mul_sum]

/-- `ENNReal` form of the filtered periodic-to-unwrapped bridge. -/
theorem primitivePeriodicReductionFilteredSum_le_unwrapped
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    primitivePeriodicReductionFilteredSum ε n hn κ P ≤
      ENNReal.ofReal
        (windingBoxBase (primitiveCopiedBoxRadius ε) *
          primitiveUnwrappedReductionCellRealSum ε n hn κ) := by
  rw [primitivePeriodicReductionFilteredSum_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal
    (primitivePeriodicReductionFilteredRealSum_le_unwrapped
      hε n hn κ P)

/-! ## Entry into the existing primitive-across machine -/

/-- Complete unconditional fallback into the existing `reductionWeight`
machine for a primitive full pairing.  Every loss is explicit; in
particular no mesh-uniform edge comparison is used. -/
theorem exists_primitivePeriodicReductionFilteredRealSum_le_primitiveAcross
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    ∃ M : ℕ,
      primitivePeriodicReductionFilteredRealSum ε n hn κ P ≤
        windingBoxBase (primitiveCopiedBoxRadius ε) *
          ((primitiveCanonicalCellCarrier ε n κ).card : ℝ) *
          windingBoxAmplification M (2 * n - 1) *
          primitiveAcrossLatticeSum M (2 * n - 1)
            (pairingLowerHalf
              (primitiveReductionPairing n hn κ)) := by
  obtain ⟨M, hM⟩ :=
    exists_primitiveUnwrappedReductionCellRealSum_le_primitiveAcross
      ε n hn κ hfull hprimitive
  refine ⟨M, ?_⟩
  have hB : 0 ≤ windingBoxBase (primitiveCopiedBoxRadius ε) :=
    (windingBoxBase_pos _).le
  calc
    primitivePeriodicReductionFilteredRealSum ε n hn κ P ≤
        windingBoxBase (primitiveCopiedBoxRadius ε) *
          primitiveUnwrappedReductionCellRealSum ε n hn κ :=
      primitivePeriodicReductionFilteredRealSum_le_unwrapped
        hε n hn κ P
    _ ≤ windingBoxBase (primitiveCopiedBoxRadius ε) *
        (((primitiveCanonicalCellCarrier ε n κ).card : ℝ) *
          windingBoxAmplification M (2 * n - 1) *
          primitiveAcrossLatticeSum M (2 * n - 1)
            (pairingLowerHalf
              (primitiveReductionPairing n hn κ))) :=
      mul_le_mul_of_nonneg_left hM hB
    _ = _ := by ring

/-- Membership-specialized `ENNReal` endpoint for the actual primitive
pairing carrier used by §5.1. -/
theorem primitivePeriodicReductionFilteredSum_le_primitiveAcross
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (hκ : κ ∈ primitiveFullPairings n)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    ∃ M : ℕ,
      primitivePeriodicReductionFilteredSum ε n hn κ P ≤
        ENNReal.ofReal
          (windingBoxBase (primitiveCopiedBoxRadius ε) *
            ((primitiveCanonicalCellCarrier ε n κ).card : ℝ) *
            windingBoxBase M ^ (2 * n) *
            primitiveAcrossLatticeSum M (2 * n - 1)
              (pairingLowerHalf
                (primitiveReductionPairing n hn κ))) := by
  obtain ⟨hfull, hprimitive⟩ :=
    mem_primitiveFullPairings.mp hκ
  obtain ⟨M, hM⟩ :=
    exists_primitivePeriodicReductionFilteredRealSum_le_primitiveAcross
      hε n hn κ hfull hprimitive P
  refine ⟨M, ?_⟩
  rw [primitivePeriodicReductionFilteredSum_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  rw [windingBoxAmplification_eq_pow] at hM
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ 2 * n)] using hM

/-! ## Scalar extraction for the cell-integral consumer -/

/-- The two exhaustive-order coefficients and the covariance factor pull
out of an arbitrarily filtered periodic sum exactly. -/
theorem primitivePeriodicReductionFilteredSum_factor
    {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    (∑ u ∈
        ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
            ((2 * n - 1) + 1)).filter
          (RespectsPairing
            (primitiveReductionPairing n hn κ))).filter P,
        ENNReal.ofReal q *
          (ENNReal.ofReal
              (a * primitivePeriodicReductionWeight ε n hn u) +
           ENNReal.ofReal
              (b * primitivePeriodicReductionWeight ε n hn u))) =
      ENNReal.ofReal q *
        (ENNReal.ofReal a + ENNReal.ofReal b) *
          primitivePeriodicReductionFilteredSum ε n hn κ P := by
  unfold primitivePeriodicReductionFilteredSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [mul_add, ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  ring

end

end Anderson4D
