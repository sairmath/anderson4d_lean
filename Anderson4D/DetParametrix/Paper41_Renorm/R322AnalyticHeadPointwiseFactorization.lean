import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticBlockOrder
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticHeadSkeletonFactorization

/-!
# Pointwise first-step factorization of the actual R-322 fibre

The endpoint-fibre sum already factors into its common signed Green skeleton
and one complete primitive covariance sum for every extraction block.  This
file reorders those block coordinates by the paper's analytic schedule and
splits both products at the head.  The result is the exact pointwise
`head-local × outer` form used before the head coordinates are integrated.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The complete primitive covariance coordinate carried by one concrete
extraction block. -/
def r322ExtractionBlockPrimitiveSum
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (B : ExtractionBlockIndex κ)
    (x : Fin m → T4) : ℝ :=
  ∑ σ :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder B.1)) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder B.1)},
    extractionBlockPrimitiveCovarianceFactor
      ρ ε κ B σ x

/-- The local signed factor at the analytic head: every Green-chain factor
touching the head block, its endpoint difference, and the complete primitive
covariance sum on that block. -/
def r322AnalyticHeadLocalIntegrandFactor
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hschedule : r322AnalyticSchedule κ = head :: tail)
    (x : Fin m → T4) : ℝ :=
  r322AnalyticHeadLocalFactorWith
      (fun _ : Fin (m - 1) => greenFn)
      κ head x *
    r322ExtractionBlockPrimitiveSum ρ ε κ
      (r322AnalyticHeadBlockIndex κ hschedule) x

/-- Everything remaining outside the analytic head: the exterior Green and
later-difference skeleton, followed by all later primitive block sums. -/
def r322AnalyticHeadOuterIntegrandFactor
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hschedule : r322AnalyticSchedule κ = head :: tail)
    (x : Fin m → T4) : ℝ :=
  r322AnalyticHeadOuterFactorWith
      (fun _ : Fin (m - 1) => greenFn)
      κ head tail x *
    ∏ j : Fin tail.length,
      r322ExtractionBlockPrimitiveSum ρ ε κ
        (r322AnalyticTailBlockIndex κ hschedule j) x

/-- **Exact pointwise head factorization of the existing endpoint fibre.**

No model integrand or output predicate occurs here: the left side is the
finite sum of the project's actual `detJintegrand`.  Both the signed skeleton
and the dependent primitive block product are split at the first analytic
schedule step. -/
theorem sum_endpointFiber_detJintegrand_eq_analyticHead_mul_outer
    (ρ : SmoothCutoff) (ε : ℝ) {q : ℕ}
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ.IsFull)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule : r322AnalyticSchedule κ = head :: tail)
    (x : Fin (2 * q) → T4) :
    (∑ τ : ReductionEndpointFiberAt κ,
        detJintegrand ρ ε q τ.1 x) =
      r322AnalyticHeadLocalIntegrandFactor
          ρ ε κ head tail hschedule x *
        r322AnalyticHeadOuterIntegrandFactor
          ρ ε κ head tail hschedule x := by
  rw [
    sum_endpointFiber_detJintegrand_eq_skeleton_mul_prod_primitiveSums
      ρ ε κ hκ x,
    ← r322AnalyticGreenSkeleton_eq_renormalized κ x,
    r322AnalyticGreenSkeleton_eq_headLocal_mul_outer
      κ head tail x hschedule]
  change
    (_ * _) *
        (∏ B : ExtractionBlockIndex κ,
          r322ExtractionBlockPrimitiveSum ρ ε κ B x) =
      (_ *
          r322ExtractionBlockPrimitiveSum ρ ε κ
            (r322AnalyticHeadBlockIndex κ hschedule) x) *
        (_ *
          ∏ j : Fin tail.length,
            r322ExtractionBlockPrimitiveSum ρ ε κ
              (r322AnalyticTailBlockIndex κ hschedule j) x)
  rw [
    extractionBlock_prod_eq_head_mul_tail
      κ hschedule
      (fun B =>
        r322ExtractionBlockPrimitiveSum ρ ε κ B x)]
  ring

/-! ## The outer factor is independent of head-block coordinates -/

/-- The analytic schedule inherits pairwise disjointness from the concrete
extraction-block list. -/
theorem r322AnalyticSchedule_blocks_pairwise_disjoint
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    ((r322AnalyticSchedule κ).map Prod.snd).Pairwise
      Disjoint := by
  exact
    (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).pairwise_iff
      (fun h => h.symm)
      |>.mpr (extractionBlocks_pairwise_disjoint κ)

/-- In a displayed head/tail schedule, the concrete head block is disjoint
from every later concrete block. -/
theorem r322AnalyticHeadBlock_disjoint_tailBlock
    {m : ℕ} (κ : PartialPairing (Fin m))
    {head : R322ExtractionStep m}
    {tail : List (R322ExtractionStep m)}
    (hschedule : r322AnalyticSchedule κ = head :: tail)
    (j : Fin tail.length) :
    Disjoint head.2 (tail.get j).2 := by
  have hp :=
    r322AnalyticSchedule_blocks_pairwise_disjoint κ
  rw [hschedule] at hp
  simp only [List.map_cons] at hp
  exact
    (List.pairwise_cons.mp hp).1
      (tail.get j).2
      (List.mem_map.mpr
        ⟨tail.get j, List.get_mem tail j, rfl⟩)

/-- A primitive covariance coordinate reads only ambient positions belonging
to its certified extraction block. -/
theorem extractionBlockPrimitiveCovarianceFactor_eq_of_eq_on
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (B : ExtractionBlockIndex κ)
    (σ :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder B.1)) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder B.1)})
    (x y : Fin m → T4)
    (hxy : ∀ i, i ∈ B.1 → x i = y i) :
    extractionBlockPrimitiveCovarianceFactor
        ρ ε κ B σ x =
      extractionBlockPrimitiveCovarianceFactor
        ρ ε κ B σ y := by
  unfold extractionBlockPrimitiveCovarianceFactor
    primitiveCovarianceProduct
  apply Finset.prod_congr rfl
  intro i _hi
  let e :=
    residualPrimitiveBlockOrderIso κ B.1
      (extractionBlock_isFullyPairedOn_of_mem
        κ B.1 B.2)
  change
    ρ.etaEpsT4 ε
        (x (e i).1 - x (e (σ.1 i)).1) =
      ρ.etaEpsT4 ε
        (y (e i).1 - y (e (σ.1 i)).1)
  rw [hxy (e i).1 (e i).2,
    hxy (e (σ.1 i)).1 (e (σ.1 i)).2]

/-- Consequently the complete primitive sum on one block depends only on
that block's ambient coordinates. -/
theorem r322ExtractionBlockPrimitiveSum_eq_of_eq_on
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (B : ExtractionBlockIndex κ)
    (x y : Fin m → T4)
    (hxy : ∀ i, i ∈ B.1 → x i = y i) :
    r322ExtractionBlockPrimitiveSum ρ ε κ B x =
      r322ExtractionBlockPrimitiveSum ρ ε κ B y := by
  unfold r322ExtractionBlockPrimitiveSum
  apply Finset.sum_congr rfl
  intro σ _hσ
  exact
    extractionBlockPrimitiveCovarianceFactor_eq_of_eq_on
      ρ ε κ B σ x y hxy

/-- The product of all later primitive coordinates is unchanged when only
head-block coordinates move. -/
theorem r322AnalyticTailPrimitiveProduct_eq
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (x y : Fin m → T4)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hschedule : r322AnalyticSchedule κ = head :: tail)
    (hxy : ∀ i, i ∉ head.2 → x i = y i) :
    (∏ j : Fin tail.length,
        r322ExtractionBlockPrimitiveSum ρ ε κ
          (r322AnalyticTailBlockIndex κ hschedule j) x) =
      ∏ j : Fin tail.length,
        r322ExtractionBlockPrimitiveSum ρ ε κ
          (r322AnalyticTailBlockIndex κ hschedule j) y := by
  apply Finset.prod_congr rfl
  intro j _hj
  apply r322ExtractionBlockPrimitiveSum_eq_of_eq_on
  intro i hi
  apply hxy i
  have hdisjoint :=
    r322AnalyticHeadBlock_disjoint_tailBlock
      κ hschedule j
  rw [r322AnalyticTailBlockIndex_val] at hi
  exact (Finset.disjoint_left.mp hdisjoint.symm) hi

/-- The complete outer pointwise factor, including every later primitive
coordinate, is constant in the head-block variables. -/
theorem r322AnalyticHeadOuterIntegrandFactor_eq
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (x y : Fin m → T4)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hschedule : r322AnalyticSchedule κ = head :: tail)
    (hxy : ∀ i, i ∉ head.2 → x i = y i) :
    r322AnalyticHeadOuterIntegrandFactor
        ρ ε κ head tail hschedule x =
      r322AnalyticHeadOuterIntegrandFactor
        ρ ε κ head tail hschedule y := by
  unfold r322AnalyticHeadOuterIntegrandFactor
  rw [
    r322AnalyticHeadOuterFactorWith_eq
      (fun _ : Fin (m - 1) => greenFn)
      κ x y head tail hschedule hxy,
    r322AnalyticTailPrimitiveProduct_eq
      ρ ε κ x y head tail hschedule hxy]

end

end Anderson4D
