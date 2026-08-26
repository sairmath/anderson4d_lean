import Anderson4D.DetParametrix.Paper41_Renorm.R322CoordinateCollapseClosure
import Anderson4D.DetParametrix.Paper41_Renorm.R322SelectedBlockKernelClosure
import Anderson4D.DetParametrix.Paper41_Renorm.R322SelectedBlockBochnerFubini

/-!
# The actual first proper-block collapse for R-322

This file starts from the existing grouped kernel
`endpointFiberDetJSum`, not from a parallel model integrand.  The first
checkpoint exposes the spatial coordinates of the first selected extraction
block on the inside of the actual endpoint-fibre integral.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Internal coordinates belonging to an ambient extraction block -/

/-- Internal `detJ` coordinates whose assembled ambient vertices lie in
`B`.  For a proper block, every vertex of `B` occurs in this finset. -/
def r322InternalCoordinatesOfBlock
    (q : ℕ) (hq : 1 ≤ q)
    (B : Finset (Fin (2 * q))) :
    Finset (Fin (2 * q - 2)) :=
  Finset.univ.filter fun i =>
    primitiveInternalIdx q hq i ∈ B

@[simp]
theorem mem_r322InternalCoordinatesOfBlock
    (q : ℕ) (hq : 1 ≤ q)
    (B : Finset (Fin (2 * q)))
    (i : Fin (2 * q - 2)) :
    i ∈ r322InternalCoordinatesOfBlock q hq B ↔
      primitiveInternalIdx q hq i ∈ B := by
  simp [r322InternalCoordinatesOfBlock]

/-! ## The grouped kernel as one actual endpoint-fibre integral -/

/-- Move the complete endpoint-fibre sum inside the existing `detJ`
integral.  The premise is exactly the section integrability needed for
finite-sum linearity; no estimate or absolute value is used. -/
theorem endpointFiberDetJSum_eq_integral_sum_detJintegrand
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (z : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure)) :
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
      lamEps lam ε ^ (2 * q) *
        ∫ v : Fin (2 * q - 2) → T4,
          ∑ τ : ReductionEndpointFiberAt κ,
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v)
          ∂(Measure.pi fun _ => paperMeasure) := by
  rw [endpointFiberDetJSum_eq_fintype
    ρ lam ε κ hκ z]
  cases q with
  | zero =>
      omega
  | succ q =>
      simp_rw [detJ]
      rw [← Finset.mul_sum]
      apply congrArg
        (fun a : ℝ =>
          lamEps lam ε ^ (2 * (q + 1)) * a)
      rw [integral_finsetSum Finset.univ]
      · rfl
      · intro τ _hτ
        simpa only [Nat.succ_eq_add_one] using hint τ

/-! ## Actual selected-coordinate Fubini form -/

/-- Exact first-block Fubini form of the actual grouped kernel.

The selected block coordinates are integrated on the inside.  The
complementary spatial tuple remains the outer parameter, ready for the
pairing-complement sum and the replacement-edge identity. -/
theorem endpointFiberDetJSum_eq_firstBlockSpatialFubini
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (h :
      ∃ a b,
        IsRelFullyPaired κ
          (Finset.univ : Finset (Fin (2 * q))) a b)
    (z : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure)) :
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
      lamEps lam ε ^ (2 * q) *
        ∫ vC :
            {i : Fin (2 * q - 2) //
              ¬r322SelectedFinPredicate
                (r322InternalCoordinatesOfBlock q hq
                  (selectedExtractionBlock
                    κ Finset.univ h)) i} → T4,
          ∫ vB :
              {i : Fin (2 * q - 2) //
                r322SelectedFinPredicate
                  (r322InternalCoordinatesOfBlock q hq
                    (selectedExtractionBlock
                      κ Finset.univ h)) i} → T4,
            ∑ τ : ReductionEndpointFiberAt κ,
              detJintegrand ρ ε q τ.1
                (primitiveAssemble q hq z 0
                  (r322MergeSelectedFinCoordinates
                    (r322InternalCoordinatesOfBlock q hq
                      (selectedExtractionBlock
                        κ Finset.univ h))
                    vB vC))
            ∂Measure.pi fun _ => paperMeasure
          ∂Measure.pi fun _ => paperMeasure := by
  rw [
    endpointFiberDetJSum_eq_integral_sum_detJintegrand
      ρ lam ε hq κ hκ z hint]
  apply congrArg
    (fun a : ℝ => lamEps lam ε ^ (2 * q) * a)
  apply
    integral_fin_pi_eq_integral_complement_integral_block_bochner
  exact integrable_finsetSum Finset.univ fun τ _hτ =>
    hint τ

/-! ## Minimal actual proper-block phase: the nested order-four fibre -/

/-- The order-four nested pairing `(0, 3)(1, 2)`.  Its first extracted
block is the strict internal interval `{1, 2}`, while `(0, 3)` is the
terminal residual pair. -/
def pairingFinFourNested : PartialPairing (Fin 4) :=
  ⟨Fin.rev, Fin.rev_involutive⟩

@[simp]
theorem pairingFinFourNested_extract :
    extract pairingFinFourNested = [(1, 2), (0, 3)] := by
  decide

theorem pairingFinFourNested_mem_nonSplit :
    pairingFinFourNested ∈ nonSplitPairings 2 := by
  decide

/-- The realized endpoint fibre of the nested pairing contains exactly
that pairing.  The crossing pairing has a different extraction endpoint
signature. -/
theorem pairingFinFourNested_endpointFiber :
    (nonSplitPairings 2).filter
        (fun τ =>
          reductionEndpointSignature τ =
            reductionEndpointSignature pairingFinFourNested) =
      {pairingFinFourNested} := by
  decide

/-- The covariance representatives of the nested pairing are `0` and
`1`, so its two covariance edges are `(0, 3)` and `(1, 2)`. -/
theorem pairingFinFourNested_lowerSupport :
    pairingFinFourNested.pairSupport.filter
        (fun i => i < pairingFinFourNested i) =
      {0, 1} := by
  decide

/-- The first block in the extraction list is genuinely proper.  The
whole interval `(0, 3)` is retained as the distinct terminal phase. -/
theorem pairingFinFourNested_firstBlock_proper :
    ({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)) ≠ Finset.univ := by
  decide

/-- Closed form of the *existing* `detJintegrand` on the nested order-four
pairing.  In particular, the inner `(1, 2)` factors occur as one complete
order-one primitive block. -/
theorem detJintegrand_two_pairingFinFourNested
    (ρ : SmoothCutoff) (ε : ℝ) (x : Fin 4 → T4) :
    detJintegrand ρ ε 2 pairingFinFourNested x =
      greenFn (x 0 - x 1) *
        greenFn (x 1 - x 2) *
        (greenFn (x 2 - x 3) -
          greenFn (x 1 - x 3)) *
        (ρ.etaEpsT4 ε (x 0 - x 3) *
          ρ.etaEpsT4 ε (x 1 - x 2)) := by
  rw [detJintegrand, pairingFinFourNested_extract,
    pairingFinFourNested_lowerSupport]
  simp [Fin.prod_univ_three, pairingFinFourNested,
    diffFactorJ]

/-- At the nested endpoint signature the existing grouped sum is a
singleton, so no hidden multiplicity remains before the analytic
collapse. -/
theorem endpointFiberDetJSum_nested_two_eq_detJ
    (ρ : SmoothCutoff) (lam ε : ℝ) (z : T4) :
    endpointFiberDetJSum ρ lam ε 2
        (reductionEndpointSignature pairingFinFourNested) z =
      detJ ρ lam ε 2 pairingFinFourNested z 0 := by
  unfold endpointFiberDetJSum
  rw [pairingFinFourNested_endpointFiber]
  simp

/-- The assembled actual order-four integrand, with the proper block
coordinates displayed as the two entries of `v`. -/
theorem detJintegrand_two_pairingFinFourNested_assembled
    (ρ : SmoothCutoff) (ε : ℝ) (z : T4)
    (v : Fin 2 → T4) :
    detJintegrand ρ ε 2 pairingFinFourNested
        (primitiveAssemble 2 (by omega) z 0 v) =
      greenFn (z - v 0) *
        greenFn (v 0 - v 1) *
        (greenFn (v 1) - greenFn (v 0)) *
        (ρ.etaEpsT4 ε z *
          ρ.etaEpsT4 ε (v 0 - v 1)) := by
  rw [detJintegrand_two_pairingFinFourNested]
  simp [primitiveAssemble, assemble]

/-- Product-measure form of the actual nested `detJ`.  This is only a
change of variables from `Fin 2 → T4` to `T4 × T4`; the displayed
integrand was proved above by unfolding the project's `detJintegrand`. -/
theorem detJ_two_pairingFinFourNested_eq_prodIntegral
    (ρ : SmoothCutoff) (lam ε : ℝ) (z : T4) :
    detJ ρ lam ε 2 pairingFinFourNested z 0 =
      lamEps lam ε ^ 4 *
        ∫ p : T4 × T4,
          greenFn (z - p.1) *
            greenFn (p.1 - p.2) *
            (greenFn p.2 - greenFn p.1) *
            (ρ.etaEpsT4 ε z *
              ρ.etaEpsT4 ε (p.1 - p.2))
          ∂(paperMeasure.prod paperMeasure) := by
  rw [detJ]
  change
    lamEps lam ε ^ 4 *
        (∫ v : Fin 2 → T4,
          detJintegrand ρ ε 2 pairingFinFourNested
            (primitiveAssemble 2 (by omega) z 0 v)
          ∂Measure.pi fun _ => paperMeasure) =
      _
  apply congrArg (fun a : ℝ => lamEps lam ε ^ 4 * a)
  rw [integral_congr_ae
    (Filter.Eventually.of_forall fun v =>
      detJintegrand_two_pairingFinFourNested_assembled
        ρ ε z v)]
  simpa using
    (measurePreserving_finTwoArrow paperMeasure).integral_comp'
      (fun p : T4 × T4 =>
        greenFn (z - p.1) *
          greenFn (p.1 - p.2) *
          (greenFn p.2 - greenFn p.1) *
          (ρ.etaEpsT4 ε z *
            ρ.etaEpsT4 ε (p.1 - p.2)))

/-- The actual nested order-four kernel is the first genuine proper-block
collapse.  The factor outside the collapse is precisely the covariance
and coupling carried by the terminal residual pair `(0, 3)`. -/
theorem detJ_two_pairingFinFourNested_eq_firstProperBlockCollapse
    (ρ : SmoothCutoff) (lam ε : ℝ) (z : T4) :
    detJ ρ lam ε 2 pairingFinFourNested z 0 =
      (lamEps lam ε ^ 2 * ρ.etaEpsT4 ε z) *
        r322Collapse greenFn
          (primitiveKernelDiff ρ lam ε 1 (by omega)
            (fun _ => greenFn))
          greenFn z := by
  rw [detJ_two_pairingFinFourNested_eq_prodIntegral]
  unfold r322Collapse primitiveKernelDiff
    r322CollapseIntegrand
  simp_rw [primitiveKernel_one, sub_zero]
  let L : ℝ := lamEps lam ε
  let ηz : ℝ := ρ.etaEpsT4 ε z
  change
    L ^ 4 *
        (∫ p : T4 × T4,
          greenFn (z - p.1) *
            greenFn (p.1 - p.2) *
            (greenFn p.2 - greenFn p.1) *
            (ηz * ρ.etaEpsT4 ε (p.1 - p.2))
          ∂paperMeasure.prod paperMeasure) =
      (L ^ 2 * ηz) *
        ∫ p : T4 × T4,
          greenFn (z - p.1) *
            (L ^ 2 *
              (greenFn (p.1 - p.2) *
                ρ.etaEpsT4 ε (p.1 - p.2))) *
            (greenFn p.2 - greenFn p.1)
          ∂paperMeasure.prod paperMeasure
  calc
    _ = ∫ p : T4 × T4,
          L ^ 4 *
            (greenFn (z - p.1) *
              greenFn (p.1 - p.2) *
              (greenFn p.2 - greenFn p.1) *
              (ηz * ρ.etaEpsT4 ε (p.1 - p.2)))
          ∂paperMeasure.prod paperMeasure := by
        rw [integral_const_mul]
    _ = ∫ p : T4 × T4,
          (L ^ 2 * ηz) *
            (greenFn (z - p.1) *
              (L ^ 2 *
                (greenFn (p.1 - p.2) *
                  ρ.etaEpsT4 ε (p.1 - p.2))) *
              (greenFn p.2 - greenFn p.1))
          ∂paperMeasure.prod paperMeasure := by
        apply integral_congr_ae
        filter_upwards with p
        ring
    _ = _ := by
      rw [integral_const_mul]

/-- **Actual first proper-block replacement, minimal nonterminal case.**

The left side is the project's existing endpoint-fibre sum.  The right
side updates one named edge by the complete signed primitive sum over the
strict first block `{1, 2}`.  The invocation of
`selectedPrimitiveInnerIntegral_eq_replacementEdge` below is the precise
bridge from the selected-coordinate integral to the replacement edge. -/
theorem endpointFiberDetJSum_nested_two_eq_firstProperBlockReplacement
    (ρ : SmoothCutoff) (lam ε : ℝ) (z : T4) :
    endpointFiberDetJSum ρ lam ε 2
        (reductionEndpointSignature pairingFinFourNested) z =
      (lamEps lam ε ^ 2 * ρ.etaEpsT4 ε z) *
        r322ReplaceEdge
          (fun _ : Fin 1 => greenFn) 0
          greenFn
          (primitiveKernelDiff ρ lam ε 1 (by omega)
            (fun _ => greenFn))
          greenFn 0 z := by
  calc
    endpointFiberDetJSum ρ lam ε 2
        (reductionEndpointSignature pairingFinFourNested) z =
        (lamEps lam ε ^ 2 * ρ.etaEpsT4 ε z) *
          r322Collapse greenFn
            (primitiveKernelDiff ρ lam ε 1 (by omega)
              (fun _ => greenFn))
            greenFn z := by
      rw [endpointFiberDetJSum_nested_two_eq_detJ]
      exact
        detJ_two_pairingFinFourNested_eq_firstProperBlockCollapse
          ρ lam ε z
    _ =
        (lamEps lam ε ^ 2 * ρ.etaEpsT4 ε z) *
          ∫ p,
            r322CollapseIntegrand greenFn
              (r322SelectedPrimitiveKernelSum
                ρ lam ε 1 (by omega)
                (fun _ => greenFn))
              greenFn z p
            ∂(paperMeasure.prod paperMeasure) := by
      rw [
        r322SelectedPrimitiveKernelSum_eq_primitiveKernelDiff]
      rfl
    _ = _ := by
      rw [
        selectedPrimitiveInnerIntegral_eq_replacementEdge
          (edges := fun _ : Fin 1 => greenFn)
          (slot := (0 : Fin 1))]

/-! ## Terminal phase kept separate -/

/-- The whole order-two interval is terminal: it is identified directly
with the complete primitive kernel and is **not** represented as a
proper-block collapse. -/
theorem endpointFiberDetJSum_terminal_one_eq_primitiveKernelDiff
    (ρ : SmoothCutoff) (lam ε : ℝ) (z : T4) :
    endpointFiberDetJSum ρ lam ε 1
        (reductionEndpointSignature pairingFinTwo) z =
      primitiveKernelDiff ρ lam ε 1 (by omega)
        (fun _ => greenFn) z := by
  unfold endpointFiberDetJSum
  rw [nonSplitPairings_one_eq]
  simp only [Finset.filter_singleton]
  simp only [if_true, Finset.sum_singleton]
  rw [detJ_one_eq_primitiveKernel]
  rfl

end

end Anderson4D
