import Anderson4D.PermSum.SingleScaleInnerAssembly

/-!
# Shared-state elimination for the two anchored runs

The local one-parity eliminator in `SingleScaleInnerAssembly` returns a
number and therefore forgets the final set of labeled copies.  At an
interior anchor, however, the right outward run must see every copy already
used by the left outward run.  This file supplies the continuation-passing
variant needed for that finite-Fubini step.

The terminal continuation receives both the final `used` set and the final
lattice point.  In `conditionedNXAnchoredRunsSum` the continuation keeps the
former and deliberately discards the latter: the right run restarts at the
anchor point, so no artificial edge between the two outer endpoints is
introduced.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

private theorem sharedLambda_nonneg (c : XYCluster) (R : ℝ)
    (skipped : Bool) (x y : Fin 4 → ℤ) :
    0 ≤ c.lambda R skipped x y := by
  unfold lambda
  split_ifs <;> positivity

private theorem sharedStrongLambda_nonneg (a b : XYCluster) (R : ℝ)
    (skipped : Bool) (x y : Fin 4 → ℤ) :
    0 ≤ strongLambda a b R skipped x y := by
  unfold strongLambda
  split_ifs <;> positivity

/--
Continuation-passing version of `conditionedNXParityChainSum`.

At the empty schedule it exposes the final used-copy set and final point to
`tail`; all nonempty cases are exactly the existing conditioned eliminator.
-/
noncomputable def conditionedNXParityChainSumThen {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) :
    List (NXParityBlock Nm mu) →
      Finset (HeppLabeledCopy mu) → (Fin 4 → ℤ) →
      (Finset (HeppLabeledCopy mu) → (Fin 4 → ℤ) → ℝ) → ℝ
  | [], used, u, tail => tail used u
  | .single a skipped :: ps, used, u, tail =>
      let ca := nxClassCluster ht hroot Nm mu z hz a.1 a.2
      ∑ x ∈ conditionedCopiesAtNX Nm mu used a.1,
        ca.lambda R skipped u (labeledCopyPoint z x) *
          conditionedNXParityChainSumThen ht hroot Nm mu z hz R ps
            (insert x used) (labeledCopyPoint z x) tail
  | .pair p :: ps, used, u, tail =>
      let ca :=
        nxClassCluster ht hroot Nm mu z hz p.left.1 p.left.2
      let cb :=
        nxClassCluster ht hroot Nm mu z hz p.right.1 p.right.2
      ∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
                (labeledCopyPoint z x) (labeledCopyPoint z y) *
              conditionedNXParityChainSumThen ht hroot Nm mu z hz R ps
                (insert y (insert x used)) (labeledCopyPoint z y) tail
  | .roughPair p :: ps, used, u, tail =>
      let ca :=
        nxClassCluster ht hroot Nm mu z hz p.left.1 p.left.2
      let cb :=
        nxClassCluster ht hroot Nm mu z hz p.right.1 p.right.2
      ∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
                (labeledCopyPoint z x) (labeledCopyPoint z y) *
              conditionedNXParityChainSumThen ht hroot Nm mu z hz R ps
                (insert y (insert x used)) (labeledCopyPoint z y) tail

/-- The CPS eliminator is monotone in its terminal continuation. -/
theorem conditionedNXParityChainSumThen_mono {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (ps : List (NXParityBlock Nm mu))
    (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ)
    (tail₁ tail₂ :
      Finset (HeppLabeledCopy mu) → (Fin 4 → ℤ) → ℝ)
    (htail : ∀ used' u', tail₁ used' u' ≤ tail₂ used' u') :
    conditionedNXParityChainSumThen ht hroot Nm mu z hz R
        ps used u tail₁ ≤
      conditionedNXParityChainSumThen ht hroot Nm mu z hz R
        ps used u tail₂ := by
  induction ps generalizing used u with
  | nil =>
      exact htail used u
  | cons p ps ih =>
      cases p with
      | single a skipped =>
          simp only [conditionedNXParityChainSumThen]
          apply Finset.sum_le_sum
          intro x _hx
          exact mul_le_mul_of_nonneg_left
            (ih (insert x used) (labeledCopyPoint z x))
            (sharedLambda_nonneg _ _ _ _ _)
      | pair p =>
          simp only [conditionedNXParityChainSumThen]
          apply Finset.sum_le_sum
          intro x _hx
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro y _hy
            exact mul_le_mul_of_nonneg_left
              (ih (insert y (insert x used)) (labeledCopyPoint z y))
              (sharedStrongLambda_nonneg _ _ _ _ _ _)
          · exact sharedLambda_nonneg _ _ _ _ _
      | roughPair p =>
          simp only [conditionedNXParityChainSumThen]
          apply Finset.sum_le_sum
          intro x _hx
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro y _hy
            exact mul_le_mul_of_nonneg_left
              (ih (insert y (insert x used)) (labeledCopyPoint z y))
              (sharedStrongLambda_nonneg _ _ _ _ _ _)
          · exact sharedLambda_nonneg _ _ _ _ _

/--
A constant terminal continuation factors out of the CPS eliminator.  This
also records that the existing eliminator is the unit-terminal special case.
-/
theorem conditionedNXParityChainSumThen_const {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R K : ℝ) (ps : List (NXParityBlock Nm mu))
    (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ) :
    conditionedNXParityChainSumThen ht hroot Nm mu z hz R ps used u
        (fun _used _u => K) =
      conditionedNXParityChainSum ht hroot Nm mu z hz R ps used u * K := by
  induction ps generalizing used u with
  | nil =>
      simp [conditionedNXParityChainSumThen,
        conditionedNXParityChainSum]
  | cons p ps ih =>
      cases p with
      | single a skipped =>
          simp only [conditionedNXParityChainSumThen,
            conditionedNXParityChainSum]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _hx
          rw [ih]
          ring
      | pair p =>
          simp only [conditionedNXParityChainSumThen,
            conditionedNXParityChainSum]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _hx
          simp_rw [ih, ← mul_assoc]
          rw [← Finset.sum_mul]
          ring
      | roughPair p =>
          simp only [conditionedNXParityChainSumThen,
            conditionedNXParityChainSum]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x _hx
          simp_rw [ih, ← mul_assoc]
          rw [← Finset.sum_mul]
          ring

/-- Unit continuation recovers `conditionedNXParityChainSum` exactly. -/
theorem conditionedNXParityChainSumThen_one {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (ps : List (NXParityBlock Nm mu))
    (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ) :
    conditionedNXParityChainSumThen ht hroot Nm mu z hz R ps used u
        (fun _used _u => 1) =
      conditionedNXParityChainSum ht hroot Nm mu z hz R ps used u := by
  simpa using
    conditionedNXParityChainSumThen_const ht hroot Nm mu z hz
      R 1 ps used u

/-- A nonnegative terminal continuation gives a nonnegative CPS sum. -/
theorem conditionedNXParityChainSumThen_nonneg {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (ps : List (NXParityBlock Nm mu))
    (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ)
    (tail : Finset (HeppLabeledCopy mu) → (Fin 4 → ℤ) → ℝ)
    (htail : ∀ used' u', 0 ≤ tail used' u') :
    0 ≤ conditionedNXParityChainSumThen ht hroot Nm mu z hz R
      ps used u tail := by
  calc
    0 =
        conditionedNXParityChainSumThen ht hroot Nm mu z hz R
          ps used u (fun _used _u => 0) := by
      rw [conditionedNXParityChainSumThen_const]
      ring
    _ ≤ conditionedNXParityChainSumThen ht hroot Nm mu z hz R
        ps used u tail :=
      conditionedNXParityChainSumThen_mono ht hroot Nm mu z hz R
        ps used u (fun _used _u => 0) tail htail

/-- Pull the same scalar out of every factor in a list product. -/
private theorem conditionedNX_prod_map_const_mul {α : Type*}
    (C : ℝ) (f : α → ℝ)
    (xs : List α) :
    (xs.map fun x => C * f x).prod =
      C ^ xs.length * (xs.map f).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, ih,
        pow_succ]
      ring

/--
Uniform target-product estimate with an arbitrary bounded terminal
continuation.  The constant is exactly the one from
`conditionedNXParityChainSum_le_targetProduct`.
-/
theorem conditionedNXParityChainSumThen_le_scaledTargetProduct :
    ∃ C : ℝ, 256 ≤ C ∧
      ∀ {t : PlaneTree}
        (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ (ps : List (NXParityBlock Nm mu))
          (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ)
          (tail :
            Finset (HeppLabeledCopy mu) → (Fin 4 → ℤ) → ℝ)
          (K : ℝ), 0 ≤ K →
          (∀ used' u', tail used' u' ≤ K) →
          conditionedNXParityChainSumThen ht hroot Nm mu z hz (R : ℝ)
              ps used u tail ≤
            K * (ps.map fun p =>
              C * nxParityBlockTarget Nm mu (R : ℝ) p).prod := by
  obtain ⟨C, hC, hchain⟩ :=
    conditionedNXParityChainSum_le_targetProduct
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu z hz R hR ps used u tail K hK htail
  calc
    conditionedNXParityChainSumThen ht hroot Nm mu z hz (R : ℝ)
        ps used u tail ≤
      conditionedNXParityChainSumThen ht hroot Nm mu z hz (R : ℝ)
        ps used u (fun _used _u => K) :=
      conditionedNXParityChainSumThen_mono
        ht hroot Nm mu z hz (R : ℝ) ps used u
          tail (fun _used _u => K) htail
    _ = conditionedNXParityChainSum ht hroot Nm mu z hz (R : ℝ)
        ps used u * K :=
      conditionedNXParityChainSumThen_const
        ht hroot Nm mu z hz (R : ℝ) K ps used u
    _ ≤ (ps.map fun p =>
          C * nxParityBlockTarget Nm mu (R : ℝ) p).prod * K :=
      mul_le_mul_of_nonneg_right
        (hchain ht hroot Nm mu z hz R hR ps used u) hK
    _ = K * (ps.map fun p =>
          C * nxParityBlockTarget Nm mu (R : ℝ) p).prod := by
      ring

/-- The same continuation estimate with the constant power made explicit. -/
theorem conditionedNXParityChainSumThen_le_pow_mul_targetProduct :
    ∃ C : ℝ, 256 ≤ C ∧
      ∀ {t : PlaneTree}
        (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ (ps : List (NXParityBlock Nm mu))
          (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ)
          (tail :
            Finset (HeppLabeledCopy mu) → (Fin 4 → ℤ) → ℝ)
          (K : ℝ), 0 ≤ K →
          (∀ used' u', tail used' u' ≤ K) →
          conditionedNXParityChainSumThen ht hroot Nm mu z hz (R : ℝ)
              ps used u tail ≤
            K * C ^ ps.length *
              (ps.map fun p =>
                nxParityBlockTarget Nm mu (R : ℝ) p).prod := by
  obtain ⟨C, hC, hbound⟩ :=
    conditionedNXParityChainSumThen_le_scaledTargetProduct
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu z hz R hR ps used u tail K hK htail
  calc
    conditionedNXParityChainSumThen ht hroot Nm mu z hz (R : ℝ)
        ps used u tail ≤
      K * (ps.map fun p =>
        C * nxParityBlockTarget Nm mu (R : ℝ) p).prod :=
      hbound ht hroot Nm mu z hz R hR ps used u tail K hK htail
    _ = K * C ^ ps.length *
        (ps.map fun p =>
          nxParityBlockTarget Nm mu (R : ℝ) p).prod := by
      rw [conditionedNX_prod_map_const_mul]
      ring

/-! ## Two outward runs with one genuinely shared used-copy state -/

/--
Run the left schedule first and pass its final used-copy set to the right
schedule.  The right schedule restarts at `anchorPoint`; the terminal point
of the left schedule is intentionally ignored.
-/
noncomputable def conditionedNXAnchoredRunsSum {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (left right : List (NXParityBlock Nm mu))
    (used : Finset (HeppLabeledCopy mu))
    (anchorPoint : Fin 4 → ℤ) : ℝ :=
  conditionedNXParityChainSumThen ht hroot Nm mu z hz R
    left used anchorPoint fun usedAfterLeft _leftEndpoint =>
      conditionedNXParityChainSum ht hroot Nm mu z hz R
        right usedAfterLeft anchorPoint

/-- Both outward runs remain nonnegative when they share the used set. -/
theorem conditionedNXAnchoredRunsSum_nonneg {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (left right : List (NXParityBlock Nm mu))
    (used : Finset (HeppLabeledCopy mu))
    (anchorPoint : Fin 4 → ℤ) :
    0 ≤ conditionedNXAnchoredRunsSum ht hroot Nm mu z hz R
      left right used anchorPoint := by
  unfold conditionedNXAnchoredRunsSum
  apply conditionedNXParityChainSumThen_nonneg
  intro usedAfterLeft _leftEndpoint
  exact conditionedNXParityChainSum_nonneg
    ht hroot Nm mu z hz R right usedAfterLeft anchorPoint

/--
The shared-state two-run sum is bounded by the product of the two local
target products.  The same universal constant is used on both sides.
-/
theorem conditionedNXAnchoredRunsSum_le_scaledTargetProducts :
    ∃ C : ℝ, 256 ≤ C ∧
      ∀ {t : PlaneTree}
        (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ (left right : List (NXParityBlock Nm mu))
          (used : Finset (HeppLabeledCopy mu))
          (anchorPoint : Fin 4 → ℤ),
          conditionedNXAnchoredRunsSum ht hroot Nm mu z hz (R : ℝ)
              left right used anchorPoint ≤
            (left.map fun p =>
              C * nxParityBlockTarget Nm mu (R : ℝ) p).prod *
            (right.map fun p =>
              C * nxParityBlockTarget Nm mu (R : ℝ) p).prod := by
  obtain ⟨C, hC, hchain⟩ :=
    conditionedNXParityChainSum_le_targetProduct
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu z hz R hR left right used anchorPoint
  let rightTarget : ℝ :=
    (right.map fun p =>
      C * nxParityBlockTarget Nm mu (R : ℝ) p).prod
  have hC0 : 0 ≤ C := by linarith
  have hrightTarget : 0 ≤ rightTarget := by
    unfold rightTarget
    apply List.prod_nonneg
    intro q hq
    obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp hq
    exact mul_nonneg hC0
      (nxParityBlockTarget_nonneg Nm mu (R : ℝ) p)
  calc
    conditionedNXAnchoredRunsSum ht hroot Nm mu z hz (R : ℝ)
        left right used anchorPoint =
      conditionedNXParityChainSumThen ht hroot Nm mu z hz (R : ℝ)
        left used anchorPoint
          (fun usedAfterLeft _leftEndpoint =>
            conditionedNXParityChainSum ht hroot Nm mu z hz (R : ℝ)
              right usedAfterLeft anchorPoint) := rfl
    _ ≤ conditionedNXParityChainSumThen ht hroot Nm mu z hz (R : ℝ)
        left used anchorPoint (fun _used _u => rightTarget) :=
      conditionedNXParityChainSumThen_mono
        ht hroot Nm mu z hz (R : ℝ) left used anchorPoint
        (fun usedAfterLeft _leftEndpoint =>
          conditionedNXParityChainSum ht hroot Nm mu z hz (R : ℝ)
            right usedAfterLeft anchorPoint)
        (fun _used _u => rightTarget)
        (fun usedAfterLeft _leftEndpoint =>
          hchain ht hroot Nm mu z hz R hR
            right usedAfterLeft anchorPoint)
    _ = conditionedNXParityChainSum ht hroot Nm mu z hz (R : ℝ)
        left used anchorPoint * rightTarget :=
      conditionedNXParityChainSumThen_const
        ht hroot Nm mu z hz (R : ℝ) rightTarget
          left used anchorPoint
    _ ≤ (left.map fun p =>
          C * nxParityBlockTarget Nm mu (R : ℝ) p).prod *
        rightTarget :=
      mul_le_mul_of_nonneg_right
        (hchain ht hroot Nm mu z hz R hR left used anchorPoint)
        hrightTarget
    _ = (left.map fun p =>
          C * nxParityBlockTarget Nm mu (R : ℝ) p).prod *
        (right.map fun p =>
          C * nxParityBlockTarget Nm mu (R : ℝ) p).prod := rfl

/--
Paper-facing normalization of the two-run bound: one factor `C` per
elimination block, followed by the unscaled left and right target products.
-/
theorem conditionedNXAnchoredRunsSum_le_pow_mul_targetProducts :
    ∃ C : ℝ, 256 ≤ C ∧
      ∀ {t : PlaneTree}
        (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ (left right : List (NXParityBlock Nm mu))
          (used : Finset (HeppLabeledCopy mu))
          (anchorPoint : Fin 4 → ℤ),
          conditionedNXAnchoredRunsSum ht hroot Nm mu z hz (R : ℝ)
              left right used anchorPoint ≤
            C ^ (left.length + right.length) *
              (left.map fun p =>
                nxParityBlockTarget Nm mu (R : ℝ) p).prod *
              (right.map fun p =>
                nxParityBlockTarget Nm mu (R : ℝ) p).prod := by
  obtain ⟨C, hC, hbound⟩ :=
    conditionedNXAnchoredRunsSum_le_scaledTargetProducts
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu z hz R hR left right used anchorPoint
  calc
    conditionedNXAnchoredRunsSum ht hroot Nm mu z hz (R : ℝ)
        left right used anchorPoint ≤
      (left.map fun p =>
        C * nxParityBlockTarget Nm mu (R : ℝ) p).prod *
      (right.map fun p =>
        C * nxParityBlockTarget Nm mu (R : ℝ) p).prod :=
      hbound ht hroot Nm mu z hz R hR
        left right used anchorPoint
    _ = C ^ (left.length + right.length) *
        (left.map fun p =>
          nxParityBlockTarget Nm mu (R : ℝ) p).prod *
        (right.map fun p =>
          nxParityBlockTarget Nm mu (R : ℝ) p).prod := by
      rw [conditionedNX_prod_map_const_mul,
        conditionedNX_prod_map_const_mul, pow_add]
      ring

end XYCluster

end

end Anderson4D
