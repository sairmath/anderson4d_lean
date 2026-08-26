import Anderson4D.PermSum.SingleScaleInnerAssembly

/-!
# Pointwise chain-weight bridge for the single-scale proof

The local estimates use the kernels `lambda` and `strongLambda`, while the
frozen Proposition 5.10 statement uses
`latticeEdgeWeight x y = (1 + ‖x-y‖²)⁻¹`.  This file records the pointwise
comparisons needed by the final finite-Fubini assembly.

For an unskipped edge, separation at the LCA scale activates the local
cutoff and the statement weight is bounded by the inverse-square kernel.
For a skipped edge, multiplying the local value `R⁻²` by `R²` recovers the
omitted statement factor exactly.
-/

namespace Anderson4D

open PlaneTree

noncomputable section

namespace XYCluster

/-- The bracketed lattice weight is no larger than the homogeneous
inverse-square weight away from the diagonal. -/
theorem latticeEdgeWeight_le_norm_inv_sq
    (x y : Fin 4 → ℤ) (hxy : 0 < znorm (x - y)) :
    latticeEdgeWeight x y ≤ (znorm (x - y))⁻¹ ^ 2 := by
  unfold latticeEdgeWeight
  have hsq : 0 < znorm (x - y) ^ 2 := sq_pos_of_pos hxy
  have hden :
      znorm (x - y) ^ 2 ≤ 1 + znorm (x - y) ^ 2 := by
    linarith
  rw [inv_pow]
  exact (inv_le_inv₀ (by positivity) hsq).2 hden

/--
An unskipped edge entering a leaf in the active `(N,X)` class `a` is
bounded by that class's `lambda` kernel.
-/
theorem latticeEdgeWeight_le_nxClassLambda_unskipped
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) {l r : HeppLeaf t} (hlr : l ≠ r)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu)
    (hra : singleScaleSigma1 Nm mu r = a) :
    latticeEdgeWeight (z l) (z r) ≤
      (nxClassCluster ht hroot Nm mu z hz a ha).lambda
        R false (z l) (z r) := by
  let c := nxClassCluster ht hroot Nm mu z hz a ha
  have hsep := parentScale_separation ht hroot Nm z hz hlr
  have hraN :
      scaleN Nm (parentV r.1) = a.1 :=
    congrArg Prod.fst hra
  have hright :
      ((scaleN Nm (parentV r.1) : ℕ) : ℝ) / 2 ≤
        ((max (scaleN Nm (parentV l.1))
          (scaleN Nm (parentV r.1)) : ℕ) : ℝ) / 2 := by
    gcongr
    exact le_max_right _ _
  have hcN :
      c.N ≤ znorm (z l - z r) := by
    rw [show c.N = (a.1 : ℝ) / 2 by
      exact nxClassCluster_N ht hroot Nm mu z hz a ha,
      ← hraN]
    exact hright.trans hsep
  have hdist : 0 < znorm (z l - z r) :=
    lt_of_lt_of_le
      (lt_of_lt_of_le one_pos c.one_le_N) hcN
  change latticeEdgeWeight (z l) (z r) ≤
    c.lambda R false (z l) (z r)
  rw [lambda]
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos hcN]
  exact latticeEdgeWeight_le_norm_inv_sq (z l) (z r) hdist

/--
The stronger cutoff on the second edge is also activated by LCA
separation when its two endpoint classes are fixed.
-/
theorem latticeEdgeWeight_le_nxClassStrongLambda_unskipped
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) {l r : HeppLeaf t} (hlr : l ≠ r)
    {a b : NXClass} (ha : a ∈ nxCarrier Nm mu)
    (hb : b ∈ nxCarrier Nm mu)
    (hla : singleScaleSigma1 Nm mu l = a)
    (hrb : singleScaleSigma1 Nm mu r = b) :
    latticeEdgeWeight (z l) (z r) ≤
      strongLambda
        (nxClassCluster ht hroot Nm mu z hz a ha)
        (nxClassCluster ht hroot Nm mu z hz b hb)
        R false (z l) (z r) := by
  let ca := nxClassCluster ht hroot Nm mu z hz a ha
  let cb := nxClassCluster ht hroot Nm mu z hz b hb
  have hsep := parentScale_separation ht hroot Nm z hz hlr
  have hlaN :
      scaleN Nm (parentV l.1) = a.1 :=
    congrArg Prod.fst hla
  have hrbN :
      scaleN Nm (parentV r.1) = b.1 :=
    congrArg Prod.fst hrb
  have haN :
      ca.N ≤ znorm (z l - z r) := by
    have hcast :
        (scaleN Nm (parentV l.1) : ℝ) ≤
          max (scaleN Nm (parentV l.1))
            (scaleN Nm (parentV r.1)) := by
      exact_mod_cast
        (le_max_left (scaleN Nm (parentV l.1))
          (scaleN Nm (parentV r.1)))
    rw [show ca.N = (a.1 : ℝ) / 2 by
      exact nxClassCluster_N ht hroot Nm mu z hz a ha,
      ← hlaN]
    exact (div_le_div_of_nonneg_right
      hcast
      (by norm_num)).trans hsep
  have hbN :
      cb.N ≤ znorm (z l - z r) := by
    have hcast :
        (scaleN Nm (parentV r.1) : ℝ) ≤
          max (scaleN Nm (parentV l.1))
            (scaleN Nm (parentV r.1)) := by
      exact_mod_cast
        (le_max_right (scaleN Nm (parentV l.1))
          (scaleN Nm (parentV r.1)))
    rw [show cb.N = (b.1 : ℝ) / 2 by
      exact nxClassCluster_N ht hroot Nm mu z hz b hb,
      ← hrbN]
    exact (div_le_div_of_nonneg_right
      hcast
      (by norm_num)).trans hsep
  have hmax :
      max ca.N cb.N ≤ znorm (z l - z r) :=
    max_le haN hbN
  have hdist : 0 < znorm (z l - z r) :=
    lt_of_lt_of_le
      (lt_of_lt_of_le one_pos ca.one_le_N) haN
  change latticeEdgeWeight (z l) (z r) ≤
    strongLambda ca cb R false (z l) (z r)
  rw [strongLambda]
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos hmax]
  exact latticeEdgeWeight_le_norm_inv_sq (z l) (z r) hdist

/-- A skipped local edge contributes exactly `R⁻²`, hence its omitted
statement factor is recovered by the global `R²` budget. -/
theorem sq_mul_lambda_skipped
    (c : XYCluster) (R : ℝ) (hR : R ≠ 0)
    (u x : Fin 4 → ℤ) :
    R ^ 2 * c.lambda R true u x = 1 := by
  simp only [lambda, if_true]
  field_simp

/-- Strong-kernel version of `sq_mul_lambda_skipped`. -/
theorem sq_mul_strongLambda_skipped
    (a b : XYCluster) (R : ℝ) (hR : R ≠ 0)
    (x y : Fin 4 → ℤ) :
    R ^ 2 * strongLambda a b R true x y = 1 := by
  simp only [strongLambda, if_true]
  field_simp

/-! ## Uniform pointwise and product interfaces -/

/-- The factor printed in the skipped-chain product at one edge. -/
def edgeStatementFactor (skipped : Bool)
    (x y : Fin 4 → ℤ) : ℝ :=
  if skipped then 1 else latticeEdgeWeight x y

theorem edgeStatementFactor_nonneg
    (skipped : Bool) (x y : Fin 4 → ℤ) :
    0 ≤ edgeStatementFactor skipped x y := by
  unfold edgeStatementFactor latticeEdgeWeight
  split_ifs <;> positivity

/--
Pointwise statement-to-`lambda` comparison, including the exact `R²`
charge on a skipped edge.
-/
theorem edgeStatementFactor_le_scaled_nxClassLambda
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (hR : R ≠ 0) {l r : HeppLeaf t}
    (skipped : Bool) (hlr : skipped = false → l ≠ r)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu)
    (hra : singleScaleSigma1 Nm mu r = a) :
    edgeStatementFactor skipped (z l) (z r) ≤
      (if skipped then R ^ 2 else 1) *
        (nxClassCluster ht hroot Nm mu z hz a ha).lambda
          R skipped (z l) (z r) := by
  cases skipped with
  | false =>
      simp only [edgeStatementFactor, Bool.false_eq_true, if_false,
        one_mul]
      exact latticeEdgeWeight_le_nxClassLambda_unskipped
        ht hroot Nm mu z hz R (hlr rfl) ha hra
  | true =>
      simp only [edgeStatementFactor, if_true]
      exact le_of_eq
        (sq_mul_lambda_skipped
          (nxClassCluster ht hroot Nm mu z hz a ha)
          R hR (z l) (z r)).symm

/--
Pointwise statement-to-`strongLambda` comparison for the second edge of a
paired elimination block.
-/
theorem edgeStatementFactor_le_scaled_nxClassStrongLambda
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (hR : R ≠ 0) {l r : HeppLeaf t}
    (skipped : Bool) (hlr : skipped = false → l ≠ r)
    {a b : NXClass} (ha : a ∈ nxCarrier Nm mu)
    (hb : b ∈ nxCarrier Nm mu)
    (hla : singleScaleSigma1 Nm mu l = a)
    (hrb : singleScaleSigma1 Nm mu r = b) :
    edgeStatementFactor skipped (z l) (z r) ≤
      (if skipped then R ^ 2 else 1) *
        strongLambda
          (nxClassCluster ht hroot Nm mu z hz a ha)
          (nxClassCluster ht hroot Nm mu z hz b hb)
          R skipped (z l) (z r) := by
  cases skipped with
  | false =>
      simp only [edgeStatementFactor, Bool.false_eq_true, if_false,
        one_mul]
      exact latticeEdgeWeight_le_nxClassStrongLambda_unskipped
        ht hroot Nm mu z hz R (hlr rfl) ha hb hla hrb
  | true =>
      simp only [edgeStatementFactor, if_true]
      exact le_of_eq
        (sq_mul_strongLambda_skipped
          (nxClassCluster ht hroot Nm mu z hz a ha)
          (nxClassCluster ht hroot Nm mu z hz b hb)
          R hR (z l) (z r)).symm

/--
Generic finite-product reinsertion of the skipped-edge budget.  This is the
algebraic statement behind the factor `R^(2s)` in (5.87), independent of
the later choice of one- and two-variable elimination blocks.
-/
theorem heppChainWeightExcept_le_R_pow_mul_kernelProduct
    {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ)
    (O : Finset (AdjacentIndex m)) (w : Fin m → HeppLeaf t)
    (R : ℝ) (K : AdjacentIndex m → ℝ)
    (hlocal : ∀ j : AdjacentIndex m,
      edgeStatementFactor (decide (j ∈ O))
          (z (w j.1)) (z (w (adjacentSucc j))) ≤
        (if j ∈ O then R ^ 2 else 1) * K j) :
    heppChainWeightExcept z O w ≤
      R ^ (2 * O.card) * ∏ j : AdjacentIndex m, K j := by
  have hpoint (j : AdjacentIndex m) :
      (if j ∈ O then 1
        else latticeEdgeWeight (z (w j.1)) (z (w (adjacentSucc j)))) ≤
          (if j ∈ O then R ^ 2 else 1) * K j := by
    simpa only [edgeStatementFactor, decide_eq_true_eq] using hlocal j
  calc
    heppChainWeightExcept z O w ≤
        ∏ j : AdjacentIndex m,
          ((if j ∈ O then R ^ 2 else 1) * K j) := by
      unfold heppChainWeightExcept
      exact Finset.prod_le_prod
        (fun j _ => by
          split_ifs
          · exact zero_le_one
          · unfold latticeEdgeWeight
            positivity)
        (fun j _ => hpoint j)
    _ = (∏ j : AdjacentIndex m,
          if j ∈ O then R ^ 2 else 1) *
        ∏ j : AdjacentIndex m, K j := by
      rw [Finset.prod_mul_distrib]
    _ = R ^ (2 * O.card) *
        ∏ j : AdjacentIndex m, K j := by
      congr 1
      calc
        (∏ j : AdjacentIndex m,
            if j ∈ O then R ^ 2 else 1) =
            (R ^ 2) ^ O.card := by simp
        _ = R ^ (2 * O.card) := by rw [pow_mul]

/-! ## A concrete kernel product attached to an `(N,X)` word -/

/--
At every adjacency, use the target class's one-variable kernel, except on
the selected set `strongEdges`, where the two-class cutoff of (5.91) is
used.  This definition is pointwise in a leaf word; the later Fubini step
turns its product into nested conditioned copy sums.
-/
noncomputable def nxClassEdgeKernel {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O strongEdges : Finset (AdjacentIndex m))
    (cls : Fin m → ActiveNXClass Nm mu)
    (w : Fin m → HeppLeaf t) (j : AdjacentIndex m) : ℝ :=
  let a := cls j.1
  let b := cls (adjacentSucc j)
  if j ∈ strongEdges then
    strongLambda
      (nxClassCluster ht hroot Nm mu z hz a.1 a.2)
      (nxClassCluster ht hroot Nm mu z hz b.1 b.2)
      R (decide (j ∈ O)) (z (w j.1)) (z (w (adjacentSucc j)))
  else
    (nxClassCluster ht hroot Nm mu z hz b.1 b.2).lambda
      R (decide (j ∈ O)) (z (w j.1)) (z (w (adjacentSucc j)))

theorem nxClassEdgeKernel_nonneg {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (O strongEdges : Finset (AdjacentIndex m))
    (cls : Fin m → ActiveNXClass Nm mu)
    (w : Fin m → HeppLeaf t) (j : AdjacentIndex m) :
    0 ≤ nxClassEdgeKernel ht hroot Nm mu z hz
      R O strongEdges cls w j := by
  by_cases hstrong : j ∈ strongEdges
  · simp only [nxClassEdgeKernel, hstrong, if_pos, strongLambda]
    split_ifs <;> first | exact sq_nonneg _ | exact le_rfl
  · simp only [nxClassEdgeKernel, hstrong, if_false, lambda]
    split_ifs <;> first | exact sq_nonneg _ | exact le_rfl

/--
Concrete statement-boundary comparison for a fixed leaf word and its
induced active `(N,X)` word.  Equal adjacent leaves are needed only off
`O`, exactly as in the frozen proposition.
-/
theorem heppChainWeightExcept_le_nxClassEdgeKernelProduct
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (hR : R ≠ 0)
    (O strongEdges : Finset (AdjacentIndex m))
    (cls : Fin m → ActiveNXClass Nm mu)
    (w : Fin m → HeppLeaf t)
    (hcls : ∀ i : Fin m, singleScaleSigma1 Nm mu (w i) = (cls i).1)
    (hno : NoAdjacentOutside O w) :
    heppChainWeightExcept z O w ≤
      R ^ (2 * O.card) *
        ∏ j : AdjacentIndex m,
          nxClassEdgeKernel ht hroot Nm mu z hz
            R O strongEdges cls w j := by
  apply heppChainWeightExcept_le_R_pow_mul_kernelProduct
  intro j
  let skipped : Bool := decide (j ∈ O)
  have hneq : skipped = false → w j.1 ≠ w (adjacentSucc j) := by
    intro hs
    apply hno j
    simpa [skipped] using hs
  by_cases hj : j ∈ strongEdges
  · rw [nxClassEdgeKernel]
    simp only [hj, if_true]
    have hlocal :=
      edgeStatementFactor_le_scaled_nxClassStrongLambda
        ht hroot Nm mu z hz R hR skipped hneq
        (cls j.1).2 (cls (adjacentSucc j)).2
        (hcls j.1) (hcls (adjacentSucc j))
    simpa [skipped] using hlocal
  · rw [nxClassEdgeKernel]
    simp only [hj, if_false]
    have hlocal :=
      edgeStatementFactor_le_scaled_nxClassLambda
        ht hroot Nm mu z hz R hR skipped hneq
        (cls (adjacentSucc j)).2 (hcls (adjacentSucc j))
    simpa [skipped] using hlocal

end XYCluster

end

end Anderson4D
