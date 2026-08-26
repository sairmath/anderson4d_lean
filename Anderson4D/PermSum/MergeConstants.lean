import Anderson4D.HeppTree.BranchExcess
import Anderson4D.HeppTree.LeafCard
import Anderson4D.PermSum.MergeScaleLedger

/-!
# Final constant absorption for Proposition 5.7

This file closes the scalar ledger after the run-compression and
all-simple-leaf reductions.  Leaf multiplicities pay for the number of
branch vertices, while one explicit exponential base absorbs the compressed
word length, the tree factor, and the uniform merge loss.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- A valid tree with total leaf multiplicity `2n` has at most `n`
branch vertices.  This is the tree-count input to the final constant
absorption in Proposition 5.7. -/
theorem card_branchNodes_le_of_totalMultiplicity_eq_two_mul
    {t : PlaneTree} (ht : t.isValid = true)
    (_hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (n : ℕ)
    (htotal : totalMultiplicity mu = 2 * n) :
    (BranchNodes t).card ≤ n := by
  have hbranch :
      (BranchNodes t).card ≤ branchExcess t := by
    rw [← sum_branchNodes_childCount_sub_one_eq_branchExcess,
      Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun v hv => by
      have htwo : 2 ≤ childCount t v.1 := by
        simpa [BranchNodes] using hv
      omega
  have hleaf :
      2 * t.leafCount ≤ totalMultiplicity mu := by
    have hcard :
        Fintype.card (HeppLeaf t) = t.leafCount := by
      rw [Fintype.card_coe, card_Leaves_eq_leafCount]
    rw [← hcard, totalMultiplicity]
    calc
      2 * Fintype.card (HeppLeaf t) =
          ∑ _l : HeppLeaf t, 2 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ l : HeppLeaf t, leafMultiplicity mu l := by
        exact Finset.sum_le_sum fun l _ => mu.two_le l.1 l.2
  calc
    (BranchNodes t).card ≤ branchExcess t := hbranch
    _ = t.leafCount - 1 :=
      branchExcess_eq_leafCount_sub_one t ht
    _ ≤ t.leafCount := Nat.sub_le _ _
    _ ≤ n := by omega

/-- One explicit final base.  The factor `64` simultaneously covers either
the `16^n` merge-pattern ledger or the coarser `64^n` version. -/
def mergeGlobalConstant (C0 D : ℝ) : ℝ :=
  max 1 (C0 ^ (2 : ℕ) * D * 64)

/-- The chosen final base is at least one. -/
theorem one_le_mergeGlobalConstant (C0 D : ℝ) :
    1 ≤ mergeGlobalConstant C0 D := by
  exact le_max_left _ _

/-- Scalar constant absorption.  The hypotheses `m ≤ 2n` and `b ≤ n`
are respectively the compressed-word and branch-count ledgers.  Any
nonnegative loss base up to `64` is absorbed. -/
theorem mergeGlobalConstant_absorbs
    (C0 D K : ℝ) (hC0 : 1000 < C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ)))
    (hK0 : 0 ≤ K) (hK64 : K ≤ 64)
    (n m b : ℕ) (hm : m ≤ 2 * n) (hb : b ≤ n) :
    C0 ^ m * D ^ b * K ^ n ≤
      mergeGlobalConstant C0 D ^ n := by
  have hC0one : 1 ≤ C0 := by linarith
  have hC0nonneg : 0 ≤ C0 := le_trans (by norm_num) hC0one
  have hDone : 1 ≤ D := by
    rw [hD]
    exact Real.one_le_exp (by positivity)
  have hDnonneg : 0 ≤ D := le_trans (by norm_num) hDone
  have hC0pow :
      C0 ^ m ≤ C0 ^ (2 * n) :=
    pow_le_pow_right₀ hC0one hm
  have hDpow :
      D ^ b ≤ D ^ n :=
    pow_le_pow_right₀ hDone hb
  have hKpow :
      K ^ n ≤ (64 : ℝ) ^ n :=
    pow_le_pow_left₀ hK0 hK64 n
  calc
    C0 ^ m * D ^ b * K ^ n ≤
        C0 ^ (2 * n) * D ^ n * (64 : ℝ) ^ n := by
      gcongr
    _ = (C0 ^ (2 : ℕ) * D * 64) ^ n := by
      simp only [mul_pow, pow_mul]
    _ ≤ mergeGlobalConstant C0 D ^ n := by
      apply pow_le_pow_left₀
      · positivity
      · exact le_max_right _ _

/-- The coarser `64^n` ledger is directly absorbed. -/
theorem mergeGlobalConstant_absorbs_sixtyFour
    (C0 D : ℝ) (hC0 : 1000 < C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ)))
    (n m b : ℕ) (hm : m ≤ 2 * n) (hb : b ≤ n) :
    C0 ^ m * D ^ b * (64 : ℝ) ^ n ≤
      mergeGlobalConstant C0 D ^ n := by
  exact mergeGlobalConstant_absorbs C0 D 64 hC0 hD
    (by norm_num) (by norm_num) n m b hm hb

/-- Tree-facing form of the final scalar ledger.  The tree hypotheses and
`totalMultiplicity = 2n` discharge the branch exponent automatically. -/
theorem mergeGlobalConstant_absorbs_tree
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (C0 D K : ℝ) (hC0 : 1000 < C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ)))
    (hK0 : 0 ≤ K) (hK64 : K ≤ 64)
    (n m : ℕ) (htotal : totalMultiplicity mu = 2 * n)
    (hm : m ≤ 2 * n) :
    C0 ^ m * D ^ (BranchNodes t).card * K ^ n ≤
      mergeGlobalConstant C0 D ^ n := by
  exact mergeGlobalConstant_absorbs C0 D K hC0 hD hK0 hK64
    n m (BranchNodes t).card hm
    (card_branchNodes_le_of_totalMultiplicity_eq_two_mul
      ht hroot mu n htotal)

/-- Tree-facing specialization with the full `64^n` loss budget. -/
theorem mergeGlobalConstant_absorbs_tree_sixtyFour
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (C0 D : ℝ) (hC0 : 1000 < C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ)))
    (n m : ℕ) (htotal : totalMultiplicity mu = 2 * n)
    (hm : m ≤ 2 * n) :
    C0 ^ m * D ^ (BranchNodes t).card * (64 : ℝ) ^ n ≤
      mergeGlobalConstant C0 D ^ n := by
  exact mergeGlobalConstant_absorbs_tree ht hroot mu C0 D 64 hC0 hD
    (by norm_num) (by norm_num) n m htotal hm

end

end Anderson4D
