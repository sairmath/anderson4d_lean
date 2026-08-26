import Anderson4D.PermSum.CollapseOffMarker
import Anderson4D.PermSum.MergeFactorial
import Anderson4D.PermSum.MergeInductiveInput

/-!
# Tree-facing factorial comparison after run compression

This module specializes the numerical factorial estimate (5.37) to the
original and run-compressed multiplicities of one primitive valid Hepp-leaf
word.  In particular, it discharges the coordinatewise, total-mass, and
skipped-branch hypotheses needed by `mergeFactorialBefore_le_four_pow`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- Run compression cannot increase the multiplicity of any leaf in a word
with the prescribed original multiplicities. -/
theorem mergedMultiplicity_le_leafMultiplicity_of_valid
    {t : PlaneTree} {M : ℕ}
    (mu : Multiplicities t)
    (w : Fin M → HeppLeaf t)
    (hvalid : w ∈ validWords (leafMultiplicity mu))
    (l : HeppLeaf t) :
    mergedMultiplicity w l ≤ leafMultiplicity mu l := by
  letI : BEq (HeppLeaf t) := instBEqOfDecidableEq
  have hcount :
      (Finset.univ.filter fun i => w i = l).card =
        leafMultiplicity mu l :=
    (Finset.mem_filter.mp hvalid).2 l
  calc
    mergedMultiplicity w l ≤ (List.ofFn w).count l :=
      mergedMultiplicity_le_originalCount w l
    _ = (Finset.univ.filter fun i => w i = l).card :=
      count_ofFn w l
    _ = leafMultiplicity mu l := hcount

/-- A subset of non-root branches is paid for by the total run-compressed
multiplicity.  The off-marker branch/leaf count uses the lower bound two
built into `mergedMultiplicities`. -/
theorem two_mul_card_le_mergedWordList_length
    {t : PlaneTree} {M : ℕ}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (w : Fin M → HeppLeaf t)
    (hvalid : w ∈ validWords (leafMultiplicity mu))
    (hprimitive : NoProperLeafBlock w)
    (W : Finset (VPos t))
    (hW : W ⊆ nonrootBranches t) :
    2 * W.card ≤ (mergedWordList w).length := by
  let mu' : Multiplicities t :=
    mergedMultiplicities hroot mu w hvalid hprimitive
  have hleafCard : 0 < Fintype.card (HeppLeaf t) := by
    rw [Fintype.card_coe, card_Leaves_eq_leafCount]
    exact lt_of_lt_of_le (by omega)
      (two_le_leafCount_of_root_mem_BranchNodes t hroot)
  let marker : HeppLeaf t :=
    Classical.choice (Fintype.card_pos_iff.mp hleafCard)
  have hoff :
      2 * W.card ≤
        ∑ l ∈
          (Finset.univ : Finset (HeppLeaf t)).erase marker,
          leafMultiplicity mu' l :=
    two_mul_card_le_sum_leafMultiplicity_erase_of_subset_nonrootBranches
      ht hroot mu' marker W hW
  have hsum :
      (∑ l ∈
          (Finset.univ : Finset (HeppLeaf t)).erase marker,
          leafMultiplicity mu' l) +
        leafMultiplicity mu' marker =
      totalMultiplicity mu' := by
    unfold totalMultiplicity
    simpa using
      (Finset.sum_erase_add
        (s := (Finset.univ : Finset (HeppLeaf t)))
        (f := fun l => leafMultiplicity mu' l)
        (Finset.mem_univ marker))
  calc
    2 * W.card ≤
        ∑ l ∈
          (Finset.univ : Finset (HeppLeaf t)).erase marker,
          leafMultiplicity mu' l := hoff
    _ ≤ totalMultiplicity mu' := by omega
    _ = (mergedWordList w).length :=
      totalMultiplicity_mergedMultiplicities
        hroot mu w hvalid hprimitive

/-- Tree-facing form of paper (5.37).

The left side is exactly the compressed P-5.9 factorial/leaf factor,
multiplied by the factorial-ledger ratios that recover the original
multiplicities.  The right side is the P-5.7 factorial/leaf factor with the
explicit uniform loss `4^n`. -/
theorem merged_factorial_leaf_product_le_four_pow
    {t : PlaneTree} {M n : ℕ}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (w : Fin M → HeppLeaf t)
    (hvalid : w ∈ validWords (leafMultiplicity mu))
    (hprimitive : NoProperLeafBlock w)
    (htotal : totalMultiplicity mu = 2 * n)
    (W : Finset (VPos t))
    (hW : W ⊆ nonrootBranches t) :
    sqrtFactorial
          ((mergedWordList w).length - 2 * W.card) *
        (∏ l : HeppLeaf t,
          sqrtFactorial
            (leafMultiplicity
              (mergedMultiplicities
                hroot mu w hvalid hprimitive) l)) *
        (∏ l : HeppLeaf t,
          ((leafMultiplicity mu l).factorial : ℝ) /
            ((leafMultiplicity
              (mergedMultiplicities
                hroot mu w hvalid hprimitive) l).factorial : ℝ)) ≤
      (4 : ℝ) ^ n * ((n - W.card).factorial : ℝ) *
        ∏ l : HeppLeaf t,
          sqrtFactorial (leafMultiplicity mu l) := by
  let mu' : Multiplicities t :=
    mergedMultiplicities hroot mu w hvalid hprimitive
  have hsub :
      ∀ l ∈ (Finset.univ : Finset (HeppLeaf t)),
        leafMultiplicity mu' l ≤ leafMultiplicity mu l := by
    intro l _hl
    dsimp only [mu']
    rw [leafMultiplicity_mergedMultiplicities]
    exact mergedMultiplicity_le_leafMultiplicity_of_valid
      mu w hvalid l
  have hml :
      (∑ l ∈ (Finset.univ : Finset (HeppLeaf t)),
        leafMultiplicity mu l) = 2 * n := by
    simpa [totalMultiplicity] using htotal
  have hsl :
      (∑ l ∈ (Finset.univ : Finset (HeppLeaf t)),
        leafMultiplicity mu' l) =
        (mergedWordList w).length := by
    calc
      (∑ l ∈ (Finset.univ : Finset (HeppLeaf t)),
          leafMultiplicity mu' l) =
          totalMultiplicity mu' := by
        simp [totalMultiplicity]
      _ = (mergedWordList w).length := by
        simpa [mu'] using
          (totalMultiplicity_mergedMultiplicities
            hroot mu w hvalid hprimitive)
  have hw :
      2 * W.card ≤ (mergedWordList w).length :=
    two_mul_card_le_mergedWordList_length
      ht hroot mu w hvalid hprimitive W hW
  have hfactorial :=
    mergeFactorialBefore_le_four_pow
      (Finset.univ : Finset (HeppLeaf t))
      (leafMultiplicity mu) (leafMultiplicity mu')
      hsub n (mergedWordList w).length W.card hml hsl hw
  simpa [mergeFactorialBefore, mergeFactorialAfter, mu', mul_assoc] using
    hfactorial

end

end Anderson4D
