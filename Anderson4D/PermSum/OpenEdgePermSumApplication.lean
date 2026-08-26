import Anderson4D.PermSum.OpenEdgeMultiplicity
import Anderson4D.PermSum.Main

/-!
# Proposition 5.7 on a fixed one-open-edge word fibre

The dummy-closed pairing supplies a genuine primitive augmented word.
The exact multiplicity package from `OpenEdgeMultiplicity` supplies the
evenness, total order, and valid-word hypotheses of Proposition 5.7.
This file performs that application without summing over an arbitrary
marker family.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open PlaneTree
open scoped BigOperators

/-- One nonnegative primitive word summand is bounded by the complete
paper factorial ledger over its valid-word fibre. -/
theorem primitiveChainWeight_le_paperSum_of_mem
    {t : PlaneTree} {q : ℕ}
    (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin q → HeppLeaf t)
    (hw : w ∈ validWords (leafMultiplicity mu)) :
    primitiveChainWeight (m := q) z w ≤
      paperSum (M := q) (leafMultiplicity mu)
        (primitiveChainWeight (m := q) z) := by
  have hsingle :
      primitiveChainWeight (m := q) z w ≤
        wordSum (leafMultiplicity mu)
          (primitiveChainWeight (m := q) z) := by
    unfold wordSum
    exact
      Finset.single_le_sum
        (fun u _hu => primitiveChainWeight_nonneg z u)
        hw
  have hwordNonneg :
      0 ≤ wordSum (leafMultiplicity mu)
        (primitiveChainWeight (m := q) z) := by
    unfold wordSum
    exact Finset.sum_nonneg fun u _hu =>
      primitiveChainWeight_nonneg z u
  have hledger :
      1 ≤ ∏ l : HeppLeaf t,
        (((leafMultiplicity mu l).factorial : ℕ) : ℝ) := by
    apply Finset.one_le_prod
    intro l _hl
    exact_mod_cast (Nat.factorial_pos
      (leafMultiplicity mu l))
  calc
    primitiveChainWeight (m := q) z w ≤
        wordSum (leafMultiplicity mu)
          (primitiveChainWeight (m := q) z) := hsingle
    _ = 1 * wordSum (leafMultiplicity mu)
          (primitiveChainWeight (m := q) z) := by ring
    _ ≤
        (∏ l : HeppLeaf t,
          (((leafMultiplicity mu l).factorial : ℕ) : ℝ)) *
          wordSum (leafMultiplicity mu)
            (primitiveChainWeight (m := q) z) :=
      mul_le_mul_of_nonneg_right hledger hwordNonneg
    _ = paperSum (M := q) (leafMultiplicity mu)
          (primitiveChainWeight (m := q) z) := by
      rfl

/-- A fixed genuine open edge, after dummy closure, is controlled by the
literal Proposition 5.7 right-hand side for its packaged augmented
multiplicity profile. -/
theorem openEdgeAugmented_chain_le_permSumRHS
    {C : ℝ} (hperm : PermSumEstimate C)
    {t : PlaneTree} {m M : ℕ}
    (mu : Multiplicities t)
    (w : Fin m → HeppLeaf t)
    (hw : w ∈ validWords (leafMultiplicity mu))
    (κ : PartialPairing (Fin m))
    (a b : Fin m) (hm : 0 < m)
    (hκab : κ a = b) (hab : a < b)
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i))
    (Nm : HeppMarking t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hadm : IsAdmissible Nm M z) :
    ∃ n : ℕ, 2 ≤ n ∧
      heppChainWeight z
          (openEdgeAugmentedWord w a b) ≤
        permSumRHS C n t Nm
          (openEdgeAugmentedMultiplicities
            mu w hw a b) := by
  let mu' :=
    openEdgeAugmentedMultiplicities mu w hw a b
  obtain ⟨n, hn, htotal, heven, hvalid⟩ :=
    exists_openEdgeAugmentedPermSumMultiplicityData
      mu w hw κ a b hm hκab (ne_of_lt hab)
      hfull hrespect
  change totalMultiplicity mu' = 2 * n at htotal
  change ∀ l : HeppLeaf t,
    Even (leafMultiplicity mu' l) at heven
  change openEdgeAugmentedWord w a b ∈
    validWords (leafMultiplicity mu') at hvalid
  have hlen : m + 2 = 2 * n := by
    rw [← htotal]
    exact
      (totalMultiplicity_openEdgeAugmentedMultiplicities
        mu w hw a b).symm
  have hnp :
      NoProperLeafBlock
        (openEdgeAugmentedWord w a b) :=
    noProperLeafBlock_openEdgeAugmentedWord
      κ a b hκab hab hfull hprimitive w hrespect
  have hsingle :
      heppChainWeight z
          (openEdgeAugmentedWord w a b) ≤
        paperSum (M := m + 2) (leafMultiplicity mu')
          (primitiveChainWeight (m := m + 2) z) := by
    calc
      heppChainWeight z
          (openEdgeAugmentedWord w a b) =
          primitiveChainWeight z
            (openEdgeAugmentedWord w a b) := by
        simp [primitiveChainWeight, hnp]
      _ ≤ paperSum (M := m + 2) (leafMultiplicity mu')
            (primitiveChainWeight (m := m + 2) z) := by
        exact primitiveChainWeight_le_paperSum_of_mem
          mu' z (openEdgeAugmentedWord w a b) hvalid
  have hbound :
      paperSum (M := 2 * n) (leafMultiplicity mu')
          (primitiveChainWeight (m := 2 * n) z) ≤
        permSumRHS C n t Nm mu' :=
    hperm.2 n M t Nm mu' z hn ht hroot
      htotal heven hadm
  rw [← hlen] at hbound
  exact ⟨n, hn, hsingle.trans hbound⟩

end

end Anderson4D
