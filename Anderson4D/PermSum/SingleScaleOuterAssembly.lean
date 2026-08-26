import Anderson4D.PermSum.SingleScaleOuterMajority

/-!
# Global assembly of the outer single-scale majority estimate

This file performs only the finite outer assembly which follows the
fixed-`P` estimate (5.82)--(5.86).  The active `P` classes partition the
Hepp leaves exactly, so the fixed-fiber bounds multiply without duplicating
any leaf payoff and their exponential losses add to the total multiplicity.

The `P`-word sequence gain and the final Fubini/reordering step of
Proposition 5.10 belong to later files.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- The unique `P = YN⁴` class attached to a Hepp leaf. -/
def leafPClass {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (l : HeppLeaf t) : ℕ :=
  singleScaleSigma3 (singleScaleSigma2 Nm mu (singleScaleSigma1 Nm mu l))

theorem leafPClass_mem_pCarrier {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (l : HeppLeaf t) :
    leafPClass Nm mu l ∈ pCarrier Nm mu := by
  exact Finset.mem_image_of_mem _
    (Finset.mem_image_of_mem _
      (Finset.mem_image_of_mem _ (Finset.mem_univ l)))

theorem mem_leavesAtP_iff_leafPClass {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (P : ℕ) (l : HeppLeaf t) :
    l ∈ leavesAtP Nm mu P ↔ leafPClass Nm mu l = P := by
  simp [leavesAtP, leafPClass]

/-- Distinct active `P` classes have disjoint exact leaf fibers. -/
theorem leavesAtP_pairwiseDisjoint {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    Set.PairwiseDisjoint (↑(pCarrier Nm mu)) (leavesAtP Nm mu) := by
  intro P hP Q hQ hPQ
  apply Finset.disjoint_left.mpr
  intro l hlP hlQ
  apply hPQ
  exact ((mem_leavesAtP_iff_leafPClass Nm mu P l).mp hlP).symm.trans
    ((mem_leavesAtP_iff_leafPClass Nm mu Q l).mp hlQ)

/-- The active `P` fibers cover every Hepp leaf, with no off-carrier residue. -/
theorem biUnion_leavesAtP_eq_univ {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    (pCarrier Nm mu).biUnion (leavesAtP Nm mu) =
      (Finset.univ : Finset (HeppLeaf t)) := by
  ext l
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  exact ⟨leafPClass Nm mu l, leafPClass_mem_pCarrier Nm mu l,
    (mem_leavesAtP_iff_leafPClass Nm mu _ l).mpr rfl⟩

/-- The full multiplicity ledger is the sum of the exact `P`-fiber ledgers. -/
theorem sum_multiplicityP_eq_totalMultiplicity {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    (∑ P ∈ pCarrier Nm mu, multiplicityP Nm mu P) =
      totalMultiplicity mu := by
  exact (totalMultiplicity_eq_sum_P Nm mu).symm

/--
Products over the exact `P` fibers flatten to one global leaf product.
This is the product-level form of both disjointness and coverage.
-/
theorem leavesAtP_product_eq_global {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (f : HeppLeaf t → ℝ) :
    (∏ P ∈ pCarrier Nm mu, ∏ l ∈ leavesAtP Nm mu P, f l) =
      ∏ l : HeppLeaf t, f l := by
  calc
    (∏ P ∈ pCarrier Nm mu, ∏ l ∈ leavesAtP Nm mu P, f l) =
        ∏ l ∈ (pCarrier Nm mu).biUnion (leavesAtP Nm mu), f l :=
      (Finset.prod_biUnion
        (leavesAtP_pairwiseDisjoint Nm mu)).symm
    _ = ∏ l : HeppLeaf t, f l := by
      rw [biUnion_leavesAtP_eq_univ]

set_option maxHeartbeats 800000 in
/--
The complete fixed-`P` outer refinement: first pass from the `(N,X)`
multinomial to the outer `(N,Y)` multinomial, then apply the majority
estimate (5.82)--(5.86).  The two uniform exponential constants are merged.
-/
theorem fixedP_outerMultinomial_le_originalPayoff :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (_ht : t.isValid = true)
        (_hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (compound : Finset (VPos t)) (P : ℕ),
        (Nat.multinomial (nxAtP Nm mu P)
          (multiplicityNX Nm mu) : ℝ) ≤
          C ^ multiplicityP Nm mu P *
            ∏ l ∈ leavesAtP Nm mu P,
              originalOuterLeafPayoff Nm mu compound l := by
  obtain ⟨C₀, hC₀, houter⟩ := fixedP_multinomial_le_outerNY
  obtain ⟨C₁, hC₁, hmajority⟩ :=
    fixedP_majority_multinomial_le_originalPayoff
  let C : ℝ := C₀ * C₁
  refine ⟨C, by dsimp [C]; nlinarith, ?_⟩
  intro t ht hroot Nm mu compound P
  let M := multiplicityP Nm mu P
  let A : ℝ :=
    Nat.multinomial (nyAtP Nm mu P) (multiplicityNY Nm mu)
  let O := ∏ l ∈ leavesAtP Nm mu P,
    originalOuterLeafPayoff Nm mu compound l
  have ho :
      (Nat.multinomial (nxAtP Nm mu P)
        (multiplicityNX Nm mu) : ℝ) ≤ C₀ ^ M * A := by
    simpa [M, A] using houter Nm mu P
  have hm : A ≤ C₁ ^ M * O := by
    simpa [M, A, O] using hmajority ht hroot Nm mu compound P
  calc
    (Nat.multinomial (nxAtP Nm mu P)
        (multiplicityNX Nm mu) : ℝ) ≤ C₀ ^ M * A := ho
    _ ≤ C₀ ^ M * (C₁ ^ M * O) :=
      mul_le_mul_of_nonneg_left hm
        (pow_nonneg (zero_le_one.trans hC₀) _)
    _ = C ^ M * O := by
      dsimp [C]
      rw [mul_pow]
      ring

set_option maxHeartbeats 800000 in
/--
Global outer refinement bound obtained by multiplying the completed
fixed-`P` majority estimate over `pCarrier`.  The constant is uniform, its
exponent is exactly the total word length, and every original leaf payoff
occurs exactly once.
-/
theorem globalOuterMajorityRefinement :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (_ht : t.isValid = true)
        (_hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (compound : Finset (VPos t)),
        (∏ P ∈ pCarrier Nm mu,
          (Nat.multinomial (nxAtP Nm mu P)
            (multiplicityNX Nm mu) : ℝ)) ≤
          C ^ totalMultiplicity mu *
            ∏ l : HeppLeaf t,
              originalOuterLeafPayoff Nm mu compound l := by
  obtain ⟨C, hC, hfixed⟩ :=
    fixedP_outerMultinomial_le_originalPayoff
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu compound
  calc
    (∏ P ∈ pCarrier Nm mu,
        (Nat.multinomial (nxAtP Nm mu P)
          (multiplicityNX Nm mu) : ℝ)) ≤
        ∏ P ∈ pCarrier Nm mu,
          (C ^ multiplicityP Nm mu P *
            ∏ l ∈ leavesAtP Nm mu P,
              originalOuterLeafPayoff Nm mu compound l) := by
      apply Finset.prod_le_prod
      · intro P hP
        positivity
      · intro P hP
        exact hfixed ht hroot Nm mu compound P
    _ =
        (∏ P ∈ pCarrier Nm mu, C ^ multiplicityP Nm mu P) *
          ∏ P ∈ pCarrier Nm mu,
            ∏ l ∈ leavesAtP Nm mu P,
              originalOuterLeafPayoff Nm mu compound l := by
      rw [Finset.prod_mul_distrib]
    _ =
        C ^ (∑ P ∈ pCarrier Nm mu, multiplicityP Nm mu P) *
          ∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l := by
      rw [Finset.prod_pow_eq_pow_sum,
        leavesAtP_product_eq_global]
    _ =
        C ^ totalMultiplicity mu *
          ∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l := by
      rw [sum_multiplicityP_eq_totalMultiplicity]

end

end Anderson4D
