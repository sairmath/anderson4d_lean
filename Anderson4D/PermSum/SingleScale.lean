import Anderson4D.PermSum.SingleScaleFiberPostprocess
import Anderson4D.PermSum.SingleScaleReferenceWord
import Anderson4D.PermSum.SingleScaleConstants

/-!
# The single-scale permutation estimate

This module closes Proposition 5.10.  The proof keeps the completed
base-scale coefficient common across the full finite Fubini sum, consumes
the outer payoff exactly once, and only then converts the distinguished
leaf power to the branch-scale ledger.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-- The single exponential base left after the inner, outer, occurrence,
position, and reverse-power ledgers have all been combined. -/
def singleScaleFinalExponentialBase
    (Cfiber Couter : ℝ) : ℝ :=
  finAnchorNXFiberSharpBase Cfiber * Couter *
    (8 * Real.exp 4) ^ 5

theorem singleScaleFinalExponentialBase_nonneg
    (Cfiber Couter : ℝ)
    (hCfiber : 0 ≤ Cfiber) (hCouter : 0 ≤ Couter) :
    0 ≤ singleScaleFinalExponentialBase Cfiber Couter := by
  unfold singleScaleFinalExponentialBase
  exact mul_nonneg
    (mul_nonneg
      (finAnchorNXFiberSharpBase_nonneg Cfiber hCfiber)
      hCouter)
    (pow_nonneg (by positivity) 5)

set_option maxHeartbeats 2000000 in
/-- The main single-scale permutation-sum theorem. -/
theorem singleScale_estimate :
    ∃ C0 : ℝ, SingleScaleEstimate C0 := by
  obtain ⟨Cfiber, hCfiberLarge, hfixed⟩ :=
    fixedFiber_singleScaleChainWeight_le_sharpOccurrence
  obtain ⟨Couter, hCouterOne, houter⟩ :=
    global_refinement_orientedWeight_total_le_originalPayoff
  have hCfiber : 0 ≤ Cfiber := by linarith
  have hCouter : 0 ≤ Couter :=
    le_trans zero_le_one hCouterOne
  let B : ℝ :=
    singleScaleFinalExponentialBase Cfiber Couter
  have hB : 0 ≤ B := by
    exact singleScaleFinalExponentialBase_nonneg
      Cfiber Couter hCfiber hCouter
  obtain ⟨C0, hC0, hBdom⟩ :=
    exists_large_halfPower_dominates_natPower B hB
  refine ⟨C0, ?_⟩
  unfold SingleScaleEstimate
  refine ⟨hC0, ?_⟩
  intro m s R t Nm mu compound z O
    ht hroot _hcompound hm hz hscale hRdyadic hRbound hs
  subst m
  subst s
  rcases hRdyadic with ⟨k, hk⟩
  subst R
  have hRpos : 0 < 2 ^ k := by positivity
  let anchor :
      (Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) →
        Fin (totalMultiplicity mu) :=
    fun x => totalMultiplicityNXScaleAnchor Nm mu x
  let xref : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu :=
    referenceNXWord Nm mu
  let completed : ℝ :=
    nxWordBaseScaleFactor xref *
      ((xref (anchor xref)).1.1 : ℝ) ^ 2
  let weight :
      (Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) → ℝ :=
    fun x =>
      finAnchorNXOrientedActivePWeight Nm mu
        false false (totalMultiplicity mu) (anchor x) x O
  let commonPrefix : ℝ :=
    finAnchorNXFiberSharpBase Cfiber ^ totalMultiplicity mu *
      sqrtFactorial
        (totalMultiplicity mu - O.card) *
      (∏ l : HeppLeaf t,
        sqrtFactorial (leafMultiplicity mu l)) *
      completed *
      ((2 ^ k : ℕ) : ℝ) ^ (2 * O.card) *
      (((scaleN Nm (rootV t) : ℝ) /
        ((2 ^ k : ℕ) : ℝ)) ^ min (2 * O.card) 3)
  have hxref :
      xref ∈ validWords (M := totalMultiplicity mu)
        (activeNXMultiplicity Nm mu) := by
    exact referenceNXWord_mem_validWords Nm mu
  have hprefix : 0 ≤ commonPrefix := by
    have hsharp :
        0 ≤ finAnchorNXFiberSharpBase Cfiber ^
          totalMultiplicity mu :=
      pow_nonneg
        (finAnchorNXFiberSharpBase_nonneg Cfiber hCfiber) _
    have hsqrt :
        0 ≤ sqrtFactorial
          (totalMultiplicity mu - O.card) := by
      unfold sqrtFactorial
      positivity
    have hglobalSqrt :
        0 ≤ ∏ l : HeppLeaf t,
          sqrtFactorial (leafMultiplicity mu l) := by
      apply Finset.prod_nonneg
      intro l _hl
      unfold sqrtFactorial
      positivity
    have hcompleted0 : 0 ≤ completed := by
      dsimp only [completed]
      unfold nxWordBaseScaleFactor
      positivity
    have hRpow :
        0 ≤ (((2 ^ k : ℕ) : ℝ) ^ (2 * O.card)) :=
      pow_nonneg (by positivity) _
    have hrootGain :
        0 ≤ (((scaleN Nm (rootV t) : ℝ) /
          ((2 ^ k : ℕ) : ℝ)) ^ min (2 * O.card) 3) :=
      pow_nonneg (by positivity) _
    dsimp only [commonPrefix]
    positivity
  have hinner :
      (∑ y ∈ validWords (M := totalMultiplicity mu)
          (activePMultiplicity Nm mu),
        ∑ x ∈ validRefinements
            (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
          ∑ sigma ∈ arrangementsAtNXWord Nm mu x,
            singleScaleChainWeight z O
              (inducedWord (leafMultiplicity mu) sigma)) ≤
        commonPrefix *
          ∑ y ∈ validWords (M := totalMultiplicity mu)
              (activePMultiplicity Nm mu),
            ∑ x ∈ validRefinements
                (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
              weight x := by
    calc
      (∑ y ∈ validWords (M := totalMultiplicity mu)
          (activePMultiplicity Nm mu),
        ∑ x ∈ validRefinements
            (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
          ∑ sigma ∈ arrangementsAtNXWord Nm mu x,
            singleScaleChainWeight z O
              (inducedWord (leafMultiplicity mu) sigma)) ≤
          ∑ y ∈ validWords (M := totalMultiplicity mu)
              (activePMultiplicity Nm mu),
            ∑ x ∈ validRefinements
                (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
              commonPrefix * weight x := by
        apply Finset.sum_le_sum
        intro y _hy
        apply Finset.sum_le_sum
        intro x hx
        have hxvalid :
            x ∈ validWords (M := totalMultiplicity mu)
              (activeNXMultiplicity Nm mu) :=
          (Finset.mem_filter.mp hx).1
        have hfiber :=
          hfixed ht hroot Nm mu z hz (2 ^ k) hRpos hRbound
            O.card O rfl x hxvalid
        have hcompleted :
            nxWordBaseScaleFactor x *
                ((x (anchor x)).1.1 : ℝ) ^ 2 =
              completed := by
          dsimp only [completed, xref, anchor]
          exact completedNXWordBaseScaleFactor_eq_of_valid
            Nm mu x (referenceNXWord Nm mu)
            hxvalid (referenceNXWord_mem_validWords Nm mu)
        calc
          (∑ sigma ∈ arrangementsAtNXWord Nm mu x,
              singleScaleChainWeight z O
                (inducedWord (leafMultiplicity mu) sigma)) ≤
            finAnchorNXFiberSharpBase Cfiber ^
                totalMultiplicity mu *
              sqrtFactorial
                (totalMultiplicity mu - O.card) *
              (∏ l : HeppLeaf t,
                sqrtFactorial (leafMultiplicity mu l)) *
              nxWordBaseScaleFactor x *
              ((x (anchor x)).1.1 : ℝ) ^ 2 *
              (((2 ^ k : ℕ) : ℝ) ^ (2 * O.card)) *
              (((scaleN Nm (rootV t) : ℝ) /
                ((2 ^ k : ℕ) : ℝ)) ^
                  min (2 * O.card) 3) *
              weight x := by
            simpa only [anchor, weight] using hfiber
          _ = commonPrefix * weight x := by
            calc
              finAnchorNXFiberSharpBase Cfiber ^
                    totalMultiplicity mu *
                  sqrtFactorial
                    (totalMultiplicity mu - O.card) *
                  (∏ l : HeppLeaf t,
                    sqrtFactorial (leafMultiplicity mu l)) *
                  nxWordBaseScaleFactor x *
                  ((x (anchor x)).1.1 : ℝ) ^ 2 *
                  (((2 ^ k : ℕ) : ℝ) ^ (2 * O.card)) *
                  (((scaleN Nm (rootV t) : ℝ) /
                    ((2 ^ k : ℕ) : ℝ)) ^
                      min (2 * O.card) 3) *
                  weight x =
                (finAnchorNXFiberSharpBase Cfiber ^
                    totalMultiplicity mu *
                  sqrtFactorial
                    (totalMultiplicity mu - O.card) *
                  (∏ l : HeppLeaf t,
                    sqrtFactorial (leafMultiplicity mu l)) *
                  (((2 ^ k : ℕ) : ℝ) ^ (2 * O.card)) *
                  (((scaleN Nm (rootV t) : ℝ) /
                    ((2 ^ k : ℕ) : ℝ)) ^
                      min (2 * O.card) 3)) *
                  (nxWordBaseScaleFactor x *
                    ((x (anchor x)).1.1 : ℝ) ^ 2) *
                  weight x := by ring
              _ =
                (finAnchorNXFiberSharpBase Cfiber ^
                    totalMultiplicity mu *
                  sqrtFactorial
                    (totalMultiplicity mu - O.card) *
                  (∏ l : HeppLeaf t,
                    sqrtFactorial (leafMultiplicity mu l)) *
                  (((2 ^ k : ℕ) : ℝ) ^ (2 * O.card)) *
                  (((scaleN Nm (rootV t) : ℝ) /
                    ((2 ^ k : ℕ) : ℝ)) ^
                      min (2 * O.card) 3)) *
                  completed * weight x := by
                rw [hcompleted]
              _ = commonPrefix * weight x := by
                dsimp only [commonPrefix]
                ring
      _ = commonPrefix *
          ∑ y ∈ validWords (M := totalMultiplicity mu)
              (activePMultiplicity Nm mu),
            ∑ x ∈ validRefinements
                (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
              weight x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Finset.mul_sum]
  have houterBound :
      (∑ y ∈ validWords (M := totalMultiplicity mu)
          (activePMultiplicity Nm mu),
        ∑ x ∈ validRefinements
            (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
          weight x) ≤
        Couter ^ totalMultiplicity mu *
          ∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l := by
    simpa only [weight, anchor] using
      houter ht hroot Nm mu compound anchor O
  have houterCombined :
      (∑ y ∈ validWords (M := totalMultiplicity mu)
          (activePMultiplicity Nm mu),
        ∑ x ∈ validRefinements
            (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
          ∑ sigma ∈ arrangementsAtNXWord Nm mu x,
            singleScaleChainWeight z O
              (inducedWord (leafMultiplicity mu) sigma)) ≤
        commonPrefix *
          (Couter ^ totalMultiplicity mu *
            ∏ l : HeppLeaf t,
              originalOuterLeafPayoff Nm mu compound l) :=
    hinner.trans
      (mul_le_mul_of_nonneg_left houterBound hprefix)
  have hcompletedLedger :
      (∏ l : HeppLeaf t,
          sqrtFactorial (leafMultiplicity mu l)) *
          completed *
          (∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l) ≤
        (∏ l ∈ simpleLeaves t compound,
          sqrtFactorial (mu.m l)) *
        (∏ l ∈ compoundLeaves t compound,
          factorialThreeQuarters (mu.m l)) *
        (8 * Real.exp 4) ^ (5 * totalMultiplicity mu) *
        singleScaleBranchPower Nm mu compound *
        ∏ v ∈ nonrootBranches t,
          (parentScaleRatio Nm v) ^ 3 := by
    have h :=
      completedNXWordScalar_mul_outerPayoff_le_branchRatioLedger
        ht hroot Nm mu compound
        (totalMultiplicityNXScaleAnchor Nm mu
          (referenceNXWord Nm mu))
        (referenceNXWord Nm mu)
        (referenceNXWord_mem_validWords Nm mu) hscale
    dsimp only [completed, xref, anchor]
    simpa only [mul_assoc] using h
  let scalar : ℝ :=
    finAnchorNXFiberSharpBase Cfiber ^ totalMultiplicity mu *
      Couter ^ totalMultiplicity mu *
      sqrtFactorial (totalMultiplicity mu - O.card) *
      (((2 ^ k : ℕ) : ℝ) ^ (2 * O.card)) *
      (((scaleN Nm (rootV t) : ℝ) /
        ((2 ^ k : ℕ) : ℝ)) ^ min (2 * O.card) 3)
  have hscalar : 0 ≤ scalar := by
    have hsharp :
        0 ≤ finAnchorNXFiberSharpBase Cfiber ^
          totalMultiplicity mu :=
      pow_nonneg
        (finAnchorNXFiberSharpBase_nonneg Cfiber hCfiber) _
    have houterPower :
        0 ≤ Couter ^ totalMultiplicity mu :=
      pow_nonneg hCouter _
    have hsqrt :
        0 ≤ sqrtFactorial
          (totalMultiplicity mu - O.card) := by
      unfold sqrtFactorial
      positivity
    have hRpow :
        0 ≤ (((2 ^ k : ℕ) : ℝ) ^ (2 * O.card)) :=
      pow_nonneg (by positivity) _
    have hrootGain :
        0 ≤ (((scaleN Nm (rootV t) : ℝ) /
          ((2 ^ k : ℕ) : ℝ)) ^ min (2 * O.card) 3) :=
      pow_nonneg (by positivity) _
    dsimp only [scalar]
    positivity
  have hledgerCombined :
      commonPrefix *
          (Couter ^ totalMultiplicity mu *
            ∏ l : HeppLeaf t,
              originalOuterLeafPayoff Nm mu compound l) ≤
        scalar *
          ((∏ l ∈ simpleLeaves t compound,
            sqrtFactorial (mu.m l)) *
          (∏ l ∈ compoundLeaves t compound,
            factorialThreeQuarters (mu.m l)) *
          (8 * Real.exp 4) ^ (5 * totalMultiplicity mu) *
          singleScaleBranchPower Nm mu compound *
          ∏ v ∈ nonrootBranches t,
            (parentScaleRatio Nm v) ^ 3) := by
    calc
      commonPrefix *
          (Couter ^ totalMultiplicity mu *
            ∏ l : HeppLeaf t,
              originalOuterLeafPayoff Nm mu compound l) =
        scalar *
          ((∏ l : HeppLeaf t,
            sqrtFactorial (leafMultiplicity mu l)) *
            completed *
            (∏ l : HeppLeaf t,
              originalOuterLeafPayoff Nm mu compound l)) := by
        dsimp only [commonPrefix, scalar]
        ring
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left hcompletedLedger hscalar
  let tail : ℝ :=
    sqrtFactorial (totalMultiplicity mu - O.card) *
      (∏ l ∈ simpleLeaves t compound,
        sqrtFactorial (mu.m l)) *
      (∏ l ∈ compoundLeaves t compound,
        factorialThreeQuarters (mu.m l)) *
      singleScaleBranchPower Nm mu compound *
      (((2 ^ k : ℕ) : ℝ) ^ (2 * O.card)) *
      (∏ v ∈ nonrootBranches t,
        (parentScaleRatio Nm v) ^ 3) *
      (((scaleN Nm (rootV t) : ℝ) /
        ((2 ^ k : ℕ) : ℝ)) ^ min (2 * O.card) 3)
  have htail : 0 ≤ tail := by
    have hsqrt :
        0 ≤ sqrtFactorial
          (totalMultiplicity mu - O.card) := by
      unfold sqrtFactorial
      positivity
    have hsimple :
        0 ≤ ∏ l ∈ simpleLeaves t compound,
          sqrtFactorial (mu.m l) := by
      apply Finset.prod_nonneg
      intro l _hl
      unfold sqrtFactorial
      positivity
    have hcompound :
        0 ≤ ∏ l ∈ compoundLeaves t compound,
          factorialThreeQuarters (mu.m l) := by
      apply Finset.prod_nonneg
      intro l _hl
      unfold factorialThreeQuarters
      positivity
    have hbranch :
        0 ≤ singleScaleBranchPower Nm mu compound := by
      unfold singleScaleBranchPower
      apply Finset.prod_nonneg
      intro v _hv
      exact zpow_nonneg (by positivity) _
    have hRpow :
        0 ≤ (((2 ^ k : ℕ) : ℝ) ^ (2 * O.card)) :=
      pow_nonneg (by positivity) _
    have hratio :
        0 ≤ ∏ v ∈ nonrootBranches t,
          (parentScaleRatio Nm v) ^ 3 := by
      apply Finset.prod_nonneg
      intro v _hv
      exact pow_nonneg (by
        unfold parentScaleRatio
        positivity) _
    have hrootGain :
        0 ≤ (((scaleN Nm (rootV t) : ℝ) /
          ((2 ^ k : ℕ) : ℝ)) ^ min (2 * O.card) 3) :=
      pow_nonneg (by positivity) _
    dsimp only [tail]
    positivity
  have hconstantForm :
      scalar *
          ((∏ l ∈ simpleLeaves t compound,
            sqrtFactorial (mu.m l)) *
          (∏ l ∈ compoundLeaves t compound,
            factorialThreeQuarters (mu.m l)) *
          (8 * Real.exp 4) ^ (5 * totalMultiplicity mu) *
          singleScaleBranchPower Nm mu compound *
          ∏ v ∈ nonrootBranches t,
            (parentScaleRatio Nm v) ^ 3) =
        B ^ totalMultiplicity mu * tail := by
    have hpow :
        finAnchorNXFiberSharpBase Cfiber ^
              totalMultiplicity mu *
            Couter ^ totalMultiplicity mu *
            (8 * Real.exp 4) ^ (5 * totalMultiplicity mu) =
          B ^ totalMultiplicity mu := by
      calc
        finAnchorNXFiberSharpBase Cfiber ^
              totalMultiplicity mu *
            Couter ^ totalMultiplicity mu *
            (8 * Real.exp 4) ^ (5 * totalMultiplicity mu) =
          (finAnchorNXFiberSharpBase Cfiber * Couter) ^
              totalMultiplicity mu *
            (8 * Real.exp 4) ^ (5 * totalMultiplicity mu) := by
            exact congrArg
              (fun q : ℝ =>
                q * (8 * Real.exp 4) ^
                  (5 * totalMultiplicity mu))
              (mul_pow
                (finAnchorNXFiberSharpBase Cfiber)
                Couter (totalMultiplicity mu)).symm
        _ =
          (finAnchorNXFiberSharpBase Cfiber * Couter) ^
              totalMultiplicity mu *
            ((8 * Real.exp 4) ^ 5) ^
              totalMultiplicity mu := by
            exact congrArg
              (fun q : ℝ =>
                (finAnchorNXFiberSharpBase Cfiber * Couter) ^
                  totalMultiplicity mu * q)
              (pow_mul (8 * Real.exp 4) 5
                (totalMultiplicity mu))
        _ =
          (finAnchorNXFiberSharpBase Cfiber * Couter *
            (8 * Real.exp 4) ^ 5) ^ totalMultiplicity mu := by
            exact
              (mul_pow
                (finAnchorNXFiberSharpBase Cfiber * Couter)
                ((8 * Real.exp 4) ^ 5)
                (totalMultiplicity mu)).symm
        _ = B ^ totalMultiplicity mu := by
            rfl
    calc
      scalar *
          ((∏ l ∈ simpleLeaves t compound,
            sqrtFactorial (mu.m l)) *
          (∏ l ∈ compoundLeaves t compound,
            factorialThreeQuarters (mu.m l)) *
          (8 * Real.exp 4) ^ (5 * totalMultiplicity mu) *
          singleScaleBranchPower Nm mu compound *
          ∏ v ∈ nonrootBranches t,
            (parentScaleRatio Nm v) ^ 3) =
        (finAnchorNXFiberSharpBase Cfiber ^
              totalMultiplicity mu *
            Couter ^ totalMultiplicity mu *
            (8 * Real.exp 4) ^ (5 * totalMultiplicity mu)) *
          tail := by
            dsimp only [scalar, tail]
            ring
      _ = B ^ totalMultiplicity mu * tail := by
        rw [hpow]
  have hfinal :
      (∑ y ∈ validWords (M := totalMultiplicity mu)
          (activePMultiplicity Nm mu),
        ∑ x ∈ validRefinements
            (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
          ∑ sigma ∈ arrangementsAtNXWord Nm mu x,
            singleScaleChainWeight z O
              (inducedWord (leafMultiplicity mu) sigma)) ≤
        C0 ^ ((totalMultiplicity mu : ℝ) / 2) * tail := by
    calc
      (∑ y ∈ validWords (M := totalMultiplicity mu)
          (activePMultiplicity Nm mu),
        ∑ x ∈ validRefinements
            (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
          ∑ sigma ∈ arrangementsAtNXWord Nm mu x,
            singleScaleChainWeight z O
              (inducedWord (leafMultiplicity mu) sigma)) ≤
          commonPrefix *
            (Couter ^ totalMultiplicity mu *
              ∏ l : HeppLeaf t,
                originalOuterLeafPayoff Nm mu compound l) :=
        houterCombined
      _ ≤
          scalar *
            ((∏ l ∈ simpleLeaves t compound,
              sqrtFactorial (mu.m l)) *
            (∏ l ∈ compoundLeaves t compound,
              factorialThreeQuarters (mu.m l)) *
            (8 * Real.exp 4) ^ (5 * totalMultiplicity mu) *
            singleScaleBranchPower Nm mu compound *
            ∏ v ∈ nonrootBranches t,
              (parentScaleRatio Nm v) ^ 3) :=
        hledgerCombined
      _ = B ^ totalMultiplicity mu * tail :=
        hconstantForm
      _ ≤ C0 ^ ((totalMultiplicity mu : ℝ) / 2) * tail :=
        mul_le_mul_of_nonneg_right
          (hBdom (totalMultiplicity mu)) htail
  rw [paperSum_eq_sum_PWords_NXWords_arrangements
    Nm mu (fun w => singleScaleChainWeight z O w)]
  calc
    (∑ y ∈ validWords (M := totalMultiplicity mu)
        (activePMultiplicity Nm mu),
      ∑ x ∈ validRefinements
          (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
        ∑ sigma ∈ arrangementsAtNXWord Nm mu x,
          singleScaleChainWeight z O
            (inducedWord (leafMultiplicity mu) sigma)) ≤
        C0 ^ ((totalMultiplicity mu : ℝ) / 2) * tail :=
      hfinal
    _ =
        singleScaleRHS C0 (totalMultiplicity mu) O.card
          (2 ^ k) t Nm mu compound := by
      dsimp only [tail, singleScaleRHS, singleScaleBranchPower]
      ring

end XYCluster

/-- Public namespace alias for Proposition 5.10. -/
theorem singleScale_estimate :
    ∃ C0 : ℝ, SingleScaleEstimate C0 :=
  XYCluster.singleScale_estimate

end

end Anderson4D
