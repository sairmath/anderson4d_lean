import Anderson4D.PermSum.SingleScaleFiberAssembly
import Anderson4D.PermSum.SingleScaleAnchorScaleLedger
import Anderson4D.PermSum.SingleScaleOuterFiberSum

/-!
# Sharp postprocessing of a fixed `(N,X)` fiber

The fixed-fiber estimate stops after the occurrence bound.  It retains the
full word base-scale factor and the square of the anchor scale.  The outer
leaf payoff is not inserted here.

A separate scalar lemma below consumes one explicit copy of the global
outer payoff and only then applies anchor completion and reverse-power
conversion to the paper-facing simple/compound and branch ledgers.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-- Uniform base accumulated before the reverse-power step. -/
def finAnchorNXFiberSharpBase (C : ℝ) : ℝ :=
  C * (positionLossBase : ℝ) * (2 * Real.exp 1)

theorem finAnchorNXFiberSharpBase_nonneg
    (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ finAnchorNXFiberSharpBase C := by
  unfold finAnchorNXFiberSharpBase
  have hposition : 0 ≤ (positionLossBase : ℝ) := by
    norm_num [positionLossBase]
  positivity

/--
Sharp coefficient bound for one valid fixed fiber.  Notice that
`nxWordBaseScaleFactor x`, the anchor-scale square, and the leaf
square-root factorial product are all still present.
-/
theorem finAnchorNXFiberChainCommonPrefactor_le_sharpOccurrence
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (C : ℝ) (hC : 0 ≤ C)
    (R s : ℕ) (hR : 0 < R)
    (O : Finset (AdjacentIndex (totalMultiplicity mu)))
    (hs : O.card = s)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := totalMultiplicity mu)
      (activeNXMultiplicity Nm mu)) :
    finAnchorNXFiberChainCommonPrefactor
        Nm mu C R anchor x O ≤
      finAnchorNXFiberSharpBase C ^ totalMultiplicity mu *
        sqrtFactorial (totalMultiplicity mu - s) *
        (∏ l : HeppLeaf t,
          sqrtFactorial (leafMultiplicity mu l)) *
        nxWordBaseScaleFactor x *
        ((x anchor).1.1 : ℝ) ^ 2 *
        (R : ℝ) ^ (2 * s) *
        (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
          min (2 * s) 3) := by
  have hcommon :
      locatedLedgerCommonProduct Nm mu
          (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            false false anchor x O) ≤
        outward588WordOccurrenceFactor Nm mu anchor O x *
          nxWordBaseScaleFactor x *
          ((x anchor).1.1 : ℝ) ^ 2 :=
    locatedLedgerCommonProduct_finAnchor_le_completed
      Nm mu false false anchor x O
  have hoccurrence :
      outward588WordOccurrenceFactor Nm mu anchor O x ≤
        (2 * Real.exp 1) ^ totalMultiplicity mu *
          sqrtFactorial (totalMultiplicity mu - s) *
          ∏ l : HeppLeaf t,
            sqrtFactorial (leafMultiplicity mu l) := by
    simpa only [sqrtFactorial] using
      outward588WordOccurrenceFactor_le_factorial
        Nm mu anchor O x hx s rfl hs
  have hbaseAnchor :
      0 ≤ nxWordBaseScaleFactor x *
        ((x anchor).1.1 : ℝ) ^ 2 := by
    unfold nxWordBaseScaleFactor
    positivity
  have hledger :
      locatedLedgerCommonProduct Nm mu
          (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            false false anchor x O) ≤
        (2 * Real.exp 1) ^ totalMultiplicity mu *
          sqrtFactorial (totalMultiplicity mu - s) *
          (∏ l : HeppLeaf t,
            sqrtFactorial (leafMultiplicity mu l)) *
          nxWordBaseScaleFactor x *
          ((x anchor).1.1 : ℝ) ^ 2 := by
    calc
      locatedLedgerCommonProduct Nm mu
          (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            false false anchor x O) ≤
        outward588WordOccurrenceFactor Nm mu anchor O x *
          nxWordBaseScaleFactor x *
          ((x anchor).1.1 : ℝ) ^ 2 := hcommon
      _ =
        outward588WordOccurrenceFactor Nm mu anchor O x *
          (nxWordBaseScaleFactor x *
            ((x anchor).1.1 : ℝ) ^ 2) := by ring
      _ ≤
        ((2 * Real.exp 1) ^ totalMultiplicity mu *
          sqrtFactorial (totalMultiplicity mu - s) *
          (∏ l : HeppLeaf t,
            sqrtFactorial (leafMultiplicity mu l))) *
          (nxWordBaseScaleFactor x *
            ((x anchor).1.1 : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hoccurrence hbaseAnchor
      _ = _ := by ring
  have hmultiplier :
      0 ≤ (R : ℝ) ^ (2 * O.card) *
        (C ^ totalMultiplicity mu *
          (positionLossBase : ℝ) ^ totalMultiplicity mu *
          (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
            min (2 * O.card) 3)) := by
    positivity
  calc
    finAnchorNXFiberChainCommonPrefactor
        Nm mu C R anchor x O =
      ((R : ℝ) ^ (2 * O.card) *
        (C ^ totalMultiplicity mu *
          (positionLossBase : ℝ) ^ totalMultiplicity mu *
          (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
            min (2 * O.card) 3))) *
        locatedLedgerCommonProduct Nm mu
          (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            false false anchor x O) := by
      unfold finAnchorNXFiberChainCommonPrefactor
        finAnchorNXFiberCommonPrefactor
      ring
    _ ≤
      ((R : ℝ) ^ (2 * O.card) *
        (C ^ totalMultiplicity mu *
          (positionLossBase : ℝ) ^ totalMultiplicity mu *
          (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
            min (2 * O.card) 3))) *
        ((2 * Real.exp 1) ^ totalMultiplicity mu *
          sqrtFactorial (totalMultiplicity mu - s) *
          (∏ l : HeppLeaf t,
            sqrtFactorial (leafMultiplicity mu l)) *
          nxWordBaseScaleFactor x *
          ((x anchor).1.1 : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hledger hmultiplier
    _ =
      finAnchorNXFiberSharpBase C ^ totalMultiplicity mu *
        sqrtFactorial (totalMultiplicity mu - s) *
        (∏ l : HeppLeaf t,
          sqrtFactorial (leafMultiplicity mu l)) *
        nxWordBaseScaleFactor x *
        ((x anchor).1.1 : ℝ) ^ 2 *
        (R : ℝ) ^ (2 * s) *
        (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
          min (2 * s) 3) := by
      rw [hs]
      unfold finAnchorNXFiberSharpBase
      rw [mul_pow, mul_pow]
      ring

/--
At successor length, the successor-free interpolated gain is exactly the
oriented active-`P` weight.
-/
theorem finAnchorNXInterpolatedFiberGain_eq_orientedActivePWeight
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (n + 1))
    (x : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    finAnchorNXInterpolatedFiberGain Nm mu
        leftPhase rightPhase (n + 1) anchor x O =
      anchoredOrientedActivePWeight (1 / 16 : ℝ)
        (finAnchorPositionalInterpolatedExceptionalFinEdges
          leftPhase rightPhase anchor O)
        anchor (fun i => activeNXToP Nm mu (x i)) := by
  exact
    finAnchorNX_interpolatedGain_eq_orientedActivePWeight
      Nm mu leftPhase rightPhase anchor x O

/--
Successor-free packaging of the oriented active-`P` weight.  Its zero
branch is uninhabited for the same reason as the interpolated fiber gain.
-/
noncomputable def finAnchorNXOrientedActivePWeight
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) :
    (m : ℕ) →
      Fin m →
      (Fin m → ActiveNXClass Nm mu) →
      Finset (AdjacentIndex m) → ℝ
  | 0, anchor, _x, _O => Fin.elim0 anchor
  | _n + 1, anchor, x, O =>
      anchoredOrientedActivePWeight (1 / 16 : ℝ)
        (finAnchorPositionalInterpolatedExceptionalFinEdges
          leftPhase rightPhase anchor O)
        anchor (fun i => activeNXToP Nm mu (x i))

/--
At every positive length the successor-free interpolated gain and the
successor-free oriented active-`P` weight coincide.  The proof exposes the
successor presentation only locally.
-/
theorem
    finAnchorNXInterpolatedFiberGain_eq_orientedActivePWeight_of_pos
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hm : 0 < m)
    (leftPhase rightPhase : Bool)
    (anchor : Fin m)
    (x : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    finAnchorNXInterpolatedFiberGain Nm mu
        leftPhase rightPhase m anchor x O =
      finAnchorNXOrientedActivePWeight Nm mu
        leftPhase rightPhase m anchor x O := by
  cases m with
  | zero =>
      simp at hm
  | succ n =>
      exact
        finAnchorNXInterpolatedFiberGain_eq_orientedActivePWeight
          Nm mu leftPhase rightPhase anchor x O

/--
Total-multiplicity-domain wrapper.  The dependent paper carriers are
generalized together before the zero/successor split.
-/
theorem
    finAnchorNXInterpolatedFiberGain_eq_orientedActivePWeight_total
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu))) :
    finAnchorNXInterpolatedFiberGain Nm mu
        leftPhase rightPhase (totalMultiplicity mu) anchor x O =
      finAnchorNXOrientedActivePWeight Nm mu
        leftPhase rightPhase (totalMultiplicity mu) anchor x O := by
  generalize hm : totalMultiplicity mu = m at anchor x O ⊢
  cases m with
  | zero =>
      exact Fin.elim0 anchor
  | succ n =>
      exact
        finAnchorNXInterpolatedFiberGain_eq_orientedActivePWeight
          Nm mu leftPhase rightPhase anchor x O

/-- The successor-free oriented active-`P` weight is nonnegative. -/
theorem finAnchorNXOrientedActivePWeight_nonneg
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hm : 0 < m)
    (leftPhase rightPhase : Bool)
    (anchor : Fin m)
    (x : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    0 ≤ finAnchorNXOrientedActivePWeight Nm mu
      leftPhase rightPhase m anchor x O := by
  rw [←
    finAnchorNXInterpolatedFiberGain_eq_orientedActivePWeight_of_pos
      Nm mu hm leftPhase rightPhase anchor x O]
  cases m with
  | zero =>
      simp at hm
  | succ n =>
      apply Finset.prod_nonneg
      intro j _hj
      exact ratioGain_nonneg (1 / 16 : ℝ)
        (finAnchorOrientedActivePRatio_nonneg anchor
          (fun i => activeNXToP Nm mu (x i)) j)

/--
Pre-outer fixed-fiber theorem at the deterministic minimal-scale anchor.
It is the sharp stopping point: no outer payoff, compound factorial, or
reverse-power estimate has been used.
-/
theorem
    fixedFiber_singleScaleChainWeight_le_sharpOccurrence :
    ∃ C : ℝ, 256 ≤ C ∧
      ∀ {t : PlaneTree}
        (_ht : t.isValid = true) (_hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (_hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), 0 < R →
          accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ (s : ℕ)
          (O : Finset (AdjacentIndex (totalMultiplicity mu))),
          O.card = s →
        ∀ (x : Fin (totalMultiplicity mu) →
              ActiveNXClass Nm mu),
          x ∈ validWords (M := totalMultiplicity mu)
            (activeNXMultiplicity Nm mu) →
          let anchor := totalMultiplicityNXScaleAnchor Nm mu x
          (∑ σ ∈ arrangementsAtNXWord Nm mu x,
              singleScaleChainWeight z O
                (inducedWord (leafMultiplicity mu) σ)) ≤
            finAnchorNXFiberSharpBase C ^ totalMultiplicity mu *
              sqrtFactorial (totalMultiplicity mu - s) *
              (∏ l : HeppLeaf t,
                sqrtFactorial (leafMultiplicity mu l)) *
              nxWordBaseScaleFactor x *
              ((x anchor).1.1 : ℝ) ^ 2 *
              (R : ℝ) ^ (2 * s) *
              (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
                min (2 * s) 3) *
              finAnchorNXOrientedActivePWeight Nm mu
                false false (totalMultiplicity mu)
                anchor x O := by
  obtain ⟨C, hC, hinterpolated⟩ :=
    fixedFiber_twoPhase_singleScaleChainWeight_le_sixteenth
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu z hz R hRpos hR s O hs x hx
  dsimp only
  let anchor := totalMultiplicityNXScaleAnchor Nm mu x
  have hCnonneg : 0 ≤ C := by
    linarith
  have hm : 0 < totalMultiplicity mu := by
    have htwo := two_le_totalMultiplicity mu
    omega
  have hinner :=
    hinterpolated ht hroot Nm mu z hz R hRpos hR
      O false false anchor x
  have hcoefficient :=
    finAnchorNXFiberChainCommonPrefactor_le_sharpOccurrence
      Nm mu C hCnonneg R s hRpos O hs anchor x hx
  have hgain :
      0 ≤ finAnchorNXInterpolatedFiberGain Nm mu
        false false (totalMultiplicity mu) anchor x O := by
    rw [
      finAnchorNXInterpolatedFiberGain_eq_orientedActivePWeight_of_pos
        Nm mu hm false false anchor x O]
    exact
      finAnchorNXOrientedActivePWeight_nonneg
        Nm mu hm false false anchor x O
  calc
    (∑ σ ∈ arrangementsAtNXWord Nm mu x,
        singleScaleChainWeight z O
          (inducedWord (leafMultiplicity mu) σ)) ≤
      finAnchorNXFiberChainCommonPrefactor
          Nm mu C R anchor x O *
        finAnchorNXInterpolatedFiberGain Nm mu
          false false (totalMultiplicity mu) anchor x O :=
      hinner
    _ ≤
      (finAnchorNXFiberSharpBase C ^ totalMultiplicity mu *
        sqrtFactorial (totalMultiplicity mu - s) *
        (∏ l : HeppLeaf t,
          sqrtFactorial (leafMultiplicity mu l)) *
        nxWordBaseScaleFactor x *
        ((x anchor).1.1 : ℝ) ^ 2 *
        (R : ℝ) ^ (2 * s) *
        (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
          min (2 * s) 3)) *
        finAnchorNXInterpolatedFiberGain Nm mu
          false false (totalMultiplicity mu) anchor x O :=
      mul_le_mul_of_nonneg_right hcoefficient hgain
    _ =
      finAnchorNXFiberSharpBase C ^ totalMultiplicity mu *
        sqrtFactorial (totalMultiplicity mu - s) *
        (∏ l : HeppLeaf t,
          sqrtFactorial (leafMultiplicity mu l)) *
        nxWordBaseScaleFactor x *
        ((x anchor).1.1 : ℝ) ^ 2 *
        (R : ℝ) ^ (2 * s) *
        (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
          min (2 * s) 3) *
        finAnchorNXOrientedActivePWeight Nm mu
          false false (totalMultiplicity mu)
          anchor x O := by
      rw [
        finAnchorNXInterpolatedFiberGain_eq_orientedActivePWeight_of_pos
          Nm mu hm false false anchor x O]

/--
One explicit copy of the global outer payoff completes the retained base
coefficient.  This lemma is intentionally independent of the fiber bound:
the caller must supply that payoff exactly once.
-/
theorem
    completedNXWordScalar_mul_outerPayoff_le_branchRatioLedger
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t))
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := totalMultiplicity mu)
      (activeNXMultiplicity Nm mu))
    (hscale : SatisfiesSingleScaleCondition Nm mu) :
    (∏ l : HeppLeaf t,
        sqrtFactorial (leafMultiplicity mu l)) *
        nxWordBaseScaleFactor x *
        ((x anchor).1.1 : ℝ) ^ 2 *
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
  obtain ⟨l₀, _hl₀, hcomplete⟩ :=
    exists_anchorLeaf_wordBaseFactorialOuterPayoff_eq_leafPower
      Nm mu compound anchor x hx
  have hleafPower :
      singleScaleLeafPower Nm mu compound l₀ ≤
        (8 * Real.exp 4) ^ (5 * totalMultiplicity mu) *
          singleScaleBranchPower Nm mu compound *
          ∏ v ∈ nonrootBranches t,
            (parentScaleRatio Nm v) ^ 3 :=
    singleScale_leafPower_le_uniformPower_mul_branchPower_mul_ratioCube
      ht hroot Nm mu compound l₀ hscale
  have hfactorialSimple :
      0 ≤ ∏ l ∈ simpleLeaves t compound,
        sqrtFactorial (mu.m l) := by
    exact Finset.prod_nonneg fun l _ => by
      unfold sqrtFactorial
      positivity
  have hfactorialCompound :
      0 ≤ ∏ l ∈ compoundLeaves t compound,
        factorialThreeQuarters (mu.m l) := by
    exact Finset.prod_nonneg fun l _ => by
      unfold factorialThreeQuarters
      positivity
  calc
    (∏ l : HeppLeaf t,
        sqrtFactorial (leafMultiplicity mu l)) *
        nxWordBaseScaleFactor x *
        ((x anchor).1.1 : ℝ) ^ 2 *
        (∏ l : HeppLeaf t,
          originalOuterLeafPayoff Nm mu compound l) =
      nxWordBaseScaleFactor x *
        (∏ l : HeppLeaf t,
          sqrtFactorial (leafMultiplicity mu l) *
            originalOuterLeafPayoff Nm mu compound l) *
        ((x anchor).1.1 : ℝ) ^ 2 := by
      rw [Finset.prod_mul_distrib]
      ring
    _ =
      (∏ l ∈ simpleLeaves t compound,
        sqrtFactorial (mu.m l)) *
      (∏ l ∈ compoundLeaves t compound,
        factorialThreeQuarters (mu.m l)) *
      singleScaleLeafPower Nm mu compound l₀ := hcomplete
    _ ≤
      (∏ l ∈ simpleLeaves t compound,
        sqrtFactorial (mu.m l)) *
      (∏ l ∈ compoundLeaves t compound,
        factorialThreeQuarters (mu.m l)) *
      ((8 * Real.exp 4) ^ (5 * totalMultiplicity mu) *
        singleScaleBranchPower Nm mu compound *
        ∏ v ∈ nonrootBranches t,
          (parentScaleRatio Nm v) ^ 3) := by
      exact mul_le_mul_of_nonneg_left hleafPower
        (mul_nonneg hfactorialSimple hfactorialCompound)
    _ = _ := by ring

/--
Total-multiplicity-domain wrapper for the existing global outer estimate.
It consumes the outer payoff once and exposes the successor-free oriented
weight used by the sharp fixed-fiber theorem.
-/
theorem
    global_refinement_orientedWeight_total_le_originalPayoff :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (_ht : t.isValid = true)
        (_hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (compound : Finset (VPos t))
        (chooseAnchor :
          (Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) →
            Fin (totalMultiplicity mu))
        (O : Finset (AdjacentIndex (totalMultiplicity mu))),
        (∑ y ∈ validWords (M := totalMultiplicity mu)
            (activePMultiplicity Nm mu),
          ∑ x ∈ validRefinements
              (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
            finAnchorNXOrientedActivePWeight Nm mu
              false false (totalMultiplicity mu)
              (chooseAnchor x) x O) ≤
          C ^ totalMultiplicity mu *
            ∏ l : HeppLeaf t,
              originalOuterLeafPayoff Nm mu compound l := by
  obtain ⟨C, hC, hglobal⟩ :=
    global_refinement_orientedWeight_le_originalPayoff
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu compound chooseAnchor O
  have h := hglobal ht hroot Nm mu compound
  generalize hm : totalMultiplicity mu = m at chooseAnchor O h ⊢
  cases m with
  | zero =>
      have htwo := two_le_totalMultiplicity mu
      rw [hm] at htwo
      omega
  | succ n =>
      simpa [finAnchorNXOrientedActivePWeight] using
        h chooseAnchor O

end XYCluster

end

end Anderson4D
