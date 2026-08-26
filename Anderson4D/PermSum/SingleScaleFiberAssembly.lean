import Anderson4D.PermSum.SingleScaleFiberKernelAlignment
import Anderson4D.PermSum.SingleScaleBaseCompletion
import Anderson4D.PermSum.SingleScaleFiberStatement
import Anderson4D.PermSum.SingleScaleInterpolatedGain
import Anderson4D.PermSum.WeightFilters

/-!
# Fixed-fiber assembly

This file combines the canonical pointwise kernel schedule with the finite
Fubini/CPS bridge.  It then bounds the exposed anchor-copy sum and records
the resulting phase-independent prefactor before complementary-phase
interpolation.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/--
The canonical pointwise kernel comparison sums exactly through the
finite-Fubini/CPS bridge.  No factorial or independent right-run choice is
introduced.
-/
theorem sum_arrangementsAtNXWord_edgeKernel_le_conditionedRuns
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ)
    (O : Finset (AdjacentIndex (totalMultiplicity mu)))
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) :
    let runs :=
      finAnchorNXCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor x O
    (∑ σ ∈ arrangementsAtNXWord Nm mu x,
        ∏ edge : AdjacentIndex (totalMultiplicity mu),
          finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
            R O leftPhase rightPhase anchor x σ edge) ≤
      ∑ b ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1,
        conditionedNXAnchoredRunsSum ht hroot Nm mu z hz R
          runs.left runs.right {b} (labeledCopyPoint z b) := by
  apply
    sum_arrangementsAtNXWord_le_finAnchorNXCoarseRunsSum_of_pointwise
      ht hroot Nm mu z hz R leftPhase rightPhase anchor x O
      (fun σ =>
        ∏ edge : AdjacentIndex (totalMultiplicity mu),
          finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
            R O leftPhase rightPhase anchor x σ edge)
  intro b _hb tail _htail
  exact
    edgeKernelProduct_le_finAnchorNXAnchoredScheduleKernel_fromTail
      ht hroot Nm mu z hz R O leftPhase rightPhase anchor x b tail

/-! ## One-phase fixed-fiber bound -/

/--
A phase-independent reference for the common scalar ledger.  Choosing the
unshifted schedule is only a normalization: the exact occurrence/scale/skip
factorization shows that every phase choice has the same value.
-/
def finAnchorNXFiberCommonPrefactor
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (C : ℝ) (R : ℕ)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu))) : ℝ :=
  C ^ totalMultiplicity mu *
    locatedLedgerCommonProduct Nm mu
      (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
        false false anchor x O) *
    (positionLossBase : ℝ) ^ totalMultiplicity mu *
    (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
      min (2 * O.card) 3)

/-- The common scalar ledger is independent of both pairing phases. -/
theorem locatedLedgerCommonProduct_finAnchor_eq_reference
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (x : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    locatedLedgerCommonProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor x O) =
      locatedLedgerCommonProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          false false anchor x O) := by
  rw [locatedLedgerCommonProduct_finAnchor_eq_occurrence_scale_skip,
    locatedLedgerCommonProduct_finAnchor_eq_occurrence_scale_skip]

/-- The named common prefactor is nonnegative at a positive cutoff. -/
theorem finAnchorNXFiberCommonPrefactor_nonneg
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (C : ℝ) (hC : 0 ≤ C) (R : ℕ) (hR : 0 < R)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu))) :
    0 ≤ finAnchorNXFiberCommonPrefactor
      Nm mu C R anchor x O := by
  have hcommon :
      0 ≤ locatedLedgerCommonProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          false false anchor x O) :=
    locatedLedgerCommonProduct_nonneg Nm mu _
  unfold finAnchorNXFiberCommonPrefactor
  positivity

/--
Successor-free wrapper for the one-phase target-ledger estimate.  Paper
fibers are indexed by `totalMultiplicity`, whose positivity is known but
whose successor presentation is not definitional.
-/
private theorem
    finAnchorNXCoarse_targetProduct_le_onePhaseLedger_of_pos
    {t : PlaneTree} {m : ℕ}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℕ) (hRpos : 0 < R)
    (hR : accumulatedScale Nm mu (rootV t) ≤ R)
    (hm : 0 < m)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    ((finAnchorNXCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O).map fun p =>
      nxParityBlockTarget Nm mu (R : ℝ) p).prod ≤
      locatedLedgerCommonProduct Nm mu
          (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O) *
        (positionLossBase : ℝ) ^ totalMultiplicity mu *
        (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
          min (2 * O.card) 3) *
        (∏ edge ∈
          finAnchorPositionPhaseCarrierWithPhases
              leftPhase rightPhase anchor \
            finAnchorNXExceptionalEdgesWithPhases Nm mu
              leftPhase rightPhase anchor cls O,
          finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge) := by
  cases m with
  | zero =>
      simp at hm
  | succ n =>
      exact
        finAnchorNXCoarse_targetProduct_le_onePhaseLedger
          ht hroot Nm mu R hRpos hR
          leftPhase rightPhase anchor cls O

/-- Target products are nonnegative term by term. -/
private theorem nxParityBlockTarget_listProduct_nonneg
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℝ) (ps : List (NXParityBlock Nm mu)) :
    0 ≤ (ps.map fun p => nxParityBlockTarget Nm mu R p).prod := by
  apply List.prod_nonneg
  intro q hq
  obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp hq
  exact nxParityBlockTarget_nonneg Nm mu R p

/--
One fixed `(N,X)` word fiber, one anchor, and one phase choice are bounded
by a phase-independent common prefactor times the retained oriented gain.
The anchor-copy cardinal and the number of elimination blocks have both
been absorbed into the single exponential constant.
-/
theorem fixedFiber_onePhase_edgeKernel_le_commonPrefactor :
    ∃ C : ℝ, 256 ≤ C ∧
      ∀ {t : PlaneTree}
        (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), 0 < R →
          accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ (O : Finset (AdjacentIndex (totalMultiplicity mu)))
          (leftPhase rightPhase : Bool)
          (anchor : Fin (totalMultiplicity mu))
          (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu),
          (∑ σ ∈ arrangementsAtNXWord Nm mu x,
              ∏ edge : AdjacentIndex (totalMultiplicity mu),
                finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
                  (R : ℝ) O leftPhase rightPhase anchor x σ edge) ≤
            finAnchorNXFiberCommonPrefactor
                Nm mu C R anchor x O *
              (∏ edge ∈
                finAnchorPositionPhaseCarrierWithPhases
                    leftPhase rightPhase anchor \
                  finAnchorNXExceptionalEdgesWithPhases Nm mu
                    leftPhase rightPhase anchor x O,
                finAnchorOrientedDyadicEdgeGain
                  Nm mu anchor x edge) := by
  obtain ⟨C₀, hC₀, hconditioned⟩ :=
    conditionedNXAnchoredRunsSum_le_pow_mul_targetProducts
  refine ⟨2 * C₀, by nlinarith, ?_⟩
  intro t ht hroot Nm mu z hz R hRpos hR
    O leftPhase rightPhase anchor x
  let runs :=
    finAnchorNXCoarseRunsWithPhases Nm mu
      leftPhase rightPhase anchor x O
  have hstage :
      (∑ σ ∈ arrangementsAtNXWord Nm mu x,
          ∏ edge : AdjacentIndex (totalMultiplicity mu),
            finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
              (R : ℝ) O leftPhase rightPhase anchor x σ edge) ≤
        ∑ b ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1,
          conditionedNXAnchoredRunsSum ht hroot Nm mu z hz (R : ℝ)
            runs.left runs.right {b} (labeledCopyPoint z b) := by
    simpa only [runs] using
      sum_arrangementsAtNXWord_edgeKernel_le_conditionedRuns
        ht hroot Nm mu z hz (R : ℝ) O
        leftPhase rightPhase anchor x
  have hanchorSum :
      (∑ b ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1,
          conditionedNXAnchoredRunsSum ht hroot Nm mu z hz (R : ℝ)
            runs.left runs.right {b} (labeledCopyPoint z b)) ≤
        (multiplicityNX Nm mu (x anchor).1 : ℝ) *
          (C₀ ^ (runs.left.length + runs.right.length) *
            (runs.left.map fun p =>
              nxParityBlockTarget Nm mu (R : ℝ) p).prod *
            (runs.right.map fun p =>
              nxParityBlockTarget Nm mu (R : ℝ) p).prod) := by
    apply sum_anchorCopyChoices_le_multiplicity_mul
    intro b _hb
    exact
      hconditioned ht hroot Nm mu z hz R hR
        runs.left runs.right {b} (labeledCopyPoint z b)
  have hC₀one : 1 ≤ C₀ := by
    linarith
  have hC₀nonneg : 0 ≤ C₀ :=
    le_trans zero_le_one hC₀one
  have hpower :
      C₀ ^ (runs.left.length + runs.right.length) ≤
        C₀ ^ totalMultiplicity mu := by
    simpa only [runs] using
      finAnchorNXCoarseRuns_constantPower_le
        Nm mu C₀ hC₀one leftPhase rightPhase anchor x O
  have hcardNat :
      multiplicityNX Nm mu (x anchor).1 ≤ totalMultiplicity mu := by
    rw [← card_anchorCopyChoices_eq_multiplicityNX Nm mu x anchor]
    exact card_anchorCopyChoices_le_totalMultiplicity Nm mu x anchor
  have hcard :
      (multiplicityNX Nm mu (x anchor).1 : ℝ) ≤
        (totalMultiplicity mu : ℝ) := by
    exact_mod_cast hcardNat
  have hcount :
      (totalMultiplicity mu : ℝ) ≤
        (2 : ℝ) ^ totalMultiplicity mu := by
    exact_mod_cast (totalMultiplicity mu).lt_two_pow_self.le
  have hcardPower :
      (multiplicityNX Nm mu (x anchor).1 : ℝ) *
          C₀ ^ (runs.left.length + runs.right.length) ≤
        (2 * C₀) ^ totalMultiplicity mu := by
    calc
      (multiplicityNX Nm mu (x anchor).1 : ℝ) *
            C₀ ^ (runs.left.length + runs.right.length) ≤
          (totalMultiplicity mu : ℝ) *
            C₀ ^ totalMultiplicity mu :=
        mul_le_mul hcard hpower
          (pow_nonneg hC₀nonneg _) (by positivity)
      _ ≤ (2 : ℝ) ^ totalMultiplicity mu *
            C₀ ^ totalMultiplicity mu :=
        mul_le_mul_of_nonneg_right hcount
          (pow_nonneg hC₀nonneg _)
      _ = (2 * C₀) ^ totalMultiplicity mu := by
        rw [mul_pow]
  have hleftTarget :
      0 ≤ (runs.left.map fun p =>
        nxParityBlockTarget Nm mu (R : ℝ) p).prod :=
    nxParityBlockTarget_listProduct_nonneg
      Nm mu (R : ℝ) runs.left
  have hrightTarget :
      0 ≤ (runs.right.map fun p =>
        nxParityBlockTarget Nm mu (R : ℝ) p).prod :=
    nxParityBlockTarget_listProduct_nonneg
      Nm mu (R : ℝ) runs.right
  have htargets :
      0 ≤
        (runs.left.map fun p =>
          nxParityBlockTarget Nm mu (R : ℝ) p).prod *
        (runs.right.map fun p =>
          nxParityBlockTarget Nm mu (R : ℝ) p).prod :=
    mul_nonneg hleftTarget hrightTarget
  calc
    (∑ σ ∈ arrangementsAtNXWord Nm mu x,
        ∏ edge : AdjacentIndex (totalMultiplicity mu),
          finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
            (R : ℝ) O leftPhase rightPhase anchor x σ edge) ≤
      ∑ b ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1,
        conditionedNXAnchoredRunsSum ht hroot Nm mu z hz (R : ℝ)
          runs.left runs.right {b} (labeledCopyPoint z b) :=
      hstage
    _ ≤ (multiplicityNX Nm mu (x anchor).1 : ℝ) *
          (C₀ ^ (runs.left.length + runs.right.length) *
            (runs.left.map fun p =>
              nxParityBlockTarget Nm mu (R : ℝ) p).prod *
            (runs.right.map fun p =>
              nxParityBlockTarget Nm mu (R : ℝ) p).prod) :=
      hanchorSum
    _ =
        ((multiplicityNX Nm mu (x anchor).1 : ℝ) *
          C₀ ^ (runs.left.length + runs.right.length)) *
        ((runs.left.map fun p =>
          nxParityBlockTarget Nm mu (R : ℝ) p).prod *
        (runs.right.map fun p =>
          nxParityBlockTarget Nm mu (R : ℝ) p).prod) := by
      ring
    _ ≤ (2 * C₀) ^ totalMultiplicity mu *
        ((runs.left.map fun p =>
          nxParityBlockTarget Nm mu (R : ℝ) p).prod *
        (runs.right.map fun p =>
          nxParityBlockTarget Nm mu (R : ℝ) p).prod) :=
      mul_le_mul_of_nonneg_right hcardPower htargets
    _ = (2 * C₀) ^ totalMultiplicity mu *
        ((finAnchorNXCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor x O).map fun p =>
            nxParityBlockTarget Nm mu (R : ℝ) p).prod := by
      rw [finAnchorNXCoarseRuns_targetProducts_eq_ledger
        Nm mu (R : ℝ) leftPhase rightPhase anchor x O]
    _ ≤ (2 * C₀) ^ totalMultiplicity mu *
        (locatedLedgerCommonProduct Nm mu
            (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
              leftPhase rightPhase anchor x O) *
          (positionLossBase : ℝ) ^ totalMultiplicity mu *
          ((((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
              min (2 * O.card) 3) *
            (∏ edge ∈
              finAnchorPositionPhaseCarrierWithPhases
                  leftPhase rightPhase anchor \
                finAnchorNXExceptionalEdgesWithPhases Nm mu
                  leftPhase rightPhase anchor x O,
              finAnchorOrientedDyadicEdgeGain
                Nm mu anchor x edge))) :=
      mul_le_mul_of_nonneg_left
        (by
          simpa only [mul_assoc] using
            finAnchorNXCoarse_targetProduct_le_onePhaseLedger_of_pos
              ht hroot Nm mu R hRpos hR
              (by
                have hm := two_le_totalMultiplicity mu
                omega)
              leftPhase rightPhase anchor x O)
        (pow_nonneg (mul_nonneg (by norm_num) hC₀nonneg) _)
    _ =
        finAnchorNXFiberCommonPrefactor
            Nm mu (2 * C₀) R anchor x O *
          (∏ edge ∈
            finAnchorPositionPhaseCarrierWithPhases
                leftPhase rightPhase anchor \
              finAnchorNXExceptionalEdgesWithPhases Nm mu
                leftPhase rightPhase anchor x O,
            finAnchorOrientedDyadicEdgeGain
              Nm mu anchor x edge) := by
      rw [locatedLedgerCommonProduct_finAnchor_eq_reference]
      unfold finAnchorNXFiberCommonPrefactor
      ring

/-! ## Complementary-phase interpolation -/

/--
Successor-free packaging of the interpolated `1/16` gain.  At positive
length it is exactly the active-`P` ratio product on the `m - 1` original
adjacencies; the zero branch is uninhabited because it requires an anchor.
-/
noncomputable def finAnchorNXInterpolatedFiberGain
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) :
    (m : ℕ) →
      Fin m →
      (Fin m → ActiveNXClass Nm mu) →
      Finset (AdjacentIndex m) → ℝ
  | 0, anchor, _cls, _O => Fin.elim0 anchor
  | _n + 1, anchor, cls, O =>
      ∏ j ∈ Finset.univ \
          finAnchorNXInterpolatedExceptionalFinEdges Nm mu
            leftPhase rightPhase anchor cls O,
        ratioGain (1 / 16 : ℝ)
          (finAnchorOrientedActivePRatio anchor
            (fun i => activeNXToP Nm mu (cls i)) j)

/--
Successor-free wrapper around the complementary-phase geometric mean.
The two hypotheses are written in original adjacency coordinates; the
proof changes to `Fin n` coordinates only after exposing `m = n + 1`.
-/
private theorem
    finAnchorNX_two_phase_edgeGain_bounds_le_interpolated_of_pos
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hm : 0 < m)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m))
    (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hphase :
      S ≤ A *
        (∏ edge ∈
          finAnchorPositionPhaseCarrierWithPhases
              leftPhase rightPhase anchor \
            finAnchorNXExceptionalEdgesWithPhases Nm mu
              leftPhase rightPhase anchor cls O,
          finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge))
    (hflip :
      S ≤ A *
        (∏ edge ∈
          finAnchorPositionPhaseCarrierWithPhases
              (!leftPhase) (!rightPhase) anchor \
            finAnchorNXExceptionalEdgesWithPhases Nm mu
              (!leftPhase) (!rightPhase) anchor cls O,
          finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge)) :
    S ≤ A *
      finAnchorNXInterpolatedFiberGain
        Nm mu leftPhase rightPhase m anchor cls O := by
  cases m with
  | zero =>
      simp at hm
  | succ n =>
      change S ≤ A *
        (∏ j ∈ Finset.univ \
            finAnchorNXInterpolatedExceptionalFinEdges Nm mu
              leftPhase rightPhase anchor cls O,
          ratioGain (1 / 16 : ℝ)
            (finAnchorOrientedActivePRatio anchor
              (fun i => activeNXToP Nm mu (cls i)) j))
      rw [finAnchor_phaseOrientedDyadicProduct_eq_ratioGain
        Nm mu leftPhase rightPhase anchor cls O] at hphase
      rw [finAnchor_phaseOrientedDyadicProduct_eq_ratioGain
        Nm mu (!leftPhase) (!rightPhase) anchor cls O] at hflip
      exact
        finAnchorNX_two_phase_scaled_gain_bounds_le_sixteenth
          Nm mu leftPhase rightPhase anchor cls O
          (finAnchorOrientedActivePRatio anchor
            (fun i => activeNXToP Nm mu (cls i)))
          (fun j =>
            finAnchorOrientedActivePRatio_nonneg anchor
              (fun i => activeNXToP Nm mu (cls i)) j)
          A S hA hS hphase hflip

/--
The common prefactor for the frozen chain-weight fiber includes the
statement-to-edge-kernel scale factor.  It is still independent of both
pairing phases.
-/
def finAnchorNXFiberChainCommonPrefactor
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (C : ℝ) (R : ℕ)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu))) : ℝ :=
  (R : ℝ) ^ (2 * O.card) *
    finAnchorNXFiberCommonPrefactor Nm mu C R anchor x O

/-- The scaled common prefactor is nonnegative. -/
theorem finAnchorNXFiberChainCommonPrefactor_nonneg
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (C : ℝ) (hC : 0 ≤ C) (R : ℕ) (hR : 0 < R)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (totalMultiplicity mu))) :
    0 ≤ finAnchorNXFiberChainCommonPrefactor
      Nm mu C R anchor x O := by
  unfold finAnchorNXFiberChainCommonPrefactor
  exact mul_nonneg
    (pow_nonneg (by positivity) _)
    (finAnchorNXFiberCommonPrefactor_nonneg
      Nm mu C hC R hR anchor x O)

/--
Complementary phase choices give the fixed-fiber `1/16` estimate for the
frozen chain weight.  The same universal constant and the same common
prefactor are used in both one-phase bounds before interpolation.
-/
theorem fixedFiber_twoPhase_singleScaleChainWeight_le_sixteenth :
    ∃ C : ℝ, 256 ≤ C ∧
      ∀ {t : PlaneTree}
        (_ht : t.isValid = true) (_hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (_hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), 0 < R →
          accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ (O : Finset (AdjacentIndex (totalMultiplicity mu)))
          (leftPhase rightPhase : Bool)
          (anchor : Fin (totalMultiplicity mu))
          (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu),
          (∑ σ ∈ arrangementsAtNXWord Nm mu x,
              singleScaleChainWeight z O
                (inducedWord (leafMultiplicity mu) σ)) ≤
            finAnchorNXFiberChainCommonPrefactor
                Nm mu C R anchor x O *
              finAnchorNXInterpolatedFiberGain Nm mu
                leftPhase rightPhase (totalMultiplicity mu)
                anchor x O := by
  obtain ⟨C, hC, honePhase⟩ :=
    fixedFiber_onePhase_edgeKernel_le_commonPrefactor
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu z hz R hRpos hR
    O leftPhase rightPhase anchor x
  let S : ℝ :=
    ∑ σ ∈ arrangementsAtNXWord Nm mu x,
      singleScaleChainWeight z O
        (inducedWord (leafMultiplicity mu) σ)
  let A : ℝ :=
    finAnchorNXFiberChainCommonPrefactor
      Nm mu C R anchor x O
  have hCnonneg : 0 ≤ C := by
    linarith
  have hS : 0 ≤ S := by
    dsimp only [S]
    apply Finset.sum_nonneg
    intro σ _hσ
    exact singleScaleChainWeight_nonneg z O
      (inducedWord (leafMultiplicity mu) σ)
  have hA : 0 ≤ A := by
    exact finAnchorNXFiberChainCommonPrefactor_nonneg
      Nm mu C hCnonneg R hRpos anchor x O
  have hRreal : (R : ℝ) ≠ 0 := by
    exact_mod_cast hRpos.ne'
  have hphaseEdge :=
    honePhase ht hroot Nm mu z hz R hRpos hR
      O leftPhase rightPhase anchor x
  have hflipEdge :=
    honePhase ht hroot Nm mu z hz R hRpos hR
      O (!leftPhase) (!rightPhase) anchor x
  have hphase :
      S ≤ A *
        (∏ edge ∈
          finAnchorPositionPhaseCarrierWithPhases
              leftPhase rightPhase anchor \
            finAnchorNXExceptionalEdgesWithPhases Nm mu
              leftPhase rightPhase anchor x O,
          finAnchorOrientedDyadicEdgeGain Nm mu anchor x edge) := by
    calc
      S ≤ (R : ℝ) ^ (2 * O.card) *
          (∑ σ ∈ arrangementsAtNXWord Nm mu x,
            ∏ edge : AdjacentIndex (totalMultiplicity mu),
              finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
                (R : ℝ) O leftPhase rightPhase anchor x σ edge) := by
        exact
          sum_arrangementsAtNXWord_singleScaleChainWeight_le_edgeKernelWithPhases
            ht hroot Nm mu z hz (R : ℝ) hRreal O
            leftPhase rightPhase anchor x
      _ ≤ (R : ℝ) ^ (2 * O.card) *
          (finAnchorNXFiberCommonPrefactor
              Nm mu C R anchor x O *
            (∏ edge ∈
              finAnchorPositionPhaseCarrierWithPhases
                  leftPhase rightPhase anchor \
                finAnchorNXExceptionalEdgesWithPhases Nm mu
                  leftPhase rightPhase anchor x O,
              finAnchorOrientedDyadicEdgeGain
                Nm mu anchor x edge)) :=
        mul_le_mul_of_nonneg_left hphaseEdge
          (pow_nonneg (by positivity) _)
      _ = A *
          (∏ edge ∈
            finAnchorPositionPhaseCarrierWithPhases
                leftPhase rightPhase anchor \
              finAnchorNXExceptionalEdgesWithPhases Nm mu
                leftPhase rightPhase anchor x O,
            finAnchorOrientedDyadicEdgeGain
              Nm mu anchor x edge) := by
        unfold A finAnchorNXFiberChainCommonPrefactor
        ring
  have hflip :
      S ≤ A *
        (∏ edge ∈
          finAnchorPositionPhaseCarrierWithPhases
              (!leftPhase) (!rightPhase) anchor \
            finAnchorNXExceptionalEdgesWithPhases Nm mu
              (!leftPhase) (!rightPhase) anchor x O,
          finAnchorOrientedDyadicEdgeGain Nm mu anchor x edge) := by
    calc
      S ≤ (R : ℝ) ^ (2 * O.card) *
          (∑ σ ∈ arrangementsAtNXWord Nm mu x,
            ∏ edge : AdjacentIndex (totalMultiplicity mu),
              finAnchorNXArrangementEdgeKernel ht hroot Nm mu z hz
                (R : ℝ) O (!leftPhase) (!rightPhase)
                anchor x σ edge) := by
        exact
          sum_arrangementsAtNXWord_singleScaleChainWeight_le_edgeKernelWithPhases
            ht hroot Nm mu z hz (R : ℝ) hRreal O
            (!leftPhase) (!rightPhase) anchor x
      _ ≤ (R : ℝ) ^ (2 * O.card) *
          (finAnchorNXFiberCommonPrefactor
              Nm mu C R anchor x O *
            (∏ edge ∈
              finAnchorPositionPhaseCarrierWithPhases
                  (!leftPhase) (!rightPhase) anchor \
                finAnchorNXExceptionalEdgesWithPhases Nm mu
                  (!leftPhase) (!rightPhase) anchor x O,
              finAnchorOrientedDyadicEdgeGain
                Nm mu anchor x edge)) :=
        mul_le_mul_of_nonneg_left hflipEdge
          (pow_nonneg (by positivity) _)
      _ = A *
          (∏ edge ∈
            finAnchorPositionPhaseCarrierWithPhases
                (!leftPhase) (!rightPhase) anchor \
              finAnchorNXExceptionalEdgesWithPhases Nm mu
                (!leftPhase) (!rightPhase) anchor x O,
            finAnchorOrientedDyadicEdgeGain
              Nm mu anchor x edge) := by
        unfold A finAnchorNXFiberChainCommonPrefactor
        ring
  exact
    finAnchorNX_two_phase_edgeGain_bounds_le_interpolated_of_pos
      Nm mu
      (by
        have hm := two_le_totalMultiplicity mu
        omega)
      leftPhase rightPhase anchor x O A S hA hS hphase hflip

end XYCluster

end

end Anderson4D
