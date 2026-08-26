import Anderson4D.PermSum.SingleScalePreciseGainGlue
import Anderson4D.PermSum.SingleScaleRoughScaleLedger
import Anderson4D.PermSum.SingleScaleSharedElimination
import Anderson4D.PermSum.SingleScaleClassFubini

/-!
# One-phase assembly for the single-scale estimate

This file combines the two outward target products into the single located
ledger and then applies the scalar-loss, rough-scale, and precise-gain
ledgers in their safe inequality directions.  It also identifies the
oriented dyadic gain with the original-edge active-`P` gain used by the
outer sequence estimate.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

theorem locatedLedgerCommonProduct_nonneg
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    0 ≤ locatedLedgerCommonProduct Nm mu bs := by
  unfold locatedLedgerCommonProduct
  apply List.prod_nonneg
  intro x hx
  obtain ⟨b, _hb, rfl⟩ := List.mem_map.mp hx
  exact locatedBlockCommonTarget_nonneg Nm mu b

theorem locatedLedgerLossAtoms_prod_nonneg
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    0 ≤ (locatedLedgerLossAtoms Nm mu bs).prod := by
  exact List.prod_nonneg fun x hx =>
    mem_locatedLedgerLossAtoms_nonneg Nm mu bs hx

theorem locatedLedgerRoughScaleProduct_nonneg
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (R : ℝ) (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    0 ≤ locatedLedgerRoughScaleProduct R bs := by
  unfold locatedLedgerRoughScaleProduct
  apply List.prod_nonneg
  intro x hx
  obtain ⟨b, _hb, rfl⟩ := List.mem_map.mp hx
  exact locatedBlockRoughScale_nonneg R b

theorem locatedLedgerPreciseGainProduct_nonneg
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    0 ≤ locatedLedgerPreciseGainProduct Nm mu bs := by
  unfold locatedLedgerPreciseGainProduct
  apply List.prod_nonneg
  intro x hx
  obtain ⟨b, _hb, rfl⟩ := List.mem_map.mp hx
  exact locatedBlockPreciseGain_nonneg Nm mu b

theorem finAnchorOrientedDyadicEdgeGain_nonneg
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (anchor : Fin m) (cls : Fin m → ActiveNXClass Nm mu)
    (edge : AdjacentIndex m) :
    0 ≤ finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge := by
  unfold finAnchorOrientedDyadicEdgeGain
  split
  · exact dyadicForwardGain_nonneg _ _
  · exact dyadicForwardGain_nonneg _ _

/--
The two analytic runs remain separate as chains, but their target products
may be concatenated algebraically into the located ledger.
-/
theorem finAnchorNXCoarseRuns_targetProducts_eq_ledger
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℝ) (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (((finAnchorNXCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).left.map fun p =>
          nxParityBlockTarget Nm mu R p).prod *
      ((finAnchorNXCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).right.map fun p =>
          nxParityBlockTarget Nm mu R p).prod) =
      ((finAnchorNXCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O).map fun p =>
          nxParityBlockTarget Nm mu R p).prod := by
  rw [← finAnchorNXCoarseRunsWithPhases_ledger
    Nm mu leftPhase rightPhase anchor cls O]
  simp [AnchoredNXParityRuns.ledger]

/-- Every position block contains at least one position. -/
theorem length_positionBlocks_le_flatten_entries
    {α : Type*} (bs : List (PositionBlock α)) :
    bs.length ≤ (bs.flatMap PositionBlock.entries).length := by
  induction bs with
  | nil =>
      simp
  | cons b bs ih =>
      cases b <;>
        simp only [List.length_cons, List.flatMap_cons,
          PositionBlock.entries, List.length_append, List.length_nil] <;>
        omega

/-- There is at most one analytic block per paper position. -/
theorem length_finAnchorNXCoarseLedgerWithPhases_le
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O).length ≤ m := by
  let located :=
    finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O
  calc
    (finAnchorNXCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O).length =
        located.length := by
      rw [← map_analyticBlock_finAnchorNXLocatedCoarseLedgerWithPhases]
      simp [located]
    _ = (located.map LocatedNXParityBlock.positionBlock).length := by
      simp
    _ ≤ ((located.map LocatedNXParityBlock.positionBlock).flatMap
          PositionBlock.entries).length :=
      length_positionBlocks_le_flatten_entries _
    _ = m - 1 := by
      rw [show located.map LocatedNXParityBlock.positionBlock =
          finAnchorPositionScheduleWithPhases
            leftPhase rightPhase anchor by
        exact
          map_positionBlock_finAnchorNXLocatedCoarseLedgerWithPhases
            Nm mu leftPhase rightPhase anchor cls O]
      exact length_flatten_finAnchorPositionScheduleWithPhases
        leftPhase rightPhase anchor
    _ ≤ m := Nat.sub_le _ _

/-- The power of the universal local constant costs at most one factor per
paper position. -/
theorem finAnchorNXCoarseRuns_constantPower_le
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (C : ℝ) (hC : 1 ≤ C)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    C ^ ((finAnchorNXCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).left.length +
      (finAnchorNXCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).right.length) ≤
      C ^ m := by
  apply pow_le_pow_right₀ hC
  have hledger :=
    length_finAnchorNXCoarseLedgerWithPhases_le
      Nm mu leftPhase rightPhase anchor cls O
  have heq := congrArg List.length
    (finAnchorNXCoarseRunsWithPhases_ledger
      Nm mu leftPhase rightPhase anchor cls O)
  simp only [AnchoredNXParityRuns.ledger, List.length_append] at heq
  omega

/--
One-phase target-ledger bound.  All three lossy replacements are applied
with explicit nonnegativity; the retained gain is the carrier-minus-
exception product in original-edge orientation.
-/
theorem finAnchorNXCoarse_targetProduct_le_onePhaseLedger
    {t : PlaneTree} {n : ℕ}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℕ) (hRpos : 0 < R)
    (hR : accumulatedScale Nm mu (rootV t) ≤ R)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
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
  let bs :=
    finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O
  have hcommon : 0 ≤ locatedLedgerCommonProduct Nm mu bs :=
    locatedLedgerCommonProduct_nonneg Nm mu bs
  have hloss : 0 ≤ (locatedLedgerLossAtoms Nm mu bs).prod :=
    locatedLedgerLossAtoms_prod_nonneg Nm mu bs
  have hrough : 0 ≤ locatedLedgerRoughScaleProduct (R : ℝ) bs :=
    locatedLedgerRoughScaleProduct_nonneg (R : ℝ) bs
  have hprecise : 0 ≤ locatedLedgerPreciseGainProduct Nm mu bs :=
    locatedLedgerPreciseGainProduct_nonneg Nm mu bs
  have hlossBound :
      (locatedLedgerLossAtoms Nm mu bs).prod ≤
        (positionLossBase : ℝ) ^ totalMultiplicity mu := by
    exact finAnchorNXCoarse_lossAtoms_prod_le
      Nm mu leftPhase rightPhase anchor cls O
  have hroughBound :
      locatedLedgerRoughScaleProduct (R : ℝ) bs ≤
        ((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
          min (2 * O.card) 3 := by
    exact finAnchorNXLocatedCoarse_roughScaleProduct_le
      ht hroot Nm mu R hR leftPhase rightPhase anchor cls O
  have hpreciseBound :
      locatedLedgerPreciseGainProduct Nm mu bs ≤
        ∏ edge ∈
          finAnchorPositionPhaseCarrierWithPhases
              leftPhase rightPhase anchor \
            finAnchorNXExceptionalEdgesWithPhases Nm mu
              leftPhase rightPhase anchor cls O,
          finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge := by
    exact
      finAnchorNXCoarse_preciseGainProduct_le_phaseCarrier_sdiff_exception
        Nm mu leftPhase rightPhase anchor cls O
  have hlossTarget :
      0 ≤ (positionLossBase : ℝ) ^ totalMultiplicity mu := by positivity
  have hroughTarget :
      0 ≤ ((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
        min (2 * O.card) 3 := by positivity
  have hpreciseTarget :
      0 ≤ ∏ edge ∈
        finAnchorPositionPhaseCarrierWithPhases
            leftPhase rightPhase anchor \
          finAnchorNXExceptionalEdgesWithPhases Nm mu
            leftPhase rightPhase anchor cls O,
        finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge := by
    exact Finset.prod_nonneg fun edge _ =>
      finAnchorOrientedDyadicEdgeGain_nonneg Nm mu anchor cls edge
  rw [finAnchorNXCoarse_targetProduct_eq_ledgers
    Nm mu (R : ℝ) (by exact_mod_cast hRpos)
    leftPhase rightPhase anchor cls O]
  change
    locatedLedgerCommonProduct Nm mu bs *
          (locatedLedgerLossAtoms Nm mu bs).prod *
          locatedLedgerRoughScaleProduct (R : ℝ) bs *
          locatedLedgerPreciseGainProduct Nm mu bs ≤ _
  calc
    locatedLedgerCommonProduct Nm mu bs *
          (locatedLedgerLossAtoms Nm mu bs).prod *
          locatedLedgerRoughScaleProduct (R : ℝ) bs *
          locatedLedgerPreciseGainProduct Nm mu bs ≤
        locatedLedgerCommonProduct Nm mu bs *
          ((positionLossBase : ℝ) ^ totalMultiplicity mu) *
          locatedLedgerRoughScaleProduct (R : ℝ) bs *
          locatedLedgerPreciseGainProduct Nm mu bs := by
      gcongr
    _ ≤ locatedLedgerCommonProduct Nm mu bs *
          ((positionLossBase : ℝ) ^ totalMultiplicity mu) *
          (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
            min (2 * O.card) 3) *
          locatedLedgerPreciseGainProduct Nm mu bs := by
      gcongr
    _ ≤ locatedLedgerCommonProduct Nm mu bs *
          ((positionLossBase : ℝ) ^ totalMultiplicity mu) *
          (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^
            min (2 * O.card) 3) *
          (∏ edge ∈
            finAnchorPositionPhaseCarrierWithPhases
                leftPhase rightPhase anchor \
              finAnchorNXExceptionalEdgesWithPhases Nm mu
                leftPhase rightPhase anchor cls O,
            finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge) := by
      gcongr

/-! ## Original-edge reindexing and scaled phase interpolation -/

/--
The precise ledger's outward dyadic gain is definitionally the active-`P`
original-edge gain after the canonical adjacency reindexing.
-/
theorem finAnchorOrientedDyadicEdgeGain_eq_activeP
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (edge : AdjacentIndex (n + 1)) :
    finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge =
      anchoredOrientedActivePEdgeGain (1 / 8 : ℝ) anchor
        (fun i => activeNXToP Nm mu (cls i))
        (adjacentIndexSuccEquiv n edge) := by
  let j : Fin n := adjacentIndexSuccEquiv n edge
  change finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge =
    anchoredOrientedActivePEdgeGain (1 / 8 : ℝ) anchor
      (fun i => activeNXToP Nm mu (cls i)) j
  have hjcast : j.castSucc = edge.1 := by
    apply Fin.ext
    rfl
  have hjsucc : j.succ = adjacentRightPosition edge := by
    apply Fin.ext
    rfl
  by_cases hleft : edge.1.1 < anchor.1
  · have hleftj : j.1 < anchor.1 := by
      change edge.1.1 < anchor.1
      exact hleft
    rw [finAnchorOrientedDyadicEdgeGain_left_eq_reverseOriginal
      Nm mu anchor cls edge hleft]
    rw [anchoredOrientedActivePEdgeGain, if_pos hleftj]
    rw [hjcast, hjsucc]
    rfl
  · have hright : anchor.1 ≤ edge.1.1 := by omega
    have hrightj : ¬j.1 < anchor.1 := by
      change ¬edge.1.1 < anchor.1
      exact hleft
    rw [finAnchorOrientedDyadicEdgeGain_right_eq_forwardOriginal
      Nm mu anchor cls edge hright]
    rw [anchoredOrientedActivePEdgeGain, if_neg hrightj]
    rw [anchoredActivePEdgeGain]
    rw [hjcast, hjsucc]
    rfl

/-- Product form of the same reindexing on an arbitrary edge carrier. -/
theorem prod_finAnchorOrientedDyadicEdgeGain_eq_activeP
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (edges : Finset (AdjacentIndex (n + 1))) :
    (∏ edge ∈ edges,
        finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge) =
      ∏ j ∈ reindexAdjacentExceptions edges,
        anchoredOrientedActivePEdgeGain (1 / 8 : ℝ) anchor
          (fun i => activeNXToP Nm mu (cls i)) j := by
  classical
  rw [reindexAdjacentExceptions, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro edge _hedge
  exact finAnchorOrientedDyadicEdgeGain_eq_activeP
    Nm mu anchor cls edge

/--
The retained one-phase product in original adjacency coordinates is exactly
the retained active-`P` product in `Fin n` coordinates.
-/
theorem
    finAnchor_phaseOrientedDyadicProduct_eq_activeP
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    (∏ edge ∈
      finAnchorPositionPhaseCarrierWithPhases
          leftPhase rightPhase anchor \
        finAnchorNXExceptionalEdgesWithPhases Nm mu
          leftPhase rightPhase anchor cls O,
      finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge) =
      ∏ j ∈
        finAnchorPositionPhaseFinCarrierWithPhases
            leftPhase rightPhase anchor \
          finAnchorNXExceptionalFinEdgesWithPhases Nm mu
            leftPhase rightPhase anchor cls O,
        anchoredOrientedActivePEdgeGain (1 / 8 : ℝ) anchor
          (fun i => activeNXToP Nm mu (cls i)) j := by
  rw [prod_finAnchorOrientedDyadicEdgeGain_eq_activeP]
  congr 1
  exact Finset.map_sdiff _ _

/--
Geometric-mean interpolation remains valid with a common nonnegative
prefactor.  This is the form required at a fixed arrangement fiber.
-/
theorem le_mul_geometricMean_of_le_both
    {x A a b g : ℝ}
    (hx : 0 ≤ x) (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hxa : x ≤ A * a) (hxb : x ≤ A * b)
    (hg : Real.sqrt (a * b) = g) :
    x ≤ A * g := by
  calc
    x ≤ Real.sqrt ((A * a) * (A * b)) :=
      le_geometricMean_of_le_both hx
        (mul_nonneg hA ha) (mul_nonneg hA hb) hxa hxb
    _ = Real.sqrt ((A * A) * (a * b)) := by
      congr 1
      ring
    _ = Real.sqrt (A * A) * Real.sqrt (a * b) :=
      Real.sqrt_mul (mul_self_nonneg A) (a * b)
    _ = A * g := by rw [Real.sqrt_mul_self hA, hg]

/--
Concrete complementary-phase interpolation with a common prefactor.  The
exception union and exponent `1/16` are exactly those of the position
ledger.
-/
theorem finAnchorNX_two_phase_scaled_gain_bounds_le_sixteenth
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1)))
    (ratio : Fin n → ℝ) (hratio : ∀ j, 0 ≤ ratio j)
    (A x : ℝ) (hA : 0 ≤ A) (hx : 0 ≤ x)
    (hphase :
      x ≤ A *
        ∏ j ∈
          finAnchorPositionPhaseFinCarrierWithPhases
              leftPhase rightPhase anchor \
            finAnchorNXExceptionalFinEdgesWithPhases Nm mu
              leftPhase rightPhase anchor cls O,
          ratioGain (1 / 8 : ℝ) (ratio j))
    (hflip :
      x ≤ A *
        ∏ j ∈
          finAnchorPositionPhaseFinCarrierWithPhases
              (!leftPhase) (!rightPhase) anchor \
            finAnchorNXExceptionalFinEdgesWithPhases Nm mu
              (!leftPhase) (!rightPhase) anchor cls O,
          ratioGain (1 / 8 : ℝ) (ratio j)) :
    x ≤ A *
      ∏ j ∈ Finset.univ \
          finAnchorNXInterpolatedExceptionalFinEdges Nm mu
            leftPhase rightPhase anchor cls O,
        ratioGain (1 / 16 : ℝ) (ratio j) := by
  apply le_mul_geometricMean_of_le_both
    (a := ∏ j ∈
      finAnchorPositionPhaseFinCarrierWithPhases
          leftPhase rightPhase anchor \
        finAnchorNXExceptionalFinEdgesWithPhases Nm mu
          leftPhase rightPhase anchor cls O,
      ratioGain (1 / 8 : ℝ) (ratio j))
    (b := ∏ j ∈
      finAnchorPositionPhaseFinCarrierWithPhases
          (!leftPhase) (!rightPhase) anchor \
        finAnchorNXExceptionalFinEdgesWithPhases Nm mu
          (!leftPhase) (!rightPhase) anchor cls O,
      ratioGain (1 / 8 : ℝ) (ratio j))
    hx hA
  · exact Finset.prod_nonneg fun j _ =>
      ratioGain_nonneg _ (hratio j)
  · exact Finset.prod_nonneg fun j _ =>
      ratioGain_nonneg _ (hratio j)
  · exact hphase
  · exact hflip
  · exact finAnchorNX_sqrt_phase_gain_eq_sixteenth
      Nm mu leftPhase rightPhase anchor cls O ratio hratio

end XYCluster

end

end Anderson4D
