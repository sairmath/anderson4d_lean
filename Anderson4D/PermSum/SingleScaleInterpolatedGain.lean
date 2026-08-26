import Anderson4D.PermSum.SingleScalePhaseAssembly

set_option warningAsError true
set_option autoImplicit false

/-!
# The interpolated gain in active-`P` coordinates

The two complementary elimination phases produce an oriented dyadic ratio
on every retained original edge.  This file records the ratio itself and
identifies the interpolated `1/16` product with the active-`P` weight used
by the outer sequence estimate.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-- The positive active-`P` ratio on an original adjacency, oriented away
from the distinguished anchor. -/
noncomputable def finAnchorOrientedActivePRatio
    {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {n : ℕ}
    (anchor : Fin (n + 1))
    (w : Fin (n + 1) → ActivePClass Nm mu)
    (j : Fin n) : ℝ :=
  if j.1 < anchor.1 then
    (((w j.castSucc).1 : ℕ) : ℝ) /
      (((w j.succ).1 : ℕ) : ℝ)
  else
    (((w j.succ).1 : ℕ) : ℝ) /
      (((w j.castSucc).1 : ℕ) : ℝ)

theorem finAnchorOrientedActivePRatio_nonneg
    {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {n : ℕ}
    (anchor : Fin (n + 1))
    (w : Fin (n + 1) → ActivePClass Nm mu)
    (j : Fin n) :
    0 ≤ finAnchorOrientedActivePRatio anchor w j := by
  unfold finAnchorOrientedActivePRatio
  split <;> positivity

/-- The active-`P` edge gain is literally `ratioGain` of the outward
oriented ratio, for every exponent. -/
theorem anchoredOrientedActivePEdgeGain_eq_ratioGain
    (theta : ℝ)
    {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {n : ℕ}
    (anchor : Fin (n + 1))
    (w : Fin (n + 1) → ActivePClass Nm mu)
    (j : Fin n) :
    anchoredOrientedActivePEdgeGain theta anchor w j =
      ratioGain theta (finAnchorOrientedActivePRatio anchor w j) := by
  unfold anchoredOrientedActivePEdgeGain
    finAnchorOrientedActivePRatio ratioGain
  split <;> rfl

/-- The retained one-phase dyadic product is the `1/8` product of the
same outward ratios later used for interpolation. -/
theorem finAnchor_phaseOrientedDyadicProduct_eq_ratioGain
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (n + 1))
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
        ratioGain (1 / 8 : ℝ)
          (finAnchorOrientedActivePRatio anchor
            (fun i => activeNXToP Nm mu (cls i)) j) := by
  rw [finAnchor_phaseOrientedDyadicProduct_eq_activeP]
  apply Finset.prod_congr rfl
  intro j _hj
  exact anchoredOrientedActivePEdgeGain_eq_ratioGain
    (1 / 8 : ℝ) anchor
    (fun i => activeNXToP Nm mu (cls i)) j

/--
The concrete interpolated product is exactly the class-independent
positional active-`P` weight consumed by the outer sequence theorem.
-/
theorem finAnchorNX_interpolatedGain_eq_orientedActivePWeight
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    (∏ j ∈ Finset.univ \
        finAnchorNXInterpolatedExceptionalFinEdges Nm mu
          leftPhase rightPhase anchor cls O,
      ratioGain (1 / 16 : ℝ)
        (finAnchorOrientedActivePRatio anchor
          (fun i => activeNXToP Nm mu (cls i)) j)) =
      anchoredOrientedActivePWeight (1 / 16 : ℝ)
        (finAnchorPositionalInterpolatedExceptionalFinEdges
          leftPhase rightPhase anchor O)
        anchor (fun i => activeNXToP Nm mu (cls i)) := by
  rw [finAnchorNXInterpolatedExceptionalFinEdges_eq_positional]
  unfold anchoredOrientedActivePWeight
  apply Finset.prod_congr rfl
  intro j _hj
  exact
    (anchoredOrientedActivePEdgeGain_eq_ratioGain
      (1 / 16 : ℝ) anchor
      (fun i => activeNXToP Nm mu (cls i)) j).symm

end XYCluster

end

end Anderson4D
