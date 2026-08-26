import Anderson4D.PermSum.SingleScaleBaseCompletion
import Anderson4D.PermSum.SingleScaleAnchorChoice

set_option warningAsError true
set_option autoImplicit false

/-!
# Word-independent minimal anchor scale

Every valid active `(N,X)` word contains every active class with its
prescribed positive multiplicity.  Consequently the value of the minimal
parent scale is independent of the ordering of the word.  Together with
the base-scale regrouping, this makes the scale coefficient used after the
fixed-fiber estimate common to the entire outer word sum.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-- Every active `(N,X)` class has positive prescribed mass. -/
theorem activeNXMultiplicity_pos
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t)
    (a : ActiveNXClass Nm mu) :
    0 < activeNXMultiplicity Nm mu a := by
  have hcard :
      0 < (leavesAtNX Nm mu a.1).card :=
    Finset.card_pos.mpr (leavesAtNX_nonempty Nm mu a.2)
  have hY :
      0 < (singleScaleSigma2 Nm mu a.1).2 := by
    have hbucket := (sigma2_bucket Nm mu a.2).2
    omega
  have hX : 0 < a.1.2 :=
    lt_of_lt_of_le Nat.zero_lt_one
      (one_le_nxClass_X Nm mu a.2)
  have hlower :=
    (multiplicityNX_bounds Nm mu a.2).1
  change 0 < multiplicityNX Nm mu a.1
  exact (Nat.mul_pos hX hY).trans_le hlower

/-- Every active letter occurs somewhere in every valid active word. -/
theorem exists_position_eq_activeNXClass_of_valid
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m)
      (activeNXMultiplicity Nm mu))
    (a : ActiveNXClass Nm mu) :
    ∃ i : Fin m, x i = a := by
  have hcount :=
    (Finset.mem_filter.mp hx).2 a
  have hpos :
      0 <
        ((Finset.univ : Finset (Fin m)).filter
          fun i => x i = a).card := by
    rw [hcount]
    exact activeNXMultiplicity_pos Nm mu a
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

/-- The minimal parent-scale value does not depend on the ordering of a
valid active word. -/
theorem totalMultiplicityNXScaleAnchor_scale_eq_of_valid
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (x y : Fin (totalMultiplicity mu) →
      ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := totalMultiplicity mu)
      (activeNXMultiplicity Nm mu))
    (hy : y ∈ validWords (M := totalMultiplicity mu)
      (activeNXMultiplicity Nm mu)) :
    (x (totalMultiplicityNXScaleAnchor Nm mu x)).1.1 =
      (y (totalMultiplicityNXScaleAnchor Nm mu y)).1.1 := by
  apply Nat.le_antisymm
  · obtain ⟨i, hi⟩ :=
      exists_position_eq_activeNXClass_of_valid
        Nm mu x hx
        (y (totalMultiplicityNXScaleAnchor Nm mu y))
    calc
      (x (totalMultiplicityNXScaleAnchor Nm mu x)).1.1 ≤
          (x i).1.1 :=
        totalMultiplicityNXScaleAnchor_le Nm mu x i
      _ =
          (y (totalMultiplicityNXScaleAnchor Nm mu y)).1.1 := by
        rw [hi]
  · obtain ⟨i, hi⟩ :=
      exists_position_eq_activeNXClass_of_valid
        Nm mu y hy
        (x (totalMultiplicityNXScaleAnchor Nm mu x))
    calc
      (y (totalMultiplicityNXScaleAnchor Nm mu y)).1.1 ≤
          (y i).1.1 :=
        totalMultiplicityNXScaleAnchor_le Nm mu y i
      _ =
          (x (totalMultiplicityNXScaleAnchor Nm mu x)).1.1 := by
        rw [hi]

/-- The full word base-scale product is likewise independent of the
ordering of a valid active word. -/
theorem nxWordBaseScaleFactor_eq_of_valid
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (x y : Fin (totalMultiplicity mu) →
      ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := totalMultiplicity mu)
      (activeNXMultiplicity Nm mu))
    (hy : y ∈ validWords (M := totalMultiplicity mu)
      (activeNXMultiplicity Nm mu)) :
    nxWordBaseScaleFactor x = nxWordBaseScaleFactor y := by
  rw [nxWordBaseScaleFactor_eq_leafProduct Nm mu x hx,
    nxWordBaseScaleFactor_eq_leafProduct Nm mu y hy]

/-- The completed base-scale coefficient appearing after anchor
completion is common to all valid active words. -/
theorem completedNXWordBaseScaleFactor_eq_of_valid
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (x y : Fin (totalMultiplicity mu) →
      ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := totalMultiplicity mu)
      (activeNXMultiplicity Nm mu))
    (hy : y ∈ validWords (M := totalMultiplicity mu)
      (activeNXMultiplicity Nm mu)) :
    nxWordBaseScaleFactor x *
          ((x (totalMultiplicityNXScaleAnchor Nm mu x)).1.1 : ℝ) ^ 2 =
      nxWordBaseScaleFactor y *
          ((y (totalMultiplicityNXScaleAnchor Nm mu y)).1.1 : ℝ) ^ 2 := by
  rw [nxWordBaseScaleFactor_eq_of_valid Nm mu x y hx hy,
    totalMultiplicityNXScaleAnchor_scale_eq_of_valid Nm mu x y hx hy]

end XYCluster

end

end Anderson4D
