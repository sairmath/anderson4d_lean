import Anderson4D.PermSum.SingleScaleClassFubini
import Anderson4D.PermSum.SingleScaleSequence

/-!
# Deterministic minimal-scale anchors

Step 4 of the proof of Proposition 5.10 cuts a class word at a position
whose parent scale is minimal.  This file makes that choice deterministic
and proves that it depends only on the fixed `(N,X)` word, not on a labeled
arrangement in its fiber.
-/

namespace Anderson4D

open PlaneTree

noncomputable section

/-- A deterministic position at which the first coordinate of an active
`(N,X)` word is minimal. -/
noncomputable def minimalNXScaleAnchor
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    {m : ℕ} (hm : 0 < m) (x : Fin m → ActiveNXClass Nm mu) : Fin m :=
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  Function.argmin fun i => (x i).1.1

theorem minimalNXScaleAnchor_le
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    {m : ℕ} (hm : 0 < m) (x : Fin m → ActiveNXClass Nm mu)
    (i : Fin m) :
    (x (minimalNXScaleAnchor hm x)).1.1 ≤ (x i).1.1 := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  exact Function.argmin_le (fun j => (x j).1.1) i

/-- Paper-length anchor; `totalMultiplicity ≥ 2` makes the carrier
nonempty without an additional hypothesis. -/
noncomputable def totalMultiplicityNXScaleAnchor
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) :
    Fin (totalMultiplicity mu) :=
  minimalNXScaleAnchor (lt_of_lt_of_le (by omega)
    (two_le_totalMultiplicity mu)) x

theorem totalMultiplicityNXScaleAnchor_le
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (i : Fin (totalMultiplicity mu)) :
    (x (totalMultiplicityNXScaleAnchor Nm mu x)).1.1 ≤ (x i).1.1 :=
  minimalNXScaleAnchor_le
    (lt_of_lt_of_le (by omega) (two_le_totalMultiplicity mu)) x i

theorem mem_arrangementsAtNXWord_iff
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (σ : HeppArrangement mu) :
    σ ∈ arrangementsAtNXWord Nm mu x ↔
      arrangementNXWord Nm mu σ = x := by
  simp [arrangementsAtNXWord]

/-- Every arrangement in a fixed `(N,X)`-word fiber has exactly the class
word's parent scale at each position. -/
theorem arrangement_parentScale_eq_NXWord
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (σ : HeppArrangement mu) (hσ : σ ∈ arrangementsAtNXWord Nm mu x)
    (i : Fin (totalMultiplicity mu)) :
    scaleN Nm (parentV (σ i).1.1) = (x i).1.1 := by
  have hword := congrFun
    ((mem_arrangementsAtNXWord_iff Nm mu x σ).mp hσ) i
  exact congrArg Prod.fst (congrArg Subtype.val hword)

/--
The distinguished labeled copy selected at the deterministic word anchor
has minimal parent scale among all positions of every arrangement in the
fiber.
-/
theorem arrangement_anchor_parentScale_minimal
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (σ : HeppArrangement mu) (hσ : σ ∈ arrangementsAtNXWord Nm mu x)
    (i : Fin (totalMultiplicity mu)) :
    scaleN Nm
        (parentV
          (σ (totalMultiplicityNXScaleAnchor Nm mu x)).1.1) ≤
      scaleN Nm (parentV (σ i).1.1) := by
  rw [arrangement_parentScale_eq_NXWord Nm mu x σ hσ,
    arrangement_parentScale_eq_NXWord Nm mu x σ hσ]
  exact totalMultiplicityNXScaleAnchor_le Nm mu x i

end

end Anderson4D
