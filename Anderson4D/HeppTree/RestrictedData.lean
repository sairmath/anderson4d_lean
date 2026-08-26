import Anderson4D.HeppTree.Basic

/-!
# Restricted Hepp data

`HeppMarking.Nexp` and `Multiplicities.m` are stored as total functions on
vertices, although paper Definition 5.1 only gives them meaning on branching
vertices and leaves, respectively.  This file supplies canonical zero
extensions and equality interfaces which forget the off-support junk.

In particular, `AutHeppMarked t Nm` is the stabilizer of the canonical raw
marking, rather than of `Nm.Nexp` itself.  Thus neither this group nor its
orbit--stabilizer count can depend on values of `Nexp` away from
`BranchNodes t`.
-/

namespace Anderson4D

namespace PlaneTree

namespace HeppMarking

/-- The marking data of `Nm`, extended by zero away from the branching
vertices.  This is the raw marking on which automorphisms should act. -/
def canonicalRaw {t : PlaneTree} (Nm : HeppMarking t) : Marking t :=
  fun v => if v ∈ BranchNodes t then Nm.Nexp v else 0

@[simp] theorem canonicalRaw_apply_of_mem {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (hv : v ∈ BranchNodes t) :
    Nm.canonicalRaw v = Nm.Nexp v := by
  simp [canonicalRaw, hv]

@[simp] theorem canonicalRaw_apply_of_not_mem {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (hv : v ∉ BranchNodes t) :
    Nm.canonicalRaw v = 0 := by
  simp [canonicalRaw, hv]

/-- Semantic equality of Hepp markings: equality only at branching vertices.
The total-function fields may differ away from `BranchNodes t`. -/
def EqOnBranch {t : PlaneTree} (Nm Nm' : HeppMarking t) : Prop :=
  ∀ v ∈ BranchNodes t, Nm.Nexp v = Nm'.Nexp v

theorem eqOnBranch_refl {t : PlaneTree} (Nm : HeppMarking t) :
    EqOnBranch Nm Nm := by
  intro v hv
  rfl

theorem eqOnBranch_symm {t : PlaneTree} {Nm Nm' : HeppMarking t}
    (h : EqOnBranch Nm Nm') : EqOnBranch Nm' Nm := by
  intro v hv
  exact (h v hv).symm

theorem eqOnBranch_trans {t : PlaneTree} {Nm₁ Nm₂ Nm₃ : HeppMarking t}
    (h₁₂ : EqOnBranch Nm₁ Nm₂) (h₂₃ : EqOnBranch Nm₂ Nm₃) :
    EqOnBranch Nm₁ Nm₃ := by
  intro v hv
  exact (h₁₂ v hv).trans (h₂₃ v hv)

/-- Two Hepp markings have the same canonical raw marking exactly when their
meaningful values agree on every branching vertex. -/
theorem canonicalRaw_eq_iff {t : PlaneTree} {Nm Nm' : HeppMarking t} :
    Nm.canonicalRaw = Nm'.canonicalRaw ↔ EqOnBranch Nm Nm' := by
  constructor
  · intro h v hv
    have hv' := congrFun h v
    simpa [canonicalRaw, hv] using hv'
  · intro h
    funext v
    by_cases hv : v ∈ BranchNodes t
    · simp [canonicalRaw, hv, h v hv]
    · simp [canonicalRaw, hv]

/-- Extensionality for canonical raw markings: only branch values need be
compared. -/
theorem canonicalRaw_ext {t : PlaneTree} {Nm Nm' : HeppMarking t}
    (h : ∀ v ∈ BranchNodes t, Nm.Nexp v = Nm'.Nexp v) :
    Nm.canonicalRaw = Nm'.canonicalRaw :=
  canonicalRaw_eq_iff.mpr h

end HeppMarking

/-- Automorphisms of the marked Hepp tree `(t, Nm)`.  The stabilizer is taken
after zero-extending `Nm` away from the branching vertices, so it is
independent of the junk values in the total field `Nm.Nexp`. -/
abbrev AutHeppMarked (t : PlaneTree) (Nm : HeppMarking t) : Subgroup (Aut t) :=
  AutMarked t Nm.canonicalRaw

@[simp] theorem mem_autHeppMarked_iff {t : PlaneTree} {Nm : HeppMarking t}
    {g : Aut t} :
    g ∈ AutHeppMarked t Nm ↔ g • Nm.canonicalRaw = Nm.canonicalRaw :=
  MulAction.mem_stabilizer_iff

/-- Semantically equal markings have literally the same marked-tree
automorphism subgroup. -/
theorem autHeppMarked_congr {t : PlaneTree} {Nm Nm' : HeppMarking t}
    (h : HeppMarking.EqOnBranch Nm Nm') :
    AutHeppMarked t Nm = AutHeppMarked t Nm' := by
  rw [AutHeppMarked, AutHeppMarked, HeppMarking.canonicalRaw_eq_iff.mpr h]

/-- Orbit--stabilizer for the paper-faithful marked-tree automorphism group.
No value of `Nm.Nexp` away from `BranchNodes t` occurs in this statement. -/
theorem card_orbit_mul_card_autHeppMarked (t : PlaneTree) (Nm : HeppMarking t) :
    (MulAction.orbit (Aut t) Nm.canonicalRaw).toFinset.card
        * Fintype.card (AutHeppMarked t Nm)
      = Fintype.card (Aut t) :=
  card_orbit_mul_card_autMarked t Nm.canonicalRaw

namespace Multiplicities

/-- The multiplicity data of `mu`, extended by zero away from the leaves. -/
def canonicalRaw {t : PlaneTree} (mu : Multiplicities t) : VPos t → ℕ :=
  fun v => if v ∈ Leaves t then mu.m v else 0

@[simp] theorem canonicalRaw_apply_of_mem {t : PlaneTree} (mu : Multiplicities t)
    {v : VPos t} (hv : v ∈ Leaves t) :
    mu.canonicalRaw v = mu.m v := by
  simp [canonicalRaw, hv]

@[simp] theorem canonicalRaw_apply_of_not_mem {t : PlaneTree} (mu : Multiplicities t)
    {v : VPos t} (hv : v ∉ Leaves t) :
    mu.canonicalRaw v = 0 := by
  simp [canonicalRaw, hv]

/-- Semantic equality of multiplicities: equality only at leaves. -/
def EqOnLeaves {t : PlaneTree} (mu mu' : Multiplicities t) : Prop :=
  ∀ v ∈ Leaves t, mu.m v = mu'.m v

theorem eqOnLeaves_refl {t : PlaneTree} (mu : Multiplicities t) :
    EqOnLeaves mu mu := by
  intro v hv
  rfl

theorem eqOnLeaves_symm {t : PlaneTree} {mu mu' : Multiplicities t}
    (h : EqOnLeaves mu mu') : EqOnLeaves mu' mu := by
  intro v hv
  exact (h v hv).symm

theorem eqOnLeaves_trans {t : PlaneTree} {mu₁ mu₂ mu₃ : Multiplicities t}
    (h₁₂ : EqOnLeaves mu₁ mu₂) (h₂₃ : EqOnLeaves mu₂ mu₃) :
    EqOnLeaves mu₁ mu₃ := by
  intro v hv
  exact (h₁₂ v hv).trans (h₂₃ v hv)

/-- Two multiplicity structures have the same canonical raw function exactly
when their meaningful values agree at every leaf. -/
theorem canonicalRaw_eq_iff {t : PlaneTree} {mu mu' : Multiplicities t} :
    mu.canonicalRaw = mu'.canonicalRaw ↔ EqOnLeaves mu mu' := by
  constructor
  · intro h v hv
    have hv' := congrFun h v
    simpa [canonicalRaw, hv] using hv'
  · intro h
    funext v
    by_cases hv : v ∈ Leaves t
    · simp [canonicalRaw, hv, h v hv]
    · simp [canonicalRaw, hv]

/-- Extensionality for canonical multiplicity functions: only leaf values
need be compared. -/
theorem canonicalRaw_ext {t : PlaneTree} {mu mu' : Multiplicities t}
    (h : ∀ v ∈ Leaves t, mu.m v = mu'.m v) :
    mu.canonicalRaw = mu'.canonicalRaw :=
  canonicalRaw_eq_iff.mpr h

end Multiplicities

end PlaneTree

end Anderson4D
