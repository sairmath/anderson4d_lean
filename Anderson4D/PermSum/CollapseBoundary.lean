import Anderson4D.HeppTree.ScaleGeometric
import Anderson4D.PermSum.CollapseEligible
import Anderson4D.PermSum.CollapseGeometry

/-!
# Boundary separation for the collapse step

For an eligible branch `r`, every point inside its subtree is much closer to
the chosen inside representative than to any outside point.  The strong
quarter-distance form below is the geometric input needed to charge each
changed boundary edge by `2`; the weaker printed comparison (5.41) alone
would not retain the paper's final `4^n` ledger.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree

/-- If `r` is a prefix of `p` but not of `q`, the longest common prefix of
`p` and `q` is a prefix of `r`. -/
theorem lcaPath_prefix_of_prefix_not_prefix
    {r p q : List ℕ} (hp : r <+: p) (hq : ¬r <+: q) :
    lcaPath p q <+: r := by
  induction r generalizing p q with
  | nil =>
      exact (hq List.nil_prefix).elim
  | cons a r ih =>
      cases p with
      | nil =>
          exact absurd hp (by simp)
      | cons b p =>
          obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
          cases q with
          | nil =>
              simp [lcaPath]
          | cons c q =>
              by_cases hac : a = c
              · subst c
                have hq' : ¬r <+: q := by
                  intro hrq
                  apply hq
                  exact List.cons_prefix_cons.mpr ⟨rfl, hrq⟩
                simp only [lcaPath, ↓reduceIte]
                exact List.cons_prefix_cons.mpr ⟨rfl, ih hp' hq'⟩
              · simp [lcaPath, hac]

/-- A proper prefix remains a prefix after deleting the final entry of the
longer path. -/
theorem prefix_dropLast_of_prefix_ne
    {p q : List ℕ} (hpq : p <+: q) (hne : p ≠ q) :
    p <+: q.dropLast := by
  let s := List.drop p.length q
  have heq : p ++ s = q :=
    List.prefix_iff_eq_append.mp hpq
  have hs : s ≠ [] := by
    intro hs
    apply hne
    simpa [s, hs] using heq
  rw [← heq, List.dropLast_append_of_ne_nil hs]
  exact List.prefix_append _ _

/-- The LCA of an inside and an outside vertex is an ancestor of the parent
of the collapsed root. -/
theorem lcaV_ancestor_parent_of_prefix_not_prefix
    {t : PlaneTree} {r x y : VPos t}
    (hx : r.1 <+: x.1) (hy : ¬r.1 <+: y.1) :
    IsAncestor (lcaV x y) (parentV r) := by
  apply isAncestor_of_prefix
  have hlca : lcaPath x.1 y.1 <+: r.1 :=
    lcaPath_prefix_of_prefix_not_prefix hx hy
  have hne : lcaPath x.1 y.1 ≠ r.1 := by
    intro h
    apply hy
    rw [← h]
    exact lcaPath_prefix_right x.1 y.1
  exact prefix_dropLast_of_prefix_ne hlca hne

/-- The parent scale of an eligible collapsed root is no larger than the LCA
scale of an inside/outside pair. -/
theorem parentScale_le_lcaScale_of_inside_outside
    {t : PlaneTree} (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {r : VPos t} (hr : CollapseEligible Nm mu r)
    {l y : HeppLeaf t}
    (hl : l ∈ leavesUnder r) (hy : y ∉ leavesUnder r) :
    scaleN Nm (parentV r) ≤ scaleN Nm (lcaV l.1 y.1) := by
  have hrmem :=
    Finset.mem_erase.mp hr.1
  have hrne : r ≠ rootV t := hrmem.1
  have hrbranch : r ∈ BranchNodes t := hrmem.2
  have hpbranch :
      parentV r ∈ BranchNodes t :=
    parentV_mem_BranchNodes_of_isValid ht hrne
  have hlprefix : r.1 <+: l.1.1 :=
    mem_leavesUnder.mp hl
  have hynot : ¬r.1 <+: y.1.1 := by
    intro h
    exact hy (mem_leavesUnder.mpr h)
  have hancestor :
      IsAncestor (lcaV l.1 y.1) (parentV r) :=
    lcaV_ancestor_parent_of_prefix_not_prefix hlprefix hynot
  have hmarked :=
    scaleN_mul_two_pow_ancestorGap_le
      ht Nm hancestor hpbranch
  have hfirst :
      scaleN Nm (parentV r) ≤
        scaleN Nm (parentV r) *
          2 ^ ancestorGap (parentV r) (lcaV l.1 y.1) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  exact hfirst.trans hmarked

/-- Strong boundary estimate behind (5.41):
`4 |z_l-z_l*| ≤ |z_y-z_l|`. -/
theorem eligible_boundary_quarter
    {t : PlaneTree} (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : CollapseEligible Nm mu r)
    {l lstar y : HeppLeaf t}
    (hl : l ∈ leavesUnder r)
    (hlstar : lstar ∈ leavesUnder r)
    (hy : y ∉ leavesUnder r) :
    4 * znorm (z l - z lstar) ≤ znorm (z y - z l) := by
  have hrbranch : r ∈ BranchNodes t :=
    (Finset.mem_erase.mp hr.1).2
  have hinside :=
    hdiam r hrbranch l hl lstar hlstar
  have hparentLca :=
    parentScale_le_lcaScale_of_inside_outside
      ht Nm mu hr hl hy
  have hly : l ≠ y := by
    intro h
    subst y
    exact hy hl
  have hseparation :=
    hsep.2 l y hly
  have helig : 8 * accumulatedScale Nm mu r ≤
      scaleN Nm (parentV r) :=
    hr.2
  have heligReal :
      (8 : ℝ) * accumulatedScale Nm mu r ≤
        scaleN Nm (parentV r) := by
    exact_mod_cast helig
  have hparentLcaReal :
      (scaleN Nm (parentV r) : ℝ) ≤
        scaleN Nm (lcaV l.1 y.1) := by
    exact_mod_cast hparentLca
  have hdistSymm :
      znorm (z l - z y) = znorm (z y - z l) :=
    znorm_sub_comm (z l) (z y)
  rw [hdistSymm] at hseparation
  nlinarith

/-- Paper's weak two-sided comparison (5.41), derived from the strong
quarter estimate and retained as a tree-facing corollary. -/
theorem eligible_boundary_comparable
    {t : PlaneTree} (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : CollapseEligible Nm mu r)
    {l lstar y : HeppLeaf t}
    (hl : l ∈ leavesUnder r)
    (hlstar : lstar ∈ leavesUnder r)
    (hy : y ∉ leavesUnder r) :
    znorm (z y - z l) ≤ 2 * znorm (z y - z lstar) ∧
      znorm (z y - z lstar) ≤ 2 * znorm (z y - z l) := by
  exact collapse_distance_comparable
    (z y) (z l) (z lstar)
    (eligible_boundary_quarter ht Nm mu z hsep hdiam hr hl hlstar hy)

end Anderson4D
