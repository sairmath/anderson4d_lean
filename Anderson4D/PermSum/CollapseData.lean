import Anderson4D.HeppTree.SubtreeCollapse
import Anderson4D.PermSum.Statements

/-!
# Data transport for the subtree-collapse induction

This file transports markings, multiplicities, and leaf carriers through the
two tree operations used in paper §5.4.1:

* restriction to the rooted subtree at `r`;
* contraction of that subtree to the marker leaf at `r`.

The constructions preserve all meaningful values definitionally.  The
theorems below expose the resulting scale and multiplicity ledgers without
depending on the later word, geometry, or summation layers.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## Parent transport -/

/-- Prepending a fixed subtree root commutes with the parent map away from
the root of the smaller tree. -/
theorem parentV_subtreeVertex {t : PlaneTree} (r : VPos t)
    (v : VPos (subtreeAt t r.1))
    (hv : v ≠ rootV (subtreeAt t r.1)) :
    parentV (subtreeVertex r v) = subtreeVertex r (parentV v) := by
  apply Subtype.ext
  change (r.1 ++ v.1).dropLast = r.1 ++ v.1.dropLast
  exact List.dropLast_append_of_ne_nil (ne_root_iff.mp hv)

/-- The unchanged paths in a contracted tree make its vertex inclusion
commute with the parent map. -/
theorem parentV_contractVertex {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) (v : VPos (contractAt t p)) :
    parentV (contractVertex hp v) =
      contractVertex hp (parentV v) := by
  apply Subtype.ext
  rfl

/-! ## Markings -/

/-- Restrict a Hepp marking to the actual rooted subtree at `r`. -/
def restrictMarking {t : PlaneTree} (Nm : HeppMarking t) (r : VPos t) :
    HeppMarking (subtreeAt t r.1) where
  Nexp v := Nm.Nexp (subtreeVertex r v)
  pos v hv := Nm.pos (subtreeVertex r v)
    ((mem_BranchNodes_subtreeVertex_iff r v).mp hv)
  parent_gt v hv hv0 := by
    have hvBranch :
        subtreeVertex r v ∈ BranchNodes t :=
      (mem_BranchNodes_subtreeVertex_iff r v).mp hv
    have hvRoot : subtreeVertex r v ≠ rootV t := by
      intro h
      apply hv0
      apply Subtype.ext
      have hval := congrArg Subtype.val h
      have happ : r.1 ++ v.1 = [] := by
        simpa [rootV] using hval
      exact (List.append_eq_nil_iff.mp happ).2
    simpa only [parentV_subtreeVertex r v hv0] using
      Nm.parent_gt (subtreeVertex r v) hvBranch hvRoot

/-- Restricting a marking preserves every subtree scale exactly. -/
@[simp]
theorem scaleN_restrictMarking {t : PlaneTree} (Nm : HeppMarking t)
    (r : VPos t) (v : VPos (subtreeAt t r.1)) :
    scaleN (restrictMarking Nm r) v =
      scaleN Nm (subtreeVertex r v) :=
  rfl

/-- Contract a Hepp marking by retaining the exponent of every surviving
branch.  The marker is a leaf, so its stored exponent is irrelevant. -/
def contractMarking {t : PlaneTree} (Nm : HeppMarking t) (r : VPos t) :
    HeppMarking (contractAt t r.1) where
  Nexp v := Nm.Nexp (contractVertex r.2 v)
  pos v hv := by
    have hvPrefix :
        ¬r.1 <+: v.1 :=
      not_prefix_of_mem_BranchNodes_contractAt r.2 v hv
    have hvNe : v.1 ≠ r.1 := by
      intro h
      exact hvPrefix (by rw [h])
    exact Nm.pos (contractVertex r.2 v)
      ((mem_BranchNodes_contractVertex_iff_of_ne r.2 v hvNe).mp hv)
  parent_gt v hv hv0 := by
    have hvPrefix :
        ¬r.1 <+: v.1 :=
      not_prefix_of_mem_BranchNodes_contractAt r.2 v hv
    have hvNe : v.1 ≠ r.1 := by
      intro h
      exact hvPrefix (by rw [h])
    have hvBranch :
        contractVertex r.2 v ∈ BranchNodes t :=
      (mem_BranchNodes_contractVertex_iff_of_ne r.2 v hvNe).mp hv
    have hvRoot : contractVertex r.2 v ≠ rootV t := by
      intro h
      apply hv0
      apply Subtype.ext
      have hval := congrArg Subtype.val h
      simpa [contractVertex, rootV] using hval
    simpa only [parentV_contractVertex r.2 v] using
      Nm.parent_gt (contractVertex r.2 v) hvBranch hvRoot

/-- Contracting a marking preserves every surviving branch scale exactly. -/
@[simp]
theorem scaleN_contractMarking {t : PlaneTree} (Nm : HeppMarking t)
    (r : VPos t) (v : VPos (contractAt t r.1)) :
    scaleN (contractMarking Nm r) v =
      scaleN Nm (contractVertex r.2 v) :=
  rfl

/-! ## Inside and outside leaf carriers -/

/-- Original leaves weakly below the selected subtree root. -/
abbrev InsideLeaf {t : PlaneTree} (r : VPos t) : Type :=
  {l : HeppLeaf t // r.1 <+: l.1.1}

/-- Original leaves outside the selected rooted subtree. -/
abbrev OutsideLeaf {t : PlaneTree} (r : VPos t) : Type :=
  {l : HeppLeaf t // ¬r.1 <+: l.1.1}

/-- Every original leaf is uniquely either inside or outside the selected
rooted subtree. -/
def leafInsideOutsideEquiv {t : PlaneTree} (r : VPos t) :
    HeppLeaf t ≃ InsideLeaf r ⊕ OutsideLeaf r where
  toFun l :=
    if h : r.1 <+: l.1.1 then
      Sum.inl ⟨l, h⟩
    else
      Sum.inr ⟨l, h⟩
  invFun
    | Sum.inl l => l.1
    | Sum.inr l => l.1
  left_inv l := by
    by_cases h : r.1 <+: l.1.1 <;> simp [h]
  right_inv l := by
    cases l with
    | inl l => simp [l.2]
    | inr l => simp [l.2]

/-- The leaves of the rooted subtree are exactly the original inside leaves. -/
def restrictLeafEquiv {t : PlaneTree} (r : VPos t) :
    HeppLeaf (subtreeAt t r.1) ≃ InsideLeaf r :=
  (subtreeLeafEquivLeavesUnder r).trans
    (Equiv.subtypeEquiv (Equiv.refl (HeppLeaf t)) fun _l => mem_leavesUnder)

/-- The distinguished marker leaf in the contracted tree. -/
def contractMarkerLeaf {t : PlaneTree} (r : VPos t) :
    HeppLeaf (contractAt t r.1) :=
  ⟨contractMarker t r.1 r.2, contractMarker_mem_Leaves t r.1 r.2⟩

/-- Contracted leaves are the marker together with all unchanged outside
leaves. -/
def contractLeafSumEquiv {t : PlaneTree} (r : VPos t) :
    HeppLeaf (contractAt t r.1) ≃ Unit ⊕ OutsideLeaf r where
  toFun l :=
    match contractLeafEquiv r.2 l with
    | none => Sum.inl ()
    | some l => Sum.inr l
  invFun
    | Sum.inl _ => (contractLeafEquiv r.2).symm none
    | Sum.inr l => (contractLeafEquiv r.2).symm (some l)
  left_inv l := by
    cases h : contractLeafEquiv r.2 l with
    | none =>
        simpa [h] using (contractLeafEquiv r.2).symm_apply_apply l
    | some l' =>
        simpa [h] using (contractLeafEquiv r.2).symm_apply_apply l
  right_inv l := by
    cases l with
    | inl u =>
        cases u
        simp
    | inr l =>
        simp

@[simp]
theorem contractLeafSumEquiv_marker {t : PlaneTree} (r : VPos t) :
    contractLeafSumEquiv r (contractMarkerLeaf r) = Sum.inl () := by
  simp [contractLeafSumEquiv, contractMarkerLeaf, contractLeafEquiv]

/-! ## Canonical leaves, compound sets, and embeddings -/

/-- View a chosen original inside leaf as a leaf of the restricted subtree. -/
def restrictInsideLeaf {t : PlaneTree} (r : VPos t) (l : InsideLeaf r) :
    HeppLeaf (subtreeAt t r.1) :=
  (restrictLeafEquiv r).symm l

@[simp]
theorem subtreeVertex_restrictInsideLeaf {t : PlaneTree} (r : VPos t)
    (l : InsideLeaf r) :
    subtreeVertex r (restrictInsideLeaf r l).1 = l.1.1 := by
  change (restrictLeafEquiv r (restrictInsideLeaf r l)).1.1 = l.1.1
  exact congrArg (fun x : InsideLeaf r => x.1.1)
    ((restrictLeafEquiv r).apply_symm_apply l)

/-- View an original outside leaf as the corresponding unchanged leaf of the
contracted tree. -/
def contractOutsideLeaf {t : PlaneTree} (r : VPos t) (l : OutsideLeaf r) :
    HeppLeaf (contractAt t r.1) :=
  (contractLeafSumEquiv r).symm (Sum.inr l)

@[simp]
theorem contractLeafSumEquiv_contractOutsideLeaf {t : PlaneTree}
    (r : VPos t) (l : OutsideLeaf r) :
    contractLeafSumEquiv r (contractOutsideLeaf r l) = Sum.inr l :=
  (contractLeafSumEquiv r).apply_symm_apply _

@[simp]
theorem contractVertex_contractOutsideLeaf {t : PlaneTree}
    (r : VPos t) (l : OutsideLeaf r) :
    contractVertex r.2 (contractOutsideLeaf r l).1 = l.1.1 := by
  rfl

/-- Restrict a vertex set to the selected subtree.  Applied to the paper's
compound-leaf set, only its inside leaves survive. -/
def restrictCompound {t : PlaneTree} (r : VPos t)
    (compound : Finset (VPos t)) :
    Finset (VPos (subtreeAt t r.1)) :=
  Finset.univ.filter fun v => subtreeVertex r v ∈ compound

@[simp]
theorem mem_restrictCompound {t : PlaneTree} (r : VPos t)
    (compound : Finset (VPos t)) (v : VPos (subtreeAt t r.1)) :
    v ∈ restrictCompound r compound ↔ subtreeVertex r v ∈ compound := by
  simp [restrictCompound]

/-- Contract a compound-leaf set.  The marker is declared compound, and an
unchanged outside vertex is compound exactly when its original vertex was. -/
def contractCompound {t : PlaneTree} (r : VPos t)
    (compound : Finset (VPos t)) :
    Finset (VPos (contractAt t r.1)) :=
  Finset.univ.filter fun v =>
    v.1 = r.1 ∨ contractVertex r.2 v ∈ compound

@[simp]
theorem mem_contractCompound {t : PlaneTree} (r : VPos t)
    (compound : Finset (VPos t)) (v : VPos (contractAt t r.1)) :
    v ∈ contractCompound r compound ↔
      v.1 = r.1 ∨ contractVertex r.2 v ∈ compound := by
  simp [contractCompound]

@[simp]
theorem contractMarker_mem_contractCompound {t : PlaneTree} (r : VPos t)
    (compound : Finset (VPos t)) :
    contractMarker t r.1 r.2 ∈ contractCompound r compound := by
  simp [contractCompound]

@[simp]
theorem restrictInsideLeaf_mem_restrictCompound_iff {t : PlaneTree}
    (r : VPos t) (compound : Finset (VPos t)) (l : InsideLeaf r) :
    (restrictInsideLeaf r l).1 ∈ restrictCompound r compound ↔
      l.1.1 ∈ compound := by
  rw [mem_restrictCompound, subtreeVertex_restrictInsideLeaf]

@[simp]
theorem contractOutsideLeaf_mem_contractCompound_iff {t : PlaneTree}
    (r : VPos t) (compound : Finset (VPos t)) (l : OutsideLeaf r) :
    (contractOutsideLeaf r l).1 ∈ contractCompound r compound ↔
      l.1.1 ∈ compound := by
  rw [mem_contractCompound, contractVertex_contractOutsideLeaf]
  have hne : (contractOutsideLeaf r l).1.1 ≠ r.1 := by
    intro h
    apply l.2
    have hval : l.1.1 = r.1 := by
      rw [← contractVertex_contractOutsideLeaf r l]
      exact h
    rw [hval]
  simp [hne]

/-- Restriction of an embedding to the actual subtree leaf carrier. -/
def restrictEmbedding {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t) :
    HeppLeaf (subtreeAt t r.1) → Fin 4 → ℤ :=
  fun l => z (restrictLeafEquiv r l).1

@[simp]
theorem restrictEmbedding_apply_inside {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t) (l : InsideLeaf r) :
    restrictEmbedding z r (restrictInsideLeaf r l) = z l.1 := by
  simp [restrictEmbedding, restrictInsideLeaf]

/-- Contract an embedding by placing the marker at a specified original
inside leaf `lstar` and retaining all outside leaf positions. -/
def contractEmbedding {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t) (lstar : InsideLeaf r) :
    HeppLeaf (contractAt t r.1) → Fin 4 → ℤ :=
  fun l =>
    Sum.elim (fun _ : Unit => z lstar.1)
      (fun lout : OutsideLeaf r => z lout.1)
      (contractLeafSumEquiv r l)

@[simp]
theorem contractEmbedding_apply_marker {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t) (lstar : InsideLeaf r) :
    contractEmbedding z r lstar (contractMarkerLeaf r) = z lstar.1 := by
  simp [contractEmbedding]

@[simp]
theorem contractEmbedding_apply_outside {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t) (lstar : InsideLeaf r)
    (l : OutsideLeaf r) :
    contractEmbedding z r lstar (contractOutsideLeaf r l) = z l.1 := by
  simp [contractEmbedding]

theorem restrictCompound_subset_leaves {t : PlaneTree} (r : VPos t)
    {compound : Finset (VPos t)} (hc : compound ⊆ Leaves t) :
    restrictCompound r compound ⊆ Leaves (subtreeAt t r.1) := by
  intro v hv
  have hOriginal : subtreeVertex r v ∈ Leaves t :=
    hc ((mem_restrictCompound r compound v).mp hv)
  exact (mem_Leaves_subtreeVertex_iff r v).mpr hOriginal

theorem contractCompound_subset_leaves {t : PlaneTree} (r : VPos t)
    {compound : Finset (VPos t)} (hc : compound ⊆ Leaves t) :
    contractCompound r compound ⊆ Leaves (contractAt t r.1) := by
  intro v hv
  rcases (mem_contractCompound r compound v).mp hv with hmarker | hcompound
  · have hvMarker : v = contractMarker t r.1 r.2 := by
      apply Subtype.ext
      exact hmarker
    rw [hvMarker]
    exact contractMarker_mem_Leaves t r.1 r.2
  · by_cases hmarker : v.1 = r.1
    · have hvMarker : v = contractMarker t r.1 r.2 := by
        apply Subtype.ext
        exact hmarker
      rw [hvMarker]
      exact contractMarker_mem_Leaves t r.1 r.2
    · exact (mem_Leaves_contractVertex_iff_of_ne r.2 v hmarker).mpr
        (hc hcompound)

/-! ## Multiplicities -/

/-- Restrict leaf multiplicities to the selected rooted subtree. -/
def restrictMultiplicities {t : PlaneTree} (mu : Multiplicities t)
    (r : VPos t) : Multiplicities (subtreeAt t r.1) where
  m v := mu.m (subtreeVertex r v)
  two_le v hv :=
    mu.two_le (subtreeVertex r v)
      ((mem_Leaves_subtreeVertex_iff r v).mp hv)

@[simp]
theorem restrictMultiplicities_m {t : PlaneTree} (mu : Multiplicities t)
    (r : VPos t) (v : VPos (subtreeAt t r.1)) :
    (restrictMultiplicities mu r).m v =
      mu.m (subtreeVertex r v) :=
  rfl

@[simp]
theorem restrictMultiplicities_inside {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) (l : InsideLeaf r) :
    leafMultiplicity (restrictMultiplicities mu r)
      (restrictInsideLeaf r l) = leafMultiplicity mu l.1 := by
  change mu.m (subtreeVertex r (restrictInsideLeaf r l).1) = mu.m l.1.1
  rw [subtreeVertex_restrictInsideLeaf]

/-- Contract leaf multiplicities.  The new marker has multiplicity `s+1`;
all unchanged outside leaves inherit their original multiplicity. -/
def contractMultiplicities {t : PlaneTree} (mu : Multiplicities t)
    (r : VPos t) (s : ℕ) (hs : 1 ≤ s) :
    Multiplicities (contractAt t r.1) where
  m v :=
    if v.1 = r.1 then s + 1 else mu.m (contractVertex r.2 v)
  two_le v hv := by
    by_cases hmarker : v.1 = r.1
    · simp only [hmarker, ↓reduceIte]
      omega
    · simp only [hmarker, ↓reduceIte]
      exact mu.two_le (contractVertex r.2 v)
        ((mem_Leaves_contractVertex_iff_of_ne r.2 v hmarker).mp hv)

@[simp]
theorem contractMultiplicities_marker {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) (s : ℕ) (hs : 1 ≤ s) :
    leafMultiplicity (contractMultiplicities mu r s hs)
      (contractMarkerLeaf r) = s + 1 := by
  simp [leafMultiplicity, contractMultiplicities, contractMarkerLeaf]

theorem contractMultiplicities_m_of_ne {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) (s : ℕ) (hs : 1 ≤ s)
    (v : VPos (contractAt t r.1)) (hv : v.1 ≠ r.1) :
    (contractMultiplicities mu r s hs).m v =
      mu.m (contractVertex r.2 v) := by
  simp [contractMultiplicities, hv]

@[simp]
theorem contractMultiplicities_outside {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) (s : ℕ) (hs : 1 ≤ s)
    (l : OutsideLeaf r) :
    leafMultiplicity (contractMultiplicities mu r s hs)
      (contractOutsideLeaf r l) = leafMultiplicity mu l.1 := by
  have hne : (contractOutsideLeaf r l).1.1 ≠ r.1 := by
    intro h
    apply l.2
    have hval :
        l.1.1 = r.1 := by
      rw [← contractVertex_contractOutsideLeaf r l]
      exact h
    rw [hval]
  change (contractMultiplicities mu r s hs).m
      (contractOutsideLeaf r l).1 = mu.m l.1.1
  rw [contractMultiplicities_m_of_ne mu r s hs _ hne,
    contractVertex_contractOutsideLeaf]

/-- Total multiplicity carried by the leaves inside the selected subtree. -/
def insideMultiplicityTotal {t : PlaneTree} (mu : Multiplicities t)
    (r : VPos t) : ℕ :=
  ∑ l : InsideLeaf r, leafMultiplicity mu l.1

/-- Total multiplicity carried by the leaves outside the selected subtree. -/
def outsideMultiplicityTotal {t : PlaneTree} (mu : Multiplicities t)
    (r : VPos t) : ℕ :=
  ∑ l : OutsideLeaf r, leafMultiplicity mu l.1

/-- Restriction preserves exactly the total multiplicity of the inside
leaves. -/
theorem totalMultiplicity_restrictMultiplicities {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) :
    totalMultiplicity (restrictMultiplicities mu r) =
      insideMultiplicityTotal mu r := by
  unfold totalMultiplicity insideMultiplicityTotal
  let e := restrictLeafEquiv r
  have hpoint :
      ∀ l : HeppLeaf (subtreeAt t r.1),
        leafMultiplicity (restrictMultiplicities mu r) l =
          leafMultiplicity mu (e l).1 := by
    intro l
    rfl
  simp_rw [hpoint]
  exact Equiv.sum_comp e (fun l : InsideLeaf r =>
    leafMultiplicity mu l.1)

/-- The original total multiplicity splits exactly into inside and outside
parts. -/
theorem totalMultiplicity_eq_inside_add_outside {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) :
    totalMultiplicity mu =
      insideMultiplicityTotal mu r + outsideMultiplicityTotal mu r := by
  unfold totalMultiplicity insideMultiplicityTotal outsideMultiplicityTotal
  let e := leafInsideOutsideEquiv r
  let f : InsideLeaf r ⊕ OutsideLeaf r → ℕ :=
    Sum.elim
      (fun l : InsideLeaf r => leafMultiplicity mu l.1)
      (fun l : OutsideLeaf r => leafMultiplicity mu l.1)
  calc
    (∑ l : HeppLeaf t, leafMultiplicity mu l) =
        ∑ l : HeppLeaf t, f (e l) := by
      apply Fintype.sum_congr
      intro l
      by_cases hinside : r.1 <+: l.1.1
      · simp [f, e, leafInsideOutsideEquiv, hinside]
      · simp [f, e, leafInsideOutsideEquiv, hinside]
    _ = ∑ x : InsideLeaf r ⊕ OutsideLeaf r, f x :=
      Equiv.sum_comp e f
    _ = (∑ l : InsideLeaf r, leafMultiplicity mu l.1) +
          ∑ l : OutsideLeaf r, leafMultiplicity mu l.1 := by
      rw [Fintype.sum_sum_type]
      rfl

/-- Under contraction, the total multiplicity is the marker contribution
`s+1` plus the unchanged outside contribution. -/
theorem totalMultiplicity_contractMultiplicities {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) (s : ℕ) (hs : 1 ≤ s) :
    totalMultiplicity (contractMultiplicities mu r s hs) =
      (s + 1) + outsideMultiplicityTotal mu r := by
  unfold totalMultiplicity outsideMultiplicityTotal
  let e := contractLeafSumEquiv r
  have h :=
    Equiv.sum_comp e
      (fun x : Unit ⊕ OutsideLeaf r =>
        Sum.elim
          (fun _ : Unit => s + 1)
          (fun l : OutsideLeaf r => leafMultiplicity mu l.1) x)
  calc
    (∑ l : HeppLeaf (contractAt t r.1),
        leafMultiplicity (contractMultiplicities mu r s hs) l) =
        ∑ l : HeppLeaf (contractAt t r.1),
          Sum.elim (fun _ : Unit => s + 1)
            (fun l : OutsideLeaf r => leafMultiplicity mu l.1) (e l) := by
      apply Fintype.sum_congr
      intro l
      cases he : e l with
      | inl u =>
          cases u
          have hlmarker :
              l = contractMarkerLeaf r := by
            apply e.injective
            rw [he, contractLeafSumEquiv_marker]
          subst l
          change leafMultiplicity (contractMultiplicities mu r s hs)
            (contractMarkerLeaf r) = s + 1
          exact contractMultiplicities_marker mu r s hs
      | inr lout =>
          simp only [Sum.elim_inr]
          have hleaf :
              contractLeafEquiv r.2 l = some lout := by
            change
              (match contractLeafEquiv r.2 l with
                | none => Sum.inl ()
                | some l => Sum.inr l) = Sum.inr lout at he
            cases hopt : contractLeafEquiv r.2 l with
            | none =>
                simp [hopt] at he
            | some l' =>
                simp only [hopt, Sum.inr.injEq] at he
                exact congrArg some he
          have hpath : l.1.1 ≠ r.1 := by
            intro hp
            have hnone :
                contractLeafEquiv r.2 l = none := by
              simp [contractLeafEquiv, hp]
            rw [hleaf] at hnone
            simp at hnone
          change (contractMultiplicities mu r s hs).m l.1 =
            mu.m lout.1.1
          rw [contractMultiplicities_m_of_ne mu r s hs l.1 hpath]
          have hout :
              (contractVertex r.2 l.1 : VPos t) = lout.1.1 := by
            have happ := congrArg
              (fun x : Option (LeavesOutside t r.1) =>
                x.map fun y => y.1.1) hleaf
            simpa [contractLeafEquiv, hpath] using happ
          rw [hout]
    _ = ∑ x : Unit ⊕ OutsideLeaf r,
        Sum.elim (fun _ : Unit => s + 1)
          (fun l : OutsideLeaf r => leafMultiplicity mu l.1) x := h
    _ = (s + 1) + ∑ l : OutsideLeaf r, leafMultiplicity mu l.1 := by
      rw [Fintype.sum_sum_type]
      simp

/-- Exact total ledger: the contracted and restricted problems together
contain the original mass plus the new marker mass. -/
theorem totalMultiplicity_contract_add_restrict {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) (s : ℕ) (hs : 1 ≤ s) :
    totalMultiplicity (contractMultiplicities mu r s hs) +
        totalMultiplicity (restrictMultiplicities mu r) =
      totalMultiplicity mu + (s + 1) := by
  calc
    totalMultiplicity (contractMultiplicities mu r s hs) +
          totalMultiplicity (restrictMultiplicities mu r) =
        ((s + 1) + outsideMultiplicityTotal mu r) +
          insideMultiplicityTotal mu r := by
      rw [totalMultiplicity_contractMultiplicities,
        totalMultiplicity_restrictMultiplicities]
    _ = (insideMultiplicityTotal mu r + outsideMultiplicityTotal mu r) +
          (s + 1) := by omega
    _ = totalMultiplicity mu + (s + 1) := by
      rw [totalMultiplicity_eq_inside_add_outside]

end

end Anderson4D
