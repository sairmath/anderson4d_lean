import Anderson4D.HeppTree.LeafCard

/-!
# Subtrees and contractions of plane Hepp trees

This file provides the structural API used by the collapse induction in
paper §5.4.1.  Positions in a `PlaneTree` are paths from the root, so the
subtree at a valid position is obtained by following that path.  Contracting
at a position replaces the whole rooted subtree there by one leaf.

The API is deliberately independent of markings, multiplicities, and
embeddings.  Those data are transported in the later collapse layers.
-/

namespace Anderson4D

open PlaneTree

namespace PlaneTree

/-! ## The rooted subtree at a position -/

/-- The subtree rooted at `p`.  At an invalid position this returns the bare
leaf; all mathematical uses supply `IsPos t p`, under which the fallback is
unreachable. -/
def subtreeAt : PlaneTree → Pos → PlaneTree
  | t, [] => t
  | node cs, i :: p =>
      if h : i < cs.length then subtreeAt cs[i] p else leaf

@[simp]
theorem subtreeAt_nil (t : PlaneTree) : subtreeAt t [] = t := rfl

theorem subtreeAt_cons_of_lt {cs : List PlaneTree} {i : ℕ} {p : Pos}
    (hi : i < cs.length) :
    subtreeAt (node cs) (i :: p) = subtreeAt cs[i] p := by
  simp [subtreeAt, hi]

/-- A path `q` is valid in the rooted subtree at `p` exactly when `p ++ q`
is valid in the original tree. -/
theorem isPos_subtreeAt_iff {t : PlaneTree} {p q : Pos}
    (hp : IsPos t p) :
    IsPos (subtreeAt t p) q ↔ IsPos t (p ++ q) := by
  induction p generalizing t with
  | nil =>
      simp [subtreeAt]
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      rw [subtreeAt_cons_of_lt hi, ih hp']
      constructor
      · exact fun h => isPos_cons_iff.mpr ⟨hi, h⟩
      · exact fun h => (isPos_cons_iff.mp h).2

/-- Child counts are unchanged when a vertex is viewed inside a rooted
subtree. -/
theorem childCount_subtreeAt {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) (q : Pos) :
    childCount (subtreeAt t p) q = childCount t (p ++ q) := by
  induction p generalizing t with
  | nil =>
      simp [subtreeAt]
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      rw [subtreeAt_cons_of_lt hi, ih hp']
      simp [childCount, hi]

private theorem isValid_get_of_isValid {cs : List PlaneTree}
    (ht : (node cs).isValid = true) (i : Fin cs.length) :
    (cs.get i).isValid = true := by
  simp only [isValid, Bool.and_eq_true] at ht
  rw [isValidList_eq_map] at ht
  simp only [List.all_eq_true, id_eq] at ht
  exact ht.2 _ (List.mem_map.mpr ⟨cs.get i, List.get_mem cs i, rfl⟩)

/-- A rooted subtree of a valid Hepp tree is valid. -/
theorem isValid_subtreeAt {t : PlaneTree} {p : Pos}
    (ht : t.isValid = true) (hp : IsPos t p) :
    (subtreeAt t p).isValid = true := by
  induction p generalizing t with
  | nil =>
      simpa [subtreeAt] using ht
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      rw [subtreeAt_cons_of_lt hi]
      exact ih (isValid_get_of_isValid ht ⟨i, hi⟩) hp'

private theorem size_le_sizeList_of_mem {c : PlaneTree} {cs : List PlaneTree}
    (hc : c ∈ cs) :
    c.size ≤ sizeList cs := by
  induction cs with
  | nil =>
      simp at hc
  | cons d ds ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · simp [sizeList]
      · have hle := ih hc
        simp only [sizeList]
        omega

private theorem size_get_lt_node {cs : List PlaneTree} (i : Fin cs.length) :
    (cs.get i).size < (node cs).size := by
  have hle : (cs.get i).size ≤ sizeList cs :=
    size_le_sizeList_of_mem (List.get_mem cs i)
  simp only [size]
  omega

/-- A rooted subtree never has more vertices than the original tree. -/
theorem subtreeAt_size_le {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) :
    (subtreeAt t p).size ≤ t.size := by
  induction p generalizing t with
  | nil =>
      simp [subtreeAt]
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      rw [subtreeAt_cons_of_lt hi]
      exact (ih hp').trans (Nat.le_of_lt (size_get_lt_node ⟨i, hi⟩))

/-- Every proper rooted subtree (one whose root is not the original root) has
strictly fewer vertices.  This is the well-founded measure for the collapse
induction. -/
theorem subtreeAt_size_lt {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) (hp0 : p ≠ []) :
    (subtreeAt t p).size < t.size := by
  induction p generalizing t with
  | nil =>
      exact absurd rfl hp0
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      rw [subtreeAt_cons_of_lt hi]
      exact (subtreeAt_size_le hp').trans_lt (size_get_lt_node ⟨i, hi⟩)

/-! ## Vertex, leaf, and branch transport -/

/-- Vertices of `t` lying weakly below `r`. -/
abbrev Descendants {t : PlaneTree} (r : VPos t) : Type :=
  {v : VPos t // r.1 <+: v.1}

/-- Include a vertex of the subtree at `r` into the original tree by
prepending `r`'s path. -/
def subtreeVertex {t : PlaneTree} (r : VPos t)
    (v : VPos (subtreeAt t r.1)) : VPos t :=
  ⟨r.1 ++ v.1, (isPos_subtreeAt_iff r.2).mp v.2⟩

@[simp]
theorem subtreeVertex_val {t : PlaneTree} (r : VPos t)
    (v : VPos (subtreeAt t r.1)) :
    (subtreeVertex r v).1 = r.1 ++ v.1 := rfl

theorem subtreeVertex_injective {t : PlaneTree} (r : VPos t) :
    Function.Injective (subtreeVertex r) := by
  intro v w h
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  exact List.append_cancel_left hv

@[simp]
theorem subtreeVertex_root {t : PlaneTree} (r : VPos t) :
    subtreeVertex r (rootV (subtreeAt t r.1)) = r := by
  apply Subtype.ext
  simp [subtreeVertex, rootV]

/-- Vertices of the rooted subtree are exactly descendants of its root in the
original tree. -/
def subtreeVertexEquiv {t : PlaneTree} (r : VPos t) :
    VPos (subtreeAt t r.1) ≃ Descendants r where
  toFun v :=
    ⟨subtreeVertex r v, List.prefix_append r.1 v.1⟩
  invFun v :=
    ⟨v.1.1.drop r.1.length,
      (isPos_subtreeAt_iff r.2).mpr (by
        rw [← List.prefix_append_drop v.2]
        exact v.1.2)⟩
  left_inv v := by
    apply Subtype.ext
    simp [subtreeVertex]
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    exact (List.prefix_append_drop v.2).symm

@[simp]
theorem subtreeVertexEquiv_apply_val {t : PlaneTree} (r : VPos t)
    (v : VPos (subtreeAt t r.1)) :
    (subtreeVertexEquiv r v).1 = subtreeVertex r v := rfl

/-- Child count is preserved by the subtree vertex inclusion. -/
theorem childCount_subtreeVertex {t : PlaneTree} (r : VPos t)
    (v : VPos (subtreeAt t r.1)) :
    childCount (subtreeAt t r.1) v.1 =
      childCount t (subtreeVertex r v).1 := by
  exact childCount_subtreeAt r.2 v.1

theorem mem_Leaves_subtreeVertex_iff {t : PlaneTree} (r : VPos t)
    (v : VPos (subtreeAt t r.1)) :
    v ∈ Leaves (subtreeAt t r.1) ↔ subtreeVertex r v ∈ Leaves t := by
  simp only [mem_Leaves_iff, childCount_subtreeVertex]

theorem mem_BranchNodes_subtreeVertex_iff {t : PlaneTree} (r : VPos t)
    (v : VPos (subtreeAt t r.1)) :
    v ∈ BranchNodes (subtreeAt t r.1) ↔ subtreeVertex r v ∈ BranchNodes t := by
  simp only [mem_BranchNodes_iff, childCount_subtreeVertex]

/-- Leaves of `t` below `r`, represented as descendant vertices. -/
abbrev DescendantLeaves {t : PlaneTree} (r : VPos t) : Type :=
  {v : Descendants r // v.1 ∈ Leaves t}

/-- Branch vertices of `t` below `r`, represented as descendant vertices. -/
abbrev DescendantBranches {t : PlaneTree} (r : VPos t) : Type :=
  {v : Descendants r // v.1 ∈ BranchNodes t}

/-- Leaves of the rooted subtree are exactly descendant leaves. -/
def subtreeLeafEquiv {t : PlaneTree} (r : VPos t) :
    {v : VPos (subtreeAt t r.1) // v ∈ Leaves (subtreeAt t r.1)} ≃
      DescendantLeaves r :=
  Equiv.subtypeEquiv (subtreeVertexEquiv r) fun v =>
    mem_Leaves_subtreeVertex_iff r v

/-- Branch vertices of the rooted subtree are exactly descendant branch
vertices. -/
def subtreeBranchEquiv {t : PlaneTree} (r : VPos t) :
    {v : VPos (subtreeAt t r.1) // v ∈ BranchNodes (subtreeAt t r.1)} ≃
      DescendantBranches r :=
  Equiv.subtypeEquiv (subtreeVertexEquiv r) fun v =>
    mem_BranchNodes_subtreeVertex_iff r v

/-- Descendant leaves are the same carrier as membership in `leavesUnder`. -/
def descendantLeavesEquivLeavesUnder {t : PlaneTree} (r : VPos t) :
    DescendantLeaves r ≃
      {l : {v : VPos t // v ∈ Leaves t} // l ∈ leavesUnder r} where
  toFun l :=
    ⟨⟨l.1.1, l.2⟩, mem_leavesUnder.mpr l.1.2⟩
  invFun l :=
    ⟨⟨l.1.1, mem_leavesUnder.mp l.2⟩, l.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Paper-facing leaf equivalence: the leaves of the actual rooted subtree
are precisely the original leaves in `leavesUnder r`. -/
def subtreeLeafEquivLeavesUnder {t : PlaneTree} (r : VPos t) :
    {v : VPos (subtreeAt t r.1) // v ∈ Leaves (subtreeAt t r.1)} ≃
      {l : {v : VPos t // v ∈ Leaves t} // l ∈ leavesUnder r} :=
  (subtreeLeafEquiv r).trans (descendantLeavesEquivLeavesUnder r)

/-- The recursive leaf count of the actual rooted subtree is the cardinality
of the previously used prefix-defined `leavesUnder` finset. -/
theorem card_leavesUnder_eq_leafCount_subtreeAt {t : PlaneTree}
    (r : VPos t) :
    (leavesUnder r).card = (subtreeAt t r.1).leafCount := by
  calc
    (leavesUnder r).card =
        Fintype.card {l : {v : VPos t // v ∈ Leaves t} // l ∈ leavesUnder r} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        {v : VPos (subtreeAt t r.1) // v ∈ Leaves (subtreeAt t r.1)} :=
      Fintype.card_congr (subtreeLeafEquivLeavesUnder r).symm
    _ = (Leaves (subtreeAt t r.1)).card :=
      Fintype.card_coe _
    _ = (subtreeAt t r.1).leafCount :=
      card_Leaves_eq_leafCount _

/-! ## Contracting a rooted subtree -/

/-- Replace the rooted subtree at `p` by a single leaf.  At an invalid step
the tree is left unchanged; all structural theorems below assume
`IsPos t p`. -/
def contractAt : PlaneTree → Pos → PlaneTree
  | _, [] => leaf
  | node cs, i :: p =>
      if h : i < cs.length then
        node (cs.set i (contractAt cs[i] p))
      else
        node cs

/-- `q` lies strictly below `p` when it properly extends `p`. -/
def IsStrictDescendant (p q : Pos) : Prop :=
  p <+: q ∧ p ≠ q

instance (p : Pos) : DecidablePred (IsStrictDescendant p) := fun q =>
  inferInstanceAs (Decidable (p <+: q ∧ p ≠ q))

@[simp]
theorem contractAt_nil (t : PlaneTree) : contractAt t [] = leaf := rfl

theorem contractAt_cons_of_lt {cs : List PlaneTree} {i : ℕ} {p : Pos}
    (hi : i < cs.length) :
    contractAt (node cs) (i :: p) =
      node (cs.set i (contractAt cs[i] p)) := by
  simp [contractAt, hi]

/-- Contracting at `p` removes exactly the vertices strictly below `p`.
The position `p` itself remains as the replacement leaf. -/
theorem isPos_contractAt_iff {t : PlaneTree} {p q : Pos}
    (hp : IsPos t p) :
    IsPos (contractAt t p) q ↔
      IsPos t q ∧ ¬IsStrictDescendant p q := by
  induction p generalizing t q with
  | nil =>
      constructor
      · intro hq
        have hq0 : q = [] := isPos_leaf_iff.mp hq
        subst q
        exact ⟨isPos_nil t, by simp [IsStrictDescendant]⟩
      · rintro ⟨_, hq⟩
        have hq0 : q = [] := by
          by_contra hne
          exact hq ⟨List.nil_prefix, fun h => hne h.symm⟩
        subst q
        exact isPos_nil leaf
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      cases q with
      | nil =>
          exact ⟨fun _ => ⟨isPos_nil _, by simp [IsStrictDescendant]⟩,
            fun _ => isPos_nil _⟩
      | cons j q =>
          rw [contractAt_cons_of_lt hi]
          by_cases hji : j = i
          · subst j
            simpa [isPos_cons_iff, List.length_set, hi,
              IsStrictDescendant] using ih (t := cs[i]) (q := q) hp'
          · simp [isPos_cons_iff, List.length_set, IsStrictDescendant,
              Ne.symm hji]

/-- Vertices retained by contraction: all original vertices except those
strictly below the contraction position. -/
abbrev RetainedVertices (t : PlaneTree) (p : Pos) : Type :=
  {v : VPos t // ¬IsStrictDescendant p v.1}

/-- Include a vertex of the contracted tree into the original tree.  Its
position path is unchanged. -/
def contractVertex {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    (v : VPos (contractAt t p)) : VPos t :=
  ⟨v.1, (isPos_contractAt_iff hp).mp v.2 |>.1⟩

@[simp]
theorem contractVertex_val {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    (v : VPos (contractAt t p)) :
    (contractVertex hp v).1 = v.1 := rfl

/-- Vertices of the contracted tree are exactly the retained vertices of the
original tree. -/
def contractVertexEquiv {t : PlaneTree} {p : Pos} (hp : IsPos t p) :
    VPos (contractAt t p) ≃ RetainedVertices t p where
  toFun v :=
    ⟨contractVertex hp v, (isPos_contractAt_iff hp).mp v.2 |>.2⟩
  invFun v :=
    ⟨v.1.1, (isPos_contractAt_iff hp).mpr ⟨v.1.2, v.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem contractVertexEquiv_apply_val {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) (v : VPos (contractAt t p)) :
    (contractVertexEquiv hp v).1 = contractVertex hp v := rfl

private theorem isValidList_set {cs : List PlaneTree} {i : ℕ} {c : PlaneTree}
    (hcs : isValidList cs = true) (hc : c.isValid = true) :
    isValidList (cs.set i c) = true := by
  rw [isValidList_eq_map, List.map_set, List.all_eq_true]
  intro b hb
  rcases List.mem_or_eq_of_mem_set hb with hb | rfl
  · rw [isValidList_eq_map, List.all_eq_true] at hcs
    exact hcs _ hb
  · exact hc

/-- Contracting a rooted subtree preserves Hepp validity. -/
theorem isValid_contractAt {t : PlaneTree} {p : Pos}
    (ht : t.isValid = true) (hp : IsPos t p) :
    (contractAt t p).isValid = true := by
  induction p generalizing t with
  | nil =>
      rfl
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      have ht' := ht
      simp only [isValid, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht'
      rw [contractAt_cons_of_lt hi]
      simp only [isValid, Bool.and_eq_true, bne_iff_ne, ne_eq, List.length_set]
      exact ⟨ht'.1,
        isValidList_set ht'.2
          (ih (isValid_get_of_isValid ht ⟨i, hi⟩) hp')⟩

/-- The contraction position remains a valid position in the contracted
tree. -/
theorem isPos_contractAt_self {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) :
    IsPos (contractAt t p) p := by
  induction p generalizing t with
  | nil =>
      exact isPos_nil _
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      rw [contractAt_cons_of_lt hi, isPos_cons_iff]
      let hi' : i < (cs.set i (contractAt cs[i] p)).length := by
        simpa using hi
      refine ⟨hi', ?_⟩
      rw [List.getElem_set_self]
      exact ih hp'

/-- The vertex replacing the contracted subtree. -/
def contractMarker (t : PlaneTree) (p : Pos) (hp : IsPos t p) :
    VPos (contractAt t p) :=
  ⟨p, isPos_contractAt_self hp⟩

@[simp]
theorem contractMarker_val (t : PlaneTree) (p : Pos) (hp : IsPos t p) :
    (contractMarker t p hp).1 = p := rfl

/-- The replacement vertex is a leaf. -/
theorem childCount_contractAt_self {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) :
    childCount (contractAt t p) p = 0 := by
  induction p generalizing t with
  | nil =>
      rfl
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      rw [contractAt_cons_of_lt hi]
      have hi' : i < (cs.set i (contractAt cs[i] p)).length := by
        simpa using hi
      simp only [childCount, dif_pos hi']
      rw [List.getElem_set_self]
      exact ih hp'

theorem contractMarker_mem_Leaves (t : PlaneTree) (p : Pos)
    (hp : IsPos t p) :
    contractMarker t p hp ∈ Leaves (contractAt t p) := by
  rw [mem_Leaves_iff]
  exact childCount_contractAt_self hp

/-- Away from the replacement vertex, contraction preserves child counts at
every retained vertex. -/
theorem childCount_contractAt_eq_of_ne {t : PlaneTree} {p q : Pos}
    (hp : IsPos t p) (hq : IsPos (contractAt t p) q) (hne : q ≠ p) :
    childCount (contractAt t p) q = childCount t q := by
  induction p generalizing t q with
  | nil =>
      have hq0 : q = [] := isPos_leaf_iff.mp hq
      exact (hne hq0).elim
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      cases q with
      | nil =>
          rw [contractAt_cons_of_lt hi]
          simp [childCount, List.length_set]
      | cons j q =>
          rw [contractAt_cons_of_lt hi] at hq ⊢
          have hj' : j < (cs.set i (contractAt cs[i] p)).length :=
            isPos_cons_lt hq
          have hj : j < cs.length := by simpa using hj'
          by_cases hji : j = i
          · subst j
            have hq' : IsPos (contractAt cs[i] p) q := by
              have htail := isPos_cons_tail hq
              simpa using htail
            have hne' : q ≠ p := by
              intro h
              apply hne
              simp [h]
            have hrec := ih hp' hq' hne'
            simp only [childCount, dif_pos hj', dif_pos hi]
            rw [List.getElem_set_self]
            exact hrec
          · simp only [childCount, dif_pos hj', dif_pos hj]
            rw [List.getElem_set_of_ne (Ne.symm hji)]

/-- Original branch vertices surviving contraction.  The root of the removed
subtree is excluded because it becomes the marker leaf. -/
abbrev BranchesOutside (t : PlaneTree) (p : Pos) : Type :=
  {v : {v : VPos t // v ∈ BranchNodes t} // ¬p <+: v.1.1}

/-- Original leaves outside the contracted rooted subtree. -/
abbrev LeavesOutside (t : PlaneTree) (p : Pos) : Type :=
  {v : {v : VPos t // v ∈ Leaves t} // ¬p <+: v.1.1}

theorem mem_BranchNodes_contractVertex_iff_of_ne
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    (v : VPos (contractAt t p)) (hne : v.1 ≠ p) :
    v ∈ BranchNodes (contractAt t p) ↔
      contractVertex hp v ∈ BranchNodes t := by
  rw [mem_BranchNodes_iff, mem_BranchNodes_iff]
  rw [childCount_contractAt_eq_of_ne hp v.2 hne]
  rfl

theorem mem_Leaves_contractVertex_iff_of_ne
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    (v : VPos (contractAt t p)) (hne : v.1 ≠ p) :
    v ∈ Leaves (contractAt t p) ↔ contractVertex hp v ∈ Leaves t := by
  rw [mem_Leaves_iff, mem_Leaves_iff]
  rw [childCount_contractAt_eq_of_ne hp v.2 hne]
  rfl

/-- A branch vertex of the contracted tree cannot lie weakly below the
contraction position: the only retained vertex there is the marker leaf. -/
theorem not_prefix_of_mem_BranchNodes_contractAt
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    (v : VPos (contractAt t p)) (hv : v ∈ BranchNodes (contractAt t p)) :
    ¬p <+: v.1 := by
  have htwo : 2 ≤ childCount (contractAt t p) v.1 :=
    mem_BranchNodes_iff.mp hv
  have hne : v.1 ≠ p := by
    intro h
    have hzero : childCount (contractAt t p) v.1 = 0 := by
      rw [h]
      exact childCount_contractAt_self hp
    omega
  have hretained := (isPos_contractAt_iff hp).mp v.2 |>.2
  intro hpre
  exact hretained ⟨hpre, fun h => hne h.symm⟩

/-- A retained vertex distinct from the marker lies completely outside the
contracted rooted subtree. -/
theorem not_prefix_of_ne_contractAt
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    (v : VPos (contractAt t p)) (hne : v.1 ≠ p) :
    ¬p <+: v.1 := by
  have hretained := (isPos_contractAt_iff hp).mp v.2 |>.2
  intro hpre
  exact hretained ⟨hpre, fun h => hne h.symm⟩

/-- Branch vertices of the contracted tree are exactly the original branch
vertices outside the removed rooted subtree. -/
def contractBranchEquiv {t : PlaneTree} {p : Pos} (hp : IsPos t p) :
    {v : VPos (contractAt t p) // v ∈ BranchNodes (contractAt t p)} ≃
      BranchesOutside t p where
  toFun v :=
    let hne : v.1.1 ≠ p := by
      intro h
      exact not_prefix_of_mem_BranchNodes_contractAt hp v.1 v.2
        ⟨[], by simpa using h.symm⟩
    ⟨⟨contractVertex hp v.1,
        (mem_BranchNodes_contractVertex_iff_of_ne hp v.1 hne).mp v.2⟩,
      not_prefix_of_mem_BranchNodes_contractAt hp v.1 v.2⟩
  invFun v :=
    let hnotStrict : ¬IsStrictDescendant p v.1.1.1 :=
      fun h => v.2 h.1
    let w : VPos (contractAt t p) :=
      ⟨v.1.1.1, (isPos_contractAt_iff hp).mpr ⟨v.1.1.2, hnotStrict⟩⟩
    let hne : w.1 ≠ p := by
      intro h
      apply v.2
      exact ⟨[], by simpa using h.symm⟩
    ⟨w, (mem_BranchNodes_contractVertex_iff_of_ne hp w hne).mpr v.1.2⟩
  left_inv _ := by
    apply Subtype.ext
    rfl
  right_inv _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Cardinal form of `contractBranchEquiv`. -/
theorem card_BranchNodes_contractAt_eq_card_branchesOutside
    {t : PlaneTree} {p : Pos} (hp : IsPos t p) :
    (BranchNodes (contractAt t p)).card =
      Fintype.card (BranchesOutside t p) := by
  calc
    (BranchNodes (contractAt t p)).card =
        Fintype.card
          {v : VPos (contractAt t p) // v ∈ BranchNodes (contractAt t p)} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (BranchesOutside t p) :=
      Fintype.card_congr (contractBranchEquiv hp)

/-- Leaves of the contracted tree consist of the new marker leaf together
with the original leaves outside the removed rooted subtree.  `none` denotes
the marker and `some l` denotes an unchanged outside leaf. -/
def contractLeafEquiv {t : PlaneTree} {p : Pos} (hp : IsPos t p) :
    {v : VPos (contractAt t p) // v ∈ Leaves (contractAt t p)} ≃
      Option (LeavesOutside t p) where
  toFun l :=
    if h : l.1.1 = p then
      none
    else
      some
        ⟨⟨contractVertex hp l.1,
            (mem_Leaves_contractVertex_iff_of_ne hp l.1 h).mp l.2⟩,
          not_prefix_of_ne_contractAt hp l.1 h⟩
  invFun
    | none =>
        ⟨contractMarker t p hp, contractMarker_mem_Leaves t p hp⟩
    | some l =>
        let hnotStrict : ¬IsStrictDescendant p l.1.1.1 :=
          fun h => l.2 h.1
        let w : VPos (contractAt t p) :=
          ⟨l.1.1.1, (isPos_contractAt_iff hp).mpr
            ⟨l.1.1.2, hnotStrict⟩⟩
        let hne : w.1 ≠ p := by
          intro h
          apply l.2
          exact ⟨[], by simpa using h.symm⟩
        ⟨w, (mem_Leaves_contractVertex_iff_of_ne hp w hne).mpr l.1.2⟩
  left_inv l := by
    by_cases h : l.1.1 = p
    · simp only [h, ↓reduceDIte]
      apply Subtype.ext
      apply Subtype.ext
      exact h.symm
    · simp only [h, ↓reduceDIte]
      apply Subtype.ext
      rfl
  right_inv l := by
    cases l with
    | none =>
        simp
    | some l =>
        have hne : l.1.1.1 ≠ p := by
          intro h
          apply l.2
          exact ⟨[], by simpa using h.symm⟩
        simp only [hne, ↓reduceDIte]
        congr 1

/-- Cardinal form of `contractLeafEquiv`. -/
theorem card_Leaves_contractAt_eq_card_option_leavesOutside
    {t : PlaneTree} {p : Pos} (hp : IsPos t p) :
    (Leaves (contractAt t p)).card =
      Fintype.card (Option (LeavesOutside t p)) := by
  calc
    (Leaves (contractAt t p)).card =
        Fintype.card
          {v : VPos (contractAt t p) // v ∈ Leaves (contractAt t p)} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (Option (LeavesOutside t p)) :=
      Fintype.card_congr (contractLeafEquiv hp)

/-- Looking below the replacement vertex gives the bare leaf. -/
theorem subtreeAt_contractAt_self {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) :
    subtreeAt (contractAt t p) p = leaf := by
  induction p generalizing t with
  | nil =>
      rfl
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      rw [contractAt_cons_of_lt hi]
      have hi' : i < (cs.set i (contractAt cs[i] p)).length := by
        simpa using hi
      rw [subtreeAt_cons_of_lt hi', List.getElem_set_self]
      exact ih hp'

private theorem sum_set_add_getElem (xs : List ℕ) (i : ℕ)
    (hi : i < xs.length) (a : ℕ) :
    (xs.set i a).sum + xs[i] = xs.sum + a := by
  have hnew := List.sum_set xs i a
  have hold : xs.sum =
      ((xs.take i).sum + xs[i]) + (xs.drop (i + 1)).sum := by
    calc
      xs.sum = (xs.set i xs[i]).sum := by
        rw [List.set_getElem_self hi]
      _ = ((xs.take i).sum + xs[i]) + (xs.drop (i + 1)).sum := by
        rw [List.sum_set]
        simp [hi]
  rw [hnew, hold]
  simp only [if_pos hi]
  omega

private theorem sizeList_set_add_get {cs : List PlaneTree} (i : Fin cs.length)
    (c : PlaneTree) :
    sizeList (cs.set i.1 c) + (cs.get i).size =
      sizeList cs + c.size := by
  rw [sizeList_eq_map, sizeList_eq_map, List.map_set]
  have hi : i.1 < (cs.map size).length := by
    rw [List.length_map]
    exact i.2
  simpa [List.get_eq_getElem] using
    sum_set_add_getElem (cs.map size) i.1 hi c.size

/-- Exact vertex-count ledger for contraction: the contracted tree and the
removed subtree overlap in precisely their common replacement/root vertex. -/
theorem contractAt_size_add_subtreeAt_size {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) :
    (contractAt t p).size + (subtreeAt t p).size = t.size + 1 := by
  induction p generalizing t with
  | nil =>
      simp [contractAt, subtreeAt, leaf, size, sizeList, Nat.add_comm]
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      rw [contractAt_cons_of_lt hi, subtreeAt_cons_of_lt hi]
      have hforest :=
        sizeList_set_add_get ⟨i, hi⟩ (contractAt cs[i] p)
      have hforest' :
          sizeList (cs.set i (contractAt cs[i] p)) + cs[i].size =
            sizeList cs + (contractAt cs[i] p).size := by
        simpa [List.get_eq_getElem] using hforest
      have hrec := ih hp'
      simp only [size]
      omega

private theorem leafCountList_set_add_get {cs : List PlaneTree}
    (i : Fin cs.length) (c : PlaneTree) :
    leafCountList (cs.set i.1 c) + (cs.get i).leafCount =
      leafCountList cs + c.leafCount := by
  rw [leafCountList_eq_map, leafCountList_eq_map, List.map_set]
  have hi : i.1 < (cs.map leafCount).length := by
    rw [List.length_map]
    exact i.2
  simpa [List.get_eq_getElem] using
    sum_set_add_getElem (cs.map leafCount) i.1 hi c.leafCount

private theorem one_le_leafCount_subtreeCollapse (t : PlaneTree) :
    1 ≤ t.leafCount := by
  obtain ⟨cs⟩ := t
  exact le_max_left 1 (leafCountList cs)

private theorem leafCount_le_leafCountList_of_mem
    {c : PlaneTree} {cs : List PlaneTree} (hc : c ∈ cs) :
    c.leafCount ≤ leafCountList cs := by
  induction cs with
  | nil =>
      simp at hc
  | cons d ds ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · simp [leafCountList]
      · have hle := ih hc
        simp only [leafCountList]
        omega

/-- Exact leaf-count ledger for contraction.  The marker replaces all leaves
of the removed subtree, hence the correction term `+ 1`. -/
theorem contractAt_leafCount_add_subtreeAt_leafCount
    {t : PlaneTree} {p : Pos} (hp : IsPos t p) :
    (contractAt t p).leafCount + (subtreeAt t p).leafCount =
      t.leafCount + 1 := by
  induction p generalizing t with
  | nil =>
      simp [contractAt, subtreeAt, leaf, leafCount, leafCountList, Nat.add_comm]
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      rw [contractAt_cons_of_lt hi, subtreeAt_cons_of_lt hi]
      have hforest :=
        leafCountList_set_add_get ⟨i, hi⟩ (contractAt cs[i] p)
      have hforest' :
          leafCountList (cs.set i (contractAt cs[i] p)) + cs[i].leafCount =
            leafCountList cs + (contractAt cs[i] p).leafCount := by
        simpa [List.get_eq_getElem] using hforest
      have hrec := ih hp'
      have hcsPos : 1 ≤ leafCountList cs :=
        (one_le_leafCount_subtreeCollapse cs[i]).trans
          (leafCount_le_leafCountList_of_mem (List.getElem_mem hi))
      have hsetPos : 1 ≤ leafCountList (cs.set i (contractAt cs[i] p)) :=
        (one_le_leafCount_subtreeCollapse (contractAt cs[i] p)).trans
          (leafCount_le_leafCountList_of_mem (List.mem_set hi _))
      simp only [leafCount]
      rw [max_eq_right hsetPos, max_eq_right hcsPos]
      omega

private theorem one_le_size (t : PlaneTree) : 1 ≤ t.size := by
  obtain ⟨cs⟩ := t
  simp [size]

private theorem length_le_sizeList (cs : List PlaneTree) :
    cs.length ≤ sizeList cs := by
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      have hc := one_le_size c
      simp only [List.length_cons, sizeList]
      omega

private theorem childCount_root_lt_size (t : PlaneTree) :
    childCount t [] < t.size := by
  obtain ⟨cs⟩ := t
  have h := length_le_sizeList cs
  simp only [childCount, size]
  omega

/-- A subtree rooted at a branch vertex has more than one vertex. -/
theorem one_lt_subtreeAt_size_of_branch {t : PlaneTree} {r : VPos t}
    (hr : r ∈ BranchNodes t) :
    1 < (subtreeAt t r.1).size := by
  have hbranch : 2 ≤ childCount t r.1 := mem_BranchNodes_iff.mp hr
  have hcount :
      childCount (subtreeAt t r.1) [] = childCount t r.1 := by
    simpa using childCount_subtreeAt r.2 []
  have hroot := childCount_root_lt_size (subtreeAt t r.1)
  omega

/-- Contracting at a branch vertex strictly decreases tree size. -/
theorem contractAt_size_lt_of_branch {t : PlaneTree} {r : VPos t}
    (hr : r ∈ BranchNodes t) :
    (contractAt t r.1).size < t.size := by
  have hledger := contractAt_size_add_subtreeAt_size r.2
  have hsub := one_lt_subtreeAt_size_of_branch hr
  omega

end PlaneTree

end Anderson4D
