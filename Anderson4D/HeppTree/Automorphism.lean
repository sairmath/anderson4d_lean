import Anderson4D.HeppTree.Admissible
import Anderson4D.HeppTree.RestrictedData

/-!
# Automorphisms on Hepp-tree data

The group `PlaneTree.Aut t` is defined graph-theoretically, as the vertex
permutations commuting with the total parent map.  This file derives the
concrete consequences needed in Proposition 5.6: child counts, leaves, and
branch vertices are invariant, and markings and multiplicities can be
transported along automorphisms.
-/

namespace Anderson4D

open PlaneTree

/-- Children described purely through the total parent map.  The inequality
removes the root from its own parent fiber. -/
def graphChildren {t : PlaneTree} (v : VPos t) : Finset (VPos t) :=
  Finset.univ.filter fun w => parentV w = v ∧ w ≠ v

@[simp]
theorem mem_graphChildren {t : PlaneTree} {v w : VPos t} :
    w ∈ graphChildren v ↔ parentV w = v ∧ w ≠ v := by
  simp [graphChildren]

private theorem graphChildren_root
    (cs : List PlaneTree) :
    graphChildren (rootV (node cs)) =
      Finset.univ.image fun i : Fin cs.length =>
        childV i (rootV (cs.get i)) := by
  ext w
  rw [mem_graphChildren]
  constructor
  · rintro ⟨hw, hne⟩
    obtain hwroot | ⟨i, rfl⟩ := parentV_eq_root_cases hw
    · exact absurd hwroot hne
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨parentV_childV_rootV i, childV_ne_root i _⟩

private theorem graphChildren_child
    {cs : List PlaneTree} (i : Fin cs.length) (v : VPos (cs.get i)) :
    graphChildren (childV i v) =
      (graphChildren v).image (childV i) := by
  ext w
  rw [mem_graphChildren]
  constructor
  · rintro ⟨hparent, hne⟩
    obtain ⟨u, rfl⟩ := exists_childV_of_parentV_eq hparent
    have huroot : u ≠ rootV (cs.get i) := by
      intro hu
      subst u
      rw [parentV_childV_rootV] at hparent
      exact childV_ne_root i v hparent.symm
    have hpu : parentV u = v := by
      rw [parentV_childV i huroot] at hparent
      exact childV_inj_snd hparent
    have huv : u ≠ v := by
      intro hu
      exact hne (congrArg (childV i) hu)
    exact Finset.mem_image.mpr
      ⟨u, mem_graphChildren.mpr ⟨hpu, huv⟩, rfl⟩
  · intro hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    rw [mem_graphChildren] at hu
    have huroot : u ≠ rootV (cs.get i) := by
      intro hroot
      have hp := hu.1
      rw [hroot, parentV_rootV] at hp
      exact hu.2 (hroot.trans hp)
    exact ⟨by rw [parentV_childV i huroot, hu.1],
      fun h => hu.2 (childV_inj_snd h)⟩

private theorem aut_size_lt_of_mem {c : PlaneTree} {cs : List PlaneTree}
    (hc : c ∈ cs) : c.size < (node cs).size := by
  have hmem : c.size ∈ cs.map size :=
    List.mem_map.mpr ⟨c, hc, rfl⟩
  have hle : c.size ≤ (cs.map size).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  simp only [size, sizeList_eq_map]
  omega

private theorem aut_planeTreeInduction {motive : PlaneTree → Prop}
    (step : ∀ cs : List PlaneTree,
      (∀ c ∈ cs, motive c) → motive (node cs)) :
    ∀ t, motive t
  | node cs => step cs fun c _hc => aut_planeTreeInduction step c
termination_by t => t.size
decreasing_by exact aut_size_lt_of_mem _hc

/-- The graph-theoretic parent fiber has the recursive child count. -/
theorem card_graphChildren_eq_childCount :
    ∀ {t : PlaneTree} (v : VPos t),
      (graphChildren v).card = childCount t v.1 := by
  intro t
  induction t using aut_planeTreeInduction with
  | step cs ih =>
      intro v
      induction v using vpos_node_cases with
      | hroot =>
          rw [graphChildren_root, Finset.card_image_of_injective]
          · change Fintype.card (Fin cs.length) = cs.length
            exact Fintype.card_fin _
          · exact fun _ _ h => childV_inj_idx h
      | hchild i v =>
          rw [graphChildren_child, Finset.card_image_of_injective]
          · simpa [childCount, i.isLt] using
              ih (cs.get i) (List.get_mem cs i) v
          · exact fun _ _ h => childV_inj_snd h

/-! ## Invariance under automorphisms -/

/-- A parent-commuting automorphism maps the child fiber of `v` bijectively
onto the child fiber of `g v`. -/
theorem image_graphChildren_aut {t : PlaneTree}
    (g : Aut t) (v : VPos t) :
    (graphChildren v).image g.1 = graphChildren (g.1 v) := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    rw [mem_graphChildren] at hu ⊢
    exact ⟨(g.2 u).symm.trans (congrArg g.1 hu.1),
      fun h => hu.2 (g.1.injective h)⟩
  · intro hw
    rw [mem_graphChildren] at hw
    let u : VPos t := g.1.symm w
    have hparent : parentV u = v := by
      apply g.1.injective
      calc
        g.1 (parentV u) = parentV (g.1 u) := g.2 u
        _ = parentV w := congrArg parentV (Equiv.apply_symm_apply g.1 w)
        _ = g.1 v := hw.1
    have hne : u ≠ v := by
      intro h
      apply hw.2
      calc
        w = g.1 u := (Equiv.apply_symm_apply g.1 w).symm
        _ = g.1 v := congrArg g.1 h
    exact Finset.mem_image.mpr
      ⟨u, mem_graphChildren.mpr ⟨hparent, hne⟩,
        Equiv.apply_symm_apply g.1 w⟩

/-- Automorphisms preserve the number of children at every vertex. -/
theorem childCount_aut {t : PlaneTree} (g : Aut t) (v : VPos t) :
    childCount t (g.1 v).1 = childCount t v.1 := by
  calc
    childCount t (g.1 v).1 = (graphChildren (g.1 v)).card :=
      (card_graphChildren_eq_childCount (g.1 v)).symm
    _ = ((graphChildren v).image g.1).card :=
      congrArg Finset.card (image_graphChildren_aut g v).symm
    _ = (graphChildren v).card :=
      Finset.card_image_of_injective _ g.1.injective
    _ = childCount t v.1 := card_graphChildren_eq_childCount v

theorem aut_mem_Leaves_iff {t : PlaneTree} (g : Aut t) (v : VPos t) :
    g.1 v ∈ Leaves t ↔ v ∈ Leaves t := by
  simp only [mem_Leaves_iff, childCount_aut]

theorem aut_mem_BranchNodes_iff {t : PlaneTree}
    (g : Aut t) (v : VPos t) :
    g.1 v ∈ BranchNodes t ↔ v ∈ BranchNodes t := by
  simp only [mem_BranchNodes_iff, childCount_aut]

/-- The permutation induced by a tree automorphism on its leaves. -/
def autLeavesEquiv {t : PlaneTree} (g : Aut t) :
    {v // v ∈ Leaves t} ≃ {v // v ∈ Leaves t} :=
  Equiv.subtypeEquiv g.1 fun v => (aut_mem_Leaves_iff g v).symm

/-- The permutation induced by a tree automorphism on branch vertices. -/
def autBranchNodesEquiv {t : PlaneTree} (g : Aut t) :
    {v // v ∈ BranchNodes t} ≃ {v // v ∈ BranchNodes t} :=
  Equiv.subtypeEquiv g.1 fun v => (aut_mem_BranchNodes_iff g v).symm

@[simp]
theorem autLeavesEquiv_apply_val {t : PlaneTree} (g : Aut t)
    (l : {v // v ∈ Leaves t}) :
    (autLeavesEquiv g l).1 = g.1 l.1 :=
  rfl

@[simp]
theorem autBranchNodesEquiv_apply_val {t : PlaneTree} (g : Aut t)
    (v : {v // v ∈ BranchNodes t}) :
    (autBranchNodesEquiv g v).1 = g.1 v.1 :=
  rfl

/-! ## Transporting the structured Hepp data -/

/-- Reindex a Hepp marking along a tree automorphism. -/
def smulHeppMarking {t : PlaneTree} (g : Aut t)
    (Nm : HeppMarking t) : HeppMarking t where
  Nexp := g • Nm.Nexp
  pos := by
    intro v hv
    exact Nm.pos ((g⁻¹ : Aut t).1 v)
      ((aut_mem_BranchNodes_iff (g⁻¹ : Aut t) v).mpr hv)
  parent_gt := by
    intro v hv hroot
    have hv' :
        (g⁻¹ : Aut t).1 v ∈ BranchNodes t :=
      (aut_mem_BranchNodes_iff (g⁻¹ : Aut t) v).mpr hv
    have hroot' :
        (g⁻¹ : Aut t).1 v ≠ rootV t := by
      intro h
      apply hroot
      have hg := congrArg g.1 h
      simpa [apply_root_eq] using hg
    simpa only [smul_marking_apply, ← (g⁻¹ : Aut t).2 v] using
      Nm.parent_gt ((g⁻¹ : Aut t).1 v) hv' hroot'

/-- Reindex leaf multiplicities along a tree automorphism. -/
def smulMultiplicities {t : PlaneTree} (g : Aut t)
    (mu : Multiplicities t) : Multiplicities t where
  m := fun v => mu.m ((g⁻¹ : Aut t).1 v)
  two_le := by
    intro v hv
    exact mu.two_le ((g⁻¹ : Aut t).1 v)
      ((aut_mem_Leaves_iff (g⁻¹ : Aut t) v).mpr hv)

@[simp]
theorem smulHeppMarking_Nexp {t : PlaneTree}
    (g : Aut t) (Nm : HeppMarking t) (v : VPos t) :
    (smulHeppMarking g Nm).Nexp v =
      Nm.Nexp ((g⁻¹ : Aut t).1 v) :=
  rfl

@[simp]
theorem smulMultiplicities_m {t : PlaneTree}
    (g : Aut t) (mu : Multiplicities t) (v : VPos t) :
    (smulMultiplicities g mu).m v =
      mu.m ((g⁻¹ : Aut t).1 v) :=
  rfl

/-- Structured transport agrees exactly with the raw marking action after
canonical zero extension. -/
theorem smulHeppMarking_canonicalRaw {t : PlaneTree}
    (g : Aut t) (Nm : HeppMarking t) :
    (smulHeppMarking g Nm).canonicalRaw = g • Nm.canonicalRaw := by
  funext v
  have hbranch :
      (g⁻¹ : Aut t).1 v ∈ BranchNodes t ↔ v ∈ BranchNodes t :=
    aut_mem_BranchNodes_iff (g⁻¹ : Aut t) v
  by_cases hv : v ∈ BranchNodes t
  · have hv' := hbranch.mpr hv
    rw [HeppMarking.canonicalRaw_apply_of_mem _ hv]
    change Nm.Nexp ((g⁻¹ : Aut t).1 v) =
      Nm.canonicalRaw ((g⁻¹ : Aut t).1 v)
    rw [HeppMarking.canonicalRaw_apply_of_mem _ hv']
  · have hv' : (g⁻¹ : Aut t).1 v ∉ BranchNodes t :=
      fun h => hv (hbranch.mp h)
    rw [HeppMarking.canonicalRaw_apply_of_not_mem _ hv]
    change 0 = Nm.canonicalRaw ((g⁻¹ : Aut t).1 v)
    rw [HeppMarking.canonicalRaw_apply_of_not_mem _ hv']

/-- Canonical leaf-only multiplicity data is transported by the same raw
function action. -/
theorem smulMultiplicities_canonicalRaw {t : PlaneTree}
    (g : Aut t) (mu : Multiplicities t) :
    (smulMultiplicities g mu).canonicalRaw = g • mu.canonicalRaw := by
  funext v
  have hleaf :
      (g⁻¹ : Aut t).1 v ∈ Leaves t ↔ v ∈ Leaves t :=
    aut_mem_Leaves_iff (g⁻¹ : Aut t) v
  by_cases hv : v ∈ Leaves t
  · have hv' := hleaf.mpr hv
    rw [Multiplicities.canonicalRaw_apply_of_mem _ hv]
    change mu.m ((g⁻¹ : Aut t).1 v) =
      mu.canonicalRaw ((g⁻¹ : Aut t).1 v)
    rw [Multiplicities.canonicalRaw_apply_of_mem _ hv']
  · have hv' : (g⁻¹ : Aut t).1 v ∉ Leaves t :=
      fun h => hv (hleaf.mp h)
    rw [Multiplicities.canonicalRaw_apply_of_not_mem _ hv]
    change 0 = mu.canonicalRaw ((g⁻¹ : Aut t).1 v)
    rw [Multiplicities.canonicalRaw_apply_of_not_mem _ hv']

@[simp]
theorem scaleN_smulHeppMarking {t : PlaneTree}
    (g : Aut t) (Nm : HeppMarking t) (v : VPos t) :
    scaleN (smulHeppMarking g Nm) v =
      scaleN Nm ((g⁻¹ : Aut t).1 v) :=
  rfl

/-- Total multiplicity is invariant under reindexing by an automorphism. -/
theorem sum_smulMultiplicities {t : PlaneTree}
    (g : Aut t) (mu : Multiplicities t) :
    (∑ l : {v // v ∈ Leaves t}, (smulMultiplicities g mu).m l.1) =
      ∑ l : {v // v ∈ Leaves t}, mu.m l.1 := by
  let e := autLeavesEquiv (g⁻¹ : Aut t)
  have he :
      ∀ l : {v // v ∈ Leaves t},
        (smulMultiplicities g mu).m l.1 = mu.m (e l).1 := by
    intro l
    rfl
  simp_rw [he]
  exact Equiv.sum_comp e (fun l => mu.m l.1)

/-- Leafwise parity is invariant under automorphism transport. -/
theorem smulMultiplicities_even_iff {t : PlaneTree}
    (g : Aut t) (mu : Multiplicities t) :
    (∀ l : {v // v ∈ Leaves t},
        Even ((smulMultiplicities g mu).m l.1)) ↔
      ∀ l : {v // v ∈ Leaves t}, Even (mu.m l.1) := by
  constructor
  · intro h l
    have := h (autLeavesEquiv g l)
    simpa [smulMultiplicities, autLeavesEquiv] using this
  · intro h l
    exact h (autLeavesEquiv (g⁻¹ : Aut t) l)

end Anderson4D
