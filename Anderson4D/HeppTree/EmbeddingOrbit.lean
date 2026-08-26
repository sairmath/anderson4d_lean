import Anderson4D.HeppTree.AutomorphismGeometry
import Anderson4D.HeppTree.RealizedSets
import Anderson4D.HeppTree.Incidence

/-!
# Free marked-automorphism orbits of admissible embeddings

This file formalizes the finite counting statement in paper §5.3, Step 2,
equation (5.18).  For fixed restricted branch data `N`, its marked-tree
automorphism group reindexes admissible leaf embeddings without changing
their underlying lattice-point set.  Since admissible embeddings are
injective and a rooted-tree automorphism is determined by its action on
leaves, this action is free.

Choosing one admissible embedding above each realized set therefore gives
an injection

`AutHeppMarked(t,N) × realizedSets(N) ↪ admissibleLeafEmbeddings(N)`,

which yields the desired division-free cardinality inequality.
-/

namespace Anderson4D

open PlaneTree

/-! ## Elementary extensionality and faithfulness on leaves -/

private theorem heppMarking_eq_of_Nexp_eq {t : PlaneTree}
    {Nm Nm' : HeppMarking t} (h : Nm.Nexp = Nm'.Nexp) :
    Nm = Nm' := by
  cases Nm with
  | mk Nexp pos parent_gt =>
      cases Nm' with
      | mk Nexp' pos' parent_gt' =>
          simpa only [HeppMarking.mk.injEq] using h

private theorem embeddingOrbit_size_lt_of_mem
    {c : PlaneTree} {cs : List PlaneTree} (hc : c ∈ cs) :
    c.size < (node cs).size := by
  have hmem : c.size ∈ cs.map size :=
    List.mem_map.mpr ⟨c, hc, rfl⟩
  have hle : c.size ≤ (cs.map size).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  simp only [size, sizeList_eq_map]
  omega

private theorem embeddingOrbit_planeTreeInduction
    {motive : PlaneTree → Prop}
    (step : ∀ cs : List PlaneTree,
      (∀ c ∈ cs, motive c) → motive (node cs)) :
    ∀ t, motive t
  | node cs =>
      step cs fun c _hc => embeddingOrbit_planeTreeInduction step c
termination_by t => t.size
decreasing_by exact embeddingOrbit_size_lt_of_mem _hc

/-- Every vertex has a leaf descendant. -/
private theorem exists_leaf_below :
    ∀ {t : PlaneTree} (v : VPos t),
      ∃ l : {l // l ∈ Leaves t}, IsAncestor v l.1 := by
  intro t
  induction t using embeddingOrbit_planeTreeInduction with
  | step cs ih =>
      intro v
      rcases vpos_node_cases_or v with rfl | ⟨i, w, rfl⟩
      · by_cases hcs : cs = []
        · subst cs
          let l : {l // l ∈ Leaves (node [])} :=
            ⟨rootV (node []), by simp [Leaves, childCount, rootV]⟩
          exact ⟨l, IsAncestor.refl _⟩
        · have hlen : 0 < cs.length := List.length_pos_iff.mpr hcs
          let i : Fin cs.length := ⟨0, hlen⟩
          obtain ⟨l, hl⟩ :=
            ih (cs.get i) (List.get_mem cs i) (rootV (cs.get i))
          exact ⟨rdec_leafUp i l,
            isAncestor_of_prefix _ _ List.nil_prefix⟩
      · obtain ⟨l, hl⟩ :=
          ih (cs.get i) (List.get_mem cs i) w
        refine ⟨rdec_leafUp i l, ?_⟩
        rw [isAncestor_iff_prefix] at hl ⊢
        exact List.cons_prefix_cons.mpr ⟨rfl, hl⟩

/-- Tree automorphisms preserve the depth of every vertex. -/
private theorem aut_path_length {t : PlaneTree}
    (g : Aut t) (v : VPos t) :
    (g.1 v).1.length = v.1.length := by
  generalize hn : v.1.length = n
  induction n generalizing v with
  | zero =>
      have hv : v = rootV t := by
        apply Subtype.ext
        exact List.length_eq_zero_iff.mp hn
      subst v
      simpa only [apply_root_eq]
  | succ n ih =>
      have hvne : v ≠ rootV t := by
        intro hv
        subst v
        change 0 = n + 1 at hn
        omega
      have hvnonempty : v.1 ≠ [] := ne_root_iff.mp hvne
      have hpLen : (parentV v).1.length = n := by
        change v.1.dropLast.length = n
        rw [List.length_dropLast, hn]
        omega
      have hparent := ih (parentV v) hpLen
      have hcomm := g.2 v
      have hparentImage :
          (parentV (g.1 v)).1.length = n := by
        rw [← hcomm]
        exact hparent
      have himageNe : g.1 v ≠ rootV t := by
        intro hroot
        apply hvne
        apply g.1.injective
        rw [hroot, apply_root_eq]
      have himageNonempty : (g.1 v).1 ≠ [] :=
        ne_root_iff.mp himageNe
      change (g.1 v).1.dropLast.length = n at hparentImage
      rw [List.length_dropLast] at hparentImage
      have himagePos : 0 < (g.1 v).1.length := by
        exact List.length_pos_iff.mpr himageNonempty
      omega

/-- The action of `Aut t` on the leaves is faithful. -/
theorem aut_eq_of_autLeavesEquiv_eq {t : PlaneTree}
    {g h : Aut t} (hleaf : autLeavesEquiv g = autLeavesEquiv h) :
    g = h := by
  apply Subtype.ext
  apply Equiv.ext
  intro v
  obtain ⟨l, hvl⟩ := exists_leaf_below v
  have hgl : g.1 l.1 = h.1 l.1 := by
    have happly := DFunLike.congr_fun hleaf l
    exact congrArg Subtype.val happly
  have hgAnc : IsAncestor (g.1 v) (g.1 l.1) :=
    hvl.map_aut g
  have hhAnc : IsAncestor (h.1 v) (g.1 l.1) := by
    rw [hgl]
    exact hvl.map_aut h
  apply Subtype.ext
  have hgTake :=
    List.prefix_iff_eq_take.mp hgAnc.prefix
  have hhTake :=
    List.prefix_iff_eq_take.mp hhAnc.prefix
  calc
    (g.1 v).1 =
        List.take (g.1 v).1.length (g.1 l.1).1 := hgTake
    _ = List.take (h.1 v).1.length (g.1 l.1).1 := by
      rw [aut_path_length g v, aut_path_length h v]
    _ = (h.1 v).1 := hhTake.symm

/-- For an injective leaf embedding, reindexing by distinct tree
automorphisms gives distinct embeddings. -/
theorem smulLeafEmbedding_left_injective {t : PlaneTree}
    (z : LeafEmbedding t) (hz : Function.Injective z) :
    Function.Injective (fun g : Aut t => smulLeafEmbedding g z) := by
  intro g h hsmul
  apply aut_eq_of_autLeavesEquiv_eq
  apply Equiv.ext
  intro l
  have heval := congrFun hsmul (autLeavesEquiv g l)
  have hzEq :
      z l =
        z ((autLeavesEquiv h).symm (autLeavesEquiv g l)) := by
    simpa [smulLeafEmbedding, reindexLeafEmbedding] using heval
  have hindex := hz hzEq
  have hmapped := congrArg (autLeavesEquiv h) hindex
  simpa using hmapped.symm

/-! ## The fixed-marking action on admissible embeddings -/

/-- For canonical restricted branch data, membership in the marked-tree
stabilizer fixes the bundled marking literally, not merely on branch
vertices.  The canonical zero extension is important here. -/
theorem smul_toHeppMarking_eq_of_mem_autHeppMarked
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (g : AutHeppMarked t (N.toHeppMarking hN)) :
    smulHeppMarking g.1 (N.toHeppMarking hN) =
      N.toHeppMarking hN := by
  apply heppMarking_eq_of_Nexp_eq
  let Nm := N.toHeppMarking hN
  have hcanonical : Nm.Nexp = Nm.canonicalRaw := by
    change N.raw = Nm.canonicalRaw
    exact (BranchExponentData.toHeppMarking_canonicalRaw N hN).symm
  funext v
  change Nm.Nexp (((g.1 : Aut t)⁻¹ : Aut t).1 v) = Nm.Nexp v
  rw [hcanonical]
  change (g.1 • Nm.canonicalRaw) v = Nm.canonicalRaw v
  exact congrFun (mem_autHeppMarked_iff.mp g.2) v

/-- The marked-tree stabilizer preserves admissibility for the fixed
restricted marking. -/
theorem IsAdmissible.map_autHeppMarked
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {z : LeafEmbedding t}
    (hz : IsAdmissible (N.toHeppMarking hN) M z)
    (g : AutHeppMarked t (N.toHeppMarking hN)) :
    IsAdmissible (N.toHeppMarking hN) M
      (smulLeafEmbedding g.1 z) := by
  have hmapped := hz.map_aut g.1
  rw [smul_toHeppMarking_eq_of_mem_autHeppMarked N hN g] at hmapped
  exact hmapped

/-- Reindexing by a tree automorphism preserves the unindexed lattice-point
set of an embedding. -/
@[simp] theorem leafEmbeddingImage_smulLeafEmbedding
    {t : PlaneTree} (g : Aut t) (z : LeafEmbedding t) :
    leafEmbeddingImage (smulLeafEmbedding g z) =
      leafEmbeddingImage z := by
  simpa [smulLeafEmbedding] using
    (leafEmbeddingImage_reindex (autLeavesEquiv g) z)

/-- The stabilizer itself is independent of the proof term witnessing
validity of the restricted marking. -/
theorem autHeppMarked_toHeppMarking_proof_irrel
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN hN' : N.IsValid) :
    AutHeppMarked t (N.toHeppMarking hN) =
      AutHeppMarked t (N.toHeppMarking hN') := by
  have hp : hN = hN' := Subsingleton.elim _ _
  cases hp
  rfl

/-! ## One representative above each realized set -/

/-- A noncanonical admissible embedding whose image is the given realized
set. -/
noncomputable def realizedSetRepresentative
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (Z : ↥(realizedSets N hN)) : LeafEmbedding t :=
  Classical.choose (Finset.mem_image.mp Z.2)

theorem realizedSetRepresentative_mem
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (Z : ↥(realizedSets N hN)) :
    realizedSetRepresentative N hN Z ∈
      admissibleLeafEmbeddings N hN :=
  (Classical.choose_spec (Finset.mem_image.mp Z.2)).1

theorem realizedSetRepresentative_image
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (Z : ↥(realizedSets N hN)) :
    leafEmbeddingImage (realizedSetRepresentative N hN Z) = Z.1 :=
  (Classical.choose_spec (Finset.mem_image.mp Z.2)).2

/-- The representative packaged in the finite admissible-embedding
carrier. -/
noncomputable def realizedSetRepresentativeEmbedding
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (Z : ↥(realizedSets N hN)) :
    ↥(admissibleLeafEmbeddings N hN) :=
  ⟨realizedSetRepresentative N hN Z,
    realizedSetRepresentative_mem N hN Z⟩

/-! ## The product injection and finite count -/

/-- Act on one chosen representative over each realized set. -/
noncomputable def markedOrbitEmbedding
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid) :
    AutHeppMarked t (N.toHeppMarking hN) ×
        ↥(realizedSets N hN) →
      ↥(admissibleLeafEmbeddings N hN) :=
  fun p => by
    let z := realizedSetRepresentativeEmbedding N hN p.2
    refine ⟨smulLeafEmbedding p.1.1 z.1, ?_⟩
    rw [mem_admissibleLeafEmbeddings]
    exact
      (mem_admissibleLeafEmbeddings.mp z.2).map_autHeppMarked p.1

theorem markedOrbitEmbedding_image
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (p : AutHeppMarked t (N.toHeppMarking hN) ×
        ↥(realizedSets N hN)) :
    leafEmbeddingImage (markedOrbitEmbedding N hN p).1 = p.2.1 := by
  change leafEmbeddingImage
      (smulLeafEmbedding p.1.1
        (realizedSetRepresentativeEmbedding N hN p.2).1) = p.2.1
  rw [leafEmbeddingImage_smulLeafEmbedding]
  exact realizedSetRepresentative_image N hN p.2

/-- Freeness on each representative and disjointness of distinct image
fibers make the product map injective. -/
theorem markedOrbitEmbedding_injective
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid) :
    Function.Injective (markedOrbitEmbedding N hN) := by
  intro p q hpq
  have himage :
      leafEmbeddingImage (markedOrbitEmbedding N hN p).1 =
        leafEmbeddingImage (markedOrbitEmbedding N hN q).1 :=
    congrArg (fun z => leafEmbeddingImage z.1) hpq
  have hZval : p.2.1 = q.2.1 := by
    rw [markedOrbitEmbedding_image N hN p,
      markedOrbitEmbedding_image N hN q] at himage
    exact himage
  have hZ : p.2 = q.2 := Subtype.ext hZval
  have hrep :
      (realizedSetRepresentativeEmbedding N hN p.2).1 =
        (realizedSetRepresentativeEmbedding N hN q.2).1 := by
    rw [hZ]
  have hemb :
      smulLeafEmbedding p.1.1
          (realizedSetRepresentativeEmbedding N hN p.2).1 =
        smulLeafEmbedding q.1.1
          (realizedSetRepresentativeEmbedding N hN p.2).1 := by
    have hval := congrArg Subtype.val hpq
    change
      smulLeafEmbedding p.1.1
          (realizedSetRepresentativeEmbedding N hN p.2).1 =
        smulLeafEmbedding q.1.1
          (realizedSetRepresentativeEmbedding N hN q.2).1 at hval
    rwa [← hrep] at hval
  have hrepAdmissible :
      IsAdmissible (N.toHeppMarking hN) M
        (realizedSetRepresentativeEmbedding N hN p.2).1 :=
    mem_admissibleLeafEmbeddings.mp
      (realizedSetRepresentativeEmbedding N hN p.2).2
  have hgAut : p.1.1 = q.1.1 :=
    smulLeafEmbedding_left_injective _
      hrepAdmissible.inj hemb
  have hg : p.1 = q.1 := Subtype.ext hgAut
  exact Prod.ext hg hZ

/-- Paper (5.18), finite division-free form. -/
theorem card_autHeppMarked_mul_card_realizedSets_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid) :
    Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSets N hN).card
      ≤ (admissibleLeafEmbeddings N hN).card := by
  have hcard :=
    Fintype.card_le_of_injective (markedOrbitEmbedding N hN)
      (markedOrbitEmbedding_injective N hN)
  simpa [Fintype.card_prod, Fintype.card_coe] using hcard

/-- Proof-irrelevant form of (5.18): the validity proof used to name the
stabilizer may differ from the proof used to enumerate the two finite
carriers. -/
theorem card_autHeppMarked_mul_card_realizedSets_le_proof_irrel
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M))
    (hGroup hSets : N.IsValid) :
    Fintype.card (AutHeppMarked t (N.toHeppMarking hGroup)) *
        (realizedSets N hSets).card
      ≤ (admissibleLeafEmbeddings N hSets).card := by
  have hp : hGroup = hSets := Subsingleton.elim _ _
  cases hp
  exact card_autHeppMarked_mul_card_realizedSets_le N hGroup

end Anderson4D
