import Anderson4D.HeppTree.ClusterRestriction
import Anderson4D.HeppTree.LeafCard
import Anderson4D.HeppTree.OrbitBound
import Anderson4D.HeppTree.VolumeIteration

/-!
# The volume estimate of Proposition 5.6

Paper: D-hepp — Prop 5.6 — the volume estimate (5.12)–(5.14)

This file connects the finite actual-cluster carriers to the scalar
bookkeeping in `VolumeIteration`, then states the division-free forms of
paper (5.13) and (5.14).
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

/-- Every plane tree has at least one paper leaf. -/
theorem one_le_leafCount (t : PlaneTree) :
    1 ≤ t.leafCount := by
  obtain ⟨cs⟩ := t
  exact le_max_left 1 (leafCountList cs)

/-- A branching descendant has no larger dyadic scale than its ancestor. -/
theorem scaleN_branchDescendant_le
    {t : PlaneTree} (ht : t.isValid = true)
    (Nm : HeppMarking t) {v u : VPos t}
    (hu : u ∈ branchDescendants v) :
    scaleN Nm u ≤ scaleN Nm v := by
  have hmark :=
    marking_add_ancestorGap_le ht Nm
      (isAncestor_of_prefix v u (mem_branchDescendants.mp hu).2)
      (mem_branchDescendants.mp hu).1
  unfold scaleN
  exact Nat.pow_le_pow_right (by omega) (Nat.le_of_add_right_le hmark)

/-- Crude local form of the paper's final `O(r²)` comparison:
the accumulated scale below any vertex is at most `2r` times its own
dyadic scale. -/
theorem tildeScale_le_two_mul_leafCount_mul_scaleN
    {t : PlaneTree} (ht : t.isValid = true)
    (Nm : HeppMarking t) (v : VPos t) :
    tildeScale Nm v ≤
      2 * (t.leafCount : ℝ) * (scaleN Nm v : ℝ) := by
  have hpoint :
      ∀ u ∈ branchDescendants v,
        (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ) ≤
          (childCount t u.1 : ℝ) * (scaleN Nm v : ℝ) := by
    intro u hu
    gcongr
    exact_mod_cast scaleN_branchDescendant_le ht Nm hu
  have hsubset : branchDescendants v ⊆ BranchNodes t := by
    intro u hu
    exact (mem_branchDescendants.mp hu).1
  have hsumNat :
      (∑ u ∈ branchDescendants v, childCount t u.1) ≤
        2 * t.leafCount := by
    calc
      (∑ u ∈ branchDescendants v, childCount t u.1)
          ≤ ∑ u ∈ BranchNodes t, childCount t u.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ => Nat.zero_le _)
      _ ≤ 2 * (t.leafCount - 1) :=
        sum_branchNodes_childCount_le_two_mul_leafCount_sub_one t ht
      _ ≤ 2 * t.leafCount := Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  unfold tildeScale
  calc
    ∑ u ∈ branchDescendants v,
        (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ)
        ≤ ∑ u ∈ branchDescendants v,
            (childCount t u.1 : ℝ) * (scaleN Nm v : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = (∑ u ∈ branchDescendants v, (childCount t u.1 : ℝ)) *
          (scaleN Nm v : ℝ) := by rw [Finset.sum_mul]
    _ ≤ (2 * (t.leafCount : ℝ)) * (scaleN Nm v : ℝ) := by
      gcongr
      exact_mod_cast hsumNat
    _ = 2 * (t.leafCount : ℝ) * (scaleN Nm v : ℝ) := by ring

/-! ## The concrete one-child placement set -/

/-- Triangle inequality for the lattice sup norm. -/
theorem znorm_triangle (x y z : LatticePoint) :
    znorm (x - z) ≤ znorm (x - y) + znorm (y - z) := by
  have hadd (a b : LatticePoint) :
      znorm (a + b) ≤ znorm a + znorm b := by
    unfold znorm
    have h : (fun i => (((a + b) i) : ℝ)) =
        (fun i => ((a i : ℤ) : ℝ)) +
          (fun i => ((b i : ℤ) : ℝ)) := by
      funext i
      simp
    rw [h]
    exact norm_add_le _ _
  have h : x - z = (x - y) + (y - z) := by abel
  rw [h]
  exact hadd _ _

/-- The canonical shortest-path parent function extracted from an actual
cluster restriction. -/
noncomputable def actualLinkParent
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (zv : ClusterEmbeddingAt v)
    (hzv : zv ∈ clusterRestrictions N hN v)
    (root : ClusterChild v) :
    ClusterChild v → ClusterChild v :=
  linkParent hv
    ((clusterExtension_admissible N hN v zv hzv).linked v hv)
    root

/-- Possible values of a representative leaf of child `c`, after the
restriction on its selected parent child `p` has been fixed. -/
noncomputable def childAnchorCandidates
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (p c : ClusterChild v)
    (ep : ClusterEmbeddingAt p.1)
    (hep : ep ∈ clusterRestrictions N hN p.1) :
    Finset LatticePoint :=
  let Nm := N.toHeppMarking hN
  let Nr : ℝ := scaleN Nm v
  latticeBallUnion
    (actualClusterCover N hN p.1 ep hep Nr
      (by
        dsimp [Nr]
        exact_mod_cast scaleN_pos Nm v))
    (2 * (Nr + tildeScale Nm c.1))

/-- Cardinality form of the one-child lattice estimate (5.23). -/
theorem card_childAnchorCandidates_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (p c : ClusterChild v)
    (ep : ClusterEmbeddingAt p.1)
    (hep : ep ∈ clusterRestrictions N hN p.1) :
    ((childAnchorCandidates N hN p c ep hep).card : ℝ) ≤
      step5LatticeConstant *
        (scaleN (N.toHeppMarking hN) v : ℝ) ^ 4 *
        (1 + tildeScale (N.toHeppMarking hN) p.1 /
          scaleN (N.toHeppMarking hN) v) *
        (1 + tildeScale (N.toHeppMarking hN) c.1 /
          scaleN (N.toHeppMarking hN) v) ^ 4 := by
  let Nm := N.toHeppMarking hN
  let Nr : ℝ := scaleN Nm v
  have hNrPos : 0 < Nr := by
    dsimp [Nr]
    exact_mod_cast scaleN_pos Nm v
  have hNr : 1 ≤ Nr := by
    dsimp [Nr]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (scaleN_pos Nm v)))
  let Q :=
    actualClusterCover N hN p.1 ep hep Nr hNrPos
  have hQ :
      (Q.card : ℝ) ≤
        3 * (1 + tildeScale Nm p.1 / Nr) :=
    (actualClusterCover_spec N hN p.1 ep hep Nr hNrPos).2.2
  exact card_latticeBallUnion_step5_le Q Nr
    (tildeScale Nm p.1) (tildeScale Nm c.1)
    hNr (tildeScale_nonneg Nm p.1) (tildeScale_nonneg Nm c.1) hQ

/-- The representative of every non-root child selected by the canonical
link parent lies in its concrete (5.23) placement set. -/
theorem childAnchor_mem_candidates
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (zv : ClusterEmbeddingAt v)
    (hzv : zv ∈ clusterRestrictions N hN v)
    (root c p : ClusterChild v) (hc : c ≠ root)
    (hp : actualLinkParent N hN hv zv hzv root c = p)
    (f : ClusterLeafAt c.1) :
    zv (clusterLeafInclusion c.2 f) ∈
      childAnchorCandidates N hN p c
        (restrictClusterEmbedding p.2 zv)
        (restrictClusterEmbedding_mem p.2 hzv) := by
  let Nm := N.toHeppMarking hN
  let z := clusterExtension N hN v zv hzv
  have hadm : IsAdmissible Nm M z :=
    clusterExtension_admissible N hN v zv hzv
  have hlinked : LinkedChildren Nm z v :=
    hadm.linked v hv
  have hlink₀ :=
    isLink_linkParent hv hlinked root hc
  have hlink : IsLink Nm z v c.1 p.1 := by
    change IsLink Nm z v c.1
      (actualLinkParent N hN hv zv hzv root c).1 at hlink₀
    rwa [hp] at hlink₀
  obtain ⟨l, hl, l', hl', hll'⟩ := hlink
  let ep : ClusterEmbeddingAt p.1 :=
    restrictClusterEmbedding p.2 zv
  have hep : ep ∈ clusterRestrictions N hN p.1 :=
    restrictClusterEmbedding_mem p.2 hzv
  let Nr : ℝ := scaleN Nm v
  have hNrPos : 0 < Nr := by
    dsimp [Nr]
    exact_mod_cast scaleN_pos Nm v
  let Q := actualClusterCover N hN p.1 ep hep Nr hNrPos
  obtain ⟨q, hqQ, hqdist⟩ :=
    (actualClusterCover_spec N hN p.1 ep hep Nr hNrPos).2.1 l' hl'
  let lp : ClusterLeafAt p.1 := ⟨l', hl'⟩
  have hparent :
      clusterExtension N hN p.1 ep hep l' = z l' := by
    calc
      clusterExtension N hN p.1 ep hep l' = ep lp :=
        clusterExtension_value N hN p.1 ep hep lp
      _ = zv (clusterLeafInclusion p.2 lp) := rfl
      _ = z l' :=
        (clusterExtension_value N hN v zv hzv
          (clusterLeafInclusion p.2 lp)).symm
  have hqdist' : znorm (z l' - q) ≤ Nr := by
    rwa [hparent] at hqdist
  have hchild :
      znorm (z f.1 - z l) ≤ tildeScale Nm c.1 :=
    clusterDiameter_le_tildeScale hadm c.1 f.2 hl
  have hdist :
      znorm (z f.1 - q) ≤
        2 * (Nr + tildeScale Nm c.1) := by
    calc
      znorm (z f.1 - q)
          ≤ znorm (z f.1 - z l) + znorm (z l - q) :=
        znorm_triangle _ _ _
      _ ≤ tildeScale Nm c.1 +
          (znorm (z l - z l') + znorm (z l' - q)) := by
        gcongr
        exact znorm_triangle _ _ _
      _ ≤ tildeScale Nm c.1 + (Nr + Nr) := by
        gcongr
      _ ≤ 2 * (Nr + tildeScale Nm c.1) := by
        nlinarith [tildeScale_nonneg Nm c.1]
  rw [← clusterExtension_value N hN v zv hzv
    (clusterLeafInclusion c.2 f)]
  exact mem_latticeBallUnion.mpr ⟨q, hqQ, hdist⟩

/-! ## One-child finite-fiber count -/

/-- Once a selected parent restriction is fixed, the possible restrictions
on one non-root child are bounded by its (5.23) placement count times a
uniform bound for the internally anchored child carrier. -/
theorem card_childRestriction_image_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (root c p : ClusterChild v) (hc : c ≠ root)
    (S : Finset (ClusterEmbeddingAt v))
    (hS : ∀ zv ∈ S, zv ∈ clusterRestrictions N hN v)
    (ep : ClusterEmbeddingAt p.1)
    (hep : ep ∈ clusterRestrictions N hN p.1)
    (hparent :
      ∀ zv, ∀ hzvS : zv ∈ S,
        actualLinkParent N hN hv zv (hS zv hzvS) root c = p)
    (hfixed :
      ∀ zv ∈ S, restrictClusterEmbedding p.2 zv = ep)
    (f : ClusterLeafAt c.1) (A : ℝ) (hA : 0 ≤ A)
    (hchild :
      ∀ x : LatticePoint,
        (clusterJ0 N hN c.1 f x : ℝ) ≤ A) :
    (((S.image fun zv => restrictClusterEmbedding c.2 zv).card : ℕ) : ℝ)
      ≤ (step5LatticeConstant : ℝ) *
          (scaleN (N.toHeppMarking hN) v : ℝ) ^ 4 *
          (1 + tildeScale (N.toHeppMarking hN) p.1 /
            scaleN (N.toHeppMarking hN) v) *
          (1 + tildeScale (N.toHeppMarking hN) c.1 /
            scaleN (N.toHeppMarking hN) v) ^ 4 * A := by
  classical
  let C : Finset LatticePoint :=
    childAnchorCandidates N hN p c ep hep
  let U : Finset (ClusterEmbeddingAt c.1) :=
    C.biUnion fun x => anchoredClusterRestrictions N hN c.1 f x
  have himage :
      S.image (fun zv => restrictClusterEmbedding c.2 zv) ⊆ U := by
    intro ec hec
    obtain ⟨zv, hzvS, rfl⟩ := Finset.mem_image.mp hec
    have hzv := hS zv hzvS
    have hp := hparent zv hzvS
    have hplace :=
      childAnchor_mem_candidates N hN hv zv hzv root c p hc hp f
    have hplace' :
        restrictClusterEmbedding c.2 zv f ∈ C := by
      dsimp [C]
      have heq := hfixed zv hzvS
      subst ep
      exact hplace
    exact Finset.mem_biUnion.mpr
      ⟨restrictClusterEmbedding c.2 zv f, hplace',
        mem_anchoredClusterRestrictions.mpr
          ⟨restrictClusterEmbedding_mem c.2 hzv, rfl⟩⟩
  have hcardNat :
      (S.image fun zv => restrictClusterEmbedding c.2 zv).card ≤
        ∑ x ∈ C,
          (anchoredClusterRestrictions N hN c.1 f x).card := by
    calc
      (S.image fun zv => restrictClusterEmbedding c.2 zv).card
          ≤ U.card := Finset.card_le_card himage
      _ ≤ ∑ x ∈ C,
          (anchoredClusterRestrictions N hN c.1 f x).card := by
        exact Finset.card_biUnion_le
  have hcard :
      (((S.image fun zv =>
        restrictClusterEmbedding c.2 zv).card : ℕ) : ℝ) ≤
        (C.card : ℝ) * A := by
    calc
      (((S.image fun zv =>
          restrictClusterEmbedding c.2 zv).card : ℕ) : ℝ)
          ≤ ((∑ x ∈ C,
              (anchoredClusterRestrictions N hN c.1 f x).card : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      _ = ∑ x ∈ C,
          ((anchoredClusterRestrictions N hN c.1 f x).card : ℝ) := by
        simp
      _ ≤ ∑ _x ∈ C, A := by
        apply Finset.sum_le_sum
        intro x hx
        simpa [clusterJ0] using hchild x
      _ = (C.card : ℝ) * A := by simp
  calc
    (((S.image fun zv =>
        restrictClusterEmbedding c.2 zv).card : ℕ) : ℝ)
        ≤ (C.card : ℝ) * A := hcard
    _ ≤ ((step5LatticeConstant : ℝ) *
          (scaleN (N.toHeppMarking hN) v : ℝ) ^ 4 *
          (1 + tildeScale (N.toHeppMarking hN) p.1 /
            scaleN (N.toHeppMarking hN) v) *
          (1 + tildeScale (N.toHeppMarking hN) c.1 /
            scaleN (N.toHeppMarking hN) v) ^ 4) * A := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact card_childAnchorCandidates_le N hN p c ep hep

/-! ## Parent-before-child exposure order -/

/-- In every suffix, its head is either the distinguished root or its
selected parent has already disappeared from that suffix. -/
def IsSuffixExposure {α : Type*} [BEq α] [LawfulBEq α]
    (p : α → α) (root : α) : List α → Prop
  | [] => True
  | c :: cs => (c = root ∨ p c ∉ c :: cs) ∧
      IsSuffixExposure p root cs

/-- A strict parent-index decrease implies the recursive suffix exposure
property, even after earlier vertices have been removed. -/
theorem isSuffixExposure_of_index
    {α : Type*} [BEq α] [LawfulBEq α]
    (p : α → α) (root : α) (L : List α)
    (hnodup : L.Nodup)
    (h :
      ∀ c ∈ L, c ≠ root →
        p c ∉ L ∨ List.idxOf (p c) L < List.idxOf c L) :
    IsSuffixExposure p root L := by
  induction L with
  | nil => trivial
  | cons a L ih =>
      have haNot : a ∉ L := (List.nodup_cons.mp hnodup).1
      have hnodupTail : L.Nodup := (List.nodup_cons.mp hnodup).2
      rw [IsSuffixExposure]
      constructor
      · by_cases har : a = root
        · exact Or.inl har
        · right
          rcases h a (by simp) har with hnot | hlt
          · exact hnot
          · by_contra hmem
            rw [List.idxOf_cons_self] at hlt
            omega
      · apply ih hnodupTail
        intro c hc hcr
        have hccons : c ∈ a :: L := by simp [hc]
        rcases h c hccons hcr with hnot | hlt
        · exact Or.inl (fun hmem => hnot (by simp [hmem]))
        · by_cases hpca : p c = a
          · exact Or.inl (by
              intro hmem
              exact haNot (hpca ▸ hmem))
          · right
            by_cases hca : c = a
            · exact (haNot (hca ▸ hc)).elim
            · simpa [List.idxOf_cons_ne L (Ne.symm hpca),
                List.idxOf_cons_ne L (Ne.symm hca)] using hlt

/-- The distance-sorted child list of the canonical extension is a valid
suffix exposure order for its selected parent function. -/
theorem isSuffixExposure_actualLinkParent
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (zv : ClusterEmbeddingAt v)
    (hzv : zv ∈ clusterRestrictions N hN v)
    (root : ClusterChild v) :
    IsSuffixExposure
      (actualLinkParent N hN hv zv hzv root) root
      (childrenByLinkDistance (N.toHeppMarking hN)
        (clusterExtension N hN v zv hzv) v root) := by
  let Nm := N.toHeppMarking hN
  let z := clusterExtension N hN v zv hzv
  let L := childrenByLinkDistance Nm z v root
  have hlinked : LinkedChildren Nm z v :=
    (clusterExtension_admissible N hN v zv hzv).linked v hv
  apply isSuffixExposure_of_index _ _ L
    (childrenByLinkDistance_nodup Nm z v root)
  intro c hcL hc
  right
  simpa only [actualLinkParent] using
    (idxOf_linkParent_lt hv hlinked root hc)

/-! ## Multiplying the exposed child fibers -/

/-- Every cluster of an actual restriction has a leaf. -/
theorem clusterLeafAt_nonempty_of_actual
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} {zv : ClusterEmbeddingAt v}
    (hzv : zv ∈ clusterRestrictions N hN v) :
    Nonempty (ClusterLeafAt v) := by
  obtain ⟨G, hG, hcost⟩ :=
    hasClusterNetwork_of_isAdmissible
      (clusterExtension_admissible N hN v zv hzv) v
  exact hG.nonempty

/-- Per-child factor revealed in the parent-before-child exposure. -/
noncomputable def childExposureWeight
    {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (root : ClusterChild v)
    (p : ClusterChild v → ClusterChild v)
    (W : ClusterChild v → ℝ) (c : ClusterChild v) : ℝ :=
  if c = root then W c
  else
    (step5LatticeConstant : ℝ) * (scaleN Nm v : ℝ) ^ 4 *
      (1 + tildeScale Nm (p c).1 / scaleN Nm v) *
      (1 + tildeScale Nm c.1 / scaleN Nm v) ^ 4 * W c

theorem childExposureWeight_nonneg
    {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (root : ClusterChild v)
    (p : ClusterChild v → ClusterChild v)
    (W : ClusterChild v → ℝ) (hW : ∀ c, 0 ≤ W c)
    (c : ClusterChild v) :
    0 ≤ childExposureWeight Nm root p W c := by
  unfold childExposureWeight
  split_ifs
  · exact hW c
  · have hscale : (0 : ℝ) < scaleN Nm v := by
      exact_mod_cast scaleN_pos Nm v
    have hp :
        0 ≤ 1 + tildeScale Nm (p c).1 / scaleN Nm v := by
      have := div_nonneg (tildeScale_nonneg Nm (p c).1) hscale.le
      linarith
    have hc :
        0 ≤ 1 + tildeScale Nm c.1 / scaleN Nm v := by
      have := div_nonneg (tildeScale_nonneg Nm c.1) hscale.le
      linarith
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · exact hp
      · positivity
    · exact hW c

/-- Fiberwise multiplication along a parent-before-child exposure list. -/
theorem card_clusterFiber_le_exposureProduct
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (root : ClusterChild v) (froot : ClusterLeafAt root.1)
    (x : LatticePoint)
    (p : ClusterChild v → ClusterChild v)
    (W : ClusterChild v → ℝ) (hW0 : ∀ c, 0 ≤ W c)
    (hW :
      ∀ c (f : ClusterLeafAt c.1) (y : LatticePoint),
        (clusterJ0 N hN c.1 f y : ℝ) ≤ W c)
    (L : List (ClusterChild v))
    (F : Finset (ClusterEmbeddingAt v))
    (hF : ∀ zv ∈ F, zv ∈ clusterRestrictions N hN v)
    (hp :
      ∀ zv, ∀ hzvF : zv ∈ F,
        actualLinkParent N hN hv zv (hF zv hzvF) root = p)
    (hanchor :
      ∀ zv ∈ F, restrictClusterEmbedding root.2 zv froot = x)
    (hfixed :
      ∀ d, d ∉ L → ∀ zv ∈ F, ∀ zv' ∈ F,
        restrictClusterEmbedding d.2 zv =
          restrictClusterEmbedding d.2 zv')
    (hexposure : IsSuffixExposure p root L) :
    (F.card : ℝ) ≤
      (L.map
        (childExposureWeight (N.toHeppMarking hN) root p W)).prod := by
  induction L generalizing F with
  | nil =>
      simp only [List.map_nil, List.prod_nil]
      have hcard : F.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro zv hzv zv' hzv'
        apply restrictEmbeddingToChildren_injective
          (Nat.zero_lt_of_lt (mem_BranchNodes_iff.mp hv))
        funext d
        exact hfixed d (by simp) zv hzv zv' hzv'
      exact_mod_cast hcard
  | cons c cs ih =>
      rw [IsSuffixExposure] at hexposure
      obtain ⟨hhead, htail⟩ := hexposure
      let coord : ClusterEmbeddingAt v → ClusterEmbeddingAt c.1 :=
        fun zv => restrictClusterEmbedding c.2 zv
      let I : Finset (ClusterEmbeddingAt c.1) := F.image coord
      have hmaps :
          Set.MapsTo coord (F : Set (ClusterEmbeddingAt v))
            (I : Set (ClusterEmbeddingAt c.1)) := by
        intro zv hzv
        exact Finset.mem_image_of_mem coord hzv
      have hcardEq :
          F.card =
            ∑ ec ∈ I, (F.filter fun zv => coord zv = ec).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
      have htailNonneg :
          0 ≤ (cs.map
            (childExposureWeight
              (N.toHeppMarking hN) root p W)).prod := by
        apply List.prod_nonneg
        intro a ha
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
        exact childExposureWeight_nonneg
          (N.toHeppMarking hN) root p W hW0 d
      have himage :
          (I.card : ℝ) ≤
            childExposureWeight
              (N.toHeppMarking hN) root p W c := by
        rcases hhead with hcr | hparentDone
        · subst c
          have hsub :
              I ⊆ anchoredClusterRestrictions
                N hN root.1 froot x := by
            intro er her
            obtain ⟨zv, hzvF, rfl⟩ := Finset.mem_image.mp her
            exact mem_anchoredClusterRestrictions.mpr
              ⟨restrictClusterEmbedding_mem root.2 (hF zv hzvF),
                hanchor zv hzvF⟩
          calc
            (I.card : ℝ) ≤
                ((anchoredClusterRestrictions
                  N hN root.1 froot x).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
            _ = (clusterJ0 N hN root.1 froot x : ℝ) := by
              rfl
            _ ≤ W root := hW root froot x
            _ = childExposureWeight
                (N.toHeppMarking hN) root p W root := by
              simp [childExposureWeight]
        · by_cases hFempty : F = ∅
          · subst F
            simp only [I, Finset.image_empty, Finset.card_empty,
              Nat.cast_zero]
            exact childExposureWeight_nonneg
              (N.toHeppMarking hN) root p W hW0 c
          · obtain ⟨zbase, hzbase⟩ := Finset.nonempty_iff_ne_empty.mpr hFempty
            let ep : ClusterEmbeddingAt (p c).1 :=
              restrictClusterEmbedding (p c).2 zbase
            have hep : ep ∈ clusterRestrictions N hN (p c).1 :=
              restrictClusterEmbedding_mem (p c).2 (hF zbase hzbase)
            have hfix :
                ∀ zv ∈ F,
                  restrictClusterEmbedding (p c).2 zv = ep := by
              intro zv hzv
              exact hfixed (p c) hparentDone zv hzv zbase hzbase
            have hcne : c ≠ root := by
              intro hcr
              subst c
              have hfun := congrFun (hp zbase hzbase) root
              have hactual :
                  actualLinkParent N hN hv zbase (hF zbase hzbase)
                    root root = root := by
                simp [actualLinkParent]
              have hproot : p root = root := hfun.symm.trans hactual
              exact hparentDone (by simp [hproot])
            let fc : ClusterLeafAt c.1 :=
              Classical.choice
                (clusterLeafAt_nonempty_of_actual N hN
                  (restrictClusterEmbedding_mem c.2 (hF zbase hzbase)))
            have hbound :=
              card_childRestriction_image_le N hN hv root c (p c)
                hcne F hF ep hep
                (fun zv hzv => congrFun (hp zv hzv) c)
                hfix fc (W c) (hW0 c)
                (hW c fc)
            simpa only [I, coord, childExposureWeight, if_neg hcne] using hbound
      rw [hcardEq, Nat.cast_sum]
      simp only [List.map_cons, List.prod_cons]
      calc
        ∑ ec ∈ I,
            ((F.filter fun zv => coord zv = ec).card : ℝ)
            ≤ ∑ _ec ∈ I,
                (cs.map (childExposureWeight
                  (N.toHeppMarking hN) root p W)).prod := by
              apply Finset.sum_le_sum
              intro ec hec
              refine ih
                (F := F.filter fun zv => coord zv = ec) ?_ ?_ ?_ ?_ htail
              · intro zv hzv
                exact hF zv (Finset.mem_filter.mp hzv).1
              · intro zv hzv
                exact hp zv (Finset.mem_filter.mp hzv).1
              · intro zv hzv
                exact hanchor zv (Finset.mem_filter.mp hzv).1
              · intro d hd zv hzv zv' hzv'
                by_cases hdc : d = c
                · subst d
                  exact (Finset.mem_filter.mp hzv).2.trans
                    (Finset.mem_filter.mp hzv').2.symm
                · exact hfixed d (by simp [hdc, hd]) zv
                    (Finset.mem_filter.mp hzv).1 zv'
                    (Finset.mem_filter.mp hzv').1
        _ = (I.card : ℝ) *
              (cs.map (childExposureWeight
                (N.toHeppMarking hN) root p W)).prod := by simp
        _ ≤ childExposureWeight
              (N.toHeppMarking hN) root p W c *
              (cs.map (childExposureWeight
                (N.toHeppMarking hN) root p W)).prod :=
          mul_le_mul_of_nonneg_right himage htailNonneg

/-! ## Two anchored leaves in one parent fiber -/

/-- Child weight for the two-anchor exposure.

If both anchors lie in the root child, its recursive weight is replaced by
the two-anchor weight `P`.  If they lie in distinct children, the second
anchored child pays the usual one-anchor placement weight times the saved
factor `N_v⁻⁴`. -/
noncomputable def pairChildExposureWeight
    {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (root₀ root₁ : ClusterChild v)
    (p : ClusterChild v → ClusterChild v)
    (W : ClusterChild v → ℝ) (P : ℝ)
    (c : ClusterChild v) : ℝ :=
  if root₀ = root₁ then
    childExposureWeight Nm root₀ p
      (fun d => if d = root₀ then P else W d) c
  else
    childExposureWeight Nm root₀ p W c *
      (if c = root₁ then lcaScaleGain Nm v else 1)

theorem pairChildExposureWeight_nonneg
    {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (root₀ root₁ : ClusterChild v)
    (p : ClusterChild v → ClusterChild v)
    (W : ClusterChild v → ℝ) (hW0 : ∀ c, 0 ≤ W c)
    (P : ℝ) (hP0 : 0 ≤ P) (c : ClusterChild v) :
    0 ≤ pairChildExposureWeight Nm root₀ root₁ p W P c := by
  unfold pairChildExposureWeight
  split_ifs with hsame hfree
  · apply childExposureWeight_nonneg
    intro d
    split_ifs
    · exact hP0
    · exact hW0 d
  · exact mul_nonneg
      (childExposureWeight_nonneg Nm root₀ p W hW0 c)
      (lcaScaleGain_nonneg Nm v)
  · exact mul_nonneg
      (childExposureWeight_nonneg Nm root₀ p W hW0 c)
      (by norm_num)

/-- Fixing an anchor in a non-root child is no more expensive than the
ordinary placement weight with the `N_v⁻⁴` gain inserted. -/
theorem childWeight_le_exposureWeight_mul_lcaScaleGain
    {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (root c : ClusterChild v) (hc : c ≠ root)
    (p : ClusterChild v → ClusterChild v)
    (W : ClusterChild v → ℝ) (hW0 : 0 ≤ W c) :
    W c ≤
      childExposureWeight Nm root p W c * lcaScaleGain Nm v := by
  let Nv : ℝ := scaleN Nm v
  have hNv : 0 < Nv := by
    dsimp [Nv]
    exact_mod_cast scaleN_pos Nm v
  have hC :
      1 ≤ (step5LatticeConstant : ℝ) := by
    norm_num [step5LatticeConstant]
  have hp :
      1 ≤ 1 + tildeScale Nm (p c).1 / Nv := by
    have hratio :=
      div_nonneg (tildeScale_nonneg Nm (p c).1) hNv.le
    linarith
  have hcscale :
      1 ≤ (1 + tildeScale Nm c.1 / Nv) ^ 4 := by
    apply one_le_pow₀
    have hratio :=
      div_nonneg (tildeScale_nonneg Nm c.1) hNv.le
    linarith
  have hfactor :
      1 ≤ (step5LatticeConstant : ℝ) *
          (1 + tildeScale Nm (p c).1 / Nv) *
          (1 + tildeScale Nm c.1 / Nv) ^ 4 := by
    calc
      (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ (step5LatticeConstant : ℝ) *
          (1 + tildeScale Nm (p c).1 / Nv) *
          (1 + tildeScale Nm c.1 / Nv) ^ 4 := by
        gcongr
  rw [childExposureWeight, if_neg hc, lcaScaleGain]
  change W c ≤
    ((step5LatticeConstant : ℝ) * Nv ^ 4 *
      (1 + tildeScale Nm (p c).1 / Nv) *
      (1 + tildeScale Nm c.1 / Nv) ^ 4 * W c) *
      (Nv ^ 4)⁻¹
  have hNv4 : Nv ^ 4 ≠ 0 := pow_ne_zero _ hNv.ne'
  rw [show
      ((step5LatticeConstant : ℝ) * Nv ^ 4 *
        (1 + tildeScale Nm (p c).1 / Nv) *
        (1 + tildeScale Nm c.1 / Nv) ^ 4 * W c) *
        (Nv ^ 4)⁻¹ =
      W c *
        ((step5LatticeConstant : ℝ) *
          (1 + tildeScale Nm (p c).1 / Nv) *
          (1 + tildeScale Nm c.1 / Nv) ^ 4) by
    field_simp]
  exact le_mul_of_one_le_right hW0 hfactor

/-- Fiberwise exposure with two fixed anchored leaves.  This is the
carrier-level Step 6 refinement: in the split-child case the second fixed
anchor removes one lattice placement. -/
theorem card_clusterPairFiber_le_exposureProduct
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (root₀ root₁ : ClusterChild v)
    (froot₀ : ClusterLeafAt root₀.1)
    (froot₁ : ClusterLeafAt root₁.1)
    (x₀ x₁ : LatticePoint)
    (p : ClusterChild v → ClusterChild v)
    (W : ClusterChild v → ℝ) (hW0 : ∀ c, 0 ≤ W c)
    (hW :
      ∀ c (f : ClusterLeafAt c.1) (y : LatticePoint),
        (clusterJ0 N hN c.1 f y : ℝ) ≤ W c)
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP :
      ∀ hsame : root₀ = root₁,
        (clusterJ01 N hN root₀.1 froot₀
          (hsame.symm ▸ froot₁) x₀ x₁ : ℝ) ≤ P)
    (L : List (ClusterChild v))
    (F : Finset (ClusterEmbeddingAt v))
    (hF : ∀ zv ∈ F, zv ∈ clusterRestrictions N hN v)
    (hp :
      ∀ zv, ∀ hzvF : zv ∈ F,
        actualLinkParent N hN hv zv (hF zv hzvF) root₀ = p)
    (hanchor₀ :
      ∀ zv ∈ F, restrictClusterEmbedding root₀.2 zv froot₀ = x₀)
    (hanchor₁ :
      ∀ zv ∈ F, restrictClusterEmbedding root₁.2 zv froot₁ = x₁)
    (hfixed :
      ∀ d, d ∉ L → ∀ zv ∈ F, ∀ zv' ∈ F,
        restrictClusterEmbedding d.2 zv =
          restrictClusterEmbedding d.2 zv')
    (hexposure : IsSuffixExposure p root₀ L) :
    (F.card : ℝ) ≤
      (L.map
        (pairChildExposureWeight
          (N.toHeppMarking hN) root₀ root₁ p W P)).prod := by
  induction L generalizing F with
  | nil =>
      simp only [List.map_nil, List.prod_nil]
      have hcard : F.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro zv hzv zv' hzv'
        apply restrictEmbeddingToChildren_injective
          (Nat.zero_lt_of_lt (mem_BranchNodes_iff.mp hv))
        funext d
        exact hfixed d (by simp) zv hzv zv' hzv'
      exact_mod_cast hcard
  | cons c cs ih =>
      rw [IsSuffixExposure] at hexposure
      obtain ⟨hhead, htail⟩ := hexposure
      let coord : ClusterEmbeddingAt v → ClusterEmbeddingAt c.1 :=
        fun zv => restrictClusterEmbedding c.2 zv
      let I : Finset (ClusterEmbeddingAt c.1) := F.image coord
      have hmaps :
          Set.MapsTo coord (F : Set (ClusterEmbeddingAt v))
            (I : Set (ClusterEmbeddingAt c.1)) := by
        intro zv hzv
        exact Finset.mem_image_of_mem coord hzv
      have hcardEq :
          F.card =
            ∑ ec ∈ I, (F.filter fun zv => coord zv = ec).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
      have htailNonneg :
          0 ≤ (cs.map
            (pairChildExposureWeight
              (N.toHeppMarking hN) root₀ root₁ p W P)).prod := by
        apply List.prod_nonneg
        intro a ha
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
        exact pairChildExposureWeight_nonneg
          (N.toHeppMarking hN) root₀ root₁ p W hW0 P hP0 d
      have himage :
          (I.card : ℝ) ≤
            pairChildExposureWeight
              (N.toHeppMarking hN) root₀ root₁ p W P c := by
        by_cases hsame : root₀ = root₁
        · subst root₁
          rcases hhead with hcr | hparentDone
          · subst c
            have hsub :
                I ⊆ doublyAnchoredClusterRestrictions
                  N hN root₀.1 froot₀ froot₁ x₀ x₁ := by
              intro er her
              obtain ⟨zv, hzvF, rfl⟩ := Finset.mem_image.mp her
              exact mem_doublyAnchoredClusterRestrictions.mpr
                ⟨restrictClusterEmbedding_mem root₀.2 (hF zv hzvF),
                  hanchor₀ zv hzvF, hanchor₁ zv hzvF⟩
            calc
              (I.card : ℝ) ≤
                  ((doublyAnchoredClusterRestrictions
                    N hN root₀.1 froot₀ froot₁ x₀ x₁).card : ℝ) := by
                exact_mod_cast Finset.card_le_card hsub
              _ = (clusterJ01 N hN root₀.1
                    froot₀ froot₁ x₀ x₁ : ℝ) := rfl
              _ ≤ P := by simpa using hP rfl
              _ = pairChildExposureWeight
                  (N.toHeppMarking hN) root₀ root₀ p W P root₀ := by
                simp [pairChildExposureWeight, childExposureWeight]
          · by_cases hFempty : F = ∅
            · subst F
              simp only [I, Finset.image_empty, Finset.card_empty,
                Nat.cast_zero]
              exact pairChildExposureWeight_nonneg
                (N.toHeppMarking hN) root₀ root₀ p W hW0 P hP0 c
            · obtain ⟨zbase, hzbase⟩ :=
                Finset.nonempty_iff_ne_empty.mpr hFempty
              let ep : ClusterEmbeddingAt (p c).1 :=
                restrictClusterEmbedding (p c).2 zbase
              have hep : ep ∈ clusterRestrictions N hN (p c).1 :=
                restrictClusterEmbedding_mem (p c).2 (hF zbase hzbase)
              have hfix :
                  ∀ zv ∈ F,
                    restrictClusterEmbedding (p c).2 zv = ep := by
                intro zv hzv
                exact hfixed (p c) hparentDone zv hzv zbase hzbase
              have hcne : c ≠ root₀ := by
                intro hcr
                subst c
                have hfun := congrFun (hp zbase hzbase) root₀
                have hactual :
                    actualLinkParent N hN hv zbase (hF zbase hzbase)
                      root₀ root₀ = root₀ := by
                  simp [actualLinkParent]
                have hproot : p root₀ = root₀ :=
                  hfun.symm.trans hactual
                exact hparentDone (by simp [hproot])
              let fc : ClusterLeafAt c.1 :=
                Classical.choice
                  (clusterLeafAt_nonempty_of_actual N hN
                    (restrictClusterEmbedding_mem c.2 (hF zbase hzbase)))
              have hbound :=
                card_childRestriction_image_le N hN hv root₀ c (p c)
                  hcne F hF ep hep
                  (fun zv hzv => congrFun (hp zv hzv) c)
                  hfix fc (W c) (hW0 c)
                  (hW c fc)
              simpa [I, coord, pairChildExposureWeight,
                childExposureWeight, hcne] using hbound
        · rcases hhead with hcr | hparentDone
          · subst c
            have hsub :
                I ⊆ anchoredClusterRestrictions
                  N hN root₀.1 froot₀ x₀ := by
              intro er her
              obtain ⟨zv, hzvF, rfl⟩ := Finset.mem_image.mp her
              exact mem_anchoredClusterRestrictions.mpr
                ⟨restrictClusterEmbedding_mem root₀.2 (hF zv hzvF),
                  hanchor₀ zv hzvF⟩
            calc
              (I.card : ℝ) ≤
                  ((anchoredClusterRestrictions
                    N hN root₀.1 froot₀ x₀).card : ℝ) := by
                exact_mod_cast Finset.card_le_card hsub
              _ = (clusterJ0 N hN root₀.1 froot₀ x₀ : ℝ) := rfl
              _ ≤ W root₀ := hW root₀ froot₀ x₀
              _ = pairChildExposureWeight
                  (N.toHeppMarking hN) root₀ root₁ p W P root₀ := by
                simp [pairChildExposureWeight, hsame,
                  childExposureWeight]
          · by_cases hcr₁ : c = root₁
            · subst c
              have hsub :
                  I ⊆ anchoredClusterRestrictions
                    N hN root₁.1 froot₁ x₁ := by
                intro er her
                obtain ⟨zv, hzvF, rfl⟩ := Finset.mem_image.mp her
                exact mem_anchoredClusterRestrictions.mpr
                  ⟨restrictClusterEmbedding_mem root₁.2 (hF zv hzvF),
                    hanchor₁ zv hzvF⟩
              have hcard :
                  (I.card : ℝ) ≤ W root₁ := by
                calc
                  (I.card : ℝ) ≤
                      ((anchoredClusterRestrictions
                        N hN root₁.1 froot₁ x₁).card : ℝ) := by
                    exact_mod_cast Finset.card_le_card hsub
                  _ = (clusterJ0 N hN root₁.1 froot₁ x₁ : ℝ) := rfl
                  _ ≤ W root₁ := hW root₁ froot₁ x₁
              calc
                (I.card : ℝ) ≤ W root₁ := hcard
                _ ≤ childExposureWeight
                      (N.toHeppMarking hN) root₀ p W root₁ *
                      lcaScaleGain (N.toHeppMarking hN) v :=
                  childWeight_le_exposureWeight_mul_lcaScaleGain
                    (N.toHeppMarking hN) root₀ root₁
                    (Ne.symm hsame) p W (hW0 root₁)
                _ = pairChildExposureWeight
                      (N.toHeppMarking hN) root₀ root₁ p W P root₁ := by
                  simp [pairChildExposureWeight, hsame]
            · by_cases hFempty : F = ∅
              · subst F
                simp only [I, Finset.image_empty, Finset.card_empty,
                  Nat.cast_zero]
                exact pairChildExposureWeight_nonneg
                  (N.toHeppMarking hN) root₀ root₁ p W hW0 P hP0 c
              · obtain ⟨zbase, hzbase⟩ :=
                  Finset.nonempty_iff_ne_empty.mpr hFempty
                let ep : ClusterEmbeddingAt (p c).1 :=
                  restrictClusterEmbedding (p c).2 zbase
                have hep : ep ∈ clusterRestrictions N hN (p c).1 :=
                  restrictClusterEmbedding_mem (p c).2 (hF zbase hzbase)
                have hfix :
                    ∀ zv ∈ F,
                      restrictClusterEmbedding (p c).2 zv = ep := by
                  intro zv hzv
                  exact hfixed (p c) hparentDone zv hzv zbase hzbase
                have hcne : c ≠ root₀ := by
                  intro hcr
                  subst c
                  have hfun := congrFun (hp zbase hzbase) root₀
                  have hactual :
                      actualLinkParent N hN hv zbase (hF zbase hzbase)
                        root₀ root₀ = root₀ := by
                    simp [actualLinkParent]
                  have hproot : p root₀ = root₀ :=
                    hfun.symm.trans hactual
                  exact hparentDone (by simp [hproot])
                let fc : ClusterLeafAt c.1 :=
                  Classical.choice
                    (clusterLeafAt_nonempty_of_actual N hN
                      (restrictClusterEmbedding_mem c.2 (hF zbase hzbase)))
                have hbound :=
                  card_childRestriction_image_le N hN hv root₀ c (p c)
                    hcne F hF ep hep
                    (fun zv hzv => congrFun (hp zv hzv) c)
                    hfix fc (W c) (hW0 c)
                    (hW c fc)
                simpa [I, coord, pairChildExposureWeight,
                  childExposureWeight, hsame, hcr₁, hcne] using hbound
      rw [hcardEq, Nat.cast_sum]
      simp only [List.map_cons, List.prod_cons]
      calc
        ∑ ec ∈ I,
            ((F.filter fun zv => coord zv = ec).card : ℝ)
            ≤ ∑ _ec ∈ I,
                (cs.map (pairChildExposureWeight
                  (N.toHeppMarking hN) root₀ root₁ p W P)).prod := by
              apply Finset.sum_le_sum
              intro ec hec
              refine ih
                (F := F.filter fun zv => coord zv = ec) ?_ ?_ ?_ ?_ ?_ htail
              · intro zv hzv
                exact hF zv (Finset.mem_filter.mp hzv).1
              · intro zv hzv
                exact hp zv (Finset.mem_filter.mp hzv).1
              · intro zv hzv
                exact hanchor₀ zv (Finset.mem_filter.mp hzv).1
              · intro zv hzv
                exact hanchor₁ zv (Finset.mem_filter.mp hzv).1
              · intro d hd zv hzv zv' hzv'
                by_cases hdc : d = c
                · subst d
                  exact (Finset.mem_filter.mp hzv).2.trans
                    (Finset.mem_filter.mp hzv').2.symm
                · exact hfixed d (by simp [hdc, hd]) zv
                    (Finset.mem_filter.mp hzv).1 zv'
                    (Finset.mem_filter.mp hzv').1
        _ = (I.card : ℝ) *
              (cs.map (pairChildExposureWeight
                (N.toHeppMarking hN) root₀ root₁ p W P)).prod := by simp
        _ ≤ pairChildExposureWeight
              (N.toHeppMarking hN) root₀ root₁ p W P c *
              (cs.map (pairChildExposureWeight
                (N.toHeppMarking hN) root₀ root₁ p W P)).prod :=
          mul_le_mul_of_nonneg_right himage htailNonneg

/-! ## One branch: summing the canonical parent-function fibers -/

/-- The immediate child containing an anchored cluster leaf. -/
noncomputable def anchorRootChild
    {t : PlaneTree} {v : VPos t}
    (hv : v ∈ BranchNodes t) (f : ClusterLeafAt v) :
    ClusterChild v :=
  Classical.choose
    (exists_child_containing_clusterLeaf
      (Nat.zero_lt_of_lt (mem_BranchNodes_iff.mp hv)) f)

theorem anchorRootChild_contains
    {t : PlaneTree} {v : VPos t}
    (hv : v ∈ BranchNodes t) (f : ClusterLeafAt v) :
    f.1 ∈ leavesUnder (anchorRootChild hv f).1 :=
  Classical.choose_spec
    (exists_child_containing_clusterLeaf
      (Nat.zero_lt_of_lt (mem_BranchNodes_iff.mp hv)) f)

/-- The anchored leaf, viewed inside its immediate root child. -/
def anchorLeafInRootChild
    {t : PlaneTree} {v : VPos t}
    (hv : v ∈ BranchNodes t) (f : ClusterLeafAt v) :
    ClusterLeafAt (anchorRootChild hv f).1 :=
  ⟨f.1, anchorRootChild_contains hv f⟩

/-- Transporting a cluster leaf across equality of its cluster child does
not change the underlying global leaf. -/
theorem cast_clusterLeafAt_val
    {t : PlaneTree} {v : VPos t}
    {c d : ClusterChild v} (h : c = d)
    (f : ClusterLeafAt d.1) :
    (h.symm ▸ f).1 = f.1 := by
  cases h
  rfl

/-- Total parent-code function used to partition an anchored carrier.  Away
from that carrier it takes the harmless identity fallback. -/
noncomputable def anchoredParentCode
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (f : ClusterLeafAt v) (x : LatticePoint)
    (zv : ClusterEmbeddingAt v) :
    ClusterChild v → ClusterChild v :=
  if hzv : zv ∈ anchoredClusterRestrictions N hN v f x then
    actualLinkParent N hN hv zv
      (mem_anchoredClusterRestrictions.mp hzv).1
      (anchorRootChild hv f)
  else fun c => c

theorem anchoredParentCode_eq
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (f : ClusterLeafAt v) (x : LatticePoint)
    {zv : ClusterEmbeddingAt v}
    (hzv : zv ∈ anchoredClusterRestrictions N hN v f x) :
    anchoredParentCode N hN hv f x zv =
      actualLinkParent N hN hv zv
        (mem_anchoredClusterRestrictions.mp hzv).1
        (anchorRootChild hv f) := by
  simp [anchoredParentCode, hzv]

/-- Product of the exposed child factors, separated into the recursive
child counts and the `fullParentWeight` consumed by Step 5. -/
theorem prod_childExposureWeight_eq
    {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (root : ClusterChild v)
    (p : ClusterChild v → ClusterChild v)
    (hpRoot : p root = root)
    (W : ClusterChild v → ℝ) :
    (∏ c : ClusterChild v,
        childExposureWeight Nm root p W c) =
      (∏ c : ClusterChild v, W c) *
        fullParentWeight root
          (fun c => 1 + tildeScale Nm c.1 / scaleN Nm v)
          (fun c =>
            (step5LatticeConstant : ℝ) *
              (scaleN Nm v : ℝ) ^ 4 *
              (1 + tildeScale Nm c.1 / scaleN Nm v) ^ 4)
          p := by
  unfold fullParentWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c hc
  by_cases hcr : c = root
  · subst c
    simp [childExposureWeight, hpRoot]
  · simp only [childExposureWeight, if_neg hcr]
    ring

/-- Bound one fiber of the canonical parent code by its full parent weight. -/
theorem card_anchoredParentFiber_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (f : ClusterLeafAt v) (x : LatticePoint)
    (W : ClusterChild v → ℝ) (hW0 : ∀ c, 0 ≤ W c)
    (hW :
      ∀ c (fc : ClusterLeafAt c.1) (y : LatticePoint),
        (clusterJ0 N hN c.1 fc y : ℝ) ≤ W c)
    (p : ClusterChild v → ClusterChild v) :
    let A := anchoredClusterRestrictions N hN v f x
    let F := A.filter fun zv =>
      anchoredParentCode N hN hv f x zv = p
    (F.card : ℝ) ≤
      (∏ c : ClusterChild v, W c) *
        fullParentWeight (anchorRootChild hv f)
          (fun c =>
            1 + tildeScale (N.toHeppMarking hN) c.1 /
              scaleN (N.toHeppMarking hN) v)
          (fun c =>
            (step5LatticeConstant : ℝ) *
              (scaleN (N.toHeppMarking hN) v : ℝ) ^ 4 *
              (1 + tildeScale (N.toHeppMarking hN) c.1 /
                scaleN (N.toHeppMarking hN) v) ^ 4)
          p := by
  classical
  dsimp only
  let A := anchoredClusterRestrictions N hN v f x
  let root := anchorRootChild hv f
  let froot := anchorLeafInRootChild hv f
  let F := A.filter fun zv =>
    anchoredParentCode N hN hv f x zv = p
  change (F.card : ℝ) ≤
    (∏ c : ClusterChild v, W c) *
      fullParentWeight root
        (fun c =>
          1 + tildeScale (N.toHeppMarking hN) c.1 /
            scaleN (N.toHeppMarking hN) v)
        (fun c =>
          (step5LatticeConstant : ℝ) *
            (scaleN (N.toHeppMarking hN) v : ℝ) ^ 4 *
            (1 + tildeScale (N.toHeppMarking hN) c.1 /
              scaleN (N.toHeppMarking hN) v) ^ 4)
        p
  by_cases hFempty : F = ∅
  · rw [hFempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    by_cases hpRoot : p root = root
    · rw [← prod_childExposureWeight_eq
        (N.toHeppMarking hN) root p hpRoot W]
      apply Finset.prod_nonneg
      intro c hc
      exact childExposureWeight_nonneg
        (N.toHeppMarking hN) root p W hW0 c
    · have hzero :
          fullParentWeight root
            (fun c =>
              1 + tildeScale (N.toHeppMarking hN) c.1 /
                scaleN (N.toHeppMarking hN) v)
            (fun c =>
              (step5LatticeConstant : ℝ) *
                (scaleN (N.toHeppMarking hN) v : ℝ) ^ 4 *
                (1 + tildeScale (N.toHeppMarking hN) c.1 /
                  scaleN (N.toHeppMarking hN) v) ^ 4)
            p = 0 := by
        unfold fullParentWeight
        exact Finset.prod_eq_zero (Finset.mem_univ root) (by simp [hpRoot])
      rw [hzero, mul_zero]
  · obtain ⟨zbase, hzbaseF⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hFempty
    have hzbaseA : zbase ∈ A :=
      (Finset.mem_filter.mp hzbaseF).1
    have hzbaseActual : zbase ∈ clusterRestrictions N hN v :=
      (mem_anchoredClusterRestrictions.mp hzbaseA).1
    have hpBase :
        actualLinkParent N hN hv zbase hzbaseActual root = p := by
      have hcode := (Finset.mem_filter.mp hzbaseF).2
      simpa only [root, anchoredParentCode_eq N hN hv f x hzbaseA] using hcode
    have hpRoot : p root = root := by
      have hfun := congrFun hpBase root
      have hactual :
          actualLinkParent N hN hv zbase hzbaseActual root root = root := by
        simp [actualLinkParent]
      exact hfun.symm.trans hactual
    let L :=
      childrenByLinkDistance (N.toHeppMarking hN)
        (clusterExtension N hN v zbase hzbaseActual) v root
    have hLnodup : L.Nodup :=
      childrenByLinkDistance_nodup _ _ _ _
    have hLall : L.toFinset =
        (Finset.univ : Finset (ClusterChild v)) := by
      ext c
      simp [L]
    have hexposure : IsSuffixExposure p root L := by
      have h :=
        isSuffixExposure_actualLinkParent N hN hv
          zbase hzbaseActual root
      rw [hpBase] at h
      exact h
    have hfiber :=
      card_clusterFiber_le_exposureProduct N hN hv root froot x p
        W hW0 hW L F
        (fun zv hzvF =>
          (mem_anchoredClusterRestrictions.mp
            (Finset.mem_filter.mp hzvF).1).1)
        (fun zv hzvF => by
          have hzvA := (Finset.mem_filter.mp hzvF).1
          have hcode := (Finset.mem_filter.mp hzvF).2
          simpa only [anchoredParentCode_eq N hN hv f x hzvA]
            using hcode)
        (fun zv hzvF => by
          have hzvA := (Finset.mem_filter.mp hzvF).1
          have hanchor :=
            (mem_anchoredClusterRestrictions.mp hzvA).2
          change zv f = x at hanchor
          simpa [froot, root, anchorLeafInRootChild,
            restrictClusterEmbedding, clusterLeafInclusion] using hanchor)
        (fun d hd => by
          exact (hd (mem_childrenByLinkDistance
            (N.toHeppMarking hN)
            (clusterExtension N hN v zbase hzbaseActual)
            v root d)).elim)
        hexposure
    calc
      (F.card : ℝ) ≤
          (L.map (childExposureWeight
            (N.toHeppMarking hN) root p W)).prod := hfiber
      _ = ∏ c : ClusterChild v,
          childExposureWeight (N.toHeppMarking hN) root p W c := by
        rw [← List.prod_toFinset _ hLnodup, hLall]
      _ = (∏ c : ClusterChild v, W c) *
          fullParentWeight root
            (fun c =>
              1 + tildeScale (N.toHeppMarking hN) c.1 /
                scaleN (N.toHeppMarking hN) v)
            (fun c =>
              (step5LatticeConstant : ℝ) *
                (scaleN (N.toHeppMarking hN) v : ℝ) ^ 4 *
                (1 + tildeScale (N.toHeppMarking hN) c.1 /
                  scaleN (N.toHeppMarking hN) v) ^ 4)
            p :=
        prod_childExposureWeight_eq
          (N.toHeppMarking hN) root p hpRoot W

/-- Product identity when both fixed leaves lie in the same child. -/
theorem prod_pairChildExposureWeight_eq_same
    {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (root₀ root₁ : ClusterChild v)
    (hsame : root₀ = root₁)
    (p : ClusterChild v → ClusterChild v)
    (hpRoot : p root₀ = root₀)
    (W : ClusterChild v → ℝ) (P : ℝ) :
    (∏ c : ClusterChild v,
        pairChildExposureWeight Nm root₀ root₁ p W P c) =
      (∏ c : ClusterChild v,
          if c = root₀ then P else W c) *
        fullParentWeight root₀
          (fun c => 1 + tildeScale Nm c.1 / scaleN Nm v)
          (fun c =>
            (step5LatticeConstant : ℝ) *
              (scaleN Nm v : ℝ) ^ 4 *
              (1 + tildeScale Nm c.1 / scaleN Nm v) ^ 4)
          p := by
  subst root₁
  simpa [pairChildExposureWeight] using
    prod_childExposureWeight_eq Nm root₀ p hpRoot
      (fun c => if c = root₀ then P else W c)

/-- Product identity when the fixed leaves first split at the current
branch.  Exactly one factor `N_v⁻⁴` survives. -/
theorem prod_pairChildExposureWeight_eq_split
    {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (root₀ root₁ : ClusterChild v)
    (hsplit : root₀ ≠ root₁)
    (p : ClusterChild v → ClusterChild v)
    (hpRoot : p root₀ = root₀)
    (W : ClusterChild v → ℝ) (P : ℝ) :
    (∏ c : ClusterChild v,
        pairChildExposureWeight Nm root₀ root₁ p W P c) =
      (∏ c : ClusterChild v, W c) *
        fullParentWeight root₀
          (fun c => 1 + tildeScale Nm c.1 / scaleN Nm v)
          (fun c =>
            (step5LatticeConstant : ℝ) *
              (scaleN Nm v : ℝ) ^ 4 *
              (1 + tildeScale Nm c.1 / scaleN Nm v) ^ 4)
          p *
        lcaScaleGain Nm v := by
  classical
  simp only [pairChildExposureWeight, if_neg hsplit,
    Finset.prod_mul_distrib]
  rw [Fintype.prod_ite_eq']
  rw [prod_childExposureWeight_eq Nm root₀ p hpRoot W]

/-- Finalized parent-code weight.  Unlike the raw exposure product, this
vanishes on functions that do not fix the distinguished root child. -/
noncomputable def pairParentVolumeWeight
    {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (root₀ root₁ : ClusterChild v)
    (p : ClusterChild v → ClusterChild v)
    (W : ClusterChild v → ℝ) (P : ℝ) : ℝ :=
  if root₀ = root₁ then
    (∏ c : ClusterChild v,
        if c = root₀ then P else W c) *
      fullParentWeight root₀
        (fun c => 1 + tildeScale Nm c.1 / scaleN Nm v)
        (fun c =>
          (step5LatticeConstant : ℝ) *
            (scaleN Nm v : ℝ) ^ 4 *
            (1 + tildeScale Nm c.1 / scaleN Nm v) ^ 4)
        p
  else
    (∏ c : ClusterChild v, W c) *
      fullParentWeight root₀
        (fun c => 1 + tildeScale Nm c.1 / scaleN Nm v)
        (fun c =>
          (step5LatticeConstant : ℝ) *
            (scaleN Nm v : ℝ) ^ 4 *
            (1 + tildeScale Nm c.1 / scaleN Nm v) ^ 4)
        p *
      lcaScaleGain Nm v

/-- Bound one two-anchor parent-code fiber by its exposed child product. -/
theorem card_doublyAnchoredParentFiber_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (f₀ f₁ : ClusterLeafAt v) (x₀ x₁ : LatticePoint)
    (W : ClusterChild v → ℝ) (hW0 : ∀ c, 0 ≤ W c)
    (hW :
      ∀ c (fc : ClusterLeafAt c.1) (y : LatticePoint),
        (clusterJ0 N hN c.1 fc y : ℝ) ≤ W c)
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP :
      ∀ hsame :
          anchorRootChild hv f₀ = anchorRootChild hv f₁,
        (clusterJ01 N hN (anchorRootChild hv f₀).1
          (anchorLeafInRootChild hv f₀)
          (hsame.symm ▸ anchorLeafInRootChild hv f₁)
          x₀ x₁ : ℝ) ≤ P)
    (p : ClusterChild v → ClusterChild v) :
    let A :=
      doublyAnchoredClusterRestrictions N hN v f₀ f₁ x₀ x₁
    let F := A.filter fun zv =>
      anchoredParentCode N hN hv f₀ x₀ zv = p
    (F.card : ℝ) ≤
      ∏ c : ClusterChild v,
        pairChildExposureWeight (N.toHeppMarking hN)
          (anchorRootChild hv f₀) (anchorRootChild hv f₁)
          p W P c := by
  classical
  dsimp only
  let A :=
    doublyAnchoredClusterRestrictions N hN v f₀ f₁ x₀ x₁
  let root₀ := anchorRootChild hv f₀
  let root₁ := anchorRootChild hv f₁
  let froot₀ := anchorLeafInRootChild hv f₀
  let froot₁ := anchorLeafInRootChild hv f₁
  let F := A.filter fun zv =>
    anchoredParentCode N hN hv f₀ x₀ zv = p
  change (F.card : ℝ) ≤
    ∏ c : ClusterChild v,
      pairChildExposureWeight (N.toHeppMarking hN)
        root₀ root₁ p W P c
  by_cases hFempty : F = ∅
  · rw [hFempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    apply Finset.prod_nonneg
    intro c hc
    exact pairChildExposureWeight_nonneg
      (N.toHeppMarking hN) root₀ root₁ p W hW0 P hP0 c
  · obtain ⟨zbase, hzbaseF⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hFempty
    have hzbaseA : zbase ∈ A :=
      (Finset.mem_filter.mp hzbaseF).1
    have hzbaseActual : zbase ∈ clusterRestrictions N hN v :=
      (mem_doublyAnchoredClusterRestrictions.mp hzbaseA).1
    have hzbaseAnchored₀ :
        zbase ∈ anchoredClusterRestrictions N hN v f₀ x₀ :=
      mem_anchoredClusterRestrictions.mpr
        ⟨hzbaseActual,
          (mem_doublyAnchoredClusterRestrictions.mp hzbaseA).2.1⟩
    have hpBase :
        actualLinkParent N hN hv zbase hzbaseActual root₀ = p := by
      have hcode := (Finset.mem_filter.mp hzbaseF).2
      simpa only [root₀,
        anchoredParentCode_eq N hN hv f₀ x₀ hzbaseAnchored₀] using hcode
    have hpRoot : p root₀ = root₀ := by
      have hfun := congrFun hpBase root₀
      have hactual :
          actualLinkParent N hN hv zbase hzbaseActual
            root₀ root₀ = root₀ := by
        simp [actualLinkParent]
      exact hfun.symm.trans hactual
    let L :=
      childrenByLinkDistance (N.toHeppMarking hN)
        (clusterExtension N hN v zbase hzbaseActual) v root₀
    have hLnodup : L.Nodup :=
      childrenByLinkDistance_nodup _ _ _ _
    have hLall : L.toFinset =
        (Finset.univ : Finset (ClusterChild v)) := by
      ext c
      simp [L]
    have hexposure : IsSuffixExposure p root₀ L := by
      have h :=
        isSuffixExposure_actualLinkParent N hN hv
          zbase hzbaseActual root₀
      rw [hpBase] at h
      exact h
    have hfiber :=
      card_clusterPairFiber_le_exposureProduct N hN hv
        root₀ root₁ froot₀ froot₁ x₀ x₁ p
        W hW0 hW P hP0
        (fun hsame => by
          simpa [root₀, root₁, froot₀, froot₁] using hP hsame)
        L F
        (fun zv hzvF =>
          (mem_doublyAnchoredClusterRestrictions.mp
            (Finset.mem_filter.mp hzvF).1).1)
        (fun zv hzvF => by
          have hzvA := (Finset.mem_filter.mp hzvF).1
          have hzvAnchored₀ :
              zv ∈ anchoredClusterRestrictions N hN v f₀ x₀ :=
            mem_anchoredClusterRestrictions.mpr
              ⟨(mem_doublyAnchoredClusterRestrictions.mp hzvA).1,
                (mem_doublyAnchoredClusterRestrictions.mp hzvA).2.1⟩
          have hcode := (Finset.mem_filter.mp hzvF).2
          simpa only [root₀,
            anchoredParentCode_eq N hN hv f₀ x₀ hzvAnchored₀]
            using hcode)
        (fun zv hzvF => by
          have hzvA := (Finset.mem_filter.mp hzvF).1
          have hanchor :=
            (mem_doublyAnchoredClusterRestrictions.mp hzvA).2.1
          change zv f₀ = x₀ at hanchor
          simpa [froot₀, root₀, anchorLeafInRootChild,
            restrictClusterEmbedding, clusterLeafInclusion] using hanchor)
        (fun zv hzvF => by
          have hzvA := (Finset.mem_filter.mp hzvF).1
          have hanchor :=
            (mem_doublyAnchoredClusterRestrictions.mp hzvA).2.2
          change zv f₁ = x₁ at hanchor
          simpa [froot₁, root₁, anchorLeafInRootChild,
            restrictClusterEmbedding, clusterLeafInclusion] using hanchor)
        (fun d hd => by
          exact (hd (mem_childrenByLinkDistance
            (N.toHeppMarking hN)
            (clusterExtension N hN v zbase hzbaseActual)
            v root₀ d)).elim)
        hexposure
    calc
      (F.card : ℝ) ≤
          (L.map (pairChildExposureWeight
            (N.toHeppMarking hN) root₀ root₁ p W P)).prod := hfiber
      _ = ∏ c : ClusterChild v,
          pairChildExposureWeight (N.toHeppMarking hN)
            root₀ root₁ p W P c := by
        rw [← List.prod_toFinset _ hLnodup, hLall]

/-- Finalized two-anchor fiber bound, including the root-fixing factor of
`fullParentWeight`.  This wrapper is needed for empty fibers indexed by
arbitrary parent functions. -/
theorem card_doublyAnchoredParentFiber_full_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (f₀ f₁ : ClusterLeafAt v) (x₀ x₁ : LatticePoint)
    (W : ClusterChild v → ℝ) (hW0 : ∀ c, 0 ≤ W c)
    (hW :
      ∀ c (fc : ClusterLeafAt c.1) (y : LatticePoint),
        (clusterJ0 N hN c.1 fc y : ℝ) ≤ W c)
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP :
      ∀ hsame :
          anchorRootChild hv f₀ = anchorRootChild hv f₁,
        (clusterJ01 N hN (anchorRootChild hv f₀).1
          (anchorLeafInRootChild hv f₀)
          (hsame.symm ▸ anchorLeafInRootChild hv f₁)
          x₀ x₁ : ℝ) ≤ P)
    (p : ClusterChild v → ClusterChild v) :
    let A :=
      doublyAnchoredClusterRestrictions N hN v f₀ f₁ x₀ x₁
    let F := A.filter fun zv =>
      anchoredParentCode N hN hv f₀ x₀ zv = p
    (F.card : ℝ) ≤
      pairParentVolumeWeight (N.toHeppMarking hN)
        (anchorRootChild hv f₀) (anchorRootChild hv f₁) p W P := by
  classical
  dsimp only
  let A :=
    doublyAnchoredClusterRestrictions N hN v f₀ f₁ x₀ x₁
  let root₀ := anchorRootChild hv f₀
  let root₁ := anchorRootChild hv f₁
  let F := A.filter fun zv =>
    anchoredParentCode N hN hv f₀ x₀ zv = p
  change (F.card : ℝ) ≤
    pairParentVolumeWeight (N.toHeppMarking hN)
      root₀ root₁ p W P
  have hraw :=
    card_doublyAnchoredParentFiber_le
      N hN hv f₀ f₁ x₀ x₁ W hW0 hW P hP0 hP p
  by_cases hFempty : F = ∅
  · rw [hFempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    by_cases hpr : p root₀ = root₀
    · by_cases hsame : root₀ = root₁
      · rw [show pairParentVolumeWeight (N.toHeppMarking hN)
              root₀ root₁ p W P =
            ∏ c : ClusterChild v,
              pairChildExposureWeight (N.toHeppMarking hN)
                root₀ root₁ p W P c by
            unfold pairParentVolumeWeight
            rw [if_pos hsame]
            exact (prod_pairChildExposureWeight_eq_same
              (N.toHeppMarking hN) root₀ root₁ hsame
              p hpr W P).symm]
        apply Finset.prod_nonneg
        intro c hc
        exact pairChildExposureWeight_nonneg
          (N.toHeppMarking hN) root₀ root₁ p W hW0 P hP0 c
      · rw [show pairParentVolumeWeight (N.toHeppMarking hN)
              root₀ root₁ p W P =
            ∏ c : ClusterChild v,
              pairChildExposureWeight (N.toHeppMarking hN)
                root₀ root₁ p W P c by
            unfold pairParentVolumeWeight
            rw [if_neg hsame]
            exact (prod_pairChildExposureWeight_eq_split
              (N.toHeppMarking hN) root₀ root₁ hsame
              p hpr W P).symm]
        apply Finset.prod_nonneg
        intro c hc
        exact pairChildExposureWeight_nonneg
          (N.toHeppMarking hN) root₀ root₁ p W hW0 P hP0 c
    · have hfull :
          fullParentWeight root₀
            (fun c =>
              1 + tildeScale (N.toHeppMarking hN) c.1 /
                scaleN (N.toHeppMarking hN) v)
            (fun c =>
              (step5LatticeConstant : ℝ) *
                (scaleN (N.toHeppMarking hN) v : ℝ) ^ 4 *
                (1 + tildeScale (N.toHeppMarking hN) c.1 /
                  scaleN (N.toHeppMarking hN) v) ^ 4)
            p = 0 := by
        unfold fullParentWeight
        exact Finset.prod_eq_zero (Finset.mem_univ root₀)
          (by simp [hpr])
      unfold pairParentVolumeWeight
      split_ifs <;> rw [hfull] <;> norm_num
  · obtain ⟨zbase, hzbaseF⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hFempty
    have hzbaseA : zbase ∈ A :=
      (Finset.mem_filter.mp hzbaseF).1
    have hzbaseActual : zbase ∈ clusterRestrictions N hN v :=
      (mem_doublyAnchoredClusterRestrictions.mp hzbaseA).1
    have hzbaseAnchored₀ :
        zbase ∈ anchoredClusterRestrictions N hN v f₀ x₀ :=
      mem_anchoredClusterRestrictions.mpr
        ⟨hzbaseActual,
          (mem_doublyAnchoredClusterRestrictions.mp hzbaseA).2.1⟩
    have hpBase :
        actualLinkParent N hN hv zbase hzbaseActual root₀ = p := by
      have hcode := (Finset.mem_filter.mp hzbaseF).2
      simpa only [root₀,
        anchoredParentCode_eq N hN hv f₀ x₀ hzbaseAnchored₀] using hcode
    have hpRoot : p root₀ = root₀ := by
      have hfun := congrFun hpBase root₀
      have hactual :
          actualLinkParent N hN hv zbase hzbaseActual
            root₀ root₀ = root₀ := by
        simp [actualLinkParent]
      exact hfun.symm.trans hactual
    by_cases hsame : root₀ = root₁
    · calc
        (F.card : ℝ) ≤
            ∏ c : ClusterChild v,
              pairChildExposureWeight (N.toHeppMarking hN)
                root₀ root₁ p W P c := by
          simpa [A, F, root₀, root₁] using hraw
        _ = pairParentVolumeWeight (N.toHeppMarking hN)
              root₀ root₁ p W P := by
          unfold pairParentVolumeWeight
          rw [if_pos hsame]
          exact prod_pairChildExposureWeight_eq_same
            (N.toHeppMarking hN) root₀ root₁ hsame
            p hpRoot W P
    · calc
        (F.card : ℝ) ≤
            ∏ c : ClusterChild v,
              pairChildExposureWeight (N.toHeppMarking hN)
                root₀ root₁ p W P c := by
          simpa [A, F, root₀, root₁] using hraw
        _ = pairParentVolumeWeight (N.toHeppMarking hN)
              root₀ root₁ p W P := by
          unfold pairParentVolumeWeight
          rw [if_neg hsame]
          exact prod_pairChildExposureWeight_eq_split
            (N.toHeppMarking hN) root₀ root₁ hsame
            p hpRoot W P

/-- Two-anchor carrier estimate before evaluating the parent-function sum. -/
theorem clusterJ01_branch_parent_sum_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (f₀ f₁ : ClusterLeafAt v) (x₀ x₁ : LatticePoint)
    (W : ClusterChild v → ℝ) (hW0 : ∀ c, 0 ≤ W c)
    (hW :
      ∀ c (fc : ClusterLeafAt c.1) (y : LatticePoint),
        (clusterJ0 N hN c.1 fc y : ℝ) ≤ W c)
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP :
      ∀ hsame :
          anchorRootChild hv f₀ = anchorRootChild hv f₁,
        (clusterJ01 N hN (anchorRootChild hv f₀).1
          (anchorLeafInRootChild hv f₀)
          (hsame.symm ▸ anchorLeafInRootChild hv f₁)
          x₀ x₁ : ℝ) ≤ P) :
    (clusterJ01 N hN v f₀ f₁ x₀ x₁ : ℝ) ≤
      ∑ p : ClusterChild v → ClusterChild v,
        pairParentVolumeWeight (N.toHeppMarking hN)
          (anchorRootChild hv f₀) (anchorRootChild hv f₁)
          p W P := by
  classical
  let A :=
    doublyAnchoredClusterRestrictions N hN v f₀ f₁ x₀ x₁
  let code := anchoredParentCode N hN hv f₀ x₀
  have hmaps :
      Set.MapsTo code (A : Set (ClusterEmbeddingAt v))
        (Finset.univ :
          Finset (ClusterChild v → ClusterChild v)) := by
    intro zv hzv
    exact Finset.mem_univ _
  have hcard :
      A.card =
        ∑ p : ClusterChild v → ClusterChild v,
          (A.filter fun zv => code zv = p).card := by
    simpa using Finset.card_eq_sum_card_fiberwise hmaps
  change (A.card : ℝ) ≤ _
  rw [hcard, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro p hp
  exact card_doublyAnchoredParentFiber_full_le
    N hN hv f₀ f₁ x₀ x₁ W hW0 hW P hP0 hP p

/-- Evaluated branch recursion when both anchors remain in the same
immediate child. -/
theorem clusterJ01_branch_le_same
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (f₀ f₁ : ClusterLeafAt v) (x₀ x₁ : LatticePoint)
    (hsame : anchorRootChild hv f₀ = anchorRootChild hv f₁)
    (W : ClusterChild v → ℝ) (hW0 : ∀ c, 0 ≤ W c)
    (hW :
      ∀ c (fc : ClusterLeafAt c.1) (y : LatticePoint),
        (clusterJ0 N hN c.1 fc y : ℝ) ≤ W c)
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP :
      (clusterJ01 N hN (anchorRootChild hv f₀).1
        (anchorLeafInRootChild hv f₀)
        (hsame.symm ▸ anchorLeafInRootChild hv f₁)
        x₀ x₁ : ℝ) ≤ P) :
    (clusterJ01 N hN v f₀ f₁ x₀ x₁ : ℝ) ≤
      (∏ c : ClusterChild v,
          if c = anchorRootChild hv f₀ then P else W c) *
        (childCount t v.1).factorial *
        (step5VolumeConstant : ℝ) ^ (childCount t v.1 - 1) *
        (scaleN (N.toHeppMarking hN) v : ℝ) ^
          (4 * (childCount t v.1 - 1)) *
        Real.exp
          (6 * ∑ c : ClusterChild v,
            tildeScale (N.toHeppMarking hN) c.1 /
              scaleN (N.toHeppMarking hN) v) := by
  let Nm := N.toHeppMarking hN
  let root := anchorRootChild hv f₀
  let w : ClusterChild v → ℝ :=
    fun c => tildeScale Nm c.1 / scaleN Nm v
  have hw : ∀ c, 0 ≤ w c := by
    intro c
    exact div_nonneg (tildeScale_nonneg Nm c.1)
      (by exact_mod_cast (Nat.zero_le (scaleN Nm v)))
  have hcard :
      Fintype.card (ClusterChild v) = childCount t v.1 := by
    rw [Fintype.card_coe, card_childrenOf]
  have hq : 2 ≤ Fintype.card (ClusterChild v) := by
    rw [hcard]
    exact mem_BranchNodes_iff.mp hv
  have hparent :=
    step5_parent_volume_bound root w hw hq (scaleN Nm v : ℝ)
  let W' : ClusterChild v → ℝ :=
    fun c => if c = root then P else W c
  have hW'0 : ∀ c, 0 ≤ W' c := by
    intro c
    simp only [W']
    split_ifs
    · exact hP0
    · exact hW0 c
  have hprod :
      0 ≤ ∏ c : ClusterChild v, W' c :=
    Finset.prod_nonneg fun c hc => hW'0 c
  have hcarrier :=
    clusterJ01_branch_parent_sum_le N hN hv f₀ f₁ x₀ x₁
      W hW0 hW P hP0 (fun h => by
        have heq : h = hsame := Subsingleton.elim _ _
        simpa [heq] using hP)
  calc
    (clusterJ01 N hN v f₀ f₁ x₀ x₁ : ℝ) ≤
        ∑ p : ClusterChild v → ClusterChild v,
          (∏ c : ClusterChild v, W' c) *
            fullParentWeight root
              (fun c => 1 + w c)
              (fun c =>
                (step5LatticeConstant : ℝ) *
                  (scaleN Nm v : ℝ) ^ 4 * (1 + w c) ^ 4)
              p := by
      simpa [pairParentVolumeWeight, hsame, root, Nm, w, W']
        using hcarrier
    _ = (∏ c : ClusterChild v, W' c) *
        ∑ p : ClusterChild v → ClusterChild v,
          fullParentWeight root
            (fun c => 1 + w c)
            (fun c =>
              (step5LatticeConstant : ℝ) *
                (scaleN Nm v : ℝ) ^ 4 * (1 + w c) ^ 4)
            p := by rw [Finset.mul_sum]
    _ ≤ (∏ c : ClusterChild v, W' c) *
          ((Fintype.card (ClusterChild v)).factorial *
            (step5VolumeConstant : ℝ) ^
              (Fintype.card (ClusterChild v) - 1) *
            (scaleN Nm v : ℝ) ^
              (4 * (Fintype.card (ClusterChild v) - 1)) *
            Real.exp (6 * ∑ c, w c)) :=
      mul_le_mul_of_nonneg_left hparent hprod
    _ = (∏ c : ClusterChild v,
            if c = anchorRootChild hv f₀ then P else W c) *
          (childCount t v.1).factorial *
          (step5VolumeConstant : ℝ) ^ (childCount t v.1 - 1) *
          (scaleN Nm v : ℝ) ^ (4 * (childCount t v.1 - 1)) *
          Real.exp (6 * ∑ c, w c) := by
      rw [hcard]
      simp only [W', root]
      ring

/-- Evaluated branch recursion at the first child split. -/
theorem clusterJ01_branch_le_split
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (f₀ f₁ : ClusterLeafAt v) (x₀ x₁ : LatticePoint)
    (hsplit : anchorRootChild hv f₀ ≠ anchorRootChild hv f₁)
    (W : ClusterChild v → ℝ) (hW0 : ∀ c, 0 ≤ W c)
    (hW :
      ∀ c (fc : ClusterLeafAt c.1) (y : LatticePoint),
        (clusterJ0 N hN c.1 fc y : ℝ) ≤ W c) :
    (clusterJ01 N hN v f₀ f₁ x₀ x₁ : ℝ) ≤
      (∏ c : ClusterChild v, W c) *
        (childCount t v.1).factorial *
        (step5VolumeConstant : ℝ) ^ (childCount t v.1 - 1) *
        (scaleN (N.toHeppMarking hN) v : ℝ) ^
          (4 * (childCount t v.1 - 1)) *
        Real.exp
          (6 * ∑ c : ClusterChild v,
            tildeScale (N.toHeppMarking hN) c.1 /
              scaleN (N.toHeppMarking hN) v) *
        lcaScaleGain (N.toHeppMarking hN) v := by
  let Nm := N.toHeppMarking hN
  let root := anchorRootChild hv f₀
  let w : ClusterChild v → ℝ :=
    fun c => tildeScale Nm c.1 / scaleN Nm v
  have hw : ∀ c, 0 ≤ w c := by
    intro c
    exact div_nonneg (tildeScale_nonneg Nm c.1)
      (by exact_mod_cast (Nat.zero_le (scaleN Nm v)))
  have hcard :
      Fintype.card (ClusterChild v) = childCount t v.1 := by
    rw [Fintype.card_coe, card_childrenOf]
  have hq : 2 ≤ Fintype.card (ClusterChild v) := by
    rw [hcard]
    exact mem_BranchNodes_iff.mp hv
  have hparent :=
    step5_parent_volume_bound root w hw hq (scaleN Nm v : ℝ)
  have hprod :
      0 ≤ ∏ c : ClusterChild v, W c :=
    Finset.prod_nonneg fun c hc => hW0 c
  have hgain := lcaScaleGain_nonneg Nm v
  have hcarrier :=
    clusterJ01_branch_parent_sum_le N hN hv f₀ f₁ x₀ x₁
      W hW0 hW 0 (by norm_num)
      (fun h => (hsplit h).elim)
  calc
    (clusterJ01 N hN v f₀ f₁ x₀ x₁ : ℝ) ≤
        ∑ p : ClusterChild v → ClusterChild v,
          (∏ c : ClusterChild v, W c) *
            fullParentWeight root
              (fun c => 1 + w c)
              (fun c =>
                (step5LatticeConstant : ℝ) *
                  (scaleN Nm v : ℝ) ^ 4 * (1 + w c) ^ 4)
              p * lcaScaleGain Nm v := by
      simpa [pairParentVolumeWeight, hsplit, root, Nm, w]
        using hcarrier
    _ = ((∏ c : ClusterChild v, W c) *
        ∑ p : ClusterChild v → ClusterChild v,
          fullParentWeight root
            (fun c => 1 + w c)
            (fun c =>
              (step5LatticeConstant : ℝ) *
                (scaleN Nm v : ℝ) ^ 4 * (1 + w c) ^ 4)
            p) * lcaScaleGain Nm v := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ((∏ c : ClusterChild v, W c) *
          ((Fintype.card (ClusterChild v)).factorial *
            (step5VolumeConstant : ℝ) ^
              (Fintype.card (ClusterChild v) - 1) *
            (scaleN Nm v : ℝ) ^
              (4 * (Fintype.card (ClusterChild v) - 1)) *
            Real.exp (6 * ∑ c, w c))) *
          lcaScaleGain Nm v := by
      gcongr
    _ = (∏ c : ClusterChild v, W c) *
          (childCount t v.1).factorial *
          (step5VolumeConstant : ℝ) ^ (childCount t v.1 - 1) *
          (scaleN Nm v : ℝ) ^ (4 * (childCount t v.1 - 1)) *
          Real.exp (6 * ∑ c, w c) * lcaScaleGain Nm v := by
      rw [hcard]
      ring

/-- One-branch actual-carrier estimate before evaluating the sum over full
parent functions. -/
theorem clusterJ0_branch_parent_sum_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (f : ClusterLeafAt v) (x : LatticePoint)
    (W : ClusterChild v → ℝ) (hW0 : ∀ c, 0 ≤ W c)
    (hW :
      ∀ c (fc : ClusterLeafAt c.1) (y : LatticePoint),
        (clusterJ0 N hN c.1 fc y : ℝ) ≤ W c) :
    (clusterJ0 N hN v f x : ℝ) ≤
      (∏ c : ClusterChild v, W c) *
        ∑ p : ClusterChild v → ClusterChild v,
          fullParentWeight (anchorRootChild hv f)
            (fun c =>
              1 + tildeScale (N.toHeppMarking hN) c.1 /
                scaleN (N.toHeppMarking hN) v)
            (fun c =>
              (step5LatticeConstant : ℝ) *
                (scaleN (N.toHeppMarking hN) v : ℝ) ^ 4 *
                (1 + tildeScale (N.toHeppMarking hN) c.1 /
                  scaleN (N.toHeppMarking hN) v) ^ 4)
            p := by
  classical
  let A := anchoredClusterRestrictions N hN v f x
  let code := anchoredParentCode N hN hv f x
  have hmaps :
      Set.MapsTo code (A : Set (ClusterEmbeddingAt v))
        (Finset.univ :
          Finset (ClusterChild v → ClusterChild v)) := by
    intro zv hzv
    exact Finset.mem_univ _
  have hcard :
      A.card =
        ∑ p : ClusterChild v → ClusterChild v,
          (A.filter fun zv => code zv = p).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise hmaps)
  change (A.card : ℝ) ≤ _
  rw [hcard, Nat.cast_sum]
  calc
    ∑ p : ClusterChild v → ClusterChild v,
        ((A.filter fun zv => code zv = p).card : ℝ)
        ≤ ∑ p : ClusterChild v → ClusterChild v,
            (∏ c : ClusterChild v, W c) *
              fullParentWeight (anchorRootChild hv f)
                (fun c =>
                  1 + tildeScale (N.toHeppMarking hN) c.1 /
                    scaleN (N.toHeppMarking hN) v)
                (fun c =>
                  (step5LatticeConstant : ℝ) *
                    (scaleN (N.toHeppMarking hN) v : ℝ) ^ 4 *
                    (1 + tildeScale (N.toHeppMarking hN) c.1 /
                      scaleN (N.toHeppMarking hN) v) ^ 4)
                p := by
          apply Finset.sum_le_sum
          intro p hp
          exact card_anchoredParentFiber_le
            N hN hv f x W hW0 hW p
    _ = (∏ c : ClusterChild v, W c) *
        ∑ p : ClusterChild v → ClusterChild v,
          fullParentWeight (anchorRootChild hv f)
            (fun c =>
              1 + tildeScale (N.toHeppMarking hN) c.1 /
                scaleN (N.toHeppMarking hN) v)
            (fun c =>
              (step5LatticeConstant : ℝ) *
                (scaleN (N.toHeppMarking hN) v : ℝ) ^ 4 *
                (1 + tildeScale (N.toHeppMarking hN) c.1 /
                  scaleN (N.toHeppMarking hN) v) ^ 4)
            p := by
      rw [Finset.mul_sum]

/-- Evaluated one-branch recursion, the actual-carrier form of paper
(5.25). -/
theorem clusterJ0_branch_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ BranchNodes t)
    (f : ClusterLeafAt v) (x : LatticePoint)
    (W : ClusterChild v → ℝ) (hW0 : ∀ c, 0 ≤ W c)
    (hW :
      ∀ c (fc : ClusterLeafAt c.1) (y : LatticePoint),
        (clusterJ0 N hN c.1 fc y : ℝ) ≤ W c) :
    (clusterJ0 N hN v f x : ℝ) ≤
      (∏ c : ClusterChild v, W c) *
        (childCount t v.1).factorial *
        (step5VolumeConstant : ℝ) ^ (childCount t v.1 - 1) *
        (scaleN (N.toHeppMarking hN) v : ℝ) ^
          (4 * (childCount t v.1 - 1)) *
        Real.exp
          (6 * ∑ c : ClusterChild v,
            tildeScale (N.toHeppMarking hN) c.1 /
              scaleN (N.toHeppMarking hN) v) := by
  let Nm := N.toHeppMarking hN
  let w : ClusterChild v → ℝ :=
    fun c => tildeScale Nm c.1 / scaleN Nm v
  have hw : ∀ c, 0 ≤ w c := by
    intro c
    exact div_nonneg (tildeScale_nonneg Nm c.1)
      (by exact_mod_cast (Nat.zero_le (scaleN Nm v)))
  have hcard :
      Fintype.card (ClusterChild v) = childCount t v.1 := by
    rw [Fintype.card_coe, card_childrenOf]
  have hq : 2 ≤ Fintype.card (ClusterChild v) := by
    rw [hcard]
    exact mem_BranchNodes_iff.mp hv
  have hparent :=
    step5_parent_volume_bound
      (anchorRootChild hv f) w hw hq (scaleN Nm v : ℝ)
  have hprod :
      0 ≤ ∏ c : ClusterChild v, W c :=
    Finset.prod_nonneg fun c hc => hW0 c
  calc
    (clusterJ0 N hN v f x : ℝ) ≤
        (∏ c : ClusterChild v, W c) *
          ∑ p : ClusterChild v → ClusterChild v,
            fullParentWeight (anchorRootChild hv f)
              (fun c => 1 + w c)
              (fun c =>
                (step5LatticeConstant : ℝ) *
                  (scaleN Nm v : ℝ) ^ 4 * (1 + w c) ^ 4)
              p := by
        simpa [Nm, w] using
          clusterJ0_branch_parent_sum_le
            N hN hv f x W hW0 hW
    _ ≤ (∏ c : ClusterChild v, W c) *
          ((Fintype.card (ClusterChild v)).factorial *
            (step5VolumeConstant : ℝ) ^
              (Fintype.card (ClusterChild v) - 1) *
            (scaleN Nm v : ℝ) ^
              (4 * (Fintype.card (ClusterChild v) - 1)) *
            Real.exp (6 * ∑ c, w c)) :=
      mul_le_mul_of_nonneg_left hparent hprod
    _ = (∏ c : ClusterChild v, W c) *
          (childCount t v.1).factorial *
          (step5VolumeConstant : ℝ) ^ (childCount t v.1 - 1) *
          (scaleN Nm v : ℝ) ^ (4 * (childCount t v.1 - 1)) *
          Real.exp (6 * ∑ c, w c) := by
      rw [hcard]
      ring

/-! ## Iteration over branch descendants -/

/-- The local exponential cost paid at one branching vertex. -/
noncomputable def localRatioCost
    {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) : ℝ :=
  ∑ c : ClusterChild v,
    tildeScale Nm c.1 / scaleN Nm v

/-- Complete local factor contributed by one branch in (5.26). -/
noncomputable def branchVolumeFactor
    {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) : ℝ :=
  (childCount t v.1).factorial *
    (step5VolumeConstant : ℝ) ^ (childCount t v.1 - 1) *
    (scaleN Nm v : ℝ) ^ (4 * (childCount t v.1 - 1)) *
    Real.exp (6 * localRatioCost Nm v)

/-- Product of all local branch factors below `v`. -/
noncomputable def localIterationWeight
    {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) : ℝ :=
  ∏ u ∈ branchDescendants v, branchVolumeFactor Nm u

theorem localRatioCost_nonneg
    {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) :
    0 ≤ localRatioCost Nm v := by
  unfold localRatioCost
  apply Finset.sum_nonneg
  intro c hc
  exact div_nonneg (tildeScale_nonneg Nm c.1)
    (by exact_mod_cast (Nat.zero_le (scaleN Nm v)))

theorem one_le_branchVolumeFactor
    {t : PlaneTree} (Nm : HeppMarking t) {v : VPos t}
    (hv : v ∈ BranchNodes t) :
    1 ≤ branchVolumeFactor Nm v := by
  have hchild : 2 ≤ childCount t v.1 :=
    mem_BranchNodes_iff.mp hv
  have hfac : 1 ≤ ((childCount t v.1).factorial : ℝ) := by
    exact_mod_cast
      (Nat.one_le_of_lt (Nat.factorial_pos (childCount t v.1)))
  have hC : 1 ≤ (step5VolumeConstant : ℝ) := by
    norm_num [step5VolumeConstant, step5LatticeConstant]
  have hscale : 1 ≤ (scaleN Nm v : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (scaleN_pos Nm v)))
  have hexp : 1 ≤ Real.exp (6 * localRatioCost Nm v) := by
    exact Real.one_le_exp
      (mul_nonneg (by norm_num) (localRatioCost_nonneg Nm v))
  unfold branchVolumeFactor
  have hCp :
      1 ≤ (step5VolumeConstant : ℝ) ^ (childCount t v.1 - 1) :=
    one_le_pow₀ hC
  have hNp :
      1 ≤ (scaleN Nm v : ℝ) ^
        (4 * (childCount t v.1 - 1)) :=
    one_le_pow₀ hscale
  nlinarith [mul_le_mul hfac hCp (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : 0 ≤ ((childCount t v.1).factorial : ℝ)),
    mul_le_mul hNp hexp (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity :
        0 ≤ (scaleN Nm v : ℝ) ^
          (4 * (childCount t v.1 - 1)))]

/-- Branch-descendant sets below distinct immediate children are disjoint. -/
theorem branchDescendants_disjoint_of_children_ne
    {t : PlaneTree} {v c c' : VPos t}
    (hc : c ∈ childrenOf v) (hc' : c' ∈ childrenOf v)
    (hne : c ≠ c') :
    Disjoint (branchDescendants c) (branchDescendants c') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  have hcu := (mem_branchDescendants.mp hu).2
  have hcu' := (mem_branchDescendants.mp hu').2
  have hlen : c.1.length = c'.1.length := by
    rw [(mem_childrenOf.mp hc).1, (mem_childrenOf.mp hc').1]
  apply hne
  apply Subtype.ext
  rw [List.prefix_iff_eq_take] at hcu hcu'
  calc
    c.1 = u.1.take c.1.length := hcu
    _ = u.1.take c'.1.length := by rw [hlen]
    _ = c'.1 := hcu'.symm

/-- All child branch descendants are strict branch descendants of the
parent. -/
theorem biUnion_branchDescendants_subset_erase
    {t : PlaneTree} {v : VPos t} :
    (childrenOf v).biUnion branchDescendants ⊆
      (branchDescendants v).erase v := by
  intro u hu
  obtain ⟨c, hc, huc⟩ := Finset.mem_biUnion.mp hu
  rw [Finset.mem_erase]
  constructor
  · intro huv
    subst u
    have hle := (mem_branchDescendants.mp huc).2.length_le
    have hlen := (mem_childrenOf.mp hc).1
    omega
  · exact mem_branchDescendants.mpr
      ⟨(mem_branchDescendants.mp huc).1,
        (mem_childrenOf.mp hc).2.trans
          (mem_branchDescendants.mp huc).2⟩

/-- Products of descendant weights over the immediate children fit inside
the strict-descendant product of the parent. -/
theorem prod_localIterationWeight_children_le
    {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) :
    (∏ c : ClusterChild v, localIterationWeight Nm c.1) ≤
      ∏ u ∈ (branchDescendants v).erase v,
        branchVolumeFactor Nm u := by
  classical
  have hpair :
      (↑(childrenOf v) : Set (VPos t)).PairwiseDisjoint
        branchDescendants := by
    intro a ha b hb hne
    exact branchDescendants_disjoint_of_children_ne ha hb hne
  have hsubtype :
      (∏ c : ClusterChild v, localIterationWeight Nm c.1) =
        ∏ c ∈ childrenOf v, localIterationWeight Nm c := by
    symm
    exact Finset.prod_subtype (childrenOf v) (fun _ => Iff.rfl)
      (localIterationWeight Nm)
  rw [hsubtype]
  simp only [localIterationWeight]
  rw [← Finset.prod_biUnion hpair]
  apply Finset.prod_le_prod_of_subset_of_one_le
    biUnion_branchDescendants_subset_erase
  · intro u hu
    exact (by norm_num : (0 : ℝ) ≤ 1).trans
      (one_le_branchVolumeFactor Nm
        (mem_branchDescendants.mp
          (Finset.mem_erase.mp
            (biUnion_branchDescendants_subset_erase hu)).2).1)
  · intro u hu hnot
    exact one_le_branchVolumeFactor Nm
      (mem_branchDescendants.mp (Finset.mem_erase.mp hu).2).1

/-- Multiplying the current branch factor with all child subtree weights is
bounded by the full descendant product at the current vertex. -/
theorem branchVolumeFactor_mul_children_le_localIterationWeight
    {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (hv : v ∈ BranchNodes t) :
    branchVolumeFactor Nm v *
        (∏ c : ClusterChild v, localIterationWeight Nm c.1) ≤
      localIterationWeight Nm v := by
  have hchild :=
    prod_localIterationWeight_children_le Nm v
  have hfactor0 : 0 ≤ branchVolumeFactor Nm v :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (one_le_branchVolumeFactor Nm hv)
  have hvdesc : v ∈ branchDescendants v :=
    mem_branchDescendants.mpr ⟨hv, List.prefix_rfl⟩
  unfold localIterationWeight
  calc
    branchVolumeFactor Nm v *
        (∏ c : ClusterChild v, localIterationWeight Nm c.1)
        ≤ branchVolumeFactor Nm v *
          (∏ u ∈ (branchDescendants v).erase v,
            branchVolumeFactor Nm u) :=
      mul_le_mul_of_nonneg_left hchild hfactor0
    _ = (∏ u ∈ (branchDescendants v).erase v,
          branchVolumeFactor Nm u) * branchVolumeFactor Nm v := by ring
    _ = ∏ u ∈ branchDescendants v, branchVolumeFactor Nm u :=
      Finset.prod_erase_mul _ _ hvdesc

/-! ## Leaf base case and well-founded cluster iteration -/

private theorem ve_lt_childCount_of_isPos_append
    {t : PlaneTree} {p : Pos} {i : ℕ}
    (h : IsPos t (p ++ [i])) :
    i < childCount t p := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      have h' : IsPos (node cs) [i] := by simpa using h
      simpa [childCount] using isPos_cons_lt h'
  | cons a p ih =>
      obtain ⟨cs⟩ := t
      have h' : IsPos (node cs) (a :: (p ++ [i])) := by simpa using h
      obtain ⟨ha, hp⟩ := isPos_cons_iff.mp h'
      have hi := ih hp
      simpa [childCount, ha] using hi

/-- A strict valid descendant forces a positive child count at its
ancestor. -/
theorem childCount_pos_of_strict_prefix
    {t : PlaneTree} {v w : VPos t}
    (hpre : v.1 <+: w.1) (hne : v ≠ w) :
    0 < childCount t v.1 := by
  let q := w.1.drop v.1.length
  have hq : v.1 ++ q = w.1 :=
    List.prefix_iff_eq_append.mp hpre
  have hqne : q ≠ [] := by
    intro hnil
    apply hne
    apply Subtype.ext
    rw [hnil] at hq
    simpa using hq
  obtain ⟨i, q', hqform⟩ := List.exists_cons_of_ne_nil hqne
  rw [hqform] at hq
  have hpos : IsPos t (v.1 ++ [i]) := by
    apply IsPos_of_prefix w.2
    rw [← hq]
    simp
  exact Nat.zero_lt_of_lt (ve_lt_childCount_of_isPos_append hpos)

/-- A leaf vertex has no branching descendants. -/
theorem branchDescendants_eq_empty_of_leaf
    {t : PlaneTree} {v : VPos t} (hv : v ∈ Leaves t) :
    branchDescendants v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨huBranch, hvu⟩ := mem_branchDescendants.mp hu
  by_cases huv : v = u
  · subst u
    have hzero := mem_Leaves_iff.mp hv
    have htwo := mem_BranchNodes_iff.mp huBranch
    omega
  · have hpos := childCount_pos_of_strict_prefix hvu huv
    have hzero := mem_Leaves_iff.mp hv
    omega

/-- The cluster leaf carrier below a leaf vertex is a subsingleton. -/
theorem clusterLeafAt_eq_of_leaf
    {t : PlaneTree} {v : VPos t} (hv : v ∈ Leaves t)
    (a b : ClusterLeafAt v) :
    a = b := by
  apply Subtype.ext
  have ha : a.1.1 = v := by
    apply Subtype.ext
    have hpre := mem_leavesUnder.mp a.2
    by_cases hav : v = a.1.1
    · exact congrArg Subtype.val hav.symm
    · have hpos := childCount_pos_of_strict_prefix hpre hav
      have hzero := mem_Leaves_iff.mp hv
      omega
  have hb : b.1.1 = v := by
    apply Subtype.ext
    have hpre := mem_leavesUnder.mp b.2
    by_cases hbv : v = b.1.1
    · exact congrArg Subtype.val hbv.symm
    · have hpos := childCount_pos_of_strict_prefix hpre hbv
      have hzero := mem_Leaves_iff.mp hv
      omega
  exact Subtype.ext (ha.trans hb.symm)

/-- An anchored actual restriction at a leaf has at most one element. -/
theorem clusterJ0_le_one_of_leaf
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    {v : VPos t} (hv : v ∈ Leaves t)
    (f : ClusterLeafAt v) (x : LatticePoint) :
    clusterJ0 N hN v f x ≤ 1 := by
  unfold clusterJ0
  rw [Finset.card_le_one]
  intro zv hzv zv' hzv'
  funext l
  have hlf : l = f := clusterLeafAt_eq_of_leaf hv l f
  subst l
  exact (mem_anchoredClusterRestrictions.mp hzv).2.trans
    (mem_anchoredClusterRestrictions.mp hzv').2.symm

private theorem ve_valid_get {cs : List PlaneTree}
    (h : isValidList cs = true) (i : Fin cs.length) :
    (cs.get i).isValid = true := by
  rw [isValidList_eq_map] at h
  simp only [List.all_eq_true, id_eq] at h
  exact h _ (List.mem_map.mpr ⟨_, List.get_mem cs i, rfl⟩)

private theorem ve_childCount_ne_one
    {t : PlaneTree} {p : Pos}
    (ht : t.isValid = true) (hp : IsPos t p) :
    childCount t p ≠ 1 := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      simp only [isValid, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht
      simpa [childCount] using ht.1
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      simp only [isValid, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht
      have hchild := ve_valid_get ht.2 ⟨i, hi⟩
      have hne := ih hchild hp'
      simpa [childCount, hi] using hne

/-- Every vertex of a valid Hepp tree is either a leaf or a branch. -/
theorem leaf_or_branch_of_valid
    {t : PlaneTree} (ht : t.isValid = true) (v : VPos t) :
    v ∈ Leaves t ∨ v ∈ BranchNodes t := by
  have hne := ve_childCount_ne_one ht v.2
  rw [mem_Leaves_iff, mem_BranchNodes_iff]
  omega

/-- The local descendant product is nonnegative. -/
theorem localIterationWeight_nonneg
    {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) :
    0 ≤ localIterationWeight Nm v := by
  unfold localIterationWeight
  apply Finset.prod_nonneg
  intro u hu
  exact (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_branchVolumeFactor Nm
      (mem_branchDescendants.mp hu).1)

private theorem ve_isPos_length_lt_size
    {t : PlaneTree} {p : Pos} (hp : IsPos t p) :
    p.length < t.size := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      simp [PlaneTree.size]
  | cons a p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨ha, hp'⟩ := isPos_cons_iff.mp hp
      let i : Fin cs.length := ⟨a, ha⟩
      have hih₀ : p.length < cs[a].size := ih hp'
      have hih : p.length < (cs.get i).size := by
        simpa [i] using hih₀
      have hmem : (cs.get i).size ∈ cs.map PlaneTree.size :=
        List.mem_map.mpr ⟨cs.get i, List.get_mem cs i, rfl⟩
      have hle : (cs.get i).size ≤
          (cs.map PlaneTree.size).sum :=
        List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
      rw [PlaneTree.size, PlaneTree.sizeList_eq_map]
      simp only [List.length_cons]
      omega

/-- Actual-carrier iteration over every cluster below a valid tree. -/
theorem clusterJ0_le_localIterationWeight
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (f : ClusterLeafAt v) (x : LatticePoint) :
    (clusterJ0 N hN v f x : ℝ) ≤
      localIterationWeight (N.toHeppMarking hN) v := by
  let Nm := N.toHeppMarking hN
  have aux :
      ∀ k : ℕ, ∀ v : VPos t,
        t.size - v.1.length = k →
        ∀ (f : ClusterLeafAt v) (x : LatticePoint),
          (clusterJ0 N hN v f x : ℝ) ≤
            localIterationWeight Nm v := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro v hk f x
        rcases leaf_or_branch_of_valid ht v with hvLeaf | hvBranch
        · have hbase := clusterJ0_le_one_of_leaf N hN hvLeaf f x
          have hweight : localIterationWeight Nm v = 1 := by
            unfold localIterationWeight
            rw [branchDescendants_eq_empty_of_leaf hvLeaf]
            simp
          rw [hweight]
          exact_mod_cast hbase
        · let W : ClusterChild v → ℝ :=
            fun c => localIterationWeight Nm c.1
          have hW0 : ∀ c, 0 ≤ W c :=
            fun c => localIterationWeight_nonneg Nm c.1
          have hW :
              ∀ c (fc : ClusterLeafAt c.1) (y : LatticePoint),
                (clusterJ0 N hN c.1 fc y : ℝ) ≤ W c := by
            intro c fc y
            have hmeasure :
                t.size - c.1.1.length < k := by
              have hvsize := ve_isPos_length_lt_size v.2
              have hclen := (mem_childrenOf.mp c.2).1
              rw [← hk]
              omega
            exact ih (t.size - c.1.1.length) hmeasure
              c.1 rfl fc y
          have hbranch :=
            clusterJ0_branch_le N hN hvBranch f x W hW0 hW
          calc
            (clusterJ0 N hN v f x : ℝ) ≤
                (∏ c : ClusterChild v, W c) *
                  (childCount t v.1).factorial *
                  (step5VolumeConstant : ℝ) ^
                    (childCount t v.1 - 1) *
                  (scaleN Nm v : ℝ) ^
                    (4 * (childCount t v.1 - 1)) *
                  Real.exp
                    (6 * ∑ c : ClusterChild v,
                      tildeScale Nm c.1 / scaleN Nm v) := by
              simpa [Nm] using hbranch
            _ = (∏ c : ClusterChild v, W c) *
                branchVolumeFactor Nm v := by
              unfold branchVolumeFactor localRatioCost
              ring
            _ = branchVolumeFactor Nm v *
                (∏ c : ClusterChild v,
                  localIterationWeight Nm c.1) := by
              simp only [W]
              ring
            _ ≤ localIterationWeight Nm v :=
              branchVolumeFactor_mul_children_le_localIterationWeight
                Nm hvBranch
  exact aux (t.size - v.1.length) v rfl f x

/-! ## Well-founded two-anchor iteration -/

private theorem ve_child_path {t : PlaneTree} {v c : VPos t}
    (hc : c ∈ childrenOf v) :
    ∃ i : ℕ, c.1 = v.1 ++ [i] := by
  rw [mem_childrenOf] at hc
  let q := c.1.drop v.1.length
  have hq : v.1 ++ q = c.1 :=
    List.prefix_iff_eq_append.mp hc.2
  have hq_len : q.length = 1 := by
    dsimp [q]
    rw [List.length_drop]
    omega
  obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp hq_len
  refine ⟨i, ?_⟩
  rw [← hq, hi]

private theorem ve_leaf_path_below
    {t : PlaneTree} {v c : VPos t}
    (hc : c ∈ childrenOf v) {l : {w // w ∈ Leaves t}}
    (hl : l ∈ leavesUnder c) :
    ∃ i : ℕ, ∃ q : List ℕ,
      c.1 = v.1 ++ [i] ∧ l.1.1 = v.1 ++ i :: q := by
  obtain ⟨i, hcpath⟩ := ve_child_path hc
  rw [mem_leavesUnder] at hl
  have happ :
      c.1 ++ l.1.1.drop c.1.length = l.1.1 := by
    simpa using List.prefix_iff_eq_append.mp hl
  refine ⟨i, l.1.1.drop c.1.length, hcpath, ?_⟩
  calc
    l.1.1 = c.1 ++ l.1.1.drop c.1.length := happ.symm
    _ = (v.1 ++ [i]) ++ l.1.1.drop c.1.length := by rw [hcpath]
    _ = v.1 ++ i :: l.1.1.drop c.1.length := by
      simp only [List.append_assoc, List.singleton_append]

private theorem ve_lcaPath_append_cons_ne
    (p q r : List ℕ) {i j : ℕ} (hij : i ≠ j) :
    lcaPath (p ++ i :: q) (p ++ j :: r) = p := by
  induction p with
  | nil => simp [lcaPath, hij]
  | cons a p ih =>
      simp [lcaPath, ih]

/-- Leaves below distinct immediate children have the parent as their
lowest common ancestor. -/
theorem lcaV_eq_of_under_distinct_children
    {t : PlaneTree} {v c c' : VPos t}
    (hc : c ∈ childrenOf v) (hc' : c' ∈ childrenOf v)
    (hne : c ≠ c')
    {l l' : {w // w ∈ Leaves t}}
    (hl : l ∈ leavesUnder c) (hl' : l' ∈ leavesUnder c') :
    lcaV l.1 l'.1 = v := by
  obtain ⟨i, q, hcpath, hpath⟩ :=
    ve_leaf_path_below hc hl
  obtain ⟨j, r, hcpath', hpath'⟩ :=
    ve_leaf_path_below hc' hl'
  have hij : i ≠ j := by
    intro h
    subst j
    have hval : c.1 = c'.1 := hcpath.trans hcpath'.symm
    exact hne (Subtype.ext hval)
  apply Subtype.ext
  change lcaPath l.1.1 l'.1.1 = v.1
  rw [hpath, hpath', ve_lcaPath_append_cons_ne _ _ _ hij]

theorem lcaV_eq_of_anchorRootChild_ne
    {t : PlaneTree} {v : VPos t}
    (hv : v ∈ BranchNodes t) (f₀ f₁ : ClusterLeafAt v)
    (hne : anchorRootChild hv f₀ ≠ anchorRootChild hv f₁) :
    lcaV f₀.1 f₁.1 = v :=
  lcaV_eq_of_under_distinct_children
    (anchorRootChild hv f₀).2 (anchorRootChild hv f₁).2
    (fun hval => hne (Subtype.ext hval))
    (anchorRootChild_contains hv f₀)
    (anchorRootChild_contains hv f₁)

/-- Replacing one factor by itself times `gain` multiplies the whole finite
product by exactly `gain`. -/
theorem prod_replace_mul_eq_prod_mul
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : α → ℝ) (root : α) (gain : ℝ) :
    (∏ c : α, if c = root then W c * gain else W c) =
      (∏ c : α, W c) * gain := by
  calc
    (∏ c : α, if c = root then W c * gain else W c) =
        ∏ c : α, W c * (if c = root then gain else 1) := by
      apply Finset.prod_congr rfl
      intro c hc
      split_ifs <;> ring
    _ = (∏ c : α, W c) *
        ∏ c : α, (if c = root then gain else 1) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ c : α, W c) * gain := by
      rw [Fintype.prod_ite_eq']

/-- Actual-carrier Step 6 iteration.  The scale gain is created exactly at
the first branch where the two distinct leaves split and is preserved
through every ancestor above it. -/
theorem clusterJ01_le_localIterationWeight_mul_lcaScaleGain
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (f₀ f₁ : ClusterLeafAt v)
    (x₀ x₁ : LatticePoint) (hne : f₀ ≠ f₁) :
    (clusterJ01 N hN v f₀ f₁ x₀ x₁ : ℝ) ≤
      localIterationWeight (N.toHeppMarking hN) v *
        lcaScaleGain (N.toHeppMarking hN) (lcaV f₀.1 f₁.1) := by
  let Nm := N.toHeppMarking hN
  have aux :
      ∀ k : ℕ, ∀ v : VPos t,
        t.size - v.1.length = k →
        ∀ (f₀ f₁ : ClusterLeafAt v) (x₀ x₁ : LatticePoint),
          f₀ ≠ f₁ →
          (clusterJ01 N hN v f₀ f₁ x₀ x₁ : ℝ) ≤
            localIterationWeight Nm v *
              lcaScaleGain Nm (lcaV f₀.1 f₁.1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro v hk f₀ f₁ x₀ x₁ hfne
        rcases leaf_or_branch_of_valid ht v with hvLeaf | hvBranch
        · exact (hfne (clusterLeafAt_eq_of_leaf hvLeaf f₀ f₁)).elim
        · let W : ClusterChild v → ℝ :=
            fun c => localIterationWeight Nm c.1
          have hW0 : ∀ c, 0 ≤ W c :=
            fun c => localIterationWeight_nonneg Nm c.1
          have hW :
              ∀ c (fc : ClusterLeafAt c.1) (y : LatticePoint),
                (clusterJ0 N hN c.1 fc y : ℝ) ≤ W c := by
            intro c fc y
            exact clusterJ0_le_localIterationWeight ht N hN c.1 fc y
          let root₀ := anchorRootChild hvBranch f₀
          let root₁ := anchorRootChild hvBranch f₁
          by_cases hsame : root₀ = root₁
          · let f₀c : ClusterLeafAt root₀.1 :=
              anchorLeafInRootChild hvBranch f₀
            let f₁c : ClusterLeafAt root₀.1 :=
              hsame.symm ▸ anchorLeafInRootChild hvBranch f₁
            have hf₀c_val : f₀c.1 = f₀.1 := by
              rfl
            have hf₁c_val : f₁c.1 = f₁.1 := by
              exact cast_clusterLeafAt_val hsame
                (anchorLeafInRootChild hvBranch f₁)
            have hfneChild : f₀c ≠ f₁c := by
              intro heq
              have hval := congrArg
                (fun f : ClusterLeafAt root₀.1 => f.1) heq
              have hleaf : f₀.1 = f₁.1 := by
                rw [← hf₀c_val, ← hf₁c_val]
                exact hval
              exact hfne (Subtype.ext hleaf)
            let gain : ℝ :=
              lcaScaleGain Nm (lcaV f₀.1 f₁.1)
            let P : ℝ := localIterationWeight Nm root₀.1 * gain
            have hP0 : 0 ≤ P :=
              mul_nonneg (localIterationWeight_nonneg Nm root₀.1)
                (lcaScaleGain_nonneg Nm (lcaV f₀.1 f₁.1))
            have hmeasure :
                t.size - root₀.1.1.length < k := by
              have hvsize := ve_isPos_length_lt_size v.2
              have hclen := (mem_childrenOf.mp root₀.2).1
              rw [← hk]
              omega
            have hP :
                (clusterJ01 N hN root₀.1 f₀c f₁c x₀ x₁ : ℝ) ≤ P := by
              have hlca :
                  lcaV f₀c.1.1 f₁c.1.1 =
                    lcaV f₀.1.1 f₁.1.1 := by
                exact congrArg₂ lcaV
                  (congrArg Subtype.val hf₀c_val)
                  (congrArg Subtype.val hf₁c_val)
              simpa [P, gain, hlca] using
                (ih (t.size - root₀.1.1.length) hmeasure
                  root₀.1 rfl f₀c f₁c x₀ x₁ hfneChild)
            have hbranch :=
              clusterJ01_branch_le_same N hN hvBranch
                f₀ f₁ x₀ x₁ hsame W hW0 hW P hP0
                (by simpa [f₀c, f₁c, root₀, root₁] using hP)
            have hreplace :
                (∏ c : ClusterChild v,
                    if c = anchorRootChild hvBranch f₀
                    then P else W c) =
                  (∏ c : ClusterChild v, W c) * gain := by
              calc
                (∏ c : ClusterChild v,
                    if c = anchorRootChild hvBranch f₀
                    then P else W c) =
                    ∏ c : ClusterChild v,
                      if c = root₀ then W c * gain else W c := by
                  apply Finset.prod_congr rfl
                  intro c hc
                  by_cases hcr : c = root₀
                  · subst c
                    simp [root₀, P, W]
                  · simp [root₀, hcr]
                _ = (∏ c : ClusterChild v, W c) * gain :=
                  prod_replace_mul_eq_prod_mul W root₀ gain
            have hlocal :=
              branchVolumeFactor_mul_children_le_localIterationWeight
                Nm hvBranch
            have hgain0 : 0 ≤ gain :=
              lcaScaleGain_nonneg Nm (lcaV f₀.1 f₁.1)
            calc
              (clusterJ01 N hN v f₀ f₁ x₀ x₁ : ℝ) ≤
                  (∏ c : ClusterChild v,
                    if c = anchorRootChild hvBranch f₀
                    then P else W c) *
                    (childCount t v.1).factorial *
                    (step5VolumeConstant : ℝ) ^
                      (childCount t v.1 - 1) *
                    (scaleN Nm v : ℝ) ^
                      (4 * (childCount t v.1 - 1)) *
                    Real.exp
                      (6 * ∑ c : ClusterChild v,
                        tildeScale Nm c.1 / scaleN Nm v) := by
                simpa [Nm] using hbranch
              _ = (branchVolumeFactor Nm v *
                    (∏ c : ClusterChild v,
                      localIterationWeight Nm c.1)) * gain := by
                rw [hreplace]
                simp only [W]
                unfold branchVolumeFactor localRatioCost
                ring
              _ ≤ localIterationWeight Nm v * gain :=
                mul_le_mul_of_nonneg_right hlocal hgain0
          · have hbranch :=
              clusterJ01_branch_le_split N hN hvBranch
                f₀ f₁ x₀ x₁ hsame W hW0 hW
            have hlca :
                lcaV f₀.1 f₁.1 = v :=
              lcaV_eq_of_anchorRootChild_ne
                hvBranch f₀ f₁ hsame
            have hlocal :=
              branchVolumeFactor_mul_children_le_localIterationWeight
                Nm hvBranch
            have hgain0 :
                0 ≤ lcaScaleGain Nm v :=
              lcaScaleGain_nonneg Nm v
            calc
              (clusterJ01 N hN v f₀ f₁ x₀ x₁ : ℝ) ≤
                  (∏ c : ClusterChild v, W c) *
                    (childCount t v.1).factorial *
                    (step5VolumeConstant : ℝ) ^
                      (childCount t v.1 - 1) *
                    (scaleN Nm v : ℝ) ^
                      (4 * (childCount t v.1 - 1)) *
                    Real.exp
                      (6 * ∑ c : ClusterChild v,
                        tildeScale Nm c.1 / scaleN Nm v) *
                    lcaScaleGain Nm v := by
                simpa [Nm] using hbranch
              _ = (branchVolumeFactor Nm v *
                    (∏ c : ClusterChild v,
                      localIterationWeight Nm c.1)) *
                    lcaScaleGain Nm v := by
                simp only [W]
                unfold branchVolumeFactor localRatioCost
                ring
              _ ≤ localIterationWeight Nm v *
                    lcaScaleGain Nm v :=
                mul_le_mul_of_nonneg_right hlocal hgain0
              _ = localIterationWeight Nm v *
                    lcaScaleGain Nm (lcaV f₀.1 f₁.1) := by
                rw [hlca]
  exact aux (t.size - v.1.length) v rfl
    f₀ f₁ x₀ x₁ hne

/-! ## Reindexing the accumulated local ratio cost -/

/-- Sum of child accumulated scales is bounded by the strict branch
descendants of the parent. -/
theorem sum_tildeScale_children_le_strictDescendants
    {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) :
    ∑ c : ClusterChild v, tildeScale Nm c.1 ≤
      ∑ u ∈ (branchDescendants v).erase v,
        (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ) := by
  classical
  have hpair :
      (↑(childrenOf v) : Set (VPos t)).PairwiseDisjoint
        branchDescendants := by
    intro a ha b hb hne
    exact branchDescendants_disjoint_of_children_ne ha hb hne
  have hsubtype :
      (∑ c : ClusterChild v, tildeScale Nm c.1) =
        ∑ c ∈ childrenOf v, tildeScale Nm c := by
    symm
    exact Finset.sum_subtype (childrenOf v) (fun _ => Iff.rfl)
      (tildeScale Nm)
  rw [hsubtype]
  change
    ∑ c ∈ childrenOf v,
        ∑ u ∈ branchDescendants c,
          (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ) ≤ _
  rw [← Finset.sum_biUnion hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    biUnion_branchDescendants_subset_erase
    (fun _ _ _ => by positivity)

/-- The same strict-descendant ratio cost, indexed with the ancestor
vertex on the outside. -/
noncomputable def strictDescendantRatioCost
    {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) : ℝ :=
  ∑ u ∈ (BranchNodes t).filter
      (fun u => v ∈ strictBranchAncestors u),
    (childCount t u.1 : ℝ) *
      ((scaleN Nm u : ℝ) / scaleN Nm v)

theorem erase_branchDescendants_eq_filter_strictAncestors
    {t : PlaneTree} {v : VPos t} (hv : v ∈ BranchNodes t) :
    (branchDescendants v).erase v =
      (BranchNodes t).filter
        (fun u => v ∈ strictBranchAncestors u) := by
  ext u
  simp only [Finset.mem_erase, mem_branchDescendants,
    Finset.mem_filter, mem_strictBranchAncestors]
  tauto

/-- The Step-5 child ratio at one branch is bounded by the cost of all its
strict branching descendants. -/
theorem localRatioCost_le_strictDescendantRatioCost
    {t : PlaneTree} (Nm : HeppMarking t)
    {v : VPos t} (hv : v ∈ BranchNodes t) :
    localRatioCost Nm v ≤ strictDescendantRatioCost Nm v := by
  have hscale : (0 : ℝ) < scaleN Nm v := by
    exact_mod_cast scaleN_pos Nm v
  have hsum := sum_tildeScale_children_le_strictDescendants Nm v
  have hdiv :
      (∑ c : ClusterChild v, tildeScale Nm c.1) /
          scaleN Nm v ≤
        (∑ u ∈ (branchDescendants v).erase v,
          (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ)) /
            scaleN Nm v :=
    div_le_div_of_nonneg_right hsum hscale.le
  simp_rw [Finset.sum_div] at hdiv
  unfold localRatioCost strictDescendantRatioCost
  rw [← erase_branchDescendants_eq_filter_strictAncestors hv]
  calc
    ∑ c : ClusterChild v,
        tildeScale Nm c.1 / scaleN Nm v
        ≤ ∑ u ∈ (branchDescendants v).erase v,
            ((childCount t u.1 : ℝ) * (scaleN Nm u : ℝ)) /
              scaleN Nm v := hdiv
    _ = ∑ u ∈ (branchDescendants v).erase v,
          (childCount t u.1 : ℝ) *
            ((scaleN Nm u : ℝ) / scaleN Nm v) := by
      apply Finset.sum_congr rfl
      intro u hu
      ring

/-- Reversing the order of the strict ancestor/descendant sum gives exactly
the scalar cost used by `VolumeIteration`. -/
theorem sum_strictDescendantRatioCost_eq_ancestorRatioCost
    {t : PlaneTree} (Nm : HeppMarking t) :
    (∑ v ∈ BranchNodes t, strictDescendantRatioCost Nm v) =
      ancestorRatioCost Nm := by
  unfold strictDescendantRatioCost ancestorRatioCost
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  have hfilter :
      (BranchNodes t).filter
          (fun v => v ∈ strictBranchAncestors u) =
        strictBranchAncestors u := by
    ext v
    simp only [Finset.mem_filter, mem_strictBranchAncestors]
    tauto
  rw [← Finset.sum_filter, hfilter]

/-- The total local Step-5 exponential cost is at most
`ancestorRatioCost`. -/
theorem sum_localRatioCost_le_ancestorRatioCost
    {t : PlaneTree} (Nm : HeppMarking t) :
    (∑ v ∈ BranchNodes t, localRatioCost Nm v) ≤
      ancestorRatioCost Nm := by
  calc
    (∑ v ∈ BranchNodes t, localRatioCost Nm v)
        ≤ ∑ v ∈ BranchNodes t,
            strictDescendantRatioCost Nm v := by
      apply Finset.sum_le_sum
      intro v hv
      exact localRatioCost_le_strictDescendantRatioCost Nm hv
    _ = ancestorRatioCost Nm :=
      sum_strictDescendantRatioCost_eq_ancestorRatioCost Nm

/-! ## Closing the one-anchor iteration -/

/-- Every branch is a branch descendant of the root. -/
@[simp] theorem branchDescendants_root_eq (t : PlaneTree) :
    branchDescendants (rootV t) = BranchNodes t := by
  ext v
  simp [mem_branchDescendants, rootV]

/-- The actual descendant product at the root is bounded by the exact
`hiterate` expression consumed by `volume_iteration_bound`. -/
theorem localIterationWeight_root_le_hiterate
    {t : PlaneTree} (ht : t.isValid = true)
    (Nm : HeppMarking t) :
    localIterationWeight Nm (rootV t) ≤
      (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        (∏ v ∈ BranchNodes t,
          ((childCount t v.1).factorial : ℝ)) *
        branchScaleProduct Nm *
        Real.exp (6 * ancestorRatioCost Nm) := by
  classical
  let B := BranchNodes t
  have hconstant :
      (∏ v ∈ B,
          (step5VolumeConstant : ℝ) ^
            (childCount t v.1 - 1)) =
        (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) := by
    rw [Finset.prod_pow_eq_pow_sum,
      show (∑ v ∈ B, (childCount t v.1 - 1)) =
          branchExcess t by
        simpa [B] using
          sum_branchNodes_childCount_sub_one_eq_branchExcess t,
      branchExcess_eq_leafCount_sub_one t ht]
  have hexponential :
      (∏ v ∈ B, Real.exp (6 * localRatioCost Nm v)) =
        Real.exp (6 * ∑ v ∈ B, localRatioCost Nm v) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
  have hexponential_le :
      Real.exp (6 * ∑ v ∈ B, localRatioCost Nm v) ≤
        Real.exp (6 * ancestorRatioCost Nm) := by
    apply Real.exp_le_exp.mpr
    have hcost := sum_localRatioCost_le_ancestorRatioCost Nm
    simpa [B] using mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 6)
  have hfactor :
      localIterationWeight Nm (rootV t) =
        (∏ v ∈ B, ((childCount t v.1).factorial : ℝ)) *
        (∏ v ∈ B,
          (step5VolumeConstant : ℝ) ^
            (childCount t v.1 - 1)) *
        branchScaleProduct Nm *
        (∏ v ∈ B, Real.exp (6 * localRatioCost Nm v)) := by
    simp only [localIterationWeight, branchDescendants_root_eq,
      branchVolumeFactor, branchScaleProduct, B,
      Finset.prod_mul_distrib]
  rw [hfactor, hconstant, hexponential]
  have hnonneg :
      0 ≤
        (∏ v ∈ B, ((childCount t v.1).factorial : ℝ)) *
        (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        branchScaleProduct Nm := by
    apply mul_nonneg
    · positivity
    · exact branchScaleProduct_nonneg Nm
  calc
    (∏ v ∈ B, ((childCount t v.1).factorial : ℝ)) *
          (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          branchScaleProduct Nm *
          Real.exp (6 * ∑ v ∈ B, localRatioCost Nm v)
        ≤ (∏ v ∈ B, ((childCount t v.1).factorial : ℝ)) *
          (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          branchScaleProduct Nm *
          Real.exp (6 * ancestorRatioCost Nm) :=
      mul_le_mul_of_nonneg_left hexponential_le hnonneg
    _ = (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          (∏ v ∈ BranchNodes t,
            ((childCount t v.1).factorial : ℝ)) *
          branchScaleProduct Nm *
          Real.exp (6 * ancestorRatioCost Nm) := by
      simp only [B]
      ring

/-- A fixed anchored leaf satisfies the fully iterated Step-5 bound. -/
theorem J0_le_iterated_volume
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f : {v // v ∈ Leaves t}) (x : LatticePoint) :
    (J0 N hN f x : ℝ) ≤
      (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        (256 : ℝ) ^ t.leafCount *
        Real.exp (12 * (t.leafCount : ℝ)) *
        (t.autCard : ℝ) *
        branchScaleProduct (N.toHeppMarking hN) := by
  let Nm := N.toHeppMarking hN
  rw [← clusterJ0_root_eq_J0 N hN f x]
  apply volume_iteration_bound ht Nm
  exact (clusterJ0_le_localIterationWeight
      ht N hN (rootV t) (rootClusterLeaf f) x).trans
    (localIterationWeight_root_le_hiterate ht Nm)

/-- The embedding of a full-tree leaf into the root cluster is injective. -/
theorem rootClusterLeaf_injective {t : PlaneTree} :
    Function.Injective (rootClusterLeaf (t := t)) := by
  intro f g h
  exact congrArg Subtype.val h

/-- A fixed ordered pair of distinct anchored leaves satisfies the fully
iterated Step-6 bound with its exact LCA scale gain. -/
theorem J01_le_iterated_volume_with_gain
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f₀ f₁ : {v // v ∈ Leaves t}) (hne : f₀ ≠ f₁)
    (x₀ x₁ : LatticePoint) :
    (J01 N hN f₀ f₁ x₀ x₁ : ℝ) ≤
      (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        (256 : ℝ) ^ t.leafCount *
        Real.exp (12 * (t.leafCount : ℝ)) *
        (t.autCard : ℝ) *
        branchScaleProduct (N.toHeppMarking hN) *
        lcaScaleGain (N.toHeppMarking hN) (lcaV f₀.1 f₁.1) := by
  let Nm := N.toHeppMarking hN
  let a := lcaV f₀.1 f₁.1
  rw [← clusterJ01_root_eq_J01 N hN f₀ f₁ x₀ x₁]
  apply volume_iteration_pair_bound ht Nm a
  have hcluster :=
    clusterJ01_le_localIterationWeight_mul_lcaScaleGain
      ht N hN (rootV t) (rootClusterLeaf f₀)
        (rootClusterLeaf f₁) x₀ x₁
        (fun h => hne (rootClusterLeaf_injective h))
  have hroot := localIterationWeight_root_le_hiterate ht Nm
  have hgain0 := lcaScaleGain_nonneg Nm a
  calc
    (clusterJ01 N hN (rootV t)
        (rootClusterLeaf f₀) (rootClusterLeaf f₁) x₀ x₁ : ℝ)
        ≤ localIterationWeight Nm (rootV t) *
            lcaScaleGain Nm a := by
          simpa [Nm, a, rootClusterLeaf] using hcluster
    _ ≤ ((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          (∏ v ∈ BranchNodes t,
            ((childCount t v.1).factorial : ℝ)) *
          branchScaleProduct Nm *
          Real.exp (6 * ancestorRatioCost Nm)) *
          lcaScaleGain Nm a :=
      mul_le_mul_of_nonneg_right hroot hgain0
    _ = (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          (∏ v ∈ BranchNodes t,
            ((childCount t v.1).factorial : ℝ)) *
          branchScaleProduct Nm *
          Real.exp (6 * ancestorRatioCost Nm) *
          lcaScaleGain Nm a := by ring

/-- The lattice bracket appearing in paper (5.14), written with the same
sup norm used by admissibility. -/
noncomputable def latticeBracketInvFourth
    (x₀ x₁ : LatticePoint) : ℝ :=
  ((1 + znorm (x₀ - x₁) ^ 2) ^ 2)⁻¹

theorem latticeBracketInvFourth_nonneg
    (x₀ x₁ : LatticePoint) :
    0 ≤ latticeBracketInvFourth x₀ x₁ := by
  unfold latticeBracketInvFourth
  positivity

/-- Convert the LCA scale gain into the spatial bracket.  The only
geometric input is the Step-4 cluster-diameter estimate at the LCA. -/
theorem lcaScaleGain_le_leafCountFactor_mul_bracket
    {t : PlaneTree} (ht : t.isValid = true)
    (Nm : HeppMarking t) (a : VPos t)
    (x₀ x₁ : LatticePoint)
    (hdist :
      znorm (x₀ - x₁) ≤ tildeScale Nm a) :
    lcaScaleGain Nm a ≤
      (1 + 2 * (t.leafCount : ℝ)) ^ 4 *
        latticeBracketInvFourth x₀ x₁ := by
  let r : ℝ := t.leafCount
  let Nv : ℝ := scaleN Nm a
  let d : ℝ := znorm (x₀ - x₁)
  have hr : 0 ≤ r := by
    dsimp [r]
    positivity
  have hNv : 1 ≤ Nv := by
    dsimp [Nv]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (scaleN_pos Nm a)))
  have hNv0 : 0 < Nv := (by norm_num : (0 : ℝ) < 1).trans_le hNv
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact norm_nonneg _
  have hd :
      d ≤ 2 * r * Nv := by
    calc
      d ≤ tildeScale Nm a := by simpa [d] using hdist
      _ ≤ 2 * (t.leafCount : ℝ) * (scaleN Nm a : ℝ) :=
        tildeScale_le_two_mul_leafCount_mul_scaleN ht Nm a
      _ = 2 * r * Nv := rfl
  have hupper0 : 0 ≤ 2 * r * Nv := by positivity
  have hsq :
      d ^ 2 ≤ (2 * r * Nv) ^ 2 := by
    have hprod :=
      mul_nonneg (sub_nonneg.mpr hd) (add_nonneg hupper0 hd0)
    nlinarith
  have hNvSq : 1 ≤ Nv ^ 2 := by nlinarith [sq_nonneg (Nv - 1)]
  have hbase :
      1 + d ^ 2 ≤ (1 + 2 * r) ^ 2 * Nv ^ 2 := by
    calc
      1 + d ^ 2 ≤ Nv ^ 2 + (2 * r * Nv) ^ 2 := by
        gcongr
      _ = (1 + (2 * r) ^ 2) * Nv ^ 2 := by ring
      _ ≤ (1 + 2 * r) ^ 2 * Nv ^ 2 := by
        gcongr
        nlinarith
  have hden :
      (1 + d ^ 2) ^ 2 ≤
        (1 + 2 * r) ^ 4 * Nv ^ 4 := by
    calc
      (1 + d ^ 2) ^ 2 ≤
          ((1 + 2 * r) ^ 2 * Nv ^ 2) ^ 2 := by
        gcongr
      _ = (1 + 2 * r) ^ 4 * Nv ^ 4 := by ring
  have hdenPos : 0 < (1 + d ^ 2) ^ 2 := by positivity
  have hNv4Pos : 0 < Nv ^ 4 := by positivity
  unfold lcaScaleGain latticeBracketInvFourth
  change (Nv ^ 4)⁻¹ ≤
    (1 + 2 * r) ^ 4 * ((1 + d ^ 2) ^ 2)⁻¹
  change (Nv ^ 4)⁻¹ ≤
    (1 + 2 * r) ^ 4 / ((1 + d ^ 2) ^ 2)
  apply (le_div_iff₀ hdenPos).2
  rw [mul_comm]
  change (1 + d ^ 2) ^ 2 / Nv ^ 4 ≤
    (1 + 2 * r) ^ 4
  exact (div_le_iff₀ hNv4Pos).2 hden

/-- Fixed-leaf form of (5.14), after converting the LCA gain to the
spatial bracket. -/
theorem J01_le_iterated_volume_bracket
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f₀ f₁ : {v // v ∈ Leaves t}) (hne : f₀ ≠ f₁)
    (x₀ x₁ : LatticePoint) :
    (J01 N hN f₀ f₁ x₀ x₁ : ℝ) ≤
      ((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        (256 : ℝ) ^ t.leafCount *
        Real.exp (12 * (t.leafCount : ℝ)) *
        (t.autCard : ℝ) *
        branchScaleProduct (N.toHeppMarking hN)) *
      (1 + 2 * (t.leafCount : ℝ)) ^ 4 *
      latticeBracketInvFourth x₀ x₁ := by
  let Nm := N.toHeppMarking hN
  let a := lcaV f₀.1 f₁.1
  let B : ℝ :=
    (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
      (256 : ℝ) ^ t.leafCount *
      Real.exp (12 * (t.leafCount : ℝ)) *
      (t.autCard : ℝ) * branchScaleProduct Nm
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (by positivity))
          (by positivity))
        (by positivity))
      (branchScaleProduct_nonneg Nm)
  by_cases hzero : J01 N hN f₀ f₁ x₀ x₁ = 0
  · simp only [hzero, Nat.cast_zero]
    exact mul_nonneg
      (mul_nonneg hB0 (by positivity))
      (latticeBracketInvFourth_nonneg x₀ x₁)
  · have hpos : 0 < J01 N hN f₀ f₁ x₀ x₁ :=
      Nat.pos_of_ne_zero hzero
    have hcarrier :
        (doublyAnchoredLeafEmbeddings N hN f₀ f₁ x₀ x₁).Nonempty := by
      rw [← Finset.card_pos]
      simpa [J01] using hpos
    obtain ⟨z, hz⟩ := hcarrier
    obtain ⟨hzAdm, hz₀, hz₁⟩ :=
      mem_doublyAnchoredLeafEmbeddings.mp hz
    have hadm : IsAdmissible Nm M z := by
      simpa [Nm] using mem_admissibleLeafEmbeddings.mp hzAdm
    have hdist :
        znorm (x₀ - x₁) ≤ tildeScale Nm a := by
      have hdiam :=
        clusterDiameter_le_tildeScale hadm a
          (mem_leavesUnder.mpr
            (lcaPath_prefix_left f₀.1.1 f₁.1.1))
          (mem_leavesUnder.mpr
            (lcaPath_prefix_right f₀.1.1 f₁.1.1))
      simpa [a, hz₀, hz₁] using hdiam
    have hgain :=
      lcaScaleGain_le_leafCountFactor_mul_bracket
        ht Nm a x₀ x₁ hdist
    calc
      (J01 N hN f₀ f₁ x₀ x₁ : ℝ) ≤
          B * lcaScaleGain Nm a := by
        simpa [B, Nm, a] using
          J01_le_iterated_volume_with_gain
            ht N hN f₀ f₁ hne x₀ x₁
      _ ≤ B * ((1 + 2 * (t.leafCount : ℝ)) ^ 4 *
          latticeBracketInvFourth x₀ x₁) :=
        mul_le_mul_of_nonneg_left hgain hB0
      _ = B * (1 + 2 * (t.leafCount : ℝ)) ^ 4 *
          latticeBracketInvFourth x₀ x₁ := by ring

/-- Division-free one-point volume bound before absorbing the harmless
choice of anchored leaf into the universal exponential constant. -/
theorem volume_estimate_one_anchor_raw
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (x : LatticePoint) :
    ((Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContaining N hN x).card : ℕ) : ℝ) ≤
      (t.leafCount : ℝ) *
        ((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          (256 : ℝ) ^ t.leafCount *
          Real.exp (12 * (t.leafCount : ℝ)) *
          (t.autCard : ℝ) *
          branchScaleProduct (N.toHeppMarking hN)) := by
  let R : ℝ :=
    (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
      (256 : ℝ) ^ t.leafCount *
      Real.exp (12 * (t.leafCount : ℝ)) *
      (t.autCard : ℝ) *
      branchScaleProduct (N.toHeppMarking hN)
  have hreduceNat :=
    card_autHeppMarked_mul_card_realizedSetsContaining_le_sum_J0
      N hN x
  have hreduce :
      ((Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
          (realizedSetsContaining N hN x).card : ℕ) : ℝ) ≤
        ∑ f : {v // v ∈ Leaves t}, (J0 N hN f x : ℝ) := by
    exact_mod_cast hreduceNat
  calc
    ((Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
          (realizedSetsContaining N hN x).card : ℕ) : ℝ)
        ≤ ∑ f : {v // v ∈ Leaves t},
            (J0 N hN f x : ℝ) := hreduce
    _ ≤ ∑ _f : {v // v ∈ Leaves t}, R := by
      apply Finset.sum_le_sum
      intro f hf
      simpa [R] using J0_le_iterated_volume ht N hN f x
    _ = (t.leafCount : ℝ) * R := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_univ]
      rw [Fintype.card_coe, card_Leaves_eq_leafCount]
    _ = (t.leafCount : ℝ) *
        ((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          (256 : ℝ) ^ t.leafCount *
          Real.exp (12 * (t.leafCount : ℝ)) *
          (t.autCard : ℝ) *
          branchScaleProduct (N.toHeppMarking hN)) := rfl

/-- Division-free two-point estimate before absorbing the ordered leaf-pair
choice and the polynomial LCA-to-distance loss into a universal exponential
constant. -/
theorem volume_estimate_two_anchor_raw
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (x₀ x₁ : LatticePoint) (hne : x₀ ≠ x₁) :
    ((Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContainingPair N hN x₀ x₁).card : ℕ) : ℝ) ≤
      (t.leafCount : ℝ) ^ 2 *
        (((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          (256 : ℝ) ^ t.leafCount *
          Real.exp (12 * (t.leafCount : ℝ)) *
          (t.autCard : ℝ) *
          branchScaleProduct (N.toHeppMarking hN)) *
        (1 + 2 * (t.leafCount : ℝ)) ^ 4 *
        latticeBracketInvFourth x₀ x₁) := by
  let R : ℝ :=
    ((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
      (256 : ℝ) ^ t.leafCount *
      Real.exp (12 * (t.leafCount : ℝ)) *
      (t.autCard : ℝ) *
      branchScaleProduct (N.toHeppMarking hN)) *
      (1 + 2 * (t.leafCount : ℝ)) ^ 4 *
      latticeBracketInvFourth x₀ x₁
  have hreduceNat :=
    card_autHeppMarked_mul_card_realizedSetsContainingPair_le_sum_J01_distinct
      N hN x₀ x₁ hne
  have hreduce :
      ((Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
          (realizedSetsContainingPair N hN x₀ x₁).card : ℕ) : ℝ) ≤
        ∑ f ∈ distinctLeafPairs t,
          (J01 N hN f.1 f.2 x₀ x₁ : ℝ) := by
    exact_mod_cast hreduceNat
  have hcardNat :
      (distinctLeafPairs t).card ≤ t.leafCount ^ 2 := by
    calc
      (distinctLeafPairs t).card ≤
          (Finset.univ :
            Finset ({v // v ∈ Leaves t} ×
              {v // v ∈ Leaves t})).card := by
        exact Finset.card_le_card (by
          intro f hf
          exact Finset.mem_univ f)
      _ = Fintype.card ({v // v ∈ Leaves t} ×
            {v // v ∈ Leaves t}) := Finset.card_univ
      _ = t.leafCount ^ 2 := by
        rw [Fintype.card_prod, Fintype.card_coe,
          card_Leaves_eq_leafCount]
        ring
  have hR0 : 0 ≤ R := by
    dsimp [R]
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by positivity) (by positivity))
              (by positivity))
            (by positivity))
          (branchScaleProduct_nonneg (N.toHeppMarking hN))
      · positivity
    · exact latticeBracketInvFourth_nonneg x₀ x₁
  calc
    ((Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
          (realizedSetsContainingPair N hN x₀ x₁).card : ℕ) : ℝ)
        ≤ ∑ f ∈ distinctLeafPairs t,
            (J01 N hN f.1 f.2 x₀ x₁ : ℝ) := hreduce
    _ ≤ ∑ _f ∈ distinctLeafPairs t, R := by
      apply Finset.sum_le_sum
      intro f hf
      exact J01_le_iterated_volume_bracket
        ht N hN f.1 f.2 (mem_distinctLeafPairs.mp hf) x₀ x₁
    _ = ((distinctLeafPairs t).card : ℝ) * R := by simp
    _ ≤ (t.leafCount : ℝ) ^ 2 * R := by
      apply mul_le_mul_of_nonneg_right _ hR0
      exact_mod_cast hcardNat
    _ = (t.leafCount : ℝ) ^ 2 *
        (((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          (256 : ℝ) ^ t.leafCount *
          Real.exp (12 * (t.leafCount : ℝ)) *
          (t.autCard : ℝ) *
          branchScaleProduct (N.toHeppMarking hN)) *
        (1 + 2 * (t.leafCount : ℝ)) ^ 4 *
        latticeBracketInvFourth x₀ x₁) := rfl

/-- A single explicit universal constant for both exponential losses in
the one-anchor estimate. -/
noncomputable def volumeEstimateConstant : ℝ :=
  2 * (step5VolumeConstant : ℝ) * 256 * Real.exp 12

private theorem ve_nat_le_two_pow (n : ℕ) :
    n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      calc
        n + 1 ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by
          rw [pow_succ]
          omega

/-- Elementary absorption of the anchored-leaf choice and all Step-5
scalar constants into `volumeEstimateConstant ^ r`. -/
theorem leafCount_mul_iterationScalar_le
    (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) *
        ((step5VolumeConstant : ℝ) ^ (r - 1) *
          (256 : ℝ) ^ r * Real.exp (12 * (r : ℝ))) ≤
      volumeEstimateConstant ^ r := by
  let C : ℝ := step5VolumeConstant
  have hC : 1 ≤ C := by
    dsimp [C]
    norm_num [step5VolumeConstant, step5LatticeConstant]
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  have hCpow0 : 0 ≤ C ^ (r - 1) := pow_nonneg hC0 _
  have hCpred :
      C ^ (r - 1) ≤ C ^ r := by
    calc
      C ^ (r - 1) = C ^ (r - 1) * 1 := by ring
      _ ≤ C ^ (r - 1) * C :=
        mul_le_mul_of_nonneg_left hC hCpow0
      _ = C ^ r := by
        rw [← pow_succ, Nat.sub_add_cancel hr]
  have hrpow : (r : ℝ) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast ve_nat_le_two_pow r
  have hexponential :
      Real.exp (12 * (r : ℝ)) = (Real.exp 12) ^ r := by
    rw [show 12 * (r : ℝ) = (r : ℝ) * 12 by ring,
      Real.exp_nat_mul]
  rw [hexponential]
  calc
    (r : ℝ) *
          ((step5VolumeConstant : ℝ) ^ (r - 1) *
            (256 : ℝ) ^ r * (Real.exp 12) ^ r)
        = (r : ℝ) * C ^ (r - 1) *
            (256 : ℝ) ^ r * (Real.exp 12) ^ r := by
          simp only [C]
          ring
    _ ≤ (2 : ℝ) ^ r * C ^ r *
          (256 : ℝ) ^ r * (Real.exp 12) ^ r := by
      gcongr
    _ = volumeEstimateConstant ^ r := by
      simp only [volumeEstimateConstant, mul_pow]
      ring

/-- A common universal constant large enough for both (5.13) and (5.14). -/
noncomputable def volumeEstimateFinalConstant : ℝ :=
  5184 * (step5VolumeConstant : ℝ) * 256 * Real.exp 12

/-- Absorb the ordered leaf-pair count and the polynomial
`(1 + 2r)^4` loss into a universal exponential constant. -/
theorem leafCountSq_mul_pairIterationScalar_le
    (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) ^ 2 *
        ((step5VolumeConstant : ℝ) ^ (r - 1) *
          (256 : ℝ) ^ r * Real.exp (12 * (r : ℝ)) *
          (1 + 2 * (r : ℝ)) ^ 4) ≤
      volumeEstimateFinalConstant ^ r := by
  let rr : ℝ := r
  let C : ℝ := step5VolumeConstant
  have hrr : 1 ≤ rr := by
    dsimp [rr]
    exact_mod_cast hr
  have hrr0 : 0 ≤ rr := (by norm_num : (0 : ℝ) ≤ 1).trans hrr
  have hC : 1 ≤ C := by
    dsimp [C]
    norm_num [step5VolumeConstant, step5LatticeConstant]
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  have hCpred :
      C ^ (r - 1) ≤ C ^ r := by
    have hpow0 : 0 ≤ C ^ (r - 1) := pow_nonneg hC0 _
    calc
      C ^ (r - 1) = C ^ (r - 1) * 1 := by ring
      _ ≤ C ^ (r - 1) * C :=
        mul_le_mul_of_nonneg_left hC hpow0
      _ = C ^ r := by
        rw [← pow_succ, Nat.sub_add_cancel hr]
  have hrpow : rr ≤ (2 : ℝ) ^ r := by
    dsimp [rr]
    exact_mod_cast ve_nat_le_two_pow r
  have hpoly :
      rr ^ 2 * (1 + 2 * rr) ^ 4 ≤
        (5184 : ℝ) ^ r := by
    have hlinear : 1 + 2 * rr ≤ 3 * rr := by
      linarith
    have hpow6 :
        rr ^ 6 ≤ ((2 : ℝ) ^ r) ^ 6 := by
      gcongr
    have h81 :
        (81 : ℝ) ≤ (81 : ℝ) ^ r := by
      calc
        (81 : ℝ) = (81 : ℝ) ^ 1 := by norm_num
        _ ≤ (81 : ℝ) ^ r :=
          pow_le_pow_right₀ (by norm_num) hr
    calc
      rr ^ 2 * (1 + 2 * rr) ^ 4
          ≤ rr ^ 2 * (3 * rr) ^ 4 := by
        gcongr
      _ = 81 * rr ^ 6 := by ring
      _ ≤ 81 * ((2 : ℝ) ^ r) ^ 6 := by
        gcongr
      _ = 81 * (64 : ℝ) ^ r := by
        rw [← pow_mul, Nat.mul_comm r 6, pow_mul]
        norm_num
      _ ≤ (81 : ℝ) ^ r * (64 : ℝ) ^ r := by
        gcongr
      _ = (5184 : ℝ) ^ r := by
        rw [← mul_pow]
        norm_num
  have hexponential :
      Real.exp (12 * (r : ℝ)) = (Real.exp 12) ^ r := by
    rw [show 12 * (r : ℝ) = (r : ℝ) * 12 by ring,
      Real.exp_nat_mul]
  rw [hexponential]
  calc
    (r : ℝ) ^ 2 *
          ((step5VolumeConstant : ℝ) ^ (r - 1) *
            (256 : ℝ) ^ r * (Real.exp 12) ^ r *
            (1 + 2 * (r : ℝ)) ^ 4)
        = (rr ^ 2 * (1 + 2 * rr) ^ 4) *
            C ^ (r - 1) * (256 : ℝ) ^ r *
            (Real.exp 12) ^ r := by
          simp only [rr, C]
          ring
    _ ≤ (5184 : ℝ) ^ r * C ^ r *
          (256 : ℝ) ^ r * (Real.exp 12) ^ r := by
      gcongr
    _ = volumeEstimateFinalConstant ^ r := by
      simp only [volumeEstimateFinalConstant, mul_pow]
      ring

/-- **Paper (5.13), division-free form.**  Multiplying by the marked-tree
automorphism cardinality avoids field division while retaining exactly the
paper's automorphism ratio. -/
theorem volume_estimate_one_anchor
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (x : LatticePoint) :
    ((Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContaining N hN x).card : ℕ) : ℝ) ≤
      volumeEstimateConstant ^ t.leafCount *
        (t.autCard : ℝ) *
        branchScaleProduct (N.toHeppMarking hN) := by
  let Nm := N.toHeppMarking hN
  have hraw := volume_estimate_one_anchor_raw ht N hN x
  have hscalar :=
    leafCount_mul_iterationScalar_le t.leafCount
      (one_le_leafCount t)
  have htail :
      0 ≤ (t.autCard : ℝ) * branchScaleProduct Nm :=
    mul_nonneg (by positivity) (branchScaleProduct_nonneg Nm)
  calc
    ((Fintype.card (AutHeppMarked t Nm) *
          (realizedSetsContaining N hN x).card : ℕ) : ℝ)
        ≤ (t.leafCount : ℝ) *
          ((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
            (256 : ℝ) ^ t.leafCount *
            Real.exp (12 * (t.leafCount : ℝ)) *
            (t.autCard : ℝ) * branchScaleProduct Nm) := by
          simpa [Nm] using hraw
    _ = ((t.leafCount : ℝ) *
          ((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
            (256 : ℝ) ^ t.leafCount *
            Real.exp (12 * (t.leafCount : ℝ)))) *
          ((t.autCard : ℝ) * branchScaleProduct Nm) := by ring
    _ ≤ volumeEstimateConstant ^ t.leafCount *
          ((t.autCard : ℝ) * branchScaleProduct Nm) :=
      mul_le_mul_of_nonneg_right hscalar htail
    _ = volumeEstimateConstant ^ t.leafCount *
          (t.autCard : ℝ) * branchScaleProduct Nm := by ring

/-- The one-anchor estimate with the common constant used by the complete
Proposition 5.6 interface. -/
theorem volume_estimate_one_anchor_final
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (x : LatticePoint) :
    ((Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContaining N hN x).card : ℕ) : ℝ) ≤
      volumeEstimateFinalConstant ^ t.leafCount *
        (t.autCard : ℝ) *
        branchScaleProduct (N.toHeppMarking hN) := by
  let Nm := N.toHeppMarking hN
  have hone := volume_estimate_one_anchor ht N hN x
  have hbase :
      volumeEstimateConstant ≤ volumeEstimateFinalConstant := by
    unfold volumeEstimateConstant volumeEstimateFinalConstant
    have htail :
        0 ≤ (step5VolumeConstant : ℝ) * 256 * Real.exp 12 := by
      positivity
    nlinarith
  have hconstant0 : 0 ≤ volumeEstimateConstant := by
    unfold volumeEstimateConstant
    positivity
  have hpow :
      volumeEstimateConstant ^ t.leafCount ≤
        volumeEstimateFinalConstant ^ t.leafCount := by
    exact pow_le_pow_left₀ hconstant0 hbase _
  have htail :
      0 ≤ (t.autCard : ℝ) * branchScaleProduct Nm :=
    mul_nonneg (by positivity) (branchScaleProduct_nonneg Nm)
  calc
    ((Fintype.card (AutHeppMarked t Nm) *
          (realizedSetsContaining N hN x).card : ℕ) : ℝ)
        ≤ volumeEstimateConstant ^ t.leafCount *
          (t.autCard : ℝ) * branchScaleProduct Nm := by
            simpa [Nm] using hone
    _ = volumeEstimateConstant ^ t.leafCount *
          ((t.autCard : ℝ) * branchScaleProduct Nm) := by ring
    _ ≤ volumeEstimateFinalConstant ^ t.leafCount *
          ((t.autCard : ℝ) * branchScaleProduct Nm) :=
      mul_le_mul_of_nonneg_right hpow htail
    _ = volumeEstimateFinalConstant ^ t.leafCount *
          (t.autCard : ℝ) * branchScaleProduct Nm := by ring

/-- **Paper (5.14), division-free form, for distinct prescribed points.**
The LCA scale gain has been converted to the spatial fourth-order bracket,
and all ordered-leaf choices are absorbed into the common universal
constant. -/
theorem volume_estimate_two_anchor_of_ne
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (x₀ x₁ : LatticePoint) (hne : x₀ ≠ x₁) :
    ((Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContainingPair N hN x₀ x₁).card : ℕ) : ℝ) ≤
      volumeEstimateFinalConstant ^ t.leafCount *
        (t.autCard : ℝ) *
        branchScaleProduct (N.toHeppMarking hN) *
        latticeBracketInvFourth x₀ x₁ := by
  let Nm := N.toHeppMarking hN
  have hraw := volume_estimate_two_anchor_raw ht N hN x₀ x₁ hne
  have hscalar :=
    leafCountSq_mul_pairIterationScalar_le t.leafCount
      (one_le_leafCount t)
  have htail :
      0 ≤ (t.autCard : ℝ) * branchScaleProduct Nm *
          latticeBracketInvFourth x₀ x₁ :=
    mul_nonneg
      (mul_nonneg (by positivity) (branchScaleProduct_nonneg Nm))
      (latticeBracketInvFourth_nonneg x₀ x₁)
  calc
    ((Fintype.card (AutHeppMarked t Nm) *
          (realizedSetsContainingPair N hN x₀ x₁).card : ℕ) : ℝ)
        ≤ (t.leafCount : ℝ) ^ 2 *
          (((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
            (256 : ℝ) ^ t.leafCount *
            Real.exp (12 * (t.leafCount : ℝ)) *
            (t.autCard : ℝ) *
            branchScaleProduct Nm) *
          (1 + 2 * (t.leafCount : ℝ)) ^ 4 *
          latticeBracketInvFourth x₀ x₁) := by
            simpa [Nm] using hraw
    _ = ((t.leafCount : ℝ) ^ 2 *
          ((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
            (256 : ℝ) ^ t.leafCount *
            Real.exp (12 * (t.leafCount : ℝ)) *
            (1 + 2 * (t.leafCount : ℝ)) ^ 4)) *
          ((t.autCard : ℝ) * branchScaleProduct Nm *
            latticeBracketInvFourth x₀ x₁) := by ring
    _ ≤ volumeEstimateFinalConstant ^ t.leafCount *
          ((t.autCard : ℝ) * branchScaleProduct Nm *
            latticeBracketInvFourth x₀ x₁) :=
      mul_le_mul_of_nonneg_right hscalar htail
    _ = volumeEstimateFinalConstant ^ t.leafCount *
          (t.autCard : ℝ) * branchScaleProduct Nm *
          latticeBracketInvFourth x₀ x₁ := by ring

/-- Requiring the same prescribed point twice gives exactly the one-anchor
realized-set carrier.  This is the diagonal case singled out in paper
Proposition 5.6, Step 2. -/
@[simp]
theorem realizedSetsContainingPair_self
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (x : LatticePoint) :
    realizedSetsContainingPair N hN x x =
      realizedSetsContaining N hN x := by
  ext Z
  simp

@[simp]
theorem latticeBracketInvFourth_self (x : LatticePoint) :
    latticeBracketInvFourth x x = 1 := by
  simp [latticeBracketInvFourth, znorm]

/-- **Paper (5.14), division-free form.**  This paper-facing version covers
all prescribed points.  On the diagonal it is exactly (5.13), since the
bracket equals one; off the diagonal it is the LCA-gain estimate above. -/
theorem volume_estimate_two_anchor
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (x₀ x₁ : LatticePoint) :
    ((Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContainingPair N hN x₀ x₁).card : ℕ) : ℝ) ≤
      volumeEstimateFinalConstant ^ t.leafCount *
        (t.autCard : ℝ) *
        branchScaleProduct (N.toHeppMarking hN) *
        latticeBracketInvFourth x₀ x₁ := by
  by_cases hne : x₀ ≠ x₁
  · exact volume_estimate_two_anchor_of_ne ht N hN x₀ x₁ hne
  · have heq : x₀ = x₁ := by
      by_contra h
      exact hne h
    subst x₁
    simpa using volume_estimate_one_anchor_final ht N hN x₀

/-- **Proposition 5.6 (P-5.6), complete frozen interface.**

The three conjuncts are respectively the division-free forms of (5.12),
(5.13), and (5.14), all using the order-forgetting tree automorphism group.
-/
theorem volume_estimate
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ} (N : BranchExponentData t (4 * M)) (hN : N.IsValid) :
    (∀ {m : ℕ} (mu : Multiplicities t)
        (y : Fin m → LatticePoint),
      RealizesTuple t (N.toHeppMarking hN) mu M y →
        Fintype.card (Aut t) ≤
          treeSymDenom t M m y *
            Fintype.card
              (AutHeppMarked t (N.toHeppMarking hN))) ∧
    (∀ x : LatticePoint,
      ((Fintype.card
          (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContaining N hN x).card : ℕ) : ℝ) ≤
        volumeEstimateFinalConstant ^ t.leafCount *
          (t.autCard : ℝ) *
          branchScaleProduct (N.toHeppMarking hN)) ∧
    (∀ x₀ x₁ : LatticePoint,
      ((Fintype.card
          (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContainingPair N hN x₀ x₁).card : ℕ) : ℝ) ≤
        volumeEstimateFinalConstant ^ t.leafCount *
          (t.autCard : ℝ) *
          branchScaleProduct (N.toHeppMarking hN) *
          latticeBracketInvFourth x₀ x₁) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m mu y hreal
    exact card_aut_le_treeSymDenom_mul_card_autHeppMarked
      ht (N.toHeppMarking hN) mu hreal
  · intro x
    exact volume_estimate_one_anchor_final ht N hN x
  · intro x₀ x₁
    exact volume_estimate_two_anchor ht N hN x₀ x₁

end Anderson4D
