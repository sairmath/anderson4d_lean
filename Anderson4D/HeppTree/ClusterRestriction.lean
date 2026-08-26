import Anderson4D.HeppTree.AnchoredEmbeddings
import Anderson4D.HeppTree.ClusterNetwork
import Anderson4D.HeppTree.LinkParent

/-!
# Finite restrictions of admissible embeddings to Hepp-tree clusters

This file supplies the carrier-level interface needed by paper §5.3,
Steps 5--6.  The geometric lemmas work on `leavesUnder v`, whereas the
finite counting carrier in `AnchoredEmbeddings` consists of full leaf
embeddings.  We bridge the two without introducing a new admissibility
notion: a cluster restriction is, by definition, the restriction of an
actual globally admissible embedding.
-/

namespace Anderson4D

open PlaneTree

/-- An embedding of the leaves below a fixed vertex. -/
abbrev ClusterEmbeddingAt {t : PlaneTree} (v : VPos t) :=
  ClusterLeafAt v → Fin 4 → ℤ

/-- Restrict a full leaf embedding to the leaves below `v`. -/
def restrictLeafEmbedding {t : PlaneTree} (z : LeafEmbedding t)
    (v : VPos t) : ClusterEmbeddingAt v :=
  fun l => z l.1

/-- A leaf below a child is canonically a leaf below its parent. -/
theorem leaf_under_parent_of_under_child
    {t : PlaneTree} {v c : VPos t} (hc : c ∈ childrenOf v)
    {l : {w // w ∈ Leaves t}} (hl : l ∈ leavesUnder c) :
    l ∈ leavesUnder v := by
  rw [mem_leavesUnder] at hl ⊢
  exact (mem_childrenOf.mp hc).2.trans hl

/-- Inclusion of a child-cluster leaf carrier into the parent cluster. -/
def clusterLeafInclusion {t : PlaneTree} {v c : VPos t}
    (hc : c ∈ childrenOf v) :
    ClusterLeafAt c ↪ ClusterLeafAt v where
  toFun l := ⟨l.1, leaf_under_parent_of_under_child hc l.2⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun x : ClusterLeafAt v => x.1) hab

/-- Restrict a parent-cluster embedding to one immediate child. -/
def restrictClusterEmbedding {t : PlaneTree} {v c : VPos t}
    (hc : c ∈ childrenOf v) (z : ClusterEmbeddingAt v) :
    ClusterEmbeddingAt c :=
  fun l => z (clusterLeafInclusion hc l)

@[simp]
theorem restrictClusterEmbedding_restrictLeafEmbedding
    {t : PlaneTree} (z : LeafEmbedding t) {v c : VPos t}
    (hc : c ∈ childrenOf v) :
    restrictClusterEmbedding hc (restrictLeafEmbedding z v) =
      restrictLeafEmbedding z c := by
  rfl

/-- The finite carrier of restrictions of actual admissible embeddings. -/
noncomputable def clusterRestrictions
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) : Finset (ClusterEmbeddingAt v) := by
  classical
  exact (admissibleLeafEmbeddings N hN).image
    fun z => restrictLeafEmbedding z v

@[simp]
theorem mem_clusterRestrictions
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {v : VPos t} {zv : ClusterEmbeddingAt v} :
    zv ∈ clusterRestrictions N hN v ↔
      ∃ z ∈ admissibleLeafEmbeddings N hN,
        restrictLeafEmbedding z v = zv := by
  classical
  simp [clusterRestrictions]

/-- Actual cluster restrictions with one specified cluster leaf anchored. -/
noncomputable def anchoredClusterRestrictions
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (f : ClusterLeafAt v) (x : Fin 4 → ℤ) :
    Finset (ClusterEmbeddingAt v) := by
  classical
  exact (clusterRestrictions N hN v).filter fun zv => zv f = x

@[simp]
theorem mem_anchoredClusterRestrictions
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {v : VPos t} {f : ClusterLeafAt v} {x : Fin 4 → ℤ}
    {zv : ClusterEmbeddingAt v} :
    zv ∈ anchoredClusterRestrictions N hN v f x ↔
      zv ∈ clusterRestrictions N hN v ∧ zv f = x := by
  classical
  simp [anchoredClusterRestrictions]

/-- Cardinality of the one-anchor actual cluster carrier. -/
noncomputable def clusterJ0
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (f : ClusterLeafAt v) (x : Fin 4 → ℤ) : ℕ :=
  (anchoredClusterRestrictions N hN v f x).card

/-- Actual cluster restrictions with two specified cluster leaves anchored. -/
noncomputable def doublyAnchoredClusterRestrictions
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (f₀ f₁ : ClusterLeafAt v)
    (x₀ x₁ : Fin 4 → ℤ) :
    Finset (ClusterEmbeddingAt v) := by
  classical
  exact (clusterRestrictions N hN v).filter fun zv =>
    zv f₀ = x₀ ∧ zv f₁ = x₁

@[simp]
theorem mem_doublyAnchoredClusterRestrictions
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {v : VPos t} {f₀ f₁ : ClusterLeafAt v}
    {x₀ x₁ : Fin 4 → ℤ} {zv : ClusterEmbeddingAt v} :
    zv ∈ doublyAnchoredClusterRestrictions N hN v f₀ f₁ x₀ x₁ ↔
      zv ∈ clusterRestrictions N hN v ∧
        zv f₀ = x₀ ∧ zv f₁ = x₁ := by
  classical
  simp [doublyAnchoredClusterRestrictions]

/-- Cardinality of the two-anchor actual cluster carrier. -/
noncomputable def clusterJ01
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (f₀ f₁ : ClusterLeafAt v)
    (x₀ x₁ : Fin 4 → ℤ) : ℕ :=
  (doublyAnchoredClusterRestrictions N hN v f₀ f₁ x₀ x₁).card

/-- Restriction preserves membership in the actual carrier. -/
theorem restrictClusterEmbedding_mem
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {v c : VPos t} (hc : c ∈ childrenOf v)
    {zv : ClusterEmbeddingAt v} (hzv : zv ∈ clusterRestrictions N hN v) :
    restrictClusterEmbedding hc zv ∈ clusterRestrictions N hN c := by
  obtain ⟨z, hz, rfl⟩ := mem_clusterRestrictions.mp hzv
  exact mem_clusterRestrictions.mpr
    ⟨z, hz, restrictClusterEmbedding_restrictLeafEmbedding z hc⟩

/-! ## Canonical extension and cover witnesses -/

/-- Choose one globally admissible extension of an actual cluster
restriction. -/
noncomputable def clusterExtension
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (zv : ClusterEmbeddingAt v)
    (hzv : zv ∈ clusterRestrictions N hN v) :
    LeafEmbedding t :=
  Classical.choose (mem_clusterRestrictions.mp hzv)

theorem clusterExtension_mem
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (zv : ClusterEmbeddingAt v)
    (hzv : zv ∈ clusterRestrictions N hN v) :
    clusterExtension N hN v zv hzv ∈
      admissibleLeafEmbeddings N hN :=
  (Classical.choose_spec (mem_clusterRestrictions.mp hzv)).1

theorem clusterExtension_admissible
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (zv : ClusterEmbeddingAt v)
    (hzv : zv ∈ clusterRestrictions N hN v) :
    IsAdmissible (N.toHeppMarking hN) M
      (clusterExtension N hN v zv hzv) :=
  mem_admissibleLeafEmbeddings.mp
    (clusterExtension_mem N hN v zv hzv)

theorem clusterExtension_restrict
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (zv : ClusterEmbeddingAt v)
    (hzv : zv ∈ clusterRestrictions N hN v) :
    restrictLeafEmbedding (clusterExtension N hN v zv hzv) v = zv :=
  (Classical.choose_spec (mem_clusterRestrictions.mp hzv)).2

@[simp]
theorem clusterExtension_value
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (zv : ClusterEmbeddingAt v)
    (hzv : zv ∈ clusterRestrictions N hN v)
    (l : ClusterLeafAt v) :
    clusterExtension N hN v zv hzv l.1 = zv l :=
  congrFun (clusterExtension_restrict N hN v zv hzv) l

/-- A canonical Step-4(b) cover of an actual cluster restriction. -/
noncomputable def actualClusterCover
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (zv : ClusterEmbeddingAt v)
    (hzv : zv ∈ clusterRestrictions N hN v)
    (R : ℝ) (hR : 0 < R) :
    Finset (Fin 4 → ℤ) :=
  Classical.choose
    (exists_clusterCover_of_isAdmissible
      (clusterExtension_admissible N hN v zv hzv) v hR)

theorem actualClusterCover_spec
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (v : VPos t) (zv : ClusterEmbeddingAt v)
    (hzv : zv ∈ clusterRestrictions N hN v)
    (R : ℝ) (hR : 0 < R) :
    let Q := actualClusterCover N hN v zv hzv R hR
    Q ⊆ (leavesUnder v).image
        (clusterExtension N hN v zv hzv) ∧
      (∀ l ∈ leavesUnder v,
        ∃ q ∈ Q,
          znorm (clusterExtension N hN v zv hzv l - q) ≤ R) ∧
      (Q.card : ℝ) ≤
        3 * (1 + tildeScale (N.toHeppMarking hN) v / R) :=
  Classical.choose_spec
    (exists_clusterCover_of_isAdmissible
      (clusterExtension_admissible N hN v zv hzv) v hR)

/-! ## Child partition of a non-leaf cluster -/

private theorem cr_isPos_append_singleton
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    {i : ℕ} (hi : i < childCount t p) :
    IsPos t (p ++ [i]) := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      rw [childCount] at hi
      simpa using (isPos_cons_iff.mpr ⟨hi, isPos_nil _⟩)
  | cons a p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨ha, hp'⟩ := isPos_cons_iff.mp hp
      rw [childCount, dif_pos ha] at hi
      rw [List.cons_append, isPos_cons_iff]
      exact ⟨ha, ih hp' hi⟩

private theorem cr_lt_childCount_of_isPos_append
    {t : PlaneTree} {p : Pos} (hp : IsPos t p)
    {i : ℕ} (hi : IsPos t (p ++ [i])) :
    i < childCount t p := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      rw [childCount]
      simpa using (isPos_cons_iff.mp hi).1
  | cons a p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨ha, hp'⟩ := isPos_cons_iff.mp hp
      have hi' : IsPos cs[a] (p ++ [i]) := by
        convert (isPos_cons_iff.mp hi).2 using 1
        simp
      rw [childCount, dif_pos ha]
      exact ih hp' hi'

/-- Child number `i` of `v`, represented as a vertex position. -/
def clusterChildAt {t : PlaneTree} (v : VPos t)
    (i : Fin (childCount t v.1)) : VPos t :=
  ⟨v.1 ++ [i.1], cr_isPos_append_singleton v.2 i.2⟩

@[simp]
theorem clusterChildAt_mem_childrenOf {t : PlaneTree}
    (v : VPos t) (i : Fin (childCount t v.1)) :
    clusterChildAt v i ∈ childrenOf v := by
  rw [mem_childrenOf]
  exact ⟨by simp [clusterChildAt], List.prefix_append _ _⟩

/-- Every leaf below a non-leaf vertex belongs to one immediate child. -/
theorem exists_child_containing_clusterLeaf
    {t : PlaneTree} {v : VPos t}
    (hv : 0 < childCount t v.1) (l : ClusterLeafAt v) :
    ∃ c : ClusterChild v, l.1 ∈ leavesUnder c.1 := by
  have hne : v.1 ≠ l.1.1.1 := by
    intro h
    have hzero : childCount t v.1 = 0 := by
      rw [h]
      exact mem_Leaves_iff.mp l.1.2
    omega
  let q := l.1.1.1.drop v.1.length
  have hq : v.1 ++ q = l.1.1.1 :=
    List.prefix_iff_eq_append.mp (mem_leavesUnder.mp l.2)
  have hqne : q ≠ [] := by
    intro hnil
    apply hne
    rw [hnil] at hq
    simpa using hq
  obtain ⟨i, q', hqform⟩ := List.exists_cons_of_ne_nil hqne
  rw [hqform] at hq
  have hipos : IsPos t (v.1 ++ [i]) := by
    apply IsPos_of_prefix l.1.1.2
    rw [← hq]
    simp
  let j : Fin (childCount t v.1) :=
    ⟨i, cr_lt_childCount_of_isPos_append v.2 hipos⟩
  let c : ClusterChild v :=
    ⟨clusterChildAt v j, clusterChildAt_mem_childrenOf v j⟩
  refine ⟨c, ?_⟩
  rw [mem_leavesUnder]
  change v.1 ++ [i] <+: l.1.1.1
  rw [← hq]
  simp

/-- Two immediate children containing the same leaf are equal. -/
theorem child_eq_of_common_clusterLeaf
    {t : PlaneTree} {v : VPos t} {c d : ClusterChild v}
    {l : {w // w ∈ Leaves t}}
    (hlc : l ∈ leavesUnder c.1) (hld : l ∈ leavesUnder d.1) :
    c = d := by
  apply Subtype.ext
  apply Subtype.ext
  have hlen : c.1.1.length = d.1.1.length := by
    rw [(mem_childrenOf.mp c.2).1, (mem_childrenOf.mp d.2).1]
  have hcp := mem_leavesUnder.mp hlc
  have hdp := mem_leavesUnder.mp hld
  rw [List.prefix_iff_eq_take] at hcp hdp
  calc
    c.1.1 = l.1.1.take c.1.1.length := hcp
    _ = l.1.1.take d.1.1.length := by rw [hlen]
    _ = d.1.1 := hdp.symm

/-- The tuple of all immediate-child restrictions. -/
def restrictEmbeddingToChildren
    {t : PlaneTree} {v : VPos t} (z : ClusterEmbeddingAt v) :
    ∀ c : ClusterChild v, ClusterEmbeddingAt c.1 :=
  fun c => restrictClusterEmbedding c.2 z

/-- A parent embedding is determined by all of its child restrictions. -/
theorem restrictEmbeddingToChildren_injective
    {t : PlaneTree} {v : VPos t} (hv : 0 < childCount t v.1) :
    Function.Injective
      (restrictEmbeddingToChildren (v := v)) := by
  intro z w h
  funext l
  obtain ⟨c, hlc⟩ :=
    exists_child_containing_clusterLeaf hv l
  let lc : ClusterLeafAt c.1 := ⟨l.1, hlc⟩
  have hc := congrFun (congrFun h c) lc
  exact hc

/-! ## Root carrier and the paper's `J₀` -/

/-- Regard a full-tree leaf as a leaf of the root cluster. -/
def rootClusterLeaf {t : PlaneTree}
    (f : {v // v ∈ Leaves t}) : ClusterLeafAt (rootV t) :=
  ⟨f, by
    rw [mem_leavesUnder]
    exact List.nil_prefix⟩

/-- Restriction to the root is injective on all leaf embeddings. -/
theorem restrictLeafEmbedding_root_injective (t : PlaneTree) :
    Function.Injective
      (fun z : LeafEmbedding t =>
        restrictLeafEmbedding z (rootV t)) := by
  intro z w h
  funext l
  exact congrFun h (rootClusterLeaf l)

/-- The anchored root-restriction carrier is exactly the image of the
paper's full-tree anchored carrier. -/
theorem anchoredClusterRestrictions_root_eq_image
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f : {v // v ∈ Leaves t}) (x : Fin 4 → ℤ) :
    anchoredClusterRestrictions N hN (rootV t)
        (rootClusterLeaf f) x =
      (anchoredLeafEmbeddings N hN f x).image
        fun z => restrictLeafEmbedding z (rootV t) := by
  classical
  ext zv
  constructor
  · intro hzv
    obtain ⟨hzvRoot, hanchor⟩ :=
      mem_anchoredClusterRestrictions.mp hzv
    obtain ⟨z, hz, hrestrict⟩ :=
      mem_clusterRestrictions.mp hzvRoot
    refine Finset.mem_image.mpr
      ⟨z, mem_anchoredLeafEmbeddings.mpr ⟨?_, ?_⟩, hrestrict⟩
    · exact hz
    · have hvalue := congrFun hrestrict (rootClusterLeaf f)
      exact hvalue.trans hanchor
  · intro hzv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hzv
    obtain ⟨hzAdm, hzAnchor⟩ :=
      mem_anchoredLeafEmbeddings.mp hz
    exact mem_anchoredClusterRestrictions.mpr
      ⟨mem_clusterRestrictions.mpr
          ⟨z, hzAdm, rfl⟩,
        hzAnchor⟩

/-- At the root, the actual cluster count is literally the paper's `J₀`. -/
theorem clusterJ0_root_eq_J0
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f : {v // v ∈ Leaves t}) (x : Fin 4 → ℤ) :
    clusterJ0 N hN (rootV t) (rootClusterLeaf f) x =
      J0 N hN f x := by
  classical
  rw [clusterJ0, J0,
    anchoredClusterRestrictions_root_eq_image N hN f x,
    Finset.card_image_of_injective]
  exact restrictLeafEmbedding_root_injective t

/-- The two-anchor root carrier is the image of the paper's full-tree
two-anchor carrier. -/
theorem doublyAnchoredClusterRestrictions_root_eq_image
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f₀ f₁ : {v // v ∈ Leaves t}) (x₀ x₁ : Fin 4 → ℤ) :
    doublyAnchoredClusterRestrictions N hN (rootV t)
        (rootClusterLeaf f₀) (rootClusterLeaf f₁) x₀ x₁ =
      (doublyAnchoredLeafEmbeddings N hN f₀ f₁ x₀ x₁).image
        fun z => restrictLeafEmbedding z (rootV t) := by
  classical
  ext zv
  constructor
  · intro hzv
    obtain ⟨hzvRoot, hanchor₀, hanchor₁⟩ :=
      mem_doublyAnchoredClusterRestrictions.mp hzv
    obtain ⟨z, hz, hrestrict⟩ :=
      mem_clusterRestrictions.mp hzvRoot
    refine Finset.mem_image.mpr
      ⟨z, mem_doublyAnchoredLeafEmbeddings.mpr
        ⟨hz, ?_, ?_⟩, hrestrict⟩
    · exact (congrFun hrestrict (rootClusterLeaf f₀)).trans hanchor₀
    · exact (congrFun hrestrict (rootClusterLeaf f₁)).trans hanchor₁
  · intro hzv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hzv
    obtain ⟨hzAdm, hzAnchor₀, hzAnchor₁⟩ :=
      mem_doublyAnchoredLeafEmbeddings.mp hz
    exact mem_doublyAnchoredClusterRestrictions.mpr
      ⟨mem_clusterRestrictions.mpr ⟨z, hzAdm, rfl⟩,
        hzAnchor₀, hzAnchor₁⟩

/-- At the root, the actual two-anchor cluster count is the paper's `J₀₁`. -/
theorem clusterJ01_root_eq_J01
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f₀ f₁ : {v // v ∈ Leaves t}) (x₀ x₁ : Fin 4 → ℤ) :
    clusterJ01 N hN (rootV t)
        (rootClusterLeaf f₀) (rootClusterLeaf f₁) x₀ x₁ =
      J01 N hN f₀ f₁ x₀ x₁ := by
  classical
  rw [clusterJ01, J01,
    doublyAnchoredClusterRestrictions_root_eq_image
      N hN f₀ f₁ x₀ x₁,
    Finset.card_image_of_injective]
  exact restrictLeafEmbedding_root_injective t

/-! ## A reusable finite exposure bound -/

/-- Recursive certificate for revealing one coordinate at a time.

At a head coordinate its image has size at most `B i`; in each resulting
fiber the tail coordinates satisfy the same certificate.  Once no
coordinates remain, at most one object is allowed. -/
noncomputable def HasExposureBounds
    {α ι κ : Type*} [DecidableEq α] [DecidableEq κ]
    (coord : ι → α → κ) (B : ι → ℝ) :
    Finset α → List ι → Prop
  | S, [] => S.card ≤ 1
  | S, i :: is =>
      ((S.image (coord i)).card : ℝ) ≤ B i ∧
        ∀ x ∈ S.image (coord i),
          HasExposureBounds coord B
            (S.filter fun a => coord i a = x) is

/-- Multiplication of the successive image bounds in an exposure
certificate.  This is the finite fiber-counting step used to multiply the
one-child estimate (5.23) through a parent-before-child list. -/
theorem card_le_prod_of_hasExposureBounds
    {α ι κ : Type*} [DecidableEq α] [DecidableEq κ]
    (coord : ι → α → κ) (B : ι → ℝ)
    (S : Finset α) (L : List ι)
    (hB : ∀ i ∈ L, 0 ≤ B i)
    (h : HasExposureBounds coord B S L) :
    (S.card : ℝ) ≤ (L.map B).prod := by
  induction L generalizing S with
  | nil =>
      simp only [HasExposureBounds, List.map_nil, List.prod_nil] at h ⊢
      exact_mod_cast h
  | cons i is ih =>
      rw [HasExposureBounds] at h
      obtain ⟨himage, hfib⟩ := h
      have hmaps :
          Set.MapsTo (coord i) (S : Set α)
            (S.image (coord i) : Set κ) := by
        intro a ha
        exact Finset.mem_image_of_mem _ ha
      have hcard :
          S.card =
            ∑ x ∈ S.image (coord i),
              (S.filter fun a => coord i a = x).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
      have htail : 0 ≤ (is.map B).prod := by
        apply List.prod_nonneg
        intro b hb
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
        exact hB j (by simp [hj])
      rw [hcard, Nat.cast_sum]
      simp only [List.map_cons, List.prod_cons]
      calc
        ∑ x ∈ S.image (coord i),
            ((S.filter fun a => coord i a = x).card : ℝ)
            ≤ ∑ _x ∈ S.image (coord i), (is.map B).prod := by
              apply Finset.sum_le_sum
              intro x hx
              exact ih
                (S := S.filter fun a => coord i a = x)
                (fun j hj => hB j (by simp [hj]))
                (hfib x hx)
        _ = ((S.image (coord i)).card : ℝ) *
              (is.map B).prod := by simp
        _ ≤ B i * (is.map B).prod :=
          mul_le_mul_of_nonneg_right himage htail

/-- A common sigma codomain for exposing child restrictions. -/
def childRestrictionCoordinate
    {t : PlaneTree} {v : VPos t}
    (c : ClusterChild v) (z : ClusterEmbeddingAt v) :
    (c : ClusterChild v) ×' ClusterEmbeddingAt c.1 :=
  ⟨c, restrictClusterEmbedding c.2 z⟩

end Anderson4D
