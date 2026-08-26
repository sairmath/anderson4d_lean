import Anderson4D.HeppTree.RealizationData
import Anderson4D.HeppTree.Admissible

/-!
# Finite realization sets for a fixed marked Hepp tree

For a fixed plane tree and finite restricted branch data, Proposition 5.6
counts realized **sets** of lattice points.  The outer carrier in this file
is therefore the image of the admissible-embedding finset under
`z ↦ Finset.univ.image z`.  In particular, embeddings with the same image
are deliberately deduplicated.

Only the elementary image-cardinality inequality is recorded here.  It is
not the sharp embedding estimate (5.13), whose proof requires the geometric
and automorphism arguments of Proposition 5.6.
-/

namespace Anderson4D

open PlaneTree

/-- A lattice embedding indexed by the leaves of `t`. -/
abbrev LeafEmbedding (t : PlaneTree) :=
  {v // v ∈ Leaves t} → Fin 4 → ℤ

/-- The set of lattice points underlying a leaf embedding.  This forgets the
leaf indices and all multiplicities. -/
def leafEmbeddingImage {t : PlaneTree} (z : LeafEmbedding t) :
    Finset (Fin 4 → ℤ) :=
  Finset.univ.image z

/-- All leaf-indexed embeddings into the lattice box `[-M,M]⁴`. -/
noncomputable def boundedLeafEmbeddings (t : PlaneTree) (M : ℕ) :
    Finset (LeafEmbedding t) :=
  Fintype.piFinset fun _ =>
    Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M

@[simp]
theorem mem_boundedLeafEmbeddings {t : PlaneTree} {M : ℕ}
    {z : LeafEmbedding t} :
    z ∈ boundedLeafEmbeddings t M ↔
      ∀ l i, |z l i| ≤ (M : ℤ) := by
  classical
  simp [boundedLeafEmbeddings, abs_le]

/-- Cardinality of the explicit ambient embedding box. -/
theorem card_boundedLeafEmbeddings (t : PlaneTree) (M : ℕ) :
    (boundedLeafEmbeddings t M).card =
      (2 * M + 1) ^ (4 * (Leaves t).card) := by
  classical
  have hIcc : (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
    rw [Int.card_Icc]
    omega
  simp only [boundedLeafEmbeddings, Fintype.card_piFinset, hIcc,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe]
  rw [pow_mul]

/-- The explicit finite carrier of admissible embeddings for fixed restricted
branch data.  The proof `hN` only packages `N` as a `HeppMarking`; it is not
enumerated and contributes no count. -/
noncomputable def admissibleLeafEmbeddings
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid) :
    Finset (LeafEmbedding t) := by
  classical
  exact (boundedLeafEmbeddings t M).filter fun z =>
    IsAdmissible (N.toHeppMarking hN) M z

@[simp]
theorem mem_admissibleLeafEmbeddings
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {z : LeafEmbedding t} :
    z ∈ admissibleLeafEmbeddings N hN ↔
      IsAdmissible (N.toHeppMarking hN) M z := by
  classical
  rw [admissibleLeafEmbeddings]
  constructor
  · exact fun hz => (Finset.mem_filter.mp hz).2
  · intro hz
    exact Finset.mem_filter.mpr
      ⟨mem_boundedLeafEmbeddings.mpr hz.bounded, hz⟩

/-- Realized sets for a fixed tree and restricted branch datum.  `Finset.image`
is essential: two admissible leaf embeddings with the same range represent
one realized set. -/
noncomputable def realizedSets
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid) :
    Finset (Finset (Fin 4 → ℤ)) :=
  (admissibleLeafEmbeddings N hN).image leafEmbeddingImage

/-- Membership is exactly existence of an admissible embedding with the
specified image. -/
theorem mem_realizedSets_iff
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {Z : Finset (Fin 4 → ℤ)} :
    Z ∈ realizedSets N hN ↔
      ∃ z : LeafEmbedding t,
        IsAdmissible (N.toHeppMarking hN) M z ∧
          Finset.univ.image z = Z := by
  classical
  constructor
  · intro hZ
    obtain ⟨z, hz, himage⟩ := Finset.mem_image.mp hZ
    exact ⟨z, mem_admissibleLeafEmbeddings.mp hz, himage⟩
  · rintro ⟨z, hz, himage⟩
    exact Finset.mem_image.mpr
      ⟨z, mem_admissibleLeafEmbeddings.mpr hz, himage⟩

/-- The preceding membership theorem in the existing `Realizes` vocabulary. -/
theorem mem_realizedSets_iff_realizes
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {Z : Finset (Fin 4 → ℤ)} :
    Z ∈ realizedSets N hN ↔
      Realizes (N.toHeppMarking hN) M Z := by
  rw [mem_realizedSets_iff]
  rfl

/-- Deduplication can only decrease cardinality.  This deliberately does not
claim the sharp formula or bound (5.13). -/
theorem card_realizedSets_le_card_admissibleLeafEmbeddings
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid) :
    (realizedSets N hN).card ≤
      (admissibleLeafEmbeddings N hN).card := by
  classical
  exact Finset.card_image_le

/-- A coarse ambient-box consequence of the image bound. -/
theorem card_realizedSets_le_box
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid) :
    (realizedSets N hN).card ≤
      (2 * M + 1) ^ (4 * (Leaves t).card) := by
  calc
    (realizedSets N hN).card
        ≤ (admissibleLeafEmbeddings N hN).card :=
      card_realizedSets_le_card_admissibleLeafEmbeddings N hN
    _ ≤ (boundedLeafEmbeddings t M).card := by
      classical
      simpa [admissibleLeafEmbeddings] using
        (Finset.card_filter_le (boundedLeafEmbeddings t M)
          fun z => IsAdmissible (N.toHeppMarking hN) M z)
    _ = (2 * M + 1) ^ (4 * (Leaves t).card) :=
      card_boundedLeafEmbeddings t M

/-! ## Index invariance of the image construction -/

/-- Reindex a leaf embedding along an arbitrary equivalence of leaf carriers.
This is the basic operation later used for tree automorphisms. -/
def reindexLeafEmbedding {t t' : PlaneTree}
    (e : {v // v ∈ Leaves t} ≃ {v // v ∈ Leaves t'})
    (z : LeafEmbedding t) : LeafEmbedding t' :=
  fun l => z (e.symm l)

/-- Reindexing leaves does not change the realized set of lattice points. -/
theorem leafEmbeddingImage_reindex {t t' : PlaneTree}
    (e : {v // v ∈ Leaves t} ≃ {v // v ∈ Leaves t'})
    (z : LeafEmbedding t) :
    leafEmbeddingImage (reindexLeafEmbedding e z) =
      leafEmbeddingImage z := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨e.symm l, Finset.mem_univ _, hl⟩
  · intro hx
    obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨e l, Finset.mem_univ _, ?_⟩
    change z (e.symm (e l)) = x
    simpa using hl

/-- The explicit box enumeration is invariant under leaf reindexing. -/
theorem reindexLeafEmbedding_mem_bounded_iff
    {t t' : PlaneTree} {M : ℕ}
    (e : {v // v ∈ Leaves t} ≃ {v // v ∈ Leaves t'})
    (z : LeafEmbedding t) :
    reindexLeafEmbedding e z ∈ boundedLeafEmbeddings t' M ↔
      z ∈ boundedLeafEmbeddings t M := by
  rw [mem_boundedLeafEmbeddings, mem_boundedLeafEmbeddings]
  constructor
  · intro h l i
    simpa [reindexLeafEmbedding] using h (e l) i
  · intro h l i
    exact h (e.symm l) i

/-- The finite carriers are independent of the particular proof that the
restricted branch data is valid. -/
theorem admissibleLeafEmbeddings_proof_irrel
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN hN' : N.IsValid) :
    admissibleLeafEmbeddings N hN =
      admissibleLeafEmbeddings N hN' := by
  have hp : hN = hN' := Subsingleton.elim _ _
  cases hp
  rfl

/-- Proof irrelevance also holds after passing from embeddings to sets. -/
theorem realizedSets_proof_irrel
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN hN' : N.IsValid) :
    realizedSets N hN = realizedSets N hN' := by
  have hp : hN = hN' := Subsingleton.elim _ _
  cases hp
  rfl

/-! ## Interface to full finite realization data -/

/-- Realized sets attached to a valid `RealizationData` pair.  Only its
branch component is used; the leaf multiplicity component remains part of
the separate denominator data. -/
noncomputable def realizedSetsOfData
    {t : PlaneTree} {M m : ℕ}
    (d : RealizationData t M m) (hd : d.IsValid) :
    Finset (Finset (Fin 4 → ℤ)) :=
  realizedSets d.1 hd.1

theorem mem_realizedSetsOfData_iff
    {t : PlaneTree} {M m : ℕ}
    {d : RealizationData t M m} {hd : d.IsValid}
    {Z : Finset (Fin 4 → ℤ)} :
    Z ∈ realizedSetsOfData d hd ↔
      Realizes (d.toHeppMarking hd) M Z := by
  exact mem_realizedSets_iff_realizes

end Anderson4D
