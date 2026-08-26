import Anderson4D.HeppTree.EmbeddingOrbit

/-!
# Anchored admissible embeddings

Paper Proposition 5.6, Step 2 reduces counts of realized sets containing one
or two prescribed lattice points to admissible embeddings with specified
leaves anchored at those points.  This file records the exact finite counting
statements before the geometric estimates of the subsequent steps.
-/

namespace Anderson4D

open PlaneTree

/-! ## Filtering by a property of the realized image -/

/-- Realized sets satisfying a predicate on their underlying point set. -/
noncomputable def realizedSetsSatisfying
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (P : Finset (Fin 4 → ℤ) → Prop) :
    Finset (Finset (Fin 4 → ℤ)) := by
  classical
  exact (realizedSets N hN).filter P

@[simp]
theorem mem_realizedSetsSatisfying
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {P : Finset (Fin 4 → ℤ) → Prop}
    {Z : Finset (Fin 4 → ℤ)} :
    Z ∈ realizedSetsSatisfying N hN P ↔
      Z ∈ realizedSets N hN ∧ P Z := by
  classical
  simp [realizedSetsSatisfying]

/-- Admissible embeddings whose unindexed image satisfies `P`. -/
noncomputable def admissibleLeafEmbeddingsSatisfying
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (P : Finset (Fin 4 → ℤ) → Prop) :
    Finset (LeafEmbedding t) := by
  classical
  exact (admissibleLeafEmbeddings N hN).filter fun z =>
    P (leafEmbeddingImage z)

@[simp]
theorem mem_admissibleLeafEmbeddingsSatisfying
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {P : Finset (Fin 4 → ℤ) → Prop}
    {z : LeafEmbedding t} :
    z ∈ admissibleLeafEmbeddingsSatisfying N hN P ↔
      z ∈ admissibleLeafEmbeddings N hN ∧
        P (leafEmbeddingImage z) := by
  classical
  simp [admissibleLeafEmbeddingsSatisfying]

/-- Restrict `markedOrbitEmbedding` to realized sets satisfying `P`. -/
noncomputable def markedOrbitEmbeddingSatisfying
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (P : Finset (Fin 4 → ℤ) → Prop) :
    AutHeppMarked t (N.toHeppMarking hN) ×
        ↥(realizedSetsSatisfying N hN P) →
      ↥(admissibleLeafEmbeddingsSatisfying N hN P) :=
  fun p => by
    let Z : ↥(realizedSets N hN) :=
      ⟨p.2.1, (mem_realizedSetsSatisfying.mp p.2.2).1⟩
    let z := markedOrbitEmbedding N hN (p.1, Z)
    refine ⟨z.1, mem_admissibleLeafEmbeddingsSatisfying.mpr
      ⟨z.2, ?_⟩⟩
    rw [markedOrbitEmbedding_image N hN (p.1, Z)]
    exact (mem_realizedSetsSatisfying.mp p.2.2).2

/-- The restricted orbit map remains injective. -/
theorem markedOrbitEmbeddingSatisfying_injective
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (P : Finset (Fin 4 → ℤ) → Prop) :
    Function.Injective (markedOrbitEmbeddingSatisfying N hN P) := by
  intro p q hpq
  let pZ : ↥(realizedSets N hN) :=
    ⟨p.2.1, (mem_realizedSetsSatisfying.mp p.2.2).1⟩
  let qZ : ↥(realizedSets N hN) :=
    ⟨q.2.1, (mem_realizedSetsSatisfying.mp q.2.2).1⟩
  have hbase :
      markedOrbitEmbedding N hN (p.1, pZ) =
        markedOrbitEmbedding N hN (q.1, qZ) := by
    apply Subtype.ext
    have hval := congrArg Subtype.val hpq
    simpa only [markedOrbitEmbeddingSatisfying] using hval
  have hpqBase :
      (p.1, pZ) = (q.1, qZ) :=
    markedOrbitEmbedding_injective N hN hbase
  have hg : p.1 = q.1 :=
    congrArg
      (fun x :
        AutHeppMarked t (N.toHeppMarking hN) ×
          ↥(realizedSets N hN) => x.1)
      hpqBase
  have hZ : p.2.1 = q.2.1 := by
    exact congrArg
      (fun x :
        AutHeppMarked t (N.toHeppMarking hN) ×
          ↥(realizedSets N hN) => x.2.1)
      hpqBase
  exact Prod.ext hg (Subtype.ext hZ)

/-- General restricted form of the free-orbit count. -/
theorem card_autHeppMarked_mul_card_realizedSetsSatisfying_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (P : Finset (Fin 4 → ℤ) → Prop) :
    Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsSatisfying N hN P).card
      ≤ (admissibleLeafEmbeddingsSatisfying N hN P).card := by
  have hcard :=
    Fintype.card_le_of_injective
      (markedOrbitEmbeddingSatisfying N hN P)
      (markedOrbitEmbeddingSatisfying_injective N hN P)
  simpa [Fintype.card_prod, Fintype.card_coe] using hcard

/-! ## One-point and two-point image conditions -/

/-- Realized sets containing a prescribed lattice point. -/
noncomputable def realizedSetsContaining
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ : Fin 4 → ℤ) :
    Finset (Finset (Fin 4 → ℤ)) :=
  realizedSetsSatisfying N hN fun Z => z₀ ∈ Z

@[simp]
theorem mem_realizedSetsContaining
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {z₀ : Fin 4 → ℤ} {Z : Finset (Fin 4 → ℤ)} :
    Z ∈ realizedSetsContaining N hN z₀ ↔
      Z ∈ realizedSets N hN ∧ z₀ ∈ Z :=
  mem_realizedSetsSatisfying

/-- Realized sets containing both prescribed points. -/
noncomputable def realizedSetsContainingPair
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ z₁ : Fin 4 → ℤ) :
    Finset (Finset (Fin 4 → ℤ)) :=
  realizedSetsSatisfying N hN fun Z => z₀ ∈ Z ∧ z₁ ∈ Z

@[simp]
theorem mem_realizedSetsContainingPair
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {z₀ z₁ : Fin 4 → ℤ} {Z : Finset (Fin 4 → ℤ)} :
    Z ∈ realizedSetsContainingPair N hN z₀ z₁ ↔
      Z ∈ realizedSets N hN ∧ z₀ ∈ Z ∧ z₁ ∈ Z := by
  rw [realizedSetsContainingPair, mem_realizedSetsSatisfying]

/-- Admissible embeddings whose image contains a prescribed point. -/
noncomputable def admissibleLeafEmbeddingsContaining
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ : Fin 4 → ℤ) :
    Finset (LeafEmbedding t) :=
  admissibleLeafEmbeddingsSatisfying N hN fun Z => z₀ ∈ Z

@[simp]
theorem mem_admissibleLeafEmbeddingsContaining
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {z₀ : Fin 4 → ℤ} {z : LeafEmbedding t} :
    z ∈ admissibleLeafEmbeddingsContaining N hN z₀ ↔
      z ∈ admissibleLeafEmbeddings N hN ∧
        z₀ ∈ leafEmbeddingImage z :=
  mem_admissibleLeafEmbeddingsSatisfying

/-- Admissible embeddings whose image contains both prescribed points. -/
noncomputable def admissibleLeafEmbeddingsContainingPair
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ z₁ : Fin 4 → ℤ) :
    Finset (LeafEmbedding t) :=
  admissibleLeafEmbeddingsSatisfying N hN fun Z =>
    z₀ ∈ Z ∧ z₁ ∈ Z

@[simp]
theorem mem_admissibleLeafEmbeddingsContainingPair
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {z₀ z₁ : Fin 4 → ℤ} {z : LeafEmbedding t} :
    z ∈ admissibleLeafEmbeddingsContainingPair N hN z₀ z₁ ↔
      z ∈ admissibleLeafEmbeddings N hN ∧
        z₀ ∈ leafEmbeddingImage z ∧ z₁ ∈ leafEmbeddingImage z := by
  rw [admissibleLeafEmbeddingsContainingPair,
    mem_admissibleLeafEmbeddingsSatisfying]

/-- One-point restricted orbit map. -/
noncomputable def markedOrbitEmbeddingContaining
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ : Fin 4 → ℤ) :
    AutHeppMarked t (N.toHeppMarking hN) ×
        ↥(realizedSetsContaining N hN z₀) →
      ↥(admissibleLeafEmbeddingsContaining N hN z₀) :=
  markedOrbitEmbeddingSatisfying N hN fun Z => z₀ ∈ Z

/-- Two-point restricted orbit map. -/
noncomputable def markedOrbitEmbeddingContainingPair
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ z₁ : Fin 4 → ℤ) :
    AutHeppMarked t (N.toHeppMarking hN) ×
        ↥(realizedSetsContainingPair N hN z₀ z₁) →
      ↥(admissibleLeafEmbeddingsContainingPair N hN z₀ z₁) :=
  markedOrbitEmbeddingSatisfying N hN fun Z => z₀ ∈ Z ∧ z₁ ∈ Z

/-- The one-point restricted orbit map is injective. -/
theorem markedOrbitEmbeddingContaining_injective
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ : Fin 4 → ℤ) :
    Function.Injective (markedOrbitEmbeddingContaining N hN z₀) :=
  markedOrbitEmbeddingSatisfying_injective N hN fun Z => z₀ ∈ Z

/-- The two-point restricted orbit map is injective. -/
theorem markedOrbitEmbeddingContainingPair_injective
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ z₁ : Fin 4 → ℤ) :
    Function.Injective
      (markedOrbitEmbeddingContainingPair N hN z₀ z₁) :=
  markedOrbitEmbeddingSatisfying_injective N hN fun Z =>
    z₀ ∈ Z ∧ z₁ ∈ Z

/-- Free-orbit count restricted to realized sets containing `z₀`. -/
theorem card_autHeppMarked_mul_card_realizedSetsContaining_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ : Fin 4 → ℤ) :
    Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContaining N hN z₀).card
      ≤ (admissibleLeafEmbeddingsContaining N hN z₀).card :=
  card_autHeppMarked_mul_card_realizedSetsSatisfying_le
    N hN fun Z => z₀ ∈ Z

/-- Free-orbit count restricted to realized sets containing both points. -/
theorem card_autHeppMarked_mul_card_realizedSetsContainingPair_le
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ z₁ : Fin 4 → ℤ) :
    Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContainingPair N hN z₀ z₁).card
      ≤ (admissibleLeafEmbeddingsContainingPair N hN z₀ z₁).card :=
  card_autHeppMarked_mul_card_realizedSetsSatisfying_le
    N hN fun Z => z₀ ∈ Z ∧ z₁ ∈ Z

/-! ## Fixed-leaf anchored carriers -/

/-- Admissible embeddings sending the specified leaf to `z₀`. -/
noncomputable def anchoredLeafEmbeddings
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f₀ : {v // v ∈ Leaves t}) (z₀ : Fin 4 → ℤ) :
    Finset (LeafEmbedding t) := by
  classical
  exact (admissibleLeafEmbeddings N hN).filter fun z => z f₀ = z₀

@[simp]
theorem mem_anchoredLeafEmbeddings
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {f₀ : {v // v ∈ Leaves t}} {z₀ : Fin 4 → ℤ}
    {z : LeafEmbedding t} :
    z ∈ anchoredLeafEmbeddings N hN f₀ z₀ ↔
      z ∈ admissibleLeafEmbeddings N hN ∧ z f₀ = z₀ := by
  classical
  simp [anchoredLeafEmbeddings]

/-- Paper's one-anchor count for a fixed leaf. -/
noncomputable def J0
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f₀ : {v // v ∈ Leaves t}) (z₀ : Fin 4 → ℤ) : ℕ :=
  (anchoredLeafEmbeddings N hN f₀ z₀).card

/-- Admissible embeddings sending two specified leaves to `z₀,z₁`. -/
noncomputable def doublyAnchoredLeafEmbeddings
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f₀ f₁ : {v // v ∈ Leaves t}) (z₀ z₁ : Fin 4 → ℤ) :
    Finset (LeafEmbedding t) := by
  classical
  exact (admissibleLeafEmbeddings N hN).filter fun z =>
    z f₀ = z₀ ∧ z f₁ = z₁

@[simp]
theorem mem_doublyAnchoredLeafEmbeddings
    {t : PlaneTree} {M : ℕ}
    {N : BranchExponentData t (4 * M)} {hN : N.IsValid}
    {f₀ f₁ : {v // v ∈ Leaves t}} {z₀ z₁ : Fin 4 → ℤ}
    {z : LeafEmbedding t} :
    z ∈ doublyAnchoredLeafEmbeddings N hN f₀ f₁ z₀ z₁ ↔
      z ∈ admissibleLeafEmbeddings N hN ∧
        z f₀ = z₀ ∧ z f₁ = z₁ := by
  classical
  simp [doublyAnchoredLeafEmbeddings]

/-- Paper's two-anchor count for a fixed ordered pair of leaves. -/
noncomputable def J01
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f₀ f₁ : {v // v ∈ Leaves t}) (z₀ z₁ : Fin 4 → ℤ) : ℕ :=
  (doublyAnchoredLeafEmbeddings N hN f₀ f₁ z₀ z₁).card

/-! ## Exact leafwise covers and their cardinality bounds -/

/-- An admissible embedding contains `z₀` exactly when at least one leaf is
anchored at `z₀`. -/
theorem admissibleLeafEmbeddingsContaining_eq_biUnion_anchored
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ : Fin 4 → ℤ) :
    admissibleLeafEmbeddingsContaining N hN z₀ =
      (Finset.univ : Finset {v // v ∈ Leaves t}).biUnion fun f₀ =>
        anchoredLeafEmbeddings N hN f₀ z₀ := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hzAdm, hz₀⟩ :=
      mem_admissibleLeafEmbeddingsContaining.mp hz
    obtain ⟨f₀, -, hf₀⟩ := Finset.mem_image.mp hz₀
    exact Finset.mem_biUnion.mpr
      ⟨f₀, Finset.mem_univ _,
        mem_anchoredLeafEmbeddings.mpr ⟨hzAdm, hf₀⟩⟩
  · intro hz
    obtain ⟨f₀, -, hf₀⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hzAdm, hf₀z⟩ :=
      mem_anchoredLeafEmbeddings.mp hf₀
    exact mem_admissibleLeafEmbeddingsContaining.mpr
      ⟨hzAdm, Finset.mem_image.mpr
        ⟨f₀, Finset.mem_univ _, hf₀z⟩⟩

/-- Union bound over the possible leaf carrying `z₀`. -/
theorem card_admissibleLeafEmbeddingsContaining_le_sum_J0
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ : Fin 4 → ℤ) :
    (admissibleLeafEmbeddingsContaining N hN z₀).card ≤
      ∑ f₀ : {v // v ∈ Leaves t}, J0 N hN f₀ z₀ := by
  rw [admissibleLeafEmbeddingsContaining_eq_biUnion_anchored]
  simpa [J0] using
    (Finset.card_biUnion_le :
      ((Finset.univ : Finset {v // v ∈ Leaves t}).biUnion fun f₀ =>
        anchoredLeafEmbeddings N hN f₀ z₀).card ≤
      ∑ f₀ ∈ (Finset.univ : Finset {v // v ∈ Leaves t}),
        (anchoredLeafEmbeddings N hN f₀ z₀).card)

/-- The full one-anchor Step 2 reduction, retaining the exact sum over the
choice of anchored leaf. -/
theorem card_autHeppMarked_mul_card_realizedSetsContaining_le_sum_J0
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ : Fin 4 → ℤ) :
    Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContaining N hN z₀).card
      ≤ ∑ f₀ : {v // v ∈ Leaves t}, J0 N hN f₀ z₀ :=
  (card_autHeppMarked_mul_card_realizedSetsContaining_le N hN z₀).trans
    (card_admissibleLeafEmbeddingsContaining_le_sum_J0 N hN z₀)

/-- An admissible embedding contains both points exactly when an ordered leaf
pair is anchored at them. -/
theorem admissibleLeafEmbeddingsContainingPair_eq_biUnion_anchored
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ z₁ : Fin 4 → ℤ) :
    admissibleLeafEmbeddingsContainingPair N hN z₀ z₁ =
      (Finset.univ :
        Finset ({v // v ∈ Leaves t} × {v // v ∈ Leaves t})).biUnion
          fun f =>
            doublyAnchoredLeafEmbeddings N hN f.1 f.2 z₀ z₁ := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hzAdm, hz₀, hz₁⟩ :=
      mem_admissibleLeafEmbeddingsContainingPair.mp hz
    obtain ⟨f₀, -, hf₀⟩ := Finset.mem_image.mp hz₀
    obtain ⟨f₁, -, hf₁⟩ := Finset.mem_image.mp hz₁
    exact Finset.mem_biUnion.mpr
      ⟨(f₀, f₁), Finset.mem_univ _,
        mem_doublyAnchoredLeafEmbeddings.mpr
          ⟨hzAdm, hf₀, hf₁⟩⟩
  · intro hz
    obtain ⟨f, -, hf⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hzAdm, hf₀, hf₁⟩ :=
      mem_doublyAnchoredLeafEmbeddings.mp hf
    exact mem_admissibleLeafEmbeddingsContainingPair.mpr
      ⟨hzAdm,
        Finset.mem_image.mpr ⟨f.1, Finset.mem_univ _, hf₀⟩,
        Finset.mem_image.mpr ⟨f.2, Finset.mem_univ _, hf₁⟩⟩

/-- Union bound over ordered pairs of leaves carrying `z₀,z₁`. -/
theorem card_admissibleLeafEmbeddingsContainingPair_le_sum_J01
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ z₁ : Fin 4 → ℤ) :
    (admissibleLeafEmbeddingsContainingPair N hN z₀ z₁).card ≤
      ∑ f : {v // v ∈ Leaves t} × {v // v ∈ Leaves t},
        J01 N hN f.1 f.2 z₀ z₁ := by
  rw [admissibleLeafEmbeddingsContainingPair_eq_biUnion_anchored]
  simpa [J01] using
    (Finset.card_biUnion_le :
      ((Finset.univ :
        Finset ({v // v ∈ Leaves t} × {v // v ∈ Leaves t})).biUnion
          fun f =>
            doublyAnchoredLeafEmbeddings N hN f.1 f.2 z₀ z₁).card ≤
      ∑ f ∈ (Finset.univ :
          Finset ({v // v ∈ Leaves t} × {v // v ∈ Leaves t})),
        (doublyAnchoredLeafEmbeddings N hN f.1 f.2 z₀ z₁).card)

/-- The full two-anchor Step 2 reduction with the exact ordered-pair sum. -/
theorem card_autHeppMarked_mul_card_realizedSetsContainingPair_le_sum_J01
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ z₁ : Fin 4 → ℤ) :
    Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContainingPair N hN z₀ z₁).card
      ≤ ∑ f : {v // v ∈ Leaves t} × {v // v ∈ Leaves t},
        J01 N hN f.1 f.2 z₀ z₁ :=
  (card_autHeppMarked_mul_card_realizedSetsContainingPair_le
      N hN z₀ z₁).trans
    (card_admissibleLeafEmbeddingsContainingPair_le_sum_J01
      N hN z₀ z₁)

/-! ## Distinct anchors for distinct prescribed points -/

/-- Ordered pairs of distinct leaves. -/
def distinctLeafPairs (t : PlaneTree) :
    Finset ({v // v ∈ Leaves t} × {v // v ∈ Leaves t}) := by
  classical
  exact Finset.univ.filter fun f => f.1 ≠ f.2

@[simp]
theorem mem_distinctLeafPairs
    {t : PlaneTree}
    {f : {v // v ∈ Leaves t} × {v // v ∈ Leaves t}} :
    f ∈ distinctLeafPairs t ↔ f.1 ≠ f.2 := by
  classical
  simp [distinctLeafPairs]

/-- A single leaf cannot be anchored at two distinct lattice points. -/
theorem doublyAnchoredLeafEmbeddings_same_leaf_eq_empty
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f : {v // v ∈ Leaves t}) (z₀ z₁ : Fin 4 → ℤ)
    (hne : z₀ ≠ z₁) :
    doublyAnchoredLeafEmbeddings N hN f f z₀ z₁ = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨-, hz₀, hz₁⟩ :=
    mem_doublyAnchoredLeafEmbeddings.mp hz
  exact hne (hz₀.symm.trans hz₁)

theorem J01_same_leaf_eq_zero
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (f : {v // v ∈ Leaves t}) (z₀ z₁ : Fin 4 → ℤ)
    (hne : z₀ ≠ z₁) :
    J01 N hN f f z₀ z₁ = 0 := by
  rw [J01, doublyAnchoredLeafEmbeddings_same_leaf_eq_empty
    N hN f z₀ z₁ hne]
  rfl

/-- If `z₀ ≠ z₁`, the two-point image carrier is already covered by
anchoring ordered pairs of distinct leaves. -/
theorem admissibleLeafEmbeddingsContainingPair_eq_biUnion_distinctAnchored
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ z₁ : Fin 4 → ℤ) (hne : z₀ ≠ z₁) :
    admissibleLeafEmbeddingsContainingPair N hN z₀ z₁ =
      (distinctLeafPairs t).biUnion fun f =>
        doublyAnchoredLeafEmbeddings N hN f.1 f.2 z₀ z₁ := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨hzAdm, hz₀, hz₁⟩ :=
      mem_admissibleLeafEmbeddingsContainingPair.mp hz
    obtain ⟨f₀, -, hf₀⟩ := Finset.mem_image.mp hz₀
    obtain ⟨f₁, -, hf₁⟩ := Finset.mem_image.mp hz₁
    have hfne : f₀ ≠ f₁ := by
      intro hff
      apply hne
      calc
        z₀ = z f₀ := hf₀.symm
        _ = z f₁ := congrArg z hff
        _ = z₁ := hf₁
    exact Finset.mem_biUnion.mpr
      ⟨(f₀, f₁), mem_distinctLeafPairs.mpr hfne,
        mem_doublyAnchoredLeafEmbeddings.mpr
          ⟨hzAdm, hf₀, hf₁⟩⟩
  · intro hz
    obtain ⟨f, -, hf⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hzAdm, hf₀, hf₁⟩ :=
      mem_doublyAnchoredLeafEmbeddings.mp hf
    exact mem_admissibleLeafEmbeddingsContainingPair.mpr
      ⟨hzAdm,
        Finset.mem_image.mpr ⟨f.1, Finset.mem_univ _, hf₀⟩,
        Finset.mem_image.mpr ⟨f.2, Finset.mem_univ _, hf₁⟩⟩

/-- Distinct-point version of the ordered leaf-pair union bound. -/
theorem card_admissibleLeafEmbeddingsContainingPair_le_sum_J01_distinct
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ z₁ : Fin 4 → ℤ) (hne : z₀ ≠ z₁) :
    (admissibleLeafEmbeddingsContainingPair N hN z₀ z₁).card ≤
      ∑ f ∈ distinctLeafPairs t, J01 N hN f.1 f.2 z₀ z₁ := by
  rw [admissibleLeafEmbeddingsContainingPair_eq_biUnion_distinctAnchored
    N hN z₀ z₁ hne]
  simpa [J01] using
    (Finset.card_biUnion_le :
      ((distinctLeafPairs t).biUnion fun f =>
        doublyAnchoredLeafEmbeddings N hN f.1 f.2 z₀ z₁).card ≤
      ∑ f ∈ distinctLeafPairs t,
        (doublyAnchoredLeafEmbeddings N hN f.1 f.2 z₀ z₁).card)

/-- Full two-anchor Step 2 reduction with diagonal leaf pairs removed when
the prescribed points are distinct. -/
theorem card_autHeppMarked_mul_card_realizedSetsContainingPair_le_sum_J01_distinct
    {t : PlaneTree} {M : ℕ}
    (N : BranchExponentData t (4 * M)) (hN : N.IsValid)
    (z₀ z₁ : Fin 4 → ℤ) (hne : z₀ ≠ z₁) :
    Fintype.card (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContainingPair N hN z₀ z₁).card
      ≤ ∑ f ∈ distinctLeafPairs t, J01 N hN f.1 f.2 z₀ z₁ :=
  (card_autHeppMarked_mul_card_realizedSetsContainingPair_le
      N hN z₀ z₁).trans
    (card_admissibleLeafEmbeddingsContainingPair_le_sum_J01_distinct
      N hN z₀ z₁ hne)

end Anderson4D
