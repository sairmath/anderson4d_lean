import Anderson4D.Continuum.PrimitiveFiberReindex
import Anderson4D.Continuum.OpenEdgeDiscretization
import Anderson4D.PermSum.OpenEdgeRawCountFiber

/-!
# Reindexing an open cell word by its occupied labels

An R-324 cell word has values in the infinite lattice `Z4`; it is never
appropriate to demand surjectivity onto that lattice.  Instead, one first
fixes its finite support and regards the word as taking values in the
subtype of labels that actually occur.  An admissible Hepp realization
identifies that finite support with the leaves of its tree.

This file proves that the resulting leaf word is surjective and transports
raw occurrence counts, selected endpoint labels, the unmarked pairing
constraint, and the adjacent-chain weight.  It is the exact bridge from
the physical cell decomposition to `OpenEdgeRawCountFiber`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open PlaneTree

/-! ## Surjectivity onto the occupied finite support -/

/-- A tuple word is tautologically surjective onto its own support. -/
theorem tupleWord_surjective
    {m : ℕ} (y : Fin m → Z4) :
    Function.Surjective (tupleWord y) := by
  intro x
  obtain ⟨i, hi⟩ := mem_tupleSupport.mp x.2
  refine ⟨i, Subtype.ext ?_⟩
  exact hi

/-- Transporting the tuple word along any leaf/support equivalence gives
a surjective leaf word. -/
theorem reindex_tupleWord_surjective
    {t : PlaneTree} {m : ℕ} (y : Fin m → Z4)
    (e : HeppLeaf t ≃ {x // x ∈ tupleSupport y}) :
    Function.Surjective
      (reindexSupportWord e (tupleWord y)) := by
  intro l
  obtain ⟨i, hi⟩ := tupleWord_surjective y (e l)
  refine ⟨i, ?_⟩
  unfold reindexSupportWord
  rw [hi, e.symm_apply_apply]

/-- Reindex a tuple whose support has been identified with a fixed finite
set `Z`. -/
def reindexTupleWordAt
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    {y : Fin m → Z4} (hZ : tupleSupport y = Z) :
    Fin m → HeppLeaf t :=
  reindexSupportWord e (tupleWordAt hZ)

/-- A word reindexed over exactly its occupied fixed support is
surjective onto the Hepp leaves. -/
theorem reindexTupleWordAt_surjective
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    {y : Fin m → Z4} (hZ : tupleSupport y = Z) :
    Function.Surjective (reindexTupleWordAt e hZ) := by
  intro l
  have hel : (e l).1 ∈ tupleSupport y := by
    rw [hZ]
    exact (e l).2
  obtain ⟨i, hi⟩ := mem_tupleSupport.mp hel
  refine ⟨i, ?_⟩
  unfold reindexTupleWordAt reindexSupportWord
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact hi

/-! ## Exact transport of labels and counts -/

/-- Forgetting the leaf reindexing recovers the original lattice label. -/
theorem reindexTupleWordAt_embedding_apply
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    {y : Fin m → Z4} (hZ : tupleSupport y = Z)
    (i : Fin m) :
    (e (reindexTupleWordAt e hZ i)).1 = y i := by
  unfold reindexTupleWordAt reindexSupportWord
  rw [e.apply_symm_apply]
  rfl

/-- Occurrence counts after leaf reindexing are exactly the original
lattice-label counts. -/
theorem wordFiberCount_reindexTupleWordAt
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    {y : Fin m → Z4} (hZ : tupleSupport y = Z)
    (l : HeppLeaf t) :
    wordFiberCount (reindexTupleWordAt e hZ) l =
      wordFiberCount y (e l).1 := by
  unfold wordFiberCount
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    have h := congrArg (fun q => (e q).1) hi
    simpa only [reindexTupleWordAt_embedding_apply] using h
  · intro hi
    apply e.injective
    apply Subtype.ext
    rw [reindexTupleWordAt_embedding_apply]
    exact hi

/-- Equality of raw counts on the occupied support transports to equality
of leaf-word raw profiles. -/
theorem wordFiberCount_reindexTupleWordAt_eq
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    {reference w : Fin m → Z4}
    (hrefZ : tupleSupport reference = Z)
    (hwZ : tupleSupport w = Z)
    (hcount :
      ∀ x : {x // x ∈ Z},
        wordFiberCount w x.1 =
          wordFiberCount reference x.1) :
    ∀ l : HeppLeaf t,
      wordFiberCount (reindexTupleWordAt e hwZ) l =
        wordFiberCount
          (reindexTupleWordAt e hrefZ) l := by
  intro l
  rw [wordFiberCount_reindexTupleWordAt,
    wordFiberCount_reindexTupleWordAt]
  exact hcount (e l)

/-- Equality at one physical endpoint transports to equality of the
corresponding leaf labels. -/
theorem reindexTupleWordAt_apply_eq_of_apply_eq
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    {reference w : Fin m → Z4}
    (hrefZ : tupleSupport reference = Z)
    (hwZ : tupleSupport w = Z)
    (i : Fin m) (hi : w i = reference i) :
    reindexTupleWordAt e hwZ i =
      reindexTupleWordAt e hrefZ i := by
  apply e.injective
  apply Subtype.ext
  rw [reindexTupleWordAt_embedding_apply,
    reindexTupleWordAt_embedding_apply]
  exact hi

/-! ## Pairing and raw-fibre transport -/

/-- The equality on every unmarked physical pairing edge survives the
occupied-label leaf reindexing. -/
theorem reindexTupleWordAt_respectsExcept
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    (κ : PartialPairing (Fin m))
    (a b : Fin m)
    {y : Fin m → Z4} (hZ : tupleSupport y = Z)
    (hy : RespectsPairingExcept κ a b y) :
    ∀ i : Fin m, i ≠ a → i ≠ b →
      reindexTupleWordAt e hZ i =
        reindexTupleWordAt e hZ (κ i) := by
  intro i hia hib
  apply e.injective
  apply Subtype.ext
  rw [reindexTupleWordAt_embedding_apply,
    reindexTupleWordAt_embedding_apply]
  exact (hy i hia hib).symm

/-- A physical word with the same occupied support, raw profile, and
selected endpoint labels as a reference maps into the exact raw-count
leaf fibre used by Proposition 5.7. -/
theorem reindexTupleWordAt_mem_openEdgeRawCountFixedEndpointFiber
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    (κ : PartialPairing (Fin m))
    (a b : Fin m)
    (reference w : Fin m → Z4)
    (hrefZ : tupleSupport reference = Z)
    (hwZ : tupleSupport w = Z)
    (hcount :
      ∀ x : {x // x ∈ Z},
        wordFiberCount w x.1 =
          wordFiberCount reference x.1)
    (ha : w a = reference a)
    (hb : w b = reference b)
    (hwRespect : RespectsPairingExcept κ a b w) :
    reindexTupleWordAt e hwZ ∈
      openEdgeRawCountFixedEndpointFiber
        κ a b (reindexTupleWordAt e hrefZ) := by
  rw [mem_openEdgeRawCountFixedEndpointFiber]
  refine
    ⟨wordFiberCount_reindexTupleWordAt_eq
        e hrefZ hwZ hcount,
      reindexTupleWordAt_apply_eq_of_apply_eq
        e hrefZ hwZ a ha,
      reindexTupleWordAt_apply_eq_of_apply_eq
        e hrefZ hwZ b hb,
      ?_⟩
  exact reindexTupleWordAt_respectsExcept
    e κ a b hwZ hwRespect

/-! ## Adjacent-chain weight -/

/-- The support chain weight is exactly the Hepp chain weight after
occupied-label reindexing. -/
theorem supportChainWeight_tupleWordAt_eq_heppChainWeight
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    {y : Fin m → Z4} (hZ : tupleSupport y = Z) :
    supportChainWeight (tupleWordAt hZ) =
      heppChainWeight
        (fun l : HeppLeaf t => (e l).1)
        (reindexTupleWordAt e hZ) := by
  exact
    supportChainWeight_eq_heppChainWeight_reindex
      e (tupleWordAt hZ)
      (fun l : HeppLeaf t => (e l).1)
      (fun _ => rfl)

end

end Anderson4D
