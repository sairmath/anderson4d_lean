import Anderson4D.Combinatorics.PairingBlockEquiv
import Anderson4D.DetParametrix.Paper42_Moment.R324CompleteBlockFactorization

/-!
# Exact primitive-pairing sums on one R-324 block

This file specializes `PartialPairing.closedOnEquiv` to an increasingly
enumerated even block.  Pairings whose restriction to the block is
primitive are exactly:

* one member of the paper's `primitiveFullPairings q`, and
* an arbitrary pairing on the complementary carrier.

Thus a sum over ambient pairings can be reindexed as the primitive pairing
sum first, with no multiplicity and no termwise cardinality loss.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Increasingly reindex the restriction of a pairing carrying only a
closure certificate on `B`. -/
def orderedClosedBlockPairing
    {n k : ℕ} (B : Finset (Fin n))
    (e : Fin k ≃o B)
    (κ : PartialPairing.ClosedOn B) :
    PartialPairing (Fin k) :=
  PartialPairing.congr e.symm.toEquiv
    (PartialPairing.restrictTo κ.1 κ.2)

/-- Exact decomposition with the block restriction already transported to
its standard increasing `Fin k` carrier. -/
def closedOnOrderedEquiv
    {n k : ℕ} (B : Finset (Fin n))
    (e : Fin k ≃o B) :
    PartialPairing.ClosedOn B ≃
      PartialPairing (Fin k) ×
        PartialPairing {i : Fin n // i ∉ B} :=
  (PartialPairing.closedOnEquiv B).trans
    ((PartialPairing.congr e.symm.toEquiv).prodCongr
      (Equiv.refl _))

@[simp]
theorem closedOnOrderedEquiv_apply_fst
    {n k : ℕ} (B : Finset (Fin n))
    (e : Fin k ≃o B)
    (κ : PartialPairing.ClosedOn B) :
    (closedOnOrderedEquiv B e κ).1 =
      orderedClosedBlockPairing B e κ :=
  rfl

@[simp]
theorem closedOnOrderedEquiv_apply_snd
    {n k : ℕ} (B : Finset (Fin n))
    (e : Fin k ≃o B)
    (κ : PartialPairing.ClosedOn B) :
    (closedOnOrderedEquiv B e κ).2 =
      PartialPairing.restrictCompl κ.1 κ.2 :=
  rfl

/-- Pulling a predicate on the first component out of a product subtype. -/
def subtypeProdFstEquiv
    {α β : Type*} (p : α → Prop) :
    {x : α × β // p x.1} ≃
      {a : α // p a} × β where
  toFun x := (⟨x.1.1, x.2⟩, x.1.2)
  invFun x := ⟨(x.1.1, x.2), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pulling a predicate on the second component out of a product subtype. -/
def subtypeProdSndEquiv
    {α β : Type*} (p : β → Prop) :
    {x : α × β // p x.2} ≃
      α × {b : β // p b} where
  toFun x := (x.1.1, ⟨x.1.2, x.2⟩)
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Ambient pairings preserving `B` and primitive on the increasingly
reindexed block. -/
abbrev PrimitiveClosedOn
    {n : ℕ} (q : ℕ) (B : Finset (Fin n))
    (e : Fin (2 * q) ≃o B) :=
  {κ : PartialPairing.ClosedOn B //
    orderedClosedBlockPairing B e κ ∈
      primitiveFullPairings q}

/-- A primitive closed ambient pairing is exactly a primitive standard
block pairing together with an arbitrary complementary pairing. -/
def primitiveClosedOnEquiv
    {n : ℕ} (q : ℕ) (B : Finset (Fin n))
    (e : Fin (2 * q) ≃o B) :
    PrimitiveClosedOn q B e ≃
      {κ : PartialPairing (Fin (2 * q)) //
        κ ∈ primitiveFullPairings q} ×
      PartialPairing {i : Fin n // i ∉ B} :=
  ((closedOnOrderedEquiv B e).subtypeEquiv fun κ => by
      exact Iff.rfl).trans
    (subtypeProdFstEquiv fun κ =>
      κ ∈ primitiveFullPairings q)

@[simp]
theorem primitiveClosedOnEquiv_apply_snd
    {n : ℕ} (q : ℕ) (B : Finset (Fin n))
    (e : Fin (2 * q) ≃o B)
    (κ : PrimitiveClosedOn q B e) :
    (primitiveClosedOnEquiv q B e κ).2 =
      PartialPairing.restrictCompl κ.1.1 κ.1.2 :=
  rfl

/-- Membership in `PrimitiveClosedOn` supplies the concrete
`IsFullyPairedOn` certificate on the ambient sparse block. -/
theorem PrimitiveClosedOn.isFullyPairedOn
    {n : ℕ} {q : ℕ} {B : Finset (Fin n)}
    {e : Fin (2 * q) ≃o B}
    (κ : PrimitiveClosedOn q B e) :
    IsFullyPairedOn κ.1.1 B := by
  have hordered :
      (orderedClosedBlockPairing B e κ.1).IsFull :=
    (mem_primitiveFullPairings.mp κ.2).1
  have hrestricted :
      (PartialPairing.restrictTo κ.1.1 κ.1.2).IsFull := by
    intro i hfix
    apply hordered (e.symm i)
    change
      e.symm
          ((PartialPairing.restrictTo κ.1.1 κ.1.2)
            (e (e.symm i))) =
        e.symm i
    rw [e.apply_symm_apply, hfix]
  constructor
  · intro i hi hfix
    exact hrestricted ⟨i, hi⟩
      (Subtype.ext hfix)
  · exact κ.1.2

/-- Standard primitivity of the increasingly transported block pairing
pulls back to relative primitivity on the ambient sparse block. -/
theorem PrimitiveClosedOn.isRelPrimitiveOn
    {n : ℕ} {q : ℕ} {B : Finset (Fin n)}
    {e : Fin (2 * q) ≃o B}
    (κ : PrimitiveClosedOn q B e) :
    IsRelPrimitiveOn κ.1.1 B := by
  have hprimitive :
      IsPrimitive (orderedClosedBlockPairing B e κ.1) :=
    (mem_primitiveFullPairings.mp κ.2).2
  have horderedApply (i : Fin (2 * q)) :
      (e (orderedClosedBlockPairing B e κ.1 i)).1 =
        κ.1.1 (e i).1 := by
    change
      (e (e.symm
        (PartialPairing.restrictTo κ.1.1 κ.1.2
          (e i)))).1 =
        κ.1.1 (e i).1
    rw [e.apply_symm_apply]
    rfl
  intro a b hab
  let aB : B := ⟨a, hab.left_mem⟩
  let bB : B := ⟨b, hab.right_mem⟩
  let ia : Fin (2 * q) := e.symm aB
  let ib : Fin (2 * q) := e.symm bB
  have hea : e ia = aB := e.apply_symm_apply aB
  have heb : e ib = bB := e.apply_symm_apply bB
  have heaVal : (e ia).1 = a :=
    congrArg Subtype.val hea
  have hebVal : (e ib).1 = b :=
    congrArg Subtype.val heb
  have hiab : ia ≤ ib := by
    apply e.le_iff_le.mp
    change (e ia).1 ≤ (e ib).1
    rw [heaVal, hebVal]
    exact hab.le
  have hfullIcc :
      IsFullyPairedOn
        (orderedClosedBlockPairing B e κ.1)
        (Finset.Icc ia ib) := by
    constructor
    · intro i hi hfix
      have heiRel :
          (e i).1 ∈ relIcc B a b := by
        rw [mem_relIcc]
        refine ⟨(e i).2, ?_, ?_⟩
        · have hii := (Finset.mem_Icc.mp hi).1
          have := e.le_iff_le.mpr hii
          change (e ia).1 ≤ (e i).1 at this
          simpa only [heaVal] using this
        · have hii := (Finset.mem_Icc.mp hi).2
          have := e.le_iff_le.mpr hii
          change (e i).1 ≤ (e ib).1 at this
          simpa only [hebVal] using this
      apply hab.isFullyPairedOn.ne_of_mem heiRel
      rw [← horderedApply i, hfix]
    · intro i hi
      rw [Finset.mem_Icc] at hi ⊢
      have heiRel :
          (e i).1 ∈ relIcc B a b := by
        rw [mem_relIcc]
        refine ⟨(e i).2, ?_, ?_⟩
        · have := e.le_iff_le.mpr hi.1
          change (e ia).1 ≤ (e i).1 at this
          simpa only [heaVal] using this
        · have := e.le_iff_le.mpr hi.2
          change (e i).1 ≤ (e ib).1 at this
          simpa only [hebVal] using this
      have hmove :=
        hab.isFullyPairedOn.apply_mem heiRel
      constructor
      · apply e.le_iff_le.mp
        change (e ia).1 ≤
          (e (orderedClosedBlockPairing B e κ.1 i)).1
        rw [heaVal, horderedApply]
        exact (mem_relIcc.mp hmove).2.1
      · apply e.le_iff_le.mp
        change
          (e (orderedClosedBlockPairing B e κ.1 i)).1 ≤
            (e ib).1
        rw [horderedApply, hebVal]
        exact (mem_relIcc.mp hmove).2.2
  have hwhole :
      Finset.Icc ia ib = Finset.univ :=
    hprimitive ia ib hiab hfullIcc
  apply Finset.Subset.antisymm
  · exact relIcc_subset_active B a b
  · intro x hxB
    let xb : B := ⟨x, hxB⟩
    let i : Fin (2 * q) := e.symm xb
    have hei : e i = xb := e.apply_symm_apply xb
    have heiVal : (e i).1 = x :=
      congrArg Subtype.val hei
    have hi : i ∈ Finset.Icc ia ib := by
      rw [hwhole]
      exact Finset.mem_univ i
    rw [mem_relIcc]
    refine ⟨hxB, ?_, ?_⟩
    · have hle := e.le_iff_le.mpr (Finset.mem_Icc.mp hi).1
      change (e ia).1 ≤ (e i).1 at hle
      simpa only [heaVal, heiVal] using hle
    · have hle := e.le_iff_le.mpr (Finset.mem_Icc.mp hi).2
      change (e i).1 ≤ (e ib).1 at hle
      simpa only [hebVal, heiVal] using hle

/-- The canonical closed primitive-block element cut out of an ambient
pairing.  Its first component is definitionally the standard residual
primitive pairing used by the R-324 block decomposition. -/
def primitiveClosedOnOfFullyPairedPrimitive
    {n : ℕ} (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B)
    (hprim : IsRelPrimitiveOn κ B) :
    PrimitiveClosedOn (residualBlockOrder B) B
      (residualPrimitiveBlockOrderIso κ B hB) :=
  ⟨⟨κ, hB.2⟩,
    residualPrimitiveBlockPairing_mem κ B hB hprim⟩

@[simp]
theorem primitiveClosedOnOfFullyPairedPrimitive_val
    {n : ℕ} (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B)
    (hprim : IsRelPrimitiveOn κ B) :
    (primitiveClosedOnOfFullyPairedPrimitive
      κ B hB hprim).1.1 = κ :=
  rfl

@[simp]
theorem primitiveClosedOnEquiv_canonical_fst
    {n : ℕ} (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) (hB : IsFullyPairedOn κ B)
    (hprim : IsRelPrimitiveOn κ B) :
    (primitiveClosedOnEquiv (residualBlockOrder B) B
      (residualPrimitiveBlockOrderIso κ B hB)
      (primitiveClosedOnOfFullyPairedPrimitive
        κ B hB hprim)).1.1 =
      residualPrimitiveBlockPairing κ B hB :=
  rfl

/-- For a primitive closed block, fullness of the ambient pairing is
equivalent to fullness of the complementary restriction.  Fullness on the
block itself is already supplied by primitive-pairing membership. -/
theorem PrimitiveClosedOn.isFull_iff_complement
    {n : ℕ} {q : ℕ} {B : Finset (Fin n)}
    {e : Fin (2 * q) ≃o B}
    (κ : PrimitiveClosedOn q B e) :
    κ.1.1.IsFull ↔
      ((primitiveClosedOnEquiv q B e κ).2).IsFull := by
  constructor
  · intro hfull
    exact PartialPairing.restrictCompl_isFull
      κ.1.1 B κ.1.2 hfull
  · intro hcompl i hfix
    by_cases hi : i ∈ B
    · exact κ.isFullyPairedOn.ne_of_mem hi hfix
    · apply hcompl ⟨i, hi⟩
      apply Subtype.ext
      exact hfix

/-- Full ambient pairings primitive on `B` are exactly a primitive pairing
on the standard block together with a full pairing on the complement. -/
def fullPrimitiveClosedOnEquiv
    {n : ℕ} (q : ℕ) (B : Finset (Fin n))
    (e : Fin (2 * q) ≃o B) :
    {κ : PrimitiveClosedOn q B e // κ.1.1.IsFull} ≃
      {κ : PartialPairing (Fin (2 * q)) //
        κ ∈ primitiveFullPairings q} ×
      {κ : PartialPairing {i : Fin n // i ∉ B} //
        κ.IsFull} :=
  ((primitiveClosedOnEquiv q B e).subtypeEquiv fun κ =>
      PrimitiveClosedOn.isFull_iff_complement κ).trans
    (subtypeProdSndEquiv fun
      κ : PartialPairing {i : Fin n // i ∉ B} =>
        κ.IsFull)

/-- Exact finite-sum reindexing for full pairings primitive on one block.
This is the form used by successive R-324 block replacement: after summing
the whole primitive block fiber, the remaining index is again a full
pairing on the complementary carrier. -/
theorem sum_fullPrimitiveClosedOn_eq_sum_block_complement
    {n : ℕ} (q : ℕ) (B : Finset (Fin n))
    (e : Fin (2 * q) ≃o B)
    {M : Type*} [AddCommMonoid M]
    (F : {κ : PrimitiveClosedOn q B e // κ.1.1.IsFull} → M) :
    (∑ κ : {κ : PrimitiveClosedOn q B e // κ.1.1.IsFull}, F κ) =
      ∑ κB :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q},
        ∑ κC :
            {κ : PartialPairing {i : Fin n // i ∉ B} //
              κ.IsFull},
          F ((fullPrimitiveClosedOnEquiv q B e).symm
            (κB, κC)) := by
  calc
    (∑ κ : {κ : PrimitiveClosedOn q B e // κ.1.1.IsFull}, F κ) =
        ∑ p :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q} ×
          {κ : PartialPairing {i : Fin n // i ∉ B} //
            κ.IsFull},
          F ((fullPrimitiveClosedOnEquiv q B e).symm p) :=
      ((fullPrimitiveClosedOnEquiv q B e).symm.sum_comp F).symm
    _ = ∑ κB :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q},
        ∑ κC :
            {κ : PartialPairing {i : Fin n // i ∉ B} //
              κ.IsFull},
          F ((fullPrimitiveClosedOnEquiv q B e).symm
            (κB, κC)) := by
      rw [Fintype.sum_prod_type]

/-- If a predicate on primitive closed pairings depends only on the
complementary coordinate, its fiber is exactly the full primitive block
coordinate times one complementary fiber.  This packages the recursive
fixed-signature factorization used by R-324. -/
def primitiveClosedOnFiberEquiv
    {n : ℕ} (q : ℕ) (B : Finset (Fin n))
    (e : Fin (2 * q) ≃o B)
    (κB₀ :
      {κ : PartialPairing (Fin (2 * q)) //
        κ ∈ primitiveFullPairings q})
    (P : PrimitiveClosedOn q B e → Prop)
    (hinvariant :
      ∀ (κB κB' :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q})
        (κC : PartialPairing {i : Fin n // i ∉ B}),
        P ((primitiveClosedOnEquiv q B e).symm
            (κB, κC)) ↔
          P ((primitiveClosedOnEquiv q B e).symm
            (κB', κC))) :
    {κ : PrimitiveClosedOn q B e // P κ} ≃
      {κ : PartialPairing (Fin (2 * q)) //
        κ ∈ primitiveFullPairings q} ×
      {κC : PartialPairing {i : Fin n // i ∉ B} //
        P ((primitiveClosedOnEquiv q B e).symm
          (κB₀, κC))} :=
  ((primitiveClosedOnEquiv q B e).subtypeEquiv fun κ => by
      change
        P κ ↔
          P ((primitiveClosedOnEquiv q B e).symm
            (primitiveClosedOnEquiv q B e κ))
      rw [Equiv.symm_apply_apply]).trans
    (((Equiv.refl
      ({κ : PartialPairing (Fin (2 * q)) //
          κ ∈ primitiveFullPairings q} ×
        PartialPairing {i : Fin n // i ∉ B})).subtypeEquiv
      fun x => hinvariant x.1 κB₀ x.2).trans
        (subtypeProdSndEquiv fun κC =>
          P ((primitiveClosedOnEquiv q B e).symm
            (κB₀, κC))))

/-- Exact finite-sum factorization attached to
`primitiveClosedOnFiberEquiv`. -/
theorem sum_primitiveClosedOnFiber_eq_sum_block_complement
    {n : ℕ} (q : ℕ) (B : Finset (Fin n))
    (e : Fin (2 * q) ≃o B)
    (κB₀ :
      {κ : PartialPairing (Fin (2 * q)) //
        κ ∈ primitiveFullPairings q})
    (P : PrimitiveClosedOn q B e → Prop)
    [DecidablePred P]
    (hinvariant :
      ∀ (κB κB' :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q})
        (κC : PartialPairing {i : Fin n // i ∉ B}),
        P ((primitiveClosedOnEquiv q B e).symm
            (κB, κC)) ↔
          P ((primitiveClosedOnEquiv q B e).symm
            (κB', κC)))
    {M : Type*} [AddCommMonoid M]
    (F : {κ : PrimitiveClosedOn q B e // P κ} → M) :
    (∑ κ : {κ : PrimitiveClosedOn q B e // P κ}, F κ) =
      ∑ κB :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q},
        ∑ κC :
            {κC : PartialPairing {i : Fin n // i ∉ B} //
              P ((primitiveClosedOnEquiv q B e).symm
                (κB₀, κC))},
          F ((primitiveClosedOnFiberEquiv
            q B e κB₀ P hinvariant).symm
              (κB, κC)) := by
  let E := primitiveClosedOnFiberEquiv
    q B e κB₀ P hinvariant
  calc
    (∑ κ : {κ : PrimitiveClosedOn q B e // P κ}, F κ) =
        ∑ x :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q} ×
          {κC : PartialPairing {i : Fin n // i ∉ B} //
            P ((primitiveClosedOnEquiv q B e).symm
              (κB₀, κC))},
          F (E.symm x) :=
      (E.symm.sum_comp F).symm
    _ = ∑ κB :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q},
        ∑ κC :
            {κC : PartialPairing {i : Fin n // i ∉ B} //
              P ((primitiveClosedOnEquiv q B e).symm
                (κB₀, κC))},
          F (E.symm (κB, κC)) := by
      rw [Fintype.sum_prod_type]

/-! ## Canonical elements supplied by the three R-324 block families -/

/-- A within-left extraction block, viewed in the full primitive-closed
pairing type on the doubled carrier. -/
def momentLeftExtractionFullPrimitiveClosedOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentLeftExtractionBlocks κp) :
    {κ : PrimitiveClosedOn (residualBlockOrder B) B
        (residualPrimitiveBlockOrderIso
          (momentCombinedPairing κp κm π) B
          (momentLeftExtractionBlock_isFullyPairedOn_of_mem
            κp κm π B hB)) //
      κ.1.1.IsFull} :=
  ⟨primitiveClosedOnOfFullyPairedPrimitive
      (momentCombinedPairing κp κm π) B
      (momentLeftExtractionBlock_isFullyPairedOn_of_mem
        κp κm π B hB)
      (momentLeftExtractionBlock_isRelPrimitiveOn_of_mem
        κp κm π B hB),
    momentCombinedPairing_isFull κp κm π⟩

/-- A within-right extraction block, viewed in the full primitive-closed
pairing type on the doubled carrier. -/
def momentRightExtractionFullPrimitiveClosedOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentRightExtractionBlocks κm) :
    {κ : PrimitiveClosedOn (residualBlockOrder B) B
        (residualPrimitiveBlockOrderIso
          (momentCombinedPairing κp κm π) B
          (momentRightExtractionBlock_isFullyPairedOn_of_mem
            κp κm π B hB)) //
      κ.1.1.IsFull} :=
  ⟨primitiveClosedOnOfFullyPairedPrimitive
      (momentCombinedPairing κp κm π) B
      (momentRightExtractionBlock_isFullyPairedOn_of_mem
        κp κm π B hB)
      (momentRightExtractionBlock_isRelPrimitiveOn_of_mem
        κp κm π B hB),
    momentCombinedPairing_isFull κp κm π⟩

/-- A residual collapse block, viewed in the full primitive-closed pairing
type on the doubled carrier. -/
def momentResidualCollapseFullPrimitiveClosedOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentResidualCollapseBlocks κp κm π) :
    {κ : PrimitiveClosedOn (residualBlockOrder B) B
        (residualPrimitiveBlockOrderIso
          (momentCombinedPairing κp κm π) B
          (momentResidualCollapseBlock_isFullyPairedOn_of_mem
            κp κm π B hB)) //
      κ.1.1.IsFull} :=
  ⟨primitiveClosedOnOfFullyPairedPrimitive
      (momentCombinedPairing κp κm π) B
      (momentResidualCollapseBlock_isFullyPairedOn_of_mem
        κp κm π B hB)
      (momentResidualCollapseBlock_isRelPrimitiveOn_of_mem
        κp κm π B hB),
    momentCombinedPairing_isFull κp κm π⟩

@[simp]
theorem momentLeftExtractionFullPrimitiveClosedOn_val
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentLeftExtractionBlocks κp) :
    (momentLeftExtractionFullPrimitiveClosedOn
      κp κm π B hB).1.1.1 =
      momentCombinedPairing κp κm π :=
  rfl

@[simp]
theorem momentRightExtractionFullPrimitiveClosedOn_val
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentRightExtractionBlocks κm) :
    (momentRightExtractionFullPrimitiveClosedOn
      κp κm π B hB).1.1.1 =
      momentCombinedPairing κp κm π :=
  rfl

@[simp]
theorem momentResidualCollapseFullPrimitiveClosedOn_val
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ momentResidualCollapseBlocks κp κm π) :
    (momentResidualCollapseFullPrimitiveClosedOn
      κp κm π B hB).1.1.1 =
      momentCombinedPairing κp κm π :=
  rfl

/-- The ambient covariance factor on a primitive closed block is exactly
the standard primitive covariance product of the first component exposed by
`primitiveClosedOnEquiv`. -/
theorem pairingCovarianceProductOn_eq_orderedClosedBlock
    {n : ℕ} {q : ℕ} {B : Finset (Fin n)}
    {e : Fin (2 * q) ≃o B}
    (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PrimitiveClosedOn q B e)
    (v : Fin n → T4) :
    pairingCovarianceProductOn ρ ε κ.1.1 B v =
      primitiveCovarianceProduct ρ ε q
        (orderedClosedBlockPairing B e κ.1)
        (fun i => v (e i).1) := by
  let κB := orderedClosedBlockPairing B e κ.1
  have hfull : κB.IsFull :=
    (mem_primitiveFullPairings.mp κ.2).1
  have hκB_apply (i : Fin (2 * q)) :
      (e (κB i)).1 = κ.1.1 (e i).1 := by
    change
      (e (e.symm
        (PartialPairing.restrictTo κ.1.1 κ.1.2
          (e i)))).1 =
        κ.1.1 (e i).1
    rw [e.apply_symm_apply]
    rfl
  unfold pairingCovarianceProductOn primitiveCovarianceProduct
  have hsource :
      κB.pairSupport.filter (fun i => i < κB i) =
        Finset.univ.filter (fun i => i < κB i) := by
    rw [PartialPairing.isFull_iff_pairSupport_eq_univ.mp hfull]
  rw [hsource]
  symm
  apply Finset.prod_bij
      (fun i _hi => (e i).1)
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨(e i).2, ?_⟩
    rw [← hκB_apply i]
    exact e.lt_iff_lt.mpr hi.2
  · intro i₁ _hi₁ i₂ _hi₂ hii
    exact e.injective (Subtype.ext hii)
  · intro b hb
    rw [Finset.mem_filter] at hb
    let bB : B := ⟨b, hb.1⟩
    let i : Fin (2 * q) := e.symm bB
    have hei : e i = bB := e.apply_symm_apply bB
    refine ⟨i, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      apply e.lt_iff_lt.mp
      change (e i).1 < (e (κB i)).1
      rw [hκB_apply, hei]
      exact hb.2
    · exact congrArg Subtype.val hei
  · intro i _hi
    congr 2
    change v (e (κB i)).1 =
      v (κ.1.1 (e i).1)
    rw [hκB_apply]

/-- Exact finite-sum reindexing which exposes the complete primitive
pairing sum on the block before the complement sum. -/
theorem sum_primitiveClosedOn_eq_sum_block_complement
    {n : ℕ} (q : ℕ) (B : Finset (Fin n))
    (e : Fin (2 * q) ≃o B)
    {M : Type*} [AddCommMonoid M]
    (F : PrimitiveClosedOn q B e → M) :
    (∑ κ : PrimitiveClosedOn q B e, F κ) =
      ∑ κB :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q},
        ∑ κC : PartialPairing {i : Fin n // i ∉ B},
          F ((primitiveClosedOnEquiv q B e).symm
            (κB, κC)) := by
  calc
    (∑ κ : PrimitiveClosedOn q B e, F κ) =
        ∑ p :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q} ×
              PartialPairing {i : Fin n // i ∉ B},
          F ((primitiveClosedOnEquiv q B e).symm p) :=
      ((primitiveClosedOnEquiv q B e).symm.sum_comp F).symm
    _ = ∑ κB :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q},
        ∑ κC : PartialPairing {i : Fin n // i ∉ B},
          F ((primitiveClosedOnEquiv q B e).symm
            (κB, κC)) := by
      rw [Fintype.sum_prod_type]

/-- If the summand separates into a block factor and a complement factor,
the complete primitive block sum factors exactly as a product of sums. -/
theorem sum_primitiveClosedOn_mul_factors
    {n : ℕ} (q : ℕ) (B : Finset (Fin n))
    (e : Fin (2 * q) ≃o B)
    {R : Type*} [CommSemiring R]
    (fB :
      {κ : PartialPairing (Fin (2 * q)) //
        κ ∈ primitiveFullPairings q} → R)
    (fC : PartialPairing {i : Fin n // i ∉ B} → R) :
    (∑ κ : PrimitiveClosedOn q B e,
        fB ((primitiveClosedOnEquiv q B e κ).1) *
          fC ((primitiveClosedOnEquiv q B e κ).2)) =
      (∑ κB, fB κB) * ∑ κC, fC κC := by
  let E := primitiveClosedOnEquiv q B e
  calc
    (∑ κ : PrimitiveClosedOn q B e,
        fB (E κ).1 * fC (E κ).2) =
      ∑ p :
          {κ : PartialPairing (Fin (2 * q)) //
            κ ∈ primitiveFullPairings q} ×
              PartialPairing {i : Fin n // i ∉ B},
        fB p.1 * fC p.2 := by
      exact E.sum_comp (fun p => fB p.1 * fC p.2)
    _ = ∑ κB,
          ∑ κC, fB κB * fC κC := by
      rw [Fintype.sum_prod_type]
    _ = (∑ κB, fB κB) * ∑ κC, fC κC := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro κB _hκB
      rw [Finset.mul_sum]

end

end Anderson4D
