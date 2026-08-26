import Anderson4D.DetParametrix.Paper41_Renorm.R322BlockIntegrand

/-!
# Canonical ambient tails of an R-322 extraction fibre

`ExtractionComplementFiberAt` is naturally a pairing on the complement
subtype.  That representation is ideal for a single block split, but awkward
for iteration because the next reduction step is formulated on the original
ordered ambient carrier.  This file gives the exact missing bridge:

* the complementary coordinate is equivalent to an ambient extraction-fibre
  member whose current block has been reset to the reference primitive
  coordinate;
* every extraction-fibre member has the fixed tail extraction after deleting
  the selected block;
* the one-step block equivalence can therefore return an ambient canonical
  tail, ready for the next active carrier.

No quotient and no multiplicity factor is introduced.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## Tail extraction on the original ambient carrier -/

/-- Equality of the complete nonempty extraction lists implies equality of
their tails on the carrier left after the common first block is removed. -/
theorem extractionFiber_tail_extractAux_eq
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (τ : ExtractionFiberAt κ fuel active) :
    extractAux τ.1 fuel
        (active \ selectedExtractionBlock κ active h) =
      extractAux κ fuel
        (active \ selectedExtractionBlock κ active h) := by
  let κ' : PartialPairing (Fin m) := τ.1
  have hextract :
      extractAux κ' (fuel + 1) active =
        extractAux κ (fuel + 1) active :=
    τ.2
  have hτ :
      ∃ a b, IsRelFullyPaired κ' active a b :=
    exists_candidate_of_extractAux_eq
      fuel active h hextract
  have hblock :
      selectedExtractionBlock κ' active hτ =
        selectedExtractionBlock κ active h :=
    selectedExtractionBlock_eq_of_extractAux_eq
      fuel active h hτ hextract
  have htails := hextract
  rw [extractAux_succ_pos fuel hτ,
    extractAux_succ_pos fuel h] at htails
  have htail :
      extractAux κ' fuel
          (active \
            selectedExtractionBlock κ' active hτ) =
        extractAux κ fuel
          (active \
            selectedExtractionBlock κ active h) := by
    exact (List.cons.inj htails).2
  simpa only [κ', hblock] using htail

/-! ## Canonical ambient representatives of complementary coordinates -/

/-- Ambient members of the current extraction fibre whose exposed first
primitive coordinate is the reference coordinate.  Their remaining pairing
is precisely the recursive tail data. -/
abbrev CanonicalExtractionTailAt
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b) :=
  {τ : ExtractionFiberAt κ fuel active //
    (extractionFiberEquivBlockComplement
      κ fuel active h τ).1 =
        selectedExtractionPrimitivePairing κ active h}

/-- The complement-subtype coordinate is exactly a canonical ambient tail.
This is the complement-to-tail bridge needed to iterate the one-block
factorization without changing the ambient ordered carrier. -/
def extractionComplementFiberEquivCanonicalTail
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    ExtractionComplementFiberAt κ fuel active h ≃
      CanonicalExtractionTailAt κ fuel active h where
  toFun κC := by
    let E :=
      extractionFiberEquivBlockComplement
        κ fuel active h
    let κB₀ :=
      selectedExtractionPrimitivePairing κ active h
    refine ⟨E.symm (κB₀, κC), ?_⟩
    exact congrArg Prod.fst
      (E.apply_symm_apply (κB₀, κC))
  invFun τ :=
    (extractionFiberEquivBlockComplement
      κ fuel active h τ.1).2
  left_inv κC := by
    apply Subtype.ext
    exact congrArg (fun p => p.2.1)
      ((extractionFiberEquivBlockComplement
        κ fuel active h).apply_symm_apply
          (selectedExtractionPrimitivePairing
            κ active h, κC))
  right_inv τ := by
    apply Subtype.ext
    apply
      (extractionFiberEquivBlockComplement
        κ fuel active h).injective
    have hfirst :
        (extractionFiberEquivBlockComplement
          κ fuel active h τ.1).1 =
          selectedExtractionPrimitivePairing
            κ active h :=
      τ.2
    rw [(extractionFiberEquivBlockComplement
      κ fuel active h).apply_symm_apply]
    apply Prod.ext
    · exact hfirst.symm
    · rfl

/-- Every canonical ambient tail has the correct next extraction on the
shrunk active carrier. -/
theorem CanonicalExtractionTailAt.tail_extractAux_eq
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (τ : CanonicalExtractionTailAt κ fuel active h) :
    extractAux τ.1.1 fuel
        (active \ selectedExtractionBlock κ active h) =
      extractAux κ fuel
        (active \ selectedExtractionBlock κ active h) :=
  extractionFiber_tail_extractAux_eq
    κ fuel active h τ.1

/-! ## First block followed by an ambient recursive tail -/

/-- Exact one-step extraction-fibre equivalence whose second coordinate
stays on the original ambient carrier and is ready for the next active set. -/
def extractionFiberEquivBlockCanonicalTail
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    ExtractionFiberAt κ fuel active ≃
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ active h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ active h))} ×
      CanonicalExtractionTailAt κ fuel active h :=
  (extractionFiberEquivBlockComplement
    κ fuel active h).trans
      ((Equiv.refl _).prodCongr
        (extractionComplementFiberEquivCanonicalTail
          κ fuel active h))

/-- Finite-sum form of `extractionFiberEquivBlockCanonicalTail`; it exposes
one complete primitive coordinate and an ambient recursive tail with no
cardinality loss. -/
theorem sum_extractionFiber_eq_sum_block_canonicalTail
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    {M : Type*} [AddCommMonoid M]
    (F : ExtractionFiberAt κ fuel active → M) :
    (∑ τ : ExtractionFiberAt κ fuel active, F τ) =
      ∑ κB :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder
                (selectedExtractionBlock κ active h))) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder
                (selectedExtractionBlock κ active h))},
        ∑ tail :
            CanonicalExtractionTailAt
              κ fuel active h,
          F ((extractionFiberEquivBlockCanonicalTail
            κ fuel active h).symm (κB, tail)) := by
  let E :=
    extractionFiberEquivBlockCanonicalTail
      κ fuel active h
  calc
    (∑ τ : ExtractionFiberAt κ fuel active, F τ) =
        ∑ p :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder
                  (selectedExtractionBlock κ active h))) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder
                  (selectedExtractionBlock κ active h))} ×
              CanonicalExtractionTailAt
                κ fuel active h,
          F (E.symm p) :=
      (E.symm.sum_comp F).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]

end

end Anderson4D
