import Anderson4D.DetParametrix.Paper42_Moment.R324MomentFiberReindex

/-!
# Stable residual carriers for the signed R-324 fibre

The first-block factorization of a within-half endpoint fibre is dependent:
after exposing the primitive block pairing `κB`, both the reconstructed
ambient pairing and the type of the cross-single equivalence mention `κB`.
Analytically, however, a primitive full block has no singles.  Consequently,
for a fixed complementary coordinate, changing `κB` cannot change the
ambient single set.

This file records that rigidity before any absolute value is taken.  It is
the type-level bridge needed to put the complete primitive sum innermost in
the signed phase-A Fubini argument while keeping the residual cross-single
carrier fixed.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## Singles are carried entirely by the complementary coordinate -/

/-- Reassembling two primitive full block coordinates over the same
complement produces ambient pairings with exactly the same single set. -/
theorem primitiveClosedOnEquiv_symm_singles_eq
    {n q : ℕ} (B : Finset (Fin n))
    (e : Fin (2 * q) ≃o B)
    (κB κB' :
      {κ : PartialPairing (Fin (2 * q)) //
        κ ∈ primitiveFullPairings q})
    (κC : PartialPairing {i : Fin n // i ∉ B}) :
    (((primitiveClosedOnEquiv q B e).symm
        (κB, κC)).1.1).singles =
      (((primitiveClosedOnEquiv q B e).symm
        (κB', κC)).1.1).singles := by
  let τ : PrimitiveClosedOn q B e :=
    (primitiveClosedOnEquiv q B e).symm (κB, κC)
  let τ' : PrimitiveClosedOn q B e :=
    (primitiveClosedOnEquiv q B e).symm (κB', κC)
  have hcomp :
      (primitiveClosedOnEquiv q B e τ).2 =
        (primitiveClosedOnEquiv q B e τ').2 := by
    simp only [τ, τ', Equiv.apply_symm_apply]
  apply Finset.ext
  intro i
  simp only [PartialPairing.mem_singles]
  constructor
  · intro hi
    by_cases hiB : i ∈ B
    · exact
        (τ.isFullyPairedOn.ne_of_mem hiB hi).elim
    · rw [← τ.eq_outside_of_complement_eq
        τ' hcomp i hiB]
      exact hi
  · intro hi
    by_cases hiB : i ∈ B
    · exact
        (τ'.isFullyPairedOn.ne_of_mem hiB hi).elim
    · rw [τ.eq_outside_of_complement_eq
        τ' hcomp i hiB]
      exact hi

/-! ## The first endpoint-fibre coordinate has a stable residual carrier -/

/-- In the public first-block endpoint-fibre equivalence, the reconstructed
pairing's singles depend only on the complementary coordinate, not on the
primitive full pairing installed on the selected block. -/
theorem
    reductionEndpointFiberEquivBlockComplement_symm_singles_eq
    {m : ℕ} (κ : PartialPairing (Fin m))
    (h :
      ∃ a b,
        IsRelFullyPaired κ
          (Finset.univ : Finset (Fin m)) a b)
    (κB κB' :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))})
    (κC :
      ExtractionComplementFiberAt
        κ (m - 1) Finset.univ h) :
    ((reductionEndpointFiberEquivBlockComplement
        κ h).symm (κB, κC)).1.singles =
      ((reductionEndpointFiberEquivBlockComplement
        κ h).symm (κB', κC)).1.singles := by
  exact
    primitiveClosedOnEquiv_symm_singles_eq
      (selectedExtractionBlock κ Finset.univ h)
      (residualPrimitiveBlockOrderIso κ
        (selectedExtractionBlock κ Finset.univ h)
        (selectRel_isRelFullyPaired
          κ Finset.univ h).isFullyPairedOn)
      κB κB' κC.1

/-- The canonical reconstructed endpoint-fibre member obtained by keeping
the complement `κC` and reinstalling the reference first-block pairing. -/
def firstBlockReferenceEndpointFiber
    {m : ℕ} (κ : PartialPairing (Fin m))
    (h :
      ∃ a b,
        IsRelFullyPaired κ
          (Finset.univ : Finset (Fin m)) a b)
    (κC :
      ExtractionComplementFiberAt
        κ (m - 1) Finset.univ h) :
    ReductionEndpointFiberAt κ :=
  (reductionEndpointFiberEquivBlockComplement
    κ h).symm
      (selectedExtractionPrimitivePairing
        κ Finset.univ h, κC)

/-- Canonical transport of a cross-single equivalence to the
`κB`-independent single carrier furnished by the reference block
coordinate. -/
def firstBlockCrossEquivStabilization
    {m : ℕ} (κ : PartialPairing (Fin m))
    (h :
      ∃ a b,
        IsRelFullyPaired κ
          (Finset.univ : Finset (Fin m)) a b)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))})
    (κC :
      ExtractionComplementFiberAt
        κ (m - 1) Finset.univ h)
    (κother : PartialPairing (Fin m)) :
    (((reductionEndpointFiberEquivBlockComplement
        κ h).symm (κB, κC)).1.singles ≃
      κother.singles) ≃
      ((firstBlockReferenceEndpointFiber
        κ h κC).1.singles ≃ κother.singles) := by
  let hsingles :
      ((reductionEndpointFiberEquivBlockComplement
          κ h).symm (κB, κC)).1.singles =
        (firstBlockReferenceEndpointFiber
          κ h κC).1.singles :=
    reductionEndpointFiberEquivBlockComplement_symm_singles_eq
      κ h κB
        (selectedExtractionPrimitivePairing
          κ Finset.univ h)
        κC
  let e :=
    finsetSubtypeEquivOfEq hsingles
  exact
    { toFun := fun π => e.symm.trans π
      invFun := fun π => e.trans π
      left_inv := by
        intro π
        ext i
        simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      right_inv := by
        intro π
        ext i
        simp only [Equiv.trans_apply, Equiv.apply_symm_apply] }

@[simp]
theorem firstBlockCrossEquivStabilization_symm_apply
    {m : ℕ} (κ : PartialPairing (Fin m))
    (h :
      ∃ a b,
        IsRelFullyPaired κ
          (Finset.univ : Finset (Fin m)) a b)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))})
    (κC :
      ExtractionComplementFiberAt
        κ (m - 1) Finset.univ h)
    (κother : PartialPairing (Fin m))
    (π :
      (firstBlockReferenceEndpointFiber
        κ h κC).1.singles ≃ κother.singles) :
    (firstBlockCrossEquivStabilization
      κ h κB κC κother).symm π =
      (finsetSubtypeEquivOfEq
        (reductionEndpointFiberEquivBlockComplement_symm_singles_eq
          κ h κB
            (selectedExtractionPrimitivePairing
              κ Finset.univ h)
          κC)).trans π :=
  rfl

/-! ## Signed first-left reindex with the primitive sum innermost -/

/-- Exact first-left reindexing in the order required by phase A:
the complementary left coordinate, right endpoint-fibre member, and
cross-single equivalence are fixed before the complete primitive block
coordinate is summed.  The cross-single type is independent of `κB`, so
the innermost finite sum can be identified with the signed primitive kernel
before any norm is taken. -/
theorem sum_momentSignatureFiber_eq_firstLeftBlock_stable
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    {A : Type*} [AddCommMonoid A]
    (F : MomentSignatureFiberAt e₀ → A) :
    (∑ e : MomentSignatureFiberAt e₀, F e) =
      ∑ κC :
          ExtractionComplementFiberAt
            e₀.1 (m - 1) Finset.univ hleft,
        ∑ κm : ReductionEndpointFiberAt e₀.2.1,
          ∑ π :
              (firstBlockReferenceEndpointFiber
                e₀.1 hleft κC).1.singles ≃
                κm.1.singles,
            ∑ κB :
                {τ : PartialPairing
                    (Fin (2 * residualBlockOrder
                      (selectedExtractionBlock
                        e₀.1 Finset.univ hleft))) //
                  τ ∈ primitiveFullPairings
                    (residualBlockOrder
                      (selectedExtractionBlock
                        e₀.1 Finset.univ hleft))},
              F ((momentSignatureFiberEquivCoordinates
                e₀).symm
                  ⟨(reductionEndpointFiberEquivBlockComplement
                      e₀.1 hleft).symm (κB, κC),
                    κm,
                    (firstBlockCrossEquivStabilization
                      e₀.1 hleft κB κC κm.1).symm π⟩) := by
  let E := momentSignatureFiberEquivCoordinates e₀
  let EL :=
    reductionEndpointFiberEquivBlockComplement
      e₀.1 hleft
  calc
    (∑ e : MomentSignatureFiberAt e₀, F e) =
        ∑ κB :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft))) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft))},
          ∑ κC :
              ExtractionComplementFiberAt
                e₀.1 (m - 1) Finset.univ hleft,
            ∑ κm : ReductionEndpointFiberAt e₀.2.1,
              ∑ π :
                  (EL.symm (κB, κC)).1.singles ≃
                    κm.1.singles,
                F (E.symm
                  ⟨EL.symm (κB, κC), κm, π⟩) :=
      sum_momentSignatureFiber_eq_firstLeftBlock
        e₀ hleft F
    _ =
        ∑ κB :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft))) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft))},
          ∑ κC :
              ExtractionComplementFiberAt
                e₀.1 (m - 1) Finset.univ hleft,
            ∑ κm : ReductionEndpointFiberAt e₀.2.1,
              ∑ π :
                  (firstBlockReferenceEndpointFiber
                    e₀.1 hleft κC).1.singles ≃
                    κm.1.singles,
                F (E.symm
                  ⟨EL.symm (κB, κC), κm,
                    (firstBlockCrossEquivStabilization
                      e₀.1 hleft κB κC κm.1).symm π⟩) := by
      apply Finset.sum_congr rfl
      intro κB _hκB
      apply Finset.sum_congr rfl
      intro κC _hκC
      apply Finset.sum_congr rfl
      intro κm _hκm
      exact
        ((firstBlockCrossEquivStabilization
          e₀.1 hleft κB κC κm.1).symm.sum_comp
            (fun π =>
              F (E.symm
                ⟨EL.symm (κB, κC), κm, π⟩))).symm
    _ =
        ∑ κC :
            ExtractionComplementFiberAt
              e₀.1 (m - 1) Finset.univ hleft,
          ∑ κm : ReductionEndpointFiberAt e₀.2.1,
            ∑ π :
                (firstBlockReferenceEndpointFiber
                  e₀.1 hleft κC).1.singles ≃
                  κm.1.singles,
              ∑ κB :
                  {τ : PartialPairing
                      (Fin (2 * residualBlockOrder
                        (selectedExtractionBlock
                          e₀.1 Finset.univ hleft))) //
                    τ ∈ primitiveFullPairings
                      (residualBlockOrder
                        (selectedExtractionBlock
                          e₀.1 Finset.univ hleft))},
                F (E.symm
                  ⟨EL.symm (κB, κC), κm,
                    (firstBlockCrossEquivStabilization
                      e₀.1 hleft κB κC κm.1).symm π⟩) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro κC _hκC
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro κm _hκm
      rw [Finset.sum_comm]

end

end Anderson4D
