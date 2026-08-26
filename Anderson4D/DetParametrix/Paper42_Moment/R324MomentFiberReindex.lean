import Anderson4D.DetParametrix.Core.ReductionSelectorRigidity

/-!
# Exact coordinate reindexing of an R-324 moment fibre

A fixed doubled moment signature is exactly a left reduction-endpoint
fibre, a right reduction-endpoint fibre, and a bijection between the two
remaining single sets.  This module records that equivalence and exposes the
first primitive coordinate of the left fibre without taking an absolute
value or paying a pairing-cardinality factor.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Converse to the signature-separation lemma: equality of the two
ordinary endpoint signatures gives equality of the doubled moment
signature. -/
theorem momentContractionSignature_eq_of_reductionEndpointSignatures_eq
    {m : ℕ} (e e' : MomentContraction m)
    (hleft :
      reductionEndpointSignature e.1 =
        reductionEndpointSignature e'.1)
    (hright :
      reductionEndpointSignature e.2.1 =
        reductionEndpointSignature e'.2.1) :
    momentContractionSignature e =
      momentContractionSignature e' := by
  have hleftLeft :
      leftEndpoints e.1 = leftEndpoints e'.1 := by
    simpa [reductionEndpointSignature] using
      congrArg Prod.fst hleft
  have hleftRight :
      rightEndpoints e.1 = rightEndpoints e'.1 := by
    simpa [reductionEndpointSignature] using
      congrArg Prod.snd hleft
  have hrightLeft :
      leftEndpoints e.2.1 = leftEndpoints e'.2.1 := by
    simpa [reductionEndpointSignature] using
      congrArg Prod.fst hright
  have hrightRight :
      rightEndpoints e.2.1 = rightEndpoints e'.2.1 := by
    simpa [reductionEndpointSignature] using
      congrArg Prod.snd hright
  unfold momentContractionSignature
    momentWithinHalfEndpointSignature
  rw [hleftLeft, hleftRight, hrightLeft, hrightRight]

/-- The finite fibre of contraction entities with the same doubled
within-half signature as a reference entity. -/
abbrev MomentSignatureFiberAt
    {m : ℕ} (e₀ : MomentContraction m) :=
  {e : MomentContraction m //
    momentContractionSignature e =
      momentContractionSignature e₀}

/-- Separated coordinates of one doubled moment-signature fibre. -/
abbrev MomentSignatureCoordinates
    {m : ℕ} (e₀ : MomentContraction m) :=
  Σ κp : ReductionEndpointFiberAt e₀.1,
    Σ κm : ReductionEndpointFiberAt e₀.2.1,
      κp.1.singles ≃ κm.1.singles

/-- Exact separation of a doubled moment-signature fibre into its two
within-half endpoint fibres and the residual cross-single bijection. -/
def momentSignatureFiberEquivCoordinates
    {m : ℕ} (e₀ : MomentContraction m) :
    MomentSignatureFiberAt e₀ ≃
      MomentSignatureCoordinates e₀ where
  toFun e := by
    let hsignatures :=
      reductionEndpointSignatures_eq_of_momentContractionSignature_eq
        e.1 e₀ e.2
    exact
      ⟨⟨e.1.1, hsignatures.1⟩,
        ⟨⟨e.1.2.1, hsignatures.2⟩, e.1.2.2⟩⟩
  invFun c :=
    ⟨⟨c.1.1, c.2.1.1, c.2.2⟩,
      momentContractionSignature_eq_of_reductionEndpointSignatures_eq
        ⟨c.1.1, c.2.1.1, c.2.2⟩ e₀
        c.1.2 c.2.1.2⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv c := by
    rcases c with ⟨κp, κm, π⟩
    rfl

/-- Finite-sum form of `momentSignatureFiberEquivCoordinates`. -/
theorem sum_momentSignatureFiber_eq_coordinates
    {m : ℕ} (e₀ : MomentContraction m)
    {A : Type*} [AddCommMonoid A]
    (F : MomentSignatureFiberAt e₀ → A) :
    (∑ e : MomentSignatureFiberAt e₀, F e) =
      ∑ κp : ReductionEndpointFiberAt e₀.1,
        ∑ κm : ReductionEndpointFiberAt e₀.2.1,
          ∑ π : κp.1.singles ≃ κm.1.singles,
            F ((momentSignatureFiberEquivCoordinates
              e₀).symm ⟨κp, κm, π⟩) := by
  let E := momentSignatureFiberEquivCoordinates e₀
  calc
    (∑ e : MomentSignatureFiberAt e₀, F e) =
        ∑ c : MomentSignatureCoordinates e₀,
          F (E.symm c) :=
      (E.symm.sum_comp F).symm
    _ = ∑ κp : ReductionEndpointFiberAt e₀.1,
          ∑ κm : ReductionEndpointFiberAt e₀.2.1,
            ∑ π : κp.1.singles ≃ κm.1.singles,
              F (E.symm ⟨κp, κm, π⟩) := by
      simp only [Fintype.sum_sigma]

/-- The exact first left primitive-block coordinate of a fixed doubled
moment fibre.  The remaining right pairing and cross-single equivalence stay
dependent on the reconstructed left complement, so no transport or
multiplicity is hidden. -/
theorem sum_momentSignatureFiber_eq_firstLeftBlock
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    {A : Type*} [AddCommMonoid A]
    (F : MomentSignatureFiberAt e₀ → A) :
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
                ((reductionEndpointFiberEquivBlockComplement
                  e₀.1 hleft).symm (κB, κC)).1.singles ≃
                  κm.1.singles,
              F ((momentSignatureFiberEquivCoordinates
                e₀).symm
                  ⟨(reductionEndpointFiberEquivBlockComplement
                    e₀.1 hleft).symm (κB, κC),
                    κm, π⟩) := by
  let E := momentSignatureFiberEquivCoordinates e₀
  let EL :=
    reductionEndpointFiberEquivBlockComplement
      e₀.1 hleft
  calc
    (∑ e : MomentSignatureFiberAt e₀, F e) =
        ∑ κp : ReductionEndpointFiberAt e₀.1,
          ∑ κm : ReductionEndpointFiberAt e₀.2.1,
            ∑ π : κp.1.singles ≃ κm.1.singles,
              F (E.symm ⟨κp, κm, π⟩) :=
      sum_momentSignatureFiber_eq_coordinates e₀ F
    _ = ∑ p :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder
                (selectedExtractionBlock
                  e₀.1 Finset.univ hleft))) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder
                (selectedExtractionBlock
                  e₀.1 Finset.univ hleft))} ×
          ExtractionComplementFiberAt
            e₀.1 (m - 1) Finset.univ hleft,
          ∑ κm : ReductionEndpointFiberAt e₀.2.1,
            ∑ π : (EL.symm p).1.singles ≃ κm.1.singles,
              F (E.symm ⟨EL.symm p, κm, π⟩) := by
      exact
        (EL.symm.sum_comp
          (fun κp =>
            ∑ κm : ReductionEndpointFiberAt e₀.2.1,
              ∑ π : κp.1.singles ≃ κm.1.singles,
                F (E.symm ⟨κp, κm, π⟩))).symm
    _ = ∑ κB :
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
            ∑ π : (EL.symm (κB, κC)).1.singles ≃
                κm.1.singles,
              F (E.symm
                ⟨EL.symm (κB, κC), κm, π⟩) := by
      rw [Fintype.sum_prod_type]

/-- The exact first right primitive-block coordinate of a fixed doubled
moment fibre.  This is the right-hand analogue of
`sum_momentSignatureFiber_eq_firstLeftBlock`. -/
theorem sum_momentSignatureFiber_eq_firstRightBlock
    {m : ℕ} (e₀ : MomentContraction m)
    (hright :
      ∃ a b,
        IsRelFullyPaired e₀.2.1
          (Finset.univ : Finset (Fin m)) a b)
    {A : Type*} [AddCommMonoid A]
    (F : MomentSignatureFiberAt e₀ → A) :
    (∑ e : MomentSignatureFiberAt e₀, F e) =
      ∑ κp : ReductionEndpointFiberAt e₀.1,
        ∑ κB :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder
                  (selectedExtractionBlock
                    e₀.2.1 Finset.univ hright))) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder
                  (selectedExtractionBlock
                    e₀.2.1 Finset.univ hright))},
          ∑ κC :
              ExtractionComplementFiberAt
                e₀.2.1 (m - 1) Finset.univ hright,
            ∑ π :
                κp.1.singles ≃
                  ((reductionEndpointFiberEquivBlockComplement
                    e₀.2.1 hright).symm (κB, κC)).1.singles,
              F ((momentSignatureFiberEquivCoordinates
                e₀).symm
                  ⟨κp,
                    (reductionEndpointFiberEquivBlockComplement
                      e₀.2.1 hright).symm (κB, κC),
                    π⟩) := by
  let E := momentSignatureFiberEquivCoordinates e₀
  let ER :=
    reductionEndpointFiberEquivBlockComplement
      e₀.2.1 hright
  calc
    (∑ e : MomentSignatureFiberAt e₀, F e) =
        ∑ κp : ReductionEndpointFiberAt e₀.1,
          ∑ κm : ReductionEndpointFiberAt e₀.2.1,
            ∑ π : κp.1.singles ≃ κm.1.singles,
              F (E.symm ⟨κp, κm, π⟩) :=
      sum_momentSignatureFiber_eq_coordinates e₀ F
    _ = ∑ κp : ReductionEndpointFiberAt e₀.1,
          ∑ p :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder
                  (selectedExtractionBlock
                    e₀.2.1 Finset.univ hright))) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder
                  (selectedExtractionBlock
                    e₀.2.1 Finset.univ hright))} ×
            ExtractionComplementFiberAt
              e₀.2.1 (m - 1) Finset.univ hright,
            ∑ π : κp.1.singles ≃ (ER.symm p).1.singles,
              F (E.symm ⟨κp, ER.symm p, π⟩) := by
      apply Finset.sum_congr rfl
      intro κp _
      exact
        (ER.symm.sum_comp
          (fun κm =>
            ∑ π : κp.1.singles ≃ κm.1.singles,
              F (E.symm ⟨κp, κm, π⟩))).symm
    _ = ∑ κp : ReductionEndpointFiberAt e₀.1,
          ∑ κB :
              {τ : PartialPairing
                  (Fin (2 * residualBlockOrder
                    (selectedExtractionBlock
                      e₀.2.1 Finset.univ hright))) //
                τ ∈ primitiveFullPairings
                  (residualBlockOrder
                    (selectedExtractionBlock
                      e₀.2.1 Finset.univ hright))},
            ∑ κC :
                ExtractionComplementFiberAt
                  e₀.2.1 (m - 1) Finset.univ hright,
              ∑ π : κp.1.singles ≃
                  (ER.symm (κB, κC)).1.singles,
                F (E.symm
                  ⟨κp, ER.symm (κB, κC), π⟩) := by
      apply Finset.sum_congr rfl
      intro κp _
      rw [Fintype.sum_prod_type]

/-- Simultaneous exact exposure of the first primitive coordinate in
both endpoint fibres.  In particular, the residual cross-single
equivalence remains dependent on both reconstructed complements; no
cardinality factor or non-canonical transport is introduced. -/
theorem sum_momentSignatureFiber_eq_firstLeftRightBlocks
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (hright :
      ∃ a b,
        IsRelFullyPaired e₀.2.1
          (Finset.univ : Finset (Fin m)) a b)
    {A : Type*} [AddCommMonoid A]
    (F : MomentSignatureFiberAt e₀ → A) :
    (∑ e : MomentSignatureFiberAt e₀, F e) =
      ∑ κBp :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder
                (selectedExtractionBlock
                  e₀.1 Finset.univ hleft))) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder
                (selectedExtractionBlock
                  e₀.1 Finset.univ hleft))},
        ∑ κCp :
            ExtractionComplementFiberAt
              e₀.1 (m - 1) Finset.univ hleft,
          ∑ κBm :
              {τ : PartialPairing
                  (Fin (2 * residualBlockOrder
                    (selectedExtractionBlock
                      e₀.2.1 Finset.univ hright))) //
                τ ∈ primitiveFullPairings
                  (residualBlockOrder
                    (selectedExtractionBlock
                      e₀.2.1 Finset.univ hright))},
            ∑ κCm :
                ExtractionComplementFiberAt
                  e₀.2.1 (m - 1) Finset.univ hright,
              ∑ π :
                  ((reductionEndpointFiberEquivBlockComplement
                    e₀.1 hleft).symm (κBp, κCp)).1.singles ≃
                    ((reductionEndpointFiberEquivBlockComplement
                      e₀.2.1 hright).symm (κBm, κCm)).1.singles,
                F ((momentSignatureFiberEquivCoordinates
                  e₀).symm
                    ⟨(reductionEndpointFiberEquivBlockComplement
                        e₀.1 hleft).symm (κBp, κCp),
                      (reductionEndpointFiberEquivBlockComplement
                        e₀.2.1 hright).symm (κBm, κCm),
                      π⟩) := by
  let E := momentSignatureFiberEquivCoordinates e₀
  let EL :=
    reductionEndpointFiberEquivBlockComplement
      e₀.1 hleft
  let ER :=
    reductionEndpointFiberEquivBlockComplement
      e₀.2.1 hright
  calc
    (∑ e : MomentSignatureFiberAt e₀, F e) =
        ∑ κBp :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft))) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft))},
          ∑ κCp :
              ExtractionComplementFiberAt
                e₀.1 (m - 1) Finset.univ hleft,
            ∑ κm : ReductionEndpointFiberAt e₀.2.1,
              ∑ π : (EL.symm (κBp, κCp)).1.singles ≃
                  κm.1.singles,
                F (E.symm
                  ⟨EL.symm (κBp, κCp), κm, π⟩) :=
      sum_momentSignatureFiber_eq_firstLeftBlock
        e₀ hleft F
    _ = ∑ κBp :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft))) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft))},
          ∑ κCp :
              ExtractionComplementFiberAt
                e₀.1 (m - 1) Finset.univ hleft,
            ∑ p :
              {τ : PartialPairing
                  (Fin (2 * residualBlockOrder
                    (selectedExtractionBlock
                      e₀.2.1 Finset.univ hright))) //
                τ ∈ primitiveFullPairings
                  (residualBlockOrder
                    (selectedExtractionBlock
                      e₀.2.1 Finset.univ hright))} ×
              ExtractionComplementFiberAt
                e₀.2.1 (m - 1) Finset.univ hright,
              ∑ π : (EL.symm (κBp, κCp)).1.singles ≃
                  (ER.symm p).1.singles,
                F (E.symm
                  ⟨EL.symm (κBp, κCp), ER.symm p, π⟩) := by
      apply Finset.sum_congr rfl
      intro κBp _
      apply Finset.sum_congr rfl
      intro κCp _
      exact
        (ER.symm.sum_comp
          (fun κm =>
            ∑ π : (EL.symm (κBp, κCp)).1.singles ≃
                κm.1.singles,
              F (E.symm
                ⟨EL.symm (κBp, κCp), κm, π⟩))).symm
    _ = ∑ κBp :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft))) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft))},
          ∑ κCp :
              ExtractionComplementFiberAt
                e₀.1 (m - 1) Finset.univ hleft,
            ∑ κBm :
                {τ : PartialPairing
                    (Fin (2 * residualBlockOrder
                      (selectedExtractionBlock
                        e₀.2.1 Finset.univ hright))) //
                  τ ∈ primitiveFullPairings
                    (residualBlockOrder
                      (selectedExtractionBlock
                        e₀.2.1 Finset.univ hright))},
              ∑ κCm :
                  ExtractionComplementFiberAt
                    e₀.2.1 (m - 1) Finset.univ hright,
                ∑ π :
                    (EL.symm (κBp, κCp)).1.singles ≃
                      (ER.symm (κBm, κCm)).1.singles,
                  F (E.symm
                    ⟨EL.symm (κBp, κCp),
                      ER.symm (κBm, κCm), π⟩) := by
      apply Finset.sum_congr rfl
      intro κBp _
      apply Finset.sum_congr rfl
      intro κCp _
      rw [Fintype.sum_prod_type]

end

end Anderson4D
