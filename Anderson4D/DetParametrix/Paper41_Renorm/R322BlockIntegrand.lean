import Anderson4D.DetParametrix.Paper41_Renorm.R322EndpointFiber
import Anderson4D.DetParametrix.Paper42_Moment.R324BlockPairingSum

/-!
# Pointwise primitive-block factorization for R-322

This module separates the two ingredients of a fixed endpoint-signature
integrand:

* the signed Green/difference skeleton, which is common to the whole fibre;
* the covariance pairing product, whose first complete primitive coordinate
  is exposed by the block-complement equivalence.

The statements are pointwise and use an arbitrary active carrier.  No
integration order or R-322 estimate is hidden here; those are supplied by the
subsequent collapse module.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The common signed `J` skeleton -/

/-- The Green and extracted-difference factors of the closed `J` integrand,
without its covariance product. -/
def renormalizedJGreenSkeleton
    {n : ℕ} (σ : PartialPairing (Fin n))
    (x : Fin n → T4) : ℝ :=
  (∏ e : Fin (n - 1),
      if e.val ∈ ((extract σ).map fun p => p.2.val) then 1
      else if h : e.val + 1 < n then
        greenFn
          (x ⟨e.val, by omega⟩ -
            x ⟨e.val + 1, h⟩)
      else 1) *
    ((extract σ).map (diffFactorJ x)).prod

/-- The frozen `J` integrand is exactly its common signed skeleton times the
ambient covariance product. -/
theorem detJintegrand_eq_skeleton_mul_covariance
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (x : Fin (2 * q) → T4) :
    detJintegrand ρ ε q σ x =
      renormalizedJGreenSkeleton σ x *
        pairingCovarianceProductOn
          ρ ε σ Finset.univ x := by
  unfold detJintegrand renormalizedJGreenSkeleton
    pairingCovarianceProductOn
  have hfilter :
      σ.pairSupport.filter (fun i => i < σ i) =
        (Finset.univ : Finset (Fin (2 * q))).filter
          (fun i => i < σ i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      PartialPairing.mem_pairSupport]
    constructor
    · exact fun hi => hi.2
    · intro hi
      exact ⟨ne_of_gt hi, hi⟩
  rw [hfilter]

/-- Endpoint signatures determine the complete signed `J` skeleton. -/
theorem renormalizedJGreenSkeleton_eq_of_signature_eq
    {n : ℕ} (σ τ : PartialPairing (Fin n))
    (hsignature :
      reductionEndpointSignature τ =
        reductionEndpointSignature σ) :
    renormalizedJGreenSkeleton τ =
      renormalizedJGreenSkeleton σ := by
  have hextract :
      extract τ = extract σ :=
    extract_eq_of_reductionEndpointSignature_eq
      τ σ hsignature
  funext x
  unfold renormalizedJGreenSkeleton
  rw [hextract]

/-- Pointwise, the complete endpoint-fibre sum has one common signed Green
skeleton multiplying the exact covariance fibre sum. -/
theorem sum_endpointFiber_detJintegrand_eq_skeleton_mul_covariance
    (ρ : SmoothCutoff) (ε : ℝ) {q : ℕ}
    (κ : PartialPairing (Fin (2 * q)))
    (x : Fin (2 * q) → T4) :
    (∑ τ : ReductionEndpointFiberAt κ,
        detJintegrand ρ ε q τ.1 x) =
      renormalizedJGreenSkeleton κ x *
        ∑ τ : ReductionEndpointFiberAt κ,
          pairingCovarianceProductOn
            ρ ε τ.1 Finset.univ x := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _hτ
  rw [detJintegrand_eq_skeleton_mul_covariance]
  have hskeleton :=
    renormalizedJGreenSkeleton_eq_of_signature_eq
      κ τ.1 τ.2
  rw [hskeleton]

/-! ## The first primitive covariance coordinate on an arbitrary active set -/

/-- The block coordinate returned by
`extractionFiberEquivBlockComplement` is definitionally the increasingly
ordered restriction carried by `extractionFiberPrimitiveClosedOn`. -/
theorem extractionFiber_firstCoordinate_eq_orderedBlockPairing
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (τ : ExtractionFiberAt κ fuel active) :
    ((extractionFiberEquivBlockComplement
      κ fuel active h τ).1).1 =
      orderedClosedBlockPairing
        (selectedExtractionBlock κ active h)
        (residualPrimitiveBlockOrderIso κ
          (selectedExtractionBlock κ active h)
          (selectRel_isRelFullyPaired
            κ active h).isFullyPairedOn)
        (extractionFiberPrimitiveClosedOn
          κ fuel active h τ).1 := by
  rfl

/-- **Arbitrary ordered-block analytic coordinate.**

For every member of an extraction fibre on an arbitrary active carrier, the
ambient covariance factor on its selected sparse block is exactly the
standard primitive covariance factor indexed by the first coordinate of the
block-complement equivalence.  This is the reusable pointwise identity for
both R-322 and the residual R-324 collapse. -/
theorem pairingCovarianceProductOn_extractionFiber_eq_firstCoordinate
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (τ : ExtractionFiberAt κ fuel active)
    (x : Fin m → T4) :
    pairingCovarianceProductOn ρ ε τ.1
        (selectedExtractionBlock κ active h) x =
      primitiveCovarianceProduct ρ ε
        (residualBlockOrder
          (selectedExtractionBlock κ active h))
        ((extractionFiberEquivBlockComplement
          κ fuel active h τ).1).1
        (fun i =>
          x ((residualPrimitiveBlockOrderIso κ
            (selectedExtractionBlock κ active h)
            (selectRel_isRelFullyPaired
              κ active h).isFullyPairedOn i).1)) := by
  let closed :=
    extractionFiberPrimitiveClosedOn
      κ fuel active h τ
  have hcov :=
    pairingCovarianceProductOn_eq_orderedClosedBlock
      ρ ε closed x
  rw [extractionFiber_firstCoordinate_eq_orderedBlockPairing
    κ fuel active h τ]
  exact hcov

/-- Changing only the exposed primitive block coordinate leaves the ambient
pairing unchanged off that block. -/
theorem extractionFiber_blockCoordinate_eq_outside
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (κB κB' :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ active h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ active h))})
    (κC : ExtractionComplementFiberAt
      κ fuel active h)
    (i : Fin m)
    (hi : i ∉ selectedExtractionBlock κ active h) :
    ((extractionFiberEquivBlockComplement
      κ fuel active h).symm (κB, κC)).1 i =
      ((extractionFiberEquivBlockComplement
        κ fuel active h).symm (κB', κC)).1 i := by
  let E :=
    extractionFiberEquivBlockComplement
      κ fuel active h
  let τ : ExtractionFiberAt κ fuel active :=
    E.symm (κB, κC)
  let τ' : ExtractionFiberAt κ fuel active :=
    E.symm (κB', κC)
  let closed :=
    extractionFiberPrimitiveClosedOn
      κ fuel active h τ
  let closed' :=
    extractionFiberPrimitiveClosedOn
      κ fuel active h τ'
  have hcoord : E τ = (κB, κC) :=
    E.apply_symm_apply (κB, κC)
  have hcoord' : E τ' = (κB', κC) :=
    E.apply_symm_apply (κB', κC)
  have hcomp :
      (primitiveClosedOnEquiv
        (residualBlockOrder
          (selectedExtractionBlock κ active h))
        (selectedExtractionBlock κ active h)
        (residualPrimitiveBlockOrderIso κ
          (selectedExtractionBlock κ active h)
          (selectRel_isRelFullyPaired
            κ active h).isFullyPairedOn)
        closed).2 =
      (primitiveClosedOnEquiv
        (residualBlockOrder
          (selectedExtractionBlock κ active h))
        (selectedExtractionBlock κ active h)
        (residualPrimitiveBlockOrderIso κ
          (selectedExtractionBlock κ active h)
          (selectRel_isRelFullyPaired
            κ active h).isFullyPairedOn)
        closed').2 := by
    change (E τ).2.1 = (E τ').2.1
    rw [hcoord, hcoord']
  exact
    closed.eq_outside_of_complement_eq
      closed' hcomp i hi

/-- Consequently the covariance product on the complementary active carrier
is independent of the primitive block coordinate. -/
theorem pairingCovarianceProductOn_complement_eq_of_blockCoordinate
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (κB κB' :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ active h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ active h))})
    (κC : ExtractionComplementFiberAt
      κ fuel active h)
    (x : Fin m → T4) :
    pairingCovarianceProductOn ρ ε
        ((extractionFiberEquivBlockComplement
          κ fuel active h).symm (κB, κC)).1
        (active \ selectedExtractionBlock κ active h) x =
      pairingCovarianceProductOn ρ ε
        ((extractionFiberEquivBlockComplement
          κ fuel active h).symm (κB', κC)).1
        (active \ selectedExtractionBlock κ active h) x := by
  let τ :=
    ((extractionFiberEquivBlockComplement
      κ fuel active h).symm (κB, κC)).1
  let τ' :=
    ((extractionFiberEquivBlockComplement
      κ fuel active h).symm (κB', κC)).1
  have hout :
      ∀ i ∈ active \ selectedExtractionBlock κ active h,
        τ i = τ' i := by
    intro i hi
    exact extractionFiber_blockCoordinate_eq_outside
      κ fuel active h κB κB' κC i
      (Finset.mem_sdiff.mp hi).2
  unfold pairingCovarianceProductOn
  have hfilter :
      (active \ selectedExtractionBlock κ active h).filter
          (fun i => i < τ i) =
        (active \ selectedExtractionBlock κ active h).filter
          (fun i => i < τ' i) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hlt⟩
      exact ⟨hi, by rw [← hout i hi]; exact hlt⟩
    · rintro ⟨hi, hlt⟩
      exact ⟨hi, by rw [hout i hi]; exact hlt⟩
  rw [hfilter]
  apply Finset.prod_congr rfl
  intro i hi
  have hiActive :
      i ∈ active \ selectedExtractionBlock κ active h :=
    (Finset.mem_filter.mp hi).1
  rw [hout i hiActive]

/-- Exact one-step factorization of the covariance fibre sum on an arbitrary
active carrier.  The first factor is the complete primitive pairing sum on
the selected block; the second is the remaining complementary fibre.  There
is no pairing-cardinality loss. -/
theorem sum_extractionFiber_covariance_eq_primitive_mul_complement
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (x : Fin m → T4) :
    (∑ τ : ExtractionFiberAt κ fuel active,
        pairingCovarianceProductOn ρ ε τ.1 active x) =
      (∑ κB :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder
                (selectedExtractionBlock κ active h))) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder
                (selectedExtractionBlock κ active h))},
          primitiveCovarianceProduct ρ ε
            (residualBlockOrder
              (selectedExtractionBlock κ active h))
            κB.1
            (fun i =>
              x ((residualPrimitiveBlockOrderIso κ
                (selectedExtractionBlock κ active h)
                (selectRel_isRelFullyPaired
                  κ active h).isFullyPairedOn i).1))) *
        ∑ κC : ExtractionComplementFiberAt
            κ fuel active h,
          pairingCovarianceProductOn ρ ε
            ((extractionFiberEquivBlockComplement
              κ fuel active h).symm
                (selectedExtractionPrimitivePairing
                  κ active h, κC)).1
            (active \
              selectedExtractionBlock κ active h) x := by
  let B := selectedExtractionBlock κ active h
  let κB₀ := selectedExtractionPrimitivePairing κ active h
  let E :=
    extractionFiberEquivBlockComplement
      κ fuel active h
  have hBactive : B ⊆ active :=
    relIcc_subset_active _ _ _
  calc
    (∑ τ : ExtractionFiberAt κ fuel active,
        pairingCovarianceProductOn ρ ε τ.1 active x) =
        ∑ p :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder B)) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder B)} ×
              ExtractionComplementFiberAt
                κ fuel active h,
          pairingCovarianceProductOn ρ ε
            (E.symm p).1 active x := by
      exact (E.symm.sum_comp fun τ =>
        pairingCovarianceProductOn
          ρ ε τ.1 active x).symm
    _ =
        ∑ κB :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder B)) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder B)},
          ∑ κC : ExtractionComplementFiberAt
              κ fuel active h,
            pairingCovarianceProductOn ρ ε
              (E.symm (κB, κC)).1 active x := by
      rw [Fintype.sum_prod_type]
    _ =
        ∑ κB :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder B)) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder B)},
          ∑ κC : ExtractionComplementFiberAt
              κ fuel active h,
            primitiveCovarianceProduct ρ ε
                (residualBlockOrder B) κB.1
                (fun i =>
                  x ((residualPrimitiveBlockOrderIso κ B
                    (selectRel_isRelFullyPaired
                      κ active h).isFullyPairedOn i).1)) *
              pairingCovarianceProductOn ρ ε
                (E.symm (κB₀, κC)).1
                (active \ B) x := by
      apply Finset.sum_congr rfl
      intro κB _hκB
      apply Finset.sum_congr rfl
      intro κC _hκC
      have hsplit :
          pairingCovarianceProductOn ρ ε
              (E.symm (κB, κC)).1 active x =
            pairingCovarianceProductOn ρ ε
                (E.symm (κB, κC)).1 B x *
              pairingCovarianceProductOn ρ ε
                (E.symm (κB, κC)).1
                (active \ B) x := by
        rw [← pairingCovarianceProductOn_union
          ρ ε (E.symm (κB, κC)).1
          B (active \ B) Finset.disjoint_sdiff x,
          Finset.union_sdiff_of_subset hBactive]
      rw [hsplit,
        pairingCovarianceProductOn_extractionFiber_eq_firstCoordinate
          ρ ε κ fuel active h
          (E.symm (κB, κC)) x]
      rw [E.apply_symm_apply (κB, κC)]
      rw [pairingCovarianceProductOn_complement_eq_of_blockCoordinate
        ρ ε κ fuel active h κB κB₀ κC x]
    _ =
        (∑ κB :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder B)) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder B)},
          primitiveCovarianceProduct ρ ε
            (residualBlockOrder B) κB.1
            (fun i =>
              x ((residualPrimitiveBlockOrderIso κ B
                (selectRel_isRelFullyPaired
                  κ active h).isFullyPairedOn i).1))) *
          ∑ κC : ExtractionComplementFiberAt
              κ fuel active h,
            pairingCovarianceProductOn ρ ε
              (E.symm (κB₀, κC)).1
              (active \ B) x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro κB _hκB
      rw [Finset.mul_sum]
    _ = _ := by
      rfl

/-- Endpoint-signature specialization of the arbitrary ordered-block
identity. -/
theorem pairingCovarianceProductOn_endpointFiber_eq_firstCoordinate
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (h :
      ∃ a b,
        IsRelFullyPaired κ
          (Finset.univ : Finset (Fin m)) a b)
    (τ : ReductionEndpointFiberAt κ)
    (x : Fin m → T4) :
    pairingCovarianceProductOn ρ ε τ.1
        (selectedExtractionBlock κ Finset.univ h) x =
      primitiveCovarianceProduct ρ ε
        (residualBlockOrder
          (selectedExtractionBlock κ Finset.univ h))
        ((reductionEndpointFiberEquivBlockComplement
          κ h τ).1).1
        (fun i =>
          x ((residualPrimitiveBlockOrderIso κ
            (selectedExtractionBlock κ Finset.univ h)
            (selectRel_isRelFullyPaired
              κ Finset.univ h).isFullyPairedOn i).1)) := by
  exact
    pairingCovarianceProductOn_extractionFiber_eq_firstCoordinate
      ρ ε κ (m - 1) Finset.univ h
      (reductionEndpointFiberEquivExtractionFiber κ h τ) x

end

end Anderson4D
