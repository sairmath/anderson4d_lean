import Anderson4D.DetParametrix.Paper41_Renorm.R322EndpointProductClosure

/-!
# Coordinate form of the R-322 endpoint-fibre integrand

The exact endpoint-fibre product equivalence is now combined with the
covariance factorization over concrete extraction blocks.  The result is a
literal product of complete primitive pairing sums, while the signed
Green/difference skeleton remains common to the whole endpoint fibre.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## List products versus dependent block products -/

theorem List.nodup_of_pairwise_disjoint_of_forall_nonempty
    {α : Type*} [DecidableEq α]
    (blocks : List (Finset α))
    (hpairwise : blocks.Pairwise Disjoint)
    (hnonempty : blocks.Forall Finset.Nonempty) :
    blocks.Nodup := by
  induction blocks with
  | nil =>
      simp
  | cons B blocks ih =>
      rw [List.pairwise_cons] at hpairwise
      rw [List.forall_cons] at hnonempty
      rw [List.nodup_cons]
      constructor
      · intro hB
        obtain ⟨i, hi⟩ := hnonempty.1
        exact
          (Finset.disjoint_left.mp
            (hpairwise.1 B hB)) hi hi
      · exact ih hpairwise.2 hnonempty.2

theorem list_map_prod_eq_fintype_prod_subtype
    {α M : Type*} [DecidableEq α] [CommMonoid M]
    (blocks : List α) (hnodup : blocks.Nodup)
    (f : α → M) :
    (blocks.map f).prod =
      ∏ a : {a : α // a ∈ blocks}, f a.1 := by
  calc
    (blocks.map f).prod =
        blocks.toFinset.prod f :=
      (List.prod_toFinset f hnodup).symm
    _ = ∏ a : {a : α // a ∈ blocks},
          f a.1 := by
      apply Finset.prod_subtype
      intro a
      simp

theorem extractionBlocks_nodup
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (extractionBlocks κ).Nodup :=
  List.nodup_of_pairwise_disjoint_of_forall_nonempty
    (extractionBlocks κ)
    (extractionBlocks_pairwise_disjoint κ)
    (extractionBlocks_forall_nonempty κ)

/-! ## One arbitrary concrete block coordinate -/

/-- Primitive covariance factor carried by one standard block coordinate. -/
def extractionBlockPrimitiveCovarianceFactor
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (B : ExtractionBlockIndex κ)
    (σ :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder B.1)) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder B.1)})
    (x : Fin m → T4) : ℝ :=
  primitiveCovarianceProduct ρ ε
    (residualBlockOrder B.1) σ.1
    (fun i =>
      x ((residualPrimitiveBlockOrderIso κ B.1
        (extractionBlock_isFullyPairedOn_of_mem
          κ B.1 B.2) i).1))

/-- On every concrete extraction block, the ambient covariance factor is
exactly the standard primitive factor selected by the corresponding product
coordinate. -/
theorem pairingCovarianceProductOn_endpointFiber_eq_blockCoordinate
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m))
    (τ : ReductionEndpointFiberAt κ)
    (B : ExtractionBlockIndex κ)
    (x : Fin m → T4) :
    pairingCovarianceProductOn ρ ε τ.1 B.1 x =
      extractionBlockPrimitiveCovarianceFactor
        ρ ε κ B
        (endpointFiberPrimitiveCoordinate κ τ B) x := by
  let hτB :=
    endpointFiber_isFullyPairedOn_extractionBlock
      κ τ B
  let e :=
    residualPrimitiveBlockOrderIso κ B.1
      (extractionBlock_isFullyPairedOn_of_mem
        κ B.1 B.2)
  let closed :
      PrimitiveClosedOn
        (residualBlockOrder B.1) B.1 e :=
    ⟨⟨τ.1, hτB.2⟩, by
      change
        orderedBlockPairing τ.1 B.1 hτB e ∈
          primitiveFullPairings
            (residualBlockOrder B.1)
      exact
        (endpointFiberPrimitiveCoordinate
          κ τ B).2⟩
  have h :=
    pairingCovarianceProductOn_eq_orderedClosedBlock
      ρ ε closed x
  change
    pairingCovarianceProductOn ρ ε τ.1 B.1 x =
      primitiveCovarianceProduct ρ ε
        (residualBlockOrder B.1)
        (endpointFiberPrimitiveCoordinate κ τ B).1
        (fun i => x (e i).1)
  exact h

/-! ## Complete covariance product and fibre sum -/

/-- The full covariance product of one endpoint-fibre member is the product
of its independent primitive block-coordinate factors. -/
theorem primitiveCovarianceProduct_endpointFiber_eq_prod_coordinates
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ.IsFull)
    (τ : ReductionEndpointFiberAt κ)
    (x : Fin (2 * q) → T4) :
    primitiveCovarianceProduct ρ ε q τ.1 x =
      ∏ B : ExtractionBlockIndex κ,
        extractionBlockPrimitiveCovarianceFactor
          ρ ε κ B
          (endpointFiberPrimitiveCoordinate κ τ B) x := by
  have hτ :
      τ.1.IsFull :=
    isFull_of_reductionEndpointSignature_eq
      κ τ.1 hκ τ.2
  have hblocks :
      extractionBlocks τ.1 =
        extractionBlocks κ :=
    extractionBlocks_eq_of_reductionEndpointSignature_eq
      τ.1 κ τ.2
  calc
    primitiveCovarianceProduct ρ ε q τ.1 x =
        ((extractionBlocks τ.1).map fun B =>
          pairingCovarianceProductOn
            ρ ε τ.1 B x).prod :=
      primitiveCovarianceProduct_eq_prod_extractionBlocks_of_full
        ρ ε q τ.1 hτ x
    _ =
        ((extractionBlocks κ).map fun B =>
          pairingCovarianceProductOn
            ρ ε τ.1 B x).prod := by
      rw [hblocks]
    _ =
        ∏ B : ExtractionBlockIndex κ,
          pairingCovarianceProductOn
            ρ ε τ.1 B.1 x := by
      exact list_map_prod_eq_fintype_prod_subtype
        (extractionBlocks κ)
        (extractionBlocks_nodup κ)
        (fun B =>
          pairingCovarianceProductOn
            ρ ε τ.1 B x)
    _ =
        ∏ B : ExtractionBlockIndex κ,
          extractionBlockPrimitiveCovarianceFactor
            ρ ε κ B
            (endpointFiberPrimitiveCoordinate
              κ τ B) x := by
      apply Fintype.prod_congr
      intro B
      exact
        pairingCovarianceProductOn_endpointFiber_eq_blockCoordinate
          ρ ε κ τ B x

/-- Summing the complete endpoint fibre separates exactly into the product
of the complete primitive pairing sums on its blocks. -/
theorem sum_endpointFiber_primitiveCovarianceProduct_eq_prod_primitiveSums
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ.IsFull)
    (x : Fin (2 * q) → T4) :
    (∑ τ : ReductionEndpointFiberAt κ,
        primitiveCovarianceProduct ρ ε q τ.1 x) =
      ∏ B : ExtractionBlockIndex κ,
        ∑ σ :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder B.1)) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder B.1)},
          extractionBlockPrimitiveCovarianceFactor
            ρ ε κ B σ x := by
  let E :=
    endpointFiberEquivPrimitiveCoordinates κ hκ
  calc
    (∑ τ : ReductionEndpointFiberAt κ,
        primitiveCovarianceProduct ρ ε q τ.1 x) =
        ∑ coordinates : ExtractionPrimitiveCoordinates κ,
          primitiveCovarianceProduct ρ ε q
            (E.symm coordinates).1 x :=
      sum_endpointFiber_eq_sum_primitiveCoordinates
        κ hκ (fun τ =>
          primitiveCovarianceProduct ρ ε q τ.1 x)
    _ =
        ∑ coordinates : ExtractionPrimitiveCoordinates κ,
          ∏ B : ExtractionBlockIndex κ,
            extractionBlockPrimitiveCovarianceFactor
              ρ ε κ B (coordinates B) x := by
      apply Finset.sum_congr rfl
      intro coordinates _hcoordinates
      rw [
        primitiveCovarianceProduct_endpointFiber_eq_prod_coordinates
          ρ ε q κ hκ (E.symm coordinates) x]
      apply Fintype.prod_congr
      intro B
      congr 1
      have hforward :
          endpointFiberPrimitiveCoordinates
              κ (E.symm coordinates) =
            coordinates := by
        rw [←
          endpointFiberEquivPrimitiveCoordinates_apply
            κ hκ (E.symm coordinates)]
        exact E.apply_symm_apply coordinates
      exact congrFun hforward B
    _ =
        ∏ B : ExtractionBlockIndex κ,
          ∑ σ :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder B.1)) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder B.1)},
            extractionBlockPrimitiveCovarianceFactor
              ρ ε κ B σ x := by
      exact
        (Fintype.prod_sum fun B σ =>
          extractionBlockPrimitiveCovarianceFactor
            ρ ε κ B σ x).symm

/-- Pointwise endpoint-fibre integrand factorization: the common signed
Green skeleton multiplies the exact product of primitive covariance sums. -/
theorem sum_endpointFiber_detJintegrand_eq_skeleton_mul_prod_primitiveSums
    (ρ : SmoothCutoff) (ε : ℝ) {q : ℕ}
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ.IsFull)
    (x : Fin (2 * q) → T4) :
    (∑ τ : ReductionEndpointFiberAt κ,
        detJintegrand ρ ε q τ.1 x) =
      renormalizedJGreenSkeleton κ x *
        ∏ B : ExtractionBlockIndex κ,
          ∑ σ :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder B.1)) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder B.1)},
            extractionBlockPrimitiveCovarianceFactor
              ρ ε κ B σ x := by
  rw [
    sum_endpointFiber_detJintegrand_eq_skeleton_mul_covariance]
  simp_rw [pairingCovarianceProductOn_univ]
  rw [
    sum_endpointFiber_primitiveCovarianceProduct_eq_prod_primitiveSums
      ρ ε q κ hκ x]

end

end Anderson4D
