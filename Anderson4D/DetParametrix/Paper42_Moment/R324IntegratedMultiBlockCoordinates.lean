import Anderson4D.DetParametrix.Paper42_Moment.R324IntegratedCollapseClosure
import Anderson4D.DetParametrix.Paper41_Renorm.R322FiberIterationClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitivePartition

/-!
# Independent primitive coordinates of one refined R-324 fibre

Fixing the within-half and residual endpoint signatures fixes the complete
primitive-block schedule.  Every contraction in that refined fibre therefore
embeds in the generic fibre of ambient pairings which are full and relatively
primitive on every block.  The carrier-generic product equivalence then
reindexes the covariance sum by one independent primitive pairing coordinate
per block.

The embedding may harmlessly enlarge the refined fibre.  Since covariance
products are nonnegative, this gives the exact direction needed by the
integrated moment estimate without a pairing-cardinality factor.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The finite type underlying one concrete residual-refined contraction
fibre. -/
abbrev MomentRefinedContractionFiberAt
    (m : ℕ)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :=
  {e : MomentContraction m //
    e ∈ momentRefinedContractionFiber m s r}

/-- A member of a residual-refined fibre is full and relatively primitive
on every block of the common schedule represented by `e₀`. -/
def momentRefinedFiberToPrimitivePartitionFiber
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (e : MomentRefinedContractionFiberAt m s r) :
    PrimitivePartitionFiber
      (momentPrimitiveBlockPartition
        e₀.1 e₀.2.1 e₀.2.2) := by
  refine
    ⟨momentCombinedPairing e.1.1 e.1.2.1 e.1.2.2, ?_⟩
  intro B hB
  have hschedule :
      momentNonemptyPrimitiveBlocks
          e.1.1 e.1.2.1 e.1.2.2 =
        momentNonemptyPrimitiveBlocks
          e₀.1 e₀.2.1 e₀.2.2 :=
    momentNonemptyPrimitiveBlocks_eq_of_mem_refinedFiber
      e.2 he₀
  have hBe :
      B ∈ momentNonemptyPrimitiveBlocks
        e.1.1 e.1.2.1 e.1.2.2 := by
    rw [hschedule]
    exact hB
  exact
    ⟨List.forall_iff_forall_mem.mp
        (momentNonemptyPrimitiveBlocks_forall_isFullyPairedOn
          e.1.1 e.1.2.1 e.1.2.2) B hBe,
      List.forall_iff_forall_mem.mp
        (momentNonemptyPrimitiveBlocks_forall_isRelPrimitiveOn
          e.1.1 e.1.2.1 e.1.2.2) B hBe⟩

/-- The common-schedule map is faithful because the complete doubled
pairing uniquely determines the contraction triple. -/
theorem momentRefinedFiberToPrimitivePartitionFiber_injective
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r) :
    Function.Injective
      (momentRefinedFiberToPrimitivePartitionFiber
        e₀ he₀) := by
  intro e e' heq
  apply Subtype.ext
  apply momentCombinedPairing_injective
  exact congrArg Subtype.val heq

/-- The residual-refined fibre therefore injects into the exact dependent
product of standard primitive-pairing coordinates, with no quotient and no
multiplicity. -/
def momentRefinedFiberPrimitiveCoordinatesEmbedding
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r) :
    MomentRefinedContractionFiberAt m s r ↪
      PrimitivePartitionCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2) :=
  ⟨fun e =>
      primitivePartitionFiberEquivCoordinates
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2)
        (momentRefinedFiberToPrimitivePartitionFiber
          e₀ he₀ e),
    fun _e _e' h =>
      momentRefinedFiberToPrimitivePartitionFiber_injective
        e₀ he₀
        ((primitivePartitionFiberEquivCoordinates
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2)).injective h)⟩

/-- A nonnegative covariance sum over one refined fibre is bounded by the
complete common primitive-partition fibre.  This is an enlargement of the
finite domain, not a termwise cardinality estimate. -/
theorem sum_refinedCovariance_le_sum_primitivePartitionFiber
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (v : Fin (2 * m) → T4) :
    (∑ e : MomentRefinedContractionFiberAt m s r,
        primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing
            e.1.1 e.1.2.1 e.1.2.2) v) ≤
      ∑ τ : PrimitivePartitionFiber
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2),
        primitiveCovarianceProduct ρ ε m τ.1 v := by
  let E :
      MomentRefinedContractionFiberAt m s r ↪
        PrimitivePartitionFiber
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2) :=
    ⟨momentRefinedFiberToPrimitivePartitionFiber e₀ he₀,
      momentRefinedFiberToPrimitivePartitionFiber_injective
        e₀ he₀⟩
  let F :
      PrimitivePartitionFiber
          (momentPrimitiveBlockPartition
            e₀.1 e₀.2.1 e₀.2.2) → ℝ :=
    fun τ =>
      primitiveCovarianceProduct ρ ε m τ.1 v
  change (∑ e, F (E e)) ≤ ∑ τ, F τ
  calc
    (∑ e, F (E e)) =
        ∑ τ ∈ (Finset.univ.image E), F τ := by
      exact (Finset.sum_image E.injective.injOn).symm
    _ ≤ ∑ τ ∈ Finset.univ, F τ := by
      exact
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _)
          (fun τ _hτ _himage =>
            primitiveCovarianceProduct_nonneg
              ρ ε m τ.1 v)
    _ = ∑ τ, F τ := rfl

/-- Paper-facing form: the original finset sum is bounded by the dependent
product of one primitive coordinate on each concrete block. -/
theorem sum_refinedCovariance_le_sum_primitivePartitionCoordinates
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (v : Fin (2 * m) → T4) :
    (∑ e ∈ momentRefinedContractionFiber m s r,
        primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing
            e.1 e.2.1 e.2.2) v) ≤
      ∑ coordinates :
          PrimitivePartitionCoordinates
            (momentPrimitiveBlockPartition
              e₀.1 e₀.2.1 e₀.2.2),
        primitiveCovarianceProduct ρ ε m
          ((primitivePartitionFiberEquivCoordinates
            (momentPrimitiveBlockPartition
              e₀.1 e₀.2.1 e₀.2.2)).symm
                coordinates).1 v := by
  let P :=
    momentPrimitiveBlockPartition
      e₀.1 e₀.2.1 e₀.2.2
  calc
    (∑ e ∈ momentRefinedContractionFiber m s r,
        primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing e.1 e.2.1 e.2.2) v) =
        ∑ e : MomentRefinedContractionFiberAt m s r,
          primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing
              e.1.1 e.1.2.1 e.1.2.2) v := by
      rw [← Finset.sum_attach]
      rw [Finset.attach_eq_univ]
    _ ≤
        ∑ τ : PrimitivePartitionFiber P,
          primitiveCovarianceProduct ρ ε m τ.1 v :=
      sum_refinedCovariance_le_sum_primitivePartitionFiber
        ρ ε m e₀ he₀ v
    _ =
        ∑ coordinates : PrimitivePartitionCoordinates P,
          primitiveCovarianceProduct ρ ε m
            ((primitivePartitionFiberEquivCoordinates
              P).symm coordinates).1 v :=
      sum_primitivePartitionFiber_eq_sum_coordinates
        P fun τ =>
          primitiveCovarianceProduct ρ ε m τ.1 v

/-! ## Exact covariance factorization of the enlarged fibre -/

/-- The standard primitive covariance factor selected by one coordinate
of a generic complete primitive partition. -/
def primitivePartitionBlockCovarianceFactor
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (ρ : SmoothCutoff) (ε : ℝ)
    (P : PrimitiveBlockPartition κ)
    (B : PrimitivePartitionBlockIndex P)
    (σ :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder B.1)) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder B.1)})
    (v : Fin n → T4) : ℝ :=
  primitiveCovarianceProduct ρ ε
    (residualBlockOrder B.1) σ.1
    (fun i =>
      v ((residualPrimitiveBlockOrderIso κ B.1
        (P.block_fullyPaired B.2) i).1))

/-- The ambient covariance factor on one block is literally the standard
primitive factor selected by that block's dependent coordinate. -/
theorem
    pairingCovarianceProductOn_primitivePartitionFiber_eq_blockCoordinate
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (ρ : SmoothCutoff) (ε : ℝ)
    (P : PrimitiveBlockPartition κ)
    (τ : PrimitivePartitionFiber P)
    (B : PrimitivePartitionBlockIndex P)
    (v : Fin n → T4) :
    pairingCovarianceProductOn ρ ε τ.1 B.1 v =
      primitivePartitionBlockCovarianceFactor
        ρ ε P B
        (primitivePartitionFiberCoordinates P τ B) v := by
  let hτB : IsFullyPairedOn τ.1 B.1 :=
    (τ.2 B.1 B.2).1
  let e :=
    residualPrimitiveBlockOrderIso κ B.1
      (P.block_fullyPaired B.2)
  let closed :
      PrimitiveClosedOn
        (residualBlockOrder B.1) B.1 e :=
    ⟨⟨τ.1, hτB.2⟩, by
      change
        orderedBlockPairing τ.1 B.1 hτB e ∈
          primitiveFullPairings
            (residualBlockOrder B.1)
      exact
        (primitivePartitionFiberCoordinates
          P τ B).2⟩
  have hfactor :=
    pairingCovarianceProductOn_eq_orderedClosedBlock
      ρ ε closed v
  change
    pairingCovarianceProductOn ρ ε τ.1 B.1 v =
      primitiveCovarianceProduct ρ ε
        (residualBlockOrder B.1)
        (primitivePartitionFiberCoordinates P τ B).1
        (fun i => v (e i).1)
  exact hfactor

/-- Pairwise-disjoint nonempty blocks cannot repeat. -/
theorem primitiveBlockPartition_blocks_nodup
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ) :
    P.blocks.Nodup := by
  have haux :
      ∀ blocks : List (Finset (Fin n)),
        blocks.Pairwise Disjoint →
        blocks.Forall Finset.Nonempty →
        blocks.Nodup := by
    intro blocks
    induction blocks with
    | nil =>
        simp
    | cons B blocks ih =>
        intro hpairwise hnonempty
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
  exact haux P.blocks P.pairwise_disjoint P.nonempty

/-- A list product over the concrete block schedule is the dependent
fintype product over blocks with their membership certificates. -/
theorem primitiveBlockPartition_list_prod_eq_fintype_prod
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (P : PrimitiveBlockPartition κ)
    {M : Type*} [CommMonoid M]
    (f : Finset (Fin n) → M) :
    (P.blocks.map f).prod =
      ∏ B : PrimitivePartitionBlockIndex P, f B.1 := by
  calc
    (P.blocks.map f).prod =
        P.blocks.toFinset.prod f :=
      (List.prod_toFinset f
        (primitiveBlockPartition_blocks_nodup P)).symm
    _ =
        ∏ B : PrimitivePartitionBlockIndex P,
          f B.1 := by
      apply Finset.prod_subtype
      intro B
      simp

/-- The full ambient covariance product is the product of the standard
primitive covariance factors selected independently on all blocks. -/
theorem
    primitiveCovarianceProduct_primitivePartitionFiber_eq_prod_coordinates
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin (2 * m)))
    (P : PrimitiveBlockPartition κ)
    (τ : PrimitivePartitionFiber P)
    (v : Fin (2 * m) → T4) :
    primitiveCovarianceProduct ρ ε m τ.1 v =
      ∏ B : PrimitivePartitionBlockIndex P,
        primitivePartitionBlockCovarianceFactor
          ρ ε P B
          (primitivePartitionFiberCoordinates P τ B) v := by
  calc
    primitiveCovarianceProduct ρ ε m τ.1 v =
        pairingCovarianceProductOn
          ρ ε τ.1 Finset.univ v := by
      exact (pairingCovarianceProductOn_univ
        ρ ε m τ.1 v).symm
    _ =
        pairingCovarianceProductOn ρ ε τ.1
          (finsetUnionList P.blocks) v := by
      rw [P.cover]
    _ =
        (P.blocks.map fun B =>
          pairingCovarianceProductOn
            ρ ε τ.1 B v).prod :=
      pairingCovarianceProductOn_finsetUnionList
        ρ ε τ.1 P.blocks P.pairwise_disjoint v
    _ =
        ∏ B : PrimitivePartitionBlockIndex P,
          pairingCovarianceProductOn
            ρ ε τ.1 B.1 v :=
      primitiveBlockPartition_list_prod_eq_fintype_prod
        P fun B =>
          pairingCovarianceProductOn ρ ε τ.1 B v
    _ =
        ∏ B : PrimitivePartitionBlockIndex P,
          primitivePartitionBlockCovarianceFactor
            ρ ε P B
            (primitivePartitionFiberCoordinates P τ B) v := by
      apply Fintype.prod_congr
      intro B
      exact
        pairingCovarianceProductOn_primitivePartitionFiber_eq_blockCoordinate
          ρ ε P τ B v

/-- Summing the enlarged common-block fibre separates exactly into the
product of the complete primitive-pairing sums on its blocks. -/
theorem
    sum_primitivePartitionFiber_covariance_eq_prod_primitiveSums
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin (2 * m)))
    (P : PrimitiveBlockPartition κ)
    (v : Fin (2 * m) → T4) :
    (∑ τ : PrimitivePartitionFiber P,
        primitiveCovarianceProduct ρ ε m τ.1 v) =
      ∏ B : PrimitivePartitionBlockIndex P,
        ∑ σ :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder B.1)) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder B.1)},
          primitivePartitionBlockCovarianceFactor
            ρ ε P B σ v := by
  let E :=
    primitivePartitionFiberEquivCoordinates P
  calc
    (∑ τ : PrimitivePartitionFiber P,
        primitiveCovarianceProduct ρ ε m τ.1 v) =
        ∑ coordinates : PrimitivePartitionCoordinates P,
          primitiveCovarianceProduct ρ ε m
            (E.symm coordinates).1 v :=
      sum_primitivePartitionFiber_eq_sum_coordinates
        P fun τ =>
          primitiveCovarianceProduct ρ ε m τ.1 v
    _ =
        ∑ coordinates : PrimitivePartitionCoordinates P,
          ∏ B : PrimitivePartitionBlockIndex P,
            primitivePartitionBlockCovarianceFactor
              ρ ε P B (coordinates B) v := by
      apply Finset.sum_congr rfl
      intro coordinates _hcoordinates
      rw [
        primitiveCovarianceProduct_primitivePartitionFiber_eq_prod_coordinates
          ρ ε m κ P (E.symm coordinates) v]
      apply Fintype.prod_congr
      intro B
      congr 1
      have hforward :
          primitivePartitionFiberCoordinates
              P (E.symm coordinates) =
            coordinates :=
        E.apply_symm_apply coordinates
      exact congrFun hforward B
    _ =
        ∏ B : PrimitivePartitionBlockIndex P,
          ∑ σ :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder B.1)) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder B.1)},
            primitivePartitionBlockCovarianceFactor
              ρ ε P B σ v := by
      exact
        (Fintype.prod_sum fun B σ =>
          primitivePartitionBlockCovarianceFactor
            ρ ε P B σ v).symm

/-- A realized refined covariance sum is controlled by the exact product
of complete primitive sums on its common concrete block schedule. -/
theorem sum_refinedCovariance_le_prod_primitiveBlockSums
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (v : Fin (2 * m) → T4) :
    (∑ e ∈ momentRefinedContractionFiber m s r,
        primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing
            e.1 e.2.1 e.2.2) v) ≤
      ∏ B :
          PrimitivePartitionBlockIndex
            (momentPrimitiveBlockPartition
              e₀.1 e₀.2.1 e₀.2.2),
        ∑ σ :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder B.1)) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder B.1)},
          primitivePartitionBlockCovarianceFactor
            ρ ε
            (momentPrimitiveBlockPartition
              e₀.1 e₀.2.1 e₀.2.2)
            B σ v := by
  calc
    (∑ e ∈ momentRefinedContractionFiber m s r,
        primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing e.1 e.2.1 e.2.2) v) ≤
        ∑ τ :
            PrimitivePartitionFiber
              (momentPrimitiveBlockPartition
                e₀.1 e₀.2.1 e₀.2.2),
          primitiveCovarianceProduct ρ ε m τ.1 v := by
      calc
        (∑ e ∈ momentRefinedContractionFiber m s r,
            primitiveCovarianceProduct ρ ε m
              (momentCombinedPairing e.1 e.2.1 e.2.2) v) =
            ∑ e : MomentRefinedContractionFiberAt m s r,
              primitiveCovarianceProduct ρ ε m
                (momentCombinedPairing
                  e.1.1 e.1.2.1 e.1.2.2) v := by
          rw [← Finset.sum_attach]
          rw [Finset.attach_eq_univ]
        _ ≤ _ :=
          sum_refinedCovariance_le_sum_primitivePartitionFiber
            ρ ε m e₀ he₀ v
    _ = _ :=
      sum_primitivePartitionFiber_covariance_eq_prod_primitiveSums
        ρ ε m
        (momentCombinedPairing e₀.1 e₀.2.1 e₀.2.2)
        (momentPrimitiveBlockPartition
          e₀.1 e₀.2.1 e₀.2.2) v

end

end Anderson4D
