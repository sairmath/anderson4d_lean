import Anderson4D.DetParametrix.Paper42_Moment.R324IntegratedMultiBlockCoordinates
import Anderson4D.DetParametrix.Paper42_Moment.R324IntegratedOneBlockClosure

/-!
# The actual R-324 grouped core as a product of primitive block sums

The endpoint integrations leave two signed interior Green profiles and the
complete covariance sum in one residual-refined fibre.  This file keeps the
two signed profiles outside the norm until the exact refined sum has been
formed, then applies the multiplicity-free primitive-coordinate product
bound from `R324IntegratedMultiBlockCoordinates`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-! ## Realized refined representatives -/

/-- Membership of a residual signature supplies an actual contraction in
the corresponding refined fibre. -/
theorem momentRefinedContractionFiber_nonempty_of_mem
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (hr : r ∈ momentResidualChainSignaturesAt m s) :
    (momentRefinedContractionFiber m s r).Nonempty := by
  obtain ⟨e, he, her⟩ :=
    Finset.mem_image.mp hr
  refine ⟨e, ?_⟩
  rw [mem_momentRefinedContractionFiber]
  exact
    ⟨mem_momentContractionFiber.mp he, her⟩

/-- Canonical representative of a realized residual-refined fibre.  Its
value outside that realized fibre is irrelevant. -/
def r324RefinedContractionRepresentative
    (m : ℕ)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    MomentContraction m :=
  if hr : r ∈ momentResidualChainSignaturesAt m s then
    Classical.choose
      (momentRefinedContractionFiber_nonempty_of_mem hr)
  else default

theorem r324RefinedContractionRepresentative_mem
    {m : ℕ}
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (hr : r ∈ momentResidualChainSignaturesAt m s) :
    r324RefinedContractionRepresentative m s r ∈
      momentRefinedContractionFiber m s r := by
  unfold r324RefinedContractionRepresentative
  rw [dif_pos hr]
  exact
    Classical.choose_spec
      (momentRefinedContractionFiber_nonempty_of_mem hr)

/-! ## Norm of the actual grouped endpoint core -/

/-- The norm of the genuine refined endpoint core is exactly the product
of the two signed interior-profile norms and the nonnegative covariance
fibre sum.  The primitive-pairing sum remains inside the core until this
identity. -/
theorem norm_r324RefinedEndpointCore_eq
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (eSkeleton : MomentContraction m)
    (v : Fin (2 * m) → T4) :
    ‖r324RefinedEndpointCore
        ρ ε m s r eSkeleton v‖ =
      ‖r324RenormalizedInteriorCore eSkeleton.1
          (fun i => v (leftMomentIndex i))‖ *
        ‖r324RenormalizedInteriorCore eSkeleton.2.1
          (fun i => v (rightMomentIndex i))‖ *
        ∑ e ∈ momentRefinedContractionFiber m s r,
          primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing
              e.1 e.2.1 e.2.2) v := by
  have hsumNonneg :
      0 ≤ ∑ e ∈ momentRefinedContractionFiber m s r,
        primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing
            e.1 e.2.1 e.2.2) v :=
    Finset.sum_nonneg fun e _he =>
      primitiveCovarianceProduct_nonneg
        ρ ε m
        (momentCombinedPairing e.1 e.2.1 e.2.2) v
  have hcast :
      (∑ e ∈ momentRefinedContractionFiber m s r,
          (primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing
              e.1 e.2.1 e.2.2) v : ℂ)) =
        ((∑ e ∈ momentRefinedContractionFiber m s r,
          primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing
              e.1 e.2.1 e.2.2) v : ℝ) : ℂ) := by
    push_cast
    rfl
  unfold r324RefinedEndpointCore
  rw [norm_mul, norm_mul, hcast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hsumNonneg]

/-- The concrete nonnegative product supplied to the successive block
integrations for one realized refined fibre. -/
def r324RefinedPrimitiveBlockProductMajorant
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (_s _r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (eSkeleton eBlocks : MomentContraction m)
    (v : Fin (2 * m) → T4) : ℝ :=
  ‖r324RenormalizedInteriorCore eSkeleton.1
      (fun i => v (leftMomentIndex i))‖ *
    ‖r324RenormalizedInteriorCore eSkeleton.2.1
      (fun i => v (rightMomentIndex i))‖ *
    ∏ B :
        PrimitivePartitionBlockIndex
          (momentPrimitiveBlockPartition
            eBlocks.1 eBlocks.2.1 eBlocks.2.2),
      ∑ σ :
        {τ : PartialPairing
            (Fin (2 * residualBlockOrder B.1)) //
          τ ∈ primitiveFullPairings
            (residualBlockOrder B.1)},
        primitivePartitionBlockCovarianceFactor
          ρ ε
          (momentPrimitiveBlockPartition
            eBlocks.1 eBlocks.2.1 eBlocks.2.2)
          B σ v

theorem r324RefinedPrimitiveBlockProductMajorant_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (eSkeleton eBlocks : MomentContraction m)
    (v : Fin (2 * m) → T4) :
    0 ≤ r324RefinedPrimitiveBlockProductMajorant
      ρ ε m s r eSkeleton eBlocks v := by
  unfold r324RefinedPrimitiveBlockProductMajorant
  apply mul_nonneg
  · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · apply Finset.prod_nonneg
    intro B _hB
    apply Finset.sum_nonneg
    intro σ _hσ
    unfold primitivePartitionBlockCovarianceFactor
    exact
      primitiveCovarianceProduct_nonneg
        ρ ε (residualBlockOrder B.1) σ.1 _

/-- **Actual grouped-core block-product bound.**  The only enlargement is
from the realized refined fibre to all independent primitive coordinates on
its fixed concrete schedule; nonnegativity makes the direction exact and no
pairing-cardinality factor is paid. -/
theorem norm_r324RefinedEndpointCore_le_primitiveBlockProduct
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    {s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (eSkeleton : MomentContraction m)
    (eBlocks : MomentContraction m)
    (heBlocks :
      eBlocks ∈ momentRefinedContractionFiber m s r)
    (v : Fin (2 * m) → T4) :
    ‖r324RefinedEndpointCore
        ρ ε m s r eSkeleton v‖ ≤
      r324RefinedPrimitiveBlockProductMajorant
        ρ ε m s r eSkeleton eBlocks v := by
  rw [norm_r324RefinedEndpointCore_eq]
  unfold r324RefinedPrimitiveBlockProductMajorant
  exact
    mul_le_mul_of_nonneg_left
      (sum_refinedCovariance_le_prod_primitiveBlockSums
        ρ ε m eBlocks heBlocks v)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-! ## All realized refined fibres -/

/-- Sum of the genuine primitive-block product majorants over all residual
schedules in one fixed within-half signature. -/
def r324ResidualPrimitiveBlockProductMajorant
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (eSkeleton : MomentContraction m)
    (v : Fin (2 * m) → T4) : ℝ :=
  ∑ r ∈ momentResidualChainSignaturesAt m s,
    r324RefinedPrimitiveBlockProductMajorant
      ρ ε m s r eSkeleton
      (r324RefinedContractionRepresentative m s r) v

theorem r324ResidualEndpointCoreNormSum_le_blockProductMajorant
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (eSkeleton : MomentContraction m)
    (v : Fin (2 * m) → T4) :
    r324ResidualEndpointCoreNormSum
        ρ ε m s eSkeleton v ≤
      r324ResidualPrimitiveBlockProductMajorant
        ρ ε m s eSkeleton v := by
  unfold r324ResidualEndpointCoreNormSum
    r324ResidualPrimitiveBlockProductMajorant
  apply Finset.sum_le_sum
  intro r hr
  exact
    norm_r324RefinedEndpointCore_le_primitiveBlockProduct
      ρ ε m eSkeleton
      (r324RefinedContractionRepresentative m s r)
      (r324RefinedContractionRepresentative_mem hr) v

/-- Complete block-product majorant after summing all realized within-half
and residual signatures. -/
def r324AllRefinedPrimitiveBlockProductMajorant
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (v : Fin (2 * m) → T4) : ℝ :=
  ∑ s ∈ momentContractionSignatures m,
    r324ResidualPrimitiveBlockProductMajorant
      ρ ε m s
      (r324MomentSignatureRepresentative m s) v

theorem r324AllRefinedEndpointCoreNormSum_le_blockProductMajorant
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (v : Fin (2 * m) → T4) :
    r324AllRefinedEndpointCoreNormSum ρ ε m v ≤
      r324AllRefinedPrimitiveBlockProductMajorant
        ρ ε m v := by
  unfold r324AllRefinedEndpointCoreNormSum
    r324AllRefinedPrimitiveBlockProductMajorant
  apply Finset.sum_le_sum
  intro s _hs
  exact
    r324ResidualEndpointCoreNormSum_le_blockProductMajorant
      ρ ε m s (r324MomentSignatureRepresentative m s) v

end

end Anderson4D
