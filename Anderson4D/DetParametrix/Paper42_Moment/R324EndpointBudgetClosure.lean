import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointFiberClosure

/-!
# Endpoint budgets for grouped refined R-324 fibres

The preceding module rewrites a complete residual-refined fibre as four
separated external Green legs times one internal core.  Here we perform the
four external Fourier integrations and derive the endpoint budget, still
without moving a norm through the primitive-pairing sum contained in the
core.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Endpoint-first coefficient of one refined fibre at fixed internal
variables. -/
def r324RefinedEndpointCoefficient
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (v : Fin (2 * m) → T4) : ℂ :=
  ∫ x, ∫ y, ∫ z, ∫ w,
    momentRefinedPhysicalIntegrand
      ρ ε m α β s r x y z w v
    ∂paperMeasure ∂paperMeasure
    ∂paperMeasure ∂paperMeasure

/-- Exact coefficient formula.  `he₀` is only the certificate selecting a
common Green skeleton for the realized within-half signature. -/
theorem r324RefinedEndpointCoefficient_eq
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentContractionFiber m s)
    (v : Fin (2 * m) → T4) :
    r324RefinedEndpointCoefficient
        ρ ε m α β s r v =
      r324EndpointCoefficient α
          ((r324ContractionEndpointAnchors hm e₀ v) 0).1
          ((r324ContractionEndpointAnchors hm e₀ v) 0).2
          ((r324ContractionEndpointFlags e₀) 0) *
        (r324EndpointCoefficient β
          ((r324ContractionEndpointAnchors hm e₀ v) 1).1
          ((r324ContractionEndpointAnchors hm e₀ v) 1).2
          ((r324ContractionEndpointFlags e₀) 1) *
        (r324EndpointCoefficient (-α)
          ((r324ContractionEndpointAnchors hm e₀ v) 2).1
          ((r324ContractionEndpointAnchors hm e₀ v) 2).2
          ((r324ContractionEndpointFlags e₀) 2) *
        (r324EndpointCoefficient (-β)
          ((r324ContractionEndpointAnchors hm e₀ v) 3).1
          ((r324ContractionEndpointAnchors hm e₀ v) 3).2
          ((r324ContractionEndpointFlags e₀) 3) *
          r324RefinedEndpointCore ρ ε m s r e₀ v))) := by
  unfold r324RefinedEndpointCoefficient
  have hrewrite :
      (∫ x, ∫ y, ∫ z, ∫ w,
          momentRefinedPhysicalIntegrand
            ρ ε m α β s r x y z w v
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure) =
        ∫ x, ∫ y, ∫ z, ∫ w,
          r324EndpointSeparatedIntegrand α β
            (r324ContractionEndpointAnchors hm e₀ v)
            (r324ContractionEndpointFlags e₀)
            (r324RefinedEndpointCore ρ ε m s r e₀ v)
            x y z w
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    apply integral_congr_ae
    filter_upwards with z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w =>
      momentRefinedPhysicalIntegrand_eq_endpointSeparated
        ρ ε m hm α β s r e₀ he₀ x y z w v
  rw [hrewrite,
    integral_r324EndpointSeparatedIntegrand]

/-- Norm of the fixed-internal-variable coefficient: all primitive-pairing
cancellation remains inside the norm of the refined core. -/
theorem norm_r324RefinedEndpointCoefficient_eq
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentContractionFiber m s)
    (v : Fin (2 * m) → T4) :
    ‖r324RefinedEndpointCoefficient
        ρ ε m α β s r v‖ =
      r324FourEndpointCoefficientWeight α β
          (r324ContractionEndpointAnchors hm e₀ v)
          (r324ContractionEndpointFlags e₀) *
        ‖r324RefinedEndpointCore ρ ε m s r e₀ v‖ := by
  rw [r324RefinedEndpointCoefficient_eq
    ρ ε m hm α β s r e₀ he₀ v]
  unfold r324FourEndpointCoefficientWeight
  simp only [norm_mul]
  ring

/-- The paper's complete four-endpoint loss at fixed internal variables.
The `ε⁻⁸` factor is exactly the four ordinary-versus-inserted sacrifices. -/
theorem sacrificed_norm_r324RefinedEndpointCoefficient_le
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentContractionFiber m s)
    (v : Fin (2 * m) → T4) :
    ε⁻¹ ^ (8 : ℕ) *
        ‖r324RefinedEndpointCoefficient
          ρ ε m α β s r v‖ ≤
      (16 * r324EndpointLoss ε α β) *
        ‖r324RefinedEndpointCore ρ ε m s r e₀ v‖ := by
  rw [norm_r324RefinedEndpointCoefficient_eq
    ρ ε m hm α β s r e₀ he₀ v]
  have hcore :
      0 ≤ ‖r324RefinedEndpointCore
        ρ ε m s r e₀ v‖ :=
    norm_nonneg _
  calc
    ε⁻¹ ^ (8 : ℕ) *
          (r324FourEndpointCoefficientWeight α β
              (r324ContractionEndpointAnchors hm e₀ v)
              (r324ContractionEndpointFlags e₀) *
            ‖r324RefinedEndpointCore ρ ε m s r e₀ v‖) =
        r324SacrificedEndpointCoefficientWeight ε α β
            (r324ContractionEndpointAnchors hm e₀ v)
            (r324ContractionEndpointFlags e₀) *
          ‖r324RefinedEndpointCore ρ ε m s r e₀ v‖ := by
      unfold r324SacrificedEndpointCoefficientWeight
      ring
    _ ≤ (16 * r324EndpointLoss ε α β) *
          ‖r324RefinedEndpointCore ρ ε m s r e₀ v‖ :=
      mul_le_mul_of_nonneg_right
        (r324SacrificedEndpointCoefficientWeight_le
          ε α β
          (r324ContractionEndpointAnchors hm e₀ v)
          (r324ContractionEndpointFlags e₀))
        hcore

/-! ## Finite aggregation over the actual refined signatures -/

/-- Sum of endpoint-first coefficient norms over all residual schedules
inside one realized within-half signature. -/
def r324ResidualEndpointCoefficientNormSum
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (v : Fin (2 * m) → T4) : ℝ :=
  ∑ r ∈ momentResidualChainSignaturesAt m s,
    ‖r324RefinedEndpointCoefficient
      ρ ε m α β s r v‖

/-- Matching grouped-core budget.  The norm is outside the complete
primitive-pairing sum in each residual-refined fibre. -/
def r324ResidualEndpointCoreNormSum
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (v : Fin (2 * m) → T4) : ℝ :=
  ∑ r ∈ momentResidualChainSignaturesAt m s,
    ‖r324RefinedEndpointCore ρ ε m s r e₀ v‖

theorem r324ResidualEndpointCoreNormSum_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (v : Fin (2 * m) → T4) :
    0 ≤ r324ResidualEndpointCoreNormSum
      ρ ε m s e₀ v := by
  unfold r324ResidualEndpointCoreNormSum
  positivity

/-- The four-leg endpoint estimate summed over every actual residual
schedule.  No residual-cardinality factor appears: both sides contain the
same finite sum. -/
theorem sacrificed_r324ResidualEndpointCoefficientNormSum_le
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentContractionFiber m s)
    (v : Fin (2 * m) → T4) :
    ε⁻¹ ^ (8 : ℕ) *
        r324ResidualEndpointCoefficientNormSum
          ρ ε m α β s v ≤
      (16 * r324EndpointLoss ε α β) *
        r324ResidualEndpointCoreNormSum
          ρ ε m s e₀ v := by
  unfold r324ResidualEndpointCoefficientNormSum
    r324ResidualEndpointCoreNormSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  exact sacrificed_norm_r324RefinedEndpointCoefficient_le
    ρ ε m hm α β s r e₀ he₀ v

/-! ## Aggregation over every realized within-half signature -/

/-- Canonical representative of a realized moment signature.  Outside the
realized signature finset the value is irrelevant. -/
def r324MomentSignatureRepresentative
    (m : ℕ)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    MomentContraction m :=
  if hs : s ∈ momentContractionSignatures m then
    Classical.choose
      (momentContractionFiber_nonempty_iff_mem_signatures.mpr hs)
  else default

theorem r324MomentSignatureRepresentative_mem
    (m : ℕ)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m) :
    r324MomentSignatureRepresentative m s ∈
      momentContractionFiber m s := by
  unfold r324MomentSignatureRepresentative
  rw [dif_pos hs]
  exact
    Classical.choose_spec
      (momentContractionFiber_nonempty_iff_mem_signatures.mpr hs)

/-- Complete pointwise endpoint-first norm budget over every realized
refined fibre. -/
def r324AllRefinedEndpointCoefficientNormSum
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4)
    (v : Fin (2 * m) → T4) : ℝ :=
  ∑ s ∈ momentContractionSignatures m,
    r324ResidualEndpointCoefficientNormSum
      ρ ε m α β s v

/-- Complete matching grouped-core budget. -/
def r324AllRefinedEndpointCoreNormSum
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (v : Fin (2 * m) → T4) : ℝ :=
  ∑ s ∈ momentContractionSignatures m,
    r324ResidualEndpointCoreNormSum
      ρ ε m s
      (r324MomentSignatureRepresentative m s) v

theorem r324AllRefinedEndpointCoreNormSum_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (v : Fin (2 * m) → T4) :
    0 ≤ r324AllRefinedEndpointCoreNormSum
      ρ ε m v := by
  unfold r324AllRefinedEndpointCoreNormSum
  exact Finset.sum_nonneg fun s _hs =>
    r324ResidualEndpointCoreNormSum_nonneg
      ρ ε m s (r324MomentSignatureRepresentative m s) v

/-- **Concrete aggregate endpoint budget.**  This is the direct
`weightBudget ≤ amplitude * r324EndpointLoss` shape before the remaining
internal-variable integral and primitive block bounds are applied. -/
theorem sacrificed_r324AllRefinedEndpointCoefficientNormSum_le
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4)
    (v : Fin (2 * m) → T4) :
    ε⁻¹ ^ (8 : ℕ) *
        r324AllRefinedEndpointCoefficientNormSum
          ρ ε m α β v ≤
      (16 * r324EndpointLoss ε α β) *
        r324AllRefinedEndpointCoreNormSum
          ρ ε m v := by
  unfold r324AllRefinedEndpointCoefficientNormSum
    r324AllRefinedEndpointCoreNormSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  exact
    sacrificed_r324ResidualEndpointCoefficientNormSum_le
      ρ ε m hm α β s
      (r324MomentSignatureRepresentative m s)
      (r324MomentSignatureRepresentative_mem m s hs) v

end

end Anderson4D
