import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointBudgetClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324DetIntegrability
import Anderson4D.DetParametrix.Core.MeasurableAssembly

/-!
# Internal-variable majorants after the R-324 endpoint integrations

In the auxiliary endpoint-first Fubini normal form, the four external
Fourier variables have already been integrated in
`R324EndpointBudgetClosure`.  This file transports its pointwise estimate
through the remaining doubled internal-variable `lintegral`.  Working first
in `ℝ≥0∞` is intentional: it neither assumes nor hides the finiteness which
must ultimately be supplied by the successive Proposition 4.1 block
collapses.

This majorant is an auxiliary endpoint-budget and integrability statement,
not the signed paper-order route to the final R-324 bound: taking the
pointwise norm here loses the cancellations needed for those collapses.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-! ## Measurability of the actual grouped core -/

/-- The endpoint-independent Green core is measurable in its internal
variables. -/
theorem measurable_r324RenormalizedInteriorCore
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Measurable (r324RenormalizedInteriorCore κ) := by
  have hassemble :
      Measurable fun v : Fin m → T4 =>
        assemble (0 : T4) 0 v := by
    exact
      (measurable_assemble_prod m).comp
        (measurable_const.prodMk
          (measurable_const.prodMk measurable_id))
  unfold r324RenormalizedInteriorCore
  apply Finset.measurable_prod
  intro i _hi
  exact
    ((measurable_originalGreenEdge i).comp hassemble).sub
      ((measurable_extractedShortcutGreenEdge κ i).comp hassemble)

/-- The covariance product of a fixed doubled pairing is measurable in the
complete doubled internal tuple. -/
theorem measurable_primitiveCovarianceProduct
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin (2 * m))) :
    Measurable (primitiveCovarianceProduct ρ ε m κ) := by
  unfold primitiveCovarianceProduct
  apply Finset.measurable_prod
  intro i _hi
  exact
    (ρ.measurable_etaEpsT4 ε).comp
      ((measurable_pi_apply i).sub
        (measurable_pi_apply (κ i)))

/-- A complete residual-refined core is measurable.  In particular, the
finite primitive-pairing fibre is still summed before the norm. -/
theorem measurable_r324RefinedEndpointCore
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m) :
    Measurable (r324RefinedEndpointCore ρ ε m s r e₀) := by
  unfold r324RefinedEndpointCore
  have hleft :
      Measurable fun v : Fin (2 * m) → T4 =>
        r324RenormalizedInteriorCore e₀.1
          (fun i => v (leftMomentIndex i)) := by
    exact
      (measurable_r324RenormalizedInteriorCore e₀.1).comp
        (measurable_pi_lambda _ fun i =>
          measurable_pi_apply (leftMomentIndex i))
  have hright :
      Measurable fun v : Fin (2 * m) → T4 =>
        r324RenormalizedInteriorCore e₀.2.1
          (fun i => v (rightMomentIndex i)) := by
    exact
      (measurable_r324RenormalizedInteriorCore e₀.2.1).comp
        (measurable_pi_lambda _ fun i =>
          measurable_pi_apply (rightMomentIndex i))
  apply (hleft.mul hright).mul
  apply Finset.measurable_sum
  intro e _he
  exact
    (measurable_primitiveCovarianceProduct ρ ε m
      (momentCombinedPairing e.1 e.2.1 e.2.2)).complex_ofReal

/-- The complete nonnegative grouped-core budget is measurable. -/
theorem measurable_r324AllRefinedEndpointCoreNormSum
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) :
    Measurable (r324AllRefinedEndpointCoreNormSum ρ ε m) := by
  unfold r324AllRefinedEndpointCoreNormSum
    r324ResidualEndpointCoreNormSum
  apply Finset.measurable_sum
  intro s _hs
  apply Finset.measurable_sum
  intro r _hr
  exact
    (measurable_r324RefinedEndpointCore
      ρ ε m s r
      (r324MomentSignatureRepresentative m s)).norm

/-! ## Tonelli-safe endpoint budget -/

/-- The sacrificed endpoint-coefficient budget integrated over all doubled
internal variables. -/
def r324SacrificedEndpointCoefficientLIntegral
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) : ℝ≥0∞ :=
  ∫⁻ v : Fin (2 * m) → T4,
    ENNReal.ofReal
      (ε⁻¹ ^ (8 : ℕ) *
        r324AllRefinedEndpointCoefficientNormSum
          ρ ε m α β v)
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

/-- The matching internal grouped-core `L¹` budget. -/
def r324EndpointCoreLIntegral
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ v : Fin (2 * m) → T4,
    ENNReal.ofReal
      (r324AllRefinedEndpointCoreNormSum ρ ε m v)
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

/-- **Integrated four-endpoint estimate.**  This is the exact Tonelli-safe
bridge from the endpoint-first calculation to the remaining Proposition 4.1
majorant problem.  It remains valid before finiteness of the core budget is
known. -/
theorem r324SacrificedEndpointCoefficientLIntegral_le
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4) :
    r324SacrificedEndpointCoefficientLIntegral
        ρ ε m α β ≤
      ENNReal.ofReal (16 * r324EndpointLoss ε α β) *
        r324EndpointCoreLIntegral ρ ε m := by
  have hscale :
      0 ≤ 16 * r324EndpointLoss ε α β :=
    mul_nonneg (by norm_num)
      (r324EndpointLoss_nonneg ε α β)
  unfold r324SacrificedEndpointCoefficientLIntegral
    r324EndpointCoreLIntegral
  calc
    (∫⁻ v : Fin (2 * m) → T4,
        ENNReal.ofReal
          (ε⁻¹ ^ (8 : ℕ) *
            r324AllRefinedEndpointCoefficientNormSum
              ρ ε m α β v)
        ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure) ≤
      ∫⁻ v : Fin (2 * m) → T4,
        ENNReal.ofReal
          ((16 * r324EndpointLoss ε α β) *
            r324AllRefinedEndpointCoreNormSum ρ ε m v)
        ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure := by
      apply lintegral_mono
      intro v
      exact ENNReal.ofReal_le_ofReal
        (sacrificed_r324AllRefinedEndpointCoefficientNormSum_le
          ρ ε m hm α β v)
    _ =
      ∫⁻ v : Fin (2 * m) → T4,
        ENNReal.ofReal (16 * r324EndpointLoss ε α β) *
          ENNReal.ofReal
            (r324AllRefinedEndpointCoreNormSum ρ ε m v)
        ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure := by
      apply lintegral_congr
      intro v
      rw [ENNReal.ofReal_mul hscale]
    _ =
      ENNReal.ofReal (16 * r324EndpointLoss ε α β) *
        (∫⁻ v : Fin (2 * m) → T4,
          ENNReal.ofReal
            (r324AllRefinedEndpointCoreNormSum ρ ε m v)
          ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      rw [lintegral_const_mul'']
      exact
        (measurable_r324AllRefinedEndpointCoreNormSum
          ρ ε m).ennreal_ofReal.aemeasurable

/-- Any finite Proposition 4.1 majorant for the grouped core immediately
gives a finite endpoint budget. -/
theorem r324SacrificedEndpointCoefficientLIntegral_ne_top
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4)
    (hcore : r324EndpointCoreLIntegral ρ ε m ≠ ∞) :
    r324SacrificedEndpointCoefficientLIntegral
        ρ ε m α β ≠ ∞ := by
  apply ne_of_lt
  refine lt_of_le_of_lt
    (r324SacrificedEndpointCoefficientLIntegral_le
      ρ ε m hm α β) ?_
  exact ENNReal.mul_lt_top
    ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.mpr hcore)

end

end Anderson4D
