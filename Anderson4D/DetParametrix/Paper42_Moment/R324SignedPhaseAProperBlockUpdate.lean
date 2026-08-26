import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhaseAOneBlockUpdate

/-!
# Proper selected-block replacement in signed R-324 phase A

This module records the analytic end of a genuine proper selected-block
update.  The complete primitive pairing coordinate is evaluated at its two
actual endpoints, translated to the difference kernel used by
`r322CollapseIntegrand`, and then replaced by the named updated edge.

The subsequent R-324 theorem applies this identity only after identifying
the corresponding factors of the original reconstructed deterministic
integrand.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The complete primitive coordinate at two actual endpoints -/

/-- Translation invariance identifies the complete primitive coordinate
at `(z,w)` with the selected difference kernel at `z-w`. -/
theorem sum_detJWith_eq_r322SelectedPrimitiveKernelSum_sub
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) :
    (∑ κB :
        {κ : PartialPairing (Fin (2 * n)) //
          κ ∈ primitiveFullPairings n},
      detJWith ρ lam ε n hn G κB.1 z w) =
      r322SelectedPrimitiveKernelSum
        ρ lam ε n hn G (z - w) := by
  unfold r322SelectedPrimitiveKernelSum
  calc
    (∑ κB :
        {κ : PartialPairing (Fin (2 * n)) //
          κ ∈ primitiveFullPairings n},
      detJWith ρ lam ε n hn G κB.1 z w) =
        ∑ κ ∈ primitiveFullPairings n,
          detJWith ρ lam ε n hn G κ z w := by
      symm
      apply Finset.sum_subtype
      intro κ
      rfl
    _ =
        ∑ κ ∈ primitiveFullPairings n,
          detJWith ρ lam ε n hn G κ (z - w) 0 := by
      apply Finset.sum_congr rfl
      intro κ _hκ
      exact detJWith_eq_diff
        ρ lam ε n hn G κ z w

/-! ## Exact signed proper-edge update -/

/-- The endpoint integral containing the complete primitive coordinate at
its actual endpoints is exactly the existing selected-kernel collapse. -/
theorem integral_completePrimitiveAtEndpoints_eq_selectedPrimitiveInner
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (Gp Gr : T4 → ℝ) (u : T4) :
    (∫ p : T4 × T4,
        Gp (u - p.1) *
          (∑ κB :
              {κ : PartialPairing (Fin (2 * n)) //
                κ ∈ primitiveFullPairings n},
            detJWith ρ lam ε n hn G κB.1 p.1 p.2) *
          (Gr p.2 - Gr p.1)
        ∂(paperMeasure.prod paperMeasure)) =
      ∫ p : T4 × T4,
        r322CollapseIntegrand Gp
          (r322SelectedPrimitiveKernelSum
            ρ lam ε n hn G)
          Gr u p
        ∂(paperMeasure.prod paperMeasure) := by
  apply integral_congr_ae
  filter_upwards with p
  rw [sum_detJWith_eq_r322SelectedPrimitiveKernelSum_sub]
  rfl

/-- **Exact generalized proper-block replacement.**

The selected pairing sum and both endpoint integrations remain signed.
The conclusion is the value of the named updated edge, so the result can be
substituted into the actual R-324 outer coordinate without changing any
other edge. -/
theorem integral_completePrimitiveAtEndpoints_eq_replacementEdge
    {ι : Type*} [DecidableEq ι]
    (edges : ι → T4 → ℝ) (slot : ι)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (Gp Gr : T4 → ℝ) (u : T4) :
    (∫ p : T4 × T4,
        Gp (u - p.1) *
          (∑ κB :
              {κ : PartialPairing (Fin (2 * n)) //
                κ ∈ primitiveFullPairings n},
            detJWith ρ lam ε n hn G κB.1 p.1 p.2) *
          (Gr p.2 - Gr p.1)
        ∂(paperMeasure.prod paperMeasure)) =
      r322ReplaceEdge edges slot Gp
        (primitiveKernelDiff ρ lam ε n hn G)
        Gr slot u := by
  rw [
    integral_completePrimitiveAtEndpoints_eq_selectedPrimitiveInner]
  exact selectedPrimitiveInnerIntegral_eq_replacementEdge
    edges slot ρ lam ε n hn G Gp Gr u

end

end Anderson4D
