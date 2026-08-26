import Anderson4D.DetParametrix.Paper41_Renorm.R322ReductionClosure

/-!
# Terminal primitive block in signed R-324 phase A

When the selected primitive block is the whole current carrier there is no
right gap to update.  The complete primitive pairing coordinate is summed
and integrated directly, producing the Proposition 4.1 primitive kernel.
No `r322Collapse` or replacement-edge object occurs in this branch.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The whole-block integrand is the genuine primitive integrand -/

/-- Pointwise, the complete terminal coordinate of generalized closed `J`
integrands is exactly the complete Proposition 4.1 primitive-integrand
sum. -/
theorem sum_terminal_detJclosedIntegrandWith_eq_primitiveIntegrand
    (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (x : Fin (2 * n) → T4) :
    (∑ κB :
        {κ : PartialPairing (Fin (2 * n)) //
          κ ∈ primitiveFullPairings n},
      detJclosedIntegrandWith ρ ε (2 * n) κB.1 G x) =
      ∑ κ ∈ primitiveFullPairings n,
        primitiveIntegrand ρ ε n hn G κ x := by
  calc
    (∑ κB :
        {κ : PartialPairing (Fin (2 * n)) //
          κ ∈ primitiveFullPairings n},
      detJclosedIntegrandWith ρ ε (2 * n) κB.1 G x) =
        ∑ κ ∈ primitiveFullPairings n,
          detJclosedIntegrandWith ρ ε (2 * n) κ G x := by
      symm
      apply Finset.sum_subtype
      intro κ
      rfl
    _ =
        ∑ κ ∈ primitiveFullPairings n,
          primitiveIntegrand ρ ε n hn G κ x := by
      apply Finset.sum_congr rfl
      intro κ hκ
      obtain ⟨hfull, hprimitive⟩ :=
        mem_primitiveFullPairings.mp hκ
      exact
        detJclosedIntegrandWith_eq_primitiveIntegrand_of_full_primitive
          ρ ε n hn G κ hfull hprimitive x

/-! ## Exact signed terminal integration -/

/-- **Exact terminal phase-A identity.**

The finite primitive sum stays inside the whole-block integral.  After
finite-sum linearity it is exactly `primitiveKernel`; in particular no
adjacent edge is introduced or replaced. -/
theorem integral_sum_terminal_detJclosedIntegrandWith_eq_primitiveKernel
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4)
    (hint :
      ∀ κB :
          {κ : PartialPairing (Fin (2 * n)) //
            κ ∈ primitiveFullPairings n},
        Integrable
          (fun u : Fin (2 * n - 2) → T4 =>
            detJclosedIntegrandWith ρ ε (2 * n)
              κB.1 G (primitiveAssemble n hn z w u))
          (Measure.pi fun _ => paperMeasure)) :
    lamEps lam ε ^ (2 * n) *
        (∫ u : Fin (2 * n - 2) → T4,
          ∑ κB :
              {κ : PartialPairing (Fin (2 * n)) //
                κ ∈ primitiveFullPairings n},
            detJclosedIntegrandWith ρ ε (2 * n)
              κB.1 G (primitiveAssemble n hn z w u)
          ∂Measure.pi fun _ => paperMeasure) =
      primitiveKernel ρ lam ε n hn G z w := by
  calc
    lamEps lam ε ^ (2 * n) *
        (∫ u : Fin (2 * n - 2) → T4,
          ∑ κB :
              {κ : PartialPairing (Fin (2 * n)) //
                κ ∈ primitiveFullPairings n},
            detJclosedIntegrandWith ρ ε (2 * n)
              κB.1 G (primitiveAssemble n hn z w u)
          ∂Measure.pi fun _ => paperMeasure) =
        lamEps lam ε ^ (2 * n) *
          ∑ κB :
              {κ : PartialPairing (Fin (2 * n)) //
                κ ∈ primitiveFullPairings n},
            ∫ u : Fin (2 * n - 2) → T4,
              detJclosedIntegrandWith ρ ε (2 * n)
                κB.1 G (primitiveAssemble n hn z w u)
              ∂Measure.pi fun _ => paperMeasure := by
      rw [integral_finsetSum Finset.univ]
      intro κB _hκB
      exact hint κB
    _ =
        ∑ κB :
            {κ : PartialPairing (Fin (2 * n)) //
              κ ∈ primitiveFullPairings n},
          detJWith ρ lam ε n hn G κB.1 z w := by
      rw [Finset.mul_sum]
      rfl
    _ =
        ∑ κ ∈ primitiveFullPairings n,
          detJWith ρ lam ε n hn G κ z w := by
      symm
      apply Finset.sum_subtype
      intro κ
      rfl
    _ = primitiveKernel ρ lam ε n hn G z w :=
      sum_detJWith_primitive_eq_primitiveKernel
        ρ lam ε n hn G z w

/-! ## Direct Proposition 4.1 terminal output -/

/-- At the translated endpoint `w=0`, Proposition 4.1 applies directly to
the terminal block produced above. -/
theorem abs_integral_sum_terminal_detJclosedIntegrandWith_le_majorant
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (orderConstant supportConstant C : ℝ)
    (hprop41 :
      Prop41BoundPredicate ρ lam ε n hn G
        orderConstant supportConstant C)
    (hreg :
      PrimitiveEstimateRegime n lam ε
        orderConstant supportConstant C)
    (hinput : IsAdmissiblePrimitiveInput n G)
    (z : T4)
    (hint :
      ∀ κB :
          {κ : PartialPairing (Fin (2 * n)) //
            κ ∈ primitiveFullPairings n},
        Integrable
          (fun u : Fin (2 * n - 2) → T4 =>
            detJclosedIntegrandWith ρ ε (2 * n)
              κB.1 G (primitiveAssemble n hn z 0 u))
          (Measure.pi fun _ => paperMeasure)) :
    |lamEps lam ε ^ (2 * n) *
        (∫ u : Fin (2 * n - 2) → T4,
          ∑ κB :
              {κ : PartialPairing (Fin (2 * n)) //
                κ ∈ primitiveFullPairings n},
            detJclosedIntegrandWith ρ ε (2 * n)
              κB.1 G (primitiveAssemble n hn z 0 u)
          ∂Measure.pi fun _ => paperMeasure)| ≤
      primitiveKernelMajorant C lam ε
        supportConstant n z := by
  rw [
    integral_sum_terminal_detJclosedIntegrandWith_eq_primitiveKernel
      ρ lam ε n hn G z 0 hint]
  obtain ⟨_hmem, _hmemInserted, hbounds⟩ :=
    hprop41 hreg hinput
  simpa only [primitiveKernelDiff, sub_zero] using
    (hbounds z).1

end

end Anderson4D
