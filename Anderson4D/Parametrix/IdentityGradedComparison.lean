import Anderson4D.Parametrix.IdentityRightKernelSymmetry

/-!
# Comparing the pairing and graded parametrix expansions

The pairing expansion is the paper's definition of `Pₙ`; the graded
word expansion makes kernel transposition transparent.  This file
packages only the analytic Fubini hypotheses already used by the
pairing proof and proves that the two expansions satisfy the same
recurrence.  Consequently the actual pairing kernel is symmetric, and
the right identity follows from the proved left identity without
duplicating the head-case combinatorics.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-- Analytic ledger needed to compare the paper's pairing parametrix
with the graded resolvent-word expansion off the endpoint diagonal.
Every field is a concrete integrability condition consumed by an
existing Fubini theorem.  The restriction `x ≠ y` is essential in four
dimensions: already `G(x-z)G(z-y)` is not integrable when `x = y`. -/
structure ParametrixIdentityIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) : Prop where
  source :
    ∀ n x y, x ≠ y →
      LeftOrderSourceIntegrability
        M ρ lam ε n x y ω
  split :
    ∀ n (κ : PartialPairing (Fin n)) x y, x ≠ y →
      LeftPairingSplitIntegrability
        M ρ ε n κ x y ω
  creation :
    ∀ n (κ : PartialPairing (Fin n)) x y, x ≠ y →
      Integrable
        (fun u : Fin (n + 1) → T4 =>
          randIntegrand M ρ ε
            (wickHeadEquiv n (Sum.inl κ))
            (assemble x y u) ω)
        (Measure.pi fun _ => paperMeasure)
  noPrefix :
    ∀ n
      (d :
        {d : MarkedSingle (Fin n) //
          ¬markedHasHeadPrefix d}) x y, x ≠ y →
      Integrable
        (fun u : Fin (n + 1) → T4 =>
          randIntegrand M ρ ε
            (wickHeadEquiv n (Sum.inr d.1))
            (assemble x y u) ω)
        (Measure.pi fun _ => paperMeasure)
  caseThree :
    ∀ n x y, x ≠ y →
      LeftWithPrefixCaseThreeIntegrability
        M ρ lam ε n x y ω
  graded :
    ∀ n x y (k : Fin (n + 1))
      (c : Composition (n - k.val)), x ≠ y →
      RenormWordIntegrable M ρ lam ε
        ((k.val + 1) :: c.blocks) x y ω

/-- The concrete analytic ledger discharges every hypothesis of the
fixed-order left pairing recurrence. -/
theorem
    leftParametrixNoiseSource_eq_parametrix_succ_add_counterterms_of_ledger
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hint :
      ParametrixIdentityIntegrability
        M ρ lam ε ω)
    (n : ℕ) (x y : T4) (hxy : x ≠ y) :
    leftParametrixNoiseSource
        M ρ lam ε n x y ω =
      parametrixP M ρ lam ε (n + 1) x y ω +
        leftOrderCountertermSum
          M ρ lam ε n x y ω := by
  apply
    leftParametrixNoiseSource_eq_parametrix_succ_add_counterterms
      M ρ lam ε n x y ω
      (hint.source n x y hxy)
      (fun κ => hint.split n κ x y hxy)
      (fun κ => hint.creation n κ x y hxy)
      (fun d => hint.noPrefix n d x y hxy)
  exact
    leftWithPrefixContractionSum_eq_randRISum_add_countertermSum
      M ρ lam ε n x y ω
      (hint.caseThree n x y hxy)

/-- Under the explicit Fubini ledger, the paper's pairing expansion is
exactly the graded word expansion. -/
theorem parametrixP_eq_gradedParametrix_of_integrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hint :
      ParametrixIdentityIntegrability
        M ρ lam ε ω) :
    ∀ n x y, x ≠ y →
      parametrixP M ρ lam ε n x y ω =
        gradedParametrix M ρ lam ε n x y ω := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
    cases order with
    | zero =>
      intro x y _hxy
      rw [parametrixP_zero, gradedParametrix_zero]
    | succ n =>
      intro x y hxy
      have hactual :=
        leftParametrixNoiseSource_eq_parametrix_succ_add_counterterms_of_ledger
          M ρ lam ε ω hint n x y hxy
      have hgraded :=
        gradedParametrix_succ_eq_noise_sub_counterterms
          M ρ lam ε n x y ω
          (fun k c => hint.graded n x y k c hxy)
      have hsource :
          leftParametrixNoiseSource
              M ρ lam ε n x y ω =
            gradedParametrixNoiseSource
              M ρ lam ε n x y ω := by
        unfold leftParametrixNoiseSource
        unfold gradedParametrixNoiseSource
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards
          [compl_mem_ae_iff.mpr
            (paperMeasure_singleton y)] with z hz
        have hzy : z ≠ y := by
          simpa only [Set.mem_compl_iff,
            Set.mem_singleton_iff] using hz
        rw [ih n (by omega) z y hzy]
        ring
      have hcounter :
          leftOrderCountertermSum
              M ρ lam ε n x y ω =
            gradedOrderCountertermSum
              M ρ lam ε n x y ω := by
        unfold leftOrderCountertermSum
        unfold gradedOrderCountertermSum
        apply Finset.sum_congr rfl
        intro q hq
        rw [caseThreeCountertermBlock_eq]
        unfold gradedCountertermBlock
        congr 1
        apply integral_congr_ae
        filter_upwards
          [compl_mem_ae_iff.mpr
            (paperMeasure_singleton y)] with z hz
        have hzy : z ≠ y := by
          simpa only [Set.mem_compl_iff,
            Set.mem_singleton_iff] using hz
        have hqbounds := Finset.mem_Icc.mp hq
        have hrlt :
            n + 1 - 2 * q < n + 1 := by
          omega
        rw [ih (n + 1 - 2 * q) hrlt z y hzy]
      calc
        parametrixP M ρ lam ε (n + 1) x y ω =
            leftParametrixNoiseSource
                M ρ lam ε n x y ω -
              leftOrderCountertermSum
                M ρ lam ε n x y ω := by
                  linarith
        _ =
            gradedParametrixNoiseSource
                M ρ lam ε n x y ω -
              gradedOrderCountertermSum
                M ρ lam ε n x y ω := by
                  rw [hsource, hcounter]
        _ =
            gradedParametrix M ρ lam ε (n + 1)
              x y ω :=
          hgraded.symm

/-- The actual pairing kernel is symmetric at every order once the
concrete Fubini ledger is available. -/
theorem parametrixKernelSymmetric_of_integrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hint :
      ParametrixIdentityIntegrability
        M ρ lam ε ω)
    (n : ℕ) :
    ParametrixKernelSymmetric
      M ρ lam ε n ω := by
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  calc
    parametrixP M ρ lam ε n x y ω =
        gradedParametrix M ρ lam ε n x y ω :=
      parametrixP_eq_gradedParametrix_of_integrability
        M ρ lam ε ω hint n x y hxy
    _ =
        gradedParametrix M ρ lam ε n y x ω :=
      gradedParametrix_symmetric
        M ρ lam ε n x y ω
    _ =
        parametrixP M ρ lam ε n y x ω :=
      (parametrixP_eq_gradedParametrix_of_integrability
        M ρ lam ε ω hint n y x (Ne.symm hxy)).symm

/-- Symmetry is simultaneously available through every finite
truncation order. -/
theorem parametrixKernelSymmetricThrough_of_integrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hint :
      ParametrixIdentityIntegrability
        M ρ lam ε ω)
    (N : ℕ) :
    ParametrixKernelSymmetricThrough
      M ρ lam ε N ω := by
  intro n _hn
  exact
    parametrixKernelSymmetric_of_integrability
      M ρ lam ε ω hint n

/-- Paper (3.17), the fixed-order right parametrix identity, follows
from the left head-case proof and the now-proved kernel symmetry. -/
theorem
    rightParametrixNoiseSource_eq_parametrix_succ_add_counterterms_of_ledger
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hint :
      ParametrixIdentityIntegrability
        M ρ lam ε ω)
    (n : ℕ) (x y : T4) (hxy : x ≠ y) :
    rightParametrixNoiseSource
        M ρ lam ε n x y ω =
      parametrixP M ρ lam ε (n + 1) x y ω +
        rightOrderCountertermSum
          M ρ lam ε n x y ω := by
  apply
    rightParametrixNoiseSource_eq_parametrix_succ_add_counterterms_of_left
      M ρ lam ε n x y ω
      (parametrixKernelSymmetricThrough_of_integrability
        M ρ lam ε ω hint (n + 1))
  exact
    leftParametrixNoiseSource_eq_parametrix_succ_add_counterterms_of_ledger
      M ρ lam ε ω hint n y x (Ne.symm hxy)

/-- **Proposition 3.4, paper (3.16)--(3.17), in the bounded
preconditioned kernel form used by the formalization.**

The first conjunct is (3.16) after applying the Green operator on the
left; the second is the mirrored right identity.  `hint` contains only
the concrete Fubini/integrability ledger needed to interpret the
totalized kernel integrals.  No parametrix identity or estimate is a
field of that ledger. -/
theorem xi_comp_parametrix
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hint :
      ParametrixIdentityIntegrability
        M ρ lam ε ω)
    (n : ℕ) (x y : T4) (hxy : x ≠ y) :
    (leftParametrixNoiseSource
          M ρ lam ε n x y ω =
        parametrixP M ρ lam ε (n + 1) x y ω +
          leftOrderCountertermSum
            M ρ lam ε n x y ω) ∧
      (rightParametrixNoiseSource
          M ρ lam ε n x y ω =
        parametrixP M ρ lam ε (n + 1) x y ω +
          rightOrderCountertermSum
            M ρ lam ε n x y ω) := by
  exact
    ⟨leftParametrixNoiseSource_eq_parametrix_succ_add_counterterms_of_ledger
        M ρ lam ε ω hint n x y hxy,
      rightParametrixNoiseSource_eq_parametrix_succ_add_counterterms_of_ledger
        M ρ lam ε ω hint n x y hxy⟩

/-- The complete left preconditioned remainder identity (3.20)--(3.21)
under the global concrete integrability ledger. -/
theorem
    leftPreconditionedParametrixAction_eq_green_add_remainder_of_ledger
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hint :
      ParametrixIdentityIntegrability
        M ρ lam ε ω)
    (A : ℕ) (x y : T4) (hxy : x ≠ y) :
    leftPreconditionedParametrixAction
        M ρ lam ε A x y ω =
      greenFn (x - y) +
        leftPreconditionedRemainder
          M ρ lam ε A x y ω := by
  apply
    leftPreconditionedParametrixAction_eq_green_add_remainder_of_integrability
      M ρ lam ε A x y ω
  · intro n _hn
    exact hint.source n x y hxy
  · intro n _hn κ
    exact hint.split n κ x y hxy
  · intro n _hn κ
    exact hint.creation n κ x y hxy
  · intro n _hn d
    exact hint.noPrefix n d x y hxy
  · intro n _hn
    exact hint.caseThree n x y hxy

/-- The complete right preconditioned remainder identity
(3.20)--(3.21), with no separate right head-case assumptions. -/
theorem
    rightPreconditionedParametrixAction_eq_green_add_remainder_of_ledger
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hint :
      ParametrixIdentityIntegrability
        M ρ lam ε ω)
    (A : ℕ) (x y : T4) (hxy : x ≠ y) :
    rightPreconditionedParametrixAction
        M ρ lam ε A x y ω =
      greenFn (x - y) +
        rightPreconditionedRemainder
          M ρ lam ε A x y ω := by
  apply
    rightPreconditionedParametrixAction_eq_green_add_remainder
      M ρ lam ε A x y ω
  intro m hm
  have hmBounds := Finset.mem_Icc.mp hm
  have hsucc : m - 1 + 1 = m := by
    omega
  have horder :=
    rightParametrixNoiseSource_eq_parametrix_succ_add_counterterms_of_ledger
      M ρ lam ε ω hint (m - 1) x y hxy
  simpa only [rightOrderCountertermSum, hsucc] using horder

end PartialPairing

end

end Anderson4D
