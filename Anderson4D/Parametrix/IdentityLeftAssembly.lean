import Anderson4D.Parametrix.IdentityRemainder

/-!
# Assembly of the left parametrix identity

This module combines the already closed head-single and no-prefix
branches with one exact statement for the with-prefix branch.  It
produces the paper-facing, free-Green-preconditioned form of
Proposition 3.4.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-- The still-unreduced with-prefix Wick-contraction sum at old order
`n`. -/
def leftWithPrefixContractionSum
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∑ d :
      {d : MarkedSingle (Fin n) //
        markedHasHeadPrefix d},
    headPairedContractionContribution
      M ρ lam ε n d.1 x y ω

/-- The ambient random kernels whose new head belongs to a fully
paired prefix. -/
def leftWithPrefixRandRISum
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∑ κ :
      {κ : PartialPairing (Fin (n + 1)) //
        HeadPairedWithPrefix κ},
    randRI M ρ lam ε (n + 1)
      κ.1 x y ω

/-- All fixed-prefix counterterm blocks at new order `n+1`, in exactly
the range of paper (3.16). -/
def leftOrderCountertermSum
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
    caseThreeCountertermBlock
      M ρ lam ε q (n + 1 - 2 * q)
        x y ω

/-- Once the with-prefix Wick source has been identified with its
ambient random kernels plus fixed-prefix counterterms, the three head
classes assemble to `P_{n+1}` with multiplicity one. -/
theorem leftNoiseOrderContribution_eq_parametrix_succ_add_counterterms
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hsplit :
      ∀ κ : PartialPairing (Fin n),
        LeftPairingSplitIntegrability
          M ρ ε n κ x y ω)
    (hcreation :
      ∀ κ : PartialPairing (Fin n),
        Integrable
          (fun u : Fin (n + 1) → T4 =>
            randIntegrand M ρ ε
              (wickHeadEquiv n (Sum.inl κ))
              (assemble x y u) ω)
          (Measure.pi fun _ => paperMeasure))
    (hnoPrefix :
      ∀ d :
          {d : MarkedSingle (Fin n) //
            ¬markedHasHeadPrefix d},
        Integrable
          (fun u : Fin (n + 1) → T4 =>
            randIntegrand M ρ ε
              (wickHeadEquiv n
                (Sum.inr d.1))
              (assemble x y u) ω)
          (Measure.pi fun _ => paperMeasure))
    (hcaseThree :
      leftWithPrefixContractionSum
          M ρ lam ε n x y ω =
        leftWithPrefixRandRISum
            M ρ lam ε n x y ω +
          leftOrderCountertermSum
            M ρ lam ε n x y ω) :
    leftNoiseOrderContribution
        M ρ lam ε n x y ω =
      parametrixP M ρ lam ε (n + 1)
          x y ω +
        leftOrderCountertermSum
          M ρ lam ε n x y ω := by
  have hleft :=
    leftNoiseOrderContribution_eq_caseOne_caseTwo_add_caseThreeSource
      M ρ lam ε n x y ω hsplit hcreation hnoPrefix
  have hparam :=
    parametrixP_succ_eq_headCases
      M ρ lam ε n x y ω
  unfold leftWithPrefixContractionSum at hcaseThree
  unfold leftWithPrefixRandRISum at hcaseThree
  rw [hleft, hcaseThree, hparam]
  abel

/-- **Preconditioned Proposition 3.4, left form.**

This is paper (3.16) after applying `(1-Δ)⁻¹` on the left.  All
integration hypotheses are explicit; the sole branch-specific input is
the exact with-prefix equality above. -/
theorem leftParametrixNoiseSource_eq_parametrix_succ_add_counterterms
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hsource :
      LeftOrderSourceIntegrability
        M ρ lam ε n x y ω)
    (hsplit :
      ∀ κ : PartialPairing (Fin n),
        LeftPairingSplitIntegrability
          M ρ ε n κ x y ω)
    (hcreation :
      ∀ κ : PartialPairing (Fin n),
        Integrable
          (fun u : Fin (n + 1) → T4 =>
            randIntegrand M ρ ε
              (wickHeadEquiv n (Sum.inl κ))
              (assemble x y u) ω)
          (Measure.pi fun _ => paperMeasure))
    (hnoPrefix :
      ∀ d :
          {d : MarkedSingle (Fin n) //
            ¬markedHasHeadPrefix d},
        Integrable
          (fun u : Fin (n + 1) → T4 =>
            randIntegrand M ρ ε
              (wickHeadEquiv n
                (Sum.inr d.1))
              (assemble x y u) ω)
          (Measure.pi fun _ => paperMeasure))
    (hcaseThree :
      leftWithPrefixContractionSum
          M ρ lam ε n x y ω =
        leftWithPrefixRandRISum
            M ρ lam ε n x y ω +
          leftOrderCountertermSum
            M ρ lam ε n x y ω) :
    leftParametrixNoiseSource
        M ρ lam ε n x y ω =
      parametrixP M ρ lam ε (n + 1)
          x y ω +
        leftOrderCountertermSum
          M ρ lam ε n x y ω := by
  rw [←
    leftNoiseOrderContribution_eq_leftParametrixNoiseSource
      M ρ lam ε n x y ω hsource]
  exact
    leftNoiseOrderContribution_eq_parametrix_succ_add_counterterms
      M ρ lam ε n x y ω
      hsplit hcreation hnoPrefix hcaseThree

/-- The complete left preconditioned remainder identity follows from
the analytic head-case data for precisely the orders below the
truncation.  The terminal order `A` appears only in the remainder and
requires no extra use of Proposition 3.4. -/
theorem leftPreconditionedParametrixAction_eq_green_add_remainder_of_headCases
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (x y : T4) (ω : M.Ω)
    (hsource :
      ∀ n ∈ Finset.range A,
        LeftOrderSourceIntegrability
          M ρ lam ε n x y ω)
    (hsplit :
      ∀ n ∈ Finset.range A,
        ∀ κ : PartialPairing (Fin n),
          LeftPairingSplitIntegrability
            M ρ ε n κ x y ω)
    (hcreation :
      ∀ n ∈ Finset.range A,
        ∀ κ : PartialPairing (Fin n),
          Integrable
            (fun u : Fin (n + 1) → T4 =>
              randIntegrand M ρ ε
                (wickHeadEquiv n (Sum.inl κ))
                (assemble x y u) ω)
            (Measure.pi fun _ => paperMeasure))
    (hnoPrefix :
      ∀ n ∈ Finset.range A,
        ∀ d :
            {d : MarkedSingle (Fin n) //
              ¬markedHasHeadPrefix d},
          Integrable
            (fun u : Fin (n + 1) → T4 =>
              randIntegrand M ρ ε
                (wickHeadEquiv n
                  (Sum.inr d.1))
                (assemble x y u) ω)
            (Measure.pi fun _ => paperMeasure))
    (hcaseThree :
      ∀ n ∈ Finset.range A,
        leftWithPrefixContractionSum
            M ρ lam ε n x y ω =
          leftWithPrefixRandRISum
              M ρ lam ε n x y ω +
            leftOrderCountertermSum
              M ρ lam ε n x y ω) :
    leftPreconditionedParametrixAction
        M ρ lam ε A x y ω =
      greenFn (x - y) +
        leftPreconditionedRemainder
          M ρ lam ε A x y ω := by
  apply
    leftPreconditionedParametrixAction_eq_green_add_remainder
      M ρ lam ε A x y ω
  intro m hm
  have hmBounds := Finset.mem_Icc.mp hm
  have hn :
      m - 1 ∈ Finset.range A := by
    apply Finset.mem_range.mpr
    omega
  have horder :=
    leftParametrixNoiseSource_eq_parametrix_succ_add_counterterms
      M ρ lam ε (m - 1) x y ω
      (hsource (m - 1) hn)
      (hsplit (m - 1) hn)
      (hcreation (m - 1) hn)
      (hnoPrefix (m - 1) hn)
      (hcaseThree (m - 1) hn)
  have hsucc : m - 1 + 1 = m := by omega
  simpa only [leftOrderCountertermSum, hsucc] using horder

end PartialPairing

end

end Anderson4D
