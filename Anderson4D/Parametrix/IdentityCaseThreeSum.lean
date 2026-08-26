import Anderson4D.Parametrix.IdentityAmbient

/-!
# Summing the case-(3) parametrix identity

This module lifts the fixed-pairing case-(3) identity from
`IdentityAmbient` to the exact finite prefix/tail sums in paper
(3.18)--(3.19).  The only hypotheses are the termwise integrability
conditions needed by the displayed Bochner integral equalities.  In
particular, no identity or estimate is hidden in an abstract output
predicate.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-- The analytic regularity needed to sum all case-(3) identities at
fixed prefix order `2(q+1)` and tail order `r`.

The first two fields are precisely the hypotheses of
`caseThreeJointContribution_eq_randRI_add_delta`; the last field licenses
the finite-sum/integral exchange in the collapsed delta block. -/
structure CaseThreeSummationIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω) : Prop where
  split :
    ∀ (σ : PartialPairing (Fin (2 * (q + 1))))
      (_hσ : IsNonSplit σ)
      (τ : PartialPairing (Fin r)),
      NestedIntegrablePair3
        paperMeasure paperMeasure
        (Measure.pi fun _ : Fin (2 * q + r) => paperMeasure)
        (fun z w t =>
          caseThreeAmbientCore M ρ ε q r σ τ x z w y ω t)
        (fun z w t =>
          caseThreeDiagonalCore M ρ ε q r σ τ x z w y ω t)
  ambient :
    ∀ (σ : PartialPairing (Fin (2 * (q + 1))))
      (_hσ : IsNonSplit σ)
      (τ : PartialPairing (Fin r)),
      Integrable
        (fun v : Fin (2 * (q + 1) + r) → T4 =>
          randIntegrand M ρ ε (appendPairing σ τ)
            (assemble x y v) ω)
        (Measure.pi fun _ => paperMeasure)
  delta :
    ∀ (σ : PartialPairing (Fin (2 * (q + 1))))
      (_hσ : IsNonSplit σ)
      (τ : PartialPairing (Fin r)),
      Integrable
        (fun z : T4 =>
          greenFn (x - z) *
            detJMass ρ lam ε (q + 1) σ *
            randRI M ρ lam ε r τ z y ω)
        paperMeasure

/-- Summing the factorized case-(3) source over every non-split prefix and
tail pairing gives the corresponding ambient random kernels plus all
delta contributions, with multiplicity one. -/
theorem sum_caseThreeFactorizedContribution_eq_randRI_add_delta
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω)
    (hint :
      CaseThreeSummationIntegrability
        M ρ lam ε q r x y ω) :
    (∑ σ ∈ Finset.univ.filter
          (fun σ : PartialPairing (Fin (2 * (q + 1))) =>
            IsNonSplit σ),
        ∑ τ : PartialPairing (Fin r),
          caseThreeFactorizedContribution
            M ρ lam ε q r σ τ x y ω) =
      (∑ σ ∈ Finset.univ.filter
            (fun σ : PartialPairing (Fin (2 * (q + 1))) =>
              IsNonSplit σ),
          ∑ τ : PartialPairing (Fin r),
            randRI M ρ lam ε (2 * (q + 1) + r)
              (appendPairing σ τ) x y ω) +
        ∑ σ ∈ Finset.univ.filter
            (fun σ : PartialPairing (Fin (2 * (q + 1))) =>
              IsNonSplit σ),
          ∑ τ : PartialPairing (Fin r),
            caseThreeDeltaContribution
              M ρ lam ε (q + 1) r σ τ x y ω := by
  classical
  calc
    _ =
        ∑ σ ∈ Finset.univ.filter
            (fun σ : PartialPairing (Fin (2 * (q + 1))) =>
              IsNonSplit σ),
          ∑ τ : PartialPairing (Fin r),
            (randRI M ρ lam ε (2 * (q + 1) + r)
                (appendPairing σ τ) x y ω +
              caseThreeDeltaContribution
                M ρ lam ε (q + 1) r σ τ x y ω) := by
      apply Finset.sum_congr rfl
      intro σ hσmem
      have hσ : IsNonSplit σ := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hσmem
      apply Fintype.sum_congr
      intro τ
      rw [← caseThreeJointContribution_eq_factorized
        M ρ lam ε q r σ τ x y ω]
      exact caseThreeJointContribution_eq_randRI_add_delta
        M ρ lam ε q r σ τ hσ x y ω
          (hint.split σ hσ τ) (hint.ambient σ hσ τ)
    _ = _ := by
      simp only [Finset.sum_add_distrib]

/-- The finite sum of the delta terms is exactly the already frozen
counterterm block.  This is the rigorous version of summing the
`C₂q,σ δ` term in paper (3.19). -/
theorem sum_caseThreeDeltaContribution_eq_countertermBlock
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω)
    (hint :
      CaseThreeSummationIntegrability
        M ρ lam ε q r x y ω) :
    (∑ σ ∈ Finset.univ.filter
          (fun σ : PartialPairing (Fin (2 * (q + 1))) =>
            IsNonSplit σ),
        ∑ τ : PartialPairing (Fin r),
          caseThreeDeltaContribution
            M ρ lam ε (q + 1) r σ τ x y ω) =
      caseThreeCountertermBlock
        M ρ lam ε (q + 1) r x y ω := by
  classical
  let S :=
    Finset.univ.filter
      (fun σ : PartialPairing (Fin (2 * (q + 1))) =>
        IsNonSplit σ)
  let F :
      PartialPairing (Fin (2 * (q + 1))) →
        PartialPairing (Fin r) → T4 → ℝ :=
    fun σ τ z =>
      greenFn (x - z) *
        detJMass ρ lam ε (q + 1) σ *
        randRI M ρ lam ε r τ z y ω
  have hσ (σ : PartialPairing (Fin (2 * (q + 1))))
      (hσmem : σ ∈ S) :
      Integrable (fun z => ∑ τ : PartialPairing (Fin r), F σ τ z)
        paperMeasure := by
    apply integrable_finsetSum
    intro τ _hτ
    apply hint.delta σ
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hσmem
  have hsum :
      (∑ σ ∈ S, ∑ τ : PartialPairing (Fin r),
          ∫ z, F σ τ z ∂paperMeasure) =
        ∫ z, ∑ σ ∈ S, ∑ τ : PartialPairing (Fin r),
          F σ τ z ∂paperMeasure := by
    symm
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro σ hσmem
      exact integral_finsetSum _ fun τ _ =>
        hint.delta σ
          (by
            simpa only [S, Finset.mem_filter, Finset.mem_univ,
              true_and] using hσmem)
          τ
    · exact hσ
  calc
    _ = ∑ σ ∈ S, ∑ τ : PartialPairing (Fin r),
          ∫ z, F σ τ z ∂paperMeasure := by
      apply Finset.sum_congr rfl
      intro σ hσmem
      apply Fintype.sum_congr
      intro τ
      rw [caseThreeDeltaContribution_eq_mass]
    _ = ∫ z, ∑ σ ∈ S, ∑ τ : PartialPairing (Fin r),
          F σ τ z ∂paperMeasure :=
      hsum
    _ = caseThreeCountertermBlock
          M ρ lam ε (q + 1) r x y ω := by
      unfold caseThreeCountertermBlock
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [S, F]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _hσ
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro τ
      ring

/-- Fully collapsed fixed-order case-(3) sum: the source block is the
ambient appended-pairing sum plus `C₂(q+1) Pᵣ` under the free Green
convolution. -/
theorem sum_caseThreeFactorizedContribution_eq_randRI_add_counterterm
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω)
    (hint :
      CaseThreeSummationIntegrability
        M ρ lam ε q r x y ω) :
    (∑ σ ∈ Finset.univ.filter
          (fun σ : PartialPairing (Fin (2 * (q + 1))) =>
            IsNonSplit σ),
        ∑ τ : PartialPairing (Fin r),
          caseThreeFactorizedContribution
            M ρ lam ε q r σ τ x y ω) =
      (∑ σ ∈ Finset.univ.filter
            (fun σ : PartialPairing (Fin (2 * (q + 1))) =>
              IsNonSplit σ),
          ∑ τ : PartialPairing (Fin r),
            randRI M ρ lam ε (2 * (q + 1) + r)
              (appendPairing σ τ) x y ω) +
        caseThreeCountertermBlock
          M ρ lam ε (q + 1) r x y ω := by
  rw [sum_caseThreeFactorizedContribution_eq_randRI_add_delta
    M ρ lam ε q r x y ω hint]
  rw [sum_caseThreeDeltaContribution_eq_countertermBlock
    M ρ lam ε q r x y ω hint]

end PartialPairing

end

end Anderson4D
