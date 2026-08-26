import Anderson4D.DetParametrix.Paper42_Moment.R324FullFullRefinedFiberFactorization
import Anderson4D.DetParametrix.Paper42_Moment.R324DetIntegrability

/-!
# The full/full half-integrability seam, discharged

Paper: R-324 — §4.2 — the full/full half-integrability seam

`R324FullFullRefinedFiberFactorization` states its factorization under the
named premise `DeterministicFullHalfIntegrable`, the integrability of one
half of (4.18) — the two endpoint characters times the closed deterministic
profile — on the flat half carrier `T4 × (T4 × (Fin m → T4))`.

That premise is not an assumption: `integrable_detIntegrand_flat` already
proves the profile itself integrable there for every `0 < ε ≤ 1`, and the
characters are unimodular (`norm_charT4`).  This module discharges it, so
the full/full branch of the Steps 2--3 dichotomy carries no analytic
hypothesis.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The two endpoint characters of one half of (4.18), as a function of the
flat half carrier. -/
private def r324HalfCharacter {m : ℕ} (α β : Z4)
    (p : T4 × (T4 × (Fin m → T4))) : ℂ :=
  charT4 α p.1 * charT4 β p.2.1

private theorem measurable_r324HalfCharacter {m : ℕ} (α β : Z4) :
    Measurable (r324HalfCharacter (m := m) α β) :=
  ((continuous_charT4 α).measurable.comp measurable_fst).mul
    ((continuous_charT4 β).measurable.comp
      (measurable_fst.comp measurable_snd))

private theorem norm_r324HalfCharacter {m : ℕ} (α β : Z4)
    (p : T4 × (T4 × (Fin m → T4))) :
    ‖r324HalfCharacter α β p‖ = 1 := by
  unfold r324HalfCharacter
  rw [norm_mul, norm_charT4, norm_charT4, mul_one]

/-- **The full/full half-integrability seam, discharged.**

For every mollification scale `0 < ε ≤ 1`, every order, every pair of
external modes and every within-half pairing, the half integrand of (4.18)
is integrable on its flat carrier.  The proof is the fixed-scale recipe in
`docs/R324_PAPER_PROOF.md`: the singular part is the closed deterministic
profile, already integrable, and the characters are a bounded measurable
factor. -/
theorem deterministicFullHalfIntegrable_all
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4) (κ : PartialPairing (Fin m)) :
    DeterministicFullHalfIntegrable ρ ε m α β κ := by
  have hbase := integrable_detIntegrand_flat ρ hε hε1 κ
  have hbdd :
      Integrable
        (fun p : T4 × (T4 × (Fin m → T4)) =>
          (detIntegrand ρ ε m κ (assemble p.1 p.2.1 p.2.2) : ℂ) *
            r324HalfCharacter α β p)
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin m => paperMeasure))) :=
    hbase.mul_bdd (c := 1)
      (measurable_r324HalfCharacter α β).aestronglyMeasurable
      (.of_forall fun p => le_of_eq (norm_r324HalfCharacter α β p))
  refine hbdd.congr (.of_forall fun p => ?_)
  unfold r324HalfCharacter
  ring

/-- The full/full refined-fibre factorization, with its two analytic
premises discharged.  This is the branch of `r324SinglesDichotomy` on which
both halves are fully paired, so the contraction carries no cross-copy
covariance and the two halves of (4.18) are independent. -/
theorem sum_momentRefinedContractionFiber_eq_fullHalfFiber_mul_of_isFull
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (α β : Z4)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (hp : e₀.1.IsFull) (hm : e₀.2.1.IsFull) :
    (∑ e ∈ momentRefinedContractionFiber m s r,
        deterministicMomentContractionTerm ρ ε m α β e) =
      (∑ κp : ReductionEndpointFiberAt e₀.1,
          deterministicFullHalfIntegral ρ ε m α β κp.1) *
        ∑ κm : ReductionEndpointFiberAt e₀.2.1,
          deterministicFullHalfIntegral ρ ε m (-α) (-β) κm.1 :=
  sum_momentRefinedContractionFiber_deterministicMomentContractionTerm_eq_fullHalfFiber_mul
    ρ ε m α β e₀ he₀ hp hm
    (fun κp => deterministicFullHalfIntegrable_all ρ hε hε1 α β κp.1)
    (fun κm => deterministicFullHalfIntegrable_all ρ hε hε1 (-α) (-β) κm.1)

end

end Anderson4D
