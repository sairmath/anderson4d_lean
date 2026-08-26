import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhysicalBudget
import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorCoreEstimate
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticResidualIteration
import Anderson4D.DetParametrix.Paper42_Moment.R324CentralDecayProof

/-!
# Interior-core reduction and unconditional signed block ledger

Support for the interior-core estimate and its final two-scalar reduction.

* `exists_prod_abs_renormC2q_le_signedBlockLedger_final` — the iterated
  Proposition 4.1 signed block ledger with **no reduction hypothesis**:
  the per-block estimate is supplied by the closed R-322 analytic
  iteration (`exists_r322_renormC2q_bound`, AE interface), so `k`
  signed blocks of orders `n i ≤ truncOrder ε` cost
  `(ε⁻²/|log ε|)^k · (Cλ)^{2Σ nᵢ}` from ranges and the cutoff alone.
* `r324InteriorCoreMajorantBound_of_uniform_logBudget` — Statement 1 at
  a solved primitive constant: any `ε`-uniform interior-core log budget
  discharges `R324InteriorCoreMajorantBound` with
  `pC = sC/min(sC,1)² · C`.
* `exists_deterministicMoment_paper_bound_of_logBudget_and_highFrequency`
  — the complete reduced form of paper (3.24) at `ε`-uniform
  constants from exactly two residual scalars, the `ε`-uniform interior
  log budget and the high-central-frequency signed bound.

**Power accounting of the residue.**  The ledger's `ε⁻²` is per *closed*
block: it is the endpoint near-field mass
`∫(|z|²+ε²)⁻³ ≍ ε⁻²/|log ε|` of the standalone `renormC2q` kernel.  The
interior core shares Green edges between adjacent blocks, so only the
four *external* legs pay `ε⁻²` — the exact `ε⁻⁸` of (3.24) — while each
interior block of order `q` must close at `C^{2q}·|log ε|^{q-1}` (the
inserted-majorant scale `∫maj ≍ (Cλ)^{2q}/|log ε|`, endpoint-free).
The remaining Statement 1 content is precisely this transport of the
closed R-322 block estimate from its endpoint-closed form
`(Cλ)^{2q}·ε⁻²/|log ε|` to the endpoint-free interior form on the
doubled moment carrier; the proved keyed interface cannot supply it
below the sharp `ε⁻⁶` amplitude (`R324TotalMassBudget`).
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- **Unconditional signed-physical block ledger.**  The hypotheses are
ranges and the cutoff only: the per-block Proposition 4.1 estimate is
supplied by the closed R-322 analytic iteration, not assumed. -/
theorem exists_prod_abs_renormC2q_le_signedBlockLedger_final
    (ρ : SmoothCutoff) :
    ∃ Crenorm : ℝ, 0 < Crenorm ∧
      ∀ (lam ε : ℝ) (k : ℕ) (n : Fin k → ℕ),
        0 < lam → 0 < ε → ε ≤ 1 →
        (∀ i, 1 ≤ n i) → (∀ i, n i ≤ truncOrder ε) →
        (∏ i, |renormC2q ρ lam ε (n i)|) ≤
          (ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) ^ k *
            (Crenorm * lam) ^ (2 * ∑ i, n i) := by
  obtain ⟨Crenorm, hCrenorm, hblock⟩ :=
    R322AnalyticResidualPrefix.exists_r322_renormC2q_bound ρ
  refine ⟨Crenorm, hCrenorm, ?_⟩
  intro lam ε k n hlam hε hε1 hn hntrunc
  calc
    (∏ i, |renormC2q ρ lam ε (n i)|) ≤
        ∏ i, (ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
          (Crenorm * lam) ^ (2 * n i)) :=
      Finset.prod_le_prod (fun i _ => abs_nonneg _)
        (fun i _ =>
          hblock lam ε (n i) hlam hε hε1 (hn i) (hntrunc i))
    _ = (ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) ^ k *
          ∏ i, (Crenorm * lam) ^ (2 * n i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    _ = (ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) ^ k *
          (Crenorm * lam) ^ (∑ i, 2 * n i) := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = (ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) ^ k *
          (Crenorm * lam) ^ (2 * ∑ i, n i) := by
      rw [← Finset.mul_sum]

/-- **Statement 1 at a solved primitive constant.**  Any `ε`-uniform
interior-core logarithmic budget constant `C` discharges the interior
inserted-majorant estimate with the explicit primitive constant
`sC/min(sC,1)² · C`: the support-constant distortion of the proved
bridge is inverted once and for all. -/
theorem r324InteriorCoreMajorantBound_of_uniform_logBudget
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {C supportConstant : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) (hlam : 0 ≤ lam)
    (hsupport : 0 < supportConstant)
    (budget : R324InteriorCoreLogBudget ρ ε m C) :
    R324InteriorCoreMajorantBound ρ lam ε m
      (supportConstant / min supportConstant 1 ^ 2 * C)
      supportConstant := by
  refine r324InteriorCoreMajorantBound_of_logBudget
    hm hε hε1 hlog hlam hsupport ?_
  have hmin : 0 < min supportConstant 1 := lt_min hsupport one_pos
  have heq :
      min supportConstant 1 ^ 2 / supportConstant *
        (supportConstant / min supportConstant 1 ^ 2 * C) = C := by
    field_simp
  rw [heq]
  exact budget

/-- **The complete reduced form of the deterministic moment estimate.**  The paper
bound (3.24) at `ε`-uniform constants follows from exactly two residual
scalar statements:

1. the interior-core logarithmic budget
   `R324InteriorCoreLogBudget ρ ε m C` at an `ε`-uniform constant `C`
   (`16·|log ε|·(interior L¹ mass) ≤ C^{2m}·|log ε|^m`, no coupling, no
   mode, no majorant), and
2. the high-central-frequency signed bound
   `R324HighCentralFrequencySignedBound` — one routed eighth-order
   decay unit, required only above the covariance frequency `ε⁻¹`.

All other layers of (3.24) are unconditional. -/
theorem exists_deterministicMoment_paper_bound_of_logBudget_and_highFrequency
    {C supportConstant : ℝ}
    (hC : 0 < C) (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 < m → 0 ≤ lam → 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        R324InteriorCoreLogBudget ρ ε m C →
        R324HighCentralFrequencySignedBound ρ lam ε m
          (lamEps lam ε ^ 2 * outerConstant *
            ((16 * (supportConstant / min supportConstant 1 ^ 2 * C)) *
              lam) ^ (2 * m - 2)) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * (supportConstant / min supportConstant 1 ^ 2 * C))
            lam ε m α β := by
  have hpC : 0 < supportConstant / min supportConstant 1 ^ 2 * C := by
    have hmin : 0 < min supportConstant 1 := lt_min hsupport one_pos
    positivity
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_interiorCore_and_highFrequency
      hpC hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m α β hm hlam hε hεsmall hlog hbudget hhigh
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  exact h ρ lam ε m α β hm hlam hε hεsmall hlog
    (r324InteriorCoreMajorantBound_of_uniform_logBudget
      hm hε hε1 hlog hlam hsupport hbudget)
    hhigh

end

end Anderson4D
