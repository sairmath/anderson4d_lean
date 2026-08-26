import Anderson4D.Main.GaussianLimit
import Anderson4D.Parametrix.FredholmCoefficientBridge

/-!
# The conditional main statement (blueprint nodes D-limit and T-1.1)

Paper: P-mom — Thm 1.1 — the conditional main statement

The characteristic-function form (paper (3.34)) of Deng–Shen's Theorem 1.1
for the mode coefficients of `H_ε = λ_ε⁻¹(G_ε − G)`, stated conditionally
on Proposition 3.6 (`Prop36`). The targets in this file are
`Prop`-valued definitions; `Prop36` itself is witness data carrying the
uniform coefficient constant, never an axiom. The proofs of the conditional
characteristic-function and convergence-in-law forms are `main_conditional`
and `main_conditional_law`.
-/

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The measurable Fredholm realization and the samplewise inverse give
the same characteristic-function integral at every positive scale.  Thus
the statement below is literally about the samplewise resolvent,
while the proof may use its Borel representative. -/
theorem integral_exp_I_measurableFredholm_eq_fredholm
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) :
    (∫ ω, Complex.exp (Complex.I *
        (measurableFredholmFiniteModeReal
          M ρ lam ε s modes c ω : ℂ))
      ∂(volume : Measure M.Ω)) =
      ∫ ω, Complex.exp (Complex.I *
        (fredholmFiniteModeReal
          M ρ lam ε s modes c ω : ℂ))
      ∂(volume : Measure M.Ω) := by
  apply integral_congr_ae
  filter_upwards
    [ae_measurableFredholmFiniteModeReal_eq_fredholmFiniteModeReal
      M ρ lam hε s modes c] with ω hω
  rw [hω]

/-- **The main theorem, characteristic-function form** (paper (3.34);
node T-1.1 conclusion). For small
coupling, every finite complex linear combination of mode coefficients of
`H_ε` satisfies
`E[exp(i · Re ∑ⱼ cⱼ Ĥ_ε(αⱼ, βⱼ))] → exp(−q/2)` as `ε ↓ 0` in `(0,1)`,
with `q = limitVar` the limit Gaussian variance.

The coefficient is the samplewise Fredholm inverse of `1 - G M`.  At positive
scale it has the almost-surely equal Borel representative used in the proof.
No Neumann small-norm condition is part of this statement. -/
def MainStatement (M : NoiseModel) (ρ : SmoothCutoff) : Prop :=
  ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, lam ∈ Set.Ioo 0 lam₀ →
    ∀ (s : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ),
      Filter.Tendsto
        (fun ε : ℝ => ∫ ω, Complex.exp (Complex.I *
          ((fredholmFiniteModeReal
            M ρ lam ε s modes c ω : ℝ) : ℂ)))
        (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1))
        (nhds ((Real.exp (-(limitVar lam modes c) / 2) : ℝ) : ℂ))

/-- **The conditional main theorem** (node T-1.1): the
uniform-in-coupling family form of Proposition 3.6 implies the
characteristic-function form of Theorem 1.1.  The shared coefficient
bound constant is what permits one small threshold to be chosen before
the coupling is quantified. -/
def MainConditional (M : NoiseModel) (ρ : SmoothCutoff) : Prop :=
  Prop36Family M ρ → MainStatement M ρ

/-- Sanity: `MainConditional` is definitionally the implication
`(uniform Prop 3.6 family) → (3.34)`. -/
example (M : NoiseModel) (ρ : SmoothCutoff) :
    MainConditional M ρ ↔
      (Prop36Family M ρ → MainStatement M ρ) :=
  Iff.rfl

end

end Anderson4D
