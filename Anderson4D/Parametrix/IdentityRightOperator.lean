import Anderson4D.Parametrix.IdentityLeftAssembly

/-!
# The paper-facing right parametrix source

This is the right-composition analogue of `IdentityLeftOperator`.  It
expands

`λ_ε ∫ Pₙ(x,z) ξ_ε(z) G(z-y) dz`

as a finite sum of pairing-level nested integrals, with the one
finite-sum/integral exchange hypothesis stated explicitly.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-- The actual right-composition noise source for one old pairing. -/
def rightNoisePairingContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε ^ (n + 1) *
    ∫ z : T4, ∫ v : Fin n → T4,
      randIntegrand M ρ ε κ
          (assemble x z v) ω *
        (M.xiEps ρ ε ω z *
          greenFn (z - y))
      ∂(Measure.pi fun _ => paperMeasure)
      ∂paperMeasure

/-- One right pairing contribution is the corresponding summand of
the paper-facing right source. -/
theorem rightNoisePairingContribution_eq_rightRandRI
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (x y : T4) (ω : M.Ω) :
    rightNoisePairingContribution
        M ρ lam ε n κ x y ω =
      lamEps lam ε *
        ∫ z : T4,
          randRI M ρ lam ε n κ x z ω *
            (M.xiEps ρ ε ω z *
              greenFn (z - y))
          ∂paperMeasure := by
  let A := lamEps lam ε
  let I : T4 → ℝ :=
    fun z =>
      ∫ v : Fin n → T4,
        randIntegrand M ρ ε κ
          (assemble x z v) ω
        ∂(Measure.pi fun _ => paperMeasure)
  have hinner (z : T4) :
      (∫ v : Fin n → T4,
          randIntegrand M ρ ε κ
              (assemble x z v) ω *
            (M.xiEps ρ ε ω z *
              greenFn (z - y))
          ∂(Measure.pi fun _ => paperMeasure)) =
        I z *
          (M.xiEps ρ ε ω z *
            greenFn (z - y)) := by
    exact integral_mul_const
      (M.xiEps ρ ε ω z *
        greenFn (z - y))
      (fun v : Fin n → T4 =>
        randIntegrand M ρ ε κ
          (assemble x z v) ω)
  have hscale :
      (∫ z : T4,
          (A ^ n * I z) *
            (M.xiEps ρ ε ω z *
              greenFn (z - y))
          ∂paperMeasure) =
        A ^ n *
          ∫ z : T4,
            I z *
              (M.xiEps ρ ε ω z *
                greenFn (z - y))
            ∂paperMeasure := by
    calc
      _ =
          ∫ z : T4,
            A ^ n *
              (I z *
                (M.xiEps ρ ε ω z *
                  greenFn (z - y)))
            ∂paperMeasure := by
        apply integral_congr_ae
        filter_upwards with z
        ring
      _ = _ := by
        rw [integral_const_mul]
  unfold rightNoisePairingContribution randRI
  change
    A ^ (n + 1) *
        (∫ z : T4,
          ∫ v : Fin n → T4,
            randIntegrand M ρ ε κ
                (assemble x z v) ω *
              (M.xiEps ρ ε ω z *
                greenFn (z - y))
            ∂(Measure.pi fun _ => paperMeasure)
          ∂paperMeasure) =
      A *
        ∫ z : T4,
          (A ^ n * I z) *
            (M.xiEps ρ ε ω z *
              greenFn (z - y))
          ∂paperMeasure
  simp_rw [hinner]
  rw [hscale, pow_succ]
  ring

/-- The full right noise source at old order `n`, before its Wick
head-case split. -/
def rightNoiseOrderContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∑ κ : PartialPairing (Fin n),
    rightNoisePairingContribution
      M ρ lam ε n κ x y ω

/-- Exact analytic input for exchanging the finite old-pairing sum
with the right source integral. -/
structure RightOrderSourceIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : Prop where
  pairing_outer :
    ∀ κ : PartialPairing (Fin n),
      Integrable
        (fun z : T4 =>
          randRI M ρ lam ε n κ x z ω *
            (M.xiEps ρ ε ω z *
              greenFn (z - y)))
        paperMeasure

/-- The integrated right pairing source is the actual right
noise-composition term containing `Pₙ`. -/
theorem rightNoiseOrderContribution_eq_rightParametrixNoiseSource
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hint :
      RightOrderSourceIntegrability
        M ρ lam ε n x y ω) :
    rightNoiseOrderContribution
        M ρ lam ε n x y ω =
      rightParametrixNoiseSource
        M ρ lam ε n x y ω := by
  unfold rightNoiseOrderContribution
  unfold rightParametrixNoiseSource
  calc
    _ =
        ∑ κ : PartialPairing (Fin n),
          lamEps lam ε *
            ∫ z : T4,
              randRI M ρ lam ε n κ x z ω *
                (M.xiEps ρ ε ω z *
                  greenFn (z - y))
              ∂paperMeasure := by
      apply Fintype.sum_congr
      intro κ
      exact
        rightNoisePairingContribution_eq_rightRandRI
          M ρ lam ε n κ x y ω
    _ =
        lamEps lam ε *
          ∑ κ : PartialPairing (Fin n),
            ∫ z : T4,
              randRI M ρ lam ε n κ x z ω *
                (M.xiEps ρ ε ω z *
                  greenFn (z - y))
              ∂paperMeasure := by
      rw [Finset.mul_sum]
    _ =
        lamEps lam ε *
          ∫ z : T4,
            ∑ κ : PartialPairing (Fin n),
              randRI M ρ lam ε n κ x z ω *
                (M.xiEps ρ ε ω z *
                  greenFn (z - y))
            ∂paperMeasure := by
      congr 1
      rw [← integral_finsetSum Finset.univ]
      intro κ _hκ
      exact hint.pairing_outer κ
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      unfold parametrixP
      rw [Finset.sum_mul]

end PartialPairing

end

end Anderson4D
