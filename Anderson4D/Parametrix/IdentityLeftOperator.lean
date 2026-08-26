import Anderson4D.Parametrix.IdentityLeftSource

/-!
# The paper-facing left parametrix source

This module identifies the finite pairing sum used by the Wick
creation--contraction analysis with the actual left-composition term

`λ_ε ∫ G(x-z) ξ_ε(z) Pₙ(z,y) dz`.

Only the exchange of the finite pairing sum with the outer integral
needs an integrability hypothesis.  Moving the scalar coupling factors
through the totalized Bochner integrals is unconditional.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-- The left noise part of `G (λ_ε ξ_ε - C_ε) Pₙ`, in the notation of
paper (3.17). -/
def leftParametrixNoiseSource
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε *
    ∫ z : T4,
      greenFn (x - z) *
        (M.xiEps ρ ε ω z *
          parametrixP M ρ lam ε n z y ω)
      ∂paperMeasure

/-- One pairing contribution is exactly the corresponding summand of
the paper-facing left noise source.  No integrability hypothesis is
needed: scalar multiplication commutes with the totalized Bochner
integral also on its junk branch. -/
theorem leftNoisePairingContribution_eq_leftRandRI
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (x y : T4) (ω : M.Ω) :
    leftNoisePairingContribution
        M ρ lam ε n κ x y ω =
      lamEps lam ε *
        ∫ z : T4,
          greenFn (x - z) *
            (M.xiEps ρ ε ω z *
              randRI M ρ lam ε n κ z y ω)
          ∂paperMeasure := by
  let A := lamEps lam ε
  let I : T4 → ℝ :=
    fun z =>
      ∫ v : Fin n → T4,
        randIntegrand M ρ ε κ
          (assemble z y v) ω
        ∂(Measure.pi fun _ => paperMeasure)
  have hinner (z : T4) :
      (∫ v : Fin n → T4,
          greenFn (x - z) *
            (M.xiEps ρ ε ω z *
              randIntegrand M ρ ε κ
                (assemble z y v) ω)
          ∂(Measure.pi fun _ => paperMeasure)) =
        (greenFn (x - z) *
          M.xiEps ρ ε ω z) * I z := by
    calc
      _ =
          ∫ v : Fin n → T4,
            (greenFn (x - z) *
              M.xiEps ρ ε ω z) *
                randIntegrand M ρ ε κ
                  (assemble z y v) ω
            ∂(Measure.pi fun _ => paperMeasure) := by
        apply integral_congr_ae
        filter_upwards with v
        ring
      _ = _ := by
        rw [integral_const_mul]
  have hscale :
      (∫ z : T4,
          greenFn (x - z) *
            (M.xiEps ρ ε ω z *
              (A ^ n * I z))
          ∂paperMeasure) =
        A ^ n *
          ∫ z : T4,
            (greenFn (x - z) *
              M.xiEps ρ ε ω z) * I z
            ∂paperMeasure := by
    calc
      _ =
          ∫ z : T4,
            A ^ n *
              ((greenFn (x - z) *
                M.xiEps ρ ε ω z) * I z)
            ∂paperMeasure := by
        apply integral_congr_ae
        filter_upwards with z
        ring
      _ = _ := by
        rw [integral_const_mul]
  unfold leftNoisePairingContribution leftNoisePairingCore randRI
  change
    A ^ (n + 1) *
        (∫ z : T4,
          ∫ v : Fin n → T4,
            greenFn (x - z) *
              (M.xiEps ρ ε ω z *
                randIntegrand M ρ ε κ
                  (assemble z y v) ω)
            ∂(Measure.pi fun _ => paperMeasure)
          ∂paperMeasure) =
      A *
        ∫ z : T4,
          greenFn (x - z) *
            (M.xiEps ρ ε ω z *
              (A ^ n * I z))
          ∂paperMeasure
  simp_rw [hinner]
  rw [hscale, pow_succ]
  ring

/-- Exact analytic input for exchanging the finite old-pairing sum
with the outer spatial integral. -/
structure LeftOrderSourceIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : Prop where
  pairing_outer :
    ∀ κ : PartialPairing (Fin n),
      Integrable
        (fun z : T4 =>
          greenFn (x - z) *
            (M.xiEps ρ ε ω z *
              randRI M ρ lam ε n κ z y ω))
        paperMeasure

/-- The integrated pairing source used by the head-case analysis is
the actual left noise term containing the order-`n` parametrix. -/
theorem leftNoiseOrderContribution_eq_leftParametrixNoiseSource
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hint :
      LeftOrderSourceIntegrability
        M ρ lam ε n x y ω) :
    leftNoiseOrderContribution
        M ρ lam ε n x y ω =
      leftParametrixNoiseSource
        M ρ lam ε n x y ω := by
  unfold leftNoiseOrderContribution
  unfold leftParametrixNoiseSource
  calc
    _ =
        ∑ κ : PartialPairing (Fin n),
          lamEps lam ε *
            ∫ z : T4,
              greenFn (x - z) *
                (M.xiEps ρ ε ω z *
                  randRI M ρ lam ε n κ z y ω)
              ∂paperMeasure := by
      apply Fintype.sum_congr
      intro κ
      exact
        leftNoisePairingContribution_eq_leftRandRI
          M ρ lam ε n κ x y ω
    _ =
        lamEps lam ε *
          ∑ κ : PartialPairing (Fin n),
            ∫ z : T4,
              greenFn (x - z) *
                (M.xiEps ρ ε ω z *
                  randRI M ρ lam ε n κ z y ω)
              ∂paperMeasure := by
      rw [Finset.mul_sum]
    _ =
        lamEps lam ε *
          ∫ z : T4,
            ∑ κ : PartialPairing (Fin n),
              greenFn (x - z) *
                (M.xiEps ρ ε ω z *
                  randRI M ρ lam ε n κ z y ω)
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
      rw [Finset.mul_sum, Finset.mul_sum]

end PartialPairing

end

end Anderson4D
