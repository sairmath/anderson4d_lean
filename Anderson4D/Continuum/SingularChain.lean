import Anderson4D.Continuum.SingularConv

/-!
# Iterated singular convolutions on the four-dimensional torus

This file packages the induction implicit in paper (5.4).  The hard
analytic input is the uniform threefold-convolution estimate proved in
`Continuum/SingularConv.lean`.  Every additional `|z|⁻²` factor costs only
its finite `L¹` mass, so all convolution chains of length at least three
are uniformly bounded, with an exponential constant in the chain length.

This is the reusable chain form of blueprint node I-singconv.  It is still
only the translation-invariant analytic core of paper (5.3)--(5.4); the
cell supports and rescaling factors belong to node R-51.
-/

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The `n`-fold convolution chain of the model kernel `|z|⁻²`.

The values at lengths `0` and `1` are totalized as `0` and `invSqKer`.
For `n ≥ 2`, the recursion adds one kernel on the left. -/
def singularChain : ℕ → T4 → ℝ
  | 0 => fun _ => 0
  | 1 => invSqKer
  | n + 2 => fun x =>
      ∫ z, invSqKer (x - z) * singularChain (n + 1) z ∂paperMeasure

/-- Every convolution chain is pointwise nonnegative. -/
theorem singularChain_nonneg : ∀ n : ℕ, ∀ x : T4, 0 ≤ singularChain n x
  | 0, x => by simp [singularChain]
  | 1, x => invSqKer_nonneg x
  | n + 2, x => by
      rw [singularChain]
      exact integral_nonneg fun z =>
        mul_nonneg (invSqKer_nonneg _) (singularChain_nonneg (n + 1) z)

/-- The length-three chain is exactly the nested integral used by
`triple_conv_invSqKer_le`. -/
theorem singularChain_three (x : T4) :
    singularChain 3 x =
      ∫ z₁, (∫ z₂,
        invSqKer (x - z₁) * invSqKer (z₁ - z₂) * invSqKer z₂
          ∂paperMeasure) ∂paperMeasure := by
  rw [singularChain, singularChain, singularChain]
  apply integral_congr_ae
  filter_upwards with z₁
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z₂
  ring

/-- The finite `L¹` mass of the model singular kernel. -/
def invSqKerMass : ℝ := ∫ z, invSqKer z ∂paperMeasure

theorem invSqKerMass_nonneg : 0 ≤ invSqKerMass :=
  integral_nonneg invSqKer_nonneg

/-- Translation invariance of the `L¹` mass, in the orientation used by
`singularChain`. -/
theorem integral_invSqKer_sub_left (x : T4) :
    ∫ z, invSqKer (x - z) ∂paperMeasure = invSqKerMass := by
  have heq : (fun z : T4 => invSqKer (x - z)) =
      fun z => invSqKer (z - x) := by
    funext z
    exact invSqKer_sub_comm x z
  rw [heq]
  have h := integral_map (μ := paperMeasure) (φ := fun z : T4 => z - x)
    (measurePreserving_sub_paper x).measurable.aemeasurable
    (f := invSqKer) measurable_invSqKer.aestronglyMeasurable
  rw [(measurePreserving_sub_paper x).map_eq] at h
  exact h.symm

/-- The shifted kernel in the left-convolution orientation is integrable. -/
theorem integrable_invSqKer_sub_left (x : T4) :
    Integrable (fun z => invSqKer (x - z)) paperMeasure := by
  have heq : (fun z : T4 => invSqKer (x - z)) =
      fun z => invSqKer (z - x) := by
    funext z
    exact invSqKer_sub_comm x z
  rw [heq]
  exact integrable_invSqKer_sub x

/-- **Uniform chain bound (paper (5.4), analytic core).**

There is one absolute constant `C > 0` such that every convolution chain
of length at least three is bounded by `Cⁿ`, uniformly in its endpoint.
The base case is `triple_conv_invSqKer_le`; the induction uses only the
finite `L¹` mass of one additional kernel. -/
theorem singularChain_le_pow :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n → ∀ x : T4,
      singularChain n x ≤ C ^ n := by
  obtain ⟨C₃, hC₃, hthree⟩ := triple_conv_invSqKer_le
  let C : ℝ := C₃ + invSqKerMass + 1
  have hmass : invSqKerMass ≤ C := by
    dsimp [C]
    linarith [hC₃]
  have hC₃C : C₃ ≤ C := by
    dsimp [C]
    linarith [invSqKerMass_nonneg]
  have hCone : 1 ≤ C := by
    dsimp [C]
    linarith [hC₃, invSqKerMass_nonneg]
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hCone
  refine ⟨C, hC, ?_⟩
  have hbase : ∀ x : T4, singularChain 3 x ≤ C ^ 3 := by
    intro x
    rw [singularChain_three]
    calc
      (∫ z₁, (∫ z₂,
          invSqKer (x - z₁) * invSqKer (z₁ - z₂) * invSqKer z₂
            ∂paperMeasure) ∂paperMeasure)
          ≤ C₃ := hthree x
      _ ≤ C := hC₃C
      _ ≤ C ^ 3 := by nlinarith [sq_nonneg (C - 1)]
  have hind : ∀ m : ℕ, ∀ x : T4,
      singularChain (m + 3) x ≤ C ^ (m + 3) := by
    intro m
    induction m with
    | zero =>
        simpa using hbase
    | succ m ih =>
        intro x
        rw [show Nat.succ m + 3 = (m + 2) + 2 by omega, singularChain]
        calc
          (∫ z, invSqKer (x - z) * singularChain (m + 3) z
              ∂paperMeasure)
              ≤ ∫ z, invSqKer (x - z) * C ^ (m + 3)
                  ∂paperMeasure := by
                exact integral_mono_of_nonneg
                  (Filter.Eventually.of_forall fun z =>
                    mul_nonneg (invSqKer_nonneg _)
                      (singularChain_nonneg (m + 3) z))
                  ((integrable_invSqKer_sub_left x).mul_const _)
                  (Filter.Eventually.of_forall fun z =>
                    mul_le_mul_of_nonneg_left (ih z) (invSqKer_nonneg _))
          _ = C ^ (m + 3) * invSqKerMass := by
                rw [integral_mul_const, integral_invSqKer_sub_left]
                ring
          _ ≤ C ^ (m + 3) * C := by
                exact mul_le_mul_of_nonneg_left hmass (by positivity)
          _ = C ^ (Nat.succ m + 3) := by
                convert (pow_succ C (m + 3)).symm using 1
  intro n hn x
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [add_comm] using hind m x

end

end Anderson4D
