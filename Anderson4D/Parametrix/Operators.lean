import Anderson4D.Continuum.Basic

/-!
# Bounded-operator realization of the resolvent

This file contains only bounded operators and therefore avoids representing
`1 - Δ`, point masses, or
multiplication by a distribution as unbounded operators.

For bounded `G` and `M`, set `K = G M`.  Invertibility of the Anderson
operator is represented by invertibility of `1 - K`.  On that event the
recentered resolvent satisfies

`(1 - K)⁻¹ G - G = (1 - K)⁻¹ G M G`.

The norm-small case is connected to the actual Neumann series in the
complete operator algebra.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The bounded operator `K = G ∘ M`. -/
def Kop (G M : H →L[ℂ] H) : H →L[ℂ] H :=
  G * M

/-- The project definition of invertibility of the corresponding Anderson
operator: `1 - K` is a unit of the bounded-operator algebra. -/
def LopInvertible (G M : H →L[ℂ] H) : Prop :=
  IsUnit (1 - Kop G M)

/-- The inverse Green operator on the invertibility event. -/
def inverseGreen (G M : H →L[ℂ] H)
    (h : LopInvertible G M) : H →L[ℂ] H :=
  ((h.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) * G

open Classical in
/-- Matrix coefficient of the recentered inverse with the sign convention
of paper (3.23), junk-totalized to zero off the invertibility event. -/
def operatorModeCoeffH
    (G M : H →L[ℂ] H) (e : Z4 → H) (α β : Z4) : ℂ :=
  if h : LopInvertible G M then
    ⟪e (-α), inverseGreen G M h (e β) - G (e β)⟫_ℂ
  else 0

/-- The inverse unit is a two-sided inverse of `1 - K`. -/
theorem inverseUnit_mul_one_sub_Kop
    (G M : H →L[ℂ] H) (h : LopInvertible G M) :
    ((h.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) *
        (1 - Kop G M) = 1 := by
  set u : (H →L[ℂ] H)ˣ := h.unit
  have hval : (u : H →L[ℂ] H) = 1 - Kop G M := h.unit_spec
  rw [← hval]
  exact_mod_cast u.inv_mul

/-- Algebraic core of the conditioned Hilbert--Schmidt difference
argument. -/
theorem inverseGreen_sub_G
    (G M : H →L[ℂ] H) (h : LopInvertible G M) :
    inverseGreen G M h - G =
      ((h.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) *
        (G * M * G) := by
  have hinv := inverseUnit_mul_one_sub_Kop G M h
  have hexpand : G * M * G = G - (1 - Kop G M) * G := by
    simp [Kop, sub_mul, one_mul]
  unfold inverseGreen
  rw [hexpand, mul_sub, ← mul_assoc, hinv, one_mul]

/-- Pointwise form of `inverseGreen_sub_G`. -/
theorem inverseGreen_apply_sub_G
    (G M : H →L[ℂ] H) (h : LopInvertible G M) (f : H) :
    inverseGreen G M h f - G f =
      ((h.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)
        (G (M (G f))) := by
  have hop := congrArg (fun A : H →L[ℂ] H => A f)
    (inverseGreen_sub_G G M h)
  simpa [sub_apply, mul_apply_eq_comp,
    mul_assoc] using hop

/-- A norm-small `K` gives the required invertibility event. -/
theorem lopInvertible_of_norm_Kop_lt_one
    [CompleteSpace H] (G M : H →L[ℂ] H)
    (hK : ‖Kop G M‖ < 1) :
    LopInvertible G M :=
  isUnit_one_sub_of_norm_lt_one hK

/-- The canonical Neumann inverse of `1 - K` when `‖K‖ < 1`. -/
def neumannInverse [CompleteSpace H]
    (K : H →L[ℂ] H) (hK : ‖K‖ < 1) : H →L[ℂ] H :=
  (((Units.oneSub K hK)⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)

/-- The Neumann inverse is the sum of the operator-valued geometric
series. -/
theorem neumannInverse_eq_tsum [CompleteSpace H]
    (K : H →L[ℂ] H) (hK : ‖K‖ < 1) :
    neumannInverse K hK = ∑' n : ℕ, K ^ n := by
  unfold neumannInverse
  symm
  rw [← NormedRing.inverse_one_sub K hK]
  exact geom_series_eq_inverse K hK

/-- The operator-valued Neumann series is summable. -/
theorem summable_pow_of_norm_lt_one [CompleteSpace H]
    (K : H →L[ℂ] H) (hK : ‖K‖ < 1) :
    Summable (fun n : ℕ => K ^ n) :=
  summable_geometric_of_norm_lt_one hK

/-- Applying the Neumann inverse agrees with the pointwise sum of the
iterated operators. -/
theorem neumannInverse_apply_eq_tsum [CompleteSpace H]
    (K : H →L[ℂ] H) (hK : ‖K‖ < 1) (f : H) :
    neumannInverse K hK f = ∑' n : ℕ, (K ^ n) f := by
  rw [neumannInverse_eq_tsum K hK]
  simpa using (ContinuousLinearMap.apply ℂ H f).map_tsum
    (summable_pow_of_norm_lt_one K hK)

/-- The canonical inverse used by the norm-small event is exactly the
inverse selected by its `IsUnit` witness. -/
theorem inverseGreen_of_norm_lt_one
    [CompleteSpace H] (G M : H →L[ℂ] H)
    (hK : ‖Kop G M‖ < 1) :
    inverseGreen G M (lopInvertible_of_norm_Kop_lt_one G M hK) =
      neumannInverse (Kop G M) hK * G := by
  have hu :
      (lopInvertible_of_norm_Kop_lt_one G M hK).unit =
        Units.oneSub (Kop G M) hK := by
    apply Units.ext
    exact (lopInvertible_of_norm_Kop_lt_one G M hK).unit_spec
  unfold inverseGreen neumannInverse
  rw [hu]

end

end Anderson4D
