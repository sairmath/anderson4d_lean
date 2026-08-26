import Anderson4D.Parametrix.Operators

/-!
# Quantitative bounds for the bounded resolvent realization

This is the abstract Banach-algebra part of blueprint node I-l2op.  It
turns the norm-small event for `K = G M` into explicit Neumann inverse,
tail, and recentered-resolvent bounds.  No random-kernel estimate enters
here; those estimates only have to prove that the event occurs with high
probability.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- The geometric-series bound for the canonical Neumann inverse. -/
theorem norm_neumannInverse_le
    (K : H →L[ℂ] H) (hK : ‖K‖ < 1) :
    ‖neumannInverse K hK‖ ≤ (1 - ‖K‖)⁻¹ := by
  rw [neumannInverse_eq_tsum K hK]
  simpa using tsum_geometric_le_of_norm_lt_one K hK

/-- On the paper's convenient half-ball, the inverse has norm at most two. -/
theorem norm_neumannInverse_le_two
    (K : H →L[ℂ] H) (hKhalf : ‖K‖ ≤ 1 / 2) :
    ‖neumannInverse K (hKhalf.trans_lt (by norm_num))‖ ≤ 2 := by
  let hK : ‖K‖ < 1 := hKhalf.trans_lt (by norm_num)
  have hden : 0 < 1 - ‖K‖ := sub_pos.mpr hK
  have hinv : (1 - ‖K‖)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hden]
    nlinarith
  exact (norm_neumannInverse_le K hK).trans hinv

omit [Nontrivial H] in
/-- Exact algebraic remainder after truncating the Neumann series at order
`n - 1`. -/
theorem neumannInverse_sub_partialSum
    (K : H →L[ℂ] H) (hK : ‖K‖ < 1) (n : ℕ) :
    neumannInverse K hK - ∑ i ∈ Finset.range n, K ^ i =
      K ^ n * neumannInverse K hK := by
  have horder := NormedRing.inverse_one_sub_nth_order'
    (R := H →L[ℂ] H) n hK
  unfold neumannInverse
  rw [← NormedRing.inverse_one_sub K hK]
  rw [sub_eq_iff_eq_add]
  simpa only [add_comm] using horder

/-- Quantitative geometric tail bound. -/
theorem norm_neumannInverse_sub_partialSum_le
    (K : H →L[ℂ] H) (hK : ‖K‖ < 1) (n : ℕ) :
    ‖neumannInverse K hK - ∑ i ∈ Finset.range n, K ^ i‖ ≤
      ‖K‖ ^ n * (1 - ‖K‖)⁻¹ := by
  rw [neumannInverse_sub_partialSum K hK n]
  calc
    ‖K ^ n * neumannInverse K hK‖ ≤
        ‖K ^ n‖ * ‖neumannInverse K hK‖ := norm_mul_le _ _
    _ ≤ ‖K‖ ^ n * (1 - ‖K‖)⁻¹ := by
      exact mul_le_mul (norm_pow_le K n)
        (norm_neumannInverse_le K hK)
        (norm_nonneg _) (pow_nonneg (norm_nonneg K) n)

/-- Abstract recentered-resolvent bound on the norm-small event. -/
theorem norm_inverseGreen_sub_G_le
    (G M : H →L[ℂ] H) (hK : ‖Kop G M‖ < 1) :
    ‖inverseGreen G M (lopInvertible_of_norm_Kop_lt_one G M hK) - G‖ ≤
      (1 - ‖Kop G M‖)⁻¹ * (‖G‖ * ‖M‖ * ‖G‖) := by
  let hunit : LopInvertible G M :=
    lopInvertible_of_norm_Kop_lt_one G M hK
  have hu :
      hunit.unit = Units.oneSub (Kop G M) hK := by
    apply Units.ext
    exact hunit.unit_spec
  have hinv :
      ‖((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖ ≤
        (1 - ‖Kop G M‖)⁻¹ := by
    rw [hu]
    exact norm_neumannInverse_le (Kop G M) hK
  rw [inverseGreen_sub_G G M hunit]
  calc
    ‖((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) *
        (G * M * G)‖ ≤
        ‖((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖ *
          ‖G * M * G‖ := norm_mul_le _ _
    _ ≤ (1 - ‖Kop G M‖)⁻¹ * (‖G‖ * ‖M‖ * ‖G‖) := by
      apply mul_le_mul hinv
      · exact (norm_mul_le (G * M) G).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le G M) (norm_nonneg G))
      · exact norm_nonneg _
      · have : 0 ≤ (1 - ‖Kop G M‖)⁻¹ := by
          exact inv_nonneg.mpr (sub_nonneg.mpr hK.le)
        exact this

/-- Half-ball specialization used by good-event estimates. -/
theorem norm_inverseGreen_sub_G_le_two
    (G M : H →L[ℂ] H) (hKhalf : ‖Kop G M‖ ≤ 1 / 2) :
    ‖inverseGreen G M
        (lopInvertible_of_norm_Kop_lt_one G M
          (hKhalf.trans_lt (by norm_num))) - G‖ ≤
      2 * (‖G‖ * ‖M‖ * ‖G‖) := by
  let hK : ‖Kop G M‖ < 1 := hKhalf.trans_lt (by norm_num)
  have hden : 0 < 1 - ‖Kop G M‖ := sub_pos.mpr hK
  have hinv : (1 - ‖Kop G M‖)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hden]
    nlinarith
  exact (norm_inverseGreen_sub_G_le G M hK).trans
    (mul_le_mul_of_nonneg_right hinv
      (mul_nonneg (mul_nonneg (norm_nonneg G) (norm_nonneg M))
        (norm_nonneg G)))

end

end Anderson4D
