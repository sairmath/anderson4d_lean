import Anderson4D.Continuum.CutoffFourierDecay

/-!
# Summability of the deterministic cutoff multiplier

This module is the layer-L2 home of the lattice majorants for the
Fourier multiplier of a fixed smooth cutoff.  The results are purely
deterministic and are shared by the random Fourier-series construction
and the R-324 frequency-routing argument.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Product `p`-series weight on `ℤ⁴`.  The exponent two in each
coordinate makes it summable and its total polynomial degree is eight. -/
def latticeSummabilityWeight (k : Z4) : ℝ :=
  ∏ i, (((Int.natAbs (k i) : ℝ) + 1) ^ 2)⁻¹

/-- A convenient polynomial lattice weight.  The added one in every
coordinate avoids exceptional treatment of the zero mode. -/
def latticePolynomialWeight (r : ℕ) (k : Z4) : ℝ :=
  (∑ i, ((Int.natAbs (k i) : ℝ) + 1)) ^ r

theorem latticePolynomialWeight_nonneg (r : ℕ) (k : Z4) :
    0 ≤ latticePolynomialWeight r k := by
  unfold latticePolynomialWeight
  exact pow_nonneg (Finset.sum_nonneg fun i hi => by positivity) _

private theorem summable_int_natAbs_succ_sq_inv :
    Summable fun m : ℤ => (((Int.natAbs m : ℝ) + 1) ^ 2)⁻¹ := by
  have hnat :
      Summable fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹ := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 2).mpr
        (by norm_num : (1 : ℝ) < 2)
    refine h.congr fun n => ?_
    rw [one_div, abs_of_nonneg (by positivity)]
    rw [Real.rpow_two]
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · simpa using hnat
  · have hshift :
        Summable fun n : ℕ => ((((n + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹ :=
      hnat.comp_injective Nat.succ_injective
    refine hshift.congr fun n => ?_
    change
      (((Int.natAbs (-((n : ℤ) + 1)) : ℝ) + 1) ^ 2)⁻¹ =
        ((((n + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹
    rw [show -((n : ℤ) + 1) = Int.negSucc n by omega,
      Int.natAbs_negSucc]

/-- Summability over a finite product of integer copies, obtained by
iterating the binary product theorem. -/
private theorem summable_pi_product {g : ℤ → ℝ}
    (h0 : ∀ m, 0 ≤ g m) (hg : Summable g) :
    ∀ n : ℕ, Summable fun k : Fin n → ℤ => ∏ i, g (k i) := by
  intro n
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    have hg0 : (0 : ℤ → ℝ) ≤ g := fun m => h0 m
    have hp0 : (0 : (Fin n → ℤ) → ℝ) ≤ fun k => ∏ i, g (k i) :=
      fun k => Finset.prod_nonneg fun i _ => h0 _
    have hstep :
        Summable fun p : ℤ × (Fin n → ℤ) =>
          g p.1 * ∏ i, g (p.2 i) :=
      @Summable.mul_of_nonneg ℤ (Fin n → ℤ) g
        (fun k => ∏ i, g (k i)) hg ih hg0 hp0
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]
    refine hstep.congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

/-- The explicit degree-eight product weight is summable on `ℤ⁴`. -/
theorem summable_latticeSummabilityWeight :
    Summable latticeSummabilityWeight := by
  unfold latticeSummabilityWeight
  exact summable_pi_product
    (fun m => inv_nonneg.mpr (sq_nonneg _))
    summable_int_natAbs_succ_sq_inv dim

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- At every positive scale the cutoff symbol is dominated by a fixed
summable product weight on `ℤ⁴`. -/
theorem exists_symbol_norm_le_latticeSummabilityWeight
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : Z4,
      ‖ρ.symbol ε k‖ ≤ C * latticeSummabilityWeight k := by
  obtain ⟨C0, hC0, hcut⟩ := ρ.exists_fourierR4_one_add_norm_bound
  let d : ℝ := min 1 (ε / (2 * Real.pi))
  have hd : 0 < d := lt_min zero_lt_one (by positivity)
  let C : ℝ := C0 * d⁻¹ ^ 8
  refine ⟨C, mul_pos hC0 (pow_pos (inv_pos.mpr hd) _), fun k => ?_⟩
  let ξ : R4 := fun i => ε * (k i : ℝ)
  let w : EuclideanR4 := euclideanFrequency ξ
  let P : ℝ := ∏ i, ((Int.natAbs (k i) : ℝ) + 1) ^ 2
  have hcoord (i : Fin dim) :
      d * ((Int.natAbs (k i) : ℝ) + 1) ≤ 1 + ‖w‖ := by
    have hd1 : d ≤ 1 := min_le_left _ _
    have hdε : d ≤ ε / (2 * Real.pi) := min_le_right _ _
    have hki :
        ε / (2 * Real.pi) * (Int.natAbs (k i) : ℝ) ≤ ‖w‖ := by
      calc
        ε / (2 * Real.pi) * (Int.natAbs (k i) : ℝ) =
            ‖w i‖ := by
          simp only [w, ξ, euclideanFrequency_apply, Real.norm_eq_abs]
          rw [abs_div, abs_mul, abs_of_pos hε,
            abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
            Nat.cast_natAbs, Int.cast_abs]
          field_simp
        _ ≤ ‖w‖ := PiLp.norm_apply_le w i
    calc
      d * ((Int.natAbs (k i) : ℝ) + 1) =
          d * (Int.natAbs (k i) : ℝ) + d := by ring
      _ ≤ ε / (2 * Real.pi) * (Int.natAbs (k i) : ℝ) + 1 := by
        gcongr
      _ ≤ ‖w‖ + 1 := by gcongr
      _ = 1 + ‖w‖ := by ring
  have hprod :
      d ^ 8 * P ≤ (1 + ‖w‖) ^ 8 := by
    have hsquares :
        ∏ i, (d * ((Int.natAbs (k i) : ℝ) + 1)) ^ 2 ≤
          ∏ _i : Fin dim, (1 + ‖w‖) ^ 2 := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact pow_le_pow_left₀ (by positivity) (hcoord i) 2
    calc
      d ^ 8 * P =
          ∏ i, (d * ((Int.natAbs (k i) : ℝ) + 1)) ^ 2 := by
        symm
        calc
          _ = ∏ i, d ^ 2 *
              (((Int.natAbs (k i) : ℝ) + 1) ^ 2) := by
            apply Finset.prod_congr rfl
            intro i hi
            ring
          _ = (∏ _i : Fin dim, d ^ 2) * P := by
            rw [Finset.prod_mul_distrib]
          _ = d ^ 8 * P := by
            rw [Finset.prod_const]
            change (d ^ 2) ^ 4 * P = d ^ 8 * P
            ring
      _ ≤ ∏ _i : Fin dim, (1 + ‖w‖) ^ 2 := hsquares
      _ = (1 + ‖w‖) ^ 8 := by
        rw [Finset.prod_const]
        change ((1 + ‖w‖) ^ 2) ^ 4 = (1 + ‖w‖) ^ 8
        ring
  have hschwartz :
      (1 + ‖w‖) ^ 8 * ‖ρ.symbol ε k‖ ≤ C0 := by
    simpa [w, ξ, SmoothCutoff.symbol] using hcut ξ
  have hPpos : 0 < P := by
    unfold P
    exact Finset.prod_pos fun i hi => sq_pos_of_pos (by positivity)
  have hden : 0 < d ^ 8 * P := mul_pos (pow_pos hd _) hPpos
  have hcombined :
      d ^ 8 * P * ‖ρ.symbol ε k‖ ≤ C0 :=
    (mul_le_mul_of_nonneg_right hprod (norm_nonneg _)).trans hschwartz
  have hdivide :
      ‖ρ.symbol ε k‖ ≤ C0 / (d ^ 8 * P) := by
    exact (le_div_iff₀ hden).2
      (by simpa [mul_assoc, mul_comm, mul_left_comm] using hcombined)
  calc
    ‖ρ.symbol ε k‖ ≤ C0 / (d ^ 8 * P) := hdivide
    _ = C * latticeSummabilityWeight k := by
      simp only [C, latticeSummabilityWeight, Finset.prod_inv_distrib]
      change C0 / (d ^ 8 * P) = C0 * d⁻¹ ^ 8 * P⁻¹
      field_simp [hd.ne', hPpos.ne']

/-- Consequently, every positive-scale cutoff symbol is absolutely
summable on the Fourier lattice. -/
theorem summable_norm_symbol {ε : ℝ} (hε : 0 < ε) :
    Summable fun k : Z4 => ‖ρ.symbol ε k‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    ρ.exists_symbol_norm_le_latticeSummabilityWeight hε
  exact (summable_latticeSummabilityWeight.mul_left C).of_nonneg_of_le
    (fun k => norm_nonneg _) hbound

/-- Rapid decay survives multiplication by a polynomial lattice weight
of arbitrary degree. -/
theorem exists_latticePolynomialWeight_mul_norm_symbol_le
    (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : Z4,
      latticePolynomialWeight r k * ‖ρ.symbol ε k‖ ≤
        C * latticeSummabilityWeight k := by
  obtain ⟨C0, hC0, hcut⟩ :=
    ρ.exists_fourierR4_one_add_norm_bound_nat (8 + r)
  let d : ℝ := min 1 (ε / (2 * Real.pi))
  have hd : 0 < d := lt_min zero_lt_one (by positivity)
  let C : ℝ := 4 ^ r * C0 * d⁻¹ ^ (8 + r)
  refine ⟨C, mul_pos (mul_pos (pow_pos (by norm_num) _) hC0)
    (pow_pos (inv_pos.mpr hd) _), fun k => ?_⟩
  let ξ : R4 := fun i => ε * (k i : ℝ)
  let w : EuclideanR4 := euclideanFrequency ξ
  let B : ℝ := 1 + ‖w‖
  let P : ℝ := ∏ i, ((Int.natAbs (k i) : ℝ) + 1) ^ 2
  let Q : ℝ := ∑ i, ((Int.natAbs (k i) : ℝ) + 1)
  have hcoord (i : Fin dim) :
      d * ((Int.natAbs (k i) : ℝ) + 1) ≤ B := by
    have hd1 : d ≤ 1 := min_le_left _ _
    have hdε : d ≤ ε / (2 * Real.pi) := min_le_right _ _
    have hki :
        ε / (2 * Real.pi) * (Int.natAbs (k i) : ℝ) ≤ ‖w‖ := by
      calc
        ε / (2 * Real.pi) * (Int.natAbs (k i) : ℝ) =
            ‖w i‖ := by
          simp only [w, ξ, euclideanFrequency_apply, Real.norm_eq_abs]
          rw [abs_div, abs_mul, abs_of_pos hε,
            abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
            Nat.cast_natAbs, Int.cast_abs]
          field_simp
        _ ≤ ‖w‖ := PiLp.norm_apply_le w i
    dsimp only [B]
    calc
      d * ((Int.natAbs (k i) : ℝ) + 1) =
          d * (Int.natAbs (k i) : ℝ) + d := by ring
      _ ≤ ε / (2 * Real.pi) * (Int.natAbs (k i) : ℝ) + 1 := by
        gcongr
      _ ≤ ‖w‖ + 1 := by gcongr
      _ = 1 + ‖w‖ := by ring
  have hprod : d ^ 8 * P ≤ B ^ 8 := by
    have hsquares :
        ∏ i, (d * ((Int.natAbs (k i) : ℝ) + 1)) ^ 2 ≤
          ∏ _i : Fin dim, B ^ 2 := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact pow_le_pow_left₀ (by positivity) (hcoord i) 2
    calc
      d ^ 8 * P =
          ∏ i, (d * ((Int.natAbs (k i) : ℝ) + 1)) ^ 2 := by
        symm
        calc
          _ = ∏ i, d ^ 2 *
              (((Int.natAbs (k i) : ℝ) + 1) ^ 2) := by
            apply Finset.prod_congr rfl
            intro i hi
            ring
          _ = (∏ _i : Fin dim, d ^ 2) * P := by
            rw [Finset.prod_mul_distrib]
          _ = d ^ 8 * P := by
            rw [Finset.prod_const]
            change (d ^ 2) ^ 4 * P = d ^ 8 * P
            ring
      _ ≤ ∏ _i : Fin dim, B ^ 2 := hsquares
      _ = B ^ 8 := by
        rw [Finset.prod_const]
        change (B ^ 2) ^ 4 = B ^ 8
        ring
  have hsum : d * Q ≤ 4 * B := by
    calc
      d * Q =
          ∑ i, d * ((Int.natAbs (k i) : ℝ) + 1) := by
        simp [Q, Finset.mul_sum]
      _ ≤ ∑ _i : Fin dim, B := by
        exact Finset.sum_le_sum fun i hi => hcoord i
      _ = 4 * B := by simp [dim]
  have hsum_pow : d ^ r * Q ^ r ≤ 4 ^ r * B ^ r := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hsum r
  have htotal :
      d ^ (8 + r) * P * Q ^ r ≤ 4 ^ r * B ^ (8 + r) := by
    calc
      d ^ (8 + r) * P * Q ^ r =
          (d ^ 8 * P) * (d ^ r * Q ^ r) := by
        rw [pow_add]
        ring
      _ ≤ B ^ 8 * (4 ^ r * B ^ r) := by
        gcongr
      _ = 4 ^ r * B ^ (8 + r) := by
        rw [pow_add]
        ring
  have hschwartz :
      B ^ (8 + r) * ‖ρ.symbol ε k‖ ≤ C0 := by
    simpa [B, w, ξ, SmoothCutoff.symbol] using hcut ξ
  have hPpos : 0 < P := by
    unfold P
    exact Finset.prod_pos fun i hi => sq_pos_of_pos (by positivity)
  have hden : 0 < d ^ (8 + r) * P :=
    mul_pos (pow_pos hd _) hPpos
  have hcombined :
      d ^ (8 + r) * P * Q ^ r * ‖ρ.symbol ε k‖ ≤
        4 ^ r * C0 := by
    calc
      _ ≤ 4 ^ r * B ^ (8 + r) * ‖ρ.symbol ε k‖ := by
        exact mul_le_mul_of_nonneg_right htotal (norm_nonneg _)
      _ = 4 ^ r * (B ^ (8 + r) * ‖ρ.symbol ε k‖) := by
        ring
      _ ≤ 4 ^ r * C0 :=
        mul_le_mul_of_nonneg_left hschwartz (pow_nonneg (by norm_num) _)
  have hdivide :
      Q ^ r * ‖ρ.symbol ε k‖ ≤
        (4 ^ r * C0) / (d ^ (8 + r) * P) := by
    exact (le_div_iff₀ hden).2
      (by simpa [mul_assoc, mul_comm, mul_left_comm] using hcombined)
  change Q ^ r * ‖ρ.symbol ε k‖ ≤ C * latticeSummabilityWeight k
  calc
    Q ^ r * ‖ρ.symbol ε k‖ ≤
        (4 ^ r * C0) / (d ^ (8 + r) * P) := hdivide
    _ = C * latticeSummabilityWeight k := by
      simp only [C, latticeSummabilityWeight, Finset.prod_inv_distrib]
      change
        (4 ^ r * C0) / (d ^ (8 + r) * P) =
          4 ^ r * C0 * d⁻¹ ^ (8 + r) * P⁻¹
      rw [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring

/-- Every polynomially weighted cutoff symbol is absolutely summable. -/
theorem summable_latticePolynomialWeight_mul_norm_symbol
    (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Summable fun k : Z4 =>
      latticePolynomialWeight r k * ‖ρ.symbol ε k‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    ρ.exists_latticePolynomialWeight_mul_norm_symbol_le r hε
  exact (summable_latticeSummabilityWeight.mul_left C).of_nonneg_of_le
    (fun k => mul_nonneg
      (pow_nonneg (Finset.sum_nonneg fun i hi => by positivity) _)
      (norm_nonneg _)) hbound

end SmoothCutoff

end

end Anderson4D
