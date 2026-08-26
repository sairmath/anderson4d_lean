import Anderson4D.Parametrix.HilbertSchmidtDifference
import Anderson4D.Parametrix.L2GreenCompact
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Sup-norm shells for the critical four-dimensional lattice convolution

This file supplies the discrete counting engine for the sharp logarithmic
Green-square convolution.  Frequencies are grouped by their exact integral
sup radius.  A shell has cubic cardinality, so its fourth-order mass is
harmonic and its eighth-order tail is summable with fourth-order decay.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Integral sup radius of a four-dimensional lattice frequency. -/
def z4SupRadius (k : Z4) : ℕ :=
  Finset.univ.sup fun i : Fin dim => Int.natAbs (k i)

theorem z4SupRadius_eq_z4FrequencyNorm (k : Z4) :
    (z4SupRadius k : ℝ) = z4FrequencyNorm k := by
  have hupper :
      z4FrequencyNorm k ≤ (z4SupRadius k : ℝ) := by
    unfold z4FrequencyNorm
    rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    intro i
    rw [Real.norm_eq_abs, ← Int.cast_abs,
      ← Int.natCast_natAbs]
    exact_mod_cast
      (Finset.le_sup (f := fun j : Fin dim =>
        Int.natAbs (k j)) (Finset.mem_univ i))
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Fin dim)))
      Finset.univ_nonempty
      (fun j : Fin dim => Int.natAbs (k j))
  have hlower :
      (z4SupRadius k : ℝ) ≤ z4FrequencyNorm k := by
    calc
      (z4SupRadius k : ℝ) =
          (Int.natAbs (k i) : ℝ) := by
        exact_mod_cast
          ((Finset.sup'_eq_sup
            Finset.univ_nonempty
            (fun j : Fin dim => Int.natAbs (k j))).symm.trans hmax)
      _ = |(k i : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      _ ≤ z4FrequencyNorm k := by
        exact znorm_coord_le k i
  exact le_antisymm hlower hupper

theorem mem_z4Cube_iff_z4SupRadius_le
    (n : ℕ) (k : Z4) :
    k ∈ z4Cube n ↔ z4SupRadius k ≤ n := by
  rw [mem_z4Cube]
  constructor
  · intro hk
    apply Finset.sup_le
    intro i _
    have habs : |k i| ≤ (n : ℤ) :=
      (abs_le).2 (hk i)
    have habs' : (Int.natAbs (k i) : ℤ) ≤ (n : ℤ) := by
      simpa only [Int.abs_eq_natAbs] using habs
    exact_mod_cast habs'
  · intro hk i
    have hi :
        Int.natAbs (k i) ≤ n :=
      (Finset.le_sup (f := fun j : Fin dim =>
        Int.natAbs (k j)) (Finset.mem_univ i)).trans hk
    have habs' : (Int.natAbs (k i) : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hi
    have habs : |k i| ≤ (n : ℤ) := by
      simpa only [Int.abs_eq_natAbs] using habs'
    exact (abs_le.mp habs)

/-- Exact integral sup-radius shell. -/
def z4SupShell : ℕ → Finset Z4
  | 0 => z4Cube 0
  | n + 1 => z4Cube (n + 1) \ z4Cube n

@[simp] theorem mem_z4SupShell (n : ℕ) (k : Z4) :
    k ∈ z4SupShell n ↔ z4SupRadius k = n := by
  cases n with
  | zero =>
      change k ∈ z4Cube 0 ↔ z4SupRadius k = 0
      rw [mem_z4Cube_iff_z4SupRadius_le]
      omega
  | succ n =>
      simp only [z4SupShell, Finset.mem_sdiff,
        mem_z4Cube_iff_z4SupRadius_le]
      omega

theorem card_z4Cube (n : ℕ) :
    (z4Cube n).card = (2 * n + 1) ^ 4 := by
  classical
  unfold z4Cube
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, dim]
  congr 1
  omega

theorem z4Cube_mono {m n : ℕ} (hmn : m ≤ n) :
    z4Cube m ⊆ z4Cube n := by
  intro k hk
  rw [mem_z4Cube_iff_z4SupRadius_le] at hk ⊢
  exact hk.trans hmn

theorem card_z4SupShell : ∀ n : ℕ,
    (z4SupShell n).card =
      if n = 0 then 1 else
        (2 * n + 1) ^ 4 - (2 * n - 1) ^ 4
  | 0 => by
      simp [z4SupShell, card_z4Cube]
  | n + 1 => by
      rw [if_neg (by omega)]
      unfold z4SupShell
      rw [Finset.card_sdiff_of_subset
          (z4Cube_mono (Nat.le_succ n)),
        card_z4Cube, card_z4Cube]
      congr 2

/-- Cubic shell count, with a generous explicit constant. -/
theorem card_z4SupShell_le (n : ℕ) :
    (z4SupShell n).card ≤ 80 * (n + 1) ^ 3 := by
  rw [card_z4SupShell]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hminus :
        2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [hminus]
    have hpoly :
        (2 * (m + 1) + 1) ^ 4 - (2 * m + 1) ^ 4 =
          64 * (m + 1) ^ 3 + 16 * (m + 1) := by
      have hcard :
          (2 * m + 1) ^ 4 ≤
            (2 * (m + 1) + 1) ^ 4 := by
        gcongr
        omega
      have hadd :
          ((2 * (m + 1) + 1) ^ 4 -
              (2 * m + 1) ^ 4) +
              (2 * m + 1) ^ 4 =
            (64 * (m + 1) ^ 3 + 16 * (m + 1)) +
              (2 * m + 1) ^ 4 := by
        rw [Nat.sub_add_cancel hcard]
        ring_nf
      exact Nat.add_right_cancel hadd
    rw [hpoly]
    have hcubic :
        (m + 1) ^ 3 ≤ (m + 2) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    have hlinear :
        m + 1 ≤ (m + 2) ^ 3 := by
      exact (by omega : m + 1 ≤ m + 2).trans
        (le_self_pow (by omega : 1 ≤ m + 2) (by norm_num))
    calc
      64 * (m + 1) ^ 3 + 16 * (m + 1) ≤
          64 * (m + 2) ^ 3 + 16 * (m + 2) ^ 3 :=
        Nat.add_le_add
          (Nat.mul_le_mul_left 64 hcubic)
          (Nat.mul_le_mul_left 16 hlinear)
      _ = 80 * (m + 2) ^ 3 := by ring

theorem l2LatticeRadialWeight_eq_z4SupRadius
    (q : ℕ) (k : Z4) :
    l2LatticeRadialWeight q k =
      ((1 + (z4SupRadius k : ℝ)) ^ q)⁻¹ := by
  unfold l2LatticeRadialWeight
  rw [z4SupRadius_eq_z4FrequencyNorm]

/-- Fourth-order mass in a finite cube is bounded by the corresponding
harmonic shell sum. -/
theorem sum_z4Cube_l2LatticeRadialWeight_four_le
    (N : ℕ) :
    (∑ k ∈ z4Cube N, l2LatticeRadialWeight 4 k) ≤
      80 * ∑ n ∈ Finset.range (N + 1),
        ((n + 1 : ℕ) : ℝ)⁻¹ := by
  classical
  have hmaps :
      ∀ k ∈ z4Cube N,
        z4SupRadius k ∈ Finset.range (N + 1) := by
    intro k hk
    rw [Finset.mem_range]
    rw [mem_z4Cube_iff_z4SupRadius_le] at hk
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun k => l2LatticeRadialWeight 4 k)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnN : n ≤ N := by
    rw [Finset.mem_range] at hn
    omega
  let F : Finset Z4 :=
    (z4Cube N).filter fun k => z4SupRadius k = n
  have hFsub : F ⊆ z4SupShell n := by
    intro k hk
    change k ∈
      (z4Cube N).filter (fun j => z4SupRadius j = n) at hk
    rw [Finset.mem_filter] at hk
    rw [mem_z4SupShell]
    exact hk.2
  have hcardNat :
      F.card ≤ 80 * (n + 1) ^ 3 :=
    (Finset.card_le_card hFsub).trans
      (card_z4SupShell_le n)
  have hcard :
      (F.card : ℝ) ≤ 80 * ((n + 1 : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast hcardNat
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    (∑ k ∈ z4Cube N with z4SupRadius k = n,
        l2LatticeRadialWeight 4 k) =
        ∑ _k ∈ F,
          (((n + 1 : ℕ) : ℝ) ^ 4)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k hk
      change k ∈
        (z4Cube N).filter (fun j => z4SupRadius j = n) at hk
      rw [Finset.mem_filter] at hk
      rw [l2LatticeRadialWeight_eq_z4SupRadius,
        hk.2]
      push_cast
      ring
    _ = (F.card : ℝ) *
        (((n + 1 : ℕ) : ℝ) ^ 4)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (80 * ((n + 1 : ℕ) : ℝ) ^ 3) *
        (((n + 1 : ℕ) : ℝ) ^ 4)⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 80 * ((n + 1 : ℕ) : ℝ)⁻¹ := by
      field_simp

/-- Logarithmic form of the finite fourth-order shell bound. -/
theorem sum_z4Cube_l2LatticeRadialWeight_four_le_log
    (N : ℕ) :
    (∑ k ∈ z4Cube N, l2LatticeRadialWeight 4 k) ≤
      80 * (1 + Real.log (N + 1)) := by
  refine (sum_z4Cube_l2LatticeRadialWeight_four_le N).trans ?_
  have hsum :
      (∑ n ∈ Finset.range (N + 1),
          ((n + 1 : ℕ) : ℝ)⁻¹) =
        (harmonic (N + 1) : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
  rw [hsum]
  exact mul_le_mul_of_nonneg_left
    (by
      simpa only [Nat.cast_add, Nat.cast_one] using
        harmonic_le_one_add_log (N + 1))
    (by norm_num)

/-- The fibre of the integral sup radius is the corresponding finite shell. -/
def z4SupRadiusFiberEquiv (n : ℕ) :
    {k : Z4 // z4SupRadius k = n} ≃ ↥(z4SupShell n) where
  toFun k := ⟨k.1, (mem_z4SupShell n k.1).2 k.2⟩
  invFun k := ⟨k.1, (mem_z4SupShell n k.1).1 k.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tsum_z4SupRadius_fiber_eq_sum_shell
    (f : Z4 → ℝ) (n : ℕ) :
    (∑' k : {k : Z4 // z4SupRadius k = n}, f k.1) =
      ∑ k ∈ z4SupShell n, f k := by
  calc
    (∑' k : {k : Z4 // z4SupRadius k = n}, f k.1) =
        ∑' k : ↥(z4SupShell n), f k.1 := by
      rw [← (z4SupRadiusFiberEquiv n).tsum_eq]
      apply tsum_congr
      intro k
      rfl
    _ = ∑ k ∈ z4SupShell n, f k := by
      rw [tsum_fintype, ← (z4SupShell n).sum_attach,
        Finset.attach_eq_univ]

def z4SupRadiusPreimageEquiv (n : ℕ) :
    ↥(z4SupRadius ⁻¹' ({n} : Set ℕ)) ≃
      {k : Z4 // z4SupRadius k = n} where
  toFun k := ⟨k.1, by
    exact Set.mem_singleton_iff.mp k.2⟩
  invFun k := ⟨k.1, by
    exact Set.mem_singleton_iff.mpr k.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tsum_z4SupRadius_preimage_eq_sum_shell
    (f : Z4 → ℝ) (n : ℕ) :
    (∑' k : ↥(z4SupRadius ⁻¹' ({n} : Set ℕ)), f k.1) =
      ∑ k ∈ z4SupShell n, f k := by
  calc
    (∑' k : ↥(z4SupRadius ⁻¹' ({n} : Set ℕ)), f k.1) =
        ∑' k : {k : Z4 // z4SupRadius k = n}, f k.1 := by
      rw [← (z4SupRadiusPreimageEquiv n).tsum_eq]
      apply tsum_congr
      intro k
      rfl
    _ = ∑ k ∈ z4SupShell n, f k :=
      tsum_z4SupRadius_fiber_eq_sum_shell f n

/-- Regroup a summable nonnegative lattice series by its exact sup radius. -/
theorem tsum_eq_tsum_z4SupShell
    (f : Z4 → ℝ) (hf : Summable f) :
    (∑' k : Z4, f k) =
      ∑' n : ℕ, ∑ k ∈ z4SupShell n, f k := by
  have hgroup := hf.hasSum.tsum_fiberwise z4SupRadius
  calc
    (∑' k : Z4, f k) =
        ∑' n : ℕ,
          ∑' k : ↥(z4SupRadius ⁻¹' ({n} : Set ℕ)), f k.1 :=
      hgroup.tsum_eq.symm
    _ = ∑' n : ℕ, ∑ k ∈ z4SupShell n, f k := by
      apply tsum_congr
      intro n
      exact tsum_z4SupRadius_preimage_eq_sum_shell f n

theorem l2LatticeRadialWeight_eight_le_five (k : Z4) :
    l2LatticeRadialWeight 8 k ≤
      l2LatticeRadialWeight 5 k := by
  let R : ℝ := 1 + z4FrequencyNorm k
  have hR : 1 ≤ R := by
    dsimp only [R]
    linarith [z4FrequencyNorm_nonneg k]
  unfold l2LatticeRadialWeight
  change (R ^ 8)⁻¹ ≤ (R ^ 5)⁻¹
  exact inv_anti₀ (by positivity)
    (pow_le_pow_right₀ hR (by norm_num))

theorem summable_l2LatticeRadialWeight_eight :
    Summable (l2LatticeRadialWeight 8) :=
  summable_l2LatticeRadialWeight_five.of_nonneg_of_le
    (fun k => by unfold l2LatticeRadialWeight; positivity)
    l2LatticeRadialWeight_eight_le_five

/-- One eighth-order shell has fifth-order residual decay after its cubic
cardinality is paid. -/
theorem sum_z4SupShell_l2LatticeRadialWeight_eight_le
    (n : ℕ) :
    (∑ k ∈ z4SupShell n, l2LatticeRadialWeight 8 k) ≤
      80 * ((n + 1 : ℕ) : ℝ)⁻¹ ^ 5 := by
  have hcard :
      ((z4SupShell n).card : ℝ) ≤
        80 * ((n + 1 : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast card_z4SupShell_le n
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    (∑ k ∈ z4SupShell n,
        l2LatticeRadialWeight 8 k) =
        ∑ _k ∈ z4SupShell n,
          (((n + 1 : ℕ) : ℝ) ^ 8)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [l2LatticeRadialWeight_eq_z4SupRadius,
        (mem_z4SupShell n k).1 hk]
      push_cast
      ring
    _ = ((z4SupShell n).card : ℝ) *
        (((n + 1 : ℕ) : ℝ) ^ 8)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (80 * ((n + 1 : ℕ) : ℝ) ^ 3) *
        (((n + 1 : ℕ) : ℝ) ^ 8)⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 80 * ((n + 1 : ℕ) : ℝ)⁻¹ ^ 5 := by
      field_simp

theorem inv_pow_five_eq_rpow_neg_five
    {x : ℝ} :
    x⁻¹ ^ 5 = x ^ (-(5 : ℝ)) := by
  calc
    x⁻¹ ^ 5 = x⁻¹ ^ (5 : ℝ) :=
      (Real.rpow_natCast x⁻¹ 5).symm
    _ = x ^ (-(5 : ℝ)) :=
      (Real.rpow_neg_eq_inv_rpow x (5 : ℝ)).symm

/-- Explicit integral-test tail for the fifth-order scalar series. -/
theorem tsum_inv_nat_add_pow_five_le
    (N : ℕ) (hN : 0 < N) :
    (∑' j : ℕ,
        (((j + N + 1 : ℕ) : ℝ)⁻¹) ^ 5) ≤
      (4 : ℝ)⁻¹ * (((N : ℝ)⁻¹) ^ 4) := by
  let f : ℝ → ℝ := fun x => x ^ (-(5 : ℝ))
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hanti : AntitoneOn f (Set.Ici (N : ℝ)) := by
    exact
      (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
        (by norm_num : (-(5 : ℝ)) ≤ 0)).mono
        (fun x hx => hNreal.trans_le hx)
  have hint :
      MeasureTheory.IntegrableOn f (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-(5 : ℝ)) < -1) hNreal
  have hnonneg :
      ∀ x ∈ Set.Ioi (N : ℝ), 0 ≤ f x :=
    fun x hx => Real.rpow_nonneg (hNreal.trans hx).le _
  have htail :=
    hanti.tsum_comp_add_le_integral N hint hnonneg
  have hconvert :
      (∑' j : ℕ,
          (((j + N + 1 : ℕ) : ℝ)⁻¹) ^ 5) ≤
        ∫ x : ℝ in Set.Ioi (N : ℝ), f x := by
    convert htail using 1
    apply tsum_congr
    intro j
    rw [inv_pow_five_eq_rpow_neg_five]
  rw [integral_Ioi_rpow_of_lt
    (by norm_num : (-(5 : ℝ)) < -1) hNreal] at hconvert
  calc
    (∑' j : ℕ,
        (((j + N + 1 : ℕ) : ℝ)⁻¹) ^ 5) ≤
        -(N : ℝ) ^ (-(5 : ℝ) + 1) /
          (-(5 : ℝ) + 1) := hconvert
    _ = (4 : ℝ)⁻¹ * (((N : ℝ)⁻¹) ^ 4) := by
      rw [show (-(5 : ℝ)) + 1 = -4 by norm_num]
      rw [Real.rpow_neg_eq_inv_rpow]
      ring_nf
      exact congrArg (fun y : ℝ => y * (1 / 4))
        (Real.rpow_natCast ((N : ℝ)⁻¹) 4)

end

end Anderson4D
