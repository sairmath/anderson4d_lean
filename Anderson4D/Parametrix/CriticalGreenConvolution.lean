import Anderson4D.Parametrix.CriticalLatticeShells
import Mathlib.Analysis.PSeries

/-!
# The sharp critical Green-square convolution

This file turns the shell-counting engine into the four-dimensional
logarithmic convolution estimate.  The proof splits the lattice into the two
endpoint regions and the residual region where both endpoints are large.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Translation identifies `ℕ` with the natural-number tail above `N`. -/
def natAddIciEquiv (N : ℕ) :
    ℕ ≃ Set.Ici N where
  toFun j := ⟨j + N, by
    change N ≤ j + N
    omega⟩
  invFun n := n.1 - N
  left_inv j := by simp
  right_inv n := by
    apply Subtype.ext
    exact Nat.sub_add_cancel n.2

/-- Eighth-order radial mass outside the integral sup-radius `N`. -/
def z4EighthRadialTail (N : ℕ) (k : Z4) : ℝ :=
  if N ≤ z4SupRadius k then
    l2LatticeRadialWeight 8 k
  else 0

theorem summable_z4EighthRadialTail (N : ℕ) :
    Summable (z4EighthRadialTail N) := by
  exact summable_l2LatticeRadialWeight_eight.of_nonneg_of_le
    (fun k => by
      unfold z4EighthRadialTail
      by_cases hk : N ≤ z4SupRadius k
      · rw [if_pos hk]
        unfold l2LatticeRadialWeight
        positivity
      · rw [if_neg hk])
    (fun k => by
      unfold z4EighthRadialTail
      by_cases hk : N ≤ z4SupRadius k
      · rw [if_pos hk]
      · rw [if_neg hk]
        unfold l2LatticeRadialWeight
        positivity)

theorem summable_scalar_fifth_shell_major :
    Summable fun n : ℕ =>
      80 * (((n + 1 : ℕ) : ℝ)⁻¹) ^ 5 := by
  have hfull :
      Summable fun n : ℕ => (((n : ℝ) ^ 5)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hshift :
      Summable fun n : ℕ =>
        ((((n + 1 : ℕ) : ℝ) ^ 5)⁻¹) := by
    refine (hfull.comp_injective
        (show Function.Injective (fun n : ℕ => n + 1) by
          intro a b h
          exact Nat.add_right_cancel h)).congr ?_
    intro n
    rfl
  simpa only [inv_pow] using hshift.mul_left 80

theorem tsum_z4EighthRadialTail_le
    (N : ℕ) (hN : 0 < N) :
    (∑' k : Z4, z4EighthRadialTail N k) ≤
      20 * (((N : ℝ)⁻¹) ^ 4) := by
  let g : ℕ → ℝ := fun n =>
    80 * (((n + 1 : ℕ) : ℝ)⁻¹) ^ 5
  have hg : Summable g := by
    simpa only [g] using summable_scalar_fifth_shell_major
  have hmajorSummable :
      Summable fun n : ℕ =>
        if N ≤ n then g n else 0 :=
    hg.of_nonneg_of_le
      (fun n => by
        by_cases hn : N ≤ n
        · rw [if_pos hn]
          dsimp only [g]
          positivity
        · rw [if_neg hn])
      (fun n => by
        by_cases hn : N ≤ n
        · rw [if_pos hn]
        · rw [if_neg hn]
          dsimp only [g]
          positivity)
  have hshell (n : ℕ) :
      (∑ k ∈ z4SupShell n, z4EighthRadialTail N k) =
        if N ≤ n then
          ∑ k ∈ z4SupShell n,
            l2LatticeRadialWeight 8 k
        else 0 := by
    by_cases hn : N ≤ n
    · rw [if_pos hn]
      apply Finset.sum_congr rfl
      intro k hk
      unfold z4EighthRadialTail
      rw [if_pos]
      simpa only [(mem_z4SupShell n k).1 hk] using hn
    · rw [if_neg hn]
      apply Finset.sum_eq_zero
      intro k hk
      unfold z4EighthRadialTail
      rw [if_neg]
      intro hNk
      apply hn
      simpa only [(mem_z4SupShell n k).1 hk] using hNk
  have hgroup :
      (∑' k : Z4, z4EighthRadialTail N k) =
        ∑' n : ℕ,
          ∑ k ∈ z4SupShell n,
            z4EighthRadialTail N k :=
    tsum_eq_tsum_z4SupShell _
      (summable_z4EighthRadialTail N)
  have hpoint (n : ℕ) :
      (∑ k ∈ z4SupShell n, z4EighthRadialTail N k) ≤
        if N ≤ n then g n else 0 := by
    rw [hshell]
    by_cases hn : N ≤ n
    · rw [if_pos hn, if_pos hn]
      exact sum_z4SupShell_l2LatticeRadialWeight_eight_le n
    · rw [if_neg hn, if_neg hn]
  have htailReindex :
      (∑' n : ℕ, if N ≤ n then g n else 0) =
        ∑' j : ℕ, g (j + N) := by
    calc
      (∑' n : ℕ, if N ≤ n then g n else 0) =
          ∑' n : Set.Ici N, g n.1 := by
        rw [tsum_subtype (Set.Ici N) g]
        apply tsum_congr
        intro n
        by_cases hn : N ≤ n
        · simp [hn]
        · simp [hn]
      _ = ∑' j : ℕ, g (j + N) := by
        rw [← (natAddIciEquiv N).tsum_eq]
        apply tsum_congr
        intro j
        rfl
  calc
    (∑' k : Z4, z4EighthRadialTail N k) =
        ∑' n : ℕ,
          ∑ k ∈ z4SupShell n,
            z4EighthRadialTail N k := hgroup
    _ ≤ ∑' n : ℕ, if N ≤ n then g n else 0 :=
      (summable_z4EighthRadialTail N
        |>.hasSum.tsum_fiberwise z4SupRadius
        |>.summable.congr
          (fun n => by
            rw [tsum_z4SupRadius_preimage_eq_sum_shell,
              hshell n]))
        |>.tsum_le_tsum hpoint hmajorSummable
    _ = ∑' j : ℕ, g (j + N) := htailReindex
    _ = 80 * ∑' j : ℕ,
        (((j + N + 1 : ℕ) : ℝ)⁻¹) ^ 5 := by
      rw [tsum_mul_left]
    _ ≤ 80 * ((4 : ℝ)⁻¹ * (((N : ℝ)⁻¹) ^ 4)) :=
      mul_le_mul_of_nonneg_left
        (tsum_inv_nat_add_pow_five_le N hN) (by norm_num)
    _ = 20 * (((N : ℝ)⁻¹) ^ 4) := by ring

/-- Fourth-order radial mass truncated to a finite sup-norm cube. -/
def z4FourthCubeMass (R : ℕ) (k : Z4) : ℝ :=
  if k ∈ z4Cube R then
    l2LatticeRadialWeight 4 k
  else 0

theorem summable_z4FourthCubeMass (R : ℕ) :
    Summable (z4FourthCubeMass R) := by
  apply summable_of_ne_finset_zero (s := z4Cube R)
  intro k hk
  simp [z4FourthCubeMass, hk]

theorem tsum_z4FourthCubeMass (R : ℕ) :
    (∑' k : Z4, z4FourthCubeMass R k) =
      ∑ k ∈ z4Cube R, l2LatticeRadialWeight 4 k := by
  have hout :
      ∀ k ∉ z4Cube R, z4FourthCubeMass R k = 0 := by
    intro k hk
    simp [z4FourthCubeMass, hk]
  calc
    (∑' k : Z4, z4FourthCubeMass R k) =
        ∑ k ∈ z4Cube R, z4FourthCubeMass R k :=
      (hasSum_sum_of_ne_finset_zero hout).tsum_eq
    _ = ∑ k ∈ z4Cube R,
        l2LatticeRadialWeight 4 k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [z4FourthCubeMass, hk]

/-- Integral sup radius obeys the triangle inequality under the convolution
decomposition `γ = α + (γ - α)`. -/
theorem z4SupRadius_triangle (α γ : Z4) :
    z4SupRadius γ ≤
      z4SupRadius α + z4SupRadius (γ - α) := by
  have hcast :
      (fun i : Fin dim => (γ i : ℝ)) =
        (fun i : Fin dim => (α i : ℝ)) +
          fun i : Fin dim => ((γ - α) i : ℝ) := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Int.cast_sub]
    ring
  have hreal :
      z4FrequencyNorm γ ≤
        z4FrequencyNorm α +
          z4FrequencyNorm (γ - α) := by
    unfold z4FrequencyNorm
    rw [hcast]
    exact norm_add_le _ _
  rw [← z4SupRadius_eq_z4FrequencyNorm,
    ← z4SupRadius_eq_z4FrequencyNorm,
    ← z4SupRadius_eq_z4FrequencyNorm] at hreal
  exact_mod_cast hreal

theorem inv_pow_four_le_sixteen_inv_pow_four
    {B G : ℝ} (hB : 0 < B) (hG : 0 < G)
    (hGB : G ≤ 2 * B) :
    (B ^ 4)⁻¹ ≤ 16 * (G ^ 4)⁻¹ := by
  have hpow :
      G ^ 4 ≤ (2 * B) ^ 4 :=
    pow_le_pow_left₀ hG.le hGB 4
  field_simp [hB.ne', hG.ne']
  nlinarith

theorem inv_pow_four_mul_le_inv_pow_eight
    {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    (A ^ 4)⁻¹ * (B ^ 4)⁻¹ ≤
      (A ^ 8)⁻¹ := by
  have hB : 0 < B := hA.trans_le hAB
  have hpow : A ^ 4 ≤ B ^ 4 :=
    pow_le_pow_left₀ hA.le hAB 4
  calc
    (A ^ 4)⁻¹ * (B ^ 4)⁻¹ ≤
        (A ^ 4)⁻¹ * (A ^ 4)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (inv_anti₀ (pow_pos hA 4) hpow)
        (inv_nonneg.mpr (pow_nonneg hA.le 4))
    _ = (A ^ 8)⁻¹ := by field_simp [hA.ne', hB.ne']

theorem l2LatticeRadialWeight_four_near_le
    (α γ : Z4)
    (hnear : 2 * z4SupRadius α ≤ z4SupRadius γ) :
    l2LatticeRadialWeight 4 (γ - α) ≤
      16 * l2LatticeRadialWeight 4 γ := by
  let B : ℝ := 1 + (z4SupRadius (γ - α) : ℝ)
  let G : ℝ := 1 + (z4SupRadius γ : ℝ)
  have htri := z4SupRadius_triangle α γ
  have hGBnat :
      z4SupRadius γ + 1 ≤
        2 * (z4SupRadius (γ - α) + 1) := by
    omega
  have hGB : G ≤ 2 * B := by
    have hGB' :
        (z4SupRadius γ : ℝ) + 1 ≤
          2 * ((z4SupRadius (γ - α) : ℝ) + 1) := by
      exact_mod_cast hGBnat
    dsimp only [G, B]
    linarith
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hG : 0 < G := by
    dsimp only [G]
    positivity
  rw [l2LatticeRadialWeight_eq_z4SupRadius,
    l2LatticeRadialWeight_eq_z4SupRadius]
  exact inv_pow_four_le_sixteen_inv_pow_four hB hG hGB

theorem l2LatticeRadialWeight_four_mul_le_eight_of_radius_le
    (k l : Z4) (hkl : z4SupRadius k ≤ z4SupRadius l) :
    l2LatticeRadialWeight 4 k *
        l2LatticeRadialWeight 4 l ≤
      l2LatticeRadialWeight 8 k := by
  let A : ℝ := 1 + (z4SupRadius k : ℝ)
  let B : ℝ := 1 + (z4SupRadius l : ℝ)
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hAB : A ≤ B := by
    have hAB' :
        (z4SupRadius k : ℝ) ≤
          (z4SupRadius l : ℝ) := by
      exact_mod_cast hkl
    dsimp only [A, B]
    linarith
  rw [l2LatticeRadialWeight_eq_z4SupRadius,
    l2LatticeRadialWeight_eq_z4SupRadius,
    l2LatticeRadialWeight_eq_z4SupRadius]
  exact inv_pow_four_mul_le_inv_pow_eight hA hAB

theorem z4FourthCubeMass_nonneg (R : ℕ) (k : Z4) :
    0 ≤ z4FourthCubeMass R k := by
  unfold z4FourthCubeMass
  split_ifs
  · unfold l2LatticeRadialWeight
    positivity
  · exact le_rfl

theorem z4EighthRadialTail_nonneg (N : ℕ) (k : Z4) :
    0 ≤ z4EighthRadialTail N k := by
  unfold z4EighthRadialTail
  split_ifs
  · unfold l2LatticeRadialWeight
    positivity
  · exact le_rfl

/-- A single summable majorant simultaneously covering the two endpoint
regions and the residual region of the critical convolution. -/
def criticalRadialConvolutionMajor (γ α : Z4) : ℝ :=
  let R := z4SupRadius γ
  let N := R / 2 + 1
  16 * l2LatticeRadialWeight 4 γ *
      z4FourthCubeMass R α +
    16 * l2LatticeRadialWeight 4 γ *
      z4FourthCubeMass R (γ - α) +
    z4EighthRadialTail N α +
    z4EighthRadialTail N (γ - α)

theorem summable_criticalRadialConvolutionMajor (γ : Z4) :
    Summable (criticalRadialConvolutionMajor γ) := by
  let R := z4SupRadius γ
  let N := R / 2 + 1
  have hcube :
      Summable (z4FourthCubeMass R) :=
    summable_z4FourthCubeMass R
  have hcubeShift :
      Summable fun α : Z4 =>
        z4FourthCubeMass R (γ - α) :=
    hcube.comp_injective (Equiv.subLeft γ).injective
  have htail :
      Summable (z4EighthRadialTail N) :=
    summable_z4EighthRadialTail N
  have htailShift :
      Summable fun α : Z4 =>
        z4EighthRadialTail N (γ - α) :=
    htail.comp_injective (Equiv.subLeft γ).injective
  unfold criticalRadialConvolutionMajor
  exact
    (((hcube.mul_left
        (16 * l2LatticeRadialWeight 4 γ)).add
      (hcubeShift.mul_left
        (16 * l2LatticeRadialWeight 4 γ))).add
      htail).add htailShift

theorem l2LatticeRadialConvolution_term_le_criticalMajor
    (γ α : Z4) :
    l2LatticeRadialWeight 4 α *
        l2LatticeRadialWeight 4 (γ - α) ≤
      criticalRadialConvolutionMajor γ α := by
  let R := z4SupRadius γ
  let A := z4SupRadius α
  let B := z4SupRadius (γ - α)
  let N := R / 2 + 1
  have hcubeA :
      0 ≤ z4FourthCubeMass R α :=
    z4FourthCubeMass_nonneg R α
  have hcubeB :
      0 ≤ z4FourthCubeMass R (γ - α) :=
    z4FourthCubeMass_nonneg R (γ - α)
  have htailA :
      0 ≤ z4EighthRadialTail N α :=
    z4EighthRadialTail_nonneg N α
  have htailB :
      0 ≤ z4EighthRadialTail N (γ - α) :=
    z4EighthRadialTail_nonneg N (γ - α)
  have hweightγ :
      0 ≤ l2LatticeRadialWeight 4 γ := by
    unfold l2LatticeRadialWeight
    positivity
  have hnearTermA :
      0 ≤ 16 * l2LatticeRadialWeight 4 γ *
        z4FourthCubeMass R α :=
    mul_nonneg (mul_nonneg (by norm_num) hweightγ) hcubeA
  have hnearTermB :
      0 ≤ 16 * l2LatticeRadialWeight 4 γ *
        z4FourthCubeMass R (γ - α) :=
    mul_nonneg (mul_nonneg (by norm_num) hweightγ) hcubeB
  change
    l2LatticeRadialWeight 4 α *
        l2LatticeRadialWeight 4 (γ - α) ≤
      16 * l2LatticeRadialWeight 4 γ *
          z4FourthCubeMass R α +
        16 * l2LatticeRadialWeight 4 γ *
          z4FourthCubeMass R (γ - α) +
        z4EighthRadialTail N α +
        z4EighthRadialTail N (γ - α)
  by_cases hnearA : 2 * A ≤ R
  · have hmemA : α ∈ z4Cube R := by
      rw [mem_z4Cube_iff_z4SupRadius_le]
      dsimp only [A, R] at hnearA ⊢
      omega
    have hnear :=
      l2LatticeRadialWeight_four_near_le α γ
        (by simpa only [A, R] using hnearA)
    have hαnonneg :
        0 ≤ l2LatticeRadialWeight 4 α := by
      unfold l2LatticeRadialWeight
      positivity
    have hproduct :
        l2LatticeRadialWeight 4 α *
            l2LatticeRadialWeight 4 (γ - α) ≤
          16 * l2LatticeRadialWeight 4 γ *
            l2LatticeRadialWeight 4 α := by
      have := mul_le_mul_of_nonneg_left hnear hαnonneg
      nlinarith
    have hcubeAEq :
        z4FourthCubeMass R α =
          l2LatticeRadialWeight 4 α := by
      simp [z4FourthCubeMass, hmemA]
    rw [hcubeAEq]
    nlinarith [hproduct, hnearTermB, htailA, htailB]
  · by_cases hnearB : 2 * B ≤ R
    · have hmemB : γ - α ∈ z4Cube R := by
        rw [mem_z4Cube_iff_z4SupRadius_le]
        dsimp only [B, R] at hnearB ⊢
        omega
      have hnear :=
        l2LatticeRadialWeight_four_near_le
          (γ - α) γ
          (by simpa only [B, R] using hnearB)
      simp only [sub_sub_cancel] at hnear
      have hBnonneg :
          0 ≤ l2LatticeRadialWeight 4 (γ - α) := by
        unfold l2LatticeRadialWeight
        positivity
      have hproduct :
          l2LatticeRadialWeight 4 α *
              l2LatticeRadialWeight 4 (γ - α) ≤
            16 * l2LatticeRadialWeight 4 γ *
              l2LatticeRadialWeight 4 (γ - α) := by
        exact mul_le_mul_of_nonneg_right hnear hBnonneg
      have hcubeBEq :
          z4FourthCubeMass R (γ - α) =
            l2LatticeRadialWeight 4 (γ - α) := by
        simp [z4FourthCubeMass, hmemB]
      rw [hcubeBEq]
      nlinarith [hproduct, hnearTermA, htailA, htailB]
    · have hfarA : R < 2 * A := by omega
      have hfarB : R < 2 * B := by omega
      have hNA : N ≤ A := by
        dsimp only [N]
        omega
      have hNB : N ≤ B := by
        dsimp only [N]
        omega
      have htailAEq :
          z4EighthRadialTail N α =
            l2LatticeRadialWeight 8 α := by
        unfold z4EighthRadialTail
        rw [if_pos]
        simpa only [A] using hNA
      have htailBEq :
          z4EighthRadialTail N (γ - α) =
            l2LatticeRadialWeight 8 (γ - α) := by
        unfold z4EighthRadialTail
        rw [if_pos]
        simpa only [B] using hNB
      rw [htailAEq, htailBEq]
      rcases le_total A B with hAB | hBA
      · have hproduct :=
          l2LatticeRadialWeight_four_mul_le_eight_of_radius_le
            α (γ - α)
            (by simpa only [A, B] using hAB)
        nlinarith [hproduct, hnearTermA, hnearTermB]
      · have hproduct :=
          l2LatticeRadialWeight_four_mul_le_eight_of_radius_le
            (γ - α) α
            (by simpa only [A, B] using hBA)
        nlinarith [hproduct, hnearTermA, hnearTermB]

/-- The sup-radius form of the critical weight. -/
def z4SupCriticalWeight (γ : Z4) : ℝ :=
  l2LatticeRadialWeight 4 γ *
    (1 + Real.log ((z4SupRadius γ + 1 : ℕ) : ℝ))

theorem z4SupCriticalWeight_nonneg (γ : Z4) :
    0 ≤ z4SupCriticalWeight γ := by
  have hlog :
      0 ≤ Real.log ((z4SupRadius γ + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast
        Nat.succ_le_succ (Nat.zero_le (z4SupRadius γ)))
  unfold z4SupCriticalWeight l2LatticeRadialWeight
  positivity

theorem tsum_criticalRadialConvolutionMajor_le
    (γ : Z4) :
    (∑' α : Z4, criticalRadialConvolutionMajor γ α) ≤
      3200 * z4SupCriticalWeight γ := by
  let R := z4SupRadius γ
  let N := R / 2 + 1
  let c : ℝ := 16 * l2LatticeRadialWeight 4 γ
  let f₁ : Z4 → ℝ := fun α => c * z4FourthCubeMass R α
  let f₂ : Z4 → ℝ := fun α => c * z4FourthCubeMass R (γ - α)
  let f₃ : Z4 → ℝ := z4EighthRadialTail N
  let f₄ : Z4 → ℝ := fun α => z4EighthRadialTail N (γ - α)
  have h₁ : Summable f₁ :=
    (summable_z4FourthCubeMass R).mul_left c
  have h₂ : Summable f₂ :=
    ((summable_z4FourthCubeMass R).comp_injective
      (Equiv.subLeft γ).injective).mul_left c
  have h₃ : Summable f₃ :=
    summable_z4EighthRadialTail N
  have h₄ : Summable f₄ :=
    h₃.comp_injective (Equiv.subLeft γ).injective
  have hcubeShift :
      (∑' α : Z4, z4FourthCubeMass R (γ - α)) =
        ∑' α : Z4, z4FourthCubeMass R α := by
    rw [← (Equiv.subLeft γ).tsum_eq]
    simp only [Equiv.subLeft_apply, sub_sub_cancel]
  have htailShift :
      (∑' α : Z4, z4EighthRadialTail N (γ - α)) =
        ∑' α : Z4, z4EighthRadialTail N α := by
    rw [← (Equiv.subLeft γ).tsum_eq]
    simp only [Equiv.subLeft_apply, sub_sub_cancel]
  have hnear :
      (∑' α : Z4, f₁ α) ≤
        1280 * z4SupCriticalWeight γ := by
    rw [show (∑' α : Z4, f₁ α) =
      c * ∑' α : Z4, z4FourthCubeMass R α by
        rw [tsum_mul_left]]
    rw [tsum_z4FourthCubeMass]
    have hball :=
      sum_z4Cube_l2LatticeRadialWeight_four_le_log R
    have hc : 0 ≤ c := by
      dsimp only [c]
      unfold l2LatticeRadialWeight
      positivity
    have hm := mul_le_mul_of_nonneg_left hball hc
    dsimp only [c]
    unfold z4SupCriticalWeight
    dsimp only [R] at hball ⊢
    push_cast at hm ⊢
    nlinarith [hm]
  have hnearShift :
      (∑' α : Z4, f₂ α) ≤
        1280 * z4SupCriticalWeight γ := by
    rw [show (∑' α : Z4, f₂ α) =
      c * ∑' α : Z4,
        z4FourthCubeMass R (γ - α) by
          rw [tsum_mul_left]]
    rw [hcubeShift]
    rw [← tsum_mul_left]
    simpa only [f₁] using hnear
  have hN : 0 < N := by
    dsimp only [N]
    omega
  have hRN : R + 1 ≤ 2 * N := by
    dsimp only [N]
    omega
  have htailScalar :
      (((N : ℝ)⁻¹) ^ 4) ≤
        16 * ((((R + 1 : ℕ) : ℝ) ^ 4)⁻¹) := by
    have hRNreal :
        ((R + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      exact_mod_cast hRN
    have h :=
      inv_pow_four_le_sixteen_inv_pow_four
        (B := (N : ℝ))
        (G := ((R + 1 : ℕ) : ℝ))
        (by positivity) (by positivity) hRNreal
    simpa only [inv_pow] using h
  have htail :
      (∑' α : Z4, f₃ α) ≤
        320 * l2LatticeRadialWeight 4 γ := by
    calc
      (∑' α : Z4, f₃ α) ≤
          20 * (((N : ℝ)⁻¹) ^ 4) :=
        tsum_z4EighthRadialTail_le N hN
      _ ≤ 20 * (16 *
          ((((R + 1 : ℕ) : ℝ) ^ 4)⁻¹)) :=
        mul_le_mul_of_nonneg_left htailScalar (by norm_num)
      _ = 320 * l2LatticeRadialWeight 4 γ := by
        rw [l2LatticeRadialWeight_eq_z4SupRadius]
        dsimp only [R]
        push_cast
        ring
  have htailLog :
      (∑' α : Z4, f₃ α) ≤
        320 * z4SupCriticalWeight γ := by
    refine htail.trans ?_
    have hlog :
        0 ≤ Real.log ((z4SupRadius γ + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by
        exact_mod_cast
          Nat.succ_le_succ (Nat.zero_le (z4SupRadius γ)))
    unfold z4SupCriticalWeight
    have hw :
        0 ≤ l2LatticeRadialWeight 4 γ := by
      unfold l2LatticeRadialWeight
      positivity
    nlinarith
  have htailShiftLog :
      (∑' α : Z4, f₄ α) ≤
        320 * z4SupCriticalWeight γ := by
    rw [show (∑' α : Z4, f₄ α) =
      ∑' α : Z4, f₃ α by
        exact htailShift]
    exact htailLog
  have hsum :
      (∑' α : Z4, criticalRadialConvolutionMajor γ α) =
        (∑' α : Z4, f₁ α) +
          (∑' α : Z4, f₂ α) +
          (∑' α : Z4, f₃ α) +
          (∑' α : Z4, f₄ α) := by
    change tsum (fun x : Z4 =>
      ((f₁ x + f₂ x) + f₃ x) + f₄ x) = _
    rw [((h₁.add h₂).add h₃).tsum_add h₄,
      (h₁.add h₂).tsum_add h₃,
      h₁.tsum_add h₂]
  rw [hsum]
  nlinarith

theorem tsum_l2LatticeRadialConvolution_le_critical
    (γ : Z4) :
    (∑' α : Z4,
        l2LatticeRadialWeight 4 α *
          l2LatticeRadialWeight 4 (γ - α)) ≤
      3200 * z4SupCriticalWeight γ := by
  exact
    (summable_l2Lattice_convolution γ).tsum_le_tsum
      (l2LatticeRadialConvolution_term_le_criticalMajor γ)
      (summable_criticalRadialConvolutionMajor γ)
    |>.trans (tsum_criticalRadialConvolutionMajor_le γ)

theorem z4FrequencyNorm_le_norm_z4EuclideanFrequency
    (k : Z4) :
    z4FrequencyNorm k ≤ ‖z4EuclideanFrequency k‖ := by
  unfold z4FrequencyNorm
  rw [pi_norm_le_iff_of_nonneg
    (norm_nonneg (z4EuclideanFrequency k))]
  intro i
  simpa only [Real.norm_eq_abs, z4EuclideanFrequency,
    Int.norm_cast_real] using
      PiLp.norm_apply_le (z4EuclideanFrequency k) i

theorem designJapaneseBracket_sq (k : Z4) :
    designJapaneseBracket k ^ 2 =
      1 + ‖z4EuclideanFrequency k‖ ^ 2 := by
  unfold designJapaneseBracket
  rw [Real.sq_sqrt (by positivity),
    norm_sq_z4EuclideanFrequency]
  rfl

theorem norm_z4EuclideanFrequency_le_designJapaneseBracket
    (k : Z4) :
    ‖z4EuclideanFrequency k‖ ≤
      designJapaneseBracket k := by
  have hJ : 0 ≤ designJapaneseBracket k := by
    unfold designJapaneseBracket
    positivity
  have hu := norm_nonneg (z4EuclideanFrequency k)
  have hsq := designJapaneseBracket_sq k
  nlinarith

theorem designJapaneseBracket_le_two_mul_supBracket
    (k : Z4) :
    designJapaneseBracket k ≤
      2 * (((z4SupRadius k + 1 : ℕ) : ℝ)) := by
  have hJ := Real.sqrt_nonneg
    (1 + ∑ i, (k i : ℝ) ^ 2)
  have hu := norm_nonneg (z4EuclideanFrequency k)
  have hsq := designJapaneseBracket_sq k
  have hJu :
      designJapaneseBracket k ≤
        1 + ‖z4EuclideanFrequency k‖ := by
    nlinarith
  have huR :=
    norm_z4EuclideanFrequency_le_two_mul_frequencyNorm k
  have hR :=
    z4SupRadius_eq_z4FrequencyNorm k
  push_cast
  nlinarith

theorem supBracket_le_two_mul_designJapaneseBracket
    (k : Z4) :
    (((z4SupRadius k + 1 : ℕ) : ℝ)) ≤
      2 * designJapaneseBracket k := by
  have hRu :=
    z4FrequencyNorm_le_norm_z4EuclideanFrequency k
  have huJ :=
    norm_z4EuclideanFrequency_le_designJapaneseBracket k
  have hJ := one_le_designJapaneseBracket k
  have hR :=
    z4SupRadius_eq_z4FrequencyNorm k
  push_cast
  nlinarith

theorem z4SupCriticalWeight_le_designCriticalHSWeight
    (γ : Z4) :
    z4SupCriticalWeight γ ≤
      32 * designCriticalHSWeight γ := by
  let S : ℝ := ((z4SupRadius γ + 1 : ℕ) : ℝ)
  let J : ℝ := designJapaneseBracket γ
  have hS : 0 < S := by
    dsimp only [S]
    positivity
  have hJ : 0 < J :=
    (one_le_designJapaneseBracket γ).trans_lt'
      zero_lt_one
  have hJS : J ≤ 2 * S := by
    simpa only [J, S] using
      designJapaneseBracket_le_two_mul_supBracket γ
  have hSJ : S ≤ 2 * J := by
    simpa only [J, S] using
      supBracket_le_two_mul_designJapaneseBracket γ
  have hinv :
      (S ^ 4)⁻¹ ≤ 16 * (J ^ 4)⁻¹ :=
    inv_pow_four_le_sixteen_inv_pow_four hS hJ hJS
  have hlogS :
      Real.log S ≤ Real.log (2 * J) :=
    Real.log_le_log hS hSJ
  have hlogTwo :
      Real.log 2 ≤ 1 := by
    have h :=
      Real.log_le_sub_one_of_pos
        (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogJ : 0 ≤ Real.log J :=
    Real.log_nonneg
      (by simpa only [J] using one_le_designJapaneseBracket γ)
  have hlogMul :
      Real.log (2 * J) =
        Real.log 2 + Real.log J :=
    Real.log_mul (by norm_num) hJ.ne'
  have hlog :
      1 + Real.log S ≤
        2 * (1 + Real.log J) := by
    rw [hlogMul] at hlogS
    linarith
  have hSlog : 0 ≤ 1 + Real.log S := by
    have : 1 ≤ S := by
      dsimp only [S]
      exact_mod_cast
        Nat.succ_le_succ (Nat.zero_le (z4SupRadius γ))
    linarith [Real.log_nonneg this]
  have hJlog : 0 ≤ 1 + Real.log J := by linarith
  unfold z4SupCriticalWeight designCriticalHSWeight
  rw [l2LatticeRadialWeight_eq_z4SupRadius]
  have hSone :
      1 + (z4SupRadius γ : ℝ) = S := by
    dsimp only [S]
    push_cast
    ring
  have hScast :
      (((z4SupRadius γ + 1 : ℕ) : ℝ)) = S := by
    rfl
  have hJdef :
      designJapaneseBracket γ = J := by
    rfl
  rw [hSone, hScast, hJdef]
  change (S ^ 4)⁻¹ * (1 + Real.log S) ≤
    32 * ((J ^ 4)⁻¹ * (1 + Real.log J))
  calc
    (S ^ 4)⁻¹ * (1 + Real.log S) ≤
        (16 * (J ^ 4)⁻¹) *
          (2 * (1 + Real.log J)) :=
      mul_le_mul hinv hlog hSlog
        (mul_nonneg (by norm_num) (inv_nonneg.mpr
          (pow_nonneg hJ.le 4)))
    _ = 32 * ((J ^ 4)⁻¹ *
        (1 + Real.log J)) := by ring

theorem tsum_greenL2SquaredConvolutionSummand_le_critical
    (γ : Z4) :
    (∑' α : Z4,
        greenL2SquaredConvolutionSummand γ α) ≤
      1638400 * designCriticalHSWeight γ := by
  have hmajor :
      Summable fun α : Z4 =>
        16 *
          (l2LatticeRadialWeight 4 α *
            l2LatticeRadialWeight 4 (γ - α)) :=
    (summable_l2Lattice_convolution γ).mul_left 16
  calc
    (∑' α : Z4,
        greenL2SquaredConvolutionSummand γ α) ≤
        ∑' α : Z4,
          16 *
            (l2LatticeRadialWeight 4 α *
              l2LatticeRadialWeight 4 (γ - α)) :=
      (summable_greenL2SquaredConvolutionSummand γ).tsum_le_tsum
        (greenL2SquaredConvolutionSummand_le γ) hmajor
    _ = 16 * ∑' α : Z4,
        (l2LatticeRadialWeight 4 α *
          l2LatticeRadialWeight 4 (γ - α)) := by
      rw [tsum_mul_left]
    _ ≤ 16 * (3200 * z4SupCriticalWeight γ) :=
      mul_le_mul_of_nonneg_left
        (tsum_l2LatticeRadialConvolution_le_critical γ)
        (by norm_num)
    _ ≤ 16 * (3200 *
        (32 * designCriticalHSWeight γ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (z4SupCriticalWeight_le_designCriticalHSWeight γ)
          (by norm_num))
        (by norm_num)
    _ = 1638400 * designCriticalHSWeight γ := by ring

/-- The scalar critical estimate required by the conditioned
Hilbert--Schmidt theorem is unconditional. -/
theorem exists_positive_criticalGreenSquaredConvolutionEstimate :
    ∃ C : ℝ, 0 < C ∧
      CriticalGreenSquaredConvolutionEstimate C := by
  refine ⟨1638400, by norm_num, ?_⟩
  constructor
  · norm_num
  · intro γ
    exact tsum_greenL2SquaredConvolutionSummand_le_critical γ

end

end Anderson4D
