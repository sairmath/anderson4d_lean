import Anderson4D.Parametrix.L2Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# The lattice summation behind the `L²` parametrix bound

This file proves the deterministic summation step (3.31) following the
weighted Fourier operator estimate (3.30).  The endpoint factors are
convolved after the shear

`(α, β) ↦ (γ, α) = (α + β, α)`,

and the remaining central frequency sum costs exactly `ε⁻⁴` in four
dimensions.  Combined with the `ε⁻⁸` in (3.24) and the `ε⁻⁸` weight in
(3.30), this preserves the paper's `ε⁻²⁰` power.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

def l2LatticeCoordWeight (m : ℤ) : ℝ :=
  ((Int.natAbs m : ℝ) + 1) ^ (-(5 / 4 : ℝ))

theorem summable_l2LatticeCoordWeight :
    Summable l2LatticeCoordWeight := by
  have hnat :
      Summable fun n : ℕ =>
        l2LatticeCoordWeight (n : ℤ) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (5 / 4)).mpr
        (by norm_num : (1 : ℝ) < 5 / 4)
    apply h.congr
    intro n
    unfold l2LatticeCoordWeight
    simp only [Int.natAbs_natCast]
    rw [abs_of_nonneg (by positivity)]
    rw [one_div, Real.rpow_neg (by positivity)]
  have hneg :
      Summable fun n : ℕ =>
        l2LatticeCoordWeight (Int.negSucc n) := by
    apply hnat.comp_injective Nat.succ_injective |>.congr
    intro n
    unfold l2LatticeCoordWeight
    simp only [Function.comp_apply, Int.natAbs_negSucc,
      Int.natAbs_natCast]
  exact Summable.of_nat_of_neg_add_one hnat hneg

private theorem summable_pi_l2LatticeProduct
    {g : ℤ → ℝ}
    (h0 : ∀ m, 0 ≤ g m) (hg : Summable g) :
    ∀ n : ℕ,
      Summable fun k : Fin n → ℤ => ∏ i, g (k i) := by
  intro n
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    have hg0 : (0 : ℤ → ℝ) ≤ g := fun m => h0 m
    have hp0 :
        (0 : (Fin n → ℤ) → ℝ) ≤
          fun k => ∏ i, g (k i) :=
      fun k => Finset.prod_nonneg fun i _ => h0 _
    have hstep :
        Summable fun p : ℤ × (Fin n → ℤ) =>
          g p.1 * ∏ i, g (p.2 i) :=
      @Summable.mul_of_nonneg ℤ (Fin n → ℤ) g
        (fun k => ∏ i, g (k i))
        hg ih hg0 hp0
    rw [← (Fin.consEquiv
      fun _ : Fin (n + 1) => ℤ).summable_iff]
    apply hstep.congr
    intro p
    simp [Fin.consEquiv, Fin.prod_univ_succ]

def l2LatticeProductWeight (k : Z4) : ℝ :=
  ∏ i, l2LatticeCoordWeight (k i)

theorem summable_l2LatticeProductWeight :
    Summable l2LatticeProductWeight := by
  exact summable_pi_l2LatticeProduct
    (fun m => Real.rpow_nonneg (by positivity) _)
    summable_l2LatticeCoordWeight dim

def l2LatticeRadialWeightRpow (k : Z4) : ℝ :=
  (1 + z4FrequencyNorm k) ^ (-(5 : ℝ))

theorem l2LatticeRadialWeightRpow_le_product (k : Z4) :
    l2LatticeRadialWeightRpow k ≤ l2LatticeProductWeight k := by
  let R : ℝ := 1 + z4FrequencyNorm k
  let a : Fin dim → ℝ :=
    fun i => (Int.natAbs (k i) : ℝ) + 1
  have hR : 0 < R := by
    dsimp [R, z4FrequencyNorm]
    nlinarith [norm_nonneg
      (fun i : Fin dim => (k i : ℝ))]
  have ha (i : Fin dim) : 0 < a i := by
    dsimp [a]
    positivity
  have hcoord (i : Fin dim) :
      a i ≤ R := by
    dsimp [a, R]
    have hi :
        ((Int.natAbs (k i) : ℕ) : ℝ) ≤
          z4FrequencyNorm k := by
      unfold z4FrequencyNorm
      simpa only [Nat.cast_natAbs, Int.cast_abs,
        Real.norm_eq_abs] using
        norm_le_pi_norm
          (fun j : Fin dim => (k j : ℝ)) i
    simpa only [add_comm] using add_le_add_right hi 1
  have hprod :
      (∏ i, a i) ≤ R ^ dim := by
    calc
      (∏ i, a i) ≤ ∏ _i : Fin dim, R := by
        apply Finset.prod_le_prod
        · intro i _
          exact (ha i).le
        · intro i _
          exact hcoord i
      _ = R ^ dim := by
        simp
  have hprodpos : 0 < ∏ i, a i :=
    Finset.prod_pos fun i _ => ha i
  have hanti :
      (R ^ dim) ^ (-(5 / 4 : ℝ)) ≤
        (∏ i, a i) ^ (-(5 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos
      hprodpos hprod (by norm_num)
  have hleft :
      (R ^ dim) ^ (-(5 / 4 : ℝ)) =
        R ^ (-(5 : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hR.le]
    norm_num [dim]
  have hright :
      (∏ i, a i) ^ (-(5 / 4 : ℝ)) =
        ∏ i, a i ^ (-(5 / 4 : ℝ)) := by
    symm
    exact Real.finsetProd_rpow
      Finset.univ a (fun i _ => (ha i).le) _
  unfold l2LatticeRadialWeightRpow l2LatticeProductWeight l2LatticeCoordWeight
  change R ^ (-(5 : ℝ)) ≤
    ∏ i, a i ^ (-(5 / 4 : ℝ))
  rw [← hleft, ← hright]
  exact hanti

theorem summable_l2LatticeRadialWeightRpow :
    Summable l2LatticeRadialWeightRpow := by
  exact summable_l2LatticeProductWeight.of_nonneg_of_le
    (fun k => Real.rpow_nonneg
      (by
        dsimp [z4FrequencyNorm]
        nlinarith [norm_nonneg
          (fun i : Fin dim => (k i : ℝ))])
      _)
    l2LatticeRadialWeightRpow_le_product

def l2LatticeRadialWeight (n : ℕ) (k : Z4) : ℝ :=
  ((1 + z4FrequencyNorm k) ^ n)⁻¹

theorem l2LatticeRadialWeightRpow_eq_five (k : Z4) :
    l2LatticeRadialWeightRpow k = l2LatticeRadialWeight 5 k := by
  unfold l2LatticeRadialWeightRpow l2LatticeRadialWeight
  rw [Real.rpow_neg
    (by
      dsimp [z4FrequencyNorm]
      positivity)]
  exact congrArg (fun x : ℝ => x⁻¹)
    (Real.rpow_natCast
      (1 + z4FrequencyNorm k) 5)

theorem summable_l2LatticeRadialWeight_five :
    Summable (l2LatticeRadialWeight 5) :=
  summable_l2LatticeRadialWeightRpow.congr
    l2LatticeRadialWeightRpow_eq_five

theorem l2Lattice_scalar_convolution_bound
    {A B G : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hG : 0 < G)
    (hGA : G ≤ 2 * A) :
    (A ^ 4)⁻¹ * (B ^ 4)⁻¹ ≤
      8 * (G ^ 3)⁻¹ *
        ((A ^ 5)⁻¹ + (B ^ 5)⁻¹) := by
  have hGpow :
      G ^ 3 ≤ 8 * A ^ 3 := by
    calc
      G ^ 3 ≤ (2 * A) ^ 3 :=
        pow_le_pow_left₀ hG.le hGA 3
      _ = 8 * A ^ 3 := by ring
  have hAB :
      A ^ 4 * B ≤ A ^ 5 + B ^ 5 := by
    rcases le_total A B with h | h
    · calc
        A ^ 4 * B ≤ B ^ 4 * B := by
          gcongr
        _ = B ^ 5 := by ring
        _ ≤ A ^ 5 + B ^ 5 :=
          le_add_of_nonneg_left (pow_nonneg hA.le 5)
    · calc
        A ^ 4 * B ≤ A ^ 4 * A := by
          gcongr
        _ = A ^ 5 := by ring
        _ ≤ A ^ 5 + B ^ 5 :=
          le_add_of_nonneg_right (pow_nonneg hB.le 5)
  field_simp [hA.ne', hB.ne', hG.ne']
  nlinarith [mul_le_mul_of_nonneg_right
    hGpow (mul_nonneg hA.le hB.le)]

theorem l2Lattice_bracket_triangle (α γ : Z4) :
    1 + z4FrequencyNorm γ ≤
      (1 + z4FrequencyNorm α) +
        (1 + z4FrequencyNorm (γ - α)) := by
  have hcast :
      (fun i : Fin dim => (γ i : ℝ)) =
        (fun i : Fin dim => (α i : ℝ)) +
          fun i : Fin dim => ((γ - α) i : ℝ) := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Int.cast_sub]
    ring
  have hnorm :
      z4FrequencyNorm γ ≤
        z4FrequencyNorm α +
          z4FrequencyNorm (γ - α) := by
    unfold z4FrequencyNorm
    rw [hcast]
    exact norm_add_le _ _
  linarith

theorem l2Lattice_convolution_term_bound (α γ : Z4) :
    l2LatticeRadialWeight 4 α *
        l2LatticeRadialWeight 4 (γ - α) ≤
      8 * l2LatticeRadialWeight 3 γ *
        (l2LatticeRadialWeight 5 α +
          l2LatticeRadialWeight 5 (γ - α)) := by
  let A : ℝ := 1 + z4FrequencyNorm α
  let B : ℝ := 1 + z4FrequencyNorm (γ - α)
  let G : ℝ := 1 + z4FrequencyNorm γ
  have hA : 0 < A := by
    dsimp [A, z4FrequencyNorm]
    positivity
  have hB : 0 < B := by
    dsimp [B, z4FrequencyNorm]
    positivity
  have hG : 0 < G := by
    dsimp [G, z4FrequencyNorm]
    positivity
  have htri : G ≤ A + B :=
    l2Lattice_bracket_triangle α γ
  have hlarge : G ≤ 2 * A ∨ G ≤ 2 * B := by
    rcases le_total A B with h | h
    · exact Or.inr (htri.trans (by linarith))
    · exact Or.inl (htri.trans (by linarith))
  unfold l2LatticeRadialWeight
  change (A ^ 4)⁻¹ * (B ^ 4)⁻¹ ≤
    8 * (G ^ 3)⁻¹ *
      ((A ^ 5)⁻¹ + (B ^ 5)⁻¹)
  rcases hlarge with hGA | hGB
  · exact l2Lattice_scalar_convolution_bound hA hB hG hGA
  · rw [mul_comm (A ^ 4)⁻¹,
      add_comm (A ^ 5)⁻¹]
    exact l2Lattice_scalar_convolution_bound hB hA hG hGB

theorem summable_l2Lattice_convolution (γ : Z4) :
    Summable fun α : Z4 =>
      l2LatticeRadialWeight 4 α *
        l2LatticeRadialWeight 4 (γ - α) := by
  have hshift :
      Summable fun α : Z4 =>
        l2LatticeRadialWeight 5 (γ - α) :=
    summable_l2LatticeRadialWeight_five.comp_injective
      (Equiv.subLeft γ).injective
  have hmajor :
      Summable fun α : Z4 =>
        8 * l2LatticeRadialWeight 3 γ *
          (l2LatticeRadialWeight 5 α +
            l2LatticeRadialWeight 5 (γ - α)) :=
    (summable_l2LatticeRadialWeight_five.add hshift).mul_left _
  exact hmajor.of_nonneg_of_le
    (fun α =>
      mul_nonneg
        (by unfold l2LatticeRadialWeight; positivity)
        (by unfold l2LatticeRadialWeight; positivity))
    (l2Lattice_convolution_term_bound · γ)

theorem tsum_l2Lattice_convolution_bound (γ : Z4) :
    (∑' α : Z4,
      l2LatticeRadialWeight 4 α *
        l2LatticeRadialWeight 4 (γ - α)) ≤
      16 * l2LatticeRadialWeight 3 γ *
        ∑' α : Z4, l2LatticeRadialWeight 5 α := by
  have hshift :
      Summable fun α : Z4 =>
        l2LatticeRadialWeight 5 (γ - α) :=
    summable_l2LatticeRadialWeight_five.comp_injective
      (Equiv.subLeft γ).injective
  have hmajor :
      Summable fun α : Z4 =>
        8 * l2LatticeRadialWeight 3 γ *
          (l2LatticeRadialWeight 5 α +
            l2LatticeRadialWeight 5 (γ - α)) :=
    (summable_l2LatticeRadialWeight_five.add hshift).mul_left _
  calc
    (∑' α : Z4,
        l2LatticeRadialWeight 4 α *
          l2LatticeRadialWeight 4 (γ - α)) ≤
        ∑' α : Z4,
          8 * l2LatticeRadialWeight 3 γ *
            (l2LatticeRadialWeight 5 α +
              l2LatticeRadialWeight 5 (γ - α)) :=
      (summable_l2Lattice_convolution γ).tsum_le_tsum
        (l2Lattice_convolution_term_bound · γ) hmajor
    _ = 8 * l2LatticeRadialWeight 3 γ *
        ((∑' α : Z4, l2LatticeRadialWeight 5 α) +
          ∑' α : Z4,
            l2LatticeRadialWeight 5 (γ - α)) := by
      rw [tsum_mul_left,
        summable_l2LatticeRadialWeight_five.tsum_add hshift]
    _ = 16 * l2LatticeRadialWeight 3 γ *
        ∑' α : Z4, l2LatticeRadialWeight 5 α := by
      have hshiftSum :
          (∑' α : Z4,
              l2LatticeRadialWeight 5 (γ - α)) =
            ∑' α : Z4,
              l2LatticeRadialWeight 5 α := by
        rw [← (Equiv.subLeft γ).tsum_eq]
        simp only [Equiv.subLeft_apply, sub_sub_cancel]
      rw [hshiftSum]
      ring

def l2LatticeCentralWeight (ε : ℝ) (k : Z4) : ℝ :=
  (1 + (ε ^ 2 * z4FrequencyNorm k) ^ 2)⁻¹

theorem l2LatticeCentralWeight_le
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (k : Z4) :
    l2LatticeCentralWeight ε k ≤
      2 * ε⁻¹ ^ (4 : ℕ) *
        l2LatticeRadialWeight 2 k := by
  let r : ℝ := z4FrequencyNorm k
  let R : ℝ := 1 + r
  let D : ℝ := 1 + (ε ^ 2 * r) ^ 2
  have hr : 0 ≤ r := by
    dsimp [r, z4FrequencyNorm]
    positivity
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hinv :
      1 ≤ ε⁻¹ ^ (4 : ℕ) :=
    one_le_pow₀ ((one_le_inv₀ hε).2 hεle)
  have hscale :
      R ^ 2 ≤
        2 * ε⁻¹ ^ (4 : ℕ) * D := by
    have hR2 :
        R ^ 2 ≤ 2 * (1 + r ^ 2) := by
      dsimp [R]
      nlinarith [sq_nonneg (r - 1)]
    have heq :
        ε⁻¹ ^ (4 : ℕ) * D =
          ε⁻¹ ^ (4 : ℕ) + r ^ 2 := by
      dsimp [D]
      field_simp [hε.ne']
    calc
      R ^ 2 ≤ 2 * (1 + r ^ 2) := hR2
      _ ≤ 2 * (ε⁻¹ ^ (4 : ℕ) + r ^ 2) := by
        gcongr
      _ = 2 * ε⁻¹ ^ (4 : ℕ) * D := by
        rw [← heq]
        ring
  unfold l2LatticeCentralWeight l2LatticeRadialWeight
  change D⁻¹ ≤
    2 * ε⁻¹ ^ (4 : ℕ) * (R ^ 2)⁻¹
  rw [le_mul_inv_iff₀ (pow_pos hR 2),
    inv_mul_eq_div, div_le_iff₀ hD]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hscale

theorem l2LatticeRadial_three_mul_central_bound
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (k : Z4) :
    l2LatticeRadialWeight 3 k *
        l2LatticeCentralWeight ε k ≤
      2 * ε⁻¹ ^ (4 : ℕ) *
        l2LatticeRadialWeight 5 k := by
  calc
    l2LatticeRadialWeight 3 k *
          l2LatticeCentralWeight ε k ≤
        l2LatticeRadialWeight 3 k *
          (2 * ε⁻¹ ^ (4 : ℕ) *
            l2LatticeRadialWeight 2 k) := by
      exact mul_le_mul_of_nonneg_left
        (l2LatticeCentralWeight_le hε hεle k)
        (by
          unfold l2LatticeRadialWeight
          exact inv_nonneg.mpr (pow_nonneg (by
            dsimp [z4FrequencyNorm]
            positivity) _))
    _ = 2 * ε⁻¹ ^ (4 : ℕ) *
        l2LatticeRadialWeight 5 k := by
      unfold l2LatticeRadialWeight
      have hR :
          0 < 1 + z4FrequencyNorm k := by
        dsimp [z4FrequencyNorm]
        positivity
      field_simp [hR.ne']

theorem summable_l2LatticeRadial_three_mul_central
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    Summable fun k : Z4 =>
      l2LatticeRadialWeight 3 k *
        l2LatticeCentralWeight ε k := by
  exact (summable_l2LatticeRadialWeight_five.mul_left
      (2 * ε⁻¹ ^ (4 : ℕ))).of_nonneg_of_le
    (fun k =>
      mul_nonneg
        (by
          unfold l2LatticeRadialWeight
          exact inv_nonneg.mpr (pow_nonneg (by
            dsimp [z4FrequencyNorm]
            positivity) _))
        (by unfold l2LatticeCentralWeight; positivity))
    (l2LatticeRadial_three_mul_central_bound hε hεle)

theorem tsum_l2LatticeRadial_three_mul_central_bound
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    (∑' k : Z4,
        l2LatticeRadialWeight 3 k *
          l2LatticeCentralWeight ε k) ≤
      2 * ε⁻¹ ^ (4 : ℕ) *
        ∑' k : Z4, l2LatticeRadialWeight 5 k := by
  calc
    (∑' k : Z4,
        l2LatticeRadialWeight 3 k *
          l2LatticeCentralWeight ε k) ≤
        ∑' k : Z4,
          2 * ε⁻¹ ^ (4 : ℕ) *
            l2LatticeRadialWeight 5 k :=
      (summable_l2LatticeRadial_three_mul_central
        hε hεle).tsum_le_tsum
        (l2LatticeRadial_three_mul_central_bound hε hεle)
        (summable_l2LatticeRadialWeight_five.mul_left _)
    _ = 2 * ε⁻¹ ^ (4 : ℕ) *
        ∑' k : Z4, l2LatticeRadialWeight 5 k := by
      rw [tsum_mul_left]

def l2LatticeGammaPairWeight (ε : ℝ) (p : Z4 × Z4) : ℝ :=
  l2LatticeCentralWeight ε p.1 *
    (l2LatticeRadialWeight 4 p.2 *
      l2LatticeRadialWeight 4 (p.1 - p.2))

theorem l2LatticeGammaPairWeight_nonneg
    (ε : ℝ) (p : Z4 × Z4) :
    0 ≤ l2LatticeGammaPairWeight ε p := by
  unfold l2LatticeGammaPairWeight l2LatticeCentralWeight
    l2LatticeRadialWeight
  positivity

theorem summable_l2LatticeGammaPairWeight_fiber
    (ε : ℝ) (γ : Z4) :
    Summable fun α : Z4 =>
      l2LatticeGammaPairWeight ε (γ, α) := by
  simpa only [l2LatticeGammaPairWeight] using
    (summable_l2Lattice_convolution γ).mul_left
      (l2LatticeCentralWeight ε γ)

theorem tsum_l2LatticeGammaPairWeight_fiber_bound
    {ε : ℝ} (γ : Z4) :
    (∑' α : Z4,
        l2LatticeGammaPairWeight ε (γ, α)) ≤
      16 *
        (∑' α : Z4, l2LatticeRadialWeight 5 α) *
        (l2LatticeRadialWeight 3 γ *
          l2LatticeCentralWeight ε γ) := by
  have hcentral :
      0 ≤ l2LatticeCentralWeight ε γ := by
    unfold l2LatticeCentralWeight
    positivity
  calc
    (∑' α : Z4,
        l2LatticeGammaPairWeight ε (γ, α)) =
        l2LatticeCentralWeight ε γ *
          ∑' α : Z4,
            (l2LatticeRadialWeight 4 α *
              l2LatticeRadialWeight 4 (γ - α)) := by
      simp only [l2LatticeGammaPairWeight]
      rw [tsum_mul_left]
    _ ≤ l2LatticeCentralWeight ε γ *
        (16 * l2LatticeRadialWeight 3 γ *
          ∑' α : Z4,
            l2LatticeRadialWeight 5 α) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_l2Lattice_convolution_bound γ) hcentral
    _ = 16 *
        (∑' α : Z4, l2LatticeRadialWeight 5 α) *
        (l2LatticeRadialWeight 3 γ *
          l2LatticeCentralWeight ε γ) := by
      ring

theorem summable_l2LatticeGammaPairWeight_outer
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    Summable fun γ : Z4 =>
      ∑' α : Z4, l2LatticeGammaPairWeight ε (γ, α) := by
  have hS :
      0 ≤ ∑' α : Z4, l2LatticeRadialWeight 5 α :=
    tsum_nonneg fun _ => by
      unfold l2LatticeRadialWeight
      exact inv_nonneg.mpr
        (pow_nonneg (by
          dsimp [z4FrequencyNorm]
          positivity) _)
  have hmajor :
      Summable fun γ : Z4 =>
        16 *
          (∑' α : Z4, l2LatticeRadialWeight 5 α) *
          (l2LatticeRadialWeight 3 γ *
            l2LatticeCentralWeight ε γ) :=
    (summable_l2LatticeRadial_three_mul_central
      hε hεle).mul_left _
  exact hmajor.of_nonneg_of_le
    (fun γ =>
      tsum_nonneg fun α =>
        l2LatticeGammaPairWeight_nonneg ε (γ, α))
    (tsum_l2LatticeGammaPairWeight_fiber_bound ·)

theorem summable_l2LatticeGammaPairWeight
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    Summable (l2LatticeGammaPairWeight ε) := by
  rw [summable_prod_of_nonneg
    (fun p => l2LatticeGammaPairWeight_nonneg ε p)]
  exact ⟨summable_l2LatticeGammaPairWeight_fiber ε,
    summable_l2LatticeGammaPairWeight_outer hε hεle⟩

theorem tsum_l2LatticeGammaPairWeight_bound
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    (∑' p : Z4 × Z4,
        l2LatticeGammaPairWeight ε p) ≤
      32 * ε⁻¹ ^ (4 : ℕ) *
        (∑' α : Z4,
          l2LatticeRadialWeight 5 α) ^ 2 := by
  let S : ℝ :=
    ∑' α : Z4, l2LatticeRadialWeight 5 α
  have hS : 0 ≤ S :=
    tsum_nonneg fun _ => by
      unfold l2LatticeRadialWeight
      exact inv_nonneg.mpr
        (pow_nonneg (by
          dsimp [z4FrequencyNorm]
          positivity) _)
  have hmajor :
      Summable fun γ : Z4 =>
        16 * S *
          (l2LatticeRadialWeight 3 γ *
            l2LatticeCentralWeight ε γ) :=
    (summable_l2LatticeRadial_three_mul_central
      hε hεle).mul_left _
  calc
    (∑' p : Z4 × Z4,
        l2LatticeGammaPairWeight ε p) =
        ∑' γ : Z4, ∑' α : Z4,
          l2LatticeGammaPairWeight ε (γ, α) :=
      (summable_l2LatticeGammaPairWeight hε hεle).tsum_prod
    _ ≤ ∑' γ : Z4,
        16 * S *
          (l2LatticeRadialWeight 3 γ *
            l2LatticeCentralWeight ε γ) :=
      (summable_l2LatticeGammaPairWeight_outer
        hε hεle).tsum_le_tsum
          (tsum_l2LatticeGammaPairWeight_fiber_bound ·)
          hmajor
    _ = 16 * S *
        ∑' γ : Z4,
          (l2LatticeRadialWeight 3 γ *
            l2LatticeCentralWeight ε γ) := by
      rw [tsum_mul_left]
    _ ≤ 16 * S *
        (2 * ε⁻¹ ^ (4 : ℕ) * S) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_l2LatticeRadial_three_mul_central_bound
          hε hεle)
        (mul_nonneg (by norm_num) hS)
    _ = 32 * ε⁻¹ ^ (4 : ℕ) * S ^ 2 := by
      ring_nf

def l2LatticePairShear : (Z4 × Z4) ≃ (Z4 × Z4) where
  toFun p := (p.1 + p.2, p.1)
  invFun q := (q.2, q.1 - q.2)
  left_inv p := by
    ext i <;> simp
  right_inv q := by
    ext i <;> simp

def l2LatticePairWeight (ε : ℝ) (p : Z4 × Z4) : ℝ :=
  l2LatticeRadialWeight 4 p.1 *
    l2LatticeRadialWeight 4 p.2 *
      l2LatticeCentralWeight ε (p.1 + p.2)

theorem l2LatticeGammaPairWeight_shear
    (ε : ℝ) (p : Z4 × Z4) :
    l2LatticeGammaPairWeight ε (l2LatticePairShear p) =
      l2LatticePairWeight ε p := by
  unfold l2LatticeGammaPairWeight l2LatticePairWeight
    l2LatticePairShear
  simp only [Equiv.coe_fn_mk]
  ring_nf

theorem summable_l2LatticePairWeight
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    Summable (l2LatticePairWeight ε) := by
  exact
    ((summable_l2LatticeGammaPairWeight hε hεle).comp_injective
      l2LatticePairShear.injective).congr
        (l2LatticeGammaPairWeight_shear ε)

theorem tsum_l2LatticePairWeight_bound
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    (∑' p : Z4 × Z4,
        l2LatticePairWeight ε p) ≤
      32 * ε⁻¹ ^ (4 : ℕ) *
        (∑' α : Z4,
          l2LatticeRadialWeight 5 α) ^ 2 := by
  calc
    (∑' p : Z4 × Z4,
        l2LatticePairWeight ε p) =
        ∑' p : Z4 × Z4,
          l2LatticeGammaPairWeight ε (l2LatticePairShear p) :=
      tsum_congr fun p =>
        (l2LatticeGammaPairWeight_shear ε p).symm
    _ = ∑' q : Z4 × Z4,
        l2LatticeGammaPairWeight ε q :=
      l2LatticePairShear.tsum_eq _
    _ ≤ 32 * ε⁻¹ ^ (4 : ℕ) *
        (∑' α : Z4,
          l2LatticeRadialWeight 5 α) ^ 2 :=
      tsum_l2LatticeGammaPairWeight_bound hε hεle

/-! ## Comparison with the exact factors in (3.24) and (3.30) -/

/-- The endpoint Japanese bracket in (3.24) is controlled by the
radial fourth-order weight used in the convolution estimate. -/
theorem fourthOrderModeDecay_le_l2LatticeRadialWeight
    (k : Z4) :
    fourthOrderModeDecay k ≤
      4 * l2LatticeRadialWeight 4 k := by
  let r : ℝ := z4FrequencyNorm k
  have hr : 0 ≤ r := by
    dsimp [r]
    exact z4FrequencyNorm_nonneg k
  have hR : 0 < 1 + r := by linarith
  have hD : 0 < 1 + r ^ 2 := by positivity
  have hsquare :
      (1 + r) ^ 2 ≤ 2 * (1 + r ^ 2) := by
    nlinarith [sq_nonneg (r - 1)]
  have hfour :
      (1 + r) ^ 4 ≤ 4 * (1 + r ^ 2) ^ 2 := by
    calc
      (1 + r) ^ 4 = ((1 + r) ^ 2) ^ 2 := by ring
      _ ≤ (2 * (1 + r ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg (1 + r))
          hsquare 2
      _ = 4 * (1 + r ^ 2) ^ 2 := by ring
  unfold fourthOrderModeDecay l2LatticeRadialWeight
  change ((1 + r ^ 2) ^ 2)⁻¹ ≤
    4 * ((1 + r) ^ 4)⁻¹
  field_simp [hR.ne', hD.ne']
  simpa only [mul_comm] using hfour

/-- In four dimensions the Euclidean frequency norm is at most twice
the sup norm used by the deterministic ledger. -/
theorem norm_z4EuclideanFrequency_le_two_mul_frequencyNorm
    (k : Z4) :
    ‖z4EuclideanFrequency k‖ ≤
      2 * z4FrequencyNorm k := by
  let x : Fin dim → ℝ := fun i => (k i : ℝ)
  have hr : 0 ≤ z4FrequencyNorm k :=
    z4FrequencyNorm_nonneg k
  have hcoord (i : Fin dim) :
      (k i : ℝ) ^ 2 ≤ z4FrequencyNorm k ^ 2 := by
    have hi :
        ‖(k i : ℝ)‖ ≤ z4FrequencyNorm k := by
      unfold z4FrequencyNorm
      exact norm_le_pi_norm x i
    have hsquare :=
      pow_le_pow_left₀ (norm_nonneg (k i : ℝ)) hi 2
    simpa only [Real.norm_eq_abs, sq_abs] using hsquare
  have hsum :
      paperModeNormSq k ≤
        4 * z4FrequencyNorm k ^ 2 := by
    unfold paperModeNormSq
    calc
      (∑ i : Fin dim, (k i : ℝ) ^ 2) ≤
          ∑ _i : Fin dim, z4FrequencyNorm k ^ 2 :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = 4 * z4FrequencyNorm k ^ 2 := by
        simp [dim]
  have hsquare :
      ‖z4EuclideanFrequency k‖ ^ 2 ≤
        (2 * z4FrequencyNorm k) ^ 2 := by
    rw [norm_sq_z4EuclideanFrequency]
    nlinarith
  nlinarith [norm_nonneg (z4EuclideanFrequency k)]

/-- The product of the eighth-order central decay in (3.24) and the
sixth-order Euclidean Japanese bracket in (3.30) leaves one central
second-order decay.  The constant `64` is the four-dimensional
Euclidean/sup-norm comparison cubed. -/
theorem eighthOrderFrequencyDecay_mul_paperWeight_le_central
    (ε : ℝ) (k : Z4) :
    eighthOrderFrequencyDecay
          (ε ^ 2 * z4FrequencyNorm k) *
        (1 +
          (ε ^ 2 * ‖z4EuclideanFrequency k‖) ^ 2) ^ 3 ≤
      64 * l2LatticeCentralWeight ε k := by
  let t : ℝ := ε ^ 2 * z4FrequencyNorm k
  let u : ℝ := ε ^ 2 * ‖z4EuclideanFrequency k‖
  have ht : 0 ≤ t := by
    dsimp [t]
    exact mul_nonneg (sq_nonneg ε)
      (z4FrequencyNorm_nonneg k)
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hut : u ≤ 2 * t := by
    dsimp [u, t]
    calc
      ε ^ 2 * ‖z4EuclideanFrequency k‖ ≤
          ε ^ 2 * (2 * z4FrequencyNorm k) :=
        mul_le_mul_of_nonneg_left
          (norm_z4EuclideanFrequency_le_two_mul_frequencyNorm k)
          (sq_nonneg ε)
      _ = 2 * (ε ^ 2 * z4FrequencyNorm k) := by ring
  have hbase :
      1 + u ^ 2 ≤ 4 * (1 + t ^ 2) := by
    have husq :
        u ^ 2 ≤ (2 * t) ^ 2 :=
      pow_le_pow_left₀ hu hut 2
    nlinarith
  have hcubic :
      (1 + u ^ 2) ^ 3 ≤
        64 * (1 + t ^ 2) ^ 3 := by
    calc
      (1 + u ^ 2) ^ 3 ≤
          (4 * (1 + t ^ 2)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hbase 3
      _ = 64 * (1 + t ^ 2) ^ 3 := by ring
  have hB : 0 < 1 + t ^ 2 := by positivity
  unfold eighthOrderFrequencyDecay l2LatticeCentralWeight
  change ((1 + t ^ 2) ^ 4)⁻¹ *
      (1 + u ^ 2) ^ 3 ≤
    64 * (1 + t ^ 2)⁻¹
  calc
    ((1 + t ^ 2) ^ 4)⁻¹ *
          (1 + u ^ 2) ^ 3 ≤
        ((1 + t ^ 2) ^ 4)⁻¹ *
          (64 * (1 + t ^ 2) ^ 3) :=
      mul_le_mul_of_nonneg_left hcubic (by positivity)
    _ = 64 * (1 + t ^ 2)⁻¹ := by
      field_simp [hB.ne']

/-- Pointwise deterministic majorant for the exact product of (3.24)
and the Fourier weight (3.30).  The two printed `ε⁻⁸` factors remain
visible as `ε⁻¹ ^ 16`; the lattice sum below contributes the final
`ε⁻⁴`. -/
theorem deterministicMomentDecay_mul_paperL2FourierWeight_le
    (ε : ℝ) (α β : Z4) :
    deterministicMomentDecay ε α β *
        paperL2FourierWeight ε α β ≤
      1024 * ε⁻¹ ^ (16 : ℕ) *
        l2LatticePairWeight ε (α, β) := by
  let E : ℝ := ε⁻¹ ^ (8 : ℕ)
  let A : ℝ := fourthOrderModeDecay α
  let B : ℝ := fourthOrderModeDecay β
  let D : ℝ :=
    eighthOrderFrequencyDecay
      (ε ^ 2 * z4FrequencyNorm (α + β))
  let W : ℝ :=
    (1 +
      (ε ^ 2 *
        ‖z4EuclideanFrequency (α + β)‖) ^ 2) ^ 3
  let RA : ℝ := l2LatticeRadialWeight 4 α
  let RB : ℝ := l2LatticeRadialWeight 4 β
  let C : ℝ := l2LatticeCentralWeight ε (α + β)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    exact fourthOrderModeDecay_nonneg α
  have hB : 0 ≤ B := by
    dsimp [B]
    exact fourthOrderModeDecay_nonneg β
  have hD : 0 ≤ D := by
    dsimp [D]
    exact eighthOrderFrequencyDecay_nonneg _
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hRA : 0 ≤ RA := by
    dsimp [RA, l2LatticeRadialWeight]
    positivity
  have hRB : 0 ≤ RB := by
    dsimp [RB, l2LatticeRadialWeight]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C, l2LatticeCentralWeight]
    positivity
  have hendpoint :
      A * B ≤ (4 * RA) * (4 * RB) :=
    mul_le_mul
      (fourthOrderModeDecay_le_l2LatticeRadialWeight α)
      (fourthOrderModeDecay_le_l2LatticeRadialWeight β)
      hB (mul_nonneg (by norm_num) hRA)
  have hcentral :
      D * W ≤ 64 * C := by
    dsimp [D, W, C]
    exact
      eighthOrderFrequencyDecay_mul_paperWeight_le_central
        ε (α + β)
  have hdecay :
      (A * B) * (D * W) ≤
        ((4 * RA) * (4 * RB)) * (64 * C) :=
    mul_le_mul hendpoint hcentral
      (mul_nonneg hD hW)
      (mul_nonneg
        (mul_nonneg (by norm_num) hRA)
        (mul_nonneg (by norm_num) hRB))
  unfold deterministicMomentDecay paperL2FourierWeight
    l2LatticePairWeight
  change E * A * B * D * (E * W) ≤
    1024 * ε⁻¹ ^ (16 : ℕ) * (RA * RB * C)
  calc
    E * A * B * D * (E * W) =
        E ^ 2 * ((A * B) * (D * W)) := by ring
    _ ≤ E ^ 2 *
        (((4 * RA) * (4 * RB)) * (64 * C)) :=
      mul_le_mul_of_nonneg_left hdecay (sq_nonneg E)
    _ = 1024 * ε⁻¹ ^ (16 : ℕ) *
        (RA * RB * C) := by
      dsimp [E]
      ring_nf

/-- The frequency-independent factor in one order of the weighted
second-moment majorant. -/
def parametrixOrderL2Scalar
    (outerConstant powerConstant lam ε : ℝ)
    (m : ℕ) : ℝ :=
  ‖(paperTorusVolume : ℂ)⁻¹‖ ^ 2 *
    lamEps lam ε ^ 2 * outerConstant *
    (powerConstant * lam) ^ (2 * m - 2)

theorem parametrixOrderL2Scalar_nonneg
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) :
    0 ≤ parametrixOrderL2Scalar
      outerConstant powerConstant lam ε m := by
  unfold parametrixOrderL2Scalar
  positivity

/-- Pointwise majorization of the actual P-3.5b right side after
inserting the `(3.30)` Fourier weight. -/
theorem parametrixOrderL2WeightedMomentRHS_le_latticePair
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ} {α β : Z4}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) :
    parametrixOrderL2WeightedMomentRHS
        outerConstant powerConstant lam ε m α β ≤
      parametrixOrderL2Scalar
          outerConstant powerConstant lam ε m *
        (1024 * ε⁻¹ ^ (16 : ℕ) *
          l2LatticePairWeight ε (α, β)) := by
  let S : ℝ :=
    parametrixOrderL2Scalar
      outerConstant powerConstant lam ε m
  let D : ℝ := deterministicMomentDecay ε α β
  let W : ℝ := paperL2FourierWeight ε α β
  have hS : 0 ≤ S := by
    dsimp [S]
    exact parametrixOrderL2Scalar_nonneg
      houter hpower hlam
  have hD : 0 ≤ D := by
    dsimp [D]
    exact deterministicMomentDecay_nonneg ε α β
  have hW : 0 ≤ W := by
    dsimp [W]
    exact paperL2FourierWeight_nonneg ε α β
  have hmin : 0 ≤ min 1 D :=
    le_min zero_le_one hD
  have hminW :
      min 1 D * W ≤ D * W :=
    mul_le_mul_of_nonneg_right (min_le_right 1 D) hW
  calc
    parametrixOrderL2WeightedMomentRHS
          outerConstant powerConstant lam ε m α β =
        S * (min 1 D * W) := by
      dsimp [S, D, W, parametrixOrderL2Scalar,
        parametrixOrderL2WeightedMomentRHS,
        deterministicMomentRHS]
      ring
    _ ≤ S * (D * W) :=
      mul_le_mul_of_nonneg_left hminW hS
    _ ≤ S *
        (1024 * ε⁻¹ ^ (16 : ℕ) *
          l2LatticePairWeight ε (α, β)) :=
      mul_le_mul_of_nonneg_left
        (deterministicMomentDecay_mul_paperL2FourierWeight_le
          ε α β)
        hS

/-- The full deterministic majorant consumed by the Tonelli form of
(3.30) is summable.  This discharges the formerly explicit
`hmajorant` hypothesis in the orderwise L² bridge. -/
theorem summable_parametrixOrderL2WeightedMomentRHS
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    Summable fun p : Z4 × Z4 =>
      parametrixOrderL2WeightedMomentRHS
        outerConstant powerConstant lam ε m p.2 p.1 := by
  let C : ℝ :=
    parametrixOrderL2Scalar
        outerConstant powerConstant lam ε m *
      (1024 * ε⁻¹ ^ (16 : ℕ))
  have hpair :
      Summable fun p : Z4 × Z4 =>
        l2LatticePairWeight ε (p.2, p.1) := by
    have hcomp :=
      (summable_l2LatticePairWeight hε hεle).comp_injective
        (Equiv.prodComm Z4 Z4).injective
    apply hcomp.congr
    rintro ⟨α, β⟩
    rfl
  have hmajor :
      Summable fun p : Z4 × Z4 =>
        C * l2LatticePairWeight ε (p.2, p.1) :=
    hpair.mul_left C
  apply hmajor.of_nonneg_of_le
  · intro p
    exact parametrixOrderL2WeightedMomentRHS_nonneg
      houter hpower hlam
  · intro p
    simpa only [C, mul_assoc] using
      (parametrixOrderL2WeightedMomentRHS_le_latticePair
        (α := p.2) (β := p.1)
        houter hpower hlam)

/-- Numerical form of paper (3.31): the complete double Fourier sum
costs `ε⁻²⁰`.  The remaining square is a fixed finite lattice mass,
independent of all paper parameters and of the order `m`. -/
theorem tsum_parametrixOrderL2WeightedMomentRHS_le
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    (∑' p : Z4 × Z4,
        parametrixOrderL2WeightedMomentRHS
          outerConstant powerConstant lam ε m p.2 p.1) ≤
      32768 *
        parametrixOrderL2Scalar
          outerConstant powerConstant lam ε m *
        ε⁻¹ ^ (20 : ℕ) *
        (∑' k : Z4,
          l2LatticeRadialWeight 5 k) ^ 2 := by
  let S : ℝ :=
    parametrixOrderL2Scalar
      outerConstant powerConstant lam ε m
  let C : ℝ := S * (1024 * ε⁻¹ ^ (16 : ℕ))
  have hS : 0 ≤ S := by
    dsimp [S]
    exact parametrixOrderL2Scalar_nonneg
      houter hpower hlam
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpairSwap :
      Summable fun p : Z4 × Z4 =>
        l2LatticePairWeight ε (p.2, p.1) := by
    have hcomp :=
      (summable_l2LatticePairWeight hε hεle).comp_injective
        (Equiv.prodComm Z4 Z4).injective
    apply hcomp.congr
    rintro ⟨α, β⟩
    rfl
  have hmajor :
      Summable fun p : Z4 × Z4 =>
        C * l2LatticePairWeight ε (p.2, p.1) :=
    hpairSwap.mul_left C
  have hswap :
      (∑' p : Z4 × Z4,
          l2LatticePairWeight ε (p.2, p.1)) =
        ∑' p : Z4 × Z4,
          l2LatticePairWeight ε p := by
    calc
      (∑' p : Z4 × Z4,
          l2LatticePairWeight ε (p.2, p.1)) =
          ∑' p : Z4 × Z4,
            l2LatticePairWeight ε
              ((Equiv.prodComm Z4 Z4) p) := by
        apply tsum_congr
        rintro ⟨α, β⟩
        rfl
      _ = ∑' p : Z4 × Z4,
          l2LatticePairWeight ε p :=
        (Equiv.prodComm Z4 Z4).tsum_eq _
  calc
    (∑' p : Z4 × Z4,
        parametrixOrderL2WeightedMomentRHS
          outerConstant powerConstant lam ε m p.2 p.1) ≤
        ∑' p : Z4 × Z4,
          C * l2LatticePairWeight ε (p.2, p.1) :=
      (summable_parametrixOrderL2WeightedMomentRHS
        houter hpower hlam hε hεle).tsum_le_tsum
          (fun p => by
            simpa only [C, S, mul_assoc] using
              (parametrixOrderL2WeightedMomentRHS_le_latticePair
                (α := p.2) (β := p.1)
                houter hpower hlam))
          hmajor
    _ = C *
        ∑' p : Z4 × Z4,
          l2LatticePairWeight ε (p.2, p.1) := by
      rw [tsum_mul_left]
    _ = C *
        ∑' p : Z4 × Z4,
          l2LatticePairWeight ε p := by
      rw [hswap]
    _ ≤ C *
        (32 * ε⁻¹ ^ (4 : ℕ) *
          (∑' k : Z4,
            l2LatticeRadialWeight 5 k) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (tsum_l2LatticePairWeight_bound hε hεle) hC
    _ = 32768 *
        parametrixOrderL2Scalar
          outerConstant powerConstant lam ε m *
        ε⁻¹ ^ (20 : ℕ) *
        (∑' k : Z4,
          l2LatticeRadialWeight 5 k) ^ 2 := by
      dsimp [C, S]
      ring_nf

/-! ## Automatic almost-sure summability and the closed P-L² bound -/

/-- Summability of the expected deterministic majorant forces the
realized weighted Fourier square-sum to be finite almost surely.  Thus
the non-junk `hsum` condition used by the abstract Tonelli adapter is a
consequence of P-3.5b, not an additional analytic hypothesis. -/
theorem ae_summable_parametrixOrder_weightedCoeff
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
    (A : M.Ω → TorusL2 →L[ℂ] TorusL2)
    (hreal :
      ParametrixOrderL2CoeffRealization
        M ρ lam ε m A)
    (hfubini :
      ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick : WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      Summable fun p : Z4 × Z4 =>
        ‖torusFourierMatrixCoeff
            (A ω) p.2 p.1‖ ^ 2 *
          paperL2FourierWeight ε p.2 p.1 := by
  let f : (Z4 × Z4) → M.Ω → ℝ :=
    fun p ω =>
      ‖torusFourierMatrixCoeff
          (A ω) p.2 p.1‖ ^ 2 *
        paperL2FourierWeight ε p.2 p.1
  let B : (Z4 × Z4) → ℝ :=
    fun p =>
      parametrixOrderL2WeightedMomentRHS
        outerConstant powerConstant lam ε m p.2 p.1
  have hcoeff (p : Z4 × Z4) :=
    parametrixOrder_weightedCoeff_measurable_and_bound
      A hreal (hfubini p.2 p.1) hwick
        (hdet p.2 p.1) hε hεle
  have hmeas :
      ∀ p : Z4 × Z4,
        AEMeasurable
          (fun ω => ENNReal.ofReal (f p ω))
          (volume : Measure M.Ω) := by
    intro p
    simpa only [f] using (hcoeff p).1
  have hterm :
      ∀ p : Z4 × Z4,
        (∫⁻ ω, ENNReal.ofReal (f p ω)
          ∂(volume : Measure M.Ω)) ≤
          ENNReal.ofReal (B p) := by
    intro p
    simpa only [f, B] using (hcoeff p).2
  have hBsum : Summable B := by
    simpa only [B] using
      (summable_parametrixOrderL2WeightedMomentRHS
        houter hpower hlam hε hεle)
  have hsumIntegrals :
      (∑' p : Z4 × Z4,
          (∫⁻ ω, ENNReal.ofReal (f p ω)
            ∂(volume : Measure M.Ω))) < ∞ := by
    exact lt_of_le_of_lt
      (ENNReal.tsum_le_tsum hterm)
      hBsum.tsum_ofReal_lt_top
  have hlintegral :
      (∫⁻ ω,
          ∑' p : Z4 × Z4,
            ENNReal.ofReal (f p ω)
          ∂(volume : Measure M.Ω)) < ∞ := by
    rw [lintegral_tsum hmeas]
    exact hsumIntegrals
  have hae :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        (∑' p : Z4 × Z4,
          ENNReal.ofReal (f p ω)) < ∞ :=
    ae_lt_top' (AEMeasurable.tsum hmeas) hlintegral.ne
  filter_upwards [hae] with ω hω
  have hnn :
      Summable
        (ENNReal.toNNReal ∘
          fun p : Z4 × Z4 =>
            ENNReal.ofReal (f p ω)) :=
    ENNReal.summable_toNNReal_of_tsum_ne_top hω.ne
  have hrealSum :
      Summable fun p : Z4 × Z4 =>
        ((ENNReal.ofReal (f p ω)).toNNReal : ℝ) :=
    NNReal.summable_coe.mpr hnn
  apply hrealSum.congr
  intro p
  have hfp : 0 ≤ f p ω := by
    dsimp [f]
    exact mul_nonneg (sq_nonneg _)
      (paperL2FourierWeight_nonneg ε p.2 p.1)
  simp only [ENNReal.ofReal, ENNReal.toNNReal_coe,
    Real.coe_toNNReal', max_eq_left hfp]
  rfl

/-- Closed ENNReal expectation form of P-L² at one parametrix order:
P-3.5b alone supplies both summability hypotheses of the abstract
Tonelli adapter, and (3.31) supplies the displayed `ε⁻²⁰` bound. -/
theorem lintegral_parametrixOrder_normSq_le_explicit
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
    (A : M.Ω → TorusL2 →L[ℂ] TorusL2)
    (hreal :
      ParametrixOrderL2CoeffRealization
        M ρ lam ε m A)
    (hfubini :
      ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick : WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    (∫⁻ ω,
        ENNReal.ofReal (‖A ω‖ ^ 2)
        ∂(volume : Measure M.Ω)) ≤
      ENNReal.ofReal
        (32768 *
          parametrixOrderL2Scalar
            outerConstant powerConstant lam ε m *
          ε⁻¹ ^ (20 : ℕ) *
          (∑' k : Z4,
            l2LatticeRadialWeight 5 k) ^ 2) := by
  have hmajorant :=
    summable_parametrixOrderL2WeightedMomentRHS
      (m := m)
      houter hpower hlam hε hεle
  have hsum :=
    ae_summable_parametrixOrder_weightedCoeff
      A hreal hfubini hwick hdet
      houter hpower hlam hε hεle
  calc
    (∫⁻ ω,
        ENNReal.ofReal (‖A ω‖ ^ 2)
        ∂(volume : Measure M.Ω)) ≤
        ENNReal.ofReal
          (∑' p : Z4 × Z4,
            parametrixOrderL2WeightedMomentRHS
              outerConstant powerConstant lam ε m p.2 p.1) :=
      lintegral_parametrixOrder_normSq_le
        A hreal hfubini hwick hdet
        houter hpower hlam hε hεle
        hmajorant hsum
    _ ≤ ENNReal.ofReal
        (32768 *
          parametrixOrderL2Scalar
            outerConstant powerConstant lam ε m *
          ε⁻¹ ^ (20 : ℕ) *
          (∑' k : Z4,
            l2LatticeRadialWeight 5 k) ^ 2) :=
      ENNReal.ofReal_le_ofReal
        (tsum_parametrixOrderL2WeightedMomentRHS_le
          (m := m)
          houter hpower hlam hε hεle)

/-- Ordinary real-integral form of the preceding explicit orderwise
bound. -/
theorem integral_parametrixOrder_normSq_le_explicit
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
    (A : M.Ω → TorusL2 →L[ℂ] TorusL2)
    (hreal :
      ParametrixOrderL2CoeffRealization
        M ρ lam ε m A)
    (hfubini :
      ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick : WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hintA :
      Integrable (fun ω => ‖A ω‖ ^ 2)
        (volume : Measure M.Ω)) :
    (∫ ω, ‖A ω‖ ^ 2
        ∂(volume : Measure M.Ω)) ≤
      32768 *
        parametrixOrderL2Scalar
          outerConstant powerConstant lam ε m *
        ε⁻¹ ^ (20 : ℕ) *
        (∑' k : Z4,
          l2LatticeRadialWeight 5 k) ^ 2 := by
  have hmajorant :=
    summable_parametrixOrderL2WeightedMomentRHS
      (m := m)
      houter hpower hlam hε hεle
  have hsum :=
    ae_summable_parametrixOrder_weightedCoeff
      A hreal hfubini hwick hdet
      houter hpower hlam hε hεle
  exact
    (integral_parametrixOrder_normSq_le
      A hreal hfubini hwick hdet
      houter hpower hlam hε hεle
      hmajorant hsum hintA).trans
      (tsum_parametrixOrderL2WeightedMomentRHS_le
        (m := m)
        houter hpower hlam hε hεle)

end

end Anderson4D
