import Anderson4D.DetParametrix.Paper42_Moment.R324SlotBudgetEstimate

/-!
# The keyed-decay ledger for the R-324 slot budget

This file quantifies every structural ingredient of the residual slot
budget `R324SlotLogBudget`:

* an explicit bound `∑_{k ∈ ℤ⁴} ⟨k⟩⁻⁸ ≤ 4096` for the eighth-order
  frequency decay (`tsum_eighthOrderFrequencyDecay_z4_le`);
* the exact slotwise product factorization of key sums over `Fin m → ℤ⁴`
  (`tsum_realSlotProduct`);
* the exponential schedule count
  `card (R324RefinedScheduleIndex m) ≤ 16 ^ (2m)`;
* the resulting discharge of the residual slot budget from a single
  per-key interior bound (`r324SlotLogBudget_of_keyedCoreL1DecayBound`),
  and the corresponding instantiations of the capstone.

The analytic estimate is isolated in the Prop `R324KeyedCoreL1DecayBound`:
the grouped interior `L¹` mass of one
common-increment group must carry two eighth-order decay units per
frequency slot, at the amplitude `A^{2m} |log ε|^{m-1}`.  This is the
iterated Proposition 4.1 estimate with keyed Fourier decay; the coarse
proved majorant (`r324GroupedRefinedCoreL1_le_skeleton_mul_covariance`)
is `ε`-divergent and cannot supply it.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## Explicit one-dimensional lattice sums -/

/-- Partial sums of `1/(n+1)²` are bounded by `2 - 1/N`. -/
private theorem sum_range_inv_succ_sq_le (N : ℕ) :
    (∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ 2)⁻¹) ≤
      2 - ((N : ℝ))⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        norm_num
      · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
        have hNs : (0 : ℝ) < (N : ℝ) + 1 := by linarith
        have hexp :
            ((N : ℝ))⁻¹ - (((N : ℝ) + 1) ^ 2)⁻¹ -
                ((N : ℝ) + 1)⁻¹ =
              ((N : ℝ) * ((N : ℝ) + 1) ^ 2)⁻¹ := by
          field_simp
          ring
        have hpos :
            (0 : ℝ) ≤ ((N : ℝ) * ((N : ℝ) + 1) ^ 2)⁻¹ := by
          positivity
        push_cast
        linarith [ih]

/-- The series `∑ 1/(n+1)²` over `ℕ` converges. -/
private theorem summable_inv_succ_sq :
    Summable fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹ := by
  have h :=
    (Real.summable_one_div_nat_add_rpow 1 2).mpr
      (by norm_num : (1 : ℝ) < 2)
  refine h.congr fun n => ?_
  rw [one_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1),
    Real.rpow_two]

/-- Explicit tail bound `∑_{n ∈ ℕ} 1/(n+1)² ≤ 2`. -/
private theorem tsum_inv_succ_sq_le :
    (∑' n : ℕ, (((n : ℝ) + 1) ^ 2)⁻¹) ≤ 2 := by
  refine summable_inv_succ_sq.tsum_le_of_sum_le fun u => ?_
  have hsub : u ⊆ Finset.range (u.sup id + 1) := by
    intro n hn
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  calc
    (∑ n ∈ u, (((n : ℝ) + 1) ^ 2)⁻¹) ≤
        ∑ n ∈ Finset.range (u.sup id + 1),
          (((n : ℝ) + 1) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => by positivity)
    _ ≤ 2 - (((u.sup id + 1 : ℕ) : ℝ))⁻¹ :=
      sum_range_inv_succ_sq_le _
    _ ≤ 2 := by
      have : (0 : ℝ) ≤ (((u.sup id + 1 : ℕ) : ℝ))⁻¹ := by
        positivity
      linarith

/-- Identification of the negative branch of the coordinate weight. -/
private theorem intCoordWeight_neg_eq (n : ℕ) :
    (((Int.natAbs (-((n : ℤ) + 1)) : ℝ) + 1) ^ 2)⁻¹ =
      ((((n + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹ := by
  rw [show -((n : ℤ) + 1) = Int.negSucc n by omega,
    Int.natAbs_negSucc]

/-- The doubled-sided coordinate weight is summable over `ℤ`. -/
private theorem summable_intCoordWeight :
    Summable fun n : ℤ => (((n.natAbs : ℝ) + 1) ^ 2)⁻¹ := by
  refine Summable.of_nat_of_neg_add_one
    (f := fun n : ℤ => (((n.natAbs : ℝ) + 1) ^ 2)⁻¹) ?_ ?_
  · simpa using summable_inv_succ_sq
  · have hshift :
        Summable fun n : ℕ => ((((n + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹ :=
      summable_inv_succ_sq.comp_injective Nat.succ_injective
    exact hshift.congr fun n => (intCoordWeight_neg_eq n).symm

/-- Explicit doubled-sided coordinate bound
`∑_{n ∈ ℤ} 1/(|n|+1)² ≤ 4`. -/
private theorem tsum_intCoordWeight_le :
    (∑' n : ℤ, (((n.natAbs : ℝ) + 1) ^ 2)⁻¹) ≤ 4 := by
  have hs1 : Summable fun n : ℕ =>
      ((((n : ℤ).natAbs : ℝ) + 1) ^ 2)⁻¹ := by
    simpa using summable_inv_succ_sq
  have hs2 : Summable fun n : ℕ =>
      (((Int.natAbs (-((n : ℤ) + 1)) : ℝ) + 1) ^ 2)⁻¹ := by
    have hshift :
        Summable fun n : ℕ => ((((n + 1 : ℕ) : ℝ) + 1) ^ 2)⁻¹ :=
      summable_inv_succ_sq.comp_injective Nat.succ_injective
    exact hshift.congr fun n => (intCoordWeight_neg_eq n).symm
  have hsplit :=
    tsum_of_nat_of_neg_add_one
      (f := fun n : ℤ => (((n.natAbs : ℝ) + 1) ^ 2)⁻¹) hs1 hs2
  have h1 : (∑' n : ℕ, ((((n : ℤ).natAbs : ℝ) + 1) ^ 2)⁻¹) ≤ 2 := by
    calc
      (∑' n : ℕ, ((((n : ℤ).natAbs : ℝ) + 1) ^ 2)⁻¹) =
          ∑' n : ℕ, (((n : ℝ) + 1) ^ 2)⁻¹ := by
        exact tsum_congr fun n => by simp
      _ ≤ 2 := tsum_inv_succ_sq_le
  have h2 : (∑' n : ℕ,
      (((Int.natAbs (-((n : ℤ) + 1)) : ℝ) + 1) ^ 2)⁻¹) ≤ 2 := by
    have hterm : ∀ n : ℕ,
        (((Int.natAbs (-((n : ℤ) + 1)) : ℝ) + 1) ^ 2)⁻¹ ≤
          (((n : ℝ) + 1) ^ 2)⁻¹ := by
      intro n
      rw [intCoordWeight_neg_eq n]
      have hbase : ((n : ℝ) + 1) ^ 2 ≤
          (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
        have hstep : ((n : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          linarith
        exact pow_le_pow_left₀ (by positivity) hstep 2
      exact inv_anti₀ (by positivity) hbase
    exact (hs2.tsum_le_tsum hterm summable_inv_succ_sq).trans
      tsum_inv_succ_sq_le
  rw [hsplit]
  linarith

/-! ## Slotwise product factorization of key sums -/

/-- Summability of a slotwise product of nonnegative summable weights
over all assignments `Fin n → A`. -/
private theorem summable_realSlotProduct
    {A : Type*} (n : ℕ) (g : Fin n → A → ℝ)
    (h0 : ∀ i a, 0 ≤ g i a) (hg : ∀ i, Summable (g i)) :
    Summable fun q : Fin n → A => ∏ i, g i (q i) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
      have htail :
          Summable fun q : Fin n → A =>
            ∏ i, g i.succ (q i) :=
        ih (fun i => g i.succ) (fun i a => h0 i.succ a)
          (fun i => hg i.succ)
      have hpair :
          Summable fun p : A × (Fin n → A) =>
            g 0 p.1 * ∏ i, g i.succ (p.2 i) :=
        (hg 0).mul_of_nonneg htail (fun a => h0 0 a)
          (fun q => Finset.prod_nonneg fun i _ => h0 i.succ _)
      refine ((Fin.consEquiv fun _ : Fin (n + 1) => A).summable_iff).mp
        (hpair.congr fun p => ?_)
      simp [Fin.consEquiv, Fin.prod_univ_succ]

/-- A key sum of slotwise products is the product of the slot sums. -/
private theorem tsum_realSlotProduct
    {A : Type*} (n : ℕ) (g : Fin n → A → ℝ)
    (h0 : ∀ i a, 0 ≤ g i a) (hg : ∀ i, Summable (g i)) :
    (∑' q : Fin n → A, ∏ i, g i (q i)) =
      ∏ i, ∑' a : A, g i a := by
  induction n with
  | zero =>
      rw [tsum_eq_single (fun i : Fin 0 => i.elim0)
        (fun q hq => absurd (funext fun i => i.elim0) hq)]
      simp
  | succ n ih =>
      have htail :
          Summable fun q : Fin n → A =>
            ∏ i, g i.succ (q i) :=
        summable_realSlotProduct n (fun i => g i.succ)
          (fun i a => h0 i.succ a) (fun i => hg i.succ)
      have hpair :
          Summable fun p : A × (Fin n → A) =>
            g 0 p.1 * ∏ i, g i.succ (p.2 i) :=
        (hg 0).mul_of_nonneg htail (fun a => h0 0 a)
          (fun q => Finset.prod_nonneg fun i _ => h0 i.succ _)
      calc
        (∑' q : Fin (n + 1) → A, ∏ i, g i (q i)) =
            ∑' p : A × (Fin n → A),
              g 0 p.1 * ∏ i, g i.succ (p.2 i) := by
          rw [← (Fin.consEquiv fun _ : Fin (n + 1) => A).tsum_eq
            (fun q : Fin (n + 1) → A => ∏ i, g i (q i))]
          exact tsum_congr fun p => by
            simp [Fin.consEquiv, Fin.prod_univ_succ]
        _ = ∑' a : A, ∑' q : Fin n → A,
              g 0 a * ∏ i, g i.succ (q i) :=
          hpair.tsum_prod' fun a => htail.mul_left (g 0 a)
        _ = ∑' a : A, g 0 a *
              ∑' q : Fin n → A, ∏ i, g i.succ (q i) :=
          tsum_congr fun a => tsum_mul_left
        _ = (∑' a : A, g 0 a) *
              ∑' q : Fin n → A, ∏ i, g i.succ (q i) :=
          tsum_mul_right
        _ = (∑' a : A, g 0 a) * ∏ i : Fin n, ∑' a : A, g i.succ a := by
          rw [ih (fun i => g i.succ) (fun i a => h0 i.succ a)
            (fun i => hg i.succ)]
        _ = ∏ i : Fin (n + 1), ∑' a : A, g i a := by
          rw [Fin.prod_univ_succ]

/-! ## The explicit eighth-order lattice budget on `ℤ⁴` -/

/-- Explicit total mass of the product summability weight:
`∑_{k ∈ ℤ⁴} ∏ᵢ (|kᵢ|+1)⁻² ≤ 256`. -/
theorem tsum_latticeSummabilityWeight_le :
    (∑' k : Z4, latticeSummabilityWeight k) ≤ 256 := by
  have hfact :=
    tsum_realSlotProduct (A := ℤ) dim
      (fun _ n => (((n.natAbs : ℝ) + 1) ^ 2)⁻¹)
      (fun _ a => by positivity)
      (fun _ => summable_intCoordWeight)
  calc
    (∑' k : Z4, latticeSummabilityWeight k) =
        ∏ _i : Fin dim, ∑' n : ℤ, (((n.natAbs : ℝ) + 1) ^ 2)⁻¹ :=
      hfact
    _ ≤ ∏ _i : Fin dim, (4 : ℝ) :=
      Finset.prod_le_prod
        (fun _ _ => tsum_nonneg fun n => by positivity)
        (fun _ _ => tsum_intCoordWeight_le)
    _ = 256 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      norm_num

/-- Pointwise comparison of the paper's `⟨k⟩⁻⁸` on the lattice with the
product summability weight. -/
theorem eighthOrderFrequencyDecay_le_latticeWeight (k : Z4) :
    eighthOrderFrequencyDecay ‖z4EuclideanFrequency k‖ ≤
      16 * latticeSummabilityWeight k := by
  have hS0 : 0 ≤ paperModeNormSq k := by
    unfold paperModeNormSq
    positivity
  have hcoord : ∀ i : Fin dim,
      ((Int.natAbs (k i) : ℝ) + 1) ^ 2 ≤
        2 * (1 + paperModeNormSq k) := by
    intro i
    have habs : ((Int.natAbs (k i) : ℝ)) = |((k i : ℝ))| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hsq : ((Int.natAbs (k i) : ℝ)) ^ 2 = ((k i : ℝ)) ^ 2 := by
      rw [habs, sq_abs]
    have hle : ((k i : ℝ)) ^ 2 ≤ paperModeNormSq k := by
      unfold paperModeNormSq
      exact Finset.single_le_sum
        (f := fun j : Fin dim => ((k j : ℝ)) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h0 : (0 : ℝ) ≤ (Int.natAbs (k i) : ℝ) := by positivity
    nlinarith [hsq, hle, h0, sq_nonneg ((Int.natAbs (k i) : ℝ) - 1)]
  have hP :
      (∏ i : Fin dim, ((Int.natAbs (k i) : ℝ) + 1) ^ 2) ≤
        16 * (1 + paperModeNormSq k) ^ 4 := by
    calc
      (∏ i : Fin dim, ((Int.natAbs (k i) : ℝ) + 1) ^ 2) ≤
          ∏ _i : Fin dim, 2 * (1 + paperModeNormSq k) :=
        Finset.prod_le_prod (fun i _ => by positivity)
          (fun i _ => hcoord i)
      _ = (2 * (1 + paperModeNormSq k)) ^ (4 : ℕ) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = 16 * (1 + paperModeNormSq k) ^ 4 := by ring
  have hPpos :
      (0 : ℝ) < ∏ i : Fin dim, ((Int.natAbs (k i) : ℝ) + 1) ^ 2 :=
    Finset.prod_pos fun i _ => by positivity
  have hlsw :
      latticeSummabilityWeight k =
        (∏ i : Fin dim, ((Int.natAbs (k i) : ℝ) + 1) ^ 2)⁻¹ := by
    unfold latticeSummabilityWeight
    rw [← Finset.prod_inv_distrib]
  unfold eighthOrderFrequencyDecay
  rw [norm_sq_z4EuclideanFrequency, hlsw]
  have h16 : ((1 + paperModeNormSq k) ^ 4)⁻¹ =
      16 * (16 * (1 + paperModeNormSq k) ^ 4)⁻¹ := by
    rw [mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (by norm_num : (16 : ℝ) ≠ 0), one_mul]
  rw [h16]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hPpos hP) (by norm_num)

/-- The paper's `⟨k⟩⁻⁸` is summable on `ℤ⁴`. -/
theorem summable_eighthOrderFrequencyDecay_z4 :
    Summable fun k : Z4 =>
      eighthOrderFrequencyDecay ‖z4EuclideanFrequency k‖ :=
  (summable_latticeSummabilityWeight.mul_left 16).of_nonneg_of_le
    (fun _ => eighthOrderFrequencyDecay_nonneg _)
    (fun k => eighthOrderFrequencyDecay_le_latticeWeight k)

/-- **Explicit eighth-order lattice budget**:
`∑_{k ∈ ℤ⁴} (1+‖k‖²)⁻⁴ ≤ 4096`. -/
theorem tsum_eighthOrderFrequencyDecay_z4_le :
    (∑' k : Z4,
      eighthOrderFrequencyDecay ‖z4EuclideanFrequency k‖) ≤ 4096 := by
  calc
    (∑' k : Z4,
        eighthOrderFrequencyDecay ‖z4EuclideanFrequency k‖) ≤
        ∑' k : Z4, 16 * latticeSummabilityWeight k :=
      summable_eighthOrderFrequencyDecay_z4.tsum_le_tsum
        (fun k => eighthOrderFrequencyDecay_le_latticeWeight k)
        (summable_latticeSummabilityWeight.mul_left 16)
    _ = 16 * ∑' k : Z4, latticeSummabilityWeight k :=
      tsum_mul_left
    _ ≤ 16 * 256 :=
      mul_le_mul_of_nonneg_left tsum_latticeSummabilityWeight_le
        (by norm_num)
    _ = 4096 := by norm_num

/-! ## The exponential schedule count -/

/-- The residual-refined schedule index is at most exponentially large:
both layers are signatures, i.e. pairs of subsets of `Fin (2m)`. -/
theorem card_r324RefinedScheduleIndex_le (m : ℕ) :
    Fintype.card (R324RefinedScheduleIndex m) ≤ 16 ^ (2 * m) := by
  classical
  have hinj :
      Function.Injective
        (fun x : R324RefinedScheduleIndex m =>
          ((x.1.1, x.2.1) :
            (Finset (Fin (2 * m)) × Finset (Fin (2 * m))) ×
              (Finset (Fin (2 * m)) × Finset (Fin (2 * m))))) := by
    rintro ⟨⟨s, hs⟩, r, hr⟩ ⟨⟨s', hs'⟩, r', hr'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    subst h2
    rfl
  refine (Fintype.card_le_of_injective _ hinj).trans ?_
  simp only [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
  have hpow :
      2 ^ (2 * m) * 2 ^ (2 * m) * (2 ^ (2 * m) * 2 ^ (2 * m)) =
        16 ^ (2 * m) := by
    rw [← pow_add, ← pow_add,
      show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    congr 1
    omega
  exact hpow.le

/-! ## The keyed decay weight and the residual hypothesis -/

/-- The eighth-order decay never exceeds one. -/
theorem eighthOrderFrequencyDecay_le_one (x : ℝ) :
    eighthOrderFrequencyDecay x ≤ 1 := by
  unfold eighthOrderFrequencyDecay
  have h1 : (1 : ℝ) ≤ (1 + x ^ 2) ^ 4 := by
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), sq_nonneg (1 + x ^ 2)]
  exact inv_le_one_of_one_le₀ h1

/-- Two eighth-order decay units at every frequency slot of one common
increment key. -/
def r324KeyedDecaySquared {m : ℕ} (hm : 0 < m) (b : ℕ) : ℝ :=
  ∏ j : Fin m,
    eighthOrderFrequencyDecay
        ‖z4EuclideanFrequency
          (SmoothCutoff.r324NatEquivStandardConfigurations hm b j)‖ ^ 2

theorem r324KeyedDecaySquared_nonneg
    {m : ℕ} (hm : 0 < m) (b : ℕ) :
    0 ≤ r324KeyedDecaySquared hm b := by
  unfold r324KeyedDecaySquared
  exact Finset.prod_nonneg fun j _ => sq_nonneg _

/-- **The residual keyed interior bound.**  The grouped interior `L¹`
mass of one common-increment group carries the amplitude
`A^{2m} |log ε|^{m-1}` and two eighth-order decay units per frequency
slot.  This is the quantitative iterated-Proposition-4.1 content with
keyed Fourier decay; everything else in the slot budget is discharged
unconditionally below. -/
def R324KeyedCoreL1DecayBound (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m)
    (ε A : ℝ) : Prop :=
  ∀ p : R324RefinedScheduleIndex m × ℕ,
    ρ.r324GroupedRefinedCoreL1 hm ε p ≤
      A ^ (2 * m) * |Real.log ε| ^ (m - 1) *
        r324KeyedDecaySquared hm p.2

/-! ## The keyed slot sum -/

/-- Exchange one squared decay unit at the marked slot against the
reciprocal routed cost. -/
private theorem prod_sq_mul_slot_eq
    {m : ℕ} (D : Fin m → ℝ) (C : ℝ) (i : Fin m)
    (hcancel : C * D i = 1) :
    (∏ j : Fin m, D j ^ 2) * C =
      ∏ j : Fin m, (if j = i then D j else D j ^ 2) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun j => D j ^ 2)
      (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ
      (fun j => if j = i then D j else D j ^ 2)
      (Finset.mem_univ i),
    if_pos rfl]
  have herase :
      (∏ j ∈ Finset.univ.erase i,
        (if j = i then D j else D j ^ 2)) =
        ∏ j ∈ Finset.univ.erase i, D j ^ 2 :=
    Finset.prod_congr rfl fun j hj =>
      if_neg (Finset.ne_of_mem_erase hj)
  rw [herase]
  calc
    D i ^ 2 * (∏ j ∈ Finset.univ.erase i, D j ^ 2) * C =
        (C * D i) * (D i * ∏ j ∈ Finset.univ.erase i, D j ^ 2) := by
      ring
    _ = D i * ∏ j ∈ Finset.univ.erase i, D j ^ 2 := by
      rw [hcancel, one_mul]

/-- The slotwise weight of the keyed slot sum: one bare decay unit at
the marked slot, two units elsewhere. -/
private def r324KeyedSlotWeight {m : ℕ} (i j : Fin m) (k : Z4) : ℝ :=
  if j = i then
    eighthOrderFrequencyDecay ‖z4EuclideanFrequency k‖
  else
    eighthOrderFrequencyDecay ‖z4EuclideanFrequency k‖ ^ 2

private theorem r324KeyedSlotWeight_nonneg
    {m : ℕ} (i j : Fin m) (k : Z4) :
    0 ≤ r324KeyedSlotWeight i j k := by
  unfold r324KeyedSlotWeight
  split
  · exact eighthOrderFrequencyDecay_nonneg _
  · exact sq_nonneg _

private theorem summable_sq_eighthOrderFrequencyDecay_z4 :
    Summable fun k : Z4 =>
      eighthOrderFrequencyDecay ‖z4EuclideanFrequency k‖ ^ 2 := by
  refine summable_eighthOrderFrequencyDecay_z4.of_nonneg_of_le
    (fun k => sq_nonneg _) (fun k => ?_)
  have h0 := eighthOrderFrequencyDecay_nonneg
    ‖z4EuclideanFrequency k‖
  have h1 := eighthOrderFrequencyDecay_le_one
    ‖z4EuclideanFrequency k‖
  nlinarith

private theorem tsum_sq_eighthOrderFrequencyDecay_z4_le :
    (∑' k : Z4,
      eighthOrderFrequencyDecay ‖z4EuclideanFrequency k‖ ^ 2) ≤
      4096 := by
  refine (summable_sq_eighthOrderFrequencyDecay_z4.tsum_le_tsum
    (fun k => ?_) summable_eighthOrderFrequencyDecay_z4).trans
    tsum_eighthOrderFrequencyDecay_z4_le
  have h0 := eighthOrderFrequencyDecay_nonneg
    ‖z4EuclideanFrequency k‖
  have h1 := eighthOrderFrequencyDecay_le_one
    ‖z4EuclideanFrequency k‖
  nlinarith

private theorem summable_r324KeyedSlotWeight
    {m : ℕ} (i j : Fin m) :
    Summable (r324KeyedSlotWeight (m := m) i j) := by
  unfold r324KeyedSlotWeight
  rcases eq_or_ne j i with h | h
  · simpa [h] using summable_eighthOrderFrequencyDecay_z4
  · simpa [h] using summable_sq_eighthOrderFrequencyDecay_z4

private theorem tsum_r324KeyedSlotWeight_le
    {m : ℕ} (i j : Fin m) :
    (∑' k : Z4, r324KeyedSlotWeight i j k) ≤ 4096 := by
  unfold r324KeyedSlotWeight
  rcases eq_or_ne j i with h | h
  · simpa [h] using tsum_eighthOrderFrequencyDecay_z4_le
  · simpa [h] using tsum_sq_eighthOrderFrequencyDecay_z4_le

/-- Pointwise exchange: keyed decay times reciprocal routed cost is the
slotwise product weight. -/
private theorem keyedDecaySquared_mul_cost_eq
    {m : ℕ} (hm : 0 < m) (b : ℕ) (i : Fin m) :
    r324KeyedDecaySquared hm b *
        SmoothCutoff.r324GroupedIncrementCost hm b i =
      ∏ j : Fin m,
        r324KeyedSlotWeight i j
          (SmoothCutoff.r324NatEquivStandardConfigurations hm b j) := by
  unfold r324KeyedDecaySquared r324KeyedSlotWeight
  exact prod_sq_mul_slot_eq
    (fun j =>
      eighthOrderFrequencyDecay
        ‖z4EuclideanFrequency
          (SmoothCutoff.r324NatEquivStandardConfigurations hm b j)‖)
    (SmoothCutoff.r324GroupedIncrementCost hm b i) i
    (SmoothCutoff.r324GroupedIncrementCost_mul_decay hm b i)

/-- The keyed slot series is summable. -/
theorem summable_keyedDecaySquared_mul_cost
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    Summable fun b : ℕ =>
      r324KeyedDecaySquared hm b *
        SmoothCutoff.r324GroupedIncrementCost hm b i := by
  have hG : Summable fun q : Fin m → Z4 =>
      ∏ j : Fin m, r324KeyedSlotWeight i j (q j) :=
    summable_realSlotProduct m (fun j => r324KeyedSlotWeight i j)
      (fun j k => r324KeyedSlotWeight_nonneg i j k)
      (fun j => summable_r324KeyedSlotWeight i j)
  refine
    (((SmoothCutoff.r324NatEquivStandardConfigurations
      hm).summable_iff.mpr hG).congr fun b => ?_)
  exact (keyedDecaySquared_mul_cost_eq hm b i).symm

/-- **The keyed slot budget**: the complete keyed slot series is at most
`4096^m`. -/
theorem tsum_keyedDecaySquared_mul_cost_le
    {m : ℕ} (hm : 0 < m) (i : Fin m) :
    (∑' b : ℕ,
      r324KeyedDecaySquared hm b *
        SmoothCutoff.r324GroupedIncrementCost hm b i) ≤ 4096 ^ m := by
  calc
    (∑' b : ℕ,
        r324KeyedDecaySquared hm b *
          SmoothCutoff.r324GroupedIncrementCost hm b i) =
        ∑' b : ℕ,
          ∏ j : Fin m,
            r324KeyedSlotWeight i j
              (SmoothCutoff.r324NatEquivStandardConfigurations
                hm b j) :=
      tsum_congr fun b => keyedDecaySquared_mul_cost_eq hm b i
    _ = ∑' q : Fin m → Z4,
          ∏ j : Fin m, r324KeyedSlotWeight i j (q j) :=
      (SmoothCutoff.r324NatEquivStandardConfigurations hm).tsum_eq
        (fun q : Fin m → Z4 =>
          ∏ j : Fin m, r324KeyedSlotWeight i j (q j))
    _ = ∏ j : Fin m, ∑' k : Z4, r324KeyedSlotWeight i j k :=
      tsum_realSlotProduct m (fun j => r324KeyedSlotWeight i j)
        (fun j k => r324KeyedSlotWeight_nonneg i j k)
        (fun j => summable_r324KeyedSlotWeight i j)
    _ ≤ ∏ _j : Fin m, (4096 : ℝ) :=
      Finset.prod_le_prod
        (fun j _ => tsum_nonneg fun k =>
          r324KeyedSlotWeight_nonneg i j k)
        (fun j _ => tsum_r324KeyedSlotWeight_le i j)
    _ = 4096 ^ m := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## Discharge of the residual slot budget -/

/-- **The keyed interior bound discharges the residual slot budget.**
The schedule count pays `16^{2m}`, the keyed slot sums pay `4096^m =
64^{2m}`, and the marked `|log ε|` closes `|log ε|^{m-1}` to
`|log ε|^m`; the budget constant is `1024·A`. -/
theorem r324SlotLogBudget_of_keyedCoreL1DecayBound
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) {ε A : ℝ}
    (hε : 0 < ε) (hlog : 1 ≤ |Real.log ε|) (hA : 0 ≤ A)
    (hkeyed : R324KeyedCoreL1DecayBound ρ hm ε A) :
    R324SlotLogBudget ρ hm ε (1024 * A) := by
  intro i
  set L : ℝ := |Real.log ε| with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hlog
  set c : ℝ := A ^ (2 * m) * L ^ (m - 1) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hslot := summable_keyedDecaySquared_mul_cost hm i
  have hslot_le := tsum_keyedDecaySquared_mul_cost_le hm i
  have hslot0 : 0 ≤ ∑' b : ℕ,
      r324KeyedDecaySquared hm b *
        SmoothCutoff.r324GroupedIncrementCost hm b i :=
    tsum_nonneg fun b => mul_nonneg
      (r324KeyedDecaySquared_nonneg hm b)
      (SmoothCutoff.r324GroupedIncrementCost_pos hm b i).le
  have hfsum : Summable fun p : R324RefinedScheduleIndex m × ℕ =>
      r324KeyedDecaySquared hm p.2 *
        SmoothCutoff.r324GroupedIncrementCost hm p.2 i := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg
      (r324KeyedDecaySquared_nonneg hm p.2)
      (SmoothCutoff.r324GroupedIncrementCost_pos hm p.2 i).le)]
    exact ⟨fun _ => hslot, Summable.of_finite⟩
  have hmaj : Summable fun p : R324RefinedScheduleIndex m × ℕ =>
      c * (r324KeyedDecaySquared hm p.2 *
        SmoothCutoff.r324GroupedIncrementCost hm p.2 i) :=
    hfsum.mul_left c
  have hLHS := summable_groupedCoreL1_mul_cost ρ hm hε hlog i
  have hle : ∀ p : R324RefinedScheduleIndex m × ℕ,
      ρ.r324GroupedRefinedCoreL1 hm ε p *
          SmoothCutoff.r324GroupedIncrementCost hm p.2 i ≤
        c * (r324KeyedDecaySquared hm p.2 *
          SmoothCutoff.r324GroupedIncrementCost hm p.2 i) := by
    intro p
    have hstep := mul_le_mul_of_nonneg_right (hkeyed p)
      (SmoothCutoff.r324GroupedIncrementCost_pos hm p.2 i).le
    calc
      ρ.r324GroupedRefinedCoreL1 hm ε p *
          SmoothCutoff.r324GroupedIncrementCost hm p.2 i ≤
          A ^ (2 * m) * L ^ (m - 1) *
            r324KeyedDecaySquared hm p.2 *
            SmoothCutoff.r324GroupedIncrementCost hm p.2 i :=
        hstep
      _ = c * (r324KeyedDecaySquared hm p.2 *
            SmoothCutoff.r324GroupedIncrementCost hm p.2 i) := by
        rw [hcdef]
        ring
  have hT :
      (∑' p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324GroupedRefinedCoreL1 hm ε p *
          SmoothCutoff.r324GroupedIncrementCost hm p.2 i) ≤
        ∑' p : R324RefinedScheduleIndex m × ℕ,
          c * (r324KeyedDecaySquared hm p.2 *
            SmoothCutoff.r324GroupedIncrementCost hm p.2 i) :=
    hLHS.tsum_le_tsum hle hmaj
  have hprod :
      (∑' p : R324RefinedScheduleIndex m × ℕ,
        c * (r324KeyedDecaySquared hm p.2 *
          SmoothCutoff.r324GroupedIncrementCost hm p.2 i)) =
        c * ((Fintype.card (R324RefinedScheduleIndex m) : ℝ) *
          ∑' b : ℕ,
            r324KeyedDecaySquared hm b *
              SmoothCutoff.r324GroupedIncrementCost hm b i) := by
    rw [tsum_mul_left]
    congr 1
    calc
      (∑' p : R324RefinedScheduleIndex m × ℕ,
          r324KeyedDecaySquared hm p.2 *
            SmoothCutoff.r324GroupedIncrementCost hm p.2 i) =
          ∑' a : R324RefinedScheduleIndex m, ∑' b : ℕ,
            r324KeyedDecaySquared hm b *
              SmoothCutoff.r324GroupedIncrementCost hm b i :=
        hfsum.tsum_prod' fun _ => hslot
      _ = ∑ _a : R324RefinedScheduleIndex m, ∑' b : ℕ,
            r324KeyedDecaySquared hm b *
              SmoothCutoff.r324GroupedIncrementCost hm b i :=
        tsum_fintype _
      _ = (Fintype.card (R324RefinedScheduleIndex m) : ℝ) *
            ∑' b : ℕ,
              r324KeyedDecaySquared hm b *
                SmoothCutoff.r324GroupedIncrementCost hm b i := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcardR :
      ((Fintype.card (R324RefinedScheduleIndex m) : ℝ)) ≤
        (16 : ℝ) ^ (2 * m) := by
    exact_mod_cast card_r324RefinedScheduleIndex_le m
  have hKle :
      (Fintype.card (R324RefinedScheduleIndex m) : ℝ) *
          (∑' b : ℕ,
            r324KeyedDecaySquared hm b *
              SmoothCutoff.r324GroupedIncrementCost hm b i) ≤
        (16 : ℝ) ^ (2 * m) * 4096 ^ m :=
    mul_le_mul hcardR hslot_le hslot0 (by positivity)
  have hLm : L ^ (m - 1) * L = L ^ m := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  have hfinal :
      L * (c * ((16 : ℝ) ^ (2 * m) * 4096 ^ m)) =
        (1024 * A) ^ (2 * m) * L ^ m := by
    rw [hcdef, show (4096 : ℝ) ^ m = 64 ^ (2 * m) by
        rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, ← pow_mul],
      mul_pow, show (1024 : ℝ) = 16 * 64 by norm_num,
      mul_pow, ← hLm]
    ring
  calc
    L * (∑' p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324GroupedRefinedCoreL1 hm ε p *
          SmoothCutoff.r324GroupedIncrementCost hm p.2 i) ≤
        L * (c * ((Fintype.card (R324RefinedScheduleIndex m) : ℝ) *
          ∑' b : ℕ,
            r324KeyedDecaySquared hm b *
              SmoothCutoff.r324GroupedIncrementCost hm b i)) :=
      mul_le_mul_of_nonneg_left (hT.trans_eq hprod) hL0.le
    _ ≤ L * (c * ((16 : ℝ) ^ (2 * m) * 4096 ^ m)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hKle hc0) hL0.le
    _ = (1024 * A) ^ (2 * m) * L ^ m := hfinal

/-! ## Capstone instantiations -/

/-- **The R-324 deterministic moment paper bound from the keyed
interior bound alone.**  Every ingredient of the slot budget other than
`R324KeyedCoreL1DecayBound` — the schedule count, the keyed slot sums,
the `|log ε|` ledger, the interior-core comparison, and the full
majorant assembly — is discharged unconditionally. -/
theorem exists_deterministicMoment_paper_bound_of_keyedDecay
    {A : ℝ} (hA : 0 < A) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
        (hm : 0 < m) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        m ≤ truncOrder ε →
        R324KeyedCoreL1DecayBound ρ hm ε A →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (65536 * A) lam ε m α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_slotBudget
      (primitiveConstant := 1024 * A) (by positivity)
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc hkeyed
  have hbound :=
    h ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
      (r324SlotLogBudget_of_keyedCoreL1DecayBound ρ hm hε hlog
        hA.le hkeyed)
  rwa [show (64 : ℝ) * (1024 * A) = 65536 * A by ring] at hbound

/-- Literal decay form of the keyed estimate: the `min` bracket is
bounded by the P-3.5b-det decay
`ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε²(α+β)⟩⁻⁸`. -/
theorem exists_deterministicMoment_decay_bound_of_keyedDecay
    {A : ℝ} (hA : 0 < A) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
        (hm : 0 < m) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        m ≤ truncOrder ε →
        R324KeyedCoreL1DecayBound ρ hm ε A →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * outerConstant *
            ((65536 * A) * lam) ^ (2 * m - 2) *
            paperDeterministicMomentDecay ε α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_decay_bound_of_slotBudget
      (primitiveConstant := 1024 * A) (by positivity)
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc hkeyed
  have hbound :=
    h ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
      (r324SlotLogBudget_of_keyedCoreL1DecayBound ρ hm hε hlog
        hA.le hkeyed)
  rwa [show (64 : ℝ) * (1024 * A) = 65536 * A by ring] at hbound

end

end Anderson4D
