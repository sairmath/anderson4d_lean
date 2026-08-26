import Anderson4D.DetParametrix.Paper42_Moment.R324KeyedPrimitiveCollapse

/-!
# The total-mass discharge of the R-324 residual slot budget

`R324KeyedPrimitiveCollapse` proves that the *per-key* interface
`R324KeyedCoreL1DecayBound` is intrinsically `ε`-divergent: at `m = 1`
the grouped mass of the key `k` is a fixed positive multiple of
`‖ρ̂(εk)‖²`, so a per-key eighth-order decay costs `ε⁻¹⁶` per constant
unit.  This file abandons per-key decay entirely and bounds the
*total* cost-weighted slot series by the exact fibre regrouping:

* the common-increment fibres partition the raw configurations, so the
  keyed slot series reassembles into the ungrouped raw mode series
  (`tsumByKey` fibration, no multiplicity loss);
* one reciprocal routed cost is dominated slotwise by the raw-mode
  bracket (`key ∈ {0, q, -q}`), and the raw series factorizes over the
  `m` frequency slots;
* each free slot pays the sharp scaled lattice mass
  `∑_k ‖ρ̂(εk)‖² ≲ ε⁻⁴` and the marked slot pays
  `∑_k ⟨k⟩⁸‖ρ̂(εk)‖² ≲ ε⁻¹²`, via the order-8 Schwartz bound and the
  block-decomposed scaled lattice sum `∑_{n∈ℤ}(1+δ|n|)⁻² ≤ 8/δ`.

The resulting ledger is `|log ε| · Σ ≤ E · U^m · ε^{-(4m+8)} · |log ε|`,
which yields `R324SlotLogBudget ρ hm ε (A₁ ε⁻⁶)`: the slot-budget
amplitude improves from the keyed `ε⁻¹⁶` to `ε⁻⁶` per constant unit.
The power `ε⁻⁶` is *sharp* for this norm-inside interface: at `m = 1`
the marked slot series is bounded below by a positive multiple of
`∑_k ⟨k⟩⁸‖ρ̂(εk)‖² ≍ ε⁻¹²` (the `m = 1` identity of the keyed-collapse
header), and the budget shape `C^{2m}|log ε|^m` forces `C ≳ ε⁻⁶` there.
The paper-scale amplitude (`ε`-uniform `C`) is therefore
unreachable through `R324SlotLogBudget` as stated; this file delivers
the strongest `ε`-power version, and the capstone instantiation
carries the amplitude `64 · A₁ · ε⁻⁶`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## One-dimensional lattice sums -/

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

/-! ## Scaled one-dimensional lattice sums -/

/-- The scaled quadratic weight is summable on `ℕ`. -/
private theorem summable_nat_scaledInvSq {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Summable fun n : ℕ => ((1 + δ * (n : ℝ)) ^ 2)⁻¹ := by
  refine (summable_inv_succ_sq.mul_left (δ ^ 2)⁻¹).of_nonneg_of_le
    (fun n => by positivity) (fun n => ?_)
  have hbase : δ * ((n : ℝ) + 1) ≤ 1 + δ * (n : ℝ) := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hsq : δ ^ 2 * ((n : ℝ) + 1) ^ 2 ≤ (1 + δ * (n : ℝ)) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hbase 2
    calc δ ^ 2 * ((n : ℝ) + 1) ^ 2 = (δ * ((n : ℝ) + 1)) ^ 2 := by ring
      _ ≤ (1 + δ * (n : ℝ)) ^ 2 := this
  calc
    ((1 + δ * (n : ℝ)) ^ 2)⁻¹ ≤
        (δ ^ 2 * ((n : ℝ) + 1) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) hsq
    _ = (δ ^ 2)⁻¹ * (((n : ℝ) + 1) ^ 2)⁻¹ := by
      rw [mul_inv]

/-- **Scaled block bound**: `∑_{n ∈ ℕ} (1+δn)⁻² ≤ 4/δ` for `0 < δ ≤ 1`,
by cutting `ℕ` into blocks of length `⌈δ⁻¹⌉`. -/
private theorem tsum_nat_scaledInvSq_le {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑' n : ℕ, ((1 + δ * (n : ℝ)) ^ 2)⁻¹) ≤ 4 / δ := by
  set M : ℕ := ⌈δ⁻¹⌉₊ with hMdef
  have hδinv : (0 : ℝ) < δ⁻¹ := by positivity
  have hM1 : 1 ≤ M := Nat.one_le_ceil_iff.mpr hδinv
  haveI : NeZero M := ⟨by omega⟩
  have hMδ : 1 ≤ δ * (M : ℝ) := by
    have hceil : δ⁻¹ ≤ (M : ℝ) := Nat.le_ceil δ⁻¹
    calc (1 : ℝ) = δ * δ⁻¹ := by field_simp
      _ ≤ δ * (M : ℝ) := by nlinarith
  have hMle : (M : ℝ) ≤ 2 / δ := by
    have hlt : (M : ℝ) < δ⁻¹ + 1 := Nat.ceil_lt_add_one hδinv.le
    have h1 : (1 : ℝ) ≤ δ⁻¹ := by
      rw [le_inv_comm₀ one_pos hδ0]
      simpa using hδ1
    rw [div_eq_mul_inv]
    nlinarith
  have hsum := summable_nat_scaledInvSq (δ := δ) hδ0 hδ1
  have hmaj : Summable fun p : ℕ × Fin M =>
      (((p.1 : ℝ) + 1) ^ 2)⁻¹ := by
    rw [summable_prod_of_nonneg (fun p => by positivity)]
    exact ⟨fun _ => Summable.of_finite, by
      simpa [tsum_fintype] using
        summable_inv_succ_sq.mul_left (M : ℝ)⟩
  have hpoint : ∀ p : ℕ × Fin M,
      ((1 + δ * (((Nat.divModEquiv M).symm p : ℕ) : ℝ)) ^ 2)⁻¹ ≤
        (((p.1 : ℝ) + 1) ^ 2)⁻¹ := by
    intro p
    have hval : ((Nat.divModEquiv M).symm p : ℕ) =
        p.1 * M + (p.2 : ℕ) := by
      simp [Nat.divModEquiv]
    have hlow : (p.1 : ℝ) + 1 ≤
        1 + δ * (((Nat.divModEquiv M).symm p : ℕ) : ℝ) := by
      rw [hval]
      push_cast
      have h2 : (0 : ℝ) ≤ (p.2 : ℕ) := Nat.cast_nonneg _
      have h1 : (0 : ℝ) ≤ (p.1 : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h0 : (0 : ℝ) < (p.1 : ℝ) + 1 := by positivity
    exact inv_anti₀ (by positivity)
      (pow_le_pow_left₀ h0.le hlow 2)
  have hequiv :
      (∑' n : ℕ, ((1 + δ * (n : ℝ)) ^ 2)⁻¹) =
        ∑' p : ℕ × Fin M,
          ((1 + δ * (((Nat.divModEquiv M).symm p : ℕ) : ℝ)) ^ 2)⁻¹ :=
    ((Nat.divModEquiv M).symm.tsum_eq
      (fun n : ℕ => ((1 + δ * (n : ℝ)) ^ 2)⁻¹)).symm
  rw [hequiv]
  have hstep :
      (∑' p : ℕ × Fin M,
        ((1 + δ * (((Nat.divModEquiv M).symm p : ℕ) : ℝ)) ^ 2)⁻¹) ≤
        ∑' p : ℕ × Fin M, (((p.1 : ℝ) + 1) ^ 2)⁻¹ := by
    refine Summable.tsum_le_tsum hpoint ?_ hmaj
    exact ((Nat.divModEquiv M).symm.summable_iff).mpr hsum
  refine hstep.trans ?_
  have hprod :
      (∑' p : ℕ × Fin M, (((p.1 : ℝ) + 1) ^ 2)⁻¹) =
        (M : ℝ) * ∑' n : ℕ, (((n : ℝ) + 1) ^ 2)⁻¹ := by
    rw [hmaj.tsum_prod' fun q => Summable.of_finite]
    rw [← tsum_mul_left]
    exact tsum_congr fun q => by
      rw [tsum_fintype]
      simp [Finset.card_univ]
  rw [hprod]
  calc
    (M : ℝ) * ∑' n : ℕ, (((n : ℝ) + 1) ^ 2)⁻¹ ≤ (M : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left tsum_inv_succ_sq_le
        (Nat.cast_nonneg _)
    _ ≤ 2 / δ * 2 := by nlinarith
    _ = 4 / δ := by ring

/-- Negative-branch identification for the scaled coordinate weight. -/
private theorem scaledIntWeight_neg_eq {δ : ℝ} (n : ℕ) :
    ((1 + δ * ((Int.natAbs (-((n : ℤ) + 1)) : ℕ) : ℝ)) ^ 2)⁻¹ =
      ((1 + δ * ((n + 1 : ℕ) : ℝ)) ^ 2)⁻¹ := by
  rw [show -((n : ℤ) + 1) = Int.negSucc n by omega,
    Int.natAbs_negSucc]

/-- The scaled coordinate weight is summable over `ℤ`. -/
private theorem summable_int_scaledInvSq {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Summable fun n : ℤ => ((1 + δ * ((n.natAbs : ℕ) : ℝ)) ^ 2)⁻¹ := by
  refine Summable.of_nat_of_neg_add_one
    (f := fun n : ℤ => ((1 + δ * ((n.natAbs : ℕ) : ℝ)) ^ 2)⁻¹) ?_ ?_
  · simpa using summable_nat_scaledInvSq hδ0 hδ1
  · have hshift :
        Summable fun n : ℕ =>
          ((1 + δ * ((n + 1 : ℕ) : ℝ)) ^ 2)⁻¹ :=
      (summable_nat_scaledInvSq hδ0 hδ1).comp_injective
        Nat.succ_injective
    exact hshift.congr fun n => (scaledIntWeight_neg_eq n).symm

/-- **Scaled two-sided coordinate bound**:
`∑_{n ∈ ℤ} (1+δ|n|)⁻² ≤ 8/δ` for `0 < δ ≤ 1`. -/
private theorem tsum_int_scaledInvSq_le {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑' n : ℤ, ((1 + δ * ((n.natAbs : ℕ) : ℝ)) ^ 2)⁻¹) ≤ 8 / δ := by
  have hs1 : Summable fun n : ℕ =>
      ((1 + δ * (((n : ℤ).natAbs : ℕ) : ℝ)) ^ 2)⁻¹ := by
    simpa using summable_nat_scaledInvSq hδ0 hδ1
  have hs2 : Summable fun n : ℕ =>
      ((1 + δ * ((Int.natAbs (-((n : ℤ) + 1)) : ℕ) : ℝ)) ^ 2)⁻¹ := by
    have hshift :
        Summable fun n : ℕ =>
          ((1 + δ * ((n + 1 : ℕ) : ℝ)) ^ 2)⁻¹ :=
      (summable_nat_scaledInvSq hδ0 hδ1).comp_injective
        Nat.succ_injective
    exact hshift.congr fun n => (scaledIntWeight_neg_eq n).symm
  have hsplit :=
    tsum_of_nat_of_neg_add_one
      (f := fun n : ℤ => ((1 + δ * ((n.natAbs : ℕ) : ℝ)) ^ 2)⁻¹)
      hs1 hs2
  have h1 : (∑' n : ℕ,
      ((1 + δ * (((n : ℤ).natAbs : ℕ) : ℝ)) ^ 2)⁻¹) ≤ 4 / δ := by
    calc
      (∑' n : ℕ, ((1 + δ * (((n : ℤ).natAbs : ℕ) : ℝ)) ^ 2)⁻¹) =
          ∑' n : ℕ, ((1 + δ * (n : ℝ)) ^ 2)⁻¹ :=
        tsum_congr fun n => by simp
      _ ≤ 4 / δ := tsum_nat_scaledInvSq_le hδ0 hδ1
  have h2 : (∑' n : ℕ,
      ((1 + δ * ((Int.natAbs (-((n : ℤ) + 1)) : ℕ) : ℝ)) ^ 2)⁻¹) ≤
        4 / δ := by
    have hterm : ∀ n : ℕ,
        ((1 + δ * ((Int.natAbs (-((n : ℤ) + 1)) : ℕ) : ℝ)) ^ 2)⁻¹ ≤
          ((1 + δ * (n : ℝ)) ^ 2)⁻¹ := by
      intro n
      rw [scaledIntWeight_neg_eq n]
      have hstep : 1 + δ * (n : ℝ) ≤ 1 + δ * ((n + 1 : ℕ) : ℝ) := by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      exact inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by positivity) hstep 2)
    exact (hs2.tsum_le_tsum hterm
      (summable_nat_scaledInvSq hδ0 hδ1)).trans
      (tsum_nat_scaledInvSq_le hδ0 hδ1)
  rw [hsplit]
  have : (4 : ℝ) / δ + 4 / δ = 8 / δ := by ring
  linarith

/-! ## Slotwise product factorization -/

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

/-! ## The scaled lattice bracket sum on `ℤ⁴` -/

/-- Every coordinate is dominated by the Euclidean frequency norm. -/
private theorem abs_coord_le_norm_z4EuclideanFrequency
    (k : Z4) (i : Fin dim) :
    |((k i : ℤ) : ℝ)| ≤ ‖z4EuclideanFrequency k‖ := by
  have hsq : (((k i : ℤ) : ℝ)) ^ 2 ≤
      ‖z4EuclideanFrequency k‖ ^ 2 := by
    rw [norm_sq_z4EuclideanFrequency]
    unfold paperModeNormSq
    exact Finset.single_le_sum
      (f := fun j : Fin dim => (((k j : ℤ) : ℝ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs,
    Real.sqrt_sq (norm_nonneg _)] at h

/-- Slotwise domination of the scaled bracket by the coordinate
product weight. -/
private theorem scaledBracket_le_coordProduct {δ : ℝ}
    (hδ0 : 0 < δ) (k : Z4) :
    ((1 + δ * ‖z4EuclideanFrequency k‖) ^ 8)⁻¹ ≤
      ∏ i : Fin dim,
        ((1 + δ * (((k i).natAbs : ℕ) : ℝ)) ^ 2)⁻¹ := by
  have hcoord : ∀ i : Fin dim,
      (1 + δ * (((k i).natAbs : ℕ) : ℝ)) ^ 2 ≤
        (1 + δ * ‖z4EuclideanFrequency k‖) ^ 2 := by
    intro i
    have habs : (((k i).natAbs : ℕ) : ℝ) = |((k i : ℤ) : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hle : (((k i).natAbs : ℕ) : ℝ) ≤
        ‖z4EuclideanFrequency k‖ := by
      rw [habs]
      exact abs_coord_le_norm_z4EuclideanFrequency k i
    have hstep : 1 + δ * (((k i).natAbs : ℕ) : ℝ) ≤
        1 + δ * ‖z4EuclideanFrequency k‖ := by
      nlinarith
    exact pow_le_pow_left₀ (by positivity) hstep 2
  have hprod :
      (∏ i : Fin dim,
        (1 + δ * (((k i).natAbs : ℕ) : ℝ)) ^ 2) ≤
        (1 + δ * ‖z4EuclideanFrequency k‖) ^ 8 := by
    calc
      (∏ i : Fin dim,
          (1 + δ * (((k i).natAbs : ℕ) : ℝ)) ^ 2) ≤
          ∏ _i : Fin dim,
            (1 + δ * ‖z4EuclideanFrequency k‖) ^ 2 :=
        Finset.prod_le_prod (fun i _ => by positivity)
          (fun i _ => hcoord i)
      _ = (1 + δ * ‖z4EuclideanFrequency k‖) ^ 8 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← pow_mul]
        norm_num [dim]
  have hPpos :
      (0 : ℝ) < ∏ i : Fin dim,
        (1 + δ * (((k i).natAbs : ℕ) : ℝ)) ^ 2 :=
    Finset.prod_pos fun i _ => by positivity
  calc
    ((1 + δ * ‖z4EuclideanFrequency k‖) ^ 8)⁻¹ ≤
        (∏ i : Fin dim,
          (1 + δ * (((k i).natAbs : ℕ) : ℝ)) ^ 2)⁻¹ :=
      inv_anti₀ hPpos hprod
    _ = ∏ i : Fin dim,
          ((1 + δ * (((k i).natAbs : ℕ) : ℝ)) ^ 2)⁻¹ := by
      rw [← Finset.prod_inv_distrib]

/-- The scaled coordinate product weight is summable on `ℤ⁴`. -/
private theorem summable_coordProduct {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Summable fun k : Z4 =>
      ∏ i : Fin dim,
        ((1 + δ * (((k i).natAbs : ℕ) : ℝ)) ^ 2)⁻¹ :=
  summable_realSlotProduct (A := ℤ) dim
    (fun _ n => ((1 + δ * ((n.natAbs : ℕ) : ℝ)) ^ 2)⁻¹)
    (fun _ a => by positivity)
    (fun _ => summable_int_scaledInvSq hδ0 hδ1)

/-- The scaled bracket is summable on `ℤ⁴`. -/
private theorem summable_scaledBracket {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Summable fun k : Z4 =>
      ((1 + δ * ‖z4EuclideanFrequency k‖) ^ 8)⁻¹ :=
  (summable_coordProduct hδ0 hδ1).of_nonneg_of_le
    (fun k => by positivity)
    (fun k => scaledBracket_le_coordProduct hδ0 k)

/-- **Scaled lattice bracket bound**:
`∑_{k ∈ ℤ⁴} (1+δ‖k‖)⁻⁸ ≤ 4096/δ⁴` for `0 < δ ≤ 1`. -/
private theorem tsum_scaledBracket_le {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑' k : Z4,
      ((1 + δ * ‖z4EuclideanFrequency k‖) ^ 8)⁻¹) ≤
      4096 / δ ^ 4 := by
  have hδ4 : (0 : ℝ) < δ ^ 4 := by positivity
  calc
    (∑' k : Z4,
        ((1 + δ * ‖z4EuclideanFrequency k‖) ^ 8)⁻¹) ≤
        ∑' k : Z4,
          ∏ i : Fin dim,
            ((1 + δ * (((k i).natAbs : ℕ) : ℝ)) ^ 2)⁻¹ :=
      (summable_scaledBracket hδ0 hδ1).tsum_le_tsum
        (fun k => scaledBracket_le_coordProduct hδ0 k)
        (summable_coordProduct hδ0 hδ1)
    _ = ∏ _i : Fin dim,
          ∑' n : ℤ, ((1 + δ * ((n.natAbs : ℕ) : ℝ)) ^ 2)⁻¹ :=
      tsum_realSlotProduct (A := ℤ) dim
        (fun _ n => ((1 + δ * ((n.natAbs : ℕ) : ℝ)) ^ 2)⁻¹)
        (fun _ a => by positivity)
        (fun _ => summable_int_scaledInvSq hδ0 hδ1)
    _ ≤ ∏ _i : Fin dim, (8 / δ) :=
      Finset.prod_le_prod
        (fun _ _ => tsum_nonneg fun n => by positivity)
        (fun _ _ => tsum_int_scaledInvSq_le hδ0 hδ1)
    _ = 4096 / δ ^ 4 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        div_pow]
      norm_num

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## The order-8 covariance symbol bound -/

/-- The Euclidean frequency of the dilated lattice mode is the dilated
Euclidean frequency of the mode, up to the `2π` normalization. -/
private theorem euclideanFrequency_eps_mode (ε : ℝ) (k : Z4) :
    euclideanFrequency (fun i => ε * (k i : ℝ)) =
      (ε / (2 * Real.pi)) • z4EuclideanFrequency k := by
  apply PiLp.ext
  intro i
  simp [euclideanFrequency, z4EuclideanFrequency]
  ring

/-- Norm form of the preceding frequency identity. -/
private theorem norm_euclideanFrequency_eps_mode
    {ε : ℝ} (hε : 0 < ε) (k : Z4) :
    ‖euclideanFrequency (fun i => ε * (k i : ℝ))‖ =
      ε / (2 * Real.pi) * ‖z4EuclideanFrequency k‖ := by
  rw [euclideanFrequency_eps_mode, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-- The covariance coefficient norm is the squared symbol norm at the
white-noise Fourier scale. -/
private theorem norm_covarianceModeCoeff_eq (ε : ℝ) (k : Z4) :
    ‖ρ.covarianceModeCoeff ε k‖ =
      NoiseModel.whiteNoiseFourierScale ^ 2 *
        ‖ρ.symbol ε k‖ ^ 2 := by
  unfold covarianceModeCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _), norm_pow, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos NoiseModel.whiteNoiseFourierScale_pos]

/-- **Order-8 scaled symbol bound.**  Every covariance Fourier
coefficient is dominated by `C (1 + δ‖k‖)⁻¹⁶` with `δ = ε/(2π)` and an
`ε`-uniform constant: the order-8 Schwartz bound, squared. -/
theorem exists_covarianceModeCoeff_order8_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ k : Z4,
        ‖ρ.covarianceModeCoeff ε k‖ ≤
          C * (((1 + ε / (2 * Real.pi) *
            ‖z4EuclideanFrequency k‖) ^ 16)⁻¹) := by
  obtain ⟨C₈, hC₈, hbound⟩ :=
    ρ.exists_fourierR4_one_add_norm_bound_nat 8
  set S : ℝ := NoiseModel.whiteNoiseFourierScale with hSdef
  have hS : 0 < S := NoiseModel.whiteNoiseFourierScale_pos
  refine ⟨S ^ 2 * C₈ ^ 2, by positivity, ?_⟩
  intro ε hε k
  set x : ℝ := ‖z4EuclideanFrequency k‖ with hxdef
  set δ : ℝ := ε / (2 * Real.pi) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hbase : (0 : ℝ) < 1 + δ * x := by
    have hx : 0 ≤ x := norm_nonneg _
    positivity
  have hsym : (1 + δ * x) ^ (8 : ℕ) * ‖ρ.symbol ε k‖ ≤ C₈ := by
    have h := hbound (fun i => ε * (k i : ℝ))
    rw [norm_euclideanFrequency_eps_mode hε k, ← hxdef,
      ← hδdef] at h
    exact h
  have hsymsq :
      (1 + δ * x) ^ (16 : ℕ) * ‖ρ.symbol ε k‖ ^ 2 ≤ C₈ ^ 2 := by
    have hnn : 0 ≤ (1 + δ * x) ^ (8 : ℕ) * ‖ρ.symbol ε k‖ :=
      mul_nonneg (by positivity) (norm_nonneg _)
    have hpow := pow_le_pow_left₀ hnn hsym 2
    calc
      (1 + δ * x) ^ (16 : ℕ) * ‖ρ.symbol ε k‖ ^ 2 =
          ((1 + δ * x) ^ (8 : ℕ) * ‖ρ.symbol ε k‖) ^ 2 := by
        ring
      _ ≤ C₈ ^ 2 := hpow
  rw [ρ.norm_covarianceModeCoeff_eq, ← hSdef]
  have h16 : (0 : ℝ) < (1 + δ * x) ^ (16 : ℕ) := by positivity
  have hfin : ‖ρ.symbol ε k‖ ^ 2 ≤
      C₈ ^ 2 / (1 + δ * x) ^ (16 : ℕ) :=
    (le_div_iff₀' h16).mpr hsymsq
  calc
    S ^ 2 * ‖ρ.symbol ε k‖ ^ 2 ≤
        S ^ 2 * (C₈ ^ 2 / (1 + δ * x) ^ (16 : ℕ)) :=
      mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = S ^ 2 * C₈ ^ 2 * (((1 + δ * x) ^ 16)⁻¹) := by
      rw [div_eq_mul_inv]
      ring

/-! ## The total-mass slot weight -/

/-- Slot weight of the total-mass ledger: one covariance coefficient
norm, carrying the reciprocal routed cost at the marked slot only. -/
private def r324TotalSlotWeight (ε : ℝ) {m : ℕ}
    (i j : Fin m) (k : Z4) : ℝ :=
  ‖ρ.covarianceModeCoeff ε k‖ *
    (if j = i then
      (1 + ‖z4EuclideanFrequency k‖ ^ 2) ^ 4 else 1)

private theorem r324TotalSlotWeight_nonneg (ε : ℝ) {m : ℕ}
    (i j : Fin m) (k : Z4) :
    0 ≤ ρ.r324TotalSlotWeight ε i j k := by
  unfold r324TotalSlotWeight
  refine mul_nonneg (norm_nonneg _) ?_
  split
  · positivity
  · norm_num

/-- Pointwise scaled-bracket domination of the slot weight. -/
private theorem r324TotalSlotWeight_le {C ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcoeff : ∀ k : Z4,
      ‖ρ.covarianceModeCoeff ε k‖ ≤
        C * (((1 + ε / (2 * Real.pi) *
          ‖z4EuclideanFrequency k‖) ^ 16)⁻¹))
    {m : ℕ} (i j : Fin m) (k : Z4) :
    ρ.r324TotalSlotWeight ε i j k ≤
      C * (if j = i then (ε / (2 * Real.pi))⁻¹ ^ 8 else 1) *
        ((1 + ε / (2 * Real.pi) *
          ‖z4EuclideanFrequency k‖) ^ 8)⁻¹ := by
  have hC0 : 0 ≤ C := by
    have h := (hcoeff 0).trans' (norm_nonneg _)
    have hpos : (0 : ℝ) <
        ((1 + ε / (2 * Real.pi) *
          ‖z4EuclideanFrequency (0 : Z4)‖) ^ 16)⁻¹ := by
      have : (0 : ℝ) ≤ ‖z4EuclideanFrequency (0 : Z4)‖ :=
        norm_nonneg _
      positivity
    nlinarith
  set x : ℝ := ‖z4EuclideanFrequency k‖ with hxdef
  have hx : 0 ≤ x := norm_nonneg _
  set δ : ℝ := ε / (2 * Real.pi) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hb0 : (0 : ℝ) < 1 + δ * x := by positivity
  have hcov := hcoeff k
  rw [← hxdef] at hcov
  unfold r324TotalSlotWeight
  rcases eq_or_ne j i with hji | hji
  · rw [if_pos hji, if_pos hji]
    have hcost : (1 + x ^ 2) ^ 4 ≤ δ⁻¹ ^ 8 * (1 + δ * x) ^ 8 := by
      have h1 : 1 + x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
      have h2 : (1 + x ^ 2) ^ 4 ≤ (1 + x) ^ 8 := by
        calc (1 + x ^ 2) ^ 4 ≤ ((1 + x) ^ 2) ^ 4 :=
              pow_le_pow_left₀ (by positivity) h1 4
          _ = (1 + x) ^ 8 := by rw [← pow_mul]
      have h3 : δ * (1 + x) ≤ 1 + δ * x := by nlinarith
      have h5 : δ ^ 8 * (1 + x) ^ 8 ≤ (1 + δ * x) ^ 8 := by
        calc δ ^ 8 * (1 + x) ^ 8 = (δ * (1 + x)) ^ 8 := by ring
          _ ≤ (1 + δ * x) ^ 8 :=
            pow_le_pow_left₀ (by positivity) h3 8
      have hδ8 : (0 : ℝ) < δ ^ 8 := by positivity
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ hδ8]
      calc (1 + x ^ 2) ^ 4 * δ ^ 8 ≤ (1 + x) ^ 8 * δ ^ 8 :=
            mul_le_mul_of_nonneg_right h2 hδ8.le
        _ = δ ^ 8 * (1 + x) ^ 8 := by ring
        _ ≤ (1 + δ * x) ^ 8 := h5
    have hstep :
        ‖ρ.covarianceModeCoeff ε k‖ * (1 + x ^ 2) ^ 4 ≤
          (C * ((1 + δ * x) ^ 16)⁻¹) *
            (δ⁻¹ ^ 8 * (1 + δ * x) ^ 8) :=
      mul_le_mul hcov hcost (by positivity) (by positivity)
    refine hstep.trans_eq ?_
    have hAne : ((1 + δ * x) ^ 8 : ℝ) ≠ 0 := by positivity
    rw [show ((1 : ℝ) + δ * x) ^ 16 =
        (1 + δ * x) ^ 8 * (1 + δ * x) ^ 8 from by rw [← pow_add],
      mul_inv]
    field_simp
  · rw [if_neg hji, if_neg hji, mul_one, mul_one]
    have hb1 : (1 : ℝ) ≤ 1 + δ * x := by nlinarith
    have hmono : ((1 + δ * x) ^ 16)⁻¹ ≤ ((1 + δ * x) ^ 8)⁻¹ :=
      inv_anti₀ (by positivity)
        (pow_le_pow_right₀ hb1 (by omega))
    calc
      ‖ρ.covarianceModeCoeff ε k‖ ≤
          C * ((1 + δ * x) ^ 16)⁻¹ := hcov
      _ ≤ C * ((1 + δ * x) ^ 8)⁻¹ :=
        mul_le_mul_of_nonneg_left hmono hC0

private theorem summable_r324TotalSlotWeight {C ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcoeff : ∀ k : Z4,
      ‖ρ.covarianceModeCoeff ε k‖ ≤
        C * (((1 + ε / (2 * Real.pi) *
          ‖z4EuclideanFrequency k‖) ^ 16)⁻¹))
    {m : ℕ} (i j : Fin m) :
    Summable (ρ.r324TotalSlotWeight ε i j) := by
  have hδ0 : 0 < ε / (2 * Real.pi) := by positivity
  have hδ1 : ε / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  refine ((summable_scaledBracket hδ0 hδ1).mul_left
    (C * if j = i then (ε / (2 * Real.pi))⁻¹ ^ 8 else 1)
    ).of_nonneg_of_le
    (fun k => ρ.r324TotalSlotWeight_nonneg ε i j k)
    (fun k => ?_)
  exact ρ.r324TotalSlotWeight_le hε hε1 hcoeff i j k

/-- **Per-slot total mass**: `Uε⁻⁴` at a free slot, `Uε⁻¹²` at the
marked slot, with `U := C · 4096 · (2π)¹²`. -/
private theorem tsum_r324TotalSlotWeight_le {C ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcoeff : ∀ k : Z4,
      ‖ρ.covarianceModeCoeff ε k‖ ≤
        C * (((1 + ε / (2 * Real.pi) *
          ‖z4EuclideanFrequency k‖) ^ 16)⁻¹))
    {m : ℕ} (i j : Fin m) :
    (∑' k : Z4, ρ.r324TotalSlotWeight ε i j k) ≤
      C * 4096 * (2 * Real.pi) ^ 12 * ε⁻¹ ^ 4 *
        (if j = i then ε⁻¹ ^ 8 else 1) := by
  have hC0 : 0 ≤ C := by
    have h := (hcoeff 0).trans' (norm_nonneg _)
    have hpos : (0 : ℝ) <
        ((1 + ε / (2 * Real.pi) *
          ‖z4EuclideanFrequency (0 : Z4)‖) ^ 16)⁻¹ := by
      have : (0 : ℝ) ≤ ‖z4EuclideanFrequency (0 : Z4)‖ :=
        norm_nonneg _
      positivity
    nlinarith
  set δ : ℝ := ε / (2 * Real.pi) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hδinv : δ⁻¹ = 2 * Real.pi * ε⁻¹ := by
    rw [hδdef, inv_div, div_eq_mul_inv]
  have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hstep :
      (∑' k : Z4, ρ.r324TotalSlotWeight ε i j k) ≤
        (C * if j = i then δ⁻¹ ^ 8 else 1) * (4096 / δ ^ 4) := by
    calc
      (∑' k : Z4, ρ.r324TotalSlotWeight ε i j k) ≤
          ∑' k : Z4,
            (C * if j = i then δ⁻¹ ^ 8 else 1) *
              ((1 + δ * ‖z4EuclideanFrequency k‖) ^ 8)⁻¹ :=
        (ρ.summable_r324TotalSlotWeight hε hε1 hcoeff i j
          ).tsum_le_tsum
          (fun k => ρ.r324TotalSlotWeight_le hε hε1 hcoeff i j k)
          ((summable_scaledBracket hδ0 hδ1).mul_left _)
      _ = (C * if j = i then δ⁻¹ ^ 8 else 1) *
            ∑' k : Z4,
              ((1 + δ * ‖z4EuclideanFrequency k‖) ^ 8)⁻¹ :=
        tsum_mul_left
      _ ≤ (C * if j = i then δ⁻¹ ^ 8 else 1) * (4096 / δ ^ 4) := by
        refine mul_le_mul_of_nonneg_left
          (tsum_scaledBracket_le hδ0 hδ1) ?_
        refine mul_nonneg hC0 ?_
        split
        · positivity
        · norm_num
  refine hstep.trans ?_
  have h4 : (4096 : ℝ) / δ ^ 4 = 4096 * δ⁻¹ ^ 4 := by
    rw [div_eq_mul_inv, inv_pow]
  rcases eq_or_ne j i with hji | hji
  · rw [if_pos hji, if_pos hji, h4, hδinv]
    have hexp :
        C * ((2 * Real.pi) * ε⁻¹) ^ 8 *
            (4096 * ((2 * Real.pi) * ε⁻¹) ^ 4) =
          C * 4096 * (2 * Real.pi) ^ 12 * ε⁻¹ ^ 4 * ε⁻¹ ^ 8 := by
      ring
    exact le_of_eq hexp
  · rw [if_neg hji, if_neg hji, h4, hδinv, mul_one, mul_one]
    have hπpow : (2 * Real.pi) ^ 4 ≤ (2 * Real.pi) ^ 12 :=
      pow_le_pow_right₀ hπ1 (by omega)
    have hε4 : (0 : ℝ) ≤ ε⁻¹ ^ 4 := by positivity
    calc
      C * (4096 * ((2 * Real.pi) * ε⁻¹) ^ 4) =
          C * 4096 * (2 * Real.pi) ^ 4 * ε⁻¹ ^ 4 := by
        ring
      _ ≤ C * 4096 * (2 * Real.pi) ^ 12 * ε⁻¹ ^ 4 := by
        have hC4 : (0 : ℝ) ≤ C * 4096 := by positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hπpow hC4) hε4

/-! ## The slot modes of a raw refined configuration -/

/-- The standard slot modes of the `a`-th raw refined configuration. -/
private def r324KeyedRawSlotMode
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    Fin m → Z4 :=
  r324NatEquivStandardConfigurations hm
    ((r324NatEquivRefinedContractionConfigurations p a).2)

/-- The raw covariance weight is the slotwise product of coefficient
norms at the standard slot modes. -/
private theorem r324RefinedRawCovarianceWeight_eq_prod
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (a : ℕ) :
    ρ.r324RefinedRawCovarianceWeight hm ε p a =
      ∏ i : Fin m,
        ‖ρ.covarianceModeCoeff ε
          (r324KeyedRawSlotMode hm p a i)‖ := by
  unfold r324RefinedRawCovarianceWeight
    r324NatCovarianceConfigurationWeight
    r324CovarianceConfigurationWeight r324KeyedRawSlotMode
  set u := r324NatEquivRefinedContractionConfigurations p a
  set κ := momentContractionEquivFullPairing m u.1.1
  set q : Fin m → Z4 :=
    r324NatEquivStandardConfigurations hm u.2 with hqdef
  rw [← Equiv.prod_comp (r324FullPairIndexEquiv κ)
    (fun j =>
      ‖ρ.covarianceModeCoeff ε
        (r324FullConfigurationOfStandard κ q j)‖)]
  apply Finset.prod_congr rfl
  intro i _hi
  unfold r324FullConfigurationOfStandard
  rw [Function.comp_apply, Equiv.symm_apply_apply]

/-- The increment key of one slot is the slot mode, its negative, or
zero. -/
private theorem r324RefinedRawIncrementKey_cases
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ) (i : Fin m) :
    r324RefinedRawIncrementKey hm p a i = 0 ∨
      r324RefinedRawIncrementKey hm p a i =
        r324KeyedRawSlotMode hm p a i ∨
      r324RefinedRawIncrementKey hm p a i =
        -r324KeyedRawSlotMode hm p a i := by
  unfold r324RefinedRawIncrementKey
    r324NatCovarianceIncrementKey r324LeftPairModeContribution
    r324KeyedRawSlotMode
  set u := r324NatEquivRefinedContractionConfigurations p a
  set κ := momentContractionEquivFullPairing m u.1.1
  set q : Fin m → Z4 :=
    r324NatEquivStandardConfigurations hm u.2 with hqdef
  have hconfig :
      r324FullConfigurationOfStandard κ q
        (r324FullPairIndexEquiv κ i) = q i := by
    unfold r324FullConfigurationOfStandard
    rw [Function.comp_apply, Equiv.symm_apply_apply]
  dsimp only
  rw [hconfig]
  split_ifs with h1 h2 h2
  · left
    simp
  · right; right
    simp
  · right; left
    simp
  · left
    simp

/-- Cost comparison: the reciprocal routed cost of the increment key is
at most the cost of the raw slot mode. -/
private theorem r324KeyCost_le_modeCost
    {m : ℕ} (hm : 0 < m)
    (p : R324RefinedScheduleIndex m) (a : ℕ) (i : Fin m) :
    (1 + ‖z4EuclideanFrequency
        (r324RefinedRawIncrementKey hm p a i)‖ ^ 2) ^ 4 ≤
      (1 + ‖z4EuclideanFrequency
        (r324KeyedRawSlotMode hm p a i)‖ ^ 2) ^ 4 := by
  have hmode : (0 : ℝ) ≤
      ‖z4EuclideanFrequency (r324KeyedRawSlotMode hm p a i)‖ :=
    norm_nonneg _
  rcases r324RefinedRawIncrementKey_cases hm p a i with h | h | h
  · rw [h]
    have hzero : z4EuclideanFrequency (0 : Z4) = 0 :=
      map_zero z4EuclideanFrequencyAddHom
    rw [hzero, norm_zero]
    have h1 : (1 : ℝ) ≤ 1 +
        ‖z4EuclideanFrequency (r324KeyedRawSlotMode hm p a i)‖ ^ 2 := by
      nlinarith
    calc ((1 : ℝ) + 0 ^ 2) ^ 4 = 1 := by norm_num
      _ ≤ (1 + ‖z4EuclideanFrequency
            (r324KeyedRawSlotMode hm p a i)‖ ^ 2) ^ 4 :=
        one_le_pow₀ h1
  · rw [h]
  · rw [h]
    have hneg :
        z4EuclideanFrequency (-r324KeyedRawSlotMode hm p a i) =
          -z4EuclideanFrequency (r324KeyedRawSlotMode hm p a i) :=
      map_neg z4EuclideanFrequencyAddHom _
    rw [hneg, norm_neg]

/-- The raw covariance weight times the marked-slot mode cost is the
slotwise product of total slot weights. -/
private theorem rawWeight_mul_modeCost_eq_prod
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m) (a : ℕ) (i : Fin m) :
    ρ.r324RefinedRawCovarianceWeight hm ε p a *
        (1 + ‖z4EuclideanFrequency
          (r324KeyedRawSlotMode hm p a i)‖ ^ 2) ^ 4 =
      ∏ j : Fin m,
        ρ.r324TotalSlotWeight ε i j
          (r324KeyedRawSlotMode hm p a j) := by
  rw [ρ.r324RefinedRawCovarianceWeight_eq_prod hm ε p a]
  unfold r324TotalSlotWeight
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite_eq' Finset.univ i
    (fun j => (1 + ‖z4EuclideanFrequency
      (r324KeyedRawSlotMode hm p a j)‖ ^ 2) ^ 4)]
  simp

/-! ## The raw total slot mass -/

private theorem summable_rawWeight_mul_modeCost
    {m : ℕ} (hm : 0 < m) {C ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcoeff : ∀ k : Z4,
      ‖ρ.covarianceModeCoeff ε k‖ ≤
        C * (((1 + ε / (2 * Real.pi) *
          ‖z4EuclideanFrequency k‖) ^ 16)⁻¹))
    (p : R324RefinedScheduleIndex m) (i : Fin m) :
    Summable fun a : ℕ =>
      ρ.r324RefinedRawCovarianceWeight hm ε p a *
        (1 + ‖z4EuclideanFrequency
          (r324KeyedRawSlotMode hm p a i)‖ ^ 2) ^ 4 := by
  have hF : Summable fun q : Fin m → Z4 =>
      ∏ j, ρ.r324TotalSlotWeight ε i j (q j) :=
    summable_realSlotProduct m
      (fun j => ρ.r324TotalSlotWeight ε i j)
      (fun j k => ρ.r324TotalSlotWeight_nonneg ε i j k)
      (fun j => ρ.summable_r324TotalSlotWeight hε hε1 hcoeff i j)
  have hFnat : Summable fun c : ℕ =>
      ∏ j, ρ.r324TotalSlotWeight ε i j
        (r324NatEquivStandardConfigurations hm c j) :=
    ((r324NatEquivStandardConfigurations hm).summable_iff).mpr hF
  have hprod : Summable fun u : R324RefinedContractionIndex p × ℕ =>
      ∏ j, ρ.r324TotalSlotWeight ε i j
        (r324NatEquivStandardConfigurations hm u.2 j) := by
    rw [summable_prod_of_nonneg (fun u => Finset.prod_nonneg
      fun j _ => ρ.r324TotalSlotWeight_nonneg ε i j _)]
    exact ⟨fun _ => hFnat, Summable.of_finite⟩
  have hpre :=
    hprod.comp_injective
      (r324NatEquivRefinedContractionConfigurations p).injective
  exact hpre.congr fun a =>
    (ρ.rawWeight_mul_modeCost_eq_prod hm ε p a i).symm

/-- **Factorized raw total**: the contraction fibre pays its
cardinality, each free slot pays `Uε⁻⁴`, and the marked slot pays
`Uε⁻¹²`. -/
private theorem tsum_rawWeight_mul_modeCost_le
    {m : ℕ} (hm : 0 < m) {C ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcoeff : ∀ k : Z4,
      ‖ρ.covarianceModeCoeff ε k‖ ≤
        C * (((1 + ε / (2 * Real.pi) *
          ‖z4EuclideanFrequency k‖) ^ 16)⁻¹))
    (p : R324RefinedScheduleIndex m) (i : Fin m) :
    (∑' a : ℕ,
      ρ.r324RefinedRawCovarianceWeight hm ε p a *
        (1 + ‖z4EuclideanFrequency
          (r324KeyedRawSlotMode hm p a i)‖ ^ 2) ^ 4) ≤
      (Nat.card (R324RefinedContractionIndex p) : ℝ) *
        ((C * 4096 * (2 * Real.pi) ^ 12) ^ m *
          ε⁻¹ ^ (4 * m + 8)) := by
  have hC0 : 0 ≤ C := by
    have h := (hcoeff 0).trans' (norm_nonneg _)
    have hpos : (0 : ℝ) <
        ((1 + ε / (2 * Real.pi) *
          ‖z4EuclideanFrequency (0 : Z4)‖) ^ 16)⁻¹ := by
      have : (0 : ℝ) ≤ ‖z4EuclideanFrequency (0 : Z4)‖ :=
        norm_nonneg _
      positivity
    nlinarith
  set U : ℝ := C * 4096 * (2 * Real.pi) ^ 12 with hUdef
  have hU0 : 0 ≤ U := by positivity
  have hF : Summable fun q : Fin m → Z4 =>
      ∏ j, ρ.r324TotalSlotWeight ε i j (q j) :=
    summable_realSlotProduct m
      (fun j => ρ.r324TotalSlotWeight ε i j)
      (fun j k => ρ.r324TotalSlotWeight_nonneg ε i j k)
      (fun j => ρ.summable_r324TotalSlotWeight hε hε1 hcoeff i j)
  have hFnat : Summable fun c : ℕ =>
      ∏ j, ρ.r324TotalSlotWeight ε i j
        (r324NatEquivStandardConfigurations hm c j) :=
    ((r324NatEquivStandardConfigurations hm).summable_iff).mpr hF
  have hprod : Summable fun u : R324RefinedContractionIndex p × ℕ =>
      ∏ j, ρ.r324TotalSlotWeight ε i j
        (r324NatEquivStandardConfigurations hm u.2 j) := by
    rw [summable_prod_of_nonneg (fun u => Finset.prod_nonneg
      fun j _ => ρ.r324TotalSlotWeight_nonneg ε i j _)]
    exact ⟨fun _ => hFnat, Summable.of_finite⟩
  have hslotBound :
      (∑' q : Fin m → Z4,
        ∏ j, ρ.r324TotalSlotWeight ε i j (q j)) ≤
        U ^ m * ε⁻¹ ^ (4 * m + 8) := by
    rw [tsum_realSlotProduct m
      (fun j => ρ.r324TotalSlotWeight ε i j)
      (fun j k => ρ.r324TotalSlotWeight_nonneg ε i j k)
      (fun j => ρ.summable_r324TotalSlotWeight hε hε1 hcoeff i j)]
    calc
      (∏ j : Fin m, ∑' k : Z4, ρ.r324TotalSlotWeight ε i j k) ≤
          ∏ j : Fin m,
            U * ε⁻¹ ^ 4 * (if j = i then ε⁻¹ ^ 8 else 1) :=
        Finset.prod_le_prod
          (fun j _ => tsum_nonneg fun k =>
            ρ.r324TotalSlotWeight_nonneg ε i j k)
          (fun j _ => ρ.tsum_r324TotalSlotWeight_le hε hε1 hcoeff i j)
      _ = (U * ε⁻¹ ^ 4) ^ m * ε⁻¹ ^ 8 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin,
          Finset.prod_ite_eq' Finset.univ i (fun _ => ε⁻¹ ^ 8)]
        simp
      _ = U ^ m * ε⁻¹ ^ (4 * m + 8) := by
        rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]
  calc
    (∑' a : ℕ,
        ρ.r324RefinedRawCovarianceWeight hm ε p a *
          (1 + ‖z4EuclideanFrequency
            (r324KeyedRawSlotMode hm p a i)‖ ^ 2) ^ 4) =
        ∑' u : R324RefinedContractionIndex p × ℕ,
          ∏ j, ρ.r324TotalSlotWeight ε i j
            (r324NatEquivStandardConfigurations hm u.2 j) := by
      rw [← (r324NatEquivRefinedContractionConfigurations p).tsum_eq
        (fun u : R324RefinedContractionIndex p × ℕ =>
          ∏ j, ρ.r324TotalSlotWeight ε i j
            (r324NatEquivStandardConfigurations hm u.2 j))]
      exact tsum_congr fun a =>
        ρ.rawWeight_mul_modeCost_eq_prod hm ε p a i
    _ = ∑' _e : R324RefinedContractionIndex p, ∑' c : ℕ,
          ∏ j, ρ.r324TotalSlotWeight ε i j
            (r324NatEquivStandardConfigurations hm c j) :=
      hprod.tsum_prod' fun _ => hFnat
    _ = (Nat.card (R324RefinedContractionIndex p) : ℝ) *
          ∑' c : ℕ,
            ∏ j, ρ.r324TotalSlotWeight ε i j
              (r324NatEquivStandardConfigurations hm c j) := by
      rw [tsum_const, nsmul_eq_mul]
    _ ≤ (Nat.card (R324RefinedContractionIndex p) : ℝ) *
          (U ^ m * ε⁻¹ ^ (4 * m + 8)) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [(r324NatEquivStandardConfigurations hm).tsum_eq
        (fun q : Fin m → Z4 =>
          ∏ j, ρ.r324TotalSlotWeight ε i j (q j))]
      exact hslotBound

/-! ## The exact fibre regrouping -/

/-- **Regrouping of the cost-weighted keyed series.**  The
common-increment fibres partition the raw configurations, the routed
cost of a key is dominated by the cost of the raw slot mode, and the
keyed series reassembles into the raw total — with no multiplicity
loss and no per-key decay. -/
private theorem tsum_covWeight_mul_cost_le
    {m : ℕ} (hm : 0 < m) {C ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcoeff : ∀ k : Z4,
      ‖ρ.covarianceModeCoeff ε k‖ ≤
        C * (((1 + ε / (2 * Real.pi) *
          ‖z4EuclideanFrequency k‖) ^ 16)⁻¹))
    (p : R324RefinedScheduleIndex m) (i : Fin m) :
    Summable (fun b : ℕ =>
      ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b *
        r324GroupedIncrementCost hm b i) ∧
    (∑' b : ℕ,
      ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b *
        r324GroupedIncrementCost hm b i) ≤
      ∑' a : ℕ,
        ρ.r324RefinedRawCovarianceWeight hm ε p a *
          (1 + ‖z4EuclideanFrequency
            (r324KeyedRawSlotMode hm p a i)‖ ^ 2) ^ 4 := by
  set G : ℕ → ℝ := fun a =>
    ρ.r324RefinedRawCovarianceWeight hm ε p a *
      (1 + ‖z4EuclideanFrequency
        (r324KeyedRawSlotMode hm p a i)‖ ^ 2) ^ 4
    with hGdef
  have hGsum : Summable G :=
    ρ.summable_rawWeight_mul_modeCost hm hε hε1 hcoeff p i
  have hpoint : ∀ b : ℕ,
      ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b *
        r324GroupedIncrementCost hm b i ≤
        tsumByKey G (r324RefinedRawIncrementKey hm p)
          (r324NatEquivStandardConfigurations hm b) := by
    intro b
    have hterm : ∀ a : {a : ℕ //
        r324RefinedRawIncrementKey hm p a =
          r324NatEquivStandardConfigurations hm b},
        ρ.r324RefinedRawCovarianceWeight hm ε p a.1 *
          r324GroupedIncrementCost hm b i ≤ G a.1 := by
      intro a
      have hcost : r324GroupedIncrementCost hm b i =
          (1 + ‖z4EuclideanFrequency
            (r324RefinedRawIncrementKey hm p a.1 i)‖ ^ 2) ^ 4 := by
        unfold r324GroupedIncrementCost
        rw [← congrFun a.2 i]
      rw [hGdef, hcost]
      exact mul_le_mul_of_nonneg_left
        (r324KeyCost_le_modeCost hm p a.1 i)
        (ρ.r324RefinedRawCovarianceWeight_nonneg hm ε p a.1)
    have hsubG : Summable fun a : {a : ℕ //
        r324RefinedRawIncrementKey hm p a =
          r324NatEquivStandardConfigurations hm b} => G a.1 :=
      hGsum.subtype _
    have hsubL : Summable fun a : {a : ℕ //
        r324RefinedRawIncrementKey hm p a =
          r324NatEquivStandardConfigurations hm b} =>
        ρ.r324RefinedRawCovarianceWeight hm ε p a.1 *
          r324GroupedIncrementCost hm b i :=
      hsubG.of_nonneg_of_le
        (fun a => mul_nonneg
          (ρ.r324RefinedRawCovarianceWeight_nonneg hm ε p a.1)
          (r324GroupedIncrementCost_pos hm b i).le)
        hterm
    unfold r324KeyGroupedRefinedCovarianceWeight tsumByKey
    rw [← tsum_mul_right]
    exact Summable.tsum_le_tsum hterm hsubL hsubG
  have hRHSsum : Summable fun b : ℕ =>
      tsumByKey G (r324RefinedRawIncrementKey hm p)
        (r324NatEquivStandardConfigurations hm b) :=
    ((r324NatEquivStandardConfigurations hm).summable_iff).mpr
      (summable_tsumByKey G _ hGsum)
  have hLHSsum : Summable fun b : ℕ =>
      ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b *
        r324GroupedIncrementCost hm b i :=
    hRHSsum.of_nonneg_of_le
      (fun b => mul_nonneg
        (ρ.r324KeyGroupedRefinedCovarianceWeight_nonneg hm ε p b)
        (r324GroupedIncrementCost_pos hm b i).le)
      hpoint
  refine ⟨hLHSsum, ?_⟩
  calc
    (∑' b : ℕ,
        ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b *
          r324GroupedIncrementCost hm b i) ≤
        ∑' b : ℕ,
          tsumByKey G (r324RefinedRawIncrementKey hm p)
            (r324NatEquivStandardConfigurations hm b) :=
      Summable.tsum_le_tsum hpoint hLHSsum hRHSsum
    _ = ∑' k : Fin m → Z4,
          tsumByKey G (r324RefinedRawIncrementKey hm p) k :=
      (r324NatEquivStandardConfigurations hm).tsum_eq
        (fun k : Fin m → Z4 =>
          tsumByKey G (r324RefinedRawIncrementKey hm p) k)
    _ = ∑' a : ℕ, G a :=
      tsum_tsumByKey G _ hGsum

end SmoothCutoff

open SmoothCutoff

/-! ## The total-mass ledger -/

/-- Schedule envelope: total refined skeleton mass weighted by the
contraction-fibre cardinalities.  This `ε`-free constant is the same
envelope that prices the proved keyed route. -/
def r324TotalScheduleEnvelope (m : ℕ) : ℝ :=
  ∑ p : R324RefinedScheduleIndex m,
    r324RefinedInteriorSkeletonL1 p *
      (Nat.card (R324RefinedContractionIndex p) : ℝ)

theorem r324TotalScheduleEnvelope_nonneg (m : ℕ) :
    0 ≤ r324TotalScheduleEnvelope m := by
  unfold r324TotalScheduleEnvelope
  exact Finset.sum_nonneg fun p _ =>
    mul_nonneg (r324RefinedInteriorSkeletonL1_nonneg p)
      (Nat.cast_nonneg _)

/-- **The sharp total-mass ledger.**  For every marked slot, the
cost-weighted grouped slot series carries exactly `ε^{-(4m+8)}`: one
`ε⁻⁴` covariance mass per frequency slot and one extra `ε⁻⁸` for the
marked reciprocal cost.  The constant `U` is `ε`-uniform and
`m`-uniform; the envelope carries the schedule combinatorics.  No
`|log ε|` weight is consumed. -/
theorem exists_tsum_groupedCoreL1_mul_cost_totalMass
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) :
    ∃ U : ℝ, 0 < U ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ i : Fin m,
        (∑' p : R324RefinedScheduleIndex m × ℕ,
          ρ.r324GroupedRefinedCoreL1 hm ε p *
            SmoothCutoff.r324GroupedIncrementCost hm p.2 i) ≤
          r324TotalScheduleEnvelope m *
            (U ^ m * ε⁻¹ ^ (4 * m + 8)) := by
  obtain ⟨C, hC, hcoeff⟩ :=
    ρ.exists_covarianceModeCoeff_order8_bound
  refine ⟨C * 4096 * (2 * Real.pi) ^ 12, by positivity, ?_⟩
  intro ε hε hε1 i
  set U : ℝ := C * 4096 * (2 * Real.pi) ^ 12 with hUdef
  have hcov := fun k : Z4 => hcoeff hε k
  -- the per-schedule keyed slot series against the raw total
  have hfibre := fun p : R324RefinedScheduleIndex m =>
    ρ.tsum_covWeight_mul_cost_le hm hε hε1 hcov p i
  have hraw := fun p : R324RefinedScheduleIndex m =>
    ρ.tsum_rawWeight_mul_modeCost_le hm hε hε1 hcov p i
  have hperp : ∀ p : R324RefinedScheduleIndex m,
      (∑' b : ℕ,
        ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b *
          SmoothCutoff.r324GroupedIncrementCost hm b i) ≤
        (Nat.card (R324RefinedContractionIndex p) : ℝ) *
          (U ^ m * ε⁻¹ ^ (4 * m + 8)) :=
    fun p => ((hfibre p).2.trans (hraw p)).trans_eq (by rw [hUdef])
  -- the majorant of the complete slot series
  have hmajSummable :
      Summable fun q : R324RefinedScheduleIndex m × ℕ =>
        r324RefinedInteriorSkeletonL1 q.1 *
          (ρ.r324KeyGroupedRefinedCovarianceWeight hm ε q.1 q.2 *
            SmoothCutoff.r324GroupedIncrementCost hm q.2 i) := by
    rw [summable_prod_of_nonneg (fun q => mul_nonneg
      (r324RefinedInteriorSkeletonL1_nonneg q.1)
      (mul_nonneg
        (ρ.r324KeyGroupedRefinedCovarianceWeight_nonneg hm ε q.1 q.2)
        (SmoothCutoff.r324GroupedIncrementCost_pos hm q.2 i).le))]
    exact ⟨fun p => (hfibre p).1.mul_left
      (r324RefinedInteriorSkeletonL1 p), Summable.of_finite⟩
  have hpoint : ∀ q : R324RefinedScheduleIndex m × ℕ,
      ρ.r324GroupedRefinedCoreL1 hm ε q *
          SmoothCutoff.r324GroupedIncrementCost hm q.2 i ≤
        r324RefinedInteriorSkeletonL1 q.1 *
          (ρ.r324KeyGroupedRefinedCovarianceWeight hm ε q.1 q.2 *
            SmoothCutoff.r324GroupedIncrementCost hm q.2 i) := by
    intro q
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (ρ.r324GroupedRefinedCoreL1_le_skeleton_mul_covariance
        hm hε q.1 q.2)
      (SmoothCutoff.r324GroupedIncrementCost_pos hm q.2 i).le
  have hLHSsummable :
      Summable fun q : R324RefinedScheduleIndex m × ℕ =>
        ρ.r324GroupedRefinedCoreL1 hm ε q *
          SmoothCutoff.r324GroupedIncrementCost hm q.2 i :=
    hmajSummable.of_nonneg_of_le
      (fun q => mul_nonneg
        (ρ.r324GroupedRefinedCoreL1_nonneg hm ε q)
        (SmoothCutoff.r324GroupedIncrementCost_pos hm q.2 i).le)
      hpoint
  calc
    (∑' q : R324RefinedScheduleIndex m × ℕ,
        ρ.r324GroupedRefinedCoreL1 hm ε q *
          SmoothCutoff.r324GroupedIncrementCost hm q.2 i) ≤
        ∑' q : R324RefinedScheduleIndex m × ℕ,
          r324RefinedInteriorSkeletonL1 q.1 *
            (ρ.r324KeyGroupedRefinedCovarianceWeight hm ε q.1 q.2 *
              SmoothCutoff.r324GroupedIncrementCost hm q.2 i) :=
      Summable.tsum_le_tsum hpoint hLHSsummable hmajSummable
    _ = ∑ p : R324RefinedScheduleIndex m,
          r324RefinedInteriorSkeletonL1 p *
            ∑' b : ℕ,
              ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b *
                SmoothCutoff.r324GroupedIncrementCost hm b i := by
      rw [hmajSummable.tsum_prod' fun p => (hfibre p).1.mul_left
          (r324RefinedInteriorSkeletonL1 p),
        tsum_fintype]
      refine Finset.sum_congr rfl fun p _ => ?_
      show (∑' c : ℕ, r324RefinedInteriorSkeletonL1 p *
          (ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p c *
            SmoothCutoff.r324GroupedIncrementCost hm c i)) = _
      exact tsum_mul_left
    _ ≤ ∑ p : R324RefinedScheduleIndex m,
          r324RefinedInteriorSkeletonL1 p *
            ((Nat.card (R324RefinedContractionIndex p) : ℝ) *
              (U ^ m * ε⁻¹ ^ (4 * m + 8))) :=
      Finset.sum_le_sum fun p _ =>
        mul_le_mul_of_nonneg_left (hperp p)
          (r324RefinedInteriorSkeletonL1_nonneg p)
    _ = r324TotalScheduleEnvelope m *
          (U ^ m * ε⁻¹ ^ (4 * m + 8)) := by
      unfold r324TotalScheduleEnvelope
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by ring

/-! ## Discharge of the residual slot budget at amplitude `ε⁻⁶` -/

/-- **Total-mass discharge of the residual slot budget.**  The budget
constant is `A₁ ε⁻⁶` with `A₁` uniform in `ε`: the ledger
`ε^{-(4m+8)} ≤ ε^{-12m}` holds for every `m ≥ 1` and is saturated at
`m = 1`, where the marked slot series is a positive multiple of
`∑_k ⟨k⟩⁸‖ρ̂(εk)‖² ≍ ε⁻¹²`.  This improves the proved keyed
amplitude `1024 A₀ ε⁻¹⁶` (`exists_r324SlotLogBudget_final`) to `ε⁻⁶`,
the optimal power for the norm-inside interface. -/
theorem exists_r324SlotLogBudget_totalMass
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) :
    ∃ A₁ : ℝ, 0 < A₁ ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        R324SlotLogBudget ρ hm ε (A₁ * ε⁻¹ ^ (6 : ℕ)) := by
  obtain ⟨U, hU, hledger⟩ :=
    exists_tsum_groupedCoreL1_mul_cost_totalMass ρ hm
  set E : ℝ := r324TotalScheduleEnvelope m with hEdef
  have hE0 : 0 ≤ E := r324TotalScheduleEnvelope_nonneg m
  refine ⟨(1 + E) * (1 + U), by positivity, ?_⟩
  intro ε hε hε1 hlog i
  set L : ℝ := |Real.log ε| with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hlog
  have hεinv1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hT := hledger hε hε1 i
  have hE' : E ≤ (1 + E) ^ (2 * m) := by
    calc E ≤ 1 + E := by linarith
      _ = (1 + E) ^ 1 := (pow_one _).symm
      _ ≤ (1 + E) ^ (2 * m) :=
        pow_le_pow_right₀ (by linarith) (by omega)
  have hU' : U ^ m ≤ (1 + U) ^ (2 * m) := by
    calc U ^ m ≤ (1 + U) ^ m :=
          pow_le_pow_left₀ hU.le (by linarith) m
      _ ≤ (1 + U) ^ (2 * m) :=
        pow_le_pow_right₀ (by linarith) (by omega)
  have hconst : E * U ^ m ≤ ((1 + E) * (1 + U)) ^ (2 * m) := by
    rw [mul_pow]
    exact mul_le_mul hE' hU' (by positivity) (by positivity)
  have hpow : ε⁻¹ ^ (4 * m + 8) ≤ ε⁻¹ ^ (12 * m) :=
    pow_le_pow_right₀ hεinv1 (by omega)
  have hLm : L ≤ L ^ m := by
    calc L = L ^ 1 := (pow_one _).symm
      _ ≤ L ^ m := pow_le_pow_right₀ hlog hm
  calc
    L * (∑' p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324GroupedRefinedCoreL1 hm ε p *
          SmoothCutoff.r324GroupedIncrementCost hm p.2 i) ≤
        L * (E * (U ^ m * ε⁻¹ ^ (4 * m + 8))) :=
      mul_le_mul_of_nonneg_left hT hL0.le
    _ = (E * U ^ m) * ε⁻¹ ^ (4 * m + 8) * L := by ring
    _ ≤ ((1 + E) * (1 + U)) ^ (2 * m) * ε⁻¹ ^ (12 * m) * L ^ m := by
      refine mul_le_mul ?_ hLm hL0.le (by positivity)
      exact mul_le_mul hconst hpow (by positivity) (by positivity)
    _ = ((1 + E) * (1 + U) * ε⁻¹ ^ (6 : ℕ)) ^ (2 * m) * L ^ m := by
      rw [mul_pow ((1 + E) * (1 + U)) (ε⁻¹ ^ (6 : ℕ)), ← pow_mul,
        show 6 * (2 * m) = 12 * m from by ring]

/-! ## Capstone instantiations at amplitude `ε⁻⁶` -/

/-- **The R-324 deterministic moment bound, total-mass form.**  Every
analytic input is discharged; the slot budget is supplied by the
total-mass ledger, so the amplitude carries `ε⁻⁶` (improving the
proved keyed capstone `exists_deterministicMoment_paper_bound_final`
from `ε⁻¹⁶`).  The power `ε⁻⁶` is optimal for the norm-inside grouped
interface (see the header); the paper-scale amplitude — `A`
independent of `ε` — is *not* claimed. -/
theorem exists_deterministicMoment_paper_bound_totalMass
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε) :
    ∃ outerConstant A : ℝ, 0 < outerConstant ∧ 0 < A ∧
      ∀ (lam : ℝ) (α β : Z4), 0 ≤ lam →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (64 * (A * ε⁻¹ ^ (6 : ℕ))) lam ε m α β := by
  obtain ⟨A₁, hA₁, hbudget⟩ :=
    exists_r324SlotLogBudget_totalMass ρ hm
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hA : (0 : ℝ) < A₁ * ε⁻¹ ^ (6 : ℕ) := by positivity
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_slotBudget
      (primitiveConstant := A₁ * ε⁻¹ ^ (6 : ℕ)) hA
  exact ⟨outerConstant, A₁, houter, hA₁,
    fun lam α β hlam =>
      h ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
        (hbudget hε hε1 hlog)⟩

/-- Literal decay form of the total-mass estimate: the `min` bracket is
bounded by the P-3.5b-det decay
`ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε²(α+β)⟩⁻⁸`, at amplitude `64 A ε⁻⁶`. -/
theorem exists_deterministicMoment_decay_bound_totalMass
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hlog : 1 ≤ |Real.log ε|)
    (hmtrunc : m ≤ truncOrder ε) :
    ∃ outerConstant A : ℝ, 0 < outerConstant ∧ 0 < A ∧
      ∀ (lam : ℝ) (α β : Z4), 0 ≤ lam →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * outerConstant *
            ((64 * (A * ε⁻¹ ^ (6 : ℕ))) * lam) ^ (2 * m - 2) *
            paperDeterministicMomentDecay ε α β := by
  obtain ⟨A₁, hA₁, hbudget⟩ :=
    exists_r324SlotLogBudget_totalMass ρ hm
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hA : (0 : ℝ) < A₁ * ε⁻¹ ^ (6 : ℕ) := by positivity
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_decay_bound_of_slotBudget
      (primitiveConstant := A₁ * ε⁻¹ ^ (6 : ℕ)) hA
  exact ⟨outerConstant, A₁, houter, hA₁,
    fun lam α β hlam =>
      h ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
        (hbudget hε hε1 hlog)⟩

end

end Anderson4D
