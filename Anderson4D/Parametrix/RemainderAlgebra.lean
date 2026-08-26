import Anderson4D.Parametrix.IdentityLeftOperator

/-!
# Finite-order algebra for the parametrix remainder

This module proves the numerical reindexing behind paper
(3.20)--(3.21).  It is independent of the analytic content of
Proposition 3.4: once an order-by-order identity is supplied, the low
counterterms cancel with multiplicity one and precisely the pairs
`m + 2q > A` remain.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

/-- Flatten the low-counterterm order/rank sum to a product finset. -/
theorem lowCountertermSum_eq_flat
    {R : Type*} [AddCommMonoid R]
    (A : ℕ) (C : ℕ → ℕ → R) :
    (∑ m ∈ Finset.Icc 1 A,
        ∑ q ∈ (Finset.Icc 1 A).filter
          (fun q => 2 * q ≤ m),
          C q (m - 2 * q)) =
      ∑ p ∈
        ((Finset.Icc 1 A).product
          (Finset.Icc 1 A)).filter
            (fun p => 2 * p.2 ≤ p.1),
        C p.2 (p.1 - 2 * p.2) := by
  calc
    _ =
        ∑ m ∈ Finset.Icc 1 A,
          ∑ q ∈ Finset.Icc 1 A,
            if 2 * q ≤ m then
              C q (m - 2 * q)
            else 0 := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact Finset.sum_filter
        (fun q => 2 * q ≤ m)
        (fun q => C q (m - 2 * q))
    _ =
        ∑ p ∈
          (Finset.Icc 1 A).product
            (Finset.Icc 1 A),
          if 2 * p.2 ≤ p.1 then
            C p.2 (p.1 - 2 * p.2)
          else 0 := by
      exact
        (Finset.sum_product
          (Finset.Icc 1 A) (Finset.Icc 1 A)
          (fun p =>
            if 2 * p.2 ≤ p.1 then
              C p.2 (p.1 - 2 * p.2)
            else 0)).symm
    _ = _ := by
      exact
        (Finset.sum_filter
          (fun p : ℕ × ℕ => 2 * p.2 ≤ p.1)
          (fun p => C p.2 (p.1 - 2 * p.2))).symm

/-- Flatten the equivalent low region in remainder coordinates. -/
theorem lowCountertermPairs_eq_flat
    {R : Type*} [AddCommMonoid R]
    (A : ℕ) (C : ℕ → ℕ → R) :
    (∑ r ∈ Finset.range (A + 1),
        ∑ q ∈ (Finset.Icc 1 A).filter
          (fun q => r + 2 * q ≤ A),
          C q r) =
      ∑ p ∈
        ((Finset.range (A + 1)).product
          (Finset.Icc 1 A)).filter
            (fun p => p.1 + 2 * p.2 ≤ A),
        C p.2 p.1 := by
  calc
    _ =
        ∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ Finset.Icc 1 A,
            if r + 2 * q ≤ A then C q r else 0 := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact Finset.sum_filter
        (fun q => r + 2 * q ≤ A)
        (fun q => C q r)
    _ =
        ∑ p ∈
          (Finset.range (A + 1)).product
            (Finset.Icc 1 A),
          if p.1 + 2 * p.2 ≤ A then
            C p.2 p.1
          else 0 := by
      exact
        (Finset.sum_product
          (Finset.range (A + 1))
          (Finset.Icc 1 A)
          (fun p =>
            if p.1 + 2 * p.2 ≤ A then
              C p.2 p.1
            else 0)).symm
    _ = _ := by
      exact
        (Finset.sum_filter
          (fun p : ℕ × ℕ =>
            p.1 + 2 * p.2 ≤ A)
          (fun p => C p.2 p.1)).symm

/-- The change of variables `r = m - 2q` is a multiplicity-one
bijection between the two descriptions of the low counterterm region. -/
theorem lowCountertermFlat_reindex
    {R : Type*} [AddCommMonoid R]
    (A : ℕ) (C : ℕ → ℕ → R) :
    (∑ p ∈
        ((Finset.Icc 1 A).product
          (Finset.Icc 1 A)).filter
            (fun p => 2 * p.2 ≤ p.1),
        C p.2 (p.1 - 2 * p.2)) =
      ∑ p ∈
        ((Finset.range (A + 1)).product
          (Finset.Icc 1 A)).filter
            (fun p => p.1 + 2 * p.2 ≤ A),
        C p.2 p.1 := by
  let S :=
    ((Finset.Icc 1 A).product (Finset.Icc 1 A)).filter
      (fun p => 2 * p.2 ≤ p.1)
  let T :=
    ((Finset.range (A + 1)).product (Finset.Icc 1 A)).filter
      (fun p => p.1 + 2 * p.2 ≤ A)
  change
    (∑ p ∈ S, C p.2 (p.1 - 2 * p.2)) =
      ∑ p ∈ T, C p.2 p.1
  apply Finset.sum_bij
    (fun p _hp => (p.1 - 2 * p.2, p.2))
  · intro p hp
    have hpS := Finset.mem_filter.mp hp
    have hpProd := Finset.mem_product.mp hpS.1
    have hm := Finset.mem_Icc.mp hpProd.1
    have hq := Finset.mem_Icc.mp hpProd.2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_range.mpr
        omega
      · exact hpProd.2
    · omega
  · intro p₁ hp₁ p₂ hp₂ heq
    have hp₁S := Finset.mem_filter.mp hp₁
    have hp₂S := Finset.mem_filter.mp hp₂
    have hp₁le := hp₁S.2
    have hp₂le := hp₂S.2
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    simp only at hfirst hsecond
    apply Prod.ext
    · omega
    · exact hsecond
  · intro p hp
    have hpT := Finset.mem_filter.mp hp
    have hpProd := Finset.mem_product.mp hpT.1
    have hr := Finset.mem_range.mp hpProd.1
    have hq := Finset.mem_Icc.mp hpProd.2
    refine ⟨(p.1 + 2 * p.2, p.2), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_Icc.mpr
          omega
        · exact hpProd.2
      · omega
    · apply Prod.ext <;> simp
  · intro p hp
    rfl

/-- Reindex the low counterterms from the order appearing in
Proposition 3.4 to the `(tail order, counterterm order)` coordinates
used by (3.20). -/
theorem lowCountertermOrder_reindex
    {R : Type*} [AddCommMonoid R]
    (A : ℕ) (C : ℕ → ℕ → R) :
    (∑ m ∈ Finset.Icc 1 A,
        ∑ q ∈ (Finset.Icc 1 A).filter
          (fun q => 2 * q ≤ m),
          C q (m - 2 * q)) =
      ∑ r ∈ Finset.range (A + 1),
        ∑ q ∈ (Finset.Icc 1 A).filter
          (fun q => r + 2 * q ≤ A),
          C q r := by
  calc
    _ =
        ∑ p ∈
          ((Finset.Icc 1 A).product
            (Finset.Icc 1 A)).filter
              (fun p => 2 * p.2 ≤ p.1),
          C p.2 (p.1 - 2 * p.2) :=
      lowCountertermSum_eq_flat A C
    _ =
        ∑ p ∈
          ((Finset.range (A + 1)).product
            (Finset.Icc 1 A)).filter
              (fun p => p.1 + 2 * p.2 ≤ A),
          C p.2 p.1 :=
      lowCountertermFlat_reindex A C
    _ = _ := (lowCountertermPairs_eq_flat A C).symm

/-- Split all counterterms into the cancelling low region and the
boundary region `r + 2q > A` of paper (3.21). -/
theorem totalCounterterm_eq_low_add_boundary
    {R : Type*} [AddCommMonoid R]
    (A : ℕ) (C : ℕ → ℕ → R) :
    (∑ r ∈ Finset.range (A + 1),
        ∑ q ∈ Finset.Icc 1 A, C q r) =
      (∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => r + 2 * q ≤ A),
            C q r) +
        ∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => ¬r + 2 * q ≤ A),
            C q r := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  exact
    (Finset.sum_filter_add_sum_filter_not
      (Finset.Icc 1 A)
      (fun q => r + 2 * q ≤ A)
      (fun q => C q r)).symm

/-- Reindex the positive orders `1,...,A` by `k ↦ k+1`. -/
theorem sum_range_succ_eq_sum_Icc
    {R : Type*} [AddCommMonoid R]
    (A : ℕ) (f : ℕ → R) :
    (∑ k ∈ Finset.range A, f (k + 1)) =
      ∑ m ∈ Finset.Icc 1 A, f m := by
  apply Finset.sum_bij (fun k _hk => k + 1)
  · intro k hk
    apply Finset.mem_Icc.mpr
    have hklt := Finset.mem_range.mp hk
    omega
  · intro k₁ hk₁ k₂ hk₂ heq
    omega
  · intro m hm
    have hmIcc := Finset.mem_Icc.mp hm
    refine ⟨m - 1, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      omega
    · omega
  · intro k hk
    rfl

/-- For an order `m ≤ A`, the globally bounded filter used by the
telescope is exactly the paper range `1 ≤ q ≤ m/2`. -/
theorem countertermFilter_eq_Icc_half
    {m A : ℕ} (hm : m ≤ A) :
    (Finset.Icc 1 A).filter
        (fun q => 2 * q ≤ m) =
      Finset.Icc 1 (m / 2) := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- Abstract telescoping form of paper (3.20)--(3.21).

Here `P m` is the order-`m` parametrix contribution, `N m` is the
noise composition at order `m`, and `C q r` is the order-`2q`
counterterm acting on `P r`. -/
theorem parametrixTelescope
    {R : Type*} [AddCommGroup R]
    (A : ℕ) (P N : ℕ → R)
    (C : ℕ → ℕ → R)
    (hN :
      ∀ m ∈ Finset.Icc 1 A,
        N (m - 1) =
          P m +
            ∑ q ∈ (Finset.Icc 1 A).filter
              (fun q => 2 * q ≤ m),
              C q (m - 2 * q)) :
    (∑ m ∈ Finset.range (A + 1), P m) -
          (∑ m ∈ Finset.range (A + 1), N m) +
        (∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ Finset.Icc 1 A, C q r) =
      P 0 - N A +
        ∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => ¬r + 2 * q ≤ A),
            C q r := by
  let low : ℕ → R :=
    fun m =>
      ∑ q ∈ (Finset.Icc 1 A).filter
        (fun q => 2 * q ≤ m),
        C q (m - 2 * q)
  have hrel (k : ℕ) (hk : k ∈ Finset.range A) :
      N k = P (k + 1) + low (k + 1) := by
    have hklt := Finset.mem_range.mp hk
    have hmem : k + 1 ∈ Finset.Icc 1 A :=
      Finset.mem_Icc.mpr (by omega)
    have h := hN (k + 1) hmem
    simpa only [Nat.add_sub_cancel, low] using h
  have hprefix :
      (∑ k ∈ Finset.range A, N k) =
        (∑ k ∈ Finset.range A, P (k + 1)) +
          ∑ k ∈ Finset.range A, low (k + 1) := by
    calc
      _ =
          ∑ k ∈ Finset.range A,
            (P (k + 1) + low (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hrel k hk
      _ = _ := Finset.sum_add_distrib
  have hlowIcc :
      (∑ k ∈ Finset.range A, low (k + 1)) =
        ∑ m ∈ Finset.Icc 1 A, low m :=
    sum_range_succ_eq_sum_Icc A low
  have hlowPairs :
      (∑ m ∈ Finset.Icc 1 A, low m) =
        ∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => r + 2 * q ≤ A),
            C q r := by
    exact lowCountertermOrder_reindex A C
  have htotal :=
    totalCounterterm_eq_low_add_boundary A C
  rw [Finset.sum_range_succ' P A]
  rw [Finset.sum_range_succ N A]
  rw [hprefix, hlowIcc, hlowPairs, htotal]
  abel

/-- Paper-indexed form of `parametrixTelescope`, with the
counterterm range written exactly as `1 ≤ q ≤ m/2`. -/
theorem parametrixTelescopeIcc
    {R : Type*} [AddCommGroup R]
    (A : ℕ) (P N : ℕ → R)
    (C : ℕ → ℕ → R)
    (hN :
      ∀ m ∈ Finset.Icc 1 A,
        N (m - 1) =
          P m +
            ∑ q ∈ Finset.Icc 1 (m / 2),
              C q (m - 2 * q)) :
    (∑ m ∈ Finset.range (A + 1), P m) -
          (∑ m ∈ Finset.range (A + 1), N m) +
        (∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ Finset.Icc 1 A, C q r) =
      P 0 - N A +
        ∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => ¬r + 2 * q ≤ A),
            C q r := by
  apply parametrixTelescope A P N C
  intro m hm
  rw [countertermFilter_eq_Icc_half
    (Finset.mem_Icc.mp hm).2]
  exact hN m hm

end Anderson4D
