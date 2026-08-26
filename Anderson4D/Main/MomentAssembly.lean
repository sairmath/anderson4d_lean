import Anderson4D.Main.GaussianLimit

/-!
# Algebraic moment assembly from Proposition 3.6

This file isolates the exact algebraic content of paper (3.28) used in
blueprint node `P-mom`.  The antidiagonal is restricted to positive
orders, odd total order vanishes, and even total order `m` contributes
`(λ / (√2 π))^(m - 2)`.  Summing the even contributions is then an
ordinary geometric series with ratio `λ² / (2π²)`.

The coefficient table furnished by `Prop36` may depend on the
truncation `B`.  This file deliberately makes no cross-truncation
identification: that separate P-mom step requires uniqueness in (3.27)
and positivity of the zero-mode four-point coefficient.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter
open scoped BigOperators Topology

/-- The positive-order antidiagonal sum occurring literally in (3.28). -/
def positiveAntidiagonalSum
    (𝔛 : ℕ → ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal m).filter
      (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2),
    𝔛 p.1 p.2

/-- The one-step amplitude in (3.28). -/
def prop36MomentBase (lam : ℝ) : ℝ :=
  lam / (Real.sqrt 2 * Real.pi)

/-- The ratio after restricting (3.28) to even total orders. -/
def prop36EvenRatio (lam : ℝ) : ℝ :=
  lam ^ 2 / (2 * Real.pi ^ 2)

/-- The first `N` even contributions, corresponding to total orders
`m = 2, 4, ..., 2N`. -/
def prop36EvenPartialSum (lam : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, prop36MomentBase lam ^ (2 * n)

/-- The part of the existential data in `Prop36` needed for the
algebraic assembly of (3.28).  It retains the bound clause as well as
the literal positive-antidiagonal identity, so downstream code does not
need to destruct the much larger eventual moment-factorization clause. -/
structure Prop36AntidiagonalData (lam : ℝ) (B : ℕ) where
  coeff : ℕ → ℕ → ℝ
  constant : ℝ
  constant_pos : 0 < constant
  coeff_bound :
    ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → 1 ≤ m₂ →
      |coeff m₁ m₂| ≤
        constant * (constant * lam) ^ (m₁ + m₂ - 2)
  sum_identity :
    ∀ m : ℕ, 2 ≤ m →
      positiveAntidiagonalSum coeff m =
        if Even m then prop36MomentBase lam ^ (m - 2) else 0

namespace Prop36

/-- The canonical (3.28) data at truncation `B` and family size `r`.
Its bound constant is definitionally independent of both parameters. -/
def antidiagonalData
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (B r : ℕ) :
    Prop36AntidiagonalData lam B where
    coeff := hP36.coefficientTable B r
    constant := hP36.boundConstant
    constant_pos := hP36.boundConstant_pos
    coeff_bound := (hP36.coefficientTable_spec B r).1
    sum_identity := by
      intro m hm
      simpa only [positiveAntidiagonalSum, prop36MomentBase] using
        (hP36.coefficientTable_spec B r).2.1 m hm

/-- Every chosen truncation and family size in Proposition 3.6 supplies
the exact algebraic data of (3.28). -/
theorem nonempty_antidiagonalData
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (B r : ℕ) :
    Nonempty (Prop36AntidiagonalData lam B) :=
  ⟨hP36.antidiagonalData B r⟩

end Prop36

namespace Prop36AntidiagonalData

variable {lam : ℝ} {B : ℕ}
variable (data : Prop36AntidiagonalData lam B)

/-- Literal odd-total-order consequence of (3.28). -/
theorem odd_sum_eq_zero
    {m : ℕ} (_hmB : m ≤ B) (hm2 : 2 ≤ m) (hm : Odd m) :
    positiveAntidiagonalSum data.coeff m = 0 := by
  rw [data.sum_identity m hm2,
    if_neg (Nat.not_even_iff_odd.mpr hm)]

/-- Literal even-total-order consequence of (3.28). -/
theorem even_sum_eq_pow
    {m : ℕ} (_hmB : m ≤ B) (hm2 : 2 ≤ m) (hm : Even m) :
    positiveAntidiagonalSum data.coeff m =
      prop36MomentBase lam ^ (m - 2) := by
  rw [data.sum_identity m hm2, if_pos hm]

/-- At total order `2n+2`, the antidiagonal contribution has exponent
exactly `2n`. -/
theorem sum_two_mul_add_two
    (n : ℕ) (hnB : 2 * n + 2 ≤ B) :
    positiveAntidiagonalSum data.coeff (2 * n + 2) =
      prop36MomentBase lam ^ (2 * n) := by
  have heven : Even (2 * n + 2) := by
    use n + 1
    omega
  rw [data.even_sum_eq_pow hnB (by omega) heven]
  congr 1

/-- Summing the (3.28) identities at total orders
`2, 4, ..., 2N` gives the exact finite even partial sum. -/
theorem sum_even_antidiagonals_eq_partialSum
    (N : ℕ) (hNB : 2 * N ≤ B) :
    (∑ n ∈ Finset.range N,
      positiveAntidiagonalSum data.coeff (2 * n + 2)) =
      prop36EvenPartialSum lam N := by
  unfold prop36EvenPartialSum
  apply Finset.sum_congr rfl
  intro n hn
  apply data.sum_two_mul_add_two
  have hnN : n < N := Finset.mem_range.mp hn
  omega

end Prop36AntidiagonalData

/-! ## Exact geometric-series evaluation -/

/-- Squaring the amplitude in (3.28) gives the geometric ratio
`λ²/(2π²)` with no hidden normalization factor. -/
theorem prop36MomentBase_sq (lam : ℝ) :
    prop36MomentBase lam ^ 2 = prop36EvenRatio lam := by
  unfold prop36MomentBase prop36EvenRatio
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  field_simp [hsqrt, hpi]
  nlinarith

/-- Every even contribution is the corresponding power of the
one-variable geometric ratio. -/
theorem prop36MomentBase_even_pow (lam : ℝ) (n : ℕ) :
    prop36MomentBase lam ^ (2 * n) =
      prop36EvenRatio lam ^ n := by
  rw [pow_mul, prop36MomentBase_sq]

/-- Exact conversion of the finite even contribution sum to a geometric
partial sum. -/
theorem prop36EvenPartialSum_eq_geometric
    (lam : ℝ) (N : ℕ) :
    prop36EvenPartialSum lam N =
      ∑ n ∈ Finset.range N, prop36EvenRatio lam ^ n := by
  unfold prop36EvenPartialSum
  apply Finset.sum_congr rfl
  intro n hn
  exact prop36MomentBase_even_pow lam n

/-- Closed form for every finite even partial sum. -/
theorem prop36EvenPartialSum_eq_closed
    (lam : ℝ) (N : ℕ)
    (hr : prop36EvenRatio lam ≠ 1) :
    prop36EvenPartialSum lam N =
      (prop36EvenRatio lam ^ N - 1) /
        (prop36EvenRatio lam - 1) := by
  rw [prop36EvenPartialSum_eq_geometric, geom_sum_eq hr]

/-- The subcritical hypothesis is exactly the statement that the even
geometric ratio is strictly below one. -/
theorem prop36EvenRatio_lt_one
    {lam : ℝ} (hlam : lam ^ 2 < 2 * Real.pi ^ 2) :
    prop36EvenRatio lam < 1 := by
  unfold prop36EvenRatio
  exact (div_lt_one (by positivity : 0 < 2 * Real.pi ^ 2)).mpr hlam

theorem prop36EvenRatio_nonneg (lam : ℝ) :
    0 ≤ prop36EvenRatio lam := by
  unfold prop36EvenRatio
  positivity

/-- Algebraic identification of the geometric-series value with the
prefactor used by the limit Gaussian law. -/
theorem one_sub_prop36EvenRatio_inv_eq_limitPrefactor
    {lam : ℝ} (hlam : lam ^ 2 < 2 * Real.pi ^ 2) :
    (1 - prop36EvenRatio lam)⁻¹ = limitPrefactor lam := by
  unfold prop36EvenRatio limitPrefactor
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : 2 * Real.pi ^ 2 - lam ^ 2 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hlam)
  field_simp [hpi, hden]

/-- The even (3.28) contributions have sum exactly
`limitPrefactor λ` in the subcritical regime. -/
theorem hasSum_prop36EvenTerms
    {lam : ℝ} (hlam : lam ^ 2 < 2 * Real.pi ^ 2) :
    HasSum
      (fun n : ℕ => prop36MomentBase lam ^ (2 * n))
      (limitPrefactor lam) := by
  have hgeo :
      HasSum
        (fun n : ℕ => prop36EvenRatio lam ^ n)
        (1 - prop36EvenRatio lam)⁻¹ :=
    hasSum_geometric_of_lt_one
      (prop36EvenRatio_nonneg lam)
      (prop36EvenRatio_lt_one hlam)
  have heven :
      HasSum
        (fun n : ℕ => prop36MomentBase lam ^ (2 * n))
        (1 - prop36EvenRatio lam)⁻¹ :=
    hgeo.congr_fun fun n =>
      prop36MomentBase_even_pow lam n
  simpa only [one_sub_prop36EvenRatio_inv_eq_limitPrefactor hlam] using
    heven

/-- `tsum` form of the exact even contribution sum. -/
theorem tsum_prop36EvenTerms_eq_limitPrefactor
    {lam : ℝ} (hlam : lam ^ 2 < 2 * Real.pi ^ 2) :
    (∑' n : ℕ, prop36MomentBase lam ^ (2 * n)) =
      limitPrefactor lam :=
  (hasSum_prop36EvenTerms hlam).tsum_eq

/-- The finite even partial sums converge to the exact prefactor in the
limit law. -/
theorem tendsto_prop36EvenPartialSum
    {lam : ℝ} (hlam : lam ^ 2 < 2 * Real.pi ^ 2) :
    Tendsto (prop36EvenPartialSum lam) atTop
      (𝓝 (limitPrefactor lam)) := by
  change Tendsto
    (fun N : ℕ =>
      ∑ n ∈ Finset.range N, prop36MomentBase lam ^ (2 * n))
    atTop (𝓝 (limitPrefactor lam))
  exact (hasSum_prop36EvenTerms hlam).tendsto_sum_nat

/-- Direct API from Proposition 3.6: at every even truncation `2N`, one
may choose a single coefficient table whose summed positive
antidiagonals through that truncation equal the geometric partial sum. -/
theorem Prop36.exists_evenAntidiagonalPartialSum
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (N r : ℕ) :
    ∃ data : Prop36AntidiagonalData lam (2 * N),
      (∑ n ∈ Finset.range N,
        positiveAntidiagonalSum data.coeff (2 * n + 2)) =
        prop36EvenPartialSum lam N := by
  let data := hP36.antidiagonalData (2 * N) r
  exact ⟨data,
    data.sum_even_antidiagonals_eq_partialSum N le_rfl⟩

end

end Anderson4D
