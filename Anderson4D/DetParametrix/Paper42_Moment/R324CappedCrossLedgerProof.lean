import Anderson4D.DetParametrix.Paper42_Moment.R324CappedCrossCalibration
import Anderson4D.DetParametrix.Paper42_Moment.R324ShiftedWindow

/-!
# Capped cross ledger, part 2: the order-three calibration

After the Parseval collapse the pure-cross entity of a bijection `σ`
is the zero-sum lattice sum

`I(σ) = Σ_{k₁+…+k_m=0} ∏ᵢ ‖ρ̂(εkᵢ)‖² ∏_{j<m} ⟨Sⱼ⟩⁻²⟨Tⱼ^σ⟩⁻²`,

`Sⱼ = k₁+…+kⱼ` (identity-order partial sums, one propagator per
internal edge of the left Green chain) and `Tⱼ^σ` the same partial sums
taken in `σ` order (right chain).  There are `m-1` free momenta and
`2(m-1)` quadratic propagators: the sum is log-critical, so each free
momentum contributes at most one factor `L = |log ε|`, and only when
the propagators covering it are *doubled* (or critically entangled).

## The `m = 3` table (proved here, uniformly in `σ`)

At `m = 3`, `S₁ = k₁`, `S₂ = -k₃`, `T₁ = k_{τ1}`, `T₂ = -k_{τ3}` with
`τ = σ⁻¹`, so the propagator multiset of `σ` is determined by the pair
`(i,j) = (τ1, τ3)`:

| `τ = σ⁻¹` | `(i,j)` | propagators                    | order |
| --------- | ------- | ------------------------------ | ----- |
| `id`      | `(1,3)` | `⟨k₁⟩⁻⁴⟨k₃⟩⁻⁴`                 | `L²`  |
| `(1 2)`   | `(2,3)` | `⟨k₁⟩⁻²⟨k₂⟩⁻²⟨k₃⟩⁻⁴`           | `L²`  |
| `(2 3)`   | `(1,2)` | `⟨k₁⟩⁻⁴⟨k₂⟩⁻²⟨k₃⟩⁻²`           | `L²`  |
| `(1 3)`   | `(3,1)` | `⟨k₁⟩⁻⁴⟨k₃⟩⁻⁴`                 | `L²`  |
| `(1 2 3)` | `(2,1)` | `⟨k₁⟩⁻⁴⟨k₂⟩⁻²⟨k₃⟩⁻²`           | `L²`  |
| `(1 3 2)` | `(3,2)` | `⟨k₁⟩⁻²⟨k₂⟩⁻²⟨k₃⟩⁻⁴`           | `L²`  |

`r324CC_exists_latticeThree_le_log_sq` proves the upper half of the
table for *all six* patterns at once: the arithmetic-geometric split
`ab ≤ (a²+b²)/2` applied to `a = ⟨S₁⟩⁻²⟨S₂⟩⁻²`, `b = ⟨T₁⟩⁻²⟨T₂⟩⁻²`
reduces every pattern to a pair of *doubled* propagators at two
distinct modes, and each of the three possible pairs `(k₁,k₂)`,
`(k₁,k₃)`, `(k₂,k₃)` iterates into two proved translated windows
`Σ_k ‖ρ̂(εk)‖²⟨k+γ⟩⁻⁴ ≤ C·L` (`r324SW_translated_window_le_log`) — the
shift `γ` of the inner window being the outer summation variable.  The
matching lower half is the classical dyadic count `Σ_{|s|≤N}⟨s⟩⁻⁴
log(N/⟨s⟩) ≍ (log N)²`, so every order-three entity is *exactly* of
order `L² = L^{m-1}`: **at `m = 3` all six entities have the same
grade, and the grading is neither available nor needed** — the count
`3! = 6` is itself geometric
(`r324CappedCrossLedgerAt_three_of_entityBoundAt`).

The first strict grade drop is at `m = 4`: `τ = (2,4,1,3)` gives
propagators `⟨k₁⟩⁻²⟨k₁+k₂⟩⁻²⟨k₄⟩⁻²⟨k₂⟩⁻²⟨k₂+k₄⟩⁻²⟨k₃⟩⁻²` in three free
momenta with no critical proper subspace (every lattice line carries
`≥ 3` quadratic propagators), hence order `L¹`, not `L³`.

## Conditional order-three physical-to-lattice collapse

`R324CappedCrossCollapseThree` packages the physical-to-lattice comparison.
Given this comparison, `r324CappedCrossLedgerAt_three_of_collapse` proves the
order-three ledger.

At higher order the collapse alone is not enough:
`r324CappedCross_flatGrade_over_budget` shows the flat grade `m-1`
(which is sharp — the identity entity saturates it) overshoots the
graded-count clause for every constant, so the general-`m` route must
go through `R324CappedCrossGradingBoundAt` with a non-constant grade.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Iterated window sums -/

/-- **Iterated summation for a two-variable nonnegative lattice
family.**  If the outer family sums to `≤ A` and every inner slice sums
to `≤ B`, the product family over `Z4 × Z4` sums to `≤ A·B`. -/
theorem r324CC_tsum_prod_le {f : Z4 → ℝ} {g : Z4 → Z4 → ℝ} {A B : ℝ}
    (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k l, 0 ≤ g k l)
    (hfs : Summable f) (hgs : ∀ k, Summable (g k))
    (hB : 0 ≤ B) (hf : ∑' k, f k ≤ A) (hg : ∀ k, ∑' l, g k l ≤ B) :
    (∑' p : Z4 × Z4, f p.1 * g p.1 p.2) ≤ A * B := by
  have hslice : ∀ k : Z4, Summable fun l : Z4 => f k * g k l :=
    fun k => (hgs k).mul_left _
  have houter : Summable fun k : Z4 => ∑' l : Z4, f k * g k l := by
    have hEq : (fun k : Z4 => ∑' l : Z4, f k * g k l) =
        fun k : Z4 => f k * ∑' l : Z4, g k l := by
      funext k
      exact tsum_mul_left
    rw [hEq]
    refine (hfs.mul_right B).of_nonneg_of_le
      (fun k => mul_nonneg (hf0 k) ?_) (fun k => ?_)
    · exact tsum_nonneg fun l => hg0 k l
    · exact mul_le_mul_of_nonneg_left (hg k) (hf0 k)
  have hprod : Summable fun p : Z4 × Z4 => f p.1 * g p.1 p.2 := by
    refine (summable_prod_of_nonneg
      (fun p => mul_nonneg (hf0 p.1) (hg0 p.1 p.2))).mpr ⟨hslice, houter⟩
  calc
    (∑' p : Z4 × Z4, f p.1 * g p.1 p.2) =
        ∑' k : Z4, ∑' l : Z4, f k * g k l := hprod.tsum_prod' hslice
    _ ≤ ∑' k : Z4, f k * B := by
      refine houter.tsum_le_tsum ?_ (hfs.mul_right B)
      intro k
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (hg k) (hf0 k)
    _ = (∑' k : Z4, f k) * B := tsum_mul_right
    _ ≤ A * B := mul_le_mul_of_nonneg_right hf hB

/-- Mirrored iterated summation (outer variable in the second slot). -/
theorem r324CC_tsum_prod_snd_le {f : Z4 → ℝ} {g : Z4 → Z4 → ℝ}
    {A B : ℝ}
    (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k l, 0 ≤ g k l)
    (hfs : Summable f) (hgs : ∀ k, Summable (g k))
    (hB : 0 ≤ B) (hf : ∑' k, f k ≤ A) (hg : ∀ k, ∑' l, g k l ≤ B) :
    (∑' p : Z4 × Z4, f p.2 * g p.2 p.1) ≤ A * B := by
  have hswap :
      (∑' p : Z4 × Z4, f p.2 * g p.2 p.1) =
        ∑' p : Z4 × Z4, f p.1 * g p.1 p.2 :=
    (Equiv.prodComm Z4 Z4).tsum_eq
      (fun p : Z4 × Z4 => f p.1 * g p.1 p.2)
  rw [hswap]
  exact r324CC_tsum_prod_le hf0 hg0 hfs hgs hB hf hg

theorem r324CC_summable_prod {f : Z4 → ℝ} {g : Z4 → Z4 → ℝ} {B : ℝ}
    (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k l, 0 ≤ g k l)
    (hfs : Summable f) (hgs : ∀ k, Summable (g k))
    (_hB : 0 ≤ B) (hg : ∀ k, ∑' l, g k l ≤ B) :
    Summable fun p : Z4 × Z4 => f p.1 * g p.1 p.2 := by
  refine (summable_prod_of_nonneg
    (fun p => mul_nonneg (hf0 p.1) (hg0 p.1 p.2))).mpr
    ⟨fun k => (hgs k).mul_left (f k), ?_⟩
  have hEq : (fun k : Z4 => ∑' l : Z4, f k * g k l) =
      fun k : Z4 => f k * ∑' l : Z4, g k l := by
    funext k
    exact tsum_mul_left
  rw [hEq]
  refine (hfs.mul_right B).of_nonneg_of_le
    (fun k => mul_nonneg (hf0 k) (tsum_nonneg fun l => hg0 k l))
    (fun k => mul_le_mul_of_nonneg_left (hg k) (hf0 k))

theorem r324CC_summable_prod_snd {f : Z4 → ℝ} {g : Z4 → Z4 → ℝ}
    {B : ℝ}
    (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k l, 0 ≤ g k l)
    (hfs : Summable f) (hgs : ∀ k, Summable (g k))
    (hB : 0 ≤ B) (hg : ∀ k, ∑' l, g k l ≤ B) :
    Summable fun p : Z4 × Z4 => f p.2 * g p.2 p.1 :=
  (Equiv.prodComm Z4 Z4).summable_iff.mpr
    (r324CC_summable_prod hf0 hg0 hfs hgs hB hg)

/-! ## The collapsed order-three lattice sums -/

/-- The Japanese bracket `⟨k⟩⁻²` of the paper's Green propagator. -/
def r324CCbrk (k : Z4) : ℝ := (1 + paperModeNormSq k)⁻¹

/-- The symbol weight `‖ρ̂(εk)‖²` of one cross leg. -/
def r324CCsym (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) : ℝ :=
  ‖ρ.symbol ε k‖ ^ 2

/-- The `ε`-window family with shift `γ`: the exact summand of the
proved translated-window estimate. -/
def r324CCwin (ρ : SmoothCutoff) (ε : ℝ) (γ k : Z4) : ℝ :=
  r324CCsym ρ ε k * r324CCbrk (k + γ) ^ 2

/-- The three cross momenta of an order-three all-cross entity, as
functions of the two free lattice variables; `k₃ = -(k₁+k₂)` is the
zero-sum constraint left by the two external Green legs. -/
def r324CCmode (i : Fin 3) (p : Z4 × Z4) : Z4 :=
  if i = 0 then p.1 else if i = 1 then p.2 else -(p.1 + p.2)

@[simp] theorem r324CCmode_zero (p : Z4 × Z4) :
    r324CCmode 0 p = p.1 := rfl

@[simp] theorem r324CCmode_one (p : Z4 × Z4) :
    r324CCmode 1 p = p.2 := rfl

@[simp] theorem r324CCmode_two (p : Z4 × Z4) :
    r324CCmode 2 p = -(p.1 + p.2) := rfl

/-- The symbol weight of all three cross legs. -/
def r324CCsymWeight (ρ : SmoothCutoff) (ε : ℝ) (p : Z4 × Z4) : ℝ :=
  r324CCsym ρ ε p.1 * r324CCsym ρ ε p.2 *
    r324CCsym ρ ε (-(p.1 + p.2))

/-- The pair family carrying two *doubled* propagators at the modes
`u ≠ w`: the resonant shape reached after the arithmetic-geometric
split. -/
def r324CCPair (ρ : SmoothCutoff) (ε : ℝ) (u w : Fin 3)
    (p : Z4 × Z4) : ℝ :=
  r324CCsymWeight ρ ε p *
    (r324CCbrk (r324CCmode u p) ^ 2 * r324CCbrk (r324CCmode w p) ^ 2)

/-- **The collapsed order-three entity value.**  After the Parseval
collapse the entity of the bijection `σ` is the zero-sum lattice sum
of the three symbol weights against the two identity-order propagators
`⟨k₁⟩⁻²⟨k₃⟩⁻²` and the two `σ`-order propagators
`⟨k_{σ⁻¹1}⟩⁻²⟨k_{σ⁻¹3}⟩⁻²`; `(i,j) = (σ⁻¹1, σ⁻¹3)`. -/
def r324CCLatticeThree (ρ : SmoothCutoff) (ε : ℝ) (i j : Fin 3) : ℝ :=
  ∑' p : Z4 × Z4,
    r324CCsymWeight ρ ε p *
      (r324CCbrk (r324CCmode 0 p) * r324CCbrk (r324CCmode 2 p) *
        (r324CCbrk (r324CCmode i p) * r324CCbrk (r324CCmode j p)))

theorem r324CCbrk_nonneg (k : Z4) : 0 ≤ r324CCbrk k :=
  r324SW_bracket_nonneg k

theorem r324CCbrk_le_one (k : Z4) : r324CCbrk k ≤ 1 :=
  r324SW_bracket_le_one k

theorem r324CCsym_nonneg (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    0 ≤ r324CCsym ρ ε k := by
  unfold r324CCsym; positivity

theorem r324CCsym_le_one (ρ : SmoothCutoff) (ε : ℝ) (k : Z4) :
    r324CCsym ρ ε k ≤ 1 :=
  pow_le_one₀ (norm_nonneg _) (ρ.norm_symbol_le_one ε k)

theorem r324CCwin_nonneg (ρ : SmoothCutoff) (ε : ℝ) (γ k : Z4) :
    0 ≤ r324CCwin ρ ε γ k :=
  mul_nonneg (r324CCsym_nonneg ρ ε k) (sq_nonneg _)

theorem r324CC_summable_win (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (γ : Z4) :
    Summable (r324CCwin ρ ε γ) :=
  r324SW_summable_translated_window ρ hε hε1 γ

theorem r324CCbrk_neg (k : Z4) : r324CCbrk (-k) = r324CCbrk k := by
  unfold r324CCbrk paperModeNormSq
  simp

theorem r324CCPair_nonneg (ρ : SmoothCutoff) (ε : ℝ) (u w : Fin 3)
    (p : Z4 × Z4) : 0 ≤ r324CCPair ρ ε u w p := by
  unfold r324CCPair r324CCsymWeight
  have h := r324CCsym_nonneg ρ ε
  exact mul_nonneg (mul_nonneg (mul_nonneg (h _) (h _)) (h _))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem r324CCPair_comm (ρ : SmoothCutoff) (ε : ℝ) (u w : Fin 3)
    (p : Z4 × Z4) :
    r324CCPair ρ ε u w p = r324CCPair ρ ε w u p := by
  unfold r324CCPair
  ring

/-! ### The three resonant shapes -/

/-- Product-form majorants of the paired lattice families, and the
value of the two window sums they iterate. -/
theorem r324CC_prodWin_bound (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {W : ℝ} (hW0 : 0 ≤ W)
    (hwin : ∀ γ : Z4, (∑' k : Z4, r324CCwin ρ ε γ k) ≤ W)
    (T : Z4 → Z4) :
    Summable (fun p : Z4 × Z4 =>
        r324CCwin ρ ε 0 p.1 * r324CCwin ρ ε (T p.1) p.2) ∧
      (∑' p : Z4 × Z4,
          r324CCwin ρ ε 0 p.1 * r324CCwin ρ ε (T p.1) p.2) ≤ W * W :=
  ⟨r324CC_summable_prod (fun k => r324CCwin_nonneg ρ ε 0 k)
      (fun k l => r324CCwin_nonneg ρ ε (T k) l)
      (r324CC_summable_win ρ hε hε1 0)
      (fun k => r324CC_summable_win ρ hε hε1 (T k)) hW0
      (fun k => hwin (T k)),
    r324CC_tsum_prod_le (fun k => r324CCwin_nonneg ρ ε 0 k)
      (fun k l => r324CCwin_nonneg ρ ε (T k) l)
      (r324CC_summable_win ρ hε hε1 0)
      (fun k => r324CC_summable_win ρ hε hε1 (T k)) hW0
      (hwin 0) (fun k => hwin (T k))⟩

theorem r324CC_prodWin_snd_bound (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {W : ℝ} (hW0 : 0 ≤ W)
    (hwin : ∀ γ : Z4, (∑' k : Z4, r324CCwin ρ ε γ k) ≤ W)
    (T : Z4 → Z4) :
    Summable (fun p : Z4 × Z4 =>
        r324CCwin ρ ε 0 p.2 * r324CCwin ρ ε (T p.2) p.1) ∧
      (∑' p : Z4 × Z4,
          r324CCwin ρ ε 0 p.2 * r324CCwin ρ ε (T p.2) p.1) ≤ W * W :=
  ⟨r324CC_summable_prod_snd (fun k => r324CCwin_nonneg ρ ε 0 k)
      (fun k l => r324CCwin_nonneg ρ ε (T k) l)
      (r324CC_summable_win ρ hε hε1 0)
      (fun k => r324CC_summable_win ρ hε hε1 (T k)) hW0
      (fun k => hwin (T k)),
    r324CC_tsum_prod_snd_le (fun k => r324CCwin_nonneg ρ ε 0 k)
      (fun k l => r324CCwin_nonneg ρ ε (T k) l)
      (r324CC_summable_win ρ hε hε1 0)
      (fun k => r324CC_summable_win ρ hε hε1 (T k)) hW0
      (hwin 0) (fun k => hwin (T k))⟩

theorem r324CC_le_of_majorant {F M : Z4 × Z4 → ℝ} {C : ℝ}
    (hF0 : ∀ p, 0 ≤ F p) (hFM : ∀ p, F p ≤ M p)
    (hM : Summable M) (hMb : (∑' p, M p) ≤ C) :
    Summable F ∧ (∑' p, F p) ≤ C := by
  have hFs : Summable F := hM.of_nonneg_of_le hF0 hFM
  exact ⟨hFs, (hFs.tsum_le_tsum hFM hM).trans hMb⟩

/-- **The paired lattice sums are logarithmic squared.**  Two doubled
propagators at distinct modes iterate into two translated windows, in
one of the three resonant shapes `(k₁,k₂)`, `(k₁,k₁+k₂)`, `(k₂,k₁+k₂)`. -/
theorem r324CC_pair_bound (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {W : ℝ} (hW0 : 0 ≤ W)
    (hwin : ∀ γ : Z4, (∑' k : Z4, r324CCwin ρ ε γ k) ≤ W)
    {u w : Fin 3} (huw : u ≠ w) :
    Summable (r324CCPair ρ ε u w) ∧
      (∑' p : Z4 × Z4, r324CCPair ρ ε u w p) ≤ W * W := by
  have hsym1 := r324CCsym_le_one ρ ε
  have hsym0 := r324CCsym_nonneg ρ ε
  -- the three shapes, each stated as `Pair = majorant * (third symbol)`
  have h01 : ∀ p : Z4 × Z4,
      r324CCPair ρ ε 0 1 p ≤
        r324CCwin ρ ε 0 p.1 * r324CCwin ρ ε ((fun _ => 0) p.1) p.2 := by
    intro p
    have hkey : r324CCPair ρ ε 0 1 p =
        (r324CCwin ρ ε 0 p.1 * r324CCwin ρ ε 0 p.2) *
          r324CCsym ρ ε (-(p.1 + p.2)) := by
      unfold r324CCPair r324CCsymWeight r324CCwin
      simp only [r324CCmode_zero, r324CCmode_one, add_zero]
      ring
    rw [hkey]
    exact mul_le_of_le_one_right
      (mul_nonneg (r324CCwin_nonneg ρ ε 0 p.1)
        (r324CCwin_nonneg ρ ε 0 p.2)) (hsym1 _)
  have h02 : ∀ p : Z4 × Z4,
      r324CCPair ρ ε 0 2 p ≤
        r324CCwin ρ ε 0 p.1 * r324CCwin ρ ε (id p.1) p.2 := by
    intro p
    have hkey : r324CCPair ρ ε 0 2 p =
        (r324CCwin ρ ε 0 p.1 * r324CCwin ρ ε p.1 p.2) *
          r324CCsym ρ ε (-(p.1 + p.2)) := by
      unfold r324CCPair r324CCsymWeight r324CCwin
      simp only [r324CCmode_zero, r324CCmode_two, add_zero,
        r324CCbrk_neg]
      rw [show p.1 + p.2 = p.2 + p.1 from add_comm _ _]
      ring
    rw [hkey]
    exact mul_le_of_le_one_right
      (mul_nonneg (r324CCwin_nonneg ρ ε 0 p.1)
        (r324CCwin_nonneg ρ ε p.1 p.2)) (hsym1 _)
  have h12 : ∀ p : Z4 × Z4,
      r324CCPair ρ ε 1 2 p ≤
        r324CCwin ρ ε 0 p.2 * r324CCwin ρ ε (id p.2) p.1 := by
    intro p
    have hkey : r324CCPair ρ ε 1 2 p =
        (r324CCwin ρ ε 0 p.2 * r324CCwin ρ ε p.2 p.1) *
          r324CCsym ρ ε (-(p.1 + p.2)) := by
      unfold r324CCPair r324CCsymWeight r324CCwin
      simp only [r324CCmode_one, r324CCmode_two, add_zero,
        r324CCbrk_neg]
      ring
    rw [hkey]
    exact mul_le_of_le_one_right
      (mul_nonneg (r324CCwin_nonneg ρ ε 0 p.2)
        (r324CCwin_nonneg ρ ε p.2 p.1)) (hsym1 _)
  have hcomm : ∀ u' w' : Fin 3,
      (Summable (r324CCPair ρ ε u' w') ∧
        (∑' p : Z4 × Z4, r324CCPair ρ ε u' w' p) ≤ W * W) →
      Summable (r324CCPair ρ ε w' u') ∧
        (∑' p : Z4 × Z4, r324CCPair ρ ε w' u' p) ≤ W * W := by
    intro u' w' h
    have hfun : r324CCPair ρ ε w' u' = r324CCPair ρ ε u' w' := by
      funext p
      exact (r324CCPair_comm ρ ε u' w' p).symm
    rw [hfun]
    exact h
  have b01 : Summable (r324CCPair ρ ε 0 1) ∧
      (∑' p : Z4 × Z4, r324CCPair ρ ε 0 1 p) ≤ W * W := by
    obtain ⟨hs, hb⟩ :=
      r324CC_prodWin_bound ρ hε hε1 hW0 hwin (fun _ => 0)
    exact r324CC_le_of_majorant
      (fun p => r324CCPair_nonneg ρ ε 0 1 p) h01 hs hb
  have b02 : Summable (r324CCPair ρ ε 0 2) ∧
      (∑' p : Z4 × Z4, r324CCPair ρ ε 0 2 p) ≤ W * W := by
    obtain ⟨hs, hb⟩ :=
      r324CC_prodWin_bound ρ hε hε1 hW0 hwin id
    exact r324CC_le_of_majorant
      (fun p => r324CCPair_nonneg ρ ε 0 2 p) h02 hs hb
  have b12 : Summable (r324CCPair ρ ε 1 2) ∧
      (∑' p : Z4 × Z4, r324CCPair ρ ε 1 2 p) ≤ W * W := by
    obtain ⟨hs, hb⟩ :=
      r324CC_prodWin_snd_bound ρ hε hε1 hW0 hwin id
    exact r324CC_le_of_majorant
      (fun p => r324CCPair_nonneg ρ ε 1 2 p) h12 hs hb
  fin_cases u <;> fin_cases w
  · exact absurd rfl huw
  · exact b01
  · exact b02
  · exact hcomm 0 1 b01
  · exact absurd rfl huw
  · exact b12
  · exact hcomm 0 2 b02
  · exact hcomm 1 2 b12
  · exact absurd rfl huw

/-- **The order-three calibration.**  Every one of the six order-three
entities collapses to a lattice sum of size `≤ (C·L)²`: the four
propagators `⟨k₁⟩⁻²⟨k₃⟩⁻²⟨k_{σ⁻¹1}⟩⁻²⟨k_{σ⁻¹3}⟩⁻²` always split, by the
arithmetic-geometric inequality, into two *doubled* propagators at two
distinct modes, and each doubled propagator is one critical translated
window. -/
theorem r324CC_latticeThree_le (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) {W : ℝ} (hW0 : 0 ≤ W)
    (hwin : ∀ γ : Z4, (∑' k : Z4, r324CCwin ρ ε γ k) ≤ W)
    {i j : Fin 3} (hij : i ≠ j) :
    r324CCLatticeThree ρ ε i j ≤ W * W := by
  obtain ⟨hs02, hb02⟩ :=
    r324CC_pair_bound ρ hε hε1 hW0 hwin (u := 0) (w := 2) (by decide)
  obtain ⟨hsij, hbij⟩ := r324CC_pair_bound ρ hε hε1 hW0 hwin hij
  set F : Z4 × Z4 → ℝ := fun p =>
    r324CCsymWeight ρ ε p *
      (r324CCbrk (r324CCmode 0 p) * r324CCbrk (r324CCmode 2 p) *
        (r324CCbrk (r324CCmode i p) * r324CCbrk (r324CCmode j p)))
    with hFdef
  have hsw : ∀ p : Z4 × Z4, 0 ≤ r324CCsymWeight ρ ε p := by
    intro p
    unfold r324CCsymWeight
    have h := r324CCsym_nonneg ρ ε
    exact mul_nonneg (mul_nonneg (h _) (h _)) (h _)
  have hF0 : ∀ p, 0 ≤ F p := by
    intro p
    rw [hFdef]
    exact mul_nonneg (hsw p)
      (mul_nonneg (mul_nonneg (r324CCbrk_nonneg _) (r324CCbrk_nonneg _))
        (mul_nonneg (r324CCbrk_nonneg _) (r324CCbrk_nonneg _)))
  have hpt : ∀ p : Z4 × Z4,
      F p ≤ (r324CCPair ρ ε 0 2 p + r324CCPair ρ ε i j p) / 2 := by
    intro p
    have hs := hsw p
    have hsq : (0 : ℝ) ≤
        (r324CCbrk (r324CCmode 0 p) * r324CCbrk (r324CCmode 2 p) -
          r324CCbrk (r324CCmode i p) * r324CCbrk (r324CCmode j p)) ^ 2 :=
      sq_nonneg _
    rw [hFdef]
    unfold r324CCPair
    nlinarith [hs, hsq]
  have hmaj : Summable fun p : Z4 × Z4 =>
      (r324CCPair ρ ε 0 2 p + r324CCPair ρ ε i j p) / 2 :=
    (hs02.add hsij).div_const 2
  have hFs : Summable F := hmaj.of_nonneg_of_le hF0 hpt
  calc
    r324CCLatticeThree ρ ε i j = ∑' p : Z4 × Z4, F p := rfl
    _ ≤ ∑' p : Z4 × Z4,
        (r324CCPair ρ ε 0 2 p + r324CCPair ρ ε i j p) / 2 :=
      hFs.tsum_le_tsum hpt hmaj
    _ = ((∑' p : Z4 × Z4, r324CCPair ρ ε 0 2 p) +
          ∑' p : Z4 × Z4, r324CCPair ρ ε i j p) / 2 := by
      rw [tsum_div_const, hs02.tsum_add hsij]
    _ ≤ (W * W + W * W) / 2 := by linarith
    _ = W * W := by ring

/-- **The `m = 3` entity table, in closed form.**  Uniformly in the
bijection, the collapsed order-three entity is `O(|log ε|²)` — exactly
`L^{m-1}` at `m = 3`.  All six entities carry the same order, so no
grading is available (or needed) at order three. -/
theorem r324CC_exists_latticeThree_le_log_sq (ρ : SmoothCutoff) :
    ∃ CL : ℝ, 0 < CL ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        ∀ i j : Fin 3, i ≠ j →
          r324CCLatticeThree ρ ε i j ≤ CL * |Real.log ε| ^ 2 := by
  obtain ⟨CT, hCT, hwin⟩ := r324SW_translated_window_le_log ρ
  refine ⟨CT * CT, by positivity, ?_⟩
  intro ε hε hε1 hlog i j hij
  have hW0 : (0 : ℝ) ≤ CT * |Real.log ε| := by positivity
  have hw : ∀ γ : Z4, (∑' k : Z4, r324CCwin ρ ε γ k) ≤
      CT * |Real.log ε| := fun γ => hwin hε hε1 hlog γ
  calc
    r324CCLatticeThree ρ ε i j ≤
        (CT * |Real.log ε|) * (CT * |Real.log ε|) :=
      r324CC_latticeThree_le ρ hε hε1 hW0 hw hij
    _ = CT * CT * |Real.log ε| ^ 2 := by ring

/-! ## From the order-three collapse to the capped ledger at `m = 3` -/

/-- **The order-three Parseval-collapse interface.** It says that the
physical entity integral is dominated by the
collapsed zero-sum lattice sum of its own propagator pattern, with a
pattern `(i,j) = (σ⁻¹1, σ⁻¹3)` of two distinct modes. -/
def R324CappedCrossCollapseThree (ρ : SmoothCutoff) (C : ℝ) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    ∀ e ∈ r324LedgerThreePermEntities 3,
      ∃ i j : Fin 3, i ≠ j ∧
        r324CappedCrossEntityIntegral ρ ε 3 e ≤
          C * r324CCLatticeThree ρ ε i j

/-- The collapse plus the proved calibration gives the ungraded
per-entity bound at order three. -/
theorem r324CappedCross_entityBoundAt_three_of_collapse
    {ρ : SmoothCutoff} {C : ℝ} (hC : 0 ≤ C)
    (h : R324CappedCrossCollapseThree ρ C) :
    ∃ K : ℝ, 2 ≤ K ∧ R324CappedCrossEntityBoundAt ρ K 3 := by
  obtain ⟨CL, hCL, hlat⟩ := r324CC_exists_latticeThree_le_log_sq ρ
  refine ⟨max 2 (C * CL), le_max_left _ _, ?_⟩
  intro ε hε hε1 hlog _ _ e he
  obtain ⟨i, j, hij, hle⟩ := h hε hε1 e he
  set K : ℝ := max 2 (C * CL) with hK
  have hK1 : (1 : ℝ) ≤ K := le_trans (by norm_num) (le_max_left _ _)
  have hKmax : C * CL ≤ K := by rw [hK]; exact le_max_right _ _
  have hKle : C * CL ≤ K ^ 3 := by
    refine le_trans hKmax ?_
    calc K = K ^ 1 := (pow_one K).symm
      _ ≤ K ^ 3 := pow_le_pow_right₀ hK1 (by norm_num)
  have hL0 : (0 : ℝ) ≤ |Real.log ε| ^ 2 := by positivity
  calc
    r324CappedCrossEntityIntegral ρ ε 3 e ≤
        C * r324CCLatticeThree ρ ε i j := hle
    _ ≤ C * (CL * |Real.log ε| ^ 2) :=
      mul_le_mul_of_nonneg_left (hlat hε hε1 hlog i j hij) hC
    _ = C * CL * |Real.log ε| ^ 2 := by ring
    _ ≤ K ^ 3 * |Real.log ε| ^ 2 :=
      mul_le_mul_of_nonneg_right hKle hL0
    _ = K ^ 3 * |Real.log ε| ^ (3 - 1) := by norm_num

/-- **The capped cross ledger at order three**, conditional only on the
order-three Parseval collapse: the six-entity count is geometric, so
the proved uniform `L²` calibration closes the whole fibre. -/
theorem r324CappedCrossLedgerAt_three_of_collapse
    {ρ : SmoothCutoff} {C : ℝ} (hC : 0 ≤ C)
    (h : R324CappedCrossCollapseThree ρ C) :
    ∃ K : ℝ, 0 ≤ K ∧ R324CappedCrossLedgerAt ρ K 3 := by
  obtain ⟨K, hK2, hent⟩ :=
    r324CappedCross_entityBoundAt_three_of_collapse hC h
  refine ⟨K * K, by nlinarith, ?_⟩
  exact r324CappedCrossLedgerAt_three_of_entityBoundAt hK2 hent

/-! ## Why the grading cannot be dropped beyond low orders -/

/-- **The flat grade is over budget at high capped orders.**  The
entity count is exactly `m!`, so the flat grade `m-1` — i.e. the
ungraded per-entity ceiling, which is *sharp* at the identity entity —
fails the graded-count clause `∑_e L^{grade e} ≤ C^m·L^{m-1}` for every
constant `C` at large `m`.  Hence any proof of the capped cross ledger
beyond the lowest orders must produce a genuinely non-constant
grade. -/
theorem r324CappedCross_flatGrade_over_budget (C : ℝ) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧
      C ^ m < ((r324LedgerThreePermEntities m).card : ℝ) := by
  obtain ⟨m, hm, hlt⟩ :=
    r324PermCross_exists_factorial_beats_pow (c := 1) (C₀ := 1)
      one_pos one_pos C N
  refine ⟨m, hm, ?_⟩
  rw [r324CappedCross_card_permEntities]
  simpa using hlt

end

end Anderson4D
