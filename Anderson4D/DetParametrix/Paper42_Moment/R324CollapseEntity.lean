import Anderson4D.DetParametrix.Paper42_Moment.R324CollapsePi
import Anderson4D.DetParametrix.Paper42_Moment.R324CappedCrossLedgerProof

/-!
# The general-order entity lattice pattern and its AM–GM grade

`R324CollapsePi` collapses one half chain at every order.  A pure-cross
entity has *two* half chains sharing the same `m` cross momenta: the
left chain reads them in identity order, the right chain in the order
of the bijection.  So the collapsed entity of the bijection `σ` is the
zero-sum lattice sum whose summand is

`W_τ(q) = ∏ᵢ ‖ρ̂(εqᵢ)‖² · P(q) · P(q∘τ)`, `τ = σ⁻¹`,

where `P(q) = ∏ⱼ ⟨qⱼ+…+q_{m-1}⟩⁻²` is exactly the propagator product
harvested by `r324Col_piChain_integral` (suffix sums; on the zero-sum
sector these are the paper's prefix sums up to sign).  This file
defines that pattern for arbitrary `m` and arbitrary `σ`, and proves
what the arithmetic-geometric argument gives.

## The grade the AM–GM argument gives is flat

`ab ≤ (a²+b²)/2` applied to `a = P(q)`, `b = P(q∘τ)` splits every
entity into two *doubled* patterns
(`r324ColLatWeight_le_doubled_avg`), and the relabelling `q ↦ q∘τ`
is a measure-preserving bijection of the lattice configuration space
under which the symbol weight is invariant
(`r324Col_tsum_doubled_perm`).  Hence **at every order and for every
bijection the AM–GM bound is the identity entity's own bound**
(`r324Col_tsum_latWeight_le`): the argument is uniform in `σ` and
therefore produces exactly the *flat* grade `m-1`.

That is sharp for the identity entity, and by
`r324CappedCross_flatGrade_over_budget` it is over budget for large
`m`.  So this file also delimits precisely what is missing for the
graded clause: a mechanism that is *not* invariant under relabelling
the cross momenta, i.e. one that sees the interaction between the two
suffix-sum families rather than each separately.  At `m = 3` the flat
grade is enough (`3! ≤ 2³`), which is why order three closes on the
calibration alone.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The lattice configuration of an entity -/

/-- Extend a finite momentum assignment to the sequence consumed by the
chain collapse. -/
def r324ColExtend {m : ℕ} (q : Fin m → Z4) : ℕ → Z4 :=
  fun j => if h : j < m then q ⟨j, h⟩ else 0

/-- The symbol weight `∏ᵢ ‖ρ̂(εqᵢ)‖²` of the `m` cross legs. -/
def r324ColLatSym (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (q : Fin m → Z4) : ℝ :=
  ∏ i : Fin m, ‖ρ.symbol ε (q i)‖ ^ 2

/-- The propagator product of one half chain, read in the order `q`:
the suffix-sum brackets delivered by `r324Col_piChain_integral`. -/
def r324ColLatProp {m : ℕ} (q : Fin m → Z4) : ℝ :=
  r324ColPiProp m (r324ColExtend q)

/-- **The lattice summand of the pure-cross entity `σ` at order `m`**:
symbol weights times the two half-chain propagator products, the left
one in identity order and the right one in the order `τ = σ⁻¹`. -/
def r324ColLatWeight (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (τ : Equiv.Perm (Fin m)) (q : Fin m → Z4) : ℝ :=
  r324ColLatSym ρ ε q * (r324ColLatProp q * r324ColLatProp (q ∘ τ))

/-- The *doubled* pattern: the same symbol weight against a squared
propagator product.  This is the resonant shape the arithmetic-geometric
split produces. -/
def r324ColLatDoubled (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (q : Fin m → Z4) : ℝ :=
  r324ColLatSym ρ ε q * r324ColLatProp q ^ 2

theorem r324ColLatSym_nonneg (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (q : Fin m → Z4) : 0 ≤ r324ColLatSym ρ ε q :=
  Finset.prod_nonneg fun _ _ => by positivity

theorem r324ColPiProp_nonneg : ∀ (n : ℕ) (q : ℕ → Z4),
    0 ≤ r324ColPiProp n q := by
  intro n
  induction n with
  | zero => intro q; rw [r324ColPiProp_zero]; norm_num
  | succ n ih =>
      intro q
      rw [r324ColPiProp_succ]
      exact mul_nonneg (r324ColBrk_nonneg _) (ih _)

theorem r324ColLatProp_nonneg {m : ℕ} (q : Fin m → Z4) :
    0 ≤ r324ColLatProp q :=
  r324ColPiProp_nonneg m (r324ColExtend q)

theorem r324ColLatWeight_nonneg (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (τ : Equiv.Perm (Fin m)) (q : Fin m → Z4) :
    0 ≤ r324ColLatWeight ρ ε τ q :=
  mul_nonneg (r324ColLatSym_nonneg ρ ε q)
    (mul_nonneg (r324ColLatProp_nonneg q) (r324ColLatProp_nonneg _))

theorem r324ColLatDoubled_nonneg (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (q : Fin m → Z4) : 0 ≤ r324ColLatDoubled ρ ε q :=
  mul_nonneg (r324ColLatSym_nonneg ρ ε q) (sq_nonneg _)

/-! ## The arithmetic-geometric split, uniformly in the order -/

/-- **The AM–GM split at every order and every bijection.**  The mixed
propagator pattern of `σ` is dominated by the average of the two
doubled patterns: the identity one and the `σ`-relabelled one. -/
theorem r324ColLatWeight_le_doubled_avg (ρ : SmoothCutoff) (ε : ℝ)
    {m : ℕ} (τ : Equiv.Perm (Fin m)) (q : Fin m → Z4) :
    r324ColLatWeight ρ ε τ q ≤
      (r324ColLatDoubled ρ ε q +
        r324ColLatSym ρ ε q * r324ColLatProp (q ∘ τ) ^ 2) / 2 := by
  unfold r324ColLatWeight r324ColLatDoubled
  have hs := r324ColLatSym_nonneg ρ ε q
  have hsq : (0 : ℝ) ≤ (r324ColLatProp q - r324ColLatProp (q ∘ τ)) ^ 2 :=
    sq_nonneg _
  nlinarith [hs, hsq]

/-! ## Relabelling invariance -/

/-- **The zero-sum sector.**  The two external Green legs of each half
chain integrate to unit mass and turn the last surviving character into
the Kronecker delta `q₀+…+q_{m-1} = 0` (`r324Col_piChain_closed`), so
the collapsed entity is a sum over this sector only.  It carries `m-1`
free momenta, which is why the flat grade is `m-1` and not `m`. -/
def R324ColZeroSum (m : ℕ) : Type :=
  {q : Fin m → Z4 // ∑ i, q i = 0}

instance (m : ℕ) : CoeFun (R324ColZeroSum m) (fun _ => Fin m → Z4) :=
  ⟨Subtype.val⟩

/-- Reordering the cross momenta is a bijection of the lattice
configuration space. -/
def r324ColReindex {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    (Fin m → Z4) ≃ (Fin m → Z4) :=
  Equiv.arrowCongr τ.symm (Equiv.refl Z4)

@[simp] theorem r324ColReindex_apply {m : ℕ} (τ : Equiv.Perm (Fin m))
    (q : Fin m → Z4) : r324ColReindex τ q = q ∘ τ := by
  funext i
  rfl

/-- Reordering preserves momentum conservation, so it restricts to the
zero-sum sector. -/
def r324ColReindexZero {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    R324ColZeroSum m ≃ R324ColZeroSum m :=
  Equiv.subtypeEquiv (r324ColReindex τ) (by
    intro q
    rw [r324ColReindex_apply]
    have h : (∑ i, (q ∘ τ) i) = ∑ i, q i :=
      Equiv.sum_comp τ (fun i => q i)
    rw [h])

@[simp] theorem r324ColReindexZero_val {m : ℕ} (τ : Equiv.Perm (Fin m))
    (q : R324ColZeroSum m) :
    ((r324ColReindexZero τ q : R324ColZeroSum m) : Fin m → Z4) =
      (q : Fin m → Z4) ∘ τ := rfl

/-- The symbol weight is symmetric in the cross momenta. -/
theorem r324ColLatSym_comp (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (τ : Equiv.Perm (Fin m)) (q : Fin m → Z4) :
    r324ColLatSym ρ ε (q ∘ τ) = r324ColLatSym ρ ε q := by
  unfold r324ColLatSym
  exact Equiv.prod_comp τ fun i => ‖ρ.symbol ε (q i)‖ ^ 2

/-- **The relabelled doubled sum is the identity doubled sum.**  This is
the exact reason the arithmetic-geometric argument cannot see the
grading: it is invariant under permuting the cross momenta. -/
theorem r324Col_tsum_doubled_perm (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (τ : Equiv.Perm (Fin m)) :
    (∑' q : R324ColZeroSum m,
        r324ColLatSym ρ ε (q : Fin m → Z4) *
          r324ColLatProp ((q : Fin m → Z4) ∘ τ) ^ 2) =
      ∑' q : R324ColZeroSum m,
        r324ColLatDoubled ρ ε (q : Fin m → Z4) := by
  have hEq : ∀ q : R324ColZeroSum m,
      r324ColLatSym ρ ε (q : Fin m → Z4) *
          r324ColLatProp ((q : Fin m → Z4) ∘ τ) ^ 2 =
        r324ColLatDoubled ρ ε
          ((r324ColReindexZero τ q : R324ColZeroSum m) : Fin m → Z4) := by
    intro q
    rw [r324ColReindexZero_val]
    unfold r324ColLatDoubled
    rw [r324ColLatSym_comp]
  simp only [hEq]
  exact (r324ColReindexZero τ).tsum_eq
    (fun q : R324ColZeroSum m => r324ColLatDoubled ρ ε (q : Fin m → Z4))

theorem r324Col_summable_doubled_perm (ρ : SmoothCutoff) (ε : ℝ)
    {m : ℕ} (τ : Equiv.Perm (Fin m))
    (h : Summable fun q : R324ColZeroSum m =>
      r324ColLatDoubled ρ ε (q : Fin m → Z4)) :
    Summable fun q : R324ColZeroSum m =>
      r324ColLatSym ρ ε (q : Fin m → Z4) *
        r324ColLatProp ((q : Fin m → Z4) ∘ τ) ^ 2 := by
  have hEq : (fun q : R324ColZeroSum m =>
      r324ColLatSym ρ ε (q : Fin m → Z4) *
        r324ColLatProp ((q : Fin m → Z4) ∘ τ) ^ 2) =
        fun q : R324ColZeroSum m =>
          r324ColLatDoubled ρ ε
            ((r324ColReindexZero τ q : R324ColZeroSum m) : Fin m → Z4) := by
    funext q
    rw [r324ColReindexZero_val]
    unfold r324ColLatDoubled
    rw [r324ColLatSym_comp]
  rw [hEq]
  exact (r324ColReindexZero τ).summable_iff.mpr h

/-! ## The grade the argument delivers -/

/-- **Every entity is bounded by the identity entity's doubled sum, at
every order.**  This is the exact output of the arithmetic-geometric
argument at general `m` and general `σ`: the *flat* grade.  It is sharp
for `σ = id` and, by `r324CappedCross_flatGrade_over_budget`, cannot by
itself fund the graded-count clause at large `m`. -/
theorem r324Col_tsum_latWeight_le (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (τ : Equiv.Perm (Fin m))
    (h : Summable fun q : R324ColZeroSum m =>
      r324ColLatDoubled ρ ε (q : Fin m → Z4)) :
    (Summable fun q : R324ColZeroSum m =>
        r324ColLatWeight ρ ε τ (q : Fin m → Z4)) ∧
      (∑' q : R324ColZeroSum m,
          r324ColLatWeight ρ ε τ (q : Fin m → Z4)) ≤
        ∑' q : R324ColZeroSum m,
          r324ColLatDoubled ρ ε (q : Fin m → Z4) := by
  have hperm := r324Col_summable_doubled_perm ρ ε τ h
  have hmaj : Summable fun q : R324ColZeroSum m =>
      (r324ColLatDoubled ρ ε (q : Fin m → Z4) +
        r324ColLatSym ρ ε (q : Fin m → Z4) *
          r324ColLatProp ((q : Fin m → Z4) ∘ τ) ^ 2) / 2 :=
    (h.add hperm).div_const 2
  have hpt : ∀ q : R324ColZeroSum m,
      r324ColLatWeight ρ ε τ (q : Fin m → Z4) ≤
        (r324ColLatDoubled ρ ε (q : Fin m → Z4) +
          r324ColLatSym ρ ε (q : Fin m → Z4) *
            r324ColLatProp ((q : Fin m → Z4) ∘ τ) ^ 2) / 2 :=
    fun q => r324ColLatWeight_le_doubled_avg ρ ε τ (q : Fin m → Z4)
  have hs : Summable fun q : R324ColZeroSum m =>
      r324ColLatWeight ρ ε τ (q : Fin m → Z4) :=
    hmaj.of_nonneg_of_le
      (fun q => r324ColLatWeight_nonneg ρ ε τ (q : Fin m → Z4)) hpt
  refine ⟨hs, ?_⟩
  calc
    (∑' q : R324ColZeroSum m,
        r324ColLatWeight ρ ε τ (q : Fin m → Z4)) ≤
        ∑' q : R324ColZeroSum m,
          (r324ColLatDoubled ρ ε (q : Fin m → Z4) +
            r324ColLatSym ρ ε (q : Fin m → Z4) *
              r324ColLatProp ((q : Fin m → Z4) ∘ τ) ^ 2) / 2 :=
      hs.tsum_le_tsum hpt hmaj
    _ = ((∑' q : R324ColZeroSum m,
            r324ColLatDoubled ρ ε (q : Fin m → Z4)) +
          ∑' q : R324ColZeroSum m,
            r324ColLatSym ρ ε (q : Fin m → Z4) *
              r324ColLatProp ((q : Fin m → Z4) ∘ τ) ^ 2) / 2 := by
      rw [tsum_div_const, h.tsum_add hperm]
    _ = ∑' q : R324ColZeroSum m,
          r324ColLatDoubled ρ ε (q : Fin m → Z4) := by
      rw [r324Col_tsum_doubled_perm ρ ε τ]
      ring

/-! ## General-order analytic inputs -/

/-- **The general-order physical→lattice collapse**, as a named Prop:
the physical entity integral is dominated by the zero-sum lattice sum
of its own suffix-bracket pattern.  This is what
`r324Col_piChain_integral` and `r324Col_piChain_closed` evaluate half
by half; assembling the two halves needs the covariance Fourier
expansion and one Tonelli interchange between the mode sum and the
`2m+4` physical integrations. -/
def R324ColPhysicalCollapseAt (ρ : SmoothCutoff) (C : ℝ) (m : ℕ) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    ∀ e ∈ r324LedgerThreePermEntities m,
      ∃ τ : Equiv.Perm (Fin m),
        r324CappedCrossEntityIntegral ρ ε m e ≤
          C ^ m * ∑' q : R324ColZeroSum m,
            r324ColLatWeight ρ ε τ (q : Fin m → Z4)

/-- **The doubled window budget**: the identity-pattern lattice sum,
`m-1` free momenta each covered by one critical quartic window, is
`D^m·L^{m-1}`.  This is the general-order form of the proved
translated-window iteration `r324SW_translated_window_le_log`. -/
def R324ColDoubledBudgetAt (ρ : SmoothCutoff) (D : ℝ) (m : ℕ) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
    (Summable fun q : R324ColZeroSum m =>
        r324ColLatDoubled ρ ε (q : Fin m → Z4)) ∧
      (∑' q : R324ColZeroSum m,
          r324ColLatDoubled ρ ε (q : Fin m → Z4)) ≤
        D ^ m * |Real.log ε| ^ (m - 1)

/-- **The general-order per-entity ledger.**  The collapse plus the
doubled window budget give the ungraded per-entity bound at *every*
order, with the flat grade `m-1` that the arithmetic-geometric argument
delivers uniformly in the bijection. -/
theorem r324Col_entityBoundAt_of_collapse {ρ : SmoothCutoff} {C D : ℝ}
    {m : ℕ} (hC : 0 ≤ C)
    (hcol : R324ColPhysicalCollapseAt ρ C m)
    (hbud : R324ColDoubledBudgetAt ρ D m) :
    R324CappedCrossEntityBoundAt ρ (C * D) m := by
  intro ε hε hε1 hlog _ _ e he
  obtain ⟨τ, hτ⟩ := hcol hε hε1 e he
  obtain ⟨hsum, hle⟩ := hbud hε hε1 hlog
  have hCm : (0 : ℝ) ≤ C ^ m := pow_nonneg hC m
  calc
    r324CappedCrossEntityIntegral ρ ε m e ≤
        C ^ m * ∑' q : R324ColZeroSum m,
          r324ColLatWeight ρ ε τ (q : Fin m → Z4) := hτ
    _ ≤ C ^ m * ∑' q : R324ColZeroSum m,
          r324ColLatDoubled ρ ε (q : Fin m → Z4) :=
      mul_le_mul_of_nonneg_left
        (r324Col_tsum_latWeight_le ρ ε τ hsum).2 hCm
    _ ≤ C ^ m * (D ^ m * |Real.log ε| ^ (m - 1)) :=
      mul_le_mul_of_nonneg_left hle hCm
    _ = (C * D) ^ m * |Real.log ε| ^ (m - 1) := by
      rw [mul_pow]; ring

/-- **Order three closes on the general machine.**  At `m = 3` the
entity count `3! = 6` is itself geometric, so the flat grade suffices
and the capped cross ledger at order three follows from the two
general-order inputs alone. -/
theorem r324Col_cappedCrossLedgerAt_three {ρ : SmoothCutoff} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcol : R324ColPhysicalCollapseAt ρ C 3)
    (hbud : R324ColDoubledBudgetAt ρ D 3) :
    ∃ K : ℝ, 0 ≤ K ∧ R324CappedCrossLedgerAt ρ K 3 := by
  have hCD : (0 : ℝ) ≤ C * D := mul_nonneg hC hD
  have hent : R324CappedCrossEntityBoundAt ρ (C * D) 3 :=
    r324Col_entityBoundAt_of_collapse hC hcol hbud
  have hmono : R324CappedCrossEntityBoundAt ρ (max 2 (C * D)) 3 := by
    intro ε hε hε1 hlog hm3 hcap e he
    refine (hent hε hε1 hlog hm3 hcap e he).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (abs_nonneg _) _)
    exact pow_le_pow_left₀ hCD (le_max_right _ _) 3
  refine ⟨max 2 (C * D) * max 2 (C * D), ?_, ?_⟩
  · have : (0 : ℝ) ≤ max 2 (C * D) :=
      le_trans (by norm_num) (le_max_left _ _)
    positivity
  · exact r324CappedCrossLedgerAt_three_of_entityBoundAt
      (le_max_left _ _) hmono

end

end Anderson4D
