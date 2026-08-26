import Anderson4D.DetParametrix.Paper42_Moment.R324CollapseChain

/-!
# The general-order half-chain collapse on the physical product space

`R324CollapseChain` collapses a Green chain presented as an *iterated*
integral.  The physical fibre integrates its `2m` internal coordinates
against `Measure.pi`, so this file redoes the collapse natively on
`Measure.pi fun _ : Fin n => paperMeasure`, by recursion on `n`.

The recursion is the one supplied by
`MeasureTheory.measurePreserving_piFinSuccAbove` at the index `0`:
`v ↦ (v 0, Fin.tail v)` identifies `Measure.pi` over `Fin (n+1)` with
`paperMeasure.prod (Measure.pi over Fin n)`, so the *first* internal
coordinate is peeled as the outer integral and the tail is a chain of
length `n` hanging off the peeled point.  Hence

```
r324ColPiChain (n+1) q a v
  = e_{q₀}(v 0) · G(a - v 0) · r324ColPiChain n (q ∘ succ) (v 0) (tail v)
```

and the collapse
`r324Col_piChain_integral` says the whole `n`-fold integral is

`⟨q₀+…+q_{n-1}⟩⁻² ⟨q₁+…+q_{n-1}⟩⁻² ⋯ ⟨q_{n-1}⟩⁻² · e_{q₀+…+q_{n-1}}(a)`,

one bracket per *suffix* sum, and the single surviving character
carrying the total momentum out to the free head `a`.  On the
zero-momentum sector (which is what the external legs enforce, see
`r324Col_piChain_closed`) suffix sums are minus prefix sums and the
brackets are the paper's `⟨S₁⟩⁻²⋯⟨S_{n-1}⟩⁻²`, one per *internal*
edge.

Everything is uniform in `n`: no order is hardcoded.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The chain on a pi-space -/

/-- **The physical half chain over `Fin n → T4`.**  `a` is the free head
(an external point or the previously peeled coordinate); each internal
coordinate carries its covariance character and the Green edge joining
it to its predecessor. -/
def r324ColPiChain : (n : ℕ) → (ℕ → Z4) → T4 → (Fin n → T4) → ℂ
  | 0, _, _, _ => 1
  | (n + 1), q, a, v =>
      charT4 (q 0) (v 0) * ((greenFn (a - v 0) : ℝ) : ℂ) *
        r324ColPiChain n (fun j => q (j + 1)) (v 0) (Fin.tail v)

/-- The modulus of the half chain: the bare Green chain. -/
def r324ColPiAbs : (n : ℕ) → T4 → (Fin n → T4) → ℝ
  | 0, _, _ => 1
  | (n + 1), a, v =>
      greenFn (a - v 0) * r324ColPiAbs n (v 0) (Fin.tail v)

/-- The propagator product harvested by a half chain of `n` internal
coordinates: one bracket per suffix sum of the momenta. -/
def r324ColPiProp : (n : ℕ) → (ℕ → Z4) → ℝ
  | 0, _ => 1
  | (n + 1), q =>
      r324ColBrk (r324ColPartial q (n + 1)) *
        r324ColPiProp n (fun j => q (j + 1))

@[simp] theorem r324ColPiChain_zero (q : ℕ → Z4) (a : T4)
    (v : Fin 0 → T4) : r324ColPiChain 0 q a v = 1 := rfl

theorem r324ColPiChain_succ (n : ℕ) (q : ℕ → Z4) (a : T4)
    (v : Fin (n + 1) → T4) :
    r324ColPiChain (n + 1) q a v =
      charT4 (q 0) (v 0) * ((greenFn (a - v 0) : ℝ) : ℂ) *
        r324ColPiChain n (fun j => q (j + 1)) (v 0) (Fin.tail v) := rfl

@[simp] theorem r324ColPiAbs_zero (a : T4) (v : Fin 0 → T4) :
    r324ColPiAbs 0 a v = 1 := rfl

theorem r324ColPiAbs_succ (n : ℕ) (a : T4) (v : Fin (n + 1) → T4) :
    r324ColPiAbs (n + 1) a v =
      greenFn (a - v 0) * r324ColPiAbs n (v 0) (Fin.tail v) := rfl

@[simp] theorem r324ColPiProp_zero (q : ℕ → Z4) :
    r324ColPiProp 0 q = 1 := rfl

theorem r324ColPiProp_succ (n : ℕ) (q : ℕ → Z4) :
    r324ColPiProp (n + 1) q =
      r324ColBrk (r324ColPartial q (n + 1)) *
        r324ColPiProp n (fun j => q (j + 1)) := rfl

theorem r324ColPartial_succ' (q : ℕ → Z4) (n : ℕ) :
    r324ColPartial q (n + 1) =
      q 0 + r324ColPartial (fun j => q (j + 1)) n := by
  unfold r324ColPartial
  rw [Finset.sum_range_succ']
  exact add_comm _ _

theorem r324ColPiAbs_nonneg : ∀ (n : ℕ) (a : T4) (v : Fin n → T4),
    0 ≤ r324ColPiAbs n a v := by
  intro n
  induction n with
  | zero => intro a v; simp
  | succ n ih =>
      intro a v
      rw [r324ColPiAbs_succ]
      exact mul_nonneg (greenFn_nonneg _) (ih _ _)

theorem r324Col_norm_piChain : ∀ (n : ℕ) (q : ℕ → Z4) (a : T4)
    (v : Fin n → T4), ‖r324ColPiChain n q a v‖ = r324ColPiAbs n a v := by
  intro n
  induction n with
  | zero => intro q a v; simp
  | succ n ih =>
      intro q a v
      rw [r324ColPiChain_succ, r324ColPiAbs_succ, norm_mul, norm_mul,
        norm_charT4, ih, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (greenFn_nonneg _), one_mul]

/-! ## Measurability -/

theorem r324Col_measurable_tail (n : ℕ) :
    Measurable fun v : Fin (n + 1) → T4 => Fin.tail v :=
  measurable_pi_lambda _ fun j => measurable_pi_apply j.succ

theorem r324Col_measurable_piAbs : ∀ n : ℕ,
    Measurable fun p : T4 × (Fin n → T4) => r324ColPiAbs n p.1 p.2 := by
  intro n
  induction n with
  | zero =>
      simp only [r324ColPiAbs_zero]
      exact measurable_const
  | succ n ih =>
      have hzero : Measurable fun p : T4 × (Fin (n + 1) → T4) => p.2 0 :=
        (measurable_pi_apply 0).comp measurable_snd
      have hg : Measurable fun p : T4 × (Fin (n + 1) → T4) =>
          greenFn (p.1 - p.2 0) :=
        measurable_greenFn.comp (measurable_fst.sub hzero)
      have hpair : Measurable fun p : T4 × (Fin (n + 1) → T4) =>
          ((p.2 0 : T4), Fin.tail p.2) :=
        hzero.prodMk ((r324Col_measurable_tail n).comp measurable_snd)
      exact hg.mul (ih.comp hpair)

theorem r324Col_measurable_piChain : ∀ (n : ℕ) (q : ℕ → Z4),
    Measurable fun p : T4 × (Fin n → T4) => r324ColPiChain n q p.1 p.2 := by
  intro n
  induction n with
  | zero =>
      intro q
      simp only [r324ColPiChain_zero]
      exact measurable_const
  | succ n ih =>
      intro q
      have hzero : Measurable fun p : T4 × (Fin (n + 1) → T4) => p.2 0 :=
        (measurable_pi_apply 0).comp measurable_snd
      have hg : Measurable fun p : T4 × (Fin (n + 1) → T4) =>
          ((greenFn (p.1 - p.2 0) : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp
          (measurable_greenFn.comp (measurable_fst.sub hzero))
      have hc : Measurable fun p : T4 × (Fin (n + 1) → T4) =>
          charT4 (q 0) (p.2 0) :=
        (continuous_charT4 (q 0)).measurable.comp hzero
      have hpair : Measurable fun p : T4 × (Fin (n + 1) → T4) =>
          ((p.2 0 : T4), Fin.tail p.2) :=
        hzero.prodMk ((r324Col_measurable_tail n).comp measurable_snd)
      exact (hc.mul hg).mul ((ih fun j => q (j + 1)).comp hpair)

/-! ## Peeling one internal coordinate -/

/-- The head/tail splitting of `Fin (n+1) → T4`, as a measurable
equivalence. -/
def r324ColPiSucc (n : ℕ) : (Fin (n + 1) → T4) ≃ᵐ T4 × (Fin n → T4) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => T4) 0

theorem r324ColPiSucc_apply (n : ℕ) (v : Fin (n + 1) → T4) :
    r324ColPiSucc n v = (v 0, Fin.tail v) := rfl

theorem r324Col_measurePreserving_piSucc (n : ℕ) :
    MeasurePreserving (r324ColPiSucc n)
      (Measure.pi fun _ : Fin (n + 1) => paperMeasure)
      (paperMeasure.prod (Measure.pi fun _ : Fin n => paperMeasure)) :=
  measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => paperMeasure) (0 : Fin (n + 1))

theorem r324Col_pi_peel_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] (F : T4 × (Fin n → T4) → E)
    (hF : Integrable F
      (paperMeasure.prod (Measure.pi fun _ : Fin n => paperMeasure))) :
    Integrable (fun v : Fin (n + 1) → T4 => F (v 0, Fin.tail v))
      (Measure.pi fun _ : Fin (n + 1) => paperMeasure) := by
  have h := ((r324Col_measurePreserving_piSucc n).integrable_comp_emb
    (r324ColPiSucc n).measurableEmbedding (g := F)).mpr hF
  exact h

/-- **Peeling the head coordinate of a pi-integral.**  This is the one
measure-theoretic step of the recursion, uniform in `n`. -/
theorem r324Col_pi_peel {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : T4 × (Fin n → T4) → E)
    (hF : Integrable F
      (paperMeasure.prod (Measure.pi fun _ : Fin n => paperMeasure))) :
    (∫ v : Fin (n + 1) → T4, F (v 0, Fin.tail v)
        ∂(Measure.pi fun _ : Fin (n + 1) => paperMeasure)) =
      ∫ a : T4, ∫ w : Fin n → T4, F (a, w)
        ∂(Measure.pi fun _ : Fin n => paperMeasure) ∂paperMeasure := by
  have h1 :
      (∫ v : Fin (n + 1) → T4, F (r324ColPiSucc n v)
          ∂(Measure.pi fun _ : Fin (n + 1) => paperMeasure)) =
        ∫ p, F p
          ∂(paperMeasure.prod (Measure.pi fun _ : Fin n => paperMeasure)) :=
    (r324Col_measurePreserving_piSucc n).integral_comp' F
  rw [show (fun v : Fin (n + 1) → T4 => F (v 0, Fin.tail v)) =
      fun v : Fin (n + 1) → T4 => F (r324ColPiSucc n v) from rfl, h1]
  exact integral_prod F hF

/-! ## The bare chain has unit mass -/

theorem r324Col_integrable_greenFn_head (a : T4) :
    Integrable (fun b : T4 => greenFn (a - b)) paperMeasure := by
  have hEq : (fun b : T4 => greenFn (a - b)) =
      fun b : T4 => greenFn (b - a) := by
    funext b
    rw [show a - b = -(b - a) by abel, greenFn_memE.neg_invariant]
  rw [hEq]
  exact integrable_greenFn_sub a

/-- **The bare Green chain is a probability density in its internal
coordinates**, at every length.  This supplies every integrability side
condition of the collapse. -/
theorem r324Col_piAbs_integrable_integral : ∀ (n : ℕ) (a : T4),
    Integrable (r324ColPiAbs n a)
        (Measure.pi fun _ : Fin n => paperMeasure) ∧
      (∫ v : Fin n → T4, r324ColPiAbs n a v
        ∂(Measure.pi fun _ : Fin n => paperMeasure)) = 1 := by
  intro n
  induction n with
  | zero =>
      intro a
      have hpi : (Measure.pi fun _ : Fin 0 => paperMeasure) =
          Measure.dirac (fun i => isEmptyElim i) :=
        Measure.pi_of_empty _ _
      have hfun : r324ColPiAbs 0 a = fun _ : Fin 0 → T4 => (1 : ℝ) := rfl
      constructor
      · rw [hfun, hpi]
        exact integrable_const 1
      · rw [hfun, hpi]
        simp
  | succ n ih =>
      intro a
      set F : T4 × (Fin n → T4) → ℝ :=
        fun p => greenFn (a - p.1) * r324ColPiAbs n p.1 p.2 with hFdef
      have hmeas : Measurable F := by
        rw [hFdef]
        exact (measurable_greenFn.comp (measurable_const.sub measurable_fst)).mul
          (r324Col_measurable_piAbs n)
      have hslice : ∀ b : T4,
          Integrable (fun w : Fin n → T4 => F (b, w))
            (Measure.pi fun _ : Fin n => paperMeasure) := by
        intro b
        have hb : (fun w : Fin n → T4 => F (b, w)) =
            fun w : Fin n → T4 => greenFn (a - b) * r324ColPiAbs n b w := rfl
        rw [hb]
        exact ((ih b).1).const_mul _
      have hnormval : ∀ b : T4,
          (∫ w : Fin n → T4, ‖F (b, w)‖
              ∂(Measure.pi fun _ : Fin n => paperMeasure)) =
            greenFn (a - b) := by
        intro b
        have hpt : ∀ w : Fin n → T4,
            ‖F (b, w)‖ = greenFn (a - b) * r324ColPiAbs n b w := by
          intro w
          rw [hFdef]
          simp only [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (greenFn_nonneg _),
            abs_of_nonneg (r324ColPiAbs_nonneg n b w)]
        simp only [hpt]
        rw [integral_const_mul, (ih b).2, mul_one]
      have hF : Integrable F
          (paperMeasure.prod (Measure.pi fun _ : Fin n => paperMeasure)) := by
        refine (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
          ⟨Filter.Eventually.of_forall hslice, ?_⟩
        have hEq : (fun b : T4 =>
            ∫ w : Fin n → T4, ‖F (b, w)‖
              ∂(Measure.pi fun _ : Fin n => paperMeasure)) =
              fun b : T4 => greenFn (a - b) := by
          funext b; exact hnormval b
        rw [hEq]
        exact r324Col_integrable_greenFn_head a
      have hchain : r324ColPiAbs (n + 1) a =
          fun v : Fin (n + 1) → T4 => F (v 0, Fin.tail v) := rfl
      have hinner : ∀ b : T4,
          (∫ w : Fin n → T4, F (b, w)
              ∂(Measure.pi fun _ : Fin n => paperMeasure)) =
            greenFn (a - b) := by
        intro b
        have hb : (fun w : Fin n → T4 => F (b, w)) =
            fun w : Fin n → T4 => greenFn (a - b) * r324ColPiAbs n b w := rfl
        rw [hb, integral_const_mul, (ih b).2, mul_one]
      constructor
      · rw [hchain]
        exact r324Col_pi_peel_integrable F hF
      · rw [hchain, r324Col_pi_peel F hF]
        simp only [hinner]
        exact integral_greenFn_shift_left a

theorem r324Col_piChain_integrable (n : ℕ) (q : ℕ → Z4) (a : T4) :
    Integrable (r324ColPiChain n q a)
      (Measure.pi fun _ : Fin n => paperMeasure) := by
  refine Integrable.mono' ((r324Col_piAbs_integrable_integral n a).1)
    ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact ((r324Col_measurable_piChain n q).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact le_of_eq (r324Col_norm_piChain n q a v)

/-! ## The general-order half-chain collapse -/

/-- **The half-chain collapse, at every order.**  The full `n`-fold
physical integral of a Green chain against one covariance character per
internal coordinate is the product of the brackets of the *suffix* sums
of the momenta, times the single surviving character carrying the total
momentum to the free head.

This is the general-`m` replacement for the hardcoded `m ≤ 2` collapses
`integral_integral_greenFn_etaPair_eq_tsum` and
`integral_prod_greenFn_mul_tsum_crossModes`.  The proof is a recursion
on `n`: peel the head coordinate
(`r324Col_pi_peel`), evaluate the exposed one-variable Green–character
integral (`integral_charT4_mul_greenFn_shift`), and merge the migrated
character with the next one (`charT4_add`). -/
theorem r324Col_piChain_integral : ∀ (n : ℕ) (q : ℕ → Z4) (a : T4),
    (∫ v : Fin n → T4, r324ColPiChain n q a v
        ∂(Measure.pi fun _ : Fin n => paperMeasure)) =
      ((r324ColPiProp n q : ℝ) : ℂ) * charT4 (r324ColPartial q n) a := by
  intro n
  induction n with
  | zero =>
      intro q a
      have hpi : (Measure.pi fun _ : Fin 0 => paperMeasure) =
          Measure.dirac (fun i => isEmptyElim i) :=
        Measure.pi_of_empty _ _
      have hfun : r324ColPiChain 0 q a = fun _ : Fin 0 → T4 => (1 : ℂ) := rfl
      rw [hfun, hpi, r324ColPiProp_zero, r324ColPartial_zero,
        r324Col_charT4_zero]
      simp
  | succ n ih =>
      intro q a
      set q' : ℕ → Z4 := fun j => q (j + 1) with hq'
      set F : T4 × (Fin n → T4) → ℂ :=
        fun p => charT4 (q 0) p.1 * ((greenFn (a - p.1) : ℝ) : ℂ) *
          r324ColPiChain n q' p.1 p.2 with hFdef
      have hmeas : Measurable F := by
        rw [hFdef]
        refine (((continuous_charT4 (q 0)).measurable.comp measurable_fst).mul
          (Complex.measurable_ofReal.comp
            (measurable_greenFn.comp (measurable_const.sub measurable_fst)))).mul ?_
        exact r324Col_measurable_piChain n q'
      have hnorm : ∀ (b : T4) (w : Fin n → T4),
          ‖F (b, w)‖ = greenFn (a - b) * r324ColPiAbs n b w := by
        intro b w
        rw [hFdef]
        simp only [norm_mul, norm_charT4, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (greenFn_nonneg _),
          r324Col_norm_piChain]
      have hslice : ∀ b : T4,
          Integrable (fun w : Fin n → T4 => F (b, w))
            (Measure.pi fun _ : Fin n => paperMeasure) := by
        intro b
        have hb : (fun w : Fin n → T4 => F (b, w)) =
            fun w : Fin n → T4 =>
              (charT4 (q 0) b * ((greenFn (a - b) : ℝ) : ℂ)) *
                r324ColPiChain n q' b w := rfl
        rw [hb]
        exact (r324Col_piChain_integrable n q' b).const_mul _
      have hF : Integrable F
          (paperMeasure.prod (Measure.pi fun _ : Fin n => paperMeasure)) := by
        refine (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
          ⟨Filter.Eventually.of_forall hslice, ?_⟩
        have hEq : (fun b : T4 =>
            ∫ w : Fin n → T4, ‖F (b, w)‖
              ∂(Measure.pi fun _ : Fin n => paperMeasure)) =
              fun b : T4 => greenFn (a - b) := by
          funext b
          simp only [hnorm b]
          rw [integral_const_mul, (r324Col_piAbs_integrable_integral n b).2,
            mul_one]
        rw [hEq]
        exact r324Col_integrable_greenFn_head a
      have hchain : r324ColPiChain (n + 1) q a =
          fun v : Fin (n + 1) → T4 => F (v 0, Fin.tail v) := rfl
      have hinner : ∀ b : T4,
          (∫ w : Fin n → T4, F (b, w)
              ∂(Measure.pi fun _ : Fin n => paperMeasure)) =
            ((r324ColPiProp n q' : ℝ) : ℂ) *
              (charT4 (r324ColPartial q (n + 1)) b *
                ((greenFn (a - b) : ℝ) : ℂ)) := by
        intro b
        have hb : (fun w : Fin n → T4 => F (b, w)) =
            fun w : Fin n → T4 =>
              (charT4 (q 0) b * ((greenFn (a - b) : ℝ) : ℂ)) *
                r324ColPiChain n q' b w := rfl
        rw [hb, integral_const_mul, ih q' b, r324ColPartial_succ' q n,
          charT4_add]
        ring
      rw [hchain, r324Col_pi_peel F hF]
      simp only [hinner]
      rw [integral_const_mul, integral_charT4_mul_greenFn_shift,
        r324ColPiProp_succ, r324ColBrk]
      push_cast
      ring

/-- **The closed half chain: momentum conservation.**  Integrating the
free head against its own external Green leg (unit mass) leaves the
Kronecker delta of total momentum: the vertex constraint that the
`m ≤ 2` files produced coordinate by coordinate. -/
theorem r324Col_piChain_closed (n : ℕ) (q : ℕ → Z4) :
    (∫ a : T4, ∫ v : Fin n → T4, r324ColPiChain n q a v
        ∂(Measure.pi fun _ : Fin n => paperMeasure) ∂paperMeasure) =
      if r324ColPartial q n = 0 then
        ((r324ColPiProp n q * (2 * Real.pi) ^ dim : ℝ) : ℂ)
      else 0 := by
  rw [integral_congr_ae
    (Filter.Eventually.of_forall fun a => r324Col_piChain_integral n q a),
    integral_const_mul, integral_charT4_paper]
  by_cases h : r324ColPartial q n = 0
  · rw [if_pos h, if_pos h]
    push_cast
    ring
  · rw [if_neg h, if_neg h, mul_zero]

end

end Anderson4D
