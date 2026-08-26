import Anderson4D.DetParametrix.Paper42_Moment.R324BracketCoreFourier

/-!
# The endpoint harvest: integrating the external character before the norm

This file carries out, for an **arbitrary** finite entity set `F` and with
the entity sum kept **inside**, the first of the four external
integrations of paper (4.16)–(4.20).

## The mechanism

In `detIntegrand ρ ε m κ (assemble x y v)` the external point `x` sits in
slot `0` of the assembled tuple and is touched by exactly one factor: the
head chain edge `greenFn (xt 0 - xt 1) = greenFn (x - v 0)`.  That edge is
never excluded, because the excluded chain slots are the numbers
`p.2.val + 1 ≥ 1` of the extracted pairs (`detIntegrand_head_not_excluded`);
every other factor — the remaining chain edges, the renormalization
difference factors and the covariance factors — reads the tuple only at
slots `≥ 1` (`r324DetHeadless_congr`).  Hence

`detIntegrand ρ ε m κ (assemble x y v) = greenFn (x - v 0) * (x-free)`
  (`detIntegrand_assemble_eq_head_mul_headless`),

and the head factor is **the same for every entity**: it does not depend on
`κ`, on the right copy, or on the cross pairing.  So it factors out of the
entity sum (`r324CMFlatCore_eq_head_mul_headless`) and the `x`-integration
of the summed core is one Green Fourier coefficient:

`∫ charT4 α x · core(x, q) dx = translatedGreenMode α (v 0) · headless(q)`
  (`integral_charT4_mul_r324CMFlatCore`),

whose modulus is exactly `⟨α⟩⁻²` — `norm_translatedGreenMode` — *no matter
how large the entity set is*.  This is the harvest the mode-independence
theorem `r324CMFlatDensity_modes_indep` says must happen before any norm is
taken: the decay is produced by the oscillation of `charT4 α`, and taking
the modulus of the integrand first destroys it.

The same computation applies verbatim to `z`, the head of the right copy
(`assemble z w (v ∘ rightMomentIndex)` has the identical head edge
`greenFn (z - v (rightMomentIndex 0))`), giving a second factor `⟨α⟩⁻²`;
together they are exactly `paperFourthOrderModeDecay α`, the `α` half of
`r324EndpointLoss`.  The `y` and `w` endpoints sit at the *last*
chain slot, which the extracted pairs may replace by a difference factor,
so their harvest is a difference of two translated Green modes rather than
one — the proved `r324EndpointCoefficient` shape.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Removing the head chain edge -/

/-- `detIntegrand` with the head chain edge `greenFn (xt 0 - xt 1)`
deleted.  Every remaining factor reads `xt` only at slots `≥ 1`. -/
def r324DetHeadless
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) : ℝ :=
  (∏ e : Fin m,
      if (e.succ : Fin (m + 1)).val ∈
          ((extract κ).map fun p => p.2.val + 1) then 1
      else greenFn (xt (e.succ : Fin (m + 1)).castSucc -
        xt (e.succ : Fin (m + 1)).succ)) *
    ((extract κ).map (diffFactor xt)).prod *
    ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
      ρ.etaEpsT4 ε (xt (varIdx i) - xt (varIdx (κ i)))

/-- The head chain slot `0` is never excluded: the excluded slots are the
numbers `p.2.val + 1` of the extracted pairs, all `≥ 1`. -/
theorem detIntegrand_head_not_excluded
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (0 : ℕ) ∉ ((extract κ).map fun p => p.2.val + 1) := by
  simp

/-- **The head split.**  `detIntegrand` is the head Green edge times an
`x`-free remainder. -/
theorem detIntegrand_eq_head_mul_headless
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) :
    detIntegrand ρ ε m κ xt =
      greenFn (xt 0 - xt 1) * r324DetHeadless ρ ε m κ xt := by
  unfold detIntegrand r324DetHeadless
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero]
  rw [if_neg (detIntegrand_head_not_excluded κ)]
  have h0 : ((0 : Fin (m + 1)).castSucc : Fin (m + 2)) = 0 := by
    apply Fin.ext; simp
  have h1 : ((0 : Fin (m + 1)).succ : Fin (m + 2)) = 1 := by
    apply Fin.ext; simp
  rw [h0, h1]
  ring

/-- The headless factor only reads the assembled tuple at slots `≥ 1`. -/
theorem r324DetHeadless_congr
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (κ : PartialPairing (Fin m))
    {xt xt' : Fin (m + 2) → T4}
    (h : ∀ j : Fin (m + 2), j.val ≠ 0 → xt j = xt' j) :
    r324DetHeadless ρ ε m κ xt = r324DetHeadless ρ ε m κ xt' := by
  have hvar : ∀ i : Fin m, xt (varIdx i) = xt' (varIdx i) := by
    intro i
    exact h _ (by simp)
  have hdiff : diffFactor (m := m) xt = diffFactor (m := m) xt' := by
    funext p
    unfold diffFactor
    have h2 : xt ⟨p.2.val + 2, by have := p.2.isLt; omega⟩ =
        xt' ⟨p.2.val + 2, by have := p.2.isLt; omega⟩ := h _ (by simp)
    rw [hvar p.2, hvar p.1, h2]
  have hchain : ∀ e : Fin m,
      (if (e.succ : Fin (m + 1)).val ∈
          ((extract κ).map fun p => p.2.val + 1) then 1
        else greenFn (xt (e.succ : Fin (m + 1)).castSucc -
          xt (e.succ : Fin (m + 1)).succ)) =
      (if (e.succ : Fin (m + 1)).val ∈
          ((extract κ).map fun p => p.2.val + 1) then 1
        else greenFn (xt' (e.succ : Fin (m + 1)).castSucc -
          xt' (e.succ : Fin (m + 1)).succ)) := by
    intro e
    have ha : xt (e.succ : Fin (m + 1)).castSucc =
        xt' (e.succ : Fin (m + 1)).castSucc := h _ (by simp)
    have hb : xt (e.succ : Fin (m + 1)).succ =
        xt' (e.succ : Fin (m + 1)).succ := h _ (by simp)
    rw [ha, hb]
  have hcov : (∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
        ρ.etaEpsT4 ε (xt (varIdx i) - xt (varIdx (κ i)))) =
      ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
        ρ.etaEpsT4 ε (xt' (varIdx i) - xt' (varIdx (κ i))) :=
    Finset.prod_congr rfl fun i _ => by rw [hvar i, hvar (κ i)]
  have hprod : (∏ e : Fin m,
        if (e.succ : Fin (m + 1)).val ∈
            ((extract κ).map fun p => p.2.val + 1) then 1
          else greenFn (xt (e.succ : Fin (m + 1)).castSucc -
            xt (e.succ : Fin (m + 1)).succ)) =
      ∏ e : Fin m,
        if (e.succ : Fin (m + 1)).val ∈
            ((extract κ).map fun p => p.2.val + 1) then 1
          else greenFn (xt' (e.succ : Fin (m + 1)).castSucc -
            xt' (e.succ : Fin (m + 1)).succ) :=
    Finset.prod_congr rfl fun e _ => hchain e
  unfold r324DetHeadless
  rw [hprod, hdiff, hcov]

/-- Assembled tuples that differ only in the external head point agree at
every slot `≥ 1`. -/
theorem assemble_eq_of_ne_zero
    {m : ℕ} (x x' y : T4) (v : Fin m → T4)
    (j : Fin (m + 2)) (hj : j.val ≠ 0) :
    assemble x y v j = assemble x' y v j := by
  simp only [assemble, dif_neg hj]

/-- The head anchor of an assembled tuple is `v 0`. -/
theorem assemble_one
    {m : ℕ} (hm : 0 < m) (x y : T4) (v : Fin m → T4) :
    assemble x y v 1 = v ⟨0, hm⟩ := by
  have hv : (1 : Fin (m + 2)).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have h0 : ¬ ((1 : Fin (m + 2)).val = 0) := by omega
  have h1 : ¬ ((1 : Fin (m + 2)).val = m + 1) := by omega
  simp only [assemble, dif_neg h0, dif_neg h1]
  exact congrArg v (Fin.ext (by simp))

/-- **The head split on an assembled tuple**, with the head factor written
in the external point `x` and the head anchor `v 0`. -/
theorem detIntegrand_assemble_eq_head_mul_headless
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (x y : T4) (v : Fin m → T4) :
    detIntegrand ρ ε m κ (assemble x y v) =
      greenFn (x - v ⟨0, hm⟩) *
        r324DetHeadless ρ ε m κ (assemble y y v) := by
  rw [detIntegrand_eq_head_mul_headless, assemble_zero, assemble_one hm,
    r324DetHeadless_congr ρ ε m κ
      (fun j hj => assemble_eq_of_ne_zero x y y v j hj)]

/-! ## The head split of the summed core -/

/-- The summed flat core with the head Green edge of the **left** copy
deleted.  It does not depend on the external point `x`. -/
def r324CMHeadlessCore
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (F : Finset (MomentContraction m))
    (q : R324PhysicalRest m) : ℝ :=
  ∑ e ∈ F,
    (r324DetHeadless ρ ε m e.1
        (assemble q.1 q.1 fun i => q.2.2.2 (leftMomentIndex i)) *
      detIntegrand ρ ε m e.2.1
        (assemble q.2.1 q.2.2.1 fun i => q.2.2.2 (rightMomentIndex i)) *
      momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 q.2.2.2)

/-- **The head factor is entity independent**, so it leaves the entity sum
untouched: the summed core is the head Green edge times an `x`-free
remainder.  No cancellation inside `F` is spent. -/
theorem r324CMFlatCore_eq_head_mul_headless
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (hm : 0 < m)
    (F : Finset (MomentContraction m))
    (x : T4) (q : R324PhysicalRest m) :
    r324CMFlatCore ρ ε m F (x, q) =
      greenFn (x - q.2.2.2 (leftMomentIndex ⟨0, hm⟩)) *
        r324CMHeadlessCore ρ ε m F q := by
  unfold r324CMFlatCore r324CMHeadlessCore
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _he => ?_
  rw [show ((x, q) : R324PhysicalPoint m).1 = x from rfl,
    detIntegrand_assemble_eq_head_mul_headless ρ ε hm e.1 x q.1
      (fun i => q.2.2.2 (leftMomentIndex i))]
  ring

/-! ## The harvest -/

/-- **The endpoint harvest at `x`.**  Integrating the summed core against
its external character produces one translated Green Fourier coefficient
at the mode `α`, times the `x`-free remainder.  The entity sum never
leaves the integrand. -/
theorem integral_charT4_mul_r324CMFlatCore
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (hm : 0 < m) (α : Z4)
    (F : Finset (MomentContraction m))
    (q : R324PhysicalRest m) :
    (∫ x : T4, charT4 α x *
        ((r324CMFlatCore ρ ε m F (x, q) : ℝ) : ℂ) ∂paperMeasure) =
      translatedGreenMode α (q.2.2.2 (leftMomentIndex ⟨0, hm⟩)) *
        ((r324CMHeadlessCore ρ ε m F q : ℝ) : ℂ) := by
  have hpt : ∀ x : T4,
      charT4 α x * ((r324CMFlatCore ρ ε m F (x, q) : ℝ) : ℂ) =
        (charT4 α x *
            ((greenFn (x - q.2.2.2 (leftMomentIndex ⟨0, hm⟩)) : ℝ) : ℂ)) *
          ((r324CMHeadlessCore ρ ε m F q : ℝ) : ℂ) := by
    intro x
    rw [r324CMFlatCore_eq_head_mul_headless ρ ε hm F x q]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_mul_const]
  rfl

/-- **The harvested modulus.**  The `x`-integration contributes exactly the
second-order mode decay `⟨α⟩⁻²`, uniformly in the entity set. -/
theorem norm_integral_charT4_mul_r324CMFlatCore
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (hm : 0 < m) (α : Z4)
    (F : Finset (MomentContraction m))
    (q : R324PhysicalRest m) :
    ‖∫ x : T4, charT4 α x *
        ((r324CMFlatCore ρ ε m F (x, q) : ℝ) : ℂ) ∂paperMeasure‖ =
      paperSecondOrderModeDecay α * |r324CMHeadlessCore ρ ε m F q| := by
  rw [integral_charT4_mul_r324CMFlatCore ρ ε hm α F q, norm_mul,
    norm_translatedGreenMode, Complex.norm_real, Real.norm_eq_abs]

end

end Anderson4D
