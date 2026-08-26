import Anderson4D.DetParametrix.Paper42_Moment.R324CharacterCosineEstimate
import Anderson4D.DetParametrix.Paper42_Moment.R324EmptyInsertedMajorantBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324DifferenceRetainingCore
import Anderson4D.DetParametrix.Paper42_Moment.R324FrequencyConservation
import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorLogBudgetProof
import Anderson4D.Continuum.PrimitiveProposition41

/-!
# Paper §4.2, Step 1: the deterministic (full-pairing) terms

Paper: R-324 — §4.2 Step 1 — the deterministic terms (κ a full pairing)

This file transcribes **Step 1 of Section 4.2** of arXiv:2607.10105v1
(pages 18–19) literally, in the paper's own order.

After the successive removal of the fully paired subintervals (the
`§4.1` iteration, recorded here as the single named hypothesis
`R324Step1Reduction`), the paper is left with (4.17): a four-fold
integral in `(x_a, x_m, x, y)` carrying `(Cλ)^{m-2p}` in front,

    ∫ e^{i(α·x+β·y)} G₀(x-x_a) J_{2p,prim}(x_a-x_m)
        [G(x_m-y) - G(x_a-y)] dx_a dx_m dx dy .

This is `r324Step1Integral`.  The remaining five moves of Step 1 are

1. **`r324Step1_integral_y`** — the `y`-integral produces
   `⟨β⟩⁻²(e^{iβ·x_m} - e^{iβ·x_a})`, i.e. the paper's
   `⟨β⟩⁻² e^{iβ·x_a}(e^{iβ·(x_m-x_a)} - 1)`;
2. **`r324Step1_integral_x`** — the `x`-integral of `G₀` produces
   `⟨α⟩⁻² e^{iα·x_a}`;
3. **`r324Step1_integral_xm`** — translating `x_m = x_a + u` and using
   `J_{2p,prim} ∈ 𝓔` (Proposition 4.1) makes the imaginary part
   `sin(β·(x_m-x_a))` integrate to zero, leaving `cos - 1`;
4. **`r324Step1_beta_cosine_le`** — the surviving real part obeys
   `⟨β⟩⁻²|cos(β·z)-1| ≤ |z|²`, which is the (4.4) insertion, so
   `J_{2p,prim}` is replaced by `J̃_{2p,prim}`;
5. **`r324Step1_norm_le`** / **`exists_r324Step1_bound`** — integrating
   `J̃` in `x_m`, `G₀` in `x` and finally in `x_a` gives
   `(Cλ)^{2p}|log ε|⁻¹`, hence `(Cλ)^m|log ε|⁻¹`, which is (3.24).

Every analytic input is a proved theorem: `proposition41_at_truncation`
(4.3)–(4.4) and `J ∈ 𝓔`; `integral_charT4_mul_greenFn_shift`
(`Ĝ(β) = ⟨β⟩⁻²`); `integral_memEClass_mul_characterSubOne_eq_cos`
(the 𝓔-symmetry cancellation); `abs_r324CharacterCos_sub_one_le_half_mul`
(the sharp cosine bound); `torusDistSq_mul_primitiveKernelMajorant_le_max_one_sq_mul_inserted`
(the `J ↦ J̃` replacement at the level of the two majorants); and
`exists_integral_primitiveInsertedMajorant_le` (the final radial
integration).
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The expression (4.17) -/

/-- The integrand of (4.17): `e^{i(α·x+β·y)} G₀(x-x_a) J(x_a-x_m)
[G(x_m-y) - G(x_a-y)]`, with the primitive kernel `J` kept abstract. -/
def r324Step1Integrand (J : T4 → ℝ) (α β : Z4) (xa xm x y : T4) : ℂ :=
  charT4 α x * charT4 β y *
    ((greenFn (x - xa) : ℝ) : ℂ) * ((J (xa - xm) : ℝ) : ℂ) *
      (((greenFn (xm - y) : ℝ) : ℂ) - ((greenFn (xa - y) : ℝ) : ℂ))

/-- The second display of (4.17), integrated in the paper's own order:
`y` innermost, then `x`, then `x_m`, then `x_a`. -/
def r324Step1Integral (J : T4 → ℝ) (α β : Z4) : ℂ :=
  ∫ xa, ∫ xm, ∫ x, ∫ y,
    r324Step1Integrand J α β xa xm x y
    ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure

/-! ## Step 1(a): the `y`-integral -/

/-- Both boundary Green legs are integrable against the character. -/
private theorem integrable_charT4_mul_greenFn_shift (b : Z4) (v : T4) :
    Integrable
      (fun y : T4 => charT4 b y * ((greenFn (v - y) : ℝ) : ℂ))
      paperMeasure := by
  have h :
      (fun y : T4 => charT4 b y * ((greenFn (v - y) : ℝ) : ℂ)) =
        fun y : T4 => charT4 b y * ((greenFn (y - v) : ℝ) : ℂ) := by
    funext y
    rw [show v - y = -(y - v) by abel, greenFn_memE.neg_invariant]
  rw [h]
  exact integrable_charT4_mul_greenFn_sub b v

/-- **The `y`-integral of (4.17).**  The paper's

`∫ e^{iβ·y}(G(x_m-y) - G(x_a-y)) dy = ⟨β⟩⁻² e^{iβ·x_a}(e^{iβ·(x_m-x_a)} - 1)`,

recorded in the equivalent un-factored form `⟨β⟩⁻²(e^{iβ·x_m} - e^{iβ·x_a})`. -/
theorem r324Step1_integral_y (J : T4 → ℝ) (α β : Z4) (xa xm x : T4) :
    (∫ y, r324Step1Integrand J α β xa xm x y ∂paperMeasure) =
      charT4 α x * ((greenFn (x - xa) : ℝ) : ℂ) * ((J (xa - xm) : ℝ) : ℂ) *
        (((paperSecondOrderModeDecay β : ℝ) : ℂ) *
          (charT4 β xm - charT4 β xa)) := by
  have hpull :
      (fun y : T4 => r324Step1Integrand J α β xa xm x y) =
        fun y : T4 =>
          (charT4 α x * ((greenFn (x - xa) : ℝ) : ℂ) *
              ((J (xa - xm) : ℝ) : ℂ)) *
            (charT4 β y * ((greenFn (xm - y) : ℝ) : ℂ) -
              charT4 β y * ((greenFn (xa - y) : ℝ) : ℂ)) := by
    funext y
    unfold r324Step1Integrand
    ring
  rw [hpull, integral_const_mul,
    integral_sub (integrable_charT4_mul_greenFn_shift β xm)
      (integrable_charT4_mul_greenFn_shift β xa),
    integral_charT4_mul_greenFn_shift β xm,
    integral_charT4_mul_greenFn_shift β xa]
  unfold paperSecondOrderModeDecay
  ring

/-! ## Step 1(b): the `x`-integral of `G₀` -/

/-- **The `x`-integral of (4.17).**  The free boundary leg `G₀(x - x_a)`
against `e^{iα·x}` is again `Ĝ(α) = ⟨α⟩⁻²`, transported to the base
point `x_a`. -/
theorem r324Step1_integral_x (J : T4 → ℝ) (α β : Z4) (xa xm : T4) :
    (∫ x, ∫ y, r324Step1Integrand J α β xa xm x y
      ∂paperMeasure ∂paperMeasure) =
      (charT4 α xa * ((paperSecondOrderModeDecay α : ℝ) : ℂ)) *
        (((J (xa - xm) : ℝ) : ℂ) *
          (((paperSecondOrderModeDecay β : ℝ) : ℂ) *
            (charT4 β xm - charT4 β xa))) := by
  have hy :
      (fun x : T4 => ∫ y, r324Step1Integrand J α β xa xm x y ∂paperMeasure) =
        fun x : T4 =>
          (charT4 α x * ((greenFn (xa - x) : ℝ) : ℂ)) *
            (((J (xa - xm) : ℝ) : ℂ) *
              (((paperSecondOrderModeDecay β : ℝ) : ℂ) *
                (charT4 β xm - charT4 β xa))) := by
    funext x
    rw [r324Step1_integral_y,
      show greenFn (x - xa) = greenFn (xa - x) by
        rw [show x - xa = -(xa - x) by abel, greenFn_memE.neg_invariant]]
    ring
  rw [hy, integral_mul_const, integral_charT4_mul_greenFn_shift α xa]
  unfold paperSecondOrderModeDecay
  ring

/-! ## Step 1(c): the `x_m`-integral and the vanishing imaginary part -/

/-- `paperMeasure` is translation invariant. -/
private theorem paperMeasure_integral_translate (f : T4 → ℂ) (a : T4) :
    (∫ x, f x ∂paperMeasure) = ∫ x, f (a + x) ∂paperMeasure := by
  rw [paperMeasure_eq_volume]
  exact (integral_add_left_eq_self f a).symm

/-- **The `x_m`-integral of (4.17).**  Setting `x_m = x_a + u` turns the
kernel argument into `-u`; since `J_{2p,prim} ∈ 𝓔` (Proposition 4.1) the
kernel is even, so the odd component `sin(β·u)` of the phase integrates
to zero and only `cos(β·u) - 1` survives.  This is the paper's sentence
"if we take the imaginary part `sin(β·(x_m-x_a))` above, then the
contribution to the whole integral vanishes because `J_{2p,prim} ∈ E`". -/
theorem r324Step1_integral_xm {J : T4 → ℝ} (hJ : MemEClassT4 J)
    (α β : Z4) (xa : T4)
    (hcos : Integrable (fun u => J u * (r324CharacterCos β u - 1))
      paperMeasure)
    (hsin : Integrable (fun u => J u * r324CharacterSin β u) paperMeasure) :
    (∫ xm, ∫ x, ∫ y, r324Step1Integrand J α β xa xm x y
      ∂paperMeasure ∂paperMeasure ∂paperMeasure) =
      (charT4 α xa * ((paperSecondOrderModeDecay α : ℝ) : ℂ)) *
        (((paperSecondOrderModeDecay β : ℝ) : ℂ) * charT4 β xa) *
        ∫ u, ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ) ∂paperMeasure := by
  have hx :
      (fun xm : T4 =>
          ∫ x, ∫ y, r324Step1Integrand J α β xa xm x y
            ∂paperMeasure ∂paperMeasure) =
        fun xm : T4 =>
          (charT4 α xa * ((paperSecondOrderModeDecay α : ℝ) : ℂ)) *
            (((J (xa - xm) : ℝ) : ℂ) *
              (((paperSecondOrderModeDecay β : ℝ) : ℂ) *
                (charT4 β xm - charT4 β xa))) := by
    funext xm
    exact r324Step1_integral_x J α β xa xm
  rw [hx, integral_const_mul,
    paperMeasure_integral_translate
      (fun xm : T4 =>
        ((J (xa - xm) : ℝ) : ℂ) *
          (((paperSecondOrderModeDecay β : ℝ) : ℂ) *
            (charT4 β xm - charT4 β xa))) xa]
  have hshift :
      (fun u : T4 =>
          ((J (xa - (xa + u)) : ℝ) : ℂ) *
            (((paperSecondOrderModeDecay β : ℝ) : ℂ) *
              (charT4 β (xa + u) - charT4 β xa))) =
        fun u : T4 =>
          (((paperSecondOrderModeDecay β : ℝ) : ℂ) * charT4 β xa) *
            (((J u : ℝ) : ℂ) * (charT4 β u - 1)) := by
    funext u
    have harg : xa - (xa + u) = -u := by abel
    rw [harg, hJ.neg_invariant, charT4_add_argument]
    ring
  rw [hshift, integral_const_mul,
    integral_memEClass_mul_characterSubOne_eq_cos hJ β hcos hsin]
  ring

/-! ## Step 1(d): the final `x_a`-integral -/

/-- Total `paperMeasure` mass of `𝕋⁴`, namely `(2π)⁴`. -/
def r324PaperTorusMass : ℝ := (2 * Real.pi) ^ (dim : ℕ)

theorem r324PaperTorusMass_pos : 0 < r324PaperTorusMass := by
  unfold r324PaperTorusMass; positivity

/-- **The three remaining integrations of Step 1.**  After `J̃` has been
integrated in `x_m` and `G₀` in `x`, the last integration in `x_a` sees
only unimodular characters, so it costs the total mass `(2π)⁴`.  The
`⟨α⟩⁻²` produced by the `x`-integral is discarded against `1`. -/
theorem r324Step1_norm_le {J : T4 → ℝ} (hJ : MemEClassT4 J) (α β : Z4)
    (hcos : Integrable (fun u => J u * (r324CharacterCos β u - 1))
      paperMeasure)
    (hsin : Integrable (fun u => J u * r324CharacterSin β u) paperMeasure) :
    ‖r324Step1Integral J α β‖ ≤
      r324PaperTorusMass *
        (paperSecondOrderModeDecay β *
          ‖∫ u, ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)
            ∂paperMeasure‖) := by
  set I : ℂ :=
    ∫ u, ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ) ∂paperMeasure with hI
  set F : T4 → ℂ := fun xa =>
    (charT4 α xa * ((paperSecondOrderModeDecay α : ℝ) : ℂ)) *
      (((paperSecondOrderModeDecay β : ℝ) : ℂ) * charT4 β xa) * I with hF
  have hxa :
      (fun xa : T4 =>
        ∫ xm, ∫ x, ∫ y, r324Step1Integrand J α β xa xm x y
          ∂paperMeasure ∂paperMeasure ∂paperMeasure) = F := by
    funext xa
    rw [hF, hI]
    exact r324Step1_integral_xm hJ α β xa hcos hsin
  have hnorm :
      (fun xa : T4 => ‖F xa‖) =
        fun _ : T4 =>
          paperSecondOrderModeDecay α *
            (paperSecondOrderModeDecay β * ‖I‖) := by
    funext xa
    rw [hF]
    simp only [norm_mul, norm_charT4, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (paperSecondOrderModeDecay_nonneg _)]
    ring
  have hconst :
      (∫ xa, ‖F xa‖ ∂paperMeasure) =
        r324PaperTorusMass *
          (paperSecondOrderModeDecay α *
            (paperSecondOrderModeDecay β * ‖I‖)) := by
    rw [hnorm, integral_const, measureReal_def, paperMeasure_univ,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    rfl
  calc
    ‖r324Step1Integral J α β‖ = ‖∫ xa, F xa ∂paperMeasure‖ := by
      unfold r324Step1Integral
      rw [hxa]
    _ ≤ ∫ xa, ‖F xa‖ ∂paperMeasure :=
      norm_integral_le_integral_norm _
    _ = r324PaperTorusMass *
          (paperSecondOrderModeDecay α *
            (paperSecondOrderModeDecay β * ‖I‖)) := hconst
    _ ≤ r324PaperTorusMass *
          (1 * (paperSecondOrderModeDecay β * ‖I‖)) := by
      refine mul_le_mul_of_nonneg_left ?_ r324PaperTorusMass_pos.le
      refine mul_le_mul_of_nonneg_right
        (paperSecondOrderModeDecay_le_one α) ?_
      exact mul_nonneg (paperSecondOrderModeDecay_nonneg β) (norm_nonneg _)
    _ = r324PaperTorusMass *
          (paperSecondOrderModeDecay β * ‖I‖) := by ring

/-! ## Step 1(e): `⟨β⟩⁻²|cos - 1|` is the (4.4) insertion -/

/-- `⟨β⟩⁻²|β|² ≤ 1`: the bracket produced by the `y`-integral pays
exactly for the two derivatives extracted from `cos(β·z) - 1`. -/
theorem r324Step1_modeNormSq_mul_decay_le_one (b : Z4) :
    paperModeNormSq b * paperSecondOrderModeDecay b ≤ 1 := by
  have hb : (0 : ℝ) ≤ paperModeNormSq b := by
    unfold paperModeNormSq; positivity
  have hpos : (0 : ℝ) < 1 + paperModeNormSq b := by linarith
  unfold paperSecondOrderModeDecay
  rw [mul_inv_le_iff₀ hpos]
  linarith

/-- **The paper's Step 1 inequality**
`⟨β⟩⁻²|cos(β·(x_m-x_a)) - 1| ≤ ⟨β⟩⁻²|β|²|x_m-x_a|² ≤ ε² + max|x_i-x_j|²`,
in the integrated form the argument actually uses: the surviving real
part, weighted by `⟨β⟩⁻²`, is bounded by the (4.3) majorant carrying one
squared-distance insertion — which is exactly (4.4), the `J ↦ J̃`
replacement. -/
theorem r324Step1_beta_cosine_le
    (ρ : SmoothCutoff) (lam ε : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (G : Fin (2 * p - 1) → T4 → ℝ)
    (supportConstant primitiveConstant : ℝ) (hε : 0 < ε)
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam) (β : Z4)
    (hbound : PrimitiveKernelBounds ρ lam ε p hp G
      supportConstant primitiveConstant) :
    paperSecondOrderModeDecay β *
        ‖∫ u, ((primitiveKernelDiff ρ lam ε p hp G u *
            (r324CharacterCos β u - 1) : ℝ) : ℂ) ∂paperMeasure‖ ≤
      (1 / 2 : ℝ) *
        (max 1 (supportConstant ^ 2) *
          ∫ z, primitiveInsertedMajorant primitiveConstant lam ε
            supportConstant p z ∂paperMeasure) := by
  set Mord : ℝ :=
    ∫ u, torusDistSq u *
      primitiveKernelMajorant primitiveConstant lam ε supportConstant p u
      ∂paperMeasure with hMord
  have hMord0 : 0 ≤ Mord :=
    integral_nonneg fun u =>
      mul_nonneg (torusDistSq_nonneg u)
        (primitiveKernelMajorant_nonneg hC hlam)
  have hkey :=
    norm_integral_primitiveKernelDiff_mul_r324CharacterCos_sub_one_le
      ρ lam ε p hp G supportConstant primitiveConstant hε hbound β
  have hbridge :=
    integral_torusDistSq_mul_primitiveKernelMajorant_le_max_one_sq_mul_integral_inserted
      primitiveConstant lam ε supportConstant p hε
  calc
    paperSecondOrderModeDecay β *
        ‖∫ u, ((primitiveKernelDiff ρ lam ε p hp G u *
            (r324CharacterCos β u - 1) : ℝ) : ℂ) ∂paperMeasure‖ ≤
        paperSecondOrderModeDecay β *
          (((1 / 2 : ℝ) * paperModeNormSq β) * Mord) :=
      mul_le_mul_of_nonneg_left hkey (paperSecondOrderModeDecay_nonneg β)
    _ = (1 / 2 : ℝ) *
          ((paperModeNormSq β * paperSecondOrderModeDecay β) * Mord) := by
      ring
    _ ≤ (1 / 2 : ℝ) * (1 * Mord) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_right
        (r324Step1_modeNormSq_mul_decay_le_one β) hMord0
    _ = (1 / 2 : ℝ) * Mord := by ring
    _ ≤ (1 / 2 : ℝ) *
          (max 1 (supportConstant ^ 2) *
            ∫ z, primitiveInsertedMajorant primitiveConstant lam ε
              supportConstant p z ∂paperMeasure) :=
      mul_le_mul_of_nonneg_left hbridge (by norm_num)

/-! ## Step 1(f): the closed estimate for one primitive full pairing -/

/-- **Step 1 of §4.2, assembled.**  The (4.17) integral for a primitive
full pairing on `2p` elements is bounded by the integrated (4.4)
majorant. -/
theorem r324Step1_primitive_norm_le
    (ρ : SmoothCutoff) (lam ε : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (G : Fin (2 * p - 1) → T4 → ℝ)
    (supportConstant primitiveConstant : ℝ) (hε : 0 < ε)
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam) (α β : Z4)
    (hJ : MemEClassT4 (primitiveKernelDiff ρ lam ε p hp G))
    (hbound : PrimitiveKernelBounds ρ lam ε p hp G
      supportConstant primitiveConstant)
    (hcos : Integrable (fun u => primitiveKernelDiff ρ lam ε p hp G u *
      (r324CharacterCos β u - 1)) paperMeasure)
    (hsin : Integrable (fun u => primitiveKernelDiff ρ lam ε p hp G u *
      r324CharacterSin β u) paperMeasure) :
    ‖r324Step1Integral (primitiveKernelDiff ρ lam ε p hp G) α β‖ ≤
      r324PaperTorusMass *
        ((1 / 2 : ℝ) *
          (max 1 (supportConstant ^ 2) *
            ∫ z, primitiveInsertedMajorant primitiveConstant lam ε
              supportConstant p z ∂paperMeasure)) :=
  le_trans (r324Step1_norm_le hJ α β hcos hsin)
    (mul_le_mul_of_nonneg_left
      (r324Step1_beta_cosine_le ρ lam ε p hp G supportConstant
        primitiveConstant hε hC hlam β hbound)
      r324PaperTorusMass_pos.le)

/-! ## Step 1(g): the paper's numerical output `(Cλ)^{2p}|log ε|⁻¹` -/

/-- **Step 1 of §4.2, in the paper's own numerical shape.**

For every primitive full pairing on `2p` elements whose inputs `G_j` are
the admissible functions produced by the successive removal (`G_j ∈ 𝓔`,
`|G_j(z)| ≤ |z|⁻²`), the (4.17) integral obeys

`|(4.17)| ≤ (C λ)^{2p} / |log ε|`

with one constant `C` depending on the mollifier alone.  This is the
paper's "`|P̂_m(α,β)| ≤ (Cλ)^m |log ε|⁻¹`" with the `(Cλ)^{m-2p}` gained
by the removal steps still to be multiplied in. -/
theorem exists_r324Step1_bound (ρ : SmoothCutoff) :
    ∃ Cstep : ℝ, 0 < Cstep ∧
      ∀ (lam ε : ℝ) (p : ℕ) (hp : 1 ≤ p)
        (G : Fin (2 * p - 1) → T4 → ℝ) (α β : Z4),
        0 < lam → 0 < ε → ε ≤ 1 → p ≤ truncOrder ε →
        1 ≤ |Real.log ε| →
        IsAdmissiblePrimitiveInput p G →
        Integrable (fun u => primitiveKernelDiff ρ lam ε p hp G u *
          (r324CharacterCos β u - 1)) paperMeasure →
        Integrable (fun u => primitiveKernelDiff ρ lam ε p hp G u *
          r324CharacterSin β u) paperMeasure →
          ‖r324Step1Integral (primitiveKernelDiff ρ lam ε p hp G) α β‖ ≤
            (Cstep * lam) ^ (2 * p) / |Real.log ε| := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨Cball, Creg, hCball, hCreg, hmaj⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  set K : ℝ :=
    r324PaperTorusMass * ((1 / 2 : ℝ) *
      (max 1 (supportConstant ^ 2) *
        (Cball * supportConstant ^ 2 + 2 * Creg))) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have h1 : (0 : ℝ) ≤ max 1 (supportConstant ^ 2) :=
      le_trans zero_le_one (le_max_left _ _)
    have h2 : (0 : ℝ) ≤ Cball * supportConstant ^ 2 + 2 * Creg := by
      positivity
    have := r324PaperTorusMass_pos.le
    positivity
  refine ⟨C * (K + 1), by positivity, ?_⟩
  intro lam ε p hp G α β hlam hε hε1 hptrunc hlog hG hcos hsin
  obtain ⟨hJmem, _hJins, hbound⟩ :=
    hprop lam ε p hp G hlam hε hε1 hptrunc hG
  have hlog0 : (0 : ℝ) < |Real.log ε| := lt_of_lt_of_le one_pos hlog
  have hmaj' :=
    hmaj C lam ε supportConstant p hε hε1 hsupport hlog
  have hmax0 : (0 : ℝ) ≤ max 1 (supportConstant ^ 2) :=
    le_trans zero_le_one (le_max_left _ _)
  have hstep :=
    r324Step1_primitive_norm_le ρ lam ε p hp G supportConstant C hε
      hC.le hlam.le α β hJmem hbound hcos hsin
  have habsorb :
      (C * lam) ^ (2 * p) * K ≤ ((C * lam) * (K + 1)) ^ (2 * p) :=
    mul_constant_le_absorbed_even_pow
      (mul_nonneg hC.le hlam.le) hK0 hp
  calc
    ‖r324Step1Integral (primitiveKernelDiff ρ lam ε p hp G) α β‖ ≤
        r324PaperTorusMass *
          ((1 / 2 : ℝ) *
            (max 1 (supportConstant ^ 2) *
              ∫ z, primitiveInsertedMajorant C lam ε supportConstant p z
                ∂paperMeasure)) := hstep
    _ ≤ r324PaperTorusMass *
          ((1 / 2 : ℝ) *
            (max 1 (supportConstant ^ 2) *
              ((C * lam) ^ (2 * p) *
                ((Cball * supportConstant ^ 2 + 2 * Creg) /
                  |Real.log ε|)))) := by
      refine mul_le_mul_of_nonneg_left ?_ r324PaperTorusMass_pos.le
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_left hmaj' hmax0
    _ = ((C * lam) ^ (2 * p) * K) / |Real.log ε| := by
      rw [hK]; field_simp
    _ ≤ ((C * lam) * (K + 1)) ^ (2 * p) / |Real.log ε| := by
      gcongr
    _ = (C * (K + 1) * lam) ^ (2 * p) / |Real.log ε| := by
      rw [show (C * lam) * (K + 1) = C * (K + 1) * lam by ring]

/-! ## Step 1, first move: the successive removal of §4.1 -/

/-- **The one input Step 1 takes from the §4.1 iteration.**

`P` stands for the full-pairing (deterministic) part of (4.16) at order
`m`.  The paper takes the maximal-and-rightmost interval `I_* = [a, m]`,
removes the fully paired subintervals to the left of `I_*` and then
those inside it one at a time; each removal invokes Proposition 4.1,
*gains a factor `Cλ`*, and replaces the removed contribution by a new
input `H` with `|H(z)| ≲ |z|⁻²`, which is (4.13).  What survives is a
primitive full pairing `κ_*` on `2p` elements together with the
expression (4.17) — precisely `r324Step1Integral` applied to
`J_{2p,prim} = primitiveKernelDiff` with the `H`'s as inputs.

This is the closed R-322 chain (`exists_r322RenormFiberReductionOutputAE`,
`exists_renormC_bound_of_reduction_ae`) transported from §4.1 to the
order-`m` deterministic fibre; the paper says explicitly that §4.2
argues "as in Section 4.1".  It is the only move of Step 1 not
discharged in this file; everything after it is proved above. -/
def R324Step1Reduction (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (Cred : ℝ) (P : ℂ) : Prop :=
  ∃ (p : ℕ) (hp : 1 ≤ p) (G : Fin (2 * p - 1) → T4 → ℝ),
    2 * p ≤ m ∧ p ≤ truncOrder ε ∧
      IsAdmissiblePrimitiveInput p G ∧
      Integrable (fun u => primitiveKernelDiff ρ lam ε p hp G u *
        (r324CharacterCos β u - 1)) paperMeasure ∧
      Integrable (fun u => primitiveKernelDiff ρ lam ε p hp G u *
        r324CharacterSin β u) paperMeasure ∧
      ‖P‖ ≤ (Cred * lam) ^ (m - 2 * p) *
        ‖r324Step1Integral (primitiveKernelDiff ρ lam ε p hp G) α β‖

/-- **Step 1 of §4.2, complete.**

Given the §4.1 successive removal, the deterministic (full-pairing)
part of (4.16) satisfies

`|P̂_m(α,β)| ≤ (Cλ)^m |log ε|⁻¹`,

which is (3.24) with `1` on the right-hand side.  The `(Cλ)^{m-2p}`
gained by the removals and the `(Cλ)^{2p}|log ε|⁻¹` produced by the
`y`-, `x`- and `x_a`-integrations recombine into a single power. -/
theorem exists_r324Step1_deterministic_bound
    (ρ : SmoothCutoff) {Cred : ℝ} (hCred : 0 < Cred) :
    ∃ Cdet : ℝ, 0 < Cdet ∧
      ∀ (lam ε : ℝ) (m : ℕ) (α β : Z4) (P : ℂ),
        0 < lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        R324Step1Reduction ρ lam ε m α β Cred P →
          ‖P‖ ≤ (Cdet * lam) ^ m / |Real.log ε| := by
  obtain ⟨Cstep, hCstep, hstep⟩ := exists_r324Step1_bound ρ
  refine ⟨max Cred Cstep, lt_max_of_lt_left hCred, ?_⟩
  intro lam ε m α β P hlam hε hε1 hlog hred
  obtain ⟨p, hp, G, hpm, hptrunc, hG, hcos, hsin, hP⟩ := hred
  have hlog0 : (0 : ℝ) < |Real.log ε| := lt_of_lt_of_le one_pos hlog
  have hbase :
      ∀ D : ℝ, 0 < D → D ≤ max Cred Cstep →
        ∀ k : ℕ, (D * lam) ^ k ≤ ((max Cred Cstep) * lam) ^ k := by
    intro D hD hDmax k
    exact pow_le_pow_left₀ (mul_nonneg hD.le hlam.le)
      (mul_le_mul_of_nonneg_right hDmax hlam.le) k
  have hmain :=
    hstep lam ε p hp G α β hlam hε hε1 hptrunc hlog hG hcos hsin
  have hsplit : (m - 2 * p) + 2 * p = m := Nat.sub_add_cancel hpm
  have hred0 : (0 : ℝ) ≤ (Cred * lam) ^ (m - 2 * p) :=
    pow_nonneg (mul_nonneg hCred.le hlam.le) _
  calc
    ‖P‖ ≤ (Cred * lam) ^ (m - 2 * p) *
        ‖r324Step1Integral (primitiveKernelDiff ρ lam ε p hp G) α β‖ := hP
    _ ≤ (Cred * lam) ^ (m - 2 * p) *
          ((Cstep * lam) ^ (2 * p) / |Real.log ε|) :=
      mul_le_mul_of_nonneg_left hmain hred0
    _ ≤ ((max Cred Cstep) * lam) ^ (m - 2 * p) *
          (((max Cred Cstep) * lam) ^ (2 * p) / |Real.log ε|) := by
      refine mul_le_mul (hbase Cred hCred (le_max_left _ _) _) ?_ ?_ ?_
      · gcongr
        exact le_max_right _ _
      · positivity
      · exact pow_nonneg
          (mul_nonneg (le_trans hCred.le (le_max_left _ _)) hlam.le) _
    _ = (((max Cred Cstep) * lam) ^ (m - 2 * p) *
          ((max Cred Cstep) * lam) ^ (2 * p)) / |Real.log ε| := by
      ring
    _ = ((max Cred Cstep) * lam) ^ m / |Real.log ε| := by
      rw [← pow_add, hsplit]

end

end Anderson4D
