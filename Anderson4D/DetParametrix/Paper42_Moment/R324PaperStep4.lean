import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep1
import Anderson4D.DetParametrix.Paper42_Moment.R324Step4CosineLoss
import Anderson4D.DetParametrix.Paper42_Moment.R324HdetAssemblyFinal
import Anderson4D.DetParametrix.Paper42_Moment.R324HdetAssemblyBracket
import Anderson4D.DetParametrix.Paper42_Moment.R324FrequencyRoutingClosure

/-!
# Paper §4.2, Step 4: the decay factors

Paper: R-324 — §4.2 Step 4 — the ⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε²(α+β)⟩⁻⁸ decay factors

This file transcribes **Step 4 of Section 4.2** of arXiv:2607.10105v1
(bottom of page 20 and top of page 21) literally.  Step 4 upgrades the
bound proved by Steps 1–3, namely (3.24) with `1` on the right, to
(3.24) with

    ε⁻⁸ ⟨α⟩⁻⁴ ⟨β⟩⁻⁴ ⟨ε²(α+β)⟩⁻⁸

on the right.  The paper gives **two independent mechanisms**.

## (A) The `⟨α⟩⁻⁴⟨β⟩⁻⁴` factor at the price of `ε⁻⁸`

> "we exploit the oscillation in `(x, y, z, w)` in (4.18).  For example
> consider the integral in `y`: if `m` is not involved in any fully
> paired subinterval, then we can integrate in `y` after removing each
> `I_i` and before taking absolute values, which gains a factor
> `|Ĝ(β)| ≤ ⟨β⟩⁻²`.  If `m` is involved in a fully paired subinterval,
> say `[a, m]` as in Step 1, then the same calculations there lead to
> the factor `⟨β⟩⁻²·|cos(β·(x_m − x_a)) − 1|`.  We now bound it by
> `2⟨β⟩⁻²` to keep the decay in `β`, although this gives up a factor
> `|x_m − x_a|²` which forces us to consider `J_{2p,prim}` instead of
> `J̃_{2p,prim}`; upon integration this leads to a loss of `ε⁻²`.  By
> doing the same for each one of `(x, y, z, w)`, we can secure the
> desired `⟨α⟩⁻⁴⟨β⟩⁻⁴` factor at the price of losing `ε⁻⁸`."

Transcribed as, in order,
`r324Step4_norm_endpoint_integral_unpaired` (the unpaired endpoint, an
exact `⟨β⟩⁻²`), `r324Step4_paired_endpoint_le_two` (the paired
endpoint, `⟨β⟩⁻²|cos−1| ≤ 2⟨β⟩⁻²`),
`r324Step4_unpaired_le_paired_budget` (the unpaired endpoint is the
cheaper of the two, so the paired budget is the worst case),
`r324Step4_primitiveKernelMajorant_le_endpointBudget` (giving up the
squared distance replaces `J̃_{2p,prim}` by `J_{2p,prim}`, at `ε⁻²`),
`exists_r324Step4_endpointDecay_bound` (the closed (4.17) bound with
`⟨α⟩⁻²⟨β⟩⁻²` retained and `ε⁻²` lost), and
`r324Step4_fourEndpoint_budget_eq` ("doing the same for each one of
`(x, y, z, w)`" — the product of the four endpoint budgets is exactly
`ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴ = r324EndpointLoss`).

## (B) The `⟨ε²(α+β)⟩⁻⁸` factor

> "`P_m` is (the renormalization of) a linear operator that is the
> composition of at most `|log ε|` factors, each of which is either
> convolution by `G` (which is a Fourier multiplier) or multiplication
> by `ξ_ε` (which is convolution by `ρ̂_ε·ξ̂` on the Fourier side).  If
> this operator shifts the frequency by `|α + β| ∼ L ≥ ε⁻²`, then one
> of the above factors must shift the frequency by `≳ ε^{1/2}L`.  For
> this factor we may replace `ξ_ε` by its projection `ξ̃_ε` to
> frequencies `≳ ε^{1/2}L`, which carries a decay factor `⟨ε²L⟩⁻⁸`
> because `ρ̂` is Schwartz."

Transcribed as `r324Step4_sqrt_mul_truncOrder_le_two` (the exact form of
`ε^{1/2}|log ε| ≲ 1`, which is what makes the pigeonhole work),
`r324Step4_exists_large_frequency_factor` ("one of the above factors
must shift the frequency by `≳ ε^{1/2}L`"),
`r324Step4_exists_symbol_eighthOrder_decay` and
`exists_r324Step4_projected_symbol_decay` (the projection `ξ̃_ε` carries
`⟨ε²L⟩⁻⁸` because `ρ̂` is Schwartz), and
`r324Step4_centralDecay_of_composition` (the assembled `⟨ε²(α+β)⟩⁻⁸`).

## The combination

`r324Step4_deterministicMomentRHS_of_step23` multiplies the two
mechanisms against the single named hypothesis `R324Step23Output`
standing for the output of Steps 2–3, and lands in the frozen
`deterministicMomentRHS` consumed by `Main/DeterministicClosure.lean`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Step 4(A), the unpaired endpoint: `|Ĝ(β)| ≤ ⟨β⟩⁻²` -/

/-- **The unpaired external endpoint.**  When `m` is not involved in any
fully paired subinterval the `y`-integral is performed *after* the
removal of each `I_i` and *before* taking absolute values; it is the
plain Fourier coefficient of the Green kernel, whose modulus is exactly
`|Ĝ(β)| = ⟨β⟩⁻²`.  No `ε`-power is spent. -/
theorem r324Step4_norm_endpoint_integral_unpaired (b : Z4) (v : T4) :
    ‖∫ y, charT4 b y * ((greenFn (v - y) : ℝ) : ℂ) ∂paperMeasure‖ =
      paperSecondOrderModeDecay b := by
  rw [integral_charT4_mul_greenFn_shift b v, norm_mul, norm_charT4,
    one_mul, Complex.norm_real, Real.norm_eq_abs]
  have h0 : (0 : ℝ) ≤ (1 + paperModeNormSq b)⁻¹ := by
    unfold paperModeNormSq; positivity
  rw [abs_of_nonneg h0]
  rfl

/-! ## Step 4(A), the paired endpoint: `⟨β⟩⁻²|cos − 1| ≤ 2⟨β⟩⁻²` -/

/-- **The paired external endpoint.**  When `m` *is* involved in a fully
paired subinterval `[a, m]`, Step 1's calculation produces the factor
`⟨β⟩⁻²·|cos(β·(x_m − x_a)) − 1|`.  The paper bounds this by `2⟨β⟩⁻²`,
keeping the decay in `β` and giving up the factor `|x_m − x_a|²`. -/
theorem r324Step4_paired_endpoint_le_two (β : Z4) (u : T4) :
    paperSecondOrderModeDecay β * |r324CharacterCos β u - 1| ≤
      2 * paperSecondOrderModeDecay β := by
  have h := abs_r324CharacterCos_sub_one_le_two β u
  have h0 : (0 : ℝ) ≤ paperSecondOrderModeDecay β :=
    paperSecondOrderModeDecay_nonneg β
  nlinarith

/-- The endpoint budget the paper actually pays at one external
variable: `ε⁻²⟨b⟩⁻²`. -/
def r324Step4EndpointBudget (ε : ℝ) (b : Z4) : ℝ :=
  ε⁻¹ ^ (2 : ℕ) * paperSecondOrderModeDecay b

theorem r324Step4EndpointBudget_nonneg (ε : ℝ) (b : Z4) :
    0 ≤ r324Step4EndpointBudget ε b := by
  unfold r324Step4EndpointBudget
  exact mul_nonneg (by positivity) (paperSecondOrderModeDecay_nonneg b)

/-- The unpaired endpoint is the cheaper of the two cases: its exact
gain `⟨b⟩⁻²` already dominates the paired budget `ε⁻²⟨b⟩⁻²`, so the
paired case is the worst case and the paper's `ε⁻⁸` covers all four
external variables regardless of which are paired. -/
theorem r324Step4_unpaired_le_paired_budget
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (b : Z4) :
    paperSecondOrderModeDecay b ≤ r324Step4EndpointBudget ε b := by
  unfold r324Step4EndpointBudget
  have hinv : (1 : ℝ) ≤ ε⁻¹ ^ (2 : ℕ) := by
    have h1 : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
    nlinarith
  nlinarith [paperSecondOrderModeDecay_nonneg b]

/-! ## Step 4(A), the `ε⁻²` loss: `J̃_{2p,prim} ↦ J_{2p,prim}` -/

/-- **Giving up `|x_m − x_a|²` costs exactly `ε⁻²`.**  Dropping the
squared-distance insertion replaces the (4.4) majorant of
`J̃_{2p,prim}` by the (4.3) majorant of `J_{2p,prim}`, and the latter is
`ε⁻²` times the former.  This is the paper's "upon integration this
leads to a loss of `ε⁻²`", in its pointwise form. -/
theorem r324Step4_primitiveKernelMajorant_le_endpointBudget
    (C lam ε supportConstant : ℝ) (n : ℕ) (z : T4) (hε : 0 < ε) :
    primitiveKernelMajorant C lam ε supportConstant n z ≤
      ε⁻¹ ^ (2 : ℕ) *
        primitiveInsertedMajorant C lam ε supportConstant n z :=
  primitiveKernelMajorant_le_invSq_mul_inserted C lam ε supportConstant
    n z hε

/-! ## Step 4(A), the (4.17) integral with both endpoint decays kept -/

/-- Step 1's three integrations, **with the `⟨α⟩⁻²` produced by the
`x`-integral retained** instead of discarded against `1`.  Step 1 could
throw it away because it only needed `(Cλ)^m|log ε|⁻¹`; Step 4 keeps it,
which is the whole point of the endpoint mechanism. -/
theorem r324Step4_norm_r324Step1Integral_le {J : T4 → ℝ}
    (hJ : MemEClassT4 J) (α β : Z4)
    (hcos : Integrable (fun u => J u * (r324CharacterCos β u - 1))
      paperMeasure)
    (hsin : Integrable (fun u => J u * r324CharacterSin β u)
      paperMeasure) :
    ‖r324Step1Integral J α β‖ ≤
      r324PaperTorusMass *
        (paperSecondOrderModeDecay α * paperSecondOrderModeDecay β *
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
            paperSecondOrderModeDecay β * ‖I‖ := by
    funext xa
    rw [hF]
    simp only [norm_mul, norm_charT4, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (paperSecondOrderModeDecay_nonneg _)]
    ring
  calc
    ‖r324Step1Integral J α β‖ = ‖∫ xa, F xa ∂paperMeasure‖ := by
      unfold r324Step1Integral
      rw [hxa]
    _ ≤ ∫ xa, ‖F xa‖ ∂paperMeasure := norm_integral_le_integral_norm _
    _ = r324PaperTorusMass *
          (paperSecondOrderModeDecay α *
            paperSecondOrderModeDecay β * ‖I‖) := by
      rw [hnorm, integral_const, measureReal_def, paperMeasure_univ,
        ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
      rfl

/-- **Step 4(A) at one external pair, closed.**

This is the paper's Step 4 applied to Step 1's expression (4.17): the
`x`-endpoint is free, so its integration gains `|Ĝ(α)| = ⟨α⟩⁻²` with no
loss; the `y`-endpoint sits inside the fully paired subinterval `[a, m]`,
so its integration gains `⟨β⟩⁻²` only after `|cos(β·(x_m−x_a)) − 1|` has
been bounded by `2`, which forgoes the squared-distance insertion and
therefore replaces `J̃_{2p,prim}` by `J_{2p,prim}`, at the cost `ε⁻²`.

Compare `exists_r324Step1_bound`, which is the same integral estimated
with the insertion kept: there the output is `(Cλ)^{2p}|log ε|⁻¹` with no
frequency decay, here it is `⟨α⟩⁻²·ε⁻²⟨β⟩⁻²·(Cλ)^{2p}|log ε|⁻¹`. -/
theorem exists_r324Step4_endpointDecay_bound (ρ : SmoothCutoff) :
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
            paperSecondOrderModeDecay α * r324Step4EndpointBudget ε β *
              ((Cstep * lam) ^ (2 * p) / |Real.log ε|) := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨Cball, Creg, hCball, hCreg, hraw⟩ :=
    exists_norm_integral_primitiveKernelDiff_mul_r324CharacterCos_sub_one_le_raw
  set K : ℝ :=
    r324PaperTorusMass * (2 * (Cball * supportConstant ^ 2 + Creg))
    with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := r324PaperTorusMass_pos.le
    positivity
  refine ⟨C * (K + 1), by positivity, ?_⟩
  intro lam ε p hp G α β hlam hε hε1 hptrunc hlog hG hcos hsin
  obtain ⟨hJmem, _hJins, hbound⟩ :=
    hprop lam ε p hp G hlam hε hε1 hptrunc hG
  have hlog0 : (0 : ℝ) < |Real.log ε| := lt_of_lt_of_le one_pos hlog
  have hdecay0 :
      (0 : ℝ) ≤ paperSecondOrderModeDecay α * paperSecondOrderModeDecay β :=
    mul_nonneg (paperSecondOrderModeDecay_nonneg α)
      (paperSecondOrderModeDecay_nonneg β)
  have hA0 :
      (0 : ℝ) ≤
        paperSecondOrderModeDecay α * r324Step4EndpointBudget ε β :=
    mul_nonneg (paperSecondOrderModeDecay_nonneg α)
      (r324Step4EndpointBudget_nonneg ε β)
  have hI :=
    hraw ρ C supportConstant lam ε p hp G hε hsupport hlog hbound β
  have habsorb :
      (C * lam) ^ (2 * p) * K ≤ ((C * lam) * (K + 1)) ^ (2 * p) :=
    mul_constant_le_absorbed_even_pow
      (mul_nonneg hC.le hlam.le) hK0 hp
  calc
    ‖r324Step1Integral (primitiveKernelDiff ρ lam ε p hp G) α β‖ ≤
        r324PaperTorusMass *
          (paperSecondOrderModeDecay α * paperSecondOrderModeDecay β *
            ‖∫ u, ((primitiveKernelDiff ρ lam ε p hp G u *
              (r324CharacterCos β u - 1) : ℝ) : ℂ) ∂paperMeasure‖) :=
      r324Step4_norm_r324Step1Integral_le hJmem α β hcos hsin
    _ ≤ r324PaperTorusMass *
          (paperSecondOrderModeDecay α * paperSecondOrderModeDecay β *
            (2 * ((C * lam) ^ (2 * p) *
              ((Cball * supportConstant ^ 2 + Creg) *
                ε⁻¹ ^ (2 : ℕ) / |Real.log ε|)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hI hdecay0)
        r324PaperTorusMass_pos.le
    _ = paperSecondOrderModeDecay α * r324Step4EndpointBudget ε β *
          ((C * lam) ^ (2 * p) * K / |Real.log ε|) := by
      unfold r324Step4EndpointBudget
      rw [hK]
      field_simp
    _ ≤ paperSecondOrderModeDecay α * r324Step4EndpointBudget ε β *
          (((C * lam) * (K + 1)) ^ (2 * p) / |Real.log ε|) := by
      refine mul_le_mul_of_nonneg_left ?_ hA0
      gcongr
    _ = paperSecondOrderModeDecay α * r324Step4EndpointBudget ε β *
          ((C * (K + 1) * lam) ^ (2 * p) / |Real.log ε|) := by
      rw [show (C * lam) * (K + 1) = C * (K + 1) * lam by ring]

/-! ## Step 4(A), the four external variables `(x, y, z, w)` -/

/-- **"By doing the same for each one of `(x, y, z, w)`, we can secure
the desired `⟨α⟩⁻⁴⟨β⟩⁻⁴` factor at the price of losing `ε⁻⁸`."**

The four external legs of (4.18) carry the modes `α, β, α, β`, and each
of the four integrations pays the endpoint budget `ε⁻²⟨·⟩⁻²` of
`exists_r324Step4_endpointDecay_bound`.  Their product is *exactly* the
proved `r324EndpointLoss ε α β = ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴`. -/
theorem r324Step4_fourEndpoint_budget_eq (ε : ℝ) (α β : Z4) :
    r324Step4EndpointBudget ε α * r324Step4EndpointBudget ε β *
        (r324Step4EndpointBudget ε α * r324Step4EndpointBudget ε β) =
      r324EndpointLoss ε α β := by
  unfold r324Step4EndpointBudget r324EndpointLoss
    paperSecondOrderModeDecay paperFourthOrderModeDecay
  rw [← four_endpoint_invSq_loss ε]
  simp only [← inv_pow]
  ring

/-! ## Step 4(B), the pigeonhole over the `|log ε|` factors -/

/-- **The inequality that makes the pigeonhole work.**  The paper's
composition has at most `|log ε|` factors and the threshold it wants is
`ε^{1/2}`; the pigeonhole is available exactly because
`ε^{1/2}·|log ε| ≲ 1`.  In the project's truncation length
`truncOrder ε = ⌊|log ε|⌋` the exact inequality is
`√ε · truncOrder ε ≤ 2`, the constant `2` coming from
`log x ≤ x^{1/2}/(1/2)`. -/
theorem r324Step4_sqrt_mul_truncOrder_le_two
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.sqrt ε * (truncOrder ε : ℝ) ≤ 2 := by
  have h := truncOrder_cast_le_two_mul_inv_sqrt hε hε1
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  calc
    Real.sqrt ε * (truncOrder ε : ℝ) ≤
        Real.sqrt ε * (2 * (Real.sqrt ε)⁻¹) :=
      mul_le_mul_of_nonneg_left h hs.le
    _ = 2 := by field_simp

/-- **"If this operator shifts the frequency by `|α+β| ∼ L`, then one of
the above factors must shift the frequency by `≳ ε^{1/2}L`."**

The factors of the composition shift the frequency by `increment i`, and
the total shift is `α + β` (frequency conservation).  Since there are at
most `truncOrder ε` factors and `√ε · truncOrder ε ≤ 2`, one factor
carries at least `(√ε/2)·L`. -/
theorem r324Step4_exists_large_frequency_factor
    {N : ℕ} (hN : 0 < N)
    (δ : Fin N → EuclideanSpace ℝ (Fin dim))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hNtrunc : N ≤ truncOrder ε)
    {α β : Z4}
    (hcons : (∑ j, δ j) = z4EuclideanFrequency (α + β)) :
    ∃ i : Fin N,
      (Real.sqrt ε / 2) * ‖z4EuclideanFrequency (α + β)‖ ≤ ‖δ i‖ := by
  obtain ⟨i, hi⟩ :=
    exists_frequency_increment_at_truncation_scale N hN δ ε hε hε1 hNtrunc
  exact ⟨i, by rwa [hcons] at hi⟩

/-! ## Step 4(B), the projection `ξ_ε ↦ ξ̃_ε` and its Schwartz decay -/

/-- **"because `ρ̂` is Schwartz".**  The cutoff symbol carries a full
eighth-order bracket: `‖ρ̂(ξ)‖ ≤ C⟨ξ⟩⁻⁸`.  This is the only property of
the mollifier that Step 4(B) uses. -/
theorem r324Step4_exists_symbol_eighthOrder_decay (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : R4,
      ‖fourierR4 ρ ξ‖ ≤
        C * eighthOrderFrequencyDecay
          ‖SmoothCutoff.euclideanFrequency ξ‖ := by
  obtain ⟨C8, hC8, hbound⟩ := ρ.exists_fourierR4_one_add_norm_bound_nat 8
  refine ⟨C8, hC8, fun ξ => ?_⟩
  set x : ℝ := ‖SmoothCutoff.euclideanFrequency ξ‖ with hxdef
  have hx0 : 0 ≤ x := norm_nonneg _
  have hkey : (1 + x ^ 2) ^ 4 ≤ (1 + x) ^ 8 := by
    have h : 1 + x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
    calc
      (1 + x ^ 2) ^ 4 ≤ ((1 + x) ^ 2) ^ 4 :=
        pow_le_pow_left₀ (by positivity) h 4
      _ = (1 + x) ^ 8 := by ring
  have hbase : (0 : ℝ) < (1 + x ^ 2) ^ 4 := by positivity
  have hsymb := hbound ξ
  rw [← hxdef] at hsymb
  rw [eighthOrderFrequencyDecay, le_mul_inv_iff₀ hbase]
  calc
    ‖fourierR4 ρ ξ‖ * (1 + x ^ 2) ^ 4 ≤
        ‖fourierR4 ρ ξ‖ * (1 + x) ^ 8 :=
      mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
    _ = (1 + x) ^ 8 * ‖fourierR4 ρ ξ‖ := by ring
    _ ≤ C8 := hsymb

/-- **"For this factor we may replace `ξ_ε` by its projection `ξ̃_ε` to
frequencies `≳ ε^{1/2}L`, which carries a decay factor `⟨ε²L⟩⁻⁸`."**

Once a factor of the composition is known to shift the frequency by at
least `(√ε/2)L`, its symbol may be replaced by the projected symbol,
whose size is `C⟨ε²L⟩⁻⁸`: the Schwartz bracket of
`r324Step4_exists_symbol_eighthOrder_decay` is evaluated at the routed
frequency and then compared to the `ε²` scale, using `ε² ≤ √ε/2` for
`ε ≤ 1/4`.  The paper writes this out for `L ≥ ε⁻²`, where the bracket
is genuinely small; the inequality itself holds at every `L ≥ 0`. -/
theorem exists_r324Step4_projected_symbol_decay (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε L : ℝ) (ξ : R4),
      0 < ε → ε ≤ 1 / 4 → 0 ≤ L →
      (Real.sqrt ε / 2) * L ≤ ‖SmoothCutoff.euclideanFrequency ξ‖ →
        ‖fourierR4 ρ ξ‖ ≤ C * eighthOrderFrequencyDecay (ε ^ 2 * L) := by
  obtain ⟨C, hC, hsymb⟩ := r324Step4_exists_symbol_eighthOrder_decay ρ
  refine ⟨C, hC, fun ε L ξ hε hεsmall hL hroute => ?_⟩
  exact (hsymb ξ).trans
    (mul_le_mul_of_nonneg_left
      (truncation_routed_decay_le_eps_sq_decay hε hεsmall hL hroute)
      hC.le)

/-! ## Step 4(B), assembled -/

/-- **Step 4(B) of §4.2.**

`P_m` is the renormalization of a composition of at most `|log ε|`
factors, each a Fourier multiplier (convolution by `G`) or a
frequency shift (multiplication by `ξ_ε`).  A
`CountableCentralRoutedMomentDecomposition` is exactly that datum: per
term, at most `truncOrder ε` frequency increments whose sum is the total
shift `α + β`, together with the projected-symbol bound
`‖term‖ ≤ weight·⟨increment⟩⁻⁸` supplied by
`exists_r324Step4_projected_symbol_decay`.  The pigeonhole
`r324Step4_exists_large_frequency_factor` selects the factor shifting by
`≳ ε^{1/2}L`, and its projected symbol yields `⟨ε²(α+β)⟩⁻⁸`. -/
theorem r324Step4_centralDecay_of_composition
    {ρ : SmoothCutoff} {lam ε weightBudget : ℝ} {m : ℕ} {α β : Z4}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hred : CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β weightBudget) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      weightBudget *
        eighthOrderFrequencyDecay
          (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) := by
  obtain ⟨d⟩ := hred
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  set D : ℝ :=
    eighthOrderFrequencyDecay
      (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) with hD
  have hterm : ∀ a : ℕ, ‖d.term a‖ ≤ d.weight a * D := by
    intro a
    obtain ⟨i, hi⟩ :=
      r324Step4_exists_large_frequency_factor
        (d.incrementCount_pos a) (d.increment a) hε hε1
        (d.incrementCount_le_trunc a) (d.increment_sum a)
    have hsel :
        eighthOrderFrequencyDecay ‖d.increment a i‖ ≤ D :=
      truncation_routed_decay_le_eps_sq_decay hε hεsmall
        (norm_nonneg _) hi
    exact (d.term_le_increment_decay a i).trans
      (mul_le_mul_of_nonneg_left hsel (d.weight_nonneg a))
  have hscaled : Summable fun a : ℕ => d.weight a * D :=
    d.summable_weight.mul_right _
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ =
        ‖∑' a, d.term a‖ := by rw [d.sum_eq]
    _ ≤ ∑' a, ‖d.term a‖ :=
      norm_tsum_le_tsum_norm d.summable_term.norm
    _ ≤ ∑' a, d.weight a * D :=
      d.summable_term.norm.tsum_le_tsum hterm hscaled
    _ = (∑' a, d.weight a) * D := by rw [tsum_mul_right]
    _ ≤ weightBudget * D :=
      mul_le_mul_of_nonneg_right d.tsum_weight_le
        (eighthOrderFrequencyDecay_nonneg _)

/-! ## The combination: (3.24) with the full right-hand side -/

/-- **The one input Step 4 takes from Steps 2–3.**

Steps 2 and 3 prove (3.24) *with `1` on the right*: after the positional
`O(C^m)` count of the interval configurations (Step 2) and the reduction
of the nested chain `[a_1,b_1] ⊃ [a_2,b_2] ⊃ …` (Step 3), the second
moment obeys `(Cλ)^{2m}|log ε|⁻¹ ≤ λ_ε²·C(Cλ)^{2m−2}`.  Step 4 takes
that number as a black box `amplitude` and multiplies the two decay
factors into it. -/
def R324Step23Output (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (amplitude : ℝ) : Prop :=
  ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤ amplitude

/-- **Step 4 of §4.2, complete.**

Mechanism (A) — one endpoint budget `ε⁻²⟨·⟩⁻²` per external variable of
`(x, y, z, w)`, whose product is `ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴` — is carried by the
routing weights; mechanism (B) — the `ε^{1/2}` pigeonhole over the at
most `|log ε|` factors plus the Schwartz projection — supplies
`⟨ε²(α+β)⟩⁻⁸`.  Together with the Steps 2–3 output `1` this is (3.24)
with the full right-hand side

`min(1, ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε²(α+β)⟩⁻⁸)`. -/
theorem r324Step4_paperDecay_of_step23
    {ρ : SmoothCutoff} {lam ε weightBudget amplitude : ℝ}
    {m : ℕ} {α β : Z4}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hstep23 : R324Step23Output ρ lam ε m α β amplitude)
    (hred : CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β weightBudget)
    (hendpoint : weightBudget ≤
      amplitude *
        (r324Step4EndpointBudget ε α * r324Step4EndpointBudget ε β *
          (r324Step4EndpointBudget ε α *
            r324Step4EndpointBudget ε β))) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      amplitude * min 1 (paperDeterministicMomentDecay ε α β) := by
  have hamp0 : 0 ≤ amplitude := le_trans (norm_nonneg _) hstep23
  set D : ℝ :=
    eighthOrderFrequencyDecay
      (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) with hD
  have hD0 : 0 ≤ D := eighthOrderFrequencyDecay_nonneg _
  have hcentral :=
    r324Step4_centralDecay_of_composition hε hεsmall hred
  have hbranch :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        amplitude * paperDeterministicMomentDecay ε α β := by
    calc
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          weightBudget * D := hcentral
      _ ≤ (amplitude * r324EndpointLoss ε α β) * D := by
        refine mul_le_mul_of_nonneg_right ?_ hD0
        rwa [r324Step4_fourEndpoint_budget_eq ε α β] at hendpoint
      _ = amplitude * paperDeterministicMomentDecay ε α β := by
        rw [paperDeterministicMomentDecay_eq_endpoint_mul_central, hD]
        ring
  have hsplit :
      amplitude * min 1 (paperDeterministicMomentDecay ε α β) =
        min (amplitude * 1)
          (amplitude * paperDeterministicMomentDecay ε α β) := by
    rcases le_total (1 : ℝ) (paperDeterministicMomentDecay ε α β) with
      h | h
    · rw [min_eq_left h,
        min_eq_left (mul_le_mul_of_nonneg_left h hamp0)]
    · rw [min_eq_right h,
        min_eq_right (mul_le_mul_of_nonneg_left h hamp0)]
  rw [hsplit]
  exact le_min (by rw [mul_one]; exact hstep23) hbranch

/-- **Step 4 of §4.2, landed in the frozen deterministic right side.**

This is the shape consumed by `Main/DeterministicClosure.lean`'s `hdet`:
`deterministicMomentRHS`, whose `min` bracket is exactly the two branches
of (3.24).  The passage from the paper's Euclidean bracket to the frozen
sup-norm ledger is the proved `paperDeterministicMomentDecay_le`,
applied inside `r324HdetAssembly_rhs_glue`. -/
theorem r324Step4_deterministicMomentRHS_of_step23
    {ρ : SmoothCutoff}
    {lam ε weightBudget amplitude outerConstant powerConstant : ℝ}
    {m : ℕ} {α β : Z4}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hstep23 : R324Step23Output ρ lam ε m α β amplitude)
    (hred : CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β weightBudget)
    (hendpoint : weightBudget ≤
      amplitude *
        (r324Step4EndpointBudget ε α * r324Step4EndpointBudget ε β *
          (r324Step4EndpointBudget ε α *
            r324Step4EndpointBudget ε β)))
    (hamp : amplitude ≤
      lamEps lam ε ^ 2 * outerConstant *
        (powerConstant * lam) ^ (2 * m - 2)) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      deterministicMomentRHS outerConstant powerConstant lam ε m α β :=
  r324HdetAssembly_rhs_glue
    (r324Step4_paperDecay_of_step23 hε hεsmall hstep23 hred hendpoint)
    hamp (le_trans (norm_nonneg _) hstep23)

end

end Anderson4D
