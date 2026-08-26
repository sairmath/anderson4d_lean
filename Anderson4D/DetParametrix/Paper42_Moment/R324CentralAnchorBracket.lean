import Anderson4D.DetParametrix.Paper42_Moment.R324BetaTailSplit
import Anderson4D.DetParametrix.Paper42_Moment.R324CollapsePi

/-!
# The central bracket: anchor resolution of the quadruple harvest

`R324BetaQuadBracketLedger` is the residual tail-region estimate:
tail region: the quadruple harvest `r324BetaQuadHarvest`, in which all
four external characters have been transported to internal anchors, must
carry the `ε`-**free** eighth-order bracket
`⟨‖freq (α+β)‖⟩⁻⁸` at the conserved mode.

This file resolves the two *transported tail characters* — which are
differences `charT4 β (v_{m-1}) - charT4 β (v_a)` whose anchor `a`
depends on the entity — into four **anchor-resolved harvests** in which
every character sits at a *fixed* internal coordinate slot, outside the
entity sum.  That is exactly the shape the general collapse machine
consumes: one character per internal coordinate.

The corresponding analytic estimate is named `R324CentralAnchorLedger`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Anchor-indexed characters -/

/-- The character of mode `β` at an *optional* internal anchor: `0` at
`none`.  Both terms of `r324BetaTailChar` are of this form, so the
transported tail character is literally a difference of two of them. -/
def r324CentralAnchorChar {m : ℕ} (β : Z4) (a : Option (Fin m))
    (u : Fin m → T4) : ℂ :=
  match a with
  | none => 0
  | some b => charT4 β (u b)

theorem norm_r324CentralAnchorChar_le {m : ℕ} (β : Z4) (a : Option (Fin m))
    (u : Fin m → T4) : ‖r324CentralAnchorChar β a u‖ ≤ 1 := by
  cases a with
  | none => simp [r324CentralAnchorChar]
  | some b => simp [r324CentralAnchorChar, norm_charT4]

/-- **The transported tail character is an anchor difference.** -/
theorem r324BetaTailChar_eq_anchorChars {m : ℕ} (β : Z4) (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (v : Fin m → T4) :
    r324BetaTailChar β hm κ v =
      r324CentralAnchorChar β (some (r324TailLastIdx hm)) v -
        r324CentralAnchorChar β (r324TailAnchor κ) v := by
  unfold r324BetaTailChar r324CentralAnchorChar
  cases r324TailAnchor κ <;> rfl

/-! ## The anchor-resolved harvest -/

/-- **The anchor-resolved integrand.**  All four external characters sit
at *fixed* internal coordinate slots — `α` at the left head anchor, `-α`
at the right head anchor, `β` at the left tail slot `aL e` and `-β` at
the right tail slot `aR e` — multiplying the character-free real core
(two tailless chain products and the internal covariance product).  The
anchor slots are allowed to depend on the entity, which is exactly what
the entity-dependent tail shortcut needs, and is harmless for the
collapse machine because it consumes one entity at a time. -/
def r324CentralAnchorIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m))
    (aL aR : MomentContraction m → Option (Fin m))
    (v : Fin (2 * m) → T4) : ℂ :=
  charT4 α (v (leftMomentIndex ⟨0, hm⟩)) *
      charT4 (-α) (v (rightMomentIndex ⟨0, hm⟩)) *
    ∑ e ∈ F,
      r324CentralAnchorChar β (aL e) (fun i => v (leftMomentIndex i)) *
        r324CentralAnchorChar (-β) (aR e) (fun i => v (rightMomentIndex i)) *
        ((r324DetTaillessV ρ ε m e.1 (fun i => v (leftMomentIndex i)) *
          r324DetTaillessV ρ ε m e.2.1 (fun i => v (rightMomentIndex i)) *
          momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v : ℝ) : ℂ)

/-- The anchor-resolved harvest: the internal integral of the
anchor-resolved integrand. -/
def r324CentralAnchorHarvest
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m))
    (aL aR : MomentContraction m → Option (Fin m)) : ℂ :=
  ∫ v : Fin (2 * m) → T4,
    r324CentralAnchorIntegrand ρ ε m α β hm F aL aR v
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

/-- **The central-anchor ledger.**  The analytic residue of clause B
after anchor resolution: on the tail region every anchor-resolved
harvest is integrable and carries the `ε`-free central bracket at the
conserved mode `α + β`.

Compared with `R324BetaQuadBracketLedger` this is a statement about a
plain four-character Fourier coefficient of a *real* core — no
differences, no entity-dependent characters — i.e. precisely the input
format of the general collapse machine
(`r324Col_piChain_integral`): one character per internal coordinate,
with the conserved mode `α + β` routed through the two head anchors. -/
def R324CentralAnchorLedger (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        r324CMBracketWeight ε α β ≤ 1 →
          ∀ (F : Finset (MomentContraction m)) (hm : 0 < m)
            (aL aR : MomentContraction m → Option (Fin m)),
            Integrable (r324CentralAnchorIntegrand ρ ε m α β hm F aL aR)
                (Measure.pi fun _ : Fin (2 * m) => paperMeasure) ∧
              ‖r324CentralAnchorHarvest ρ ε m α β hm F aL aR‖ ≤
                K ^ m * |Real.log ε| ^ (m - 1) *
                  eighthOrderFrequencyDecay
                    ‖z4EuclideanFrequency (α + β)‖

/-! ## Resolving the quadruple harvest into four anchor harvests -/

/-- The constant "tail slot" anchor assignment. -/
def r324CentralLastAnchor {m : ℕ} (hm : 0 < m) :
    MomentContraction m → Option (Fin m) :=
  fun _ => some (r324TailLastIdx hm)

/-- The left shortcut anchor assignment. -/
def r324CentralLeftAnchor {m : ℕ} :
    MomentContraction m → Option (Fin m) :=
  fun e => r324TailAnchor e.1

/-- The right shortcut anchor assignment. -/
def r324CentralRightAnchor {m : ℕ} :
    MomentContraction m → Option (Fin m) :=
  fun e => r324TailAnchor e.2.1

/-- **Anchor resolution, pointwise.**  Expanding the two transported tail
characters as anchor differences splits the quadruple-harvest integrand
into the four anchor-resolved integrands with alternating signs. -/
theorem r324CentralAnchor_integrand_pointwise
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (α β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m)) (v : Fin (2 * m) → T4) :
    charT4 α (v (leftMomentIndex ⟨0, hm⟩)) *
          charT4 (-α) (v (rightMomentIndex ⟨0, hm⟩)) *
        r324BetaQuadCore ρ ε m β hm F v =
      r324CentralAnchorIntegrand ρ ε m α β hm F
          (r324CentralLastAnchor hm) (r324CentralLastAnchor hm) v -
        r324CentralAnchorIntegrand ρ ε m α β hm F
          (r324CentralLastAnchor hm) r324CentralRightAnchor v -
        r324CentralAnchorIntegrand ρ ε m α β hm F
          r324CentralLeftAnchor (r324CentralLastAnchor hm) v +
        r324CentralAnchorIntegrand ρ ε m α β hm F
          r324CentralLeftAnchor r324CentralRightAnchor v := by
  unfold r324CentralAnchorIntegrand r324BetaQuadCore
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _he => ?_
  rw [r324BetaTailChar_eq_anchorChars β hm e.1,
    r324BetaTailChar_eq_anchorChars (-β) hm e.2.1]
  unfold r324CentralLastAnchor r324CentralLeftAnchor r324CentralRightAnchor
  ring

/-- **Anchor resolution of the quadruple harvest.**  Given integrability
of the four anchor-resolved integrands, the quadruple harvest is their
alternating sum. -/
theorem r324BetaQuadHarvest_eq_anchorCombination
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (α β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m))
    (h₁ : Integrable (r324CentralAnchorIntegrand ρ ε m α β hm F
        (r324CentralLastAnchor hm) (r324CentralLastAnchor hm))
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure))
    (h₂ : Integrable (r324CentralAnchorIntegrand ρ ε m α β hm F
        (r324CentralLastAnchor hm) r324CentralRightAnchor)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure))
    (h₃ : Integrable (r324CentralAnchorIntegrand ρ ε m α β hm F
        r324CentralLeftAnchor (r324CentralLastAnchor hm))
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure))
    (h₄ : Integrable (r324CentralAnchorIntegrand ρ ε m α β hm F
        r324CentralLeftAnchor r324CentralRightAnchor)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure)) :
    r324BetaQuadHarvest ρ ε m α β hm F =
      r324CentralAnchorHarvest ρ ε m α β hm F
          (r324CentralLastAnchor hm) (r324CentralLastAnchor hm) -
        r324CentralAnchorHarvest ρ ε m α β hm F
          (r324CentralLastAnchor hm) r324CentralRightAnchor -
        r324CentralAnchorHarvest ρ ε m α β hm F
          r324CentralLeftAnchor (r324CentralLastAnchor hm) +
        r324CentralAnchorHarvest ρ ε m α β hm F
          r324CentralLeftAnchor r324CentralRightAnchor := by
  have hpt : ∀ v : Fin (2 * m) → T4,
      charT4 α (v (leftMomentIndex ⟨0, hm⟩)) *
            charT4 (-α) (v (rightMomentIndex ⟨0, hm⟩)) *
          r324BetaQuadCore ρ ε m β hm F v =
        (r324CentralAnchorIntegrand ρ ε m α β hm F
              (r324CentralLastAnchor hm) (r324CentralLastAnchor hm) -
            r324CentralAnchorIntegrand ρ ε m α β hm F
              (r324CentralLastAnchor hm) r324CentralRightAnchor -
            r324CentralAnchorIntegrand ρ ε m α β hm F
              r324CentralLeftAnchor (r324CentralLastAnchor hm) +
            r324CentralAnchorIntegrand ρ ε m α β hm F
              r324CentralLeftAnchor r324CentralRightAnchor) v := by
    intro v
    simp only [Pi.add_apply, Pi.sub_apply]
    exact r324CentralAnchor_integrand_pointwise ρ ε α β hm F v
  unfold r324BetaQuadHarvest r324CentralAnchorHarvest
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add' ((h₁.sub h₂).sub h₃) h₄, integral_sub' (h₁.sub h₂) h₃,
    integral_sub' h₁ h₂]

/-! ## The central bracket from the anchor ledger -/

/-- **The central bracket, from anchor resolution.**  The four anchor
harvests cost a factor `4`, absorbed into the base constant. -/
theorem R324BetaQuadBracketLedger_of_centralAnchor
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324CentralAnchorLedger ρ K) :
    R324BetaQuadBracketLedger ρ (4 * K) := by
  intro ε m α β hε hε1 hlog hm2 hcap hW F hm
  obtain ⟨h₁i, h₁b⟩ := h m α β hε hε1 hlog hm2 hcap hW F hm
    (r324CentralLastAnchor hm) (r324CentralLastAnchor hm)
  obtain ⟨h₂i, h₂b⟩ := h m α β hε hε1 hlog hm2 hcap hW F hm
    (r324CentralLastAnchor hm) r324CentralRightAnchor
  obtain ⟨h₃i, h₃b⟩ := h m α β hε hε1 hlog hm2 hcap hW F hm
    r324CentralLeftAnchor (r324CentralLastAnchor hm)
  obtain ⟨h₄i, h₄b⟩ := h m α β hε hε1 hlog hm2 hcap hW F hm
    r324CentralLeftAnchor r324CentralRightAnchor
  set B : ℝ := K ^ m * |Real.log ε| ^ (m - 1) *
    eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖ with hB
  have hsplit :
      ‖r324BetaQuadHarvest ρ ε m α β hm F‖ ≤ 4 * B := by
    rw [r324BetaQuadHarvest_eq_anchorCombination ρ ε α β hm F h₁i h₂i h₃i h₄i]
    calc
      ‖_ - _ - _ + _‖ ≤ ‖_ - _ - _‖ + ‖_‖ := norm_add_le _ _
      _ ≤ (‖_ - _‖ + ‖_‖) + ‖_‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((‖_‖ + ‖_‖) + ‖_‖) + ‖_‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ((B + B) + B) + B := by gcongr
      _ = 4 * B := by ring
  refine hsplit.trans ?_
  have hEnn : (0 : ℝ) ≤ |Real.log ε| ^ (m - 1) *
      eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖ :=
    mul_nonneg (by positivity) (eighthOrderFrequencyDecay_nonneg _)
  have hKm : (0 : ℝ) ≤ K ^ m := pow_nonneg hK m
  have hfour : (4 : ℝ) ≤ 4 ^ m := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ m := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
  have hstep : 4 * (K ^ m) ≤ (4 * K) ^ m := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hfour hKm
  calc
    4 * B = (4 * K ^ m) * (|Real.log ε| ^ (m - 1) *
        eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖) := by
      rw [hB]; ring
    _ ≤ ((4 * K) ^ m) * (|Real.log ε| ^ (m - 1) *
        eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖) :=
      mul_le_mul_of_nonneg_right hstep hEnn
    _ = (4 * K) ^ m * |Real.log ε| ^ (m - 1) *
        eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖ := by ring

/-! ## Which mechanism can produce the `ε`-free central bracket

Two candidate mechanisms are ruled in / out here by explicit arithmetic.
-/

theorem paperModeNormSq_add_le (α β : Z4) :
    paperModeNormSq (α + β) ≤
      2 * paperModeNormSq α + 2 * paperModeNormSq β := by
  unfold paperModeNormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _hi => ?_
  simp only [Pi.add_apply]
  push_cast
  nlinarith [sq_nonneg ((α i : ℝ) - (β i : ℝ))]

/-- **Peetre for the paper bracket.** -/
theorem r324Central_peetre (α β : Z4) :
    1 + paperModeNormSq (α + β) ≤
      2 * ((1 + paperModeNormSq α) * (1 + paperModeNormSq β)) := by
  have hα : (0 : ℝ) ≤ paperModeNormSq α := by
    unfold paperModeNormSq; positivity
  have hβ : (0 : ℝ) ≤ paperModeNormSq β := by
    unfold paperModeNormSq; positivity
  nlinarith [paperModeNormSq_add_le α β, mul_nonneg hα hβ]

/-- **The endpoint trade, exactly priced.**  The *square* of the two
endpoint decays is dominated by the central bracket (up to `16`), and the
square is sharp: at `β = α` the bracket is genuinely smaller than the
endpoint product itself.  So buying the central bracket out of endpoint
decay costs `⟨α⟩⁻⁸⟨β⟩⁻⁸` on the harvest, i.e. `⟨α⟩⁻¹²⟨β⟩⁻¹²` on the
entity sum — three endpoint harvests per external mode, where the four
external Green legs supply only one each.  The trade is therefore *not*
the mechanism. -/
theorem r324Central_endpointTrade_sq (α β : Z4) :
    (paperFourthOrderModeDecay α * paperFourthOrderModeDecay β) ^ 2 ≤
      16 * eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖ := by
  have hα : (0 : ℝ) < 1 + paperModeNormSq α := by
    unfold paperModeNormSq; positivity
  have hβ : (0 : ℝ) < 1 + paperModeNormSq β := by
    unfold paperModeNormSq; positivity
  have hγ : (0 : ℝ) < 1 + paperModeNormSq (α + β) := by
    unfold paperModeNormSq; positivity
  have hkey : (1 + paperModeNormSq (α + β)) ^ 4 ≤
      16 * ((1 + paperModeNormSq α) * (1 + paperModeNormSq β)) ^ 4 := by
    have h := r324Central_peetre α β
    calc (1 + paperModeNormSq (α + β)) ^ 4 ≤
        (2 * ((1 + paperModeNormSq α) * (1 + paperModeNormSq β))) ^ 4 := by
          apply pow_le_pow_left₀ hγ.le h
      _ = 16 * ((1 + paperModeNormSq α) * (1 + paperModeNormSq β)) ^ 4 := by
          ring
  unfold paperFourthOrderModeDecay eighthOrderFrequencyDecay
  rw [norm_sq_z4EuclideanFrequency]
  have h1 : (((1 + paperModeNormSq α) ^ 2)⁻¹ *
        ((1 + paperModeNormSq β) ^ 2)⁻¹) ^ 2 =
      1 / ((1 + paperModeNormSq α) * (1 + paperModeNormSq β)) ^ 4 := by
    field_simp
  have h2 : (16 : ℝ) * ((1 + paperModeNormSq (α + β)) ^ 4)⁻¹ =
      16 / (1 + paperModeNormSq (α + β)) ^ 4 := by
    ring
  rw [h1, h2, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hkey]

/-- **The half-symbol route is `ε⁻¹⁶` away from the target.**  The
covariance symbols only see `ε k`, so the product bracket produced by
`r324HdetAssembly_prod_eighthDecay_le` is `ε⁻⁸⟨ε‖α+β‖⟩⁻⁸`, which
exceeds the `ε`-free bracket by exactly the endpoint loss squared.  On
the capped range `m ≤ truncOrder ε` the factor `ε⁻¹⁶ = e^{16|log ε|}`
is not absorbable into `K^m|log ε|^{m-1}` (which only sees `m ≤ |log ε|`
copies), so the half-symbol harvest cannot supply the `ε`-free central
bracket either. -/
theorem r324Central_epsScale_gap {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : ℝ) :
    ε⁻¹ ^ (8 : ℕ) * eighthOrderFrequencyDecay (ε * x) ≤
      ε⁻¹ ^ (16 : ℕ) * eighthOrderFrequencyDecay x := by
  have hlow : ε ^ 2 * (1 + x ^ 2) ≤ 1 + (ε * x) ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg ε, sq_nonneg (1 - ε)]
  have hpow : (ε ^ 2 * (1 + x ^ 2)) ^ 4 ≤ (1 + (ε * x) ^ 2) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hlow 4
  have hmain : ε ^ (8 : ℕ) * eighthOrderFrequencyDecay (ε * x) ≤
      eighthOrderFrequencyDecay x := by
    unfold eighthOrderFrequencyDecay
    have e1 : ε ^ (8 : ℕ) * ((1 + (ε * x) ^ 2) ^ 4)⁻¹ =
        ε ^ (8 : ℕ) / (1 + (ε * x) ^ 2) ^ 4 := by ring
    have e2 : (((1 + x ^ 2) ^ 4)⁻¹ : ℝ) = 1 / (1 + x ^ 2) ^ 4 := by ring
    rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have e3 : ε ^ (8 : ℕ) * (1 + x ^ 2) ^ 4 = (ε ^ 2 * (1 + x ^ 2)) ^ 4 := by
      ring
    rw [e3]
    exact hpow
  have hεinv : (0 : ℝ) < ε⁻¹ ^ (16 : ℕ) := by positivity
  have hstep : ε⁻¹ ^ (8 : ℕ) * eighthOrderFrequencyDecay (ε * x) =
      ε⁻¹ ^ (16 : ℕ) * (ε ^ (8 : ℕ) * eighthOrderFrequencyDecay (ε * x)) := by
    have hεne : ε ≠ 0 := hε.ne'
    field_simp
  rw [hstep]
  exact mul_le_mul_of_nonneg_left hmain hεinv.le

/-! ## Where the `ε`-free bracket actually comes from

The proved chain collapse `r324Col_piChain_integral` evaluates a
`Green` chain carrying one character per internal coordinate to
`r324ColPiProp n q` times a character, and every factor of
`r324ColPiProp` is a bracket `⟨·⟩⁻²` at a **suffix sum** of the keys —
`ε`-free, because it comes from a Green edge and not from a covariance
symbol `ρ̂(εk)`.  With `α` at the head slot and `β` at the tail anchor
slot, the head suffix sum is exactly the conserved mode `α + β`: the
central bracket is produced by the Green edges downstream of the
anchors.  `r324Central_epsScale_gap` above shows that the competing half-symbol
mechanism misses the `ε`-free target by `ε⁻¹⁶`. -/

/-- The two-mode key assignment: `α` at the head slot, `β` at the tail
anchor slot `a`, nothing elsewhere. -/
def r324CentralKeys (α β : Z4) (a : ℕ) : ℕ → Z4 :=
  fun j => if j = 0 then α else if j = a then β else 0

/-- **Momentum conservation at the head bracket.**  The collapse's head
suffix sum for the two-mode key assignment is the conserved mode
`α + β`, so the head factor of `r324ColPiProp` is the `ε`-free bracket
`⟨α+β⟩⁻²`. -/
theorem r324ColPartial_centralKeys
    (α β : Z4) {a n : ℕ} (ha : 0 < a) (han : a < n) :
    r324ColPartial (r324CentralKeys α β a) n = α + β := by
  have hpt : ∀ j : ℕ, r324CentralKeys α β a j =
      (if j = 0 then α else 0) + (if j = a then β else 0) := by
    intro j
    unfold r324CentralKeys
    rcases eq_or_ne j 0 with hj | hj
    · subst hj
      rw [if_pos rfl, if_pos rfl, if_neg (by omega), add_zero]
    · rw [if_neg hj, if_neg hj]
      rcases eq_or_ne j a with hja | hja
      · rw [if_pos hja, zero_add]
      · rw [if_neg hja, add_zero]
  unfold r324ColPartial
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_range]
  rw [if_pos (by omega), if_pos han]

/-- The head factor of the collapse product is the `ε`-free central
bracket. -/
theorem r324ColBrk_centralKeys
    (α β : Z4) {a n : ℕ} (ha : 0 < a) (han : a < n) :
    r324ColBrk (r324ColPartial (r324CentralKeys α β a) n) =
      paperSecondOrderModeDecay (α + β) := by
  rw [r324ColPartial_centralKeys α β ha han]
  rfl

end

end Anderson4D
