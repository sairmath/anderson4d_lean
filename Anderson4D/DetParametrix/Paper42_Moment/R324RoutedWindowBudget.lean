import Anderson4D.DetParametrix.Paper42_Moment.R324VHFRoutedPigeonhole
import Anderson4D.DetParametrix.Paper42_Moment.R324FinalDeterministicClosure

/-!
# The Green-windowed routed budget at the frozen paper amplitude

**(A) The exact routed obligation.**  The capstone consumer
`exists_deterministicMoment_paper_bound_of_refinedIntegrated_and_countable`
fixes `outerConstant` from `(primitiveConstant, supportConstant)` alone
and then demands, at every admissible `(ρ, lam, ε, m, α, β)`, the routed
output at the frozen amplitude

`CountableCentralRoutedMomentReductionOutput ρ lam ε m α β
  ((lamEps lam ε ^ 2 * outerConstant *
      ((16 * primitiveConstant) * lam) ^ (2*m-2)) *
    r324EndpointLoss ε α β)`,

with `r324EndpointLoss ε α β = ε⁻⁸ · ⟨α⟩⁻⁴ · ⟨β⟩⁻⁴`.  Through the two
proved honest constructors this is *equivalent* to two scalar
ledgers on the exact route weights (both already carrying the endpoint
factor `16⟨α⟩⁻⁴⟨β⟩⁻⁴` extracted from the four endpoint Fourier
integrations):

* `α + β ≠ 0`:  `∑'_{(p,route)} r324RefinedEndpointNonzeroRouteWeight ≤ W`;
* `α + β = 0`:  `∑'_{(p,n)} r324ZeroShiftGroupedWeight ≤ W`.

Since `|λ_ε|^{2m} · L^{m-1} = λ_ε² · λ^{2m-2} / 1` (with `L = |log ε|`),
the frozen amplitude is reached **iff** the physical route mass obeys
the Green-windowed value — one endpoint sacrifice `ε⁻⁸` for the marked
pair and one diagonal Green window `C·L` for each of the other `m - 1`
pairs:

`∑' weights ≤ 16⟨α⟩⁻⁴⟨β⟩⁻⁴ · |λ_ε|^{2m} · C^m · L^{m-1} · ε⁻⁸`,

together with the `ε`-free comparison
`16 · C^m · λ^{2m-2} ≤ outerConstant · ((16·primitiveConstant)·λ)^{2m-2}`.
This file states the windowed ledgers as the two named Props below,
proves the general-`m` reduction (routed output at the frozen amplitude
*from* the Props), and composes with the capstone consumer.

The scalar raw ledger cannot discharge these Props' role: its raw mass
already scales as `c·ε⁻¹²` at `m = 1`, against a target of `K·ε⁻⁸`.
The Props instead live on the *route weights themselves* — physical
integrals of the fibre-summed internal core with the Green skeleton
still inside — not on the norm-inside raw covariance series, so the
raw total-mass obstruction does not apply to them.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- **The routed per-term window ledger (nonzero shift).**  The total
corrected nonzero-route weight — per term the physical integral of the
signed fibre-summed internal core with its routing slot costs, the
Green windows retained — is bounded by the windowed value
`C^m · L^{m-1} · ε⁻⁸` at the coupling weight `|λ_ε|^{2m}` and the
extracted endpoint factor.  This is the routed-branch analogue of the
uniform branch's `R324GeneralPeelFibreLogBound`: same physical layer
(norm after the fibre sum), with the route resolution and one marked
slot cost added, and the value upgraded from `K^m·L^{m-1}` to
`C^m·L^{m-1}·ε⁻⁸` by the endpoint sacrifice. -/
def R324RoutedPerTermWindowBound
    (ρ : SmoothCutoff) (lam : ℝ) (m : ℕ) (C : ℝ) : Prop :=
  ∀ (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
    1 ≤ |Real.log ε| →
    ∀ (hmtrunc : m ≤ truncOrder ε) (α β : Z4)
      (hexternal : α + β ≠ 0),
      (∑' pr :
          R324RefinedScheduleIndex m ×
            SmoothCutoff.R324NonzeroRouteLabel m,
        ρ.r324RefinedEndpointNonzeroRouteWeight
          lam hm ε α β hexternal hε hε1 hmtrunc
          pr.1 pr.2) ≤
        (16 * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) *
          (|lamEps lam ε| ^ (2 * m) *
            (C ^ m * |Real.log ε| ^ (m - 1) * ε⁻¹ ^ (8 : ℕ)))

/-- **The zero-shift window ledger.**  The same windowed value bounds
the grouped zero-shift weights (the `α + β = 0` branch, where every
routed increment is zero and no central decay is spent). -/
def R324RoutedZeroShiftWindowBound
    (ρ : SmoothCutoff) (lam : ℝ) (m : ℕ) (C : ℝ) : Prop :=
  ∀ (hm : 0 < m) (ε : ℝ), 0 < ε → ε ≤ 1 →
    1 ≤ |Real.log ε| → m ≤ truncOrder ε →
    ∀ α β : Z4, α + β = 0 →
      (∑' p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324ZeroShiftGroupedWeight lam hm ε α β p) ≤
        (16 * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) *
          (|lamEps lam ε| ^ (2 * m) *
            (C ^ m * |Real.log ε| ^ (m - 1) * ε⁻¹ ^ (8 : ℕ)))

/-- **Amplitude bookkeeping.**  The windowed physical value *is* the
endpoint-loss form of the amplitude `λ_ε² · (16·C^m·λ^{2m-2})`:
`|λ_ε|^{2m} · L^{m-1}` collapses to `λ_ε² · λ^{2m-2}` exactly. -/
theorem r324RoutedWindow_budget_eq
    {lam ε C : ℝ} (hlog : 1 ≤ |Real.log ε|)
    {m : ℕ} (hm : 0 < m) (α β : Z4) :
    (16 * paperFourthOrderModeDecay α *
        paperFourthOrderModeDecay β) *
      (|lamEps lam ε| ^ (2 * m) *
        (C ^ m * |Real.log ε| ^ (m - 1) * ε⁻¹ ^ (8 : ℕ))) =
    (lamEps lam ε ^ 2 * (16 * C ^ m * lam ^ (2 * m - 2))) *
      r324EndpointLoss ε α β := by
  have hlogPos : 0 < |Real.log ε| := lt_of_lt_of_le one_pos hlog
  set L : ℝ := |Real.log ε| with hLdef
  have habs : |lamEps lam ε| ^ (2 * m) = lam ^ (2 * m) / L ^ m :=
    abs_lamEps_even_pow m hlogPos
  have hLpow : L ^ m = L ^ (m - 1) * L := by
    rw [← pow_succ]
    congr 1
    omega
  have hlampow : lam ^ (2 * m) = lam ^ (2 * m - 2) * lam ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hL0 : L ≠ 0 := hlogPos.ne'
  have hLm10 : L ^ (m - 1) ≠ 0 := pow_ne_zero _ hL0
  unfold r324EndpointLoss
  rw [habs, lamEps_sq hlogPos, ← hLdef, hLpow, hlampow]
  field_simp

/-- **The general-`m` routed reduction.**  The two windowed ledgers
produce the countable central routed output at the amplitude
`λ_ε² · (16·C^m·λ^{2m-2})` times the endpoint loss, for *every*
external mode pair — the exact interface consumed by the pigeonhole
file and the capstone closure. -/
theorem countableCentralRoutedMomentReductionOutput_of_routedWindow
    {ρ : SmoothCutoff} {lam ε C : ℝ} {m : ℕ}
    (hm : 0 < m) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) (hmtrunc : m ≤ truncOrder ε)
    (hnonzero : R324RoutedPerTermWindowBound ρ lam m C)
    (hzero : R324RoutedZeroShiftWindowBound ρ lam m C)
    (α β : Z4) :
    CountableCentralRoutedMomentReductionOutput ρ lam ε m α β
      ((lamEps lam ε ^ 2 * (16 * C ^ m * lam ^ (2 * m - 2))) *
        r324EndpointLoss ε α β) := by
  by_cases hshift : α + β = 0
  · refine
      ρ.countableCentralRoutedMomentReductionOutput_of_zeroShift
        lam hm hε α β hshift hε1 hmtrunc _ ?_
    exact
      (hzero hm ε hε hε1 hlog hmtrunc α β hshift).trans_eq
        (r324RoutedWindow_budget_eq hlog hm α β)
  · refine
      ρ.countableCentralRoutedMomentReductionOutput_of_nonzeroRoutes
        lam hm hε α β hshift hε1 hmtrunc _ ?_
    exact
      (hnonzero hm ε hε hε1 hlog hmtrunc α β hshift).trans_eq
        (r324RoutedWindow_budget_eq hlog hm α β)

/-- **Landing at the paper amplitude.**  With the `ε`-free
constant comparison `16·C^m·λ^{2m-2} ≤ outer·((16·C₀)·λ)^{2m-2}`, the
windowed ledgers deliver the routed output at the exact paper amplitude. -/
theorem countableCentralRoutedMomentReductionOutput_frozen_of_routedWindow
    {ρ : SmoothCutoff}
    {lam ε C outerConstant primitiveConstant : ℝ} {m : ℕ}
    (hm : 0 < m) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) (hmtrunc : m ≤ truncOrder ε)
    (hnonzero : R324RoutedPerTermWindowBound ρ lam m C)
    (hzero : R324RoutedZeroShiftWindowBound ρ lam m C)
    (hclose : 16 * C ^ m * lam ^ (2 * m - 2) ≤
      outerConstant *
        ((16 * primitiveConstant) * lam) ^ (2 * m - 2))
    (α β : Z4) :
    CountableCentralRoutedMomentReductionOutput ρ lam ε m α β
      ((lamEps lam ε ^ 2 * outerConstant *
          ((16 * primitiveConstant) * lam) ^ (2 * m - 2)) *
        r324EndpointLoss ε α β) := by
  refine
    (countableCentralRoutedMomentReductionOutput_of_routedWindow
      hm hε hε1 hlog hmtrunc hnonzero hzero α β).mono ?_
  refine
    mul_le_mul_of_nonneg_right ?_ (r324EndpointLoss_nonneg ε α β)
  calc
    lamEps lam ε ^ 2 * (16 * C ^ m * lam ^ (2 * m - 2)) ≤
        lamEps lam ε ^ 2 *
          (outerConstant *
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2)) :=
      mul_le_mul_of_nonneg_left hclose (sq_nonneg _)
    _ = lamEps lam ε ^ 2 * outerConstant *
          ((16 * primitiveConstant) * lam) ^ (2 * m - 2) := by
      ring

/-- **(E) The conditional endgame.**  The two windowed route ledgers
are, together with the uniform-branch reduction output, sufficient for
the complete deterministic paper bound: the routed half of `hdet` at
the paper amplitude follows from
`countableCentralRoutedMomentReductionOutput_frozen_of_routedWindow`
inside the final consumer.  The outer constant is chosen
before the cutoff, coupling, scale, order, Fourier modes, and window
constant. -/
theorem
    exists_deterministicMoment_paper_bound_of_refinedIntegrated_and_routedWindow
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε C : ℝ) (m : ℕ) (α β : Z4),
        0 ≤ lam → 0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| → 1 ≤ m → m ≤ truncOrder ε →
        MomentRefinedIntegratedReductionOutputAt
          ρ lam ε m α β primitiveConstant supportConstant →
        R324RoutedPerTermWindowBound ρ lam m C →
        R324RoutedZeroShiftWindowBound ρ lam m C →
        16 * C ^ m * lam ^ (2 * m - 2) ≤
          outerConstant *
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_refinedIntegrated_and_countable
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε C m α β hlam hε hεsmall hlog hm hmtrunc
    hrefined hnonzero hzero hclose
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  exact
    h ρ lam ε m α β hlam hε hεsmall hlog hm hrefined
      (countableCentralRoutedMomentReductionOutput_frozen_of_routedWindow
        (by omega) hε hε1 hlog hmtrunc hnonzero hzero hclose α β)

end

end Anderson4D
