import Anderson4D.DetParametrix.Paper42_Moment.R324FinalAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324DirectFourierBranch
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedCollapseProducer

/-!
# Mode-free reduction of the R-324 middle estimate

The middle estimate `R324RefinedInsertedMajorantBound` is a
per-fibre bound depending on the Fourier modes `α, β`.  Through the
scalarized direct Fourier evaluation of `R324DirectFourierBranch` —
which covers *every* refined fibre, in particular realizing the
`.directFourier` incoming branch with no case split — it reduces to a
single mode-independent interior estimate: the weighted interior `L¹`
mass of each refined fibre against the integrated inserted majorant.
Combined with the slot-budget producer of the signed collapse datum,
the final deterministic moment bound of `R324FinalAssembly` follows
from two scalar inequalities, neither mentioning Fourier modes, endpoint
case splits, or density data.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

theorem paperFourthOrderModeDecay_le_one (k : Z4) :
    paperFourthOrderModeDecay k ≤ 1 := by
  have hn : 0 ≤ paperModeNormSq k := by
    unfold paperModeNormSq
    positivity
  have hpos : 0 < (1 + paperModeNormSq k) ^ 2 := by nlinarith
  unfold paperFourthOrderModeDecay
  exact (inv_le_one₀ hpos).mpr (by nlinarith)

/-- **The mode-free interior form of the middle estimate.**  The
`2m`-weighted interior `L¹` mass of every refined fibre, with the
universal endpoint factor `16`, is bounded by the integrated inserted
majorant.  This is the mode-free Proposition-4.1 content: no Fourier mode,
endpoint flag, or incoming case split remains. -/
def R324InteriorCoreMajorantBound
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (primitiveConstant supportConstant : ℝ) : Prop :=
  ∀ p : R324RefinedScheduleIndex m,
    16 * (|lamEps lam ε| ^ (2 * m) *
        r324RefinedInteriorCoreIntegral ρ ε m p) ≤
      ∫ z,
        primitiveInsertedMajorant
          primitiveConstant lam ε supportConstant m z
        ∂paperMeasure

/-- The interior estimate discharges the middle estimate at every pair
of Fourier modes: the `⟨α⟩⁻⁴⟨β⟩⁻⁴` decay produced by the direct
endpoint evaluation is simply dropped against `1`. -/
theorem r324RefinedInsertedMajorantBound_of_interiorCore
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {primitiveConstant supportConstant : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : 0 < m) (α β : Z4)
    (h :
      R324InteriorCoreMajorantBound
        ρ lam ε m primitiveConstant supportConstant) :
    R324RefinedInsertedMajorantBound
      ρ lam ε m α β primitiveConstant supportConstant := by
  intro p
  refine le_trans ?_ (h p)
  have hphys :=
    norm_r324RefinedPhysicalIntegral_le_modeDecay_mul_interiorCore
      ρ hε hε1 hm α β p
  have hCI := r324RefinedInteriorCoreIntegral_nonneg ρ ε m p
  have hα := paperFourthOrderModeDecay_le_one α
  have hβ := paperFourthOrderModeDecay_le_one β
  have hα0 := paperFourthOrderModeDecay_nonneg α
  have hβ0 := paperFourthOrderModeDecay_nonneg β
  calc
    |lamEps lam ε| ^ (2 * m) *
          ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
        |lamEps lam ε| ^ (2 * m) *
          (16 * paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β *
            r324RefinedInteriorCoreIntegral ρ ε m p) :=
      mul_le_mul_of_nonneg_left hphys
        (pow_nonneg (abs_nonneg _) _)
    _ ≤ |lamEps lam ε| ^ (2 * m) *
          (16 * 1 * 1 *
            r324RefinedInteriorCoreIntegral ρ ε m p) := by
      have hfactor :
          16 * paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β *
            r324RefinedInteriorCoreIntegral ρ ε m p ≤
          16 * 1 * 1 *
            r324RefinedInteriorCoreIntegral ρ ε m p := by
        gcongr
      exact mul_le_mul_of_nonneg_left hfactor
        (pow_nonneg (abs_nonneg _) _)
    _ = 16 * (|lamEps lam ε| ^ (2 * m) *
          r324RefinedInteriorCoreIntegral ρ ε m p) := by
      ring

/-- **Final assembly from the two mode-free scalar inputs.**  The
deterministic moment pairing sum obeys the paper bound (3.24) — the
P-3.5b-det shape realized by `paperDeterministicMomentRHS`, including
its `⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε²(α+β)⟩⁻⁸` bracket — given only the interior
inserted-majorant estimate and the per-slot signed route budget.  Both
hypotheses are inequalities of real numbers against the same integrated
inserted majorant; the Fourier-mode layers of (3.24) are unconditional. -/
theorem exists_deterministicMoment_paper_bound_of_interiorCore_and_slotBudget
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
        (hm : 0 < m) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        m ≤ truncOrder ε →
        R324InteriorCoreMajorantBound
          ρ lam ε m primitiveConstant supportConstant →
        (∀ i : Fin m,
          (∑' p : R324RefinedScheduleIndex m × ℕ,
            ρ.r324SignedRouteSlotWeight lam hm ε i p) ≤
            ∫ z,
              primitiveInsertedMajorant
                primitiveConstant lam ε supportConstant m z
              ∂paperMeasure) →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_insertedMajorant_and_signedCollapse
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
    hcore hbudget
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  exact
    h ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
      (r324RefinedInsertedMajorantBound_of_interiorCore
        hε hε1 hm α β hcore)
      (ρ.signedRoutedPrimitiveSlotCollapseData_of_slotInsertedBudget
        lam hm hε hε1 primitiveConstant supportConstant
        hprimitive.le hlam hbudget)

/-- **Alignment with the P-3.5b-det decay bracket.**  The (3.24) bound
`paperDeterministicMomentRHS` has a `min` bracket that dominates the decay form
`ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε²(α+β)⟩⁻⁸` carried by
`paperDeterministicMomentDecay`. -/
theorem paperDeterministicMomentRHS_le_decayBracket
    (outerConstant powerConstant lam ε : ℝ) (m : ℕ)
    (α β : Z4)
    (houter : 0 ≤ outerConstant)
    (hbase : 0 ≤ powerConstant * lam) :
    paperDeterministicMomentRHS
        outerConstant powerConstant lam ε m α β ≤
      lamEps lam ε ^ 2 * outerConstant *
        (powerConstant * lam) ^ (2 * m - 2) *
        paperDeterministicMomentDecay ε α β := by
  unfold paperDeterministicMomentRHS
  exact mul_le_mul_of_nonneg_left
    (min_le_right _ _)
    (by positivity)

end

end Anderson4D
