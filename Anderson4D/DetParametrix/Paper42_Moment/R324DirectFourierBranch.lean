import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointFirstPhysicalBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointMajorantClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324MarkedResidualComplementBudget

/-!
# Direct Fourier evaluation of the four endpoint legs, per refined fibre

The endpoint-first Fubini normal form of a refined physical fibre
evaluates all four external endpoints directly against their surviving
Green legs — in particular the incoming endpoint, whose flag is `false`
by definition, so the `.directFourier` incoming branch is realized
unconditionally, with no case split on `⟨0, hm⟩ ∈ finalActive`.  This
file scalarizes that normal form: the weighted refined physical
integral is bounded, for *every* refined schedule index, by the full
paper mode decay `16⟨α⟩⁻⁴⟨β⟩⁻⁴` times the mode-independent `L¹` norm of
the interior signed core.  On the doubly-direct outgoing branch the
universal factor `16` improves to `1`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Pointwise scalarization of the endpoint-first integrand: its norm is
exactly the four-endpoint Fourier weight times the interior core norm. -/
theorem norm_r324EndpointFirstRefinedCoreIntegrand_eq
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4) (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4) :
    ‖r324EndpointFirstRefinedCoreIntegrand
        ρ ε m hm α β p v‖ =
      r324FourEndpointCoefficientWeight α β
          (r324ContractionEndpointAnchors hm
            (r324RefinedScheduleRepresentative p) v)
          (r324ContractionEndpointFlags
            (r324RefinedScheduleRepresentative p)) *
        ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
          (r324RefinedScheduleRepresentative p) v‖ := by
  rw [←
    r324RefinedEndpointCoefficient_eq_endpointFirstRefinedCoreIntegrand
      ρ ε m hm α β p v]
  exact
    norm_r324RefinedEndpointCoefficient_eq
      ρ ε m hm α β p.1.1 p.2.1
      (r324RefinedScheduleRepresentative p)
      (r324RefinedScheduleRepresentative_mem p) v

/-- The finite primitive-pairing covariance sum of one refined fibre is
uniformly bounded on the doubled configuration space. -/
theorem exists_norm_sum_primitiveCovarianceProduct_le
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ)
    (s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ v : Fin (2 * m) → T4,
        ‖∑ e ∈ momentRefinedContractionFiber m s r,
          (primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ)‖ ≤
          B := by
  obtain ⟨Cη, hCη, hbound⟩ := ρ.exists_pos_etaEpsT4_uniform_bound
  set M : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη with hM
  have hM0 : 0 ≤ M := by positivity
  refine
    ⟨∑ e ∈ momentRefinedContractionFiber m s r,
      M ^ ((momentCombinedPairing e.1 e.2.1
          e.2.2).pairSupport.filter
        (fun i => i < momentCombinedPairing e.1 e.2.1 e.2.2 i)).card,
      Finset.sum_nonneg fun e _ => pow_nonneg hM0 _, ?_⟩
  intro v
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro e _he
  have hnonneg :
      0 ≤ primitiveCovarianceProduct ρ ε m
        (momentCombinedPairing e.1 e.2.1 e.2.2) v := by
    unfold primitiveCovarianceProduct
    exact Finset.prod_nonneg fun i _ => ρ.etaEpsT4_nonneg ε _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  unfold primitiveCovarianceProduct
  calc
    (∏ i ∈ (momentCombinedPairing e.1 e.2.1 e.2.2).pairSupport.filter
        (fun i => i < momentCombinedPairing e.1 e.2.1 e.2.2 i),
        ρ.etaEpsT4 ε
          (v i - v (momentCombinedPairing e.1 e.2.1 e.2.2 i))) ≤
        ∏ _i ∈ (momentCombinedPairing e.1 e.2.1 e.2.2).pairSupport.filter
          (fun i => i < momentCombinedPairing e.1 e.2.1 e.2.2 i),
          M :=
      Finset.prod_le_prod
        (fun i _ => ρ.etaEpsT4_nonneg ε _)
        (fun i _ => hbound hε hε1 _)
    _ = M ^ ((momentCombinedPairing e.1 e.2.1
          e.2.2).pairSupport.filter
        (fun i => i < momentCombinedPairing e.1 e.2.1 e.2.2 i)).card :=
      Finset.prod_const M

/-- The interior signed core of a refined fibre has integrable norm on
the doubled configuration space: the two endpoint-free Green profiles
are jointly integrable and the finite primitive-pairing covariance sum
is uniformly bounded. -/
theorem integrable_norm_r324RefinedEndpointCore
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ)
    (s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m) :
    Integrable
      (fun v : Fin (2 * m) → T4 =>
        ‖r324RefinedEndpointCore ρ ε m s r e₀ v‖)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_norm_sum_primitiveCovarianceProduct_le
      ρ hε hε1 m s r
  have hdens :=
    SmoothCutoff.integrable_r324SelectedInteriorSkeletonNormDensity
      (κp := e₀.1) (κm := e₀.2.1)
  refine (hdens.const_mul B).mono'
    (((measurable_r324RefinedEndpointCore
      ρ ε m s r e₀).norm).aestronglyMeasurable) ?_
  filter_upwards with v
  rw [norm_norm]
  unfold r324RefinedEndpointCore
  rw [norm_mul, norm_mul]
  calc
    ‖r324RenormalizedInteriorCore e₀.1
          (fun i => v (leftMomentIndex i))‖ *
          ‖r324RenormalizedInteriorCore e₀.2.1
            (fun i => v (rightMomentIndex i))‖ *
          ‖∑ e ∈ momentRefinedContractionFiber m s r,
            (primitiveCovarianceProduct ρ ε m
              (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ)‖ ≤
        ‖r324RenormalizedInteriorCore e₀.1
            (fun i => v (leftMomentIndex i))‖ *
          ‖r324RenormalizedInteriorCore e₀.2.1
            (fun i => v (rightMomentIndex i))‖ * B :=
      mul_le_mul_of_nonneg_left (hB v)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = B *
        SmoothCutoff.r324SelectedInteriorSkeletonNormDensity
          e₀.1 e₀.2.1 v := by
      unfold SmoothCutoff.r324SelectedInteriorSkeletonNormDensity
      ring

/-- Mode-independent interior `L¹` mass of one refined fibre. -/
def r324RefinedInteriorCoreIntegral
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (p : R324RefinedScheduleIndex m) : ℝ :=
  ∫ v : Fin (2 * m) → T4,
    ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
      (r324RefinedScheduleRepresentative p) v‖
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

theorem r324RefinedInteriorCoreIntegral_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (p : R324RefinedScheduleIndex m) :
    0 ≤ r324RefinedInteriorCoreIntegral ρ ε m p :=
  integral_nonneg fun _ => norm_nonneg _

/-- **Scalarized direct Fourier evaluation, all refined fibres.**  The
four endpoint legs (the incoming ones with flag `false`, i.e. the
`.directFourier` evaluation, and the outgoing ones with their shortcut
flag) are Fourier-evaluated directly, yielding the complete paper mode
decay `16⟨α⟩⁻⁴⟨β⟩⁻⁴` in front of the mode-independent interior mass.
No case split on `⟨0, hm⟩ ∈ finalActive` is needed: this bound holds
for *every* refined schedule index. -/
theorem norm_r324RefinedPhysicalIntegral_le_modeDecay_mul_interiorCore
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 0 < m) (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
      16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β *
        r324RefinedInteriorCoreIntegral ρ ε m p := by
  rw [r324RefinedPhysicalIntegral_eq_integral_endpointFirstRefinedCore
    ρ hε hε1 hm α β p]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint :
      Integrable
        (fun v : Fin (2 * m) → T4 =>
          (16 * paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β) *
            ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
              (r324RefinedScheduleRepresentative p) v‖)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    (integrable_norm_r324RefinedEndpointCore
      ρ hε hε1 m p.1.1 p.2.1
      (r324RefinedScheduleRepresentative p)).const_mul _
  calc
    (∫ v : Fin (2 * m) → T4,
        ‖r324EndpointFirstRefinedCoreIntegrand
          ρ ε m hm α β p v‖
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) ≤
        ∫ v : Fin (2 * m) → T4,
          (16 * paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β) *
            ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
              (r324RefinedScheduleRepresentative p) v‖
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun v => norm_nonneg _)
        hint
        (Filter.Eventually.of_forall fun v => ?_)
      dsimp only
      rw [norm_r324EndpointFirstRefinedCoreIntegrand_eq
        ρ ε m hm α β p v]
      exact mul_le_mul_of_nonneg_right
        (r324FourEndpointCoefficientWeight_le α β _ _)
        (norm_nonneg _)
    _ = 16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β *
        r324RefinedInteriorCoreIntegral ρ ε m p := by
      rw [integral_const_mul]
      rfl

/-- A flagless endpoint leg is Fourier-evaluated exactly: its
coefficient norm is the Euclidean Green multiplier itself. -/
theorem norm_r324EndpointCoefficient_false
    (k : Z4) (u v : T4) :
    ‖r324EndpointCoefficient k u v false‖ =
      paperSecondOrderModeDecay k := by
  simp [r324EndpointCoefficient, norm_translatedGreenMode]

theorem sq_paperSecondOrderModeDecay (k : Z4) :
    paperSecondOrderModeDecay k * paperSecondOrderModeDecay k =
      paperFourthOrderModeDecay k := by
  unfold paperSecondOrderModeDecay paperFourthOrderModeDecay
  rw [← mul_inv, ← pow_two]

/-- With all four flags `false` (both incoming legs are always direct;
both outgoing legs non-shortcut) the four-endpoint weight is exactly
`⟨α⟩⁻⁴⟨β⟩⁻⁴`, with no factor `16`. -/
theorem r324FourEndpointCoefficientWeight_eq_of_direct
    (α β : Z4) (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags)
    (h1 : flags 1 = false) (h3 : flags 3 = false)
    (h0 : flags 0 = false) (h2 : flags 2 = false) :
    r324FourEndpointCoefficientWeight α β anchors flags =
      paperFourthOrderModeDecay α *
        paperFourthOrderModeDecay β := by
  unfold r324FourEndpointCoefficientWeight
  rw [h0, h1, h2, h3,
    norm_r324EndpointCoefficient_false,
    norm_r324EndpointCoefficient_false,
    norm_r324EndpointCoefficient_false,
    norm_r324EndpointCoefficient_false,
    paperSecondOrderModeDecay_neg,
    paperSecondOrderModeDecay_neg]
  rw [← sq_paperSecondOrderModeDecay α,
    ← sq_paperSecondOrderModeDecay β]
  ring

/-- **Doubly-direct branch strengthening.**  When both outgoing legs of
the representative are non-shortcut (the incoming legs are direct by
definition), the universal factor `16` disappears: the refined physical
integral is bounded by the exact `⟨α⟩⁻⁴⟨β⟩⁻⁴` decay times the interior
mass. -/
theorem norm_r324RefinedPhysicalIntegral_le_modeDecay_mul_interiorCore_of_direct
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 0 < m) (α β : Z4)
    (p : R324RefinedScheduleIndex m)
    (hout1 :
      r324OutgoingIsShortcut
        (r324RefinedScheduleRepresentative p).1 = false)
    (hout2 :
      r324OutgoingIsShortcut
        (r324RefinedScheduleRepresentative p).2.1 = false) :
    ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
      paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β *
        r324RefinedInteriorCoreIntegral ρ ε m p := by
  rw [r324RefinedPhysicalIntegral_eq_integral_endpointFirstRefinedCore
    ρ hε hε1 hm α β p]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpoint : ∀ v : Fin (2 * m) → T4,
      ‖r324EndpointFirstRefinedCoreIntegrand
          ρ ε m hm α β p v‖ =
        (paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) *
          ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
            (r324RefinedScheduleRepresentative p) v‖ := by
    intro v
    rw [norm_r324EndpointFirstRefinedCoreIntegrand_eq
      ρ ε m hm α β p v,
      r324FourEndpointCoefficientWeight_eq_of_direct
        α β _ _
        (by rw [r324ContractionEndpointFlags_one, hout1])
        (by rw [r324ContractionEndpointFlags_three, hout2])
        (r324ContractionEndpointFlags_zero _)
        (r324ContractionEndpointFlags_two _)]
  refine le_of_eq ?_
  calc
    (∫ v : Fin (2 * m) → T4,
        ‖r324EndpointFirstRefinedCoreIntegrand
          ρ ε m hm α β p v‖
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
        ∫ v : Fin (2 * m) → T4,
          (paperFourthOrderModeDecay α *
              paperFourthOrderModeDecay β) *
            ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
              (r324RefinedScheduleRepresentative p) v‖
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
      integral_congr_ae
        (Filter.Eventually.of_forall fun v => hpoint v)
    _ = paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β *
        r324RefinedInteriorCoreIntegral ρ ε m p := by
      rw [integral_const_mul]
      rfl

end

end Anderson4D
