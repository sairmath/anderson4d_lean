import Anderson4D.Main.ConditionalAssembly
import Anderson4D.Main.FredholmErrorAsymptotics
import Anderson4D.Parametrix.L2GoodEventClosure
import Anderson4D.Continuum.LogAsymptotics

/-!
# Constructing the measurable resolvent good event

The quantitative operator event used in paper §3.4 is not presented as a
measurable set: its defining operator-valued random variables are only
specified almost everywhere.  This file replaces its bad set by a measurable
envelope of the same measure.  The envelope also absorbs the two null sets on
which the physical coefficient realization and the measurable Fredholm
realization may disagree with their samplewise versions.

This closes the set-theoretic and measurability gap between the paper-scale
`L²` good-event estimate and `FixedModeGoodEventData`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MainGoodEvent

/-- The samplewise moving truncation and the finite physical-parametrix
coefficient use exactly the same normalization. -/
theorem fullParametrixReal_eq_truncatedParametrixFiniteModeReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) (ω : M.Ω)
    (hA : A = truncOrder ε) :
    fullParametrixReal M ρ lam ε s modes c ω =
      truncatedParametrixFiniteModeReal
        M ρ lam ε A s modes c ω := by
  subst A
  unfold fullParametrixReal fixedTruncationReal
    fixedTruncationModeSum
    truncatedParametrixFiniteModeReal
    truncatedParametrixModeHcoeff
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Failure of the physical-operator coefficient realization for one finite
family of modes. -/
def coefficientFailure
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A s : ℕ) (modes : Fin s → Z4 × Z4) : Set M.Ω :=
  {ω | ¬ ∀ j : Fin s,
    torusFourierMatrixCoeff
        (canonicalPositiveTruncatedParametrixL2Operator
          M ρ lam ε A ω)
        (modes j).1 (modes j).2 =
      (paperTorusVolume : ℂ)⁻¹ *
        ∑ n ∈ Finset.range A,
          pmCoeff M ρ lam ε (n + 1)
            (modes j).1 (modes j).2 ω}

/-- Failure of the almost-sure identification between the Borel Fredholm
coefficient and its samplewise inverse realization. -/
def fredholmFailure
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) : Set M.Ω :=
  {ω |
    measurableFredholmFiniteModeReal M ρ lam ε s modes c ω ≠
      fredholmFiniteModeReal M ρ lam ε s modes c ω}

/-- The full bad set: the paper's quantitative operator failure together
with the two representation-null sets. -/
def bad
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) : Set M.Ω :=
  (PartialPairing.canonicalOneSidedL2ParametrixGoodEvent
      M ρ lam ε (truncOrder ε)
      (PartialPairing.canonicalGradedTruncatedParametrixL2Factor
        M ρ lam ε (truncOrder ε))
      (PartialPairing.canonicalPerrLeftRemainder
        M ρ lam ε (truncOrder ε)))ᶜ ∪
    coefficientFailure M ρ lam ε (truncOrder ε) s modes ∪
    fredholmFailure M ρ lam ε s modes c

/-- A measurable subset of the raw good event obtained by taking a measurable
envelope of the full bad set. -/
def good
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) : Set M.Ω :=
  (toMeasurable (volume : Measure M.Ω)
    (bad M ρ lam ε s modes c))ᶜ

theorem measurableSet_good
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) :
    MeasurableSet (good M ρ lam ε s modes c) :=
  (measurableSet_toMeasurable _ _).compl

theorem good_subset_raw
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) :
    good M ρ lam ε s modes c ⊆
      PartialPairing.canonicalOneSidedL2ParametrixGoodEvent
        M ρ lam ε (truncOrder ε)
        (PartialPairing.canonicalGradedTruncatedParametrixL2Factor
          M ρ lam ε (truncOrder ε))
        (PartialPairing.canonicalPerrLeftRemainder
          M ρ lam ε (truncOrder ε)) := by
  intro ω hω
  by_contra hraw
  exact hω
    (subset_toMeasurable (volume : Measure M.Ω)
      (bad M ρ lam ε s modes c)
      (Or.inl (Or.inl hraw)))

theorem good_avoids_coefficientFailure
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ)
    {ω : M.Ω} (hω : ω ∈ good M ρ lam ε s modes c) :
    ω ∉ coefficientFailure
      M ρ lam ε (truncOrder ε) s modes := by
  intro hfail
  exact hω
    (subset_toMeasurable (volume : Measure M.Ω)
      (bad M ρ lam ε s modes c)
      (Or.inl (Or.inr hfail)))

theorem good_avoids_fredholmFailure
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ)
    {ω : M.Ω} (hω : ω ∈ good M ρ lam ε s modes c) :
    ω ∉ fredholmFailure M ρ lam ε s modes c := by
  intro hfail
  exact hω
    (subset_toMeasurable (volume : Measure M.Ω)
      (bad M ρ lam ε s modes c)
      (Or.inr hfail))

/-- Adding the two almost-sure representation failures does not enlarge the
paper's exceptional-set bound. -/
theorem measureReal_compl_good_le
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) {δ : ℝ}
    (hraw :
      (volume : Measure M.Ω).real
          (PartialPairing.canonicalOneSidedL2ParametrixGoodEvent
            M ρ lam ε (truncOrder ε)
            (PartialPairing.canonicalGradedTruncatedParametrixL2Factor
              M ρ lam ε (truncOrder ε))
            (PartialPairing.canonicalPerrLeftRemainder
              M ρ lam ε (truncOrder ε)))ᶜ ≤ δ)
    (hcoeff :
      ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ j : Fin s,
        torusFourierMatrixCoeff
            (canonicalPositiveTruncatedParametrixL2Operator
              M ρ lam ε (truncOrder ε) ω)
            (modes j).1 (modes j).2 =
          (paperTorusVolume : ℂ)⁻¹ *
            ∑ n ∈ Finset.range (truncOrder ε),
              pmCoeff M ρ lam ε (n + 1)
                (modes j).1 (modes j).2 ω)
    (hfred :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        measurableFredholmFiniteModeReal
            M ρ lam ε s modes c ω =
          fredholmFiniteModeReal M ρ lam ε s modes c ω) :
    (volume : Measure M.Ω).real
        (good M ρ lam ε s modes c)ᶜ ≤ δ := by
  let μ : Measure M.Ω := volume
  have hcoeffZero :
      μ.real
          (coefficientFailure
            M ρ lam ε (truncOrder ε) s modes) = 0 := by
    rw [measureReal_eq_zero_iff]
    exact ae_iff.mp hcoeff
  have hfredZero :
      μ.real (fredholmFailure M ρ lam ε s modes c) = 0 := by
    rw [measureReal_eq_zero_iff]
    exact ae_iff.mp hfred
  calc
    μ.real (good M ρ lam ε s modes c)ᶜ =
        μ.real (bad M ρ lam ε s modes c) := by
      dsimp only [μ]
      unfold good
      simp only [compl_compl, Measure.real, measure_toMeasurable]
    _ ≤
        μ.real
            (PartialPairing.canonicalOneSidedL2ParametrixGoodEvent
              M ρ lam ε (truncOrder ε)
              (PartialPairing.canonicalGradedTruncatedParametrixL2Factor
                M ρ lam ε (truncOrder ε))
              (PartialPairing.canonicalPerrLeftRemainder
                M ρ lam ε (truncOrder ε)))ᶜ +
          μ.real
            (coefficientFailure
              M ρ lam ε (truncOrder ε) s modes) +
          μ.real (fredholmFailure M ρ lam ε s modes c) := by
      unfold bad
      exact
        (measureReal_union_le _ _).trans
          (add_le_add (measureReal_union_le _ _) le_rfl)
    _ = μ.real
          (PartialPairing.canonicalOneSidedL2ParametrixGoodEvent
            M ρ lam ε (truncOrder ε)
            (PartialPairing.canonicalGradedTruncatedParametrixL2Factor
              M ρ lam ε (truncOrder ε))
            (PartialPairing.canonicalPerrLeftRemainder
              M ρ lam ε (truncOrder ε)))ᶜ := by
      rw [hcoeffZero, hfredZero, add_zero, add_zero]
    _ ≤ δ := hraw

/-- On the measurable trimmed event, the moving coefficient truncation is
close to the Borel Fredholm realization by the same paper-scale error. -/
theorem norm_fullParametrixReal_sub_fullResolventReal_le_on_good
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (s : ℕ)
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ω : M.Ω)
    (hεpos : 0 < ε)
    (hεsmall : 2 * ε ^ 2 ≤ 1)
    (hεpow : ε ^ 28 < 1 / 2)
    (hω : ω ∈ good M ρ lam ε s modes c) :
    ‖fullParametrixReal M ρ lam ε s modes c ω -
        fullResolventReal M ρ lam ε s modes c ω‖ ≤
      ∑ j : Fin s, ‖c j‖ *
        (‖(paperTorusVolume : ℂ) *
            (lamEps lam ε : ℂ)⁻¹‖ * ε ^ 12) := by
  have hraw :=
    good_subset_raw M ρ lam ε s modes c hω
  have hcoeff :
      ∀ j : Fin s,
        torusFourierMatrixCoeff
            (canonicalPositiveTruncatedParametrixL2Operator
              M ρ lam ε (truncOrder ε) ω)
            (modes j).1 (modes j).2 =
          (paperTorusVolume : ℂ)⁻¹ *
            ∑ n ∈ Finset.range (truncOrder ε),
              pmCoeff M ρ lam ε (n + 1)
                (modes j).1 (modes j).2 ω := by
    simpa only [coefficientFailure, Set.mem_setOf_eq,
      not_not] using
      good_avoids_coefficientFailure
        M ρ lam ε s modes c hω
  have hfred :
      measurableFredholmFiniteModeReal M ρ lam ε s modes c ω =
        fredholmFiniteModeReal M ρ lam ε s modes c ω := by
    simpa only [fredholmFailure, Set.mem_setOf_eq,
      not_not] using
      good_avoids_fredholmFailure
        M ρ lam ε s modes c hω
  rw [fullResolventReal, hfred,
    fullParametrixReal_eq_truncatedParametrixFiniteModeReal
      M ρ lam ε (truncOrder ε) s modes c ω rfl]
  exact
    norm_truncatedParametrixFiniteModeReal_sub_fredholmFiniteModeReal_le_on_good
      M ρ lam ε (truncOrder ε)
      (PartialPairing.canonicalGradedTruncatedParametrixL2Factor
        M ρ lam ε (truncOrder ε))
      (PartialPairing.canonicalPerrLeftRemainder
        M ρ lam ε (truncOrder ε))
      s modes c ω hεpos hεsmall hεpow hraw hcoeff

/-- The finite Cramér--Wold error supplied by the one-sided Fredholm
comparison. -/
def error
    {s : ℕ} (c : Fin s → ℂ) (lam ε : ℝ) : ℝ :=
  ∑ j : Fin s, ‖c j‖ * fredholmModeErrorScale lam ε

theorem error_nonneg
    {s : ℕ} (c : Fin s → ℂ) (lam ε : ℝ) :
    0 ≤ error c lam ε :=
  sum_norm_mul_fredholmModeErrorScale_nonneg c lam ε

theorem tendsto_error
    {s : ℕ} (c : Fin s → ℂ)
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (error c lam)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
  tendsto_sum_norm_mul_fredholmModeErrorScale_nhdsGT_zero c hlam

/-- The deterministic P-3.5b and R-322 bounds construct the exact measurable
good-event package consumed by the final characteristic-function
replacement.  No measurability premise on the raw operator event is needed. -/
theorem nonempty_fixedModeGoodEventData_of_deterministic_bounds
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant Crenorm lam : ℝ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hCrenorm : 0 ≤ Crenorm)
    (hlam : 0 < lam) (hlamle : lam ≤ 1)
    (hpowerRatio :
      powerConstant * lam ≤ PartialPairing.boundaryGeometricRatio)
    (hrenormRatio :
      Crenorm * lam ≤ PartialPairing.boundaryGeometricRatio)
    (hdet :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
          ‖deterministicMomentPairingSum
              ρ lam ε m α β‖ ≤
            deterministicMomentRHS
              outerConstant powerConstant lam ε m α β)
    (hcounter :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        ∀ q ∈ Finset.Icc 1 (truncOrder ε),
          |renormC2q ρ lam ε q| ≤
            ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
              (Crenorm * lam) ^ (2 * q))
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) :
    Nonempty (FixedModeGoodEventData M ρ lam s modes c) := by
  let goodSet : ℝ → Set M.Ω :=
    fun ε => good M ρ lam ε s modes c
  let errorScale : ℝ → ℝ := error c lam
  have hraw :=
    PartialPairing.eventually_measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_two_mul_sq_closed
      (M := M) (ρ := ρ)
      houter hpower hCrenorm hlam.le hlamle
      hpowerRatio hrenormRatio hdet hcounter
  have htrim :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        (volume : Measure M.Ω).real (goodSet ε)ᶜ ≤
          2 * ε ^ 2 := by
    filter_upwards
        [hraw, hdet, self_mem_nhdsWithin,
          eventually_smallScale_le zero_lt_one] with
        ε hrawε hdetε hε hεle
    have hcoeffAll :
        ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ α β,
          torusFourierMatrixCoeff
              (canonicalPositiveTruncatedParametrixL2Operator
                M ρ lam ε (truncOrder ε) ω) α β =
            (paperTorusVolume : ℂ)⁻¹ *
              ∑ n ∈ Finset.range (truncOrder ε),
                pmCoeff M ρ lam ε (n + 1) α β ω :=
      canonicalPositiveTruncatedParametrixL2Operator_coeff_of_momentBounds
        (fun m _hm _hmA α β =>
          pmCoeffMomentFubiniOutput_of_r324
            M ρ lam hε (hεle) m α β)
        (fun m _hm _hmA =>
          M.wickAtSecondMomentLaw ρ hε m)
        hdetε houter hpower hlam.le hε hεle
    have hcoeff :
        ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ j : Fin s,
          torusFourierMatrixCoeff
              (canonicalPositiveTruncatedParametrixL2Operator
                M ρ lam ε (truncOrder ε) ω)
              (modes j).1 (modes j).2 =
            (paperTorusVolume : ℂ)⁻¹ *
              ∑ n ∈ Finset.range (truncOrder ε),
                pmCoeff M ρ lam ε (n + 1)
                  (modes j).1 (modes j).2 ω :=
      hcoeffAll.mono fun _ hω j => hω (modes j).1 (modes j).2
    have hfred :=
      ae_measurableFredholmFiniteModeReal_eq_fredholmFiniteModeReal
        M ρ lam hε s modes c
    exact
      measureReal_compl_good_le
        M ρ lam ε s modes c hrawε hcoeff hfred
  refine ⟨{
    good := goodSet
    error := errorScale
    good_measurable := ?_
    error_nonneg := ?_
    error_tendsto := ?_
    bad_probability_tendsto := ?_
    close_on_good := ?_ }⟩
  · intro ε
    exact measurableSet_good M ρ lam ε s modes c
  · exact
      Eventually.of_forall fun ε =>
        error_nonneg c lam ε
  · exact tendsto_error c hlam
  · have hid :
        Tendsto (fun ε : ℝ => 2 * ε ^ 2)
          (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
      have hε :
          Tendsto (fun ε : ℝ => ε)
            (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (hε.pow 2).const_mul 2
    apply squeeze_zero'
      (Eventually.of_forall fun ε =>
        measureReal_nonneg)
      htrim hid
  · filter_upwards
        [self_mem_nhdsWithin,
          eventually_smallScale_le
            (by norm_num : (0 : ℝ) < 1 / 2)] with
        ε hε hεhalf
    intro ω hω
    have hεsmall : 2 * ε ^ 2 ≤ 1 := by
      have hsquare :
          ε ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hε.le hεhalf 2
      norm_num at hsquare ⊢
      linarith
    have hεpow : ε ^ 28 < 1 / 2 := by
      calc
        ε ^ 28 ≤ (1 / 2 : ℝ) ^ 28 :=
          pow_le_pow_left₀ hε.le hεhalf 28
        _ < 1 / 2 := by norm_num
    exact
      norm_fullParametrixReal_sub_fullResolventReal_le_on_good
        M ρ lam ε s modes c ω hε hεsmall hεpow hω

end MainGoodEvent

end

end Anderson4D
