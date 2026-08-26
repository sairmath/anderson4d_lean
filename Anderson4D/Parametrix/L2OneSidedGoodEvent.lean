import Anderson4D.Parametrix.L2GreenCompact
import Anderson4D.Parametrix.PerrBoundaryAlgebra

/-!
# Paper-faithful one-sided parametrix good event

Paper (3.32)--(3.33) controls the physical parametrix and the left
factor residual

`Q (1 - G M) - 1`.

Compactness of `G M` makes this one-sided information sufficient for
invertibility.  This file packages the corresponding probability event
and specializes it to the canonical finite parametrix and the explicit
boundary sum of (3.21).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Topology

/-! ## Abstract one-sided event and probability estimate -/

/-- Mixed second/first-moment event with only the residual estimated in
the paper. -/
def oneSidedQuantitativeL2ParametrixGoodEvent
    {Ω : Type*}
    (P Rleft : Ω → TorusL2 →L[ℂ] TorusL2)
    (valid : Ω → Prop) (ε : ℝ) : Set Ω :=
  {ω |
    ‖P ω‖ ≤ ε ^ (-14 : ℤ) ∧
      ‖Rleft ω‖ ≤ ε ^ 28 ∧
      valid ω}

/-- The existing mixed Markov estimate, specialized with zero right
residual, gives the paper-faithful one-sided exceptional-set bound. -/
theorem
    measureReal_compl_oneSidedQuantitativeL2ParametrixGoodEvent_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (P Rleft : Ω → TorusL2 →L[ℂ] TorusL2)
    (valid : Ω → Prop)
    (ε δP δR : ℝ)
    (hεpos : 0 < ε)
    (hintP : Integrable (fun ω => ‖P ω‖ ^ 2) μ)
    (hintR : Integrable (fun ω => ‖Rleft ω‖) μ)
    (hsecondP : (∫ ω, ‖P ω‖ ^ 2 ∂μ) ≤ δP)
    (hfirstR : (∫ ω, ‖Rleft ω‖ ∂μ) ≤ δR)
    (hvalid : ∀ᵐ ω ∂μ, valid ω) :
    μ.real
        (oneSidedQuantitativeL2ParametrixGoodEvent
          P Rleft valid ε)ᶜ ≤
      δP / (ε ^ (-14 : ℤ)) ^ 2 +
        δR / ε ^ 28 := by
  let Rzero : Ω → TorusL2 →L[ℂ] TorusL2 :=
    fun _ => 0
  have hintR' :
      Integrable
        (fun ω => ‖Rleft ω‖ + ‖Rzero ω‖) μ := by
    simpa [Rzero] using hintR
  have hfirstR' :
      (∫ ω, ‖Rleft ω‖ + ‖Rzero ω‖ ∂μ) ≤ δR := by
    simpa [Rzero] using hfirstR
  simpa [oneSidedQuantitativeL2ParametrixGoodEvent,
      quantitativeL2ParametrixGoodEvent, Rzero] using
    (measureReal_compl_quantitativeL2ParametrixGoodEvent_le
      μ P Rleft Rzero valid ε δP δR hεpos
      hintP hintR' hsecondP hfirstR' hvalid)

namespace PartialPairing

/-! ## Canonical finite factor -/

/-- The exact one-sided identity and the physical bridge needed by the
compact Fredholm argument. -/
def canonicalOneSidedParametrixValid
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ)
    (Qfactor Rleft :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
    (ω : M.Ω) : Prop :=
  Qfactor ω *
        (1 - Kop greenL2Op
          (mollifiedPotentialL2Op M ρ lam ε ω)) =
      1 + Rleft ω ∧
    Qfactor ω * greenL2Op =
      canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω

/-- The canonical paper-scale event with only the left P-err residual. -/
def canonicalOneSidedL2ParametrixGoodEvent
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ)
    (Qfactor Rleft :
      M.Ω → TorusL2 →L[ℂ] TorusL2) :
    Set M.Ω :=
  oneSidedQuantitativeL2ParametrixGoodEvent
    (canonicalPhysicalTruncatedParametrixL2Operator
      M ρ lam ε A)
    Rleft
    (canonicalOneSidedParametrixValid
      M ρ lam ε A Qfactor Rleft)
    ε

theorem canonicalOneSidedParametrixValid_of_factorized
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ)
    (Qfactor Rleft Rright :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
    (ω : M.Ω)
    (hvalid :
      canonicalFactorizedParametrixValid
        M ρ lam ε A Qfactor Rleft Rright ω) :
    canonicalOneSidedParametrixValid
      M ρ lam ε A Qfactor Rleft ω :=
  ⟨hvalid.1.leftIdentity, hvalid.2⟩

/-! ## Canonical probability bounds -/

theorem
    measureReal_compl_canonicalOneSidedL2ParametrixGoodEvent_le
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (Qfactor Rleft :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
    (hfubini :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick :
      ∀ m, 1 ≤ m → m ≤ A →
        WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hintR :
      Integrable (fun ω => ‖Rleft ω‖)
        (volume : Measure M.Ω))
    (δR : ℝ)
    (hfirstR :
      (∫ ω, ‖Rleft ω‖
        ∂(volume : Measure M.Ω)) ≤ δR)
    (hvalid :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        canonicalOneSidedParametrixValid
          M ρ lam ε A Qfactor Rleft ω) :
    (volume : Measure M.Ω).real
        (canonicalOneSidedL2ParametrixGoodEvent
          M ρ lam ε A Qfactor Rleft)ᶜ ≤
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε A /
        (ε ^ (-14 : ℤ)) ^ 2 +
      δR / ε ^ 28 := by
  exact
    measureReal_compl_oneSidedQuantitativeL2ParametrixGoodEvent_le
      (volume : Measure M.Ω)
      (canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A)
      Rleft
      (canonicalOneSidedParametrixValid
        M ρ lam ε A Qfactor Rleft)
      ε
      (canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
        outerConstant powerConstant lam ε A)
      δR hε
      (integrable_normSq_canonicalPhysicalTruncatedParametrixL2Operator
        hfubini hwick hdet
        houter hpower hlam hε hεle)
      hintR
      (integral_normSq_canonicalPhysicalTruncatedParametrixL2Operator_le
        hfubini hwick hdet
        houter hpower hlam hε hεle)
      hfirstR hvalid

/-- The canonical factor discharges the one-sided validity predicate
almost surely from the already proved coefficient bridge. -/
theorem ae_canonicalOneSidedParametrixValid
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (hfubini :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick :
      ∀ m, 1 ≤ m → m ≤ A →
        WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε A ω) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      canonicalOneSidedParametrixValid
        M ρ lam ε A
        (canonicalGradedTruncatedParametrixL2Factor
          M ρ lam ε A)
        (canonicalPerrLeftRemainder
          M ρ lam ε A)
        ω := by
  filter_upwards
    [ae_canonicalFactorizedParametrixValid
      hfubini hwick hdet
      houter hpower hlam hε hεle hagree] with
      ω hvalid
  exact canonicalOneSidedParametrixValid_of_factorized
    M ρ lam ε A
    (canonicalGradedTruncatedParametrixL2Factor
      M ρ lam ε A)
    (canonicalPerrLeftRemainder
      M ρ lam ε A)
    (canonicalPerrRightRemainder
      M ρ lam ε A)
    ω hvalid

/-- Exceptional-set bound with the canonical factor and only its left
residual. -/
theorem
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (hfubini :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick :
      ∀ m, 1 ≤ m → m ≤ A →
        WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε A ω)
    (hintR :
      Integrable
        (fun ω =>
          ‖canonicalPerrLeftRemainder
            M ρ lam ε A ω‖)
        (volume : Measure M.Ω))
    (δR : ℝ)
    (hfirstR :
      (∫ ω,
          ‖canonicalPerrLeftRemainder
            M ρ lam ε A ω‖
        ∂(volume : Measure M.Ω)) ≤ δR) :
    (volume : Measure M.Ω).real
        (canonicalOneSidedL2ParametrixGoodEvent
          M ρ lam ε A
          (canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε A)
          (canonicalPerrLeftRemainder
            M ρ lam ε A))ᶜ ≤
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε A /
        (ε ^ (-14 : ℤ)) ^ 2 +
      δR / ε ^ 28 := by
  exact
    measureReal_compl_canonicalOneSidedL2ParametrixGoodEvent_le
      (canonicalGradedTruncatedParametrixL2Factor
        M ρ lam ε A)
      (canonicalPerrLeftRemainder
        M ρ lam ε A)
      hfubini hwick hdet
      houter hpower hlam hε hεle
      hintR δR hfirstR
      (ae_canonicalOneSidedParametrixValid
        hfubini hwick hdet
        houter hpower hlam hε hεle hagree)

/-- The final P-err interface is the first moment of the explicit
last-block boundary sum in (3.21). -/
theorem
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_of_boundary
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    (hfubini :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε →
        WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε (truncOrder ε) ω)
    (hintBoundary :
      Integrable
        (fun ω =>
          ‖canonicalPerrLeftBoundary
            M ρ lam ε (truncOrder ε) ω‖)
        (volume : Measure M.Ω))
    (δR : ℝ)
    (hfirstBoundary :
      (∫ ω,
          ‖canonicalPerrLeftBoundary
            M ρ lam ε (truncOrder ε) ω‖
        ∂(volume : Measure M.Ω)) ≤ δR) :
    (volume : Measure M.Ω).real
        (canonicalOneSidedL2ParametrixGoodEvent
          M ρ lam ε (truncOrder ε)
          (canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε (truncOrder ε))
          (canonicalPerrLeftRemainder
            M ρ lam ε (truncOrder ε)))ᶜ ≤
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε (truncOrder ε) /
        (ε ^ (-14 : ℤ)) ^ 2 +
      δR / ε ^ 28 := by
  have hboundary :=
    ae_canonicalPerrRemainders_eq_boundaries
      M ρ lam hε
  have hnorm :
      (fun ω =>
        ‖canonicalPerrLeftRemainder
          M ρ lam ε (truncOrder ε) ω‖) =ᵐ[
          (volume : Measure M.Ω)]
        fun ω =>
          ‖canonicalPerrLeftBoundary
            M ρ lam ε (truncOrder ε) ω‖ := by
    filter_upwards [hboundary] with ω hω
    rw [hω.2]
  have hintR :
      Integrable
        (fun ω =>
          ‖canonicalPerrLeftRemainder
            M ρ lam ε (truncOrder ε) ω‖)
        (volume : Measure M.Ω) :=
    hintBoundary.congr hnorm.symm
  have hfirstR :
      (∫ ω,
          ‖canonicalPerrLeftRemainder
            M ρ lam ε (truncOrder ε) ω‖
        ∂(volume : Measure M.Ω)) ≤ δR := by
    rw [integral_congr_ae hnorm]
    exact hfirstBoundary
  exact
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le
      hfubini hwick hdet
      houter hpower hlam hε hεle hagree
      hintR δR hfirstR

/-- Paper-scale powers give an exceptional set of size at most
`2 ε²`; no non-paper right residual occurs. -/
theorem
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_two_mul_sq
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    (hfubini :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε →
        WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hbudget :
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε (truncOrder ε) ≤
        ε ^ (-24 : ℤ))
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε (truncOrder ε) ω)
    (hintBoundary :
      Integrable
        (fun ω =>
          ‖canonicalPerrLeftBoundary
            M ρ lam ε (truncOrder ε) ω‖)
        (volume : Measure M.Ω))
    (hfirstBoundary :
      (∫ ω,
          ‖canonicalPerrLeftBoundary
            M ρ lam ε (truncOrder ε) ω‖
        ∂(volume : Measure M.Ω)) ≤ ε ^ 30) :
    (volume : Measure M.Ω).real
        (canonicalOneSidedL2ParametrixGoodEvent
          M ρ lam ε (truncOrder ε)
          (canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε (truncOrder ε))
          (canonicalPerrLeftRemainder
            M ρ lam ε (truncOrder ε)))ᶜ ≤
      2 * ε ^ 2 := by
  calc
    (volume : Measure M.Ω).real
        (canonicalOneSidedL2ParametrixGoodEvent
          M ρ lam ε (truncOrder ε)
          (canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε (truncOrder ε))
          (canonicalPerrLeftRemainder
            M ρ lam ε (truncOrder ε)))ᶜ ≤
        canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
            outerConstant powerConstant lam ε (truncOrder ε) /
          (ε ^ (-14 : ℤ)) ^ 2 +
        ε ^ 30 / ε ^ 28 :=
      measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_of_boundary
        hfubini hwick hdet
        houter hpower hlam hε hεle hagree
        hintBoundary (ε ^ 30) hfirstBoundary
    _ ≤
        ε ^ (-24 : ℤ) /
            (ε ^ (-14 : ℤ)) ^ 2 +
          ε ^ 30 / ε ^ 28 := by
      gcongr
    _ = ε ^ 4 + ε ^ 2 := by
      field_simp [ne_of_gt hε]
    _ ≤ ε ^ 2 + ε ^ 2 := by
      exact add_le_add
        (pow_le_pow_of_le_one hε.le hεle (by norm_num))
        le_rfl
    _ = 2 * ε ^ 2 := by ring

/-- Compact Fredholm inversion on the one-sided good event. -/
theorem lopInvertible_on_canonicalOneSidedL2ParametrixGoodEvent
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ)
    (Qfactor Rleft :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
    (hεpow : ε ^ 28 < 1 / 2)
    {ω : M.Ω}
    (hω : ω ∈ canonicalOneSidedL2ParametrixGoodEvent
      M ρ lam ε A Qfactor Rleft) :
    LopInvertible greenL2Op
      (mollifiedPotentialL2Op M ρ lam ε ω) := by
  change
    ‖canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω‖ ≤ ε ^ (-14 : ℤ) ∧
      ‖Rleft ω‖ ≤ ε ^ 28 ∧
      canonicalOneSidedParametrixValid
        M ρ lam ε A Qfactor Rleft ω at hω
  rcases hω with ⟨_hPbound, hRbound, hvalid⟩
  have hRhalf : ‖Rleft ω‖ < 1 / 2 :=
    hRbound.trans_lt hεpow
  exact lopInvertible_of_compact_leftParametrix
    greenL2Op
    (mollifiedPotentialL2Op M ρ lam ε ω)
    (Qfactor ω) (Rleft ω)
    (isCompactOperator_Kop_greenL2Op
      (mollifiedPotentialL2Op M ρ lam ε ω))
    hvalid.1
    (hRhalf.trans (by norm_num))

/-- Paper (3.33) from precisely the one-sided event controlled by
(3.32). -/
theorem
    norm_inverseGreen_sub_canonicalParametrix_on_oneSidedGoodEvent
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ)
    (Qfactor Rleft :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
    (hεpos : 0 < ε)
    (hεsmall : 2 * ε ^ 2 ≤ 1)
    (hεpow : ε ^ 28 < 1 / 2)
    {ω : M.Ω}
    (hω : ω ∈ canonicalOneSidedL2ParametrixGoodEvent
      M ρ lam ε A Qfactor Rleft) :
    ‖inverseGreen greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)
        (lopInvertible_on_canonicalOneSidedL2ParametrixGoodEvent
          M ρ lam ε A Qfactor Rleft hεpow hω) -
      canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω‖ ≤
      ε ^ 12 := by
  letI : Nontrivial TorusL2 :=
    nontrivial_of_ne (torusFourierBasis (0 : Z4)) 0
      (torusFourierBasis.orthonormal.ne_zero 0)
  have hωcopy := hω
  change
    ‖canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω‖ ≤ ε ^ (-14 : ℤ) ∧
      ‖Rleft ω‖ ≤ ε ^ 28 ∧
      canonicalOneSidedParametrixValid
        M ρ lam ε A Qfactor Rleft ω at hωcopy
  rcases hωcopy with ⟨hPbound, hRbound, hvalid⟩
  have hleft :
      Qfactor ω *
          (1 - Kop greenL2Op
            (mollifiedPotentialL2Op M ρ lam ε ω)) =
        1 + Rleft ω :=
    hvalid.1
  have hbridge :
      Qfactor ω * greenL2Op =
        canonicalPhysicalTruncatedParametrixL2Operator
          M ρ lam ε A ω :=
    hvalid.2
  have hRhalf : ‖Rleft ω‖ < 1 / 2 :=
    hRbound.trans_lt hεpow
  have hproof :
      lopInvertible_on_canonicalOneSidedL2ParametrixGoodEvent
          M ρ lam ε A Qfactor Rleft hεpow hω =
        lopInvertible_of_compact_leftParametrix
          greenL2Op
          (mollifiedPotentialL2Op M ρ lam ε ω)
          (Qfactor ω) (Rleft ω)
          (isCompactOperator_Kop_greenL2Op
            (mollifiedPotentialL2Op M ρ lam ε ω))
          hleft
          (hRhalf.trans (by norm_num)) :=
    Subsingleton.elim _ _
  rw [hproof, ← hbridge]
  calc
    ‖inverseGreen greenL2Op
          (mollifiedPotentialL2Op M ρ lam ε ω)
          (lopInvertible_of_compact_leftParametrix
            greenL2Op
            (mollifiedPotentialL2Op M ρ lam ε ω)
            (Qfactor ω) (Rleft ω)
            (isCompactOperator_Kop_greenL2Op
              (mollifiedPotentialL2Op M ρ lam ε ω))
            hleft
            (hRhalf.trans (by norm_num))) -
        Qfactor ω * greenL2Op‖ ≤
        2 * ‖Qfactor ω * greenL2Op‖ *
          ‖Rleft ω‖ :=
      norm_inverseGreen_sub_parametrix_mul_le_two_of_compact
        greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)
        (Qfactor ω) (Rleft ω)
        (isCompactOperator_Kop_greenL2Op
          (mollifiedPotentialL2Op M ρ lam ε ω))
        hleft hRhalf
    _ ≤
        2 * ε ^ (-14 : ℤ) * ε ^ 28 := by
      gcongr
      · rw [hbridge]
        exact hPbound
    _ = (2 * ε ^ 2) * ε ^ 12 := by
      field_simp [ne_of_gt hεpos]
    _ ≤ 1 * ε ^ 12 :=
      mul_le_mul_of_nonneg_right hεsmall
        (pow_nonneg hεpos.le 12)
    _ = ε ^ 12 := one_mul _

end PartialPairing

end

end Anderson4D
