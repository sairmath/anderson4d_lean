import Anderson4D.DetParametrix.Paper42_Moment.R324FullFullStep1ReductionProducer
import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingHalfEstimate
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhaseAOneBlockUpdate
import Anderson4D.DetParametrix.Paper42_Moment.R324FullFullUniformBound
import Anderson4D.DetParametrix.Paper42_Moment.R324EmptyResidualStructure
import Anderson4D.Parametrix.Identity

/-!
# Paper-faithful incoming input for R-324 Step 1

In (4.17) the kernel on the incoming leg is the input denoted `G₀` in the
paper.  Proper intervals lying to the left of the retained terminal block
may already have been collapsed into this leg, so it is not in general the
free Green kernel.  The only property used for the frequency-independent
Step-1 estimate is the output of (4.13): measurability and the bound
`|G₀(z)| ≤ A |z|⁻²`.

This file is the minimal generalization of `R324PaperStep1.lean` needed at
that seam.  The terminal primitive kernel and all of the `y`/cosine/inserted
kernel argument are unchanged.  The incoming `x` integral is paid in `L¹`,
as in the paper, rather than being incorrectly identified with the Fourier
multiplier of `greenFn`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The corrected form of (4.17) -/

/-- The integrand (4.17) with the actual incoming removal output `G₀`. -/
def r324Step1IntegrandWithIncoming
    (G0 J : T4 → ℝ) (α β : Z4) (xa xm x y : T4) : ℂ :=
  charT4 α x * charT4 β y *
    ((G0 (x - xa) : ℝ) : ℂ) * ((J (xa - xm) : ℝ) : ℂ) *
      (((greenFn (xm - y) : ℝ) : ℂ) - ((greenFn (xa - y) : ℝ) : ℂ))

/-- The corrected four-fold Step-1 amplitude. -/
def r324Step1IntegralWithIncoming
    (G0 J : T4 → ℝ) (α β : Z4) : ℂ :=
  ∫ xa, ∫ xm, ∫ x, ∫ y,
    r324Step1IntegrandWithIncoming G0 J α β xa xm x y
    ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure

/-- The untranslated Fourier coefficient of the incoming removal output. -/
def r324IncomingMode (G0 : T4 → ℝ) (α : Z4) : ℂ :=
  ∫ u, charT4 α u * ((G0 u : ℝ) : ℂ) ∂paperMeasure

private theorem paperMeasure_integral_translate
    (f : T4 → ℂ) (a : T4) :
    (∫ x, f x ∂paperMeasure) = ∫ x, f (a + x) ∂paperMeasure := by
  rw [paperMeasure_eq_volume]
  exact (integral_add_left_eq_self f a).symm

/-- Translating the incoming leg extracts only its endpoint character; no
special Fourier formula for `G₀` is used. -/
theorem integral_charT4_mul_incoming_shift
    (G0 : T4 → ℝ) (α : Z4) (xa : T4) :
    (∫ x, charT4 α x * ((G0 (x - xa) : ℝ) : ℂ) ∂paperMeasure) =
      charT4 α xa * r324IncomingMode G0 α := by
  rw [paperMeasure_integral_translate
    (fun x => charT4 α x * ((G0 (x - xa) : ℝ) : ℂ)) xa]
  unfold r324IncomingMode
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [charT4_add_argument]
  simp only [add_sub_cancel_left]
  ring

/-! ## The unchanged endpoint and symmetry calculation -/

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

/-- The `y` integral is exactly the one in the original Step-1 proof. -/
theorem r324Step1WithIncoming_integral_y
    (G0 J : T4 → ℝ) (α β : Z4) (xa xm x : T4) :
    (∫ y, r324Step1IntegrandWithIncoming G0 J α β xa xm x y
      ∂paperMeasure) =
      charT4 α x * ((G0 (x - xa) : ℝ) : ℂ) *
        ((J (xa - xm) : ℝ) : ℂ) *
        (((paperSecondOrderModeDecay β : ℝ) : ℂ) *
          (charT4 β xm - charT4 β xa)) := by
  have hpull :
      (fun y : T4 =>
        r324Step1IntegrandWithIncoming G0 J α β xa xm x y) =
        fun y : T4 =>
          (charT4 α x * ((G0 (x - xa) : ℝ) : ℂ) *
              ((J (xa - xm) : ℝ) : ℂ)) *
            (charT4 β y * ((greenFn (xm - y) : ℝ) : ℂ) -
              charT4 β y * ((greenFn (xa - y) : ℝ) : ℂ)) := by
    funext y
    unfold r324Step1IntegrandWithIncoming
    ring
  rw [hpull, integral_const_mul,
    integral_sub (integrable_charT4_mul_greenFn_shift β xm)
      (integrable_charT4_mul_greenFn_shift β xa),
    integral_charT4_mul_greenFn_shift β xm,
    integral_charT4_mul_greenFn_shift β xa]
  unfold paperSecondOrderModeDecay
  ring

/-- The `x` integral records the arbitrary incoming Fourier coefficient. -/
theorem r324Step1WithIncoming_integral_x
    (G0 J : T4 → ℝ) (α β : Z4) (xa xm : T4) :
    (∫ x, ∫ y,
      r324Step1IntegrandWithIncoming G0 J α β xa xm x y
      ∂paperMeasure ∂paperMeasure) =
      (charT4 α xa * r324IncomingMode G0 α) *
        (((J (xa - xm) : ℝ) : ℂ) *
          (((paperSecondOrderModeDecay β : ℝ) : ℂ) *
            (charT4 β xm - charT4 β xa))) := by
  have hy :
      (fun x : T4 => ∫ y,
        r324Step1IntegrandWithIncoming G0 J α β xa xm x y
        ∂paperMeasure) =
        fun x : T4 =>
          (charT4 α x * ((G0 (x - xa) : ℝ) : ℂ)) *
            (((J (xa - xm) : ℝ) : ℂ) *
              (((paperSecondOrderModeDecay β : ℝ) : ℂ) *
                (charT4 β xm - charT4 β xa))) := by
    funext x
    rw [r324Step1WithIncoming_integral_y]
    ring
  rw [hy, integral_mul_const, integral_charT4_mul_incoming_shift]

/-- The terminal primitive kernel still supplies the identical
`E`-symmetry cancellation. -/
theorem r324Step1WithIncoming_integral_xm
    (G0 : T4 → ℝ) {J : T4 → ℝ} (hJ : MemEClassT4 J)
    (α β : Z4) (xa : T4)
    (hcos : Integrable (fun u => J u * (r324CharacterCos β u - 1))
      paperMeasure)
    (hsin : Integrable (fun u => J u * r324CharacterSin β u)
      paperMeasure) :
    (∫ xm, ∫ x, ∫ y,
      r324Step1IntegrandWithIncoming G0 J α β xa xm x y
      ∂paperMeasure ∂paperMeasure ∂paperMeasure) =
      (charT4 α xa * r324IncomingMode G0 α) *
        (((paperSecondOrderModeDecay β : ℝ) : ℂ) * charT4 β xa) *
        ∫ u, ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)
          ∂paperMeasure := by
  have hx :
      (fun xm : T4 => ∫ x, ∫ y,
        r324Step1IntegrandWithIncoming G0 J α β xa xm x y
        ∂paperMeasure ∂paperMeasure) =
        fun xm : T4 =>
          (charT4 α xa * r324IncomingMode G0 α) *
            (((J (xa - xm) : ℝ) : ℂ) *
              (((paperSecondOrderModeDecay β : ℝ) : ℂ) *
                (charT4 β xm - charT4 β xa))) := by
    funext xm
    exact r324Step1WithIncoming_integral_x G0 J α β xa xm
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

/-! ## Paying the incoming removal output in `L¹` -/

/-- The Fourier coefficient of any (4.13) input costs only its `L¹`
inverse-square majorant. -/
theorem norm_r324IncomingMode_le
    {G0 : T4 → ℝ} (hG0meas : Measurable G0) {A0 : ℝ}
    (hA0 : 0 ≤ A0)
    (hG0 : ∀ z, z ≠ 0 → |G0 z| ≤ A0 * invSqKer z) (α : Z4) :
    ‖r324IncomingMode G0 α‖ ≤
      A0 * ∫ z, invSqKer z ∂paperMeasure := by
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  have hG0int : Integrable G0 paperMeasure :=
    (integrable_invSqKer.const_mul A0).mono
      hG0meas.aestronglyMeasurable
      (by
        filter_upwards [paperMeasure.ae_ne (0 : T4)] with z hz
        simpa only [Real.norm_eq_abs, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg hA0, abs_of_nonneg (invSqKer_nonneg z)] using
          hG0 z hz)
  calc
    ‖r324IncomingMode G0 α‖ ≤
        ∫ z, ‖charT4 α z * ((G0 z : ℝ) : ℂ)‖ ∂paperMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ z, |G0 z| ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [norm_mul, norm_charT4, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    _ ≤ ∫ z, A0 * invSqKer z ∂paperMeasure := by
      exact integral_mono_ae hG0int.norm
        (integrable_invSqKer.const_mul A0)
        (by
          filter_upwards [paperMeasure.ae_ne (0 : T4)] with z hz
          exact hG0 z hz)
    _ = A0 * ∫ z, invSqKer z ∂paperMeasure := by
      rw [integral_const_mul]

/-- The generalized Step-1 integral differs from the old one only by the
incoming `L¹` factor. -/
theorem r324Step1WithIncoming_norm_le
    {G0 J : T4 → ℝ} (hG0meas : Measurable G0) {A0 : ℝ}
    (hA0 : 0 ≤ A0)
    (hG0 : ∀ z, z ≠ 0 → |G0 z| ≤ A0 * invSqKer z)
    (hJ : MemEClassT4 J) (α β : Z4)
    (hcos : Integrable (fun u => J u * (r324CharacterCos β u - 1))
      paperMeasure)
    (hsin : Integrable (fun u => J u * r324CharacterSin β u)
      paperMeasure) :
    ‖r324Step1IntegralWithIncoming G0 J α β‖ ≤
      r324PaperTorusMass *
        ((A0 * ∫ z, invSqKer z ∂paperMeasure) *
          (paperSecondOrderModeDecay β *
            ‖∫ u, ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)
              ∂paperMeasure‖)) := by
  set I : ℂ :=
    ∫ u, ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)
      ∂paperMeasure with hI
  set B : ℂ := r324IncomingMode G0 α with hB
  set F : T4 → ℂ := fun xa =>
    (charT4 α xa * B) *
      (((paperSecondOrderModeDecay β : ℝ) : ℂ) * charT4 β xa) * I
      with hF
  have hxa :
      (fun xa : T4 => ∫ xm, ∫ x, ∫ y,
        r324Step1IntegrandWithIncoming G0 J α β xa xm x y
        ∂paperMeasure ∂paperMeasure ∂paperMeasure) = F := by
    funext xa
    rw [hF, hI, hB]
    exact r324Step1WithIncoming_integral_xm G0 hJ α β xa hcos hsin
  have hnorm :
      (fun xa : T4 => ‖F xa‖) =
        fun _ : T4 =>
          ‖B‖ * (paperSecondOrderModeDecay β * ‖I‖) := by
    funext xa
    rw [hF]
    simp only [norm_mul, norm_charT4, one_mul, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (paperSecondOrderModeDecay_nonneg β)]
    ring
  have hconst :
      (∫ xa, ‖F xa‖ ∂paperMeasure) =
        r324PaperTorusMass *
          (‖B‖ * (paperSecondOrderModeDecay β * ‖I‖)) := by
    rw [hnorm, integral_const, measureReal_def, paperMeasure_univ,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    rfl
  have hBbound :
      ‖B‖ ≤ A0 * ∫ z, invSqKer z ∂paperMeasure := by
    simpa only [hB] using norm_r324IncomingMode_le hG0meas hA0 hG0 α
  have hphaseNonneg :
      0 ≤ paperSecondOrderModeDecay β * ‖I‖ :=
    mul_nonneg (paperSecondOrderModeDecay_nonneg β) (norm_nonneg I)
  calc
    ‖r324Step1IntegralWithIncoming G0 J α β‖ =
        ‖∫ xa, F xa ∂paperMeasure‖ := by
      unfold r324Step1IntegralWithIncoming
      rw [hxa]
    _ ≤ ∫ xa, ‖F xa‖ ∂paperMeasure :=
      norm_integral_le_integral_norm _
    _ = r324PaperTorusMass *
        (‖B‖ * (paperSecondOrderModeDecay β * ‖I‖)) := hconst
    _ ≤ r324PaperTorusMass *
        ((A0 * ∫ z, invSqKer z ∂paperMeasure) *
          (paperSecondOrderModeDecay β * ‖I‖)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hBbound hphaseNonneg)
        r324PaperTorusMass_pos.le

/-! ## The corrected normalized reduction interface -/

/-- Minimal paper-faithful replacement for `R324Step1Reduction`: the
incoming output of the proper-prefix removal is explicit and carries its
own scale. -/
def R324Step1ReductionWithIncoming
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (Cred : ℝ) (P : ℂ) : Prop :=
  ∃ (p : ℕ) (hp : 1 ≤ p) (G0 : T4 → ℝ) (A0 : ℝ)
    (G : Fin (2 * p - 1) → T4 → ℝ),
    2 * p ≤ m ∧ p ≤ truncOrder ε ∧
      Measurable G0 ∧ 0 ≤ A0 ∧
      (∀ z, |G0 z| ≤ A0 * invSqKer z) ∧
      IsAdmissiblePrimitiveInput p G ∧
      Integrable (fun u => primitiveKernelDiff ρ lam ε p hp G u *
        (r324CharacterCos β u - 1)) paperMeasure ∧
      Integrable (fun u => primitiveKernelDiff ρ lam ε p hp G u *
        r324CharacterSin β u) paperMeasure ∧
      ‖P‖ ≤ (Cred * lam) ^ (m - 2 * p) *
      ‖r324Step1IntegralWithIncoming G0
          (primitiveKernelDiff ρ lam ε p hp G) α β‖

/-! ## The genuine terminal trace: the inserted-majorant estimate -/

namespace R324WithinHalfResidualPrefix

namespace R324FullPairingBudgetTerminalAdapter

variable {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    {budget :
      R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ}

/-! ## Removing the genuinely empty post-terminal carrier -/

/-- The carrier after the retained terminal head is empty, hence the
apparently retained post-head Haar integral has mass one.  This is the
normalization fact deliberately left literal by the earlier Fubini bridge. -/
theorem integral_terminalPost_rawLocal_eq
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (x y : T4)
    (t :
      Fin
          (2 * residualBlockOrder
            data.geometry.terminalData.terminal.2) →
        T4) :
    (∫ _v :
        (data.geometry.trace.stopPrefix.afterHead
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton)
            |>.SurvivingCoordinate →
          T4,
      ((data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).rawLocalIntegrand
          ρ ε (x - y) (fun j => t j - y) : ℂ)
      ∂Measure.pi fun _ => paperMeasure) =
      ((data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).rawLocalIntegrand
          ρ ε (x - y) (fun j => t j - y) : ℂ) := by
  let post :=
    data.geometry.trace.stopPrefix.afterHead
      data.geometry.terminalData.terminal []
      data.geometry.stop_remaining_eq_singleton
  letI : IsEmpty post.SurvivingCoordinate :=
    ⟨fun i => by
      let j : Fin (2 * q) := i.1
      have hi : j ∈ post.state.active := i.2
      have hempty : post.state.active = ∅ := by
        simpa only [post] using
          data.geometry.terminal_afterHead_active_eq_empty
      have hnot : j ∉ post.state.active := by
        rw [hempty]
        simp
      exact hnot hi⟩
  rw [integral_unique]
  have hmass :
      (Measure.pi fun _ : post.SurvivingCoordinate =>
        paperMeasure).real Set.univ = 1 := by
    rw [measureReal_def, Measure.pi_empty_univ]
    simp
  rw [hmass, one_smul]

/-- At the singleton stop the complete active-scale carrier is exactly the
incoming predecessor, the terminal internal chain, and the one outgoing
Green slot.  This is the local product decomposition needed to compare the
actual Step-1 charge with the global budget invariant. -/
theorem terminal_activeEdgeScaleProduct_eq
    (data : R324FullPairingBudgetTerminalAdapter budget) :
    (∏ edge ∈ data.geometry.trace.stopPrefix.activeEdgeSlots,
        budget.stopScale edge) =
      budget.stopScale
          (r324WithinHalfPredecessorSlot
            data.geometry.trace.stopPrefix.state
            data.geometry.terminalData.terminal) *
        r324WithinHalfInternalEdgeScaleProduct
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton)
          budget.stopScale *
        budget.stopScale
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).outgoingSlot := by
  let res := data.geometry.trace.stopPrefix
  let head := data.geometry.terminalData.terminal
  let hremaining : res.remaining = head :: [] :=
    data.geometry.stop_remaining_eq_singleton
  let block := res.headBlockSlots head [] hremaining
  have hsubset : block ⊆ res.activeEdgeSlots :=
    res.headBlockSlots_subset_activeEdgeSlots head [] hremaining
  have hpartition :=
    Finset.prod_sdiff hsubset (f := budget.stopScale)
  have hpost :
      res.activeEdgeSlots \ block =
        (res.afterHead head [] hremaining).activeEdgeSlots := by
    exact (res.afterHead_activeEdgeSlots head [] hremaining).symm
  have hblockProduct :
      (∏ edge ∈ block, budget.stopScale edge) =
        r324WithinHalfInternalEdgeScaleProduct
            (res.headContext head [] hremaining) budget.stopScale *
          budget.stopScale
            (res.headContext head [] hremaining).outgoingSlot := by
    simpa only [block,
      R324WithinHalfResidualPrefix.headBlockScaleProduct] using
      res.headBlockScaleProduct_eq_internal_mul_outgoing
        head [] hremaining budget.stopScale
  rw [hpost,
    data.geometry.terminal_afterHead_activeEdgeSlots_eq_singleton,
    Finset.prod_singleton, hblockProduct] at hpartition
  rw [data.geometry.terminal_predecessorSlot_eq_zero]
  simpa only [res, head, hremaining, block,
    R324WithinHalfResidualPrefix.headBlockScaleProduct, mul_assoc] using
    hpartition.symm

/-! ## Absolute integrability of the corrected four-point Step-1 kernel -/

private theorem integrable_char_mul_real_sub_right
    (G : T4 → ℝ) (hG : Integrable G paperMeasure)
    (k : Z4) (a : T4) :
    Integrable
      (fun x : T4 => charT4 k x * ((G (x - a) : ℝ) : ℂ))
      paperMeasure := by
  have htranslated :
      Integrable (fun x : T4 => (G (x - a) : ℂ)) paperMeasure := by
    have hreal : Integrable (fun x : T4 => G (x - a)) paperMeasure :=
      ((measurePreserving_sub_paper a).integrable_comp
        hG.aestronglyMeasurable).mpr hG
    exact hreal.ofReal
  exact htranslated.bdd_mul
    (continuous_charT4 k).aestronglyMeasurable
    (.of_forall fun x => by rw [norm_charT4])

private theorem integrable_char_mul_greenDifference_left
    (k : Z4) (a b : T4) :
    Integrable
      (fun y : T4 =>
        charT4 k y *
          (((greenFn (a - y) : ℝ) : ℂ) -
            ((greenFn (b - y) : ℝ) : ℂ)))
      paperMeasure := by
  have ha :
      Integrable
        (fun y : T4 =>
          charT4 k y * ((greenFn (a - y) : ℝ) : ℂ))
        paperMeasure :=
    integrable_charT4_mul_greenFn_shift k a
  have hb :
      Integrable
        (fun y : T4 =>
          charT4 k y * ((greenFn (b - y) : ℝ) : ℂ))
        paperMeasure :=
    integrable_charT4_mul_greenFn_shift k b
  apply (ha.sub hb).congr
  filter_upwards with y
  simp only [Pi.sub_apply]
  ring

private theorem integral_abs_real_sub_right
    (G : T4 → ℝ) (a : T4) :
    (∫ x : T4, |G (x - a)| ∂paperMeasure) =
      ∫ u : T4, |G u| ∂paperMeasure := by
  rw [paperMeasure_eq_volume]
  exact integral_sub_right_eq_self (fun u : T4 => |G u|) a

private theorem integral_abs_greenDifference_left_le_two
    (a b : T4) :
    (∫ y : T4, |greenFn (a - y) - greenFn (b - y)|
        ∂paperMeasure) ≤ 2 := by
  have ha : Integrable (fun y : T4 => greenFn (a - y)) paperMeasure := by
    have heq :
        (fun y : T4 => greenFn (a - y)) =
          fun y : T4 => greenFn (y - a) := by
      funext y
      rw [show a - y = -(y - a) by abel,
        greenFn_memE.neg_invariant]
    rw [heq]
    exact integrable_greenFn_sub a
  have hb : Integrable (fun y : T4 => greenFn (b - y)) paperMeasure := by
    have heq :
        (fun y : T4 => greenFn (b - y)) =
          fun y : T4 => greenFn (y - b) := by
      funext y
      rw [show b - y = -(y - b) by abel,
        greenFn_memE.neg_invariant]
    rw [heq]
    exact integrable_greenFn_sub b
  calc
    (∫ y : T4, |greenFn (a - y) - greenFn (b - y)|
        ∂paperMeasure) ≤
        ∫ y : T4, greenFn (a - y) + greenFn (b - y)
          ∂paperMeasure := by
      have hdiff :
          Integrable
            (fun y : T4 => greenFn (a - y) - greenFn (b - y))
            paperMeasure := by
        apply (ha.sub hb).congr
        filter_upwards with y
        change greenFn (a - y) - greenFn (b - y) =
          greenFn (a - y) - greenFn (b - y)
        rfl
      have hsum :
          Integrable
            (fun y : T4 => greenFn (a - y) + greenFn (b - y))
            paperMeasure := by
        apply (ha.add hb).congr
        filter_upwards with y
        change greenFn (a - y) + greenFn (b - y) =
          greenFn (a - y) + greenFn (b - y)
        rfl
      apply integral_mono hdiff.norm hsum
      intro y
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (greenFn_nonneg _)] using
        abs_sub (greenFn (a - y)) (greenFn (b - y))
    _ = 2 := by
      have hadd :
          (∫ y : T4, greenFn (a - y) + greenFn (b - y)
              ∂paperMeasure) =
            (∫ y : T4, greenFn (a - y) ∂paperMeasure) +
              ∫ y : T4, greenFn (b - y) ∂paperMeasure := by
        have hfun :
            (fun y : T4 => greenFn (a - y) + greenFn (b - y)) =
              (fun y : T4 => greenFn (a - y)) +
                fun y : T4 => greenFn (b - y) := by
          funext y
          change greenFn (a - y) + greenFn (b - y) =
            greenFn (a - y) + greenFn (b - y)
          rfl
        rw [hfun]
        exact integral_add ha hb
      rw [hadd]
      have hleft (c : T4) :
          (∫ y : T4, greenFn (c - y) ∂paperMeasure) = 1 := by
        have heq :
            (fun y : T4 => greenFn (c - y)) =
              fun y : T4 => greenFn (y - c) := by
          funext y
          rw [show c - y = -(y - c) by abel,
            greenFn_memE.neg_invariant]
        rw [heq]
        exact integral_greenFn_sub c
      rw [hleft a, hleft b]
      norm_num

private theorem integrable_paperDifferenceKernel_local
    (J : T4 → ℝ) (hJ : Integrable J paperMeasure)
    (hJmeas : Measurable J) :
    Integrable (fun p : T4 × T4 => J (p.1 - p.2))
      (paperMeasure.prod paperMeasure) := by
  have hmeas : Measurable (fun p : T4 × T4 => J (p.1 - p.2)) :=
    hJmeas.comp (measurable_fst.sub measurable_snd)
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact .of_forall fun x => by
      have hcomp :=
        ((measurePreserving_subLeftT4 x).integrable_comp
          hJ.aestronglyMeasurable).mpr hJ
      refine hcomp.congr (.of_forall fun y => ?_)
      rw [Function.comp_apply, subLeftT4MeasurableEquiv_apply]
  · have heq :
        (fun x : T4 =>
          ∫ y : T4, ‖J (x - y)‖ ∂paperMeasure) =
          fun _ : T4 => ∫ z : T4, ‖J z‖ ∂paperMeasure := by
      funext x
      simpa only [subLeftT4MeasurableEquiv_apply] using
        (measurePreserving_subLeftT4 x).integral_comp'
          (fun z : T4 => ‖J z‖)
    rw [heq]
    exact integrable_const _

/-- The corrected four-point integrand is absolutely integrable whenever
the incoming removal output and the retained primitive kernel are in `L¹`.
This is the Fubini license used below; no estimate is taken here. -/
theorem integrable_r324Step1PairIntegrandWithIncoming
    (G0 J : T4 → ℝ)
    (hG0 : Integrable G0 paperMeasure) (hG0meas : Measurable G0)
    (hJ : Integrable J paperMeasure) (hJmeas : Measurable J)
    (alpha beta : Z4) :
    Integrable
      (fun p : (T4 × T4) × (T4 × T4) =>
        r324Step1IntegrandWithIncoming G0 J alpha beta
          p.1.1 p.1.2 p.2.1 p.2.2)
      ((paperMeasure.prod paperMeasure).prod
        (paperMeasure.prod paperMeasure)) := by
  let F : (T4 × T4) × (T4 × T4) → ℂ := fun p =>
    r324Step1IntegrandWithIncoming G0 J alpha beta
      p.1.1 p.1.2 p.2.1 p.2.2
  have hFmeas : Measurable F := by
    have hca : Measurable (fun p : (T4 × T4) × (T4 × T4) =>
        charT4 alpha p.2.1) :=
      (continuous_charT4 alpha).measurable.comp
        (measurable_fst.comp measurable_snd)
    have hcb : Measurable (fun p : (T4 × T4) × (T4 × T4) =>
        charT4 beta p.2.2) :=
      (continuous_charT4 beta).measurable.comp
        (measurable_snd.comp measurable_snd)
    have hG : Measurable (fun p : (T4 × T4) × (T4 × T4) =>
        ((G0 (p.2.1 - p.1.1) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp
        (hG0meas.comp
          ((measurable_fst.comp measurable_snd).sub
            (measurable_fst.comp measurable_fst)))
    have hJm : Measurable (fun p : (T4 × T4) × (T4 × T4) =>
        ((J (p.1.1 - p.1.2) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp
        (hJmeas.comp
          ((measurable_fst.comp measurable_fst).sub
            (measurable_snd.comp measurable_fst)))
    have hGa : Measurable (fun p : (T4 × T4) × (T4 × T4) =>
        ((greenFn (p.1.2 - p.2.2) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp
        (measurable_greenFn.comp
          ((measurable_snd.comp measurable_fst).sub
            (measurable_snd.comp measurable_snd)))
    have hGb : Measurable (fun p : (T4 × T4) × (T4 × T4) =>
        ((greenFn (p.1.1 - p.2.2) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp
        (measurable_greenFn.comp
          ((measurable_fst.comp measurable_fst).sub
            (measurable_snd.comp measurable_snd)))
    exact hca.mul hcb |>.mul hG |>.mul hJm |>.mul (hGa.sub hGb)
  rw [integrable_prod_iff hFmeas.aestronglyMeasurable]
  constructor
  · exact .of_forall fun p => by
      let fx : T4 → ℂ := fun x =>
        charT4 alpha x * ((G0 (x - p.1) : ℝ) : ℂ)
      let fy : T4 → ℂ := fun y =>
        charT4 beta y *
          (((greenFn (p.2 - y) : ℝ) : ℂ) -
            ((greenFn (p.1 - y) : ℝ) : ℂ))
      have hfx : Integrable fx paperMeasure :=
        integrable_char_mul_real_sub_right G0 hG0 alpha p.1
      have hfy : Integrable fy paperMeasure :=
        integrable_char_mul_greenDifference_left beta p.2 p.1
      have hprod := hfx.mul_prod hfy
      have hconst := hprod.const_mul ((J (p.1 - p.2) : ℝ) : ℂ)
      apply hconst.congr
      filter_upwards with xy
      dsimp only [F, fx, fy]
      unfold r324Step1IntegrandWithIncoming
      ring
  · have hnormMeas :
        StronglyMeasurable
          (fun p : T4 × T4 =>
            ∫ xy : T4 × T4, ‖F (p, xy)‖
              ∂(paperMeasure.prod paperMeasure)) :=
      hFmeas.norm.stronglyMeasurable.integral_prod_right'
    let Gmass : ℝ := ∫ u : T4, |G0 u| ∂paperMeasure
    let major : T4 × T4 → ℝ := fun p =>
      |J (p.1 - p.2)| * (Gmass * 2)
    have hJabs : Integrable (fun u => |J u|) paperMeasure := by
      simpa only [Real.norm_eq_abs] using hJ.norm
    have hJabsMeas : Measurable (fun u => |J u|) := hJmeas.abs
    have hmajor : Integrable major (paperMeasure.prod paperMeasure) := by
      exact
        (integrable_paperDifferenceKernel_local
          (fun u => |J u|) hJabs hJabsMeas).mul_const (Gmass * 2)
    refine hmajor.mono' hnormMeas.aestronglyMeasurable (.of_forall fun p => ?_)
    have hsection :
        Integrable (fun xy : T4 × T4 => F (p, xy))
          (paperMeasure.prod paperMeasure) := by
      let fx : T4 → ℂ := fun x =>
        charT4 alpha x * ((G0 (x - p.1) : ℝ) : ℂ)
      let fy : T4 → ℂ := fun y =>
        charT4 beta y *
          (((greenFn (p.2 - y) : ℝ) : ℂ) -
            ((greenFn (p.1 - y) : ℝ) : ℂ))
      have hfx : Integrable fx paperMeasure :=
        integrable_char_mul_real_sub_right G0 hG0 alpha p.1
      have hfy : Integrable fy paperMeasure :=
        integrable_char_mul_greenDifference_left beta p.2 p.1
      have hprod := hfx.mul_prod hfy
      have hconst := hprod.const_mul ((J (p.1 - p.2) : ℝ) : ℂ)
      apply hconst.congr
      filter_upwards with xy
      dsimp only [F, fx, fy]
      unfold r324Step1IntegrandWithIncoming
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg
      (integral_nonneg fun xy => norm_nonneg (F (p, xy)))]
    change
      (∫ xy : T4 × T4, ‖F (p, xy)‖
          ∂(paperMeasure.prod paperMeasure)) ≤ major p
    have hnormEq :
        (∫ xy : T4 × T4, ‖F (p, xy)‖
            ∂(paperMeasure.prod paperMeasure)) =
          |J (p.1 - p.2)| *
            ((∫ x : T4, |G0 (x - p.1)| ∂paperMeasure) *
              ∫ y : T4,
                |greenFn (p.2 - y) - greenFn (p.1 - y)|
                ∂paperMeasure) := by
      calc
        (∫ xy : T4 × T4, ‖F (p, xy)‖
            ∂(paperMeasure.prod paperMeasure)) =
            ∫ xy : T4 × T4,
              |J (p.1 - p.2)| *
                (|G0 (xy.1 - p.1)| *
                  |greenFn (p.2 - xy.2) - greenFn (p.1 - xy.2)|)
              ∂(paperMeasure.prod paperMeasure) := by
          apply integral_congr_ae
          filter_upwards with xy
          dsimp only [F]
          unfold r324Step1IntegrandWithIncoming
          simp only [norm_mul, norm_charT4, one_mul, Complex.norm_real,
            Real.norm_eq_abs]
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          ring
        _ = |J (p.1 - p.2)| *
            ∫ xy : T4 × T4,
              |G0 (xy.1 - p.1)| *
                |greenFn (p.2 - xy.2) - greenFn (p.1 - xy.2)|
              ∂(paperMeasure.prod paperMeasure) := by
          rw [integral_const_mul]
        _ = _ := by
          exact congrArg (|J (p.1 - p.2)| * ·)
            (integral_prod_mul
              (μ := paperMeasure) (ν := paperMeasure)
              (fun x : T4 => |G0 (x - p.1)|)
              (fun y : T4 =>
                |greenFn (p.2 - y) - greenFn (p.1 - y)|))
    rw [hnormEq, integral_abs_real_sub_right]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (integral_abs_greenDifference_left_le_two p.2 p.1)
        (integral_nonneg fun u => abs_nonneg (G0 u)))
      (abs_nonneg (J (p.1 - p.2)))

private theorem integrable_r324Step1PairSectionWithIncoming
    (G0 J : T4 → ℝ)
    (hG0 : Integrable G0 paperMeasure)
    (alpha beta : Z4) (z w : T4) :
    Integrable
      (fun p : T4 × T4 =>
        r324Step1IntegrandWithIncoming G0 J alpha beta
          z w p.1 p.2)
      (paperMeasure.prod paperMeasure) := by
  let fx : T4 → ℂ := fun x =>
    charT4 alpha x * ((G0 (x - z) : ℝ) : ℂ)
  let fy : T4 → ℂ := fun y =>
    charT4 beta y *
      (((greenFn (w - y) : ℝ) : ℂ) -
        ((greenFn (z - y) : ℝ) : ℂ))
  have hfx : Integrable fx paperMeasure :=
    integrable_char_mul_real_sub_right G0 hG0 alpha z
  have hfy : Integrable fy paperMeasure :=
    integrable_char_mul_greenDifference_left beta w z
  have hprod := hfx.mul_prod hfy
  have hconst := hprod.const_mul ((J (z - w) : ℝ) : ℂ)
  apply hconst.congr
  filter_upwards with xy
  dsimp only [fx, fy]
  unfold r324Step1IntegrandWithIncoming
  ring

/-- The nested order used in the paper's display (4.17) is the grouped
`(z,w)`-then-`(x,y)` product integral. -/
theorem r324Step1IntegralWithIncoming_eq_pairIntegral
    (G0 J : T4 → ℝ)
    (hG0 : Integrable G0 paperMeasure) (hG0meas : Measurable G0)
    (hJ : Integrable J paperMeasure) (hJmeas : Measurable J)
    (alpha beta : Z4) :
    r324Step1IntegralWithIncoming G0 J alpha beta =
      ∫ p : (T4 × T4) × (T4 × T4),
        r324Step1IntegrandWithIncoming G0 J alpha beta
          p.1.1 p.1.2 p.2.1 p.2.2
        ∂((paperMeasure.prod paperMeasure).prod
          (paperMeasure.prod paperMeasure)) := by
  let F : (T4 × T4) × (T4 × T4) → ℂ := fun p =>
    r324Step1IntegrandWithIncoming G0 J alpha beta
      p.1.1 p.1.2 p.2.1 p.2.2
  have hF : Integrable F
      ((paperMeasure.prod paperMeasure).prod
        (paperMeasure.prod paperMeasure)) :=
    integrable_r324Step1PairIntegrandWithIncoming
      G0 J hG0 hG0meas hJ hJmeas alpha beta
  have houter :
      Integrable
        (fun zw : T4 × T4 =>
          ∫ xy : T4 × T4, F (zw, xy)
            ∂(paperMeasure.prod paperMeasure))
        (paperMeasure.prod paperMeasure) :=
    hF.integral_prod_left
  unfold r324Step1IntegralWithIncoming
  rw [integral_prod F hF]
  rw [integral_prod _ houter]
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with w
  have hsection :=
    integrable_r324Step1PairSectionWithIncoming
      G0 J hG0 alpha beta z w
  rw [integral_prod _ hsection]

/-! ## Actual terminal inputs are in `L¹` -/

private theorem integrable_certified_terminalEdge
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (edge : Fin (2 * q + 1)) :
    Integrable
      (data.geometry.trace.stopPrefix.state.edges edge)
      paperMeasure := by
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  refine
    (integrable_invSqKer.const_mul (budget.stopScale edge)).mono
      (data.certificate.measurable edge).aestronglyMeasurable ?_
  filter_upwards [paperMeasure.ae_ne (0 : T4)] with z hz
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg
      (mul_nonneg (data.certificate.scale_pos edge).le
        (invSqKer_nonneg z))]
  exact data.certificate.bound edge z hz

/-- Honest integrability of the translated terminal raw local block follows
from integrability of the stopped residual.  The apparently remaining
post-head tuple has empty index type, so the almost-everywhere head section
provided by Fubini is the unique section. -/
private theorem integrable_terminalRawLocal_of_stop
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (x y : T4)
    (hstop :
      Integrable
        (fun v :
            data.geometry.trace.stopPrefix.SurvivingCoordinate → T4 =>
          (data.geometry.trace.stopPrefix.residualIntegrand
              ρ ε x y
              (data.geometry.trace.stopPrefix.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun t :
          Fin
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2) → T4 =>
        ((data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).rawLocalIntegrand
            ρ ε (x - y) (fun j => t j - y) : ℂ))
      (Measure.pi fun _ => paperMeasure) := by
  let post :=
    data.geometry.trace.stopPrefix.afterHead
      data.geometry.terminalData.terminal []
      data.geometry.stop_remaining_eq_singleton
  letI : IsEmpty post.SurvivingCoordinate :=
    ⟨fun i => by
      let j : Fin (2 * q) := i.1
      have hi : j ∈ post.state.active := i.2
      have hempty : post.state.active = ∅ := by
        simpa only [post] using
          data.geometry.terminal_afterHead_active_eq_empty
      have hnot : j ∉ post.state.active := by
        rw [hempty]
        simp
      exact hnot hi⟩
  let μpost : Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  have hμpost : μpost ≠ 0 := by
    intro hzero
    have huniv := congrArg
      (fun μ : Measure (post.SurvivingCoordinate → T4) => μ Set.univ)
      hzero
    have hmass : μpost Set.univ = 1 := by
      dsimp only [μpost]
      rw [Measure.pi_empty_univ]
    rw [hzero] at hmass
    simp at hmass
  letI : NeZero μpost := ⟨hμpost⟩
  have hsections :=
    data.geometry.trace.stopPrefix
      |>.eventually_integrable_weightedHeadLocal_of_integrable
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton x y hstop
  change ∀ᵐ v ∂μpost, _ at hsections
  obtain ⟨v, hv⟩ := hsections.exists
  have hraw :
      Integrable
        (fun t :
            Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2) → T4 =>
          ((data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).rawLocalIntegrand
              ρ ε (x - y) t : ℂ))
        (Measure.pi fun _ => paperMeasure) := by
    apply hv.congr
    filter_upwards with t
    rw [data.geometry.terminal_headPredecessorPoint_eq_left,
      data.geometry.terminal_headSuccessorPoint_eq_right,
      data.geometry.terminal_headOuterFactor_eq_one]
    norm_num
  let ctx :=
    data.geometry.trace.stopPrefix.headContext
      data.geometry.terminalData.terminal []
      data.geometry.stop_remaining_eq_singleton
  let translation := ctx.physicalBlockTranslation (-y)
  have htranslated :
      Integrable
        ((fun t :
            Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2) → T4 =>
          ((ctx.rawLocalIntegrand ρ ε (x - y) t : ℂ))) ∘ translation)
        (Measure.pi fun _ => paperMeasure) :=
    (ctx.measurePreserving_physicalBlockTranslation (-y))
      |>.integrable_comp_emb translation.measurableEmbedding
      |>.mpr hraw
  apply htranslated.congr
  filter_upwards with t
  dsimp only [Function.comp_apply, ctx]
  rw [show translation t = fun j => t j - y by
    funext j
    rw [ctx.physicalBlockTranslation_apply]
    abel]

/-- The terminal raw-local block, after the honest standard-block change of
coordinates, is exactly the four physical kernels of (4.17).  In particular
the incoming factor is the actual predecessor edge of the reached trace. -/
theorem lamEps_pow_integral_terminalRawLocal_eq_step1Section
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x y : T4)
    (hstop :
      Integrable
        (fun v :
            data.geometry.trace.stopPrefix.SurvivingCoordinate → T4 =>
          (data.geometry.trace.stopPrefix.residualIntegrand
              ρ ε x y
              (data.geometry.trace.stopPrefix.reconstruct v) : ℂ))
        (Measure.pi fun _ => paperMeasure)) :
    lamEps lam ε ^
          (2 * residualBlockOrder
            data.geometry.terminalData.terminal.2) *
        (∫ t :
            Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2) → T4,
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).rawLocalIntegrand
              ρ ε (x - y) (fun j => t j - y)
          ∂Measure.pi fun _ => paperMeasure) =
      ∫ p : T4 × T4,
        data.geometry.trace.stopPrefix.state.edges
            (r324WithinHalfPredecessorSlot
              data.geometry.trace.stopPrefix.state
              data.geometry.terminalData.terminal)
            (x - p.1) *
          primitiveKernelDiff ρ lam ε
            (residualBlockOrder
              data.geometry.terminalData.terminal.2)
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).internalEdges
            (p.1 - p.2) *
          (greenFn (p.2 - y) - greenFn (p.1 - y))
        ∂(paperMeasure.prod paperMeasure) := by
  let n := residualBlockOrder data.geometry.terminalData.terminal.2
  let ctx :=
    data.geometry.trace.stopPrefix.headContext
      data.geometry.terminalData.terminal []
      data.geometry.stop_remaining_eq_singleton
  have hn : 1 ≤ n := by
    simpa only [n] using
      data.geometry.trace.stopPrefix.head_one_le_blockOrder
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton
  have hraw := data.integrable_terminalRawLocal_of_stop x y hstop
  have hrawReal :
      Integrable
        (fun t : Fin (2 * n) → T4 =>
          ctx.rawLocalIntegrand ρ ε (x - y) (fun j => t j - y))
        (Measure.pi fun _ => paperMeasure) := by
    apply hraw.re.congr
    filter_upwards with t
    dsimp only [ctx, n]
    norm_num
  rw [integral_standardBlock_eq_integral_endpoints_internal
    n hn _ hrawReal]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  have hpoint :
      (fun u : Fin (2 * n - 2) → T4 =>
        ctx.rawLocalIntegrand ρ ε (x - y)
          (fun j =>
            primitiveAssemble n hn
              p.1 p.2 u j - y)) =
        fun u =>
          data.geometry.terminalGroupedPrimitiveCore x
              (primitiveAssemble n hn p.1 p.2 u) *
            (greenFn (p.2 - y) - greenFn (p.1 - y)) := by
    funext u
    rw [show
      ctx.rawLocalIntegrand ρ ε (x - y)
          (fun j =>
            primitiveAssemble n hn
              p.1 p.2 u j - y) =
        data.geometry.terminalGroupedPrimitiveCore x
            (primitiveAssemble n hn p.1 p.2 u) *
          (greenFn
              ((primitiveAssemble n hn
                p.1 p.2 u)
                  (primitiveLast n hn) - y) -
            greenFn
              ((primitiveAssemble n hn p.1 p.2 u)
                ⟨0, Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hn)⟩ - y)) by
      simpa only [n, ctx] using
        data.geometry.terminal_rawLocal_translated_eq_groupedCore_mul_greenDifference
          x y (primitiveAssemble n hn p.1 p.2 u)]
    rw [primitiveAssemble_last, primitiveAssemble_zero]
  rw [hpoint, integral_mul_const]
  rw [← mul_assoc]
  rw [data.lamEps_pow_integral_terminalGroupedPrimitiveCore_eq_predecessor_mul_primitiveKernelDiff
    x p.1 p.2
      (fun κB =>
        data.integrable_terminalClosedIntegrand_section
          hε hε1 κB p.1 p.2)]

/-- Exact paper-(4.17) representation of the complete terminal Fourier
integral.  This is the missing normalization seam: the incoming kernel is
the reached predecessor edge, not an unjustified fresh copy of `greenFn`.
All changes of integration order are licensed by the stopped-residual and
four-point `L¹` theorems. -/
theorem terminalRawLocalFourierIntegral_eq_step1IntegralWithIncoming
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hJ :
      Integrable
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder
            data.geometry.terminalData.terminal.2)
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalEdges)
        paperMeasure)
    (alpha beta : Z4) :
    data.terminalRawLocalFourierIntegral alpha beta =
      r324Step1IntegralWithIncoming
        (data.geometry.trace.stopPrefix.state.edges
          (r324WithinHalfPredecessorSlot
            data.geometry.trace.stopPrefix.state
            data.geometry.terminalData.terminal))
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder
            data.geometry.terminalData.terminal.2)
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalEdges)
        alpha beta := by
  let pred :=
    r324WithinHalfPredecessorSlot
      data.geometry.trace.stopPrefix.state
      data.geometry.terminalData.terminal
  let G0 : T4 → ℝ :=
    data.geometry.trace.stopPrefix.state.edges pred
  let J : T4 → ℝ :=
    primitiveKernelDiff ρ lam ε
      (residualBlockOrder data.geometry.terminalData.terminal.2)
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).internalEdges
  let F : (T4 × T4) × (T4 × T4) → ℂ := fun p =>
    r324Step1IntegrandWithIncoming G0 J alpha beta
      p.1.1 p.1.2 p.2.1 p.2.2
  have hG0 : Integrable G0 paperMeasure := by
    exact data.integrable_certified_terminalEdge pred
  have hG0meas : Measurable G0 := by
    exact data.certificate.measurable pred
  have hJmeas : Measurable J := by
    dsimp only [J]
    exact measurable_primitiveKernelDiff ρ lam ε
      (residualBlockOrder data.geometry.terminalData.terminal.2)
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).internalEdges
      (fun j => by
        simpa only [R324WithinHalfStepContext.internalEdges,
          R324WithinHalfResidualPrefix.headContext] using
          data.certificate.measurable
            ((data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).internalSlot j))
  have hF : Integrable F
      ((paperMeasure.prod paperMeasure).prod
        (paperMeasure.prod paperMeasure)) := by
    exact integrable_r324Step1PairIntegrandWithIncoming
      G0 J hG0 hG0meas (by simpa only [J] using hJ) hJmeas alpha beta
  have hroot :=
    eventually_integrable_initial_residualIntegrand
      ρ lam hε hε1 κ
  have hstopAE :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        Integrable
          (fun v :
              data.geometry.trace.stopPrefix.SurvivingCoordinate → T4 =>
            (data.geometry.trace.stopPrefix.residualIntegrand
                ρ ε p.1 p.2
                (data.geometry.trace.stopPrefix.reconstruct v) : ℂ))
          (Measure.pi fun _ => paperMeasure) := by
    filter_upwards [hroot] with p hp
    exact
      data.geometry.trace.integrable_stopPrefix_residualIntegrand_of_integrable
        p.1 p.2 hp
  let raw : T4 × T4 → ℝ := fun p =>
    ∫ t :
        Fin
            (2 * residualBlockOrder
              data.geometry.terminalData.terminal.2) → T4,
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).rawLocalIntegrand
          ρ ε (p.1 - p.2) (fun j => t j - p.2)
      ∂Measure.pi fun _ => paperMeasure
  let stepSection : T4 × T4 → ℝ := fun p =>
    ∫ zw : T4 × T4,
      G0 (p.1 - zw.1) * J (zw.1 - zw.2) *
        (greenFn (zw.2 - p.2) - greenFn (zw.1 - p.2))
      ∂(paperMeasure.prod paperMeasure)
  calc
    data.terminalRawLocalFourierIntegral alpha beta =
        ∫ p : T4 × T4,
          charT4 alpha p.1 * charT4 beta p.2 *
            ((lamEps lam ε ^
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2) *
              raw p : ℝ) : ℂ)
          ∂(paperMeasure.prod paperMeasure) := by
      unfold terminalRawLocalFourierIntegral
      apply integral_congr_ae
      filter_upwards with p
      have hpost :
          (∫ t :
              Fin
                  (2 * residualBlockOrder
                    data.geometry.terminalData.terminal.2) → T4,
            ∫ _v :
                (data.geometry.trace.stopPrefix.afterHead
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton)
                    |>.SurvivingCoordinate → T4,
              ((data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).rawLocalIntegrand
                  ρ ε (p.1 - p.2) (fun j => t j - p.2) : ℂ)
              ∂Measure.pi fun _ => paperMeasure
            ∂Measure.pi fun _ => paperMeasure) =
            ∫ t :
                Fin
                    (2 * residualBlockOrder
                      data.geometry.terminalData.terminal.2) → T4,
              ((data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).rawLocalIntegrand
                  ρ ε (p.1 - p.2) (fun j => t j - p.2) : ℂ)
              ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        exact data.integral_terminalPost_rawLocal_eq p.1 p.2 t
      rw [hpost, integral_complex_ofReal]
      dsimp only [raw]
      push_cast
      ring
    _ =
        ∫ p : T4 × T4,
          charT4 alpha p.1 * charT4 beta p.2 *
            ((stepSection p : ℝ) : ℂ)
          ∂(paperMeasure.prod paperMeasure) := by
      apply integral_congr_ae
      filter_upwards [hstopAE] with p hp
      dsimp only [raw, stepSection, G0, J]
      rw [data.lamEps_pow_integral_terminalRawLocal_eq_step1Section
        hε hε1 p.1 p.2 hp]
    _ =
        ∫ xy : T4 × T4,
          ∫ zw : T4 × T4, F (zw, xy)
            ∂(paperMeasure.prod paperMeasure)
          ∂(paperMeasure.prod paperMeasure) := by
      apply integral_congr_ae
      filter_upwards with xy
      dsimp only [stepSection]
      rw [← integral_complex_ofReal]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with zw
      dsimp only [F, G0, J, r324Step1IntegrandWithIncoming]
      push_cast
      ring
    _ = ∫ p, F p
          ∂((paperMeasure.prod paperMeasure).prod
            (paperMeasure.prod paperMeasure)) :=
      (integral_prod_symm F hF).symm
    _ = r324Step1IntegralWithIncoming G0 J alpha beta := by
      exact (r324Step1IntegralWithIncoming_eq_pairIntegral
        G0 J hG0 hG0meas (by simpa only [J] using hJ) hJmeas
        alpha beta).symm
    _ = _ := by rfl

/-- Proposition 4.1 applied to the normalized actual terminal edges makes
the heterogeneous retained primitive kernel genuinely integrable. -/
theorem integrable_terminalPrimitiveKernelDiff_of_provider
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (supportConstant primitiveConstant : ℝ)
    (hprop :
      ∀ H :
          Fin
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2 - 1) →
            T4 → ℝ,
        IsAdmissiblePrimitiveInput
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              H supportConstant primitiveConstant) :
    Integrable
      (primitiveKernelDiff ρ lam ε
        (residualBlockOrder
          data.geometry.terminalData.terminal.2)
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).internalEdges)
      paperMeasure := by
  let ctx :=
    data.geometry.trace.stopPrefix.headContext
      data.geometry.terminalData.terminal []
      data.geometry.stop_remaining_eq_singleton
  let J : T4 → ℝ :=
    primitiveKernelDiff ρ lam ε
      (residualBlockOrder data.geometry.terminalData.terminal.2)
      ctx.one_le_blockOrder ctx.internalEdges
  let Jscale : ℝ :=
    r324WithinHalfInternalEdgeScaleProduct ctx budget.stopScale
  let M : T4 → ℝ :=
    primitiveKernelMajorant primitiveConstant lam ε supportConstant
      (residualBlockOrder data.geometry.terminalData.terminal.2)
  have hJmeas : Measurable J := by
    dsimp only [J]
    exact measurable_primitiveKernelDiff ρ lam ε
      (residualBlockOrder data.geometry.terminalData.terminal.2)
      ctx.one_le_blockOrder ctx.internalEdges
      (fun j => by
        simpa only [ctx, R324WithinHalfStepContext.internalEdges,
          R324WithinHalfResidualPrefix.headContext] using
          data.certificate.measurable (ctx.internalSlot j))
  have hM : Integrable M paperMeasure :=
    integrable_primitiveKernelMajorant primitiveConstant lam ε
      supportConstant
      (residualBlockOrder data.geometry.terminalData.terminal.2) hε
  have hJscale : 0 < Jscale := by
    dsimp only [Jscale]
    exact data.certificate.internalEdgeScaleProduct_pos
  have hJoff : ∀ u, u ≠ 0 → |J u| ≤ Jscale * M u := by
    intro u hu
    dsimp only [J, Jscale, M]
    simpa [ctx, R324WithinHalfResidualPrefix.headContext,
      R324WithinHalfStepContext.internalEdges,
      r324WithinHalfInternalEdgeScaleProduct] using
      primitiveKernelDiff_le_prod_edgeScales_mul_majorant_offDiagonal
        ρ ctx.one_le_blockOrder ctx.internalEdges
        (fun j => budget.stopScale (ctx.internalSlot j))
        (fun j => data.certificate.scale_pos (ctx.internalSlot j))
        (fun j => data.certificate.memE (ctx.internalSlot j))
        (fun j => data.certificate.bound (ctx.internalSlot j))
        hprop u hu
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  refine (hM.const_mul Jscale).mono hJmeas.aestronglyMeasurable ?_
  filter_upwards [paperMeasure.ae_ne (0 : T4)] with u hu
  have hprod : 0 ≤ Jscale * M u :=
    (abs_nonneg (J u)).trans (hJoff u hu)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hprod] using hJoff u hu

/-- The terminal primitive phase with all genuine internal edge scales,
paid by the inserted majorant of (4.4).  This is the frequency-independent
analogue of `norm_integral_terminalPrimitiveKernelDiff_mul_..._le_scaled`;
the latter deliberately uses the Step-4 bound `|cos-1| ≤ 2`, whereas
Step 1 keeps the quadratic cosine gain.

The proof takes the modulus only after the signed primitive-pairing sum has
been integrated and the `E`-symmetry cancellation has been applied. -/
theorem
    paperDecay_mul_norm_integral_terminalPrimitiveKernelDiff_le_scaled_inserted
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (supportConstant primitiveConstant : ℝ)
    (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (hprop :
      ∀ H :
          Fin
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2 - 1) →
            T4 → ℝ,
        IsAdmissiblePrimitiveInput
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              H supportConstant primitiveConstant)
    (β : Z4) :
    paperSecondOrderModeDecay β *
        ‖∫ u,
          (primitiveKernelDiff ρ lam ε
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).internalEdges u :
            ℂ) *
            (charT4 (-β) u - 1)
          ∂paperMeasure‖ ≤
      r324WithinHalfInternalEdgeScaleProduct
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton)
          budget.stopScale *
        ((1 / 2 : ℝ) *
          (max 1 (supportConstant ^ 2) *
            ∫ z,
              primitiveInsertedMajorant
                primitiveConstant lam ε supportConstant
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2) z
              ∂paperMeasure)) := by
  let ctx :=
    data.geometry.trace.stopPrefix.headContext
      data.geometry.terminalData.terminal []
      data.geometry.stop_remaining_eq_singleton
  let J : T4 → ℝ :=
    primitiveKernelDiff ρ lam ε
      (residualBlockOrder data.geometry.terminalData.terminal.2)
      ctx.one_le_blockOrder ctx.internalEdges
  let Jscale : ℝ :=
    r324WithinHalfInternalEdgeScaleProduct ctx budget.stopScale
  let M : T4 → ℝ :=
    primitiveKernelMajorant primitiveConstant lam ε supportConstant
      (residualBlockOrder data.geometry.terminalData.terminal.2)
  let Mscaled : T4 → ℝ := fun u => Jscale * M u
  have hJscale : 0 < Jscale :=
    data.certificate.internalEdgeScaleProduct_pos
  have hMnonneg : ∀ u, 0 ≤ M u := by
    intro u
    exact primitiveKernelMajorant_nonneg hprimitive hlam
  have hM : Integrable M paperMeasure :=
    integrable_primitiveKernelMajorant primitiveConstant lam ε
      supportConstant
      (residualBlockOrder data.geometry.terminalData.terminal.2) hε
  have hJoff : ∀ u, u ≠ 0 → |J u| ≤ Jscale * M u := by
    intro u hu
    dsimp only [J, Jscale, M]
    simpa [ctx, R324WithinHalfResidualPrefix.headContext,
      R324WithinHalfStepContext.internalEdges,
      r324WithinHalfInternalEdgeScaleProduct] using
      primitiveKernelDiff_le_prod_edgeScales_mul_majorant_offDiagonal
        ρ ctx.one_le_blockOrder ctx.internalEdges
        (fun j => budget.stopScale (ctx.internalSlot j))
        (fun j => data.certificate.scale_pos (ctx.internalSlot j))
        (fun j => data.certificate.memE (ctx.internalSlot j))
        (fun j => data.certificate.bound (ctx.internalSlot j))
        hprop u hu
  have hrep :
      ∀ u, |offDiagonalRepresentative J u| ≤ Mscaled u := by
    intro u
    by_cases hu : u = 0
    · subst u
      rw [offDiagonalRepresentative_zero, abs_zero]
      exact mul_nonneg hJscale.le (hMnonneg 0)
    · rw [offDiagonalRepresentative_eq J hu]
      exact hJoff u hu
  have hweighted :
      Integrable (fun u => torusDistSq u * Mscaled u) paperMeasure := by
    have hscaled : Integrable Mscaled paperMeasure := by
      exact hM.const_mul Jscale
    exact integrable_torusDistSq_mul_of_integrable hscaled
  have hcosBound :
      ‖∫ u,
          ((offDiagonalRepresentative J u *
            (r324CharacterCos β u - 1) : ℝ) : ℂ)
          ∂paperMeasure‖ ≤
        ((1 / 2 : ℝ) * paperModeNormSq β) *
          ∫ u, torusDistSq u * Mscaled u ∂paperMeasure :=
    norm_integral_mul_r324CharacterCos_sub_one_le_of_abs_le
      β hrep hweighted
  have hJmeas : Measurable J := by
    dsimp only [J]
    exact measurable_primitiveKernelDiff ρ lam ε
      (residualBlockOrder data.geometry.terminalData.terminal.2)
      ctx.one_le_blockOrder ctx.internalEdges
      (fun j => by
        simpa only [ctx, R324WithinHalfStepContext.internalEdges,
          R324WithinHalfResidualPrefix.headContext] using
          data.certificate.measurable (ctx.internalSlot j))
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  have hJint : Integrable J paperMeasure := by
    refine (hM.const_mul Jscale).mono hJmeas.aestronglyMeasurable ?_
    filter_upwards [paperMeasure.ae_ne (0 : T4)] with u hu
    simpa only [Mscaled, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hJscale.le (hMnonneg u))] using hJoff u hu
  have hcos :
      Integrable (fun u => J u * (r324CharacterCos β u - 1))
        paperMeasure := by
    have hweight : Measurable fun u : T4 => r324CharacterCos β u - 1 :=
      (Complex.measurable_re.comp
        (continuous_charT4 β).measurable).sub measurable_const
    refine hJint.mul_bdd (c := 2) hweight.aestronglyMeasurable
      (.of_forall fun u => ?_)
    simpa only [Real.norm_eq_abs] using
      abs_r324CharacterCos_sub_one_le_two β u
  have hsin :
      Integrable (fun u => J u * r324CharacterSin (-β) u)
        paperMeasure := by
    have hweight : Measurable (r324CharacterSin (-β)) :=
      Complex.measurable_im.comp (continuous_charT4 (-β)).measurable
    refine hJint.mul_bdd (c := 1) hweight.aestronglyMeasurable
      (.of_forall fun u => ?_)
    unfold r324CharacterSin
    simpa only [Real.norm_eq_abs, norm_charT4] using
      Complex.abs_im_le_norm (charT4 (-β) u)
  have hphaseCos :
      (∫ u, (J u : ℂ) * (charT4 (-β) u - 1) ∂paperMeasure) =
        ∫ u, ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)
          ∂paperMeasure := by
    exact integral_terminalPrimitiveKernelDiff_mul_negCharacterSubOne_eq_cos
      ρ lam ε
      (residualBlockOrder data.geometry.terminalData.terminal.2)
      ctx.one_le_blockOrder ctx.internalEdges
      data.terminalInternalEdges_memE β hcos hsin
  have hcosRepresentative :
      (∫ u, ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)
          ∂paperMeasure) =
        ∫ u,
          ((offDiagonalRepresentative J u *
            (r324CharacterCos β u - 1) : ℝ) : ℂ)
          ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards [offDiagonalRepresentative_ae_eq J] with u hu
    rw [hu]
  have hMscaledIntegral :
      (∫ u, torusDistSq u * Mscaled u ∂paperMeasure) =
        Jscale * ∫ u, torusDistSq u * M u ∂paperMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    simp only [Mscaled]
    ring
  have hkey :
      ‖∫ u, (J u : ℂ) * (charT4 (-β) u - 1) ∂paperMeasure‖ ≤
        ((1 / 2 : ℝ) * paperModeNormSq β) *
          (Jscale * ∫ u, torusDistSq u * M u ∂paperMeasure) := by
    calc
      ‖∫ u, (J u : ℂ) * (charT4 (-β) u - 1) ∂paperMeasure‖ =
          ‖∫ u,
            ((offDiagonalRepresentative J u *
              (r324CharacterCos β u - 1) : ℝ) : ℂ)
            ∂paperMeasure‖ := by rw [hphaseCos, hcosRepresentative]
      _ ≤ ((1 / 2 : ℝ) * paperModeNormSq β) *
          ∫ u, torusDistSq u * Mscaled u ∂paperMeasure := hcosBound
      _ = ((1 / 2 : ℝ) * paperModeNormSq β) *
          (Jscale * ∫ u, torusDistSq u * M u ∂paperMeasure) := by
        rw [hMscaledIntegral]
  have hdistNonneg :
      0 ≤ ∫ u, torusDistSq u * M u ∂paperMeasure :=
    integral_nonneg fun u => mul_nonneg (torusDistSq_nonneg u) (hMnonneg u)
  have hbridge :=
    integral_torusDistSq_mul_primitiveKernelMajorant_le_max_one_sq_mul_integral_inserted
      primitiveConstant lam ε supportConstant
      (residualBlockOrder data.geometry.terminalData.terminal.2) hε
  have hmode := r324Step1_modeNormSq_mul_decay_le_one β
  change paperSecondOrderModeDecay β *
      ‖∫ u, (J u : ℂ) * (charT4 (-β) u - 1) ∂paperMeasure‖ ≤ _
  calc
    paperSecondOrderModeDecay β *
          ‖∫ u, (J u : ℂ) * (charT4 (-β) u - 1)
            ∂paperMeasure‖ ≤
        paperSecondOrderModeDecay β *
          (((1 / 2 : ℝ) * paperModeNormSq β) *
            (Jscale * ∫ u, torusDistSq u * M u ∂paperMeasure)) :=
      mul_le_mul_of_nonneg_left hkey (paperSecondOrderModeDecay_nonneg β)
    _ = (1 / 2 : ℝ) *
        ((paperModeNormSq β * paperSecondOrderModeDecay β) *
          (Jscale * ∫ u, torusDistSq u * M u ∂paperMeasure)) := by
      ring
    _ ≤ (1 / 2 : ℝ) *
        (1 * (Jscale * ∫ u, torusDistSq u * M u ∂paperMeasure)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hmode
          (mul_nonneg hJscale.le hdistNonneg)) (by norm_num)
    _ = Jscale *
        ((1 / 2 : ℝ) * ∫ u, torusDistSq u * M u ∂paperMeasure) := by
      ring
    _ ≤ Jscale *
        ((1 / 2 : ℝ) *
          (max 1 (supportConstant ^ 2) *
            ∫ z,
              primitiveInsertedMajorant primitiveConstant lam ε
                supportConstant
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2) z
              ∂paperMeasure)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbridge (by norm_num)) hJscale.le

/-- Fixed-endpoint Step 1 for the actual terminal trace.  The predecessor
is the paper's `G₀`; its certificate scale is charged exactly once.  The
terminal internal edge scales are charged by the preceding theorem, while
the outgoing Green difference is Fourier-integrated without a norm. -/
theorem fullPairingHalfTerminalEstimateInserted
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (x z : T4) (hxz : x ≠ z)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (supportConstant primitiveConstant : ℝ)
    (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (hprop :
      ∀ H :
          Fin
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2 - 1) →
            T4 → ℝ,
        IsAdmissiblePrimitiveInput
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              H supportConstant primitiveConstant)
    (β : Z4) :
    paperSecondOrderModeDecay β *
      ‖∫ u : T4,
          (((lamEps lam ε ^
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2) *
              (∫ v :
                  Fin
                      (2 * residualBlockOrder
                        data.geometry.terminalData.terminal.2 - 2) →
                    T4,
                data.geometry.terminalGroupedPrimitiveCore x
                  (primitiveAssemble
                    (residualBlockOrder
                      data.geometry.terminalData.terminal.2)
                    (data.geometry.trace.stopPrefix.headContext
                      data.geometry.terminalData.terminal []
                      data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                    z (z - u) v)
                ∂Measure.pi fun _ => paperMeasure)) : ℝ) : ℂ) *
            (charT4 (-β) u - 1)
          ∂paperMeasure‖ ≤
      (budget.stopScale
          (r324WithinHalfPredecessorSlot
            data.geometry.trace.stopPrefix.state
            data.geometry.terminalData.terminal) *
        invSqKer (x - z)) *
        (r324WithinHalfInternalEdgeScaleProduct
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton)
            budget.stopScale *
          ((1 / 2 : ℝ) *
            (max 1 (supportConstant ^ 2) *
              ∫ u,
                primitiveInsertedMajorant primitiveConstant lam ε
                  supportConstant
                  (residualBlockOrder
                    data.geometry.terminalData.terminal.2) u
                ∂paperMeasure))) := by
  let pred :=
    r324WithinHalfPredecessorSlot
      data.geometry.trace.stopPrefix.state
      data.geometry.terminalData.terminal
  let Jscale :=
    r324WithinHalfInternalEdgeScaleProduct
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton)
      budget.stopScale
  let B : ℝ :=
    (1 / 2 : ℝ) *
      (max 1 (supportConstant ^ 2) *
        ∫ u,
          primitiveInsertedMajorant primitiveConstant lam ε
            supportConstant
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) u
          ∂paperMeasure)
  have hint :
      ∀ (w : T4)
        (κB :
          {κB : PartialPairing
              (Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)}),
        Integrable
          (fun v :
              Fin
                  (2 * residualBlockOrder
                    data.geometry.terminalData.terminal.2 - 2) →
                T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2)
              κB.1
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).internalEdges
              (primitiveAssemble
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                z w v))
          (Measure.pi fun _ => paperMeasure) := by
    intro w κB
    exact data.integrable_terminalClosedIntegrand_section hε hε1 κB z w
  have hphase :
      paperSecondOrderModeDecay β *
        ‖∫ u,
          (primitiveKernelDiff ρ lam ε
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).internalEdges u :
            ℂ) * (charT4 (-β) u - 1)
          ∂paperMeasure‖ ≤ Jscale * B := by
    simpa only [Jscale, B] using
      data.paperDecay_mul_norm_integral_terminalPrimitiveKernelDiff_le_scaled_inserted
        hε supportConstant primitiveConstant hprimitive hlam hprop β
  have hpred :
      |data.geometry.trace.stopPrefix.state.edges pred (x - z)| ≤
        budget.stopScale pred * invSqKer (x - z) := by
    exact data.certificate.bound pred (x - z) (sub_ne_zero.mpr hxz)
  have hBnonneg : 0 ≤ B := by
    dsimp only [B]
    have hmax : 0 ≤ max 1 (supportConstant ^ 2) :=
      zero_le_one.trans (le_max_left _ _)
    have hintNonneg :
        0 ≤ ∫ u,
          primitiveInsertedMajorant primitiveConstant lam ε
            supportConstant
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) u
          ∂paperMeasure :=
      integral_nonneg fun u => primitiveInsertedMajorant_nonneg hprimitive hlam
    positivity
  have hJscale : 0 ≤ Jscale := by
    exact data.certificate.internalEdgeScaleProduct_pos.le
  rw [
    data.integral_lamEps_pow_terminalGroupedPrimitiveCore_gap_mul_negCharacterSubOne_eq
      x z hint β,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  change paperSecondOrderModeDecay β *
      (|data.geometry.trace.stopPrefix.state.edges pred (x - z)| * _) ≤
    (budget.stopScale pred * invSqKer (x - z)) * (Jscale * B)
  calc
    paperSecondOrderModeDecay β *
        (|data.geometry.trace.stopPrefix.state.edges pred (x - z)| *
          ‖∫ u,
            (primitiveKernelDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).internalEdges u :
              ℂ) * (charT4 (-β) u - 1)
            ∂paperMeasure‖) =
        |data.geometry.trace.stopPrefix.state.edges pred (x - z)| *
          (paperSecondOrderModeDecay β *
            ‖∫ u,
              (primitiveKernelDiff ρ lam ε
                  (residualBlockOrder
                    data.geometry.terminalData.terminal.2)
                  (data.geometry.trace.stopPrefix.headContext
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                  (data.geometry.trace.stopPrefix.headContext
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton).internalEdges u :
                ℂ) * (charT4 (-β) u - 1)
              ∂paperMeasure‖) := by ring
    _ ≤ |data.geometry.trace.stopPrefix.state.edges pred (x - z)| *
        (Jscale * B) :=
      mul_le_mul_of_nonneg_left hphase (abs_nonneg _)
    _ ≤ (budget.stopScale pred * invSqKer (x - z)) *
        (Jscale * B) :=
      mul_le_mul_of_nonneg_right hpred (mul_nonneg hJscale hBnonneg)

/-- Uniform Step-1 estimate for the *complete* terminal Fourier half, with
the two scale charges exposed exactly as they occur in the trace ledger.
This is (4.17) followed by the paper's quadratic cosine cancellation and
inserted-kernel majorant; no absolute value is taken before the signed
terminal primitive sum has been integrated. -/
theorem norm_terminalRawLocalFourierIntegral_le_insertedScaleLedger
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (supportConstant primitiveConstant : ℝ)
    (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (hprop :
      ∀ H :
          Fin
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2 - 1) →
            T4 → ℝ,
        IsAdmissiblePrimitiveInput
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              H supportConstant primitiveConstant)
    (alpha beta : Z4) :
    ‖data.terminalRawLocalFourierIntegral alpha beta‖ ≤
      r324PaperTorusMass *
        ((budget.stopScale
            (r324WithinHalfPredecessorSlot
              data.geometry.trace.stopPrefix.state
              data.geometry.terminalData.terminal) *
            ∫ z, invSqKer z ∂paperMeasure) *
          (r324WithinHalfInternalEdgeScaleProduct
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton)
              budget.stopScale *
            ((1 / 2 : ℝ) *
              (max 1 (supportConstant ^ 2) *
                ∫ z,
                  primitiveInsertedMajorant
                    primitiveConstant lam ε supportConstant
                    (residualBlockOrder
                      data.geometry.terminalData.terminal.2) z
                  ∂paperMeasure)))) := by
  let ctx :=
    data.geometry.trace.stopPrefix.headContext
      data.geometry.terminalData.terminal []
      data.geometry.stop_remaining_eq_singleton
  let pred :=
    r324WithinHalfPredecessorSlot
      data.geometry.trace.stopPrefix.state
      data.geometry.terminalData.terminal
  let G0 : T4 → ℝ :=
    data.geometry.trace.stopPrefix.state.edges pred
  let J : T4 → ℝ :=
    primitiveKernelDiff ρ lam ε
      (residualBlockOrder data.geometry.terminalData.terminal.2)
      ctx.one_le_blockOrder ctx.internalEdges
  let Jscale :=
    r324WithinHalfInternalEdgeScaleProduct ctx budget.stopScale
  let B : ℝ :=
    (1 / 2 : ℝ) *
      (max 1 (supportConstant ^ 2) *
        ∫ z,
          primitiveInsertedMajorant primitiveConstant lam ε
            supportConstant
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) z
          ∂paperMeasure)
  have hJint : Integrable J paperMeasure := by
    dsimp only [J]
    exact data.integrable_terminalPrimitiveKernelDiff_of_provider
      hε supportConstant primitiveConstant hprop
  have hJmem : MemEClassT4 J := by
    dsimp only [J]
    exact primitiveKernelDiff_memE ρ lam ε
      (residualBlockOrder data.geometry.terminalData.terminal.2)
      ctx.one_le_blockOrder ctx.internalEdges
      data.terminalInternalEdges_memE
  have hcos :
      Integrable (fun u => J u * (r324CharacterCos beta u - 1))
        paperMeasure := by
    have hweight : Measurable fun u : T4 =>
        r324CharacterCos beta u - 1 :=
      (Complex.measurable_re.comp
        (continuous_charT4 beta).measurable).sub measurable_const
    refine hJint.mul_bdd (c := 2) hweight.aestronglyMeasurable
      (.of_forall fun u => ?_)
    simpa only [Real.norm_eq_abs] using
      abs_r324CharacterCos_sub_one_le_two beta u
  have hsin :
      Integrable (fun u => J u * r324CharacterSin beta u)
        paperMeasure := by
    have hweight : Measurable (r324CharacterSin beta) :=
      Complex.measurable_im.comp (continuous_charT4 beta).measurable
    refine hJint.mul_bdd (c := 1) hweight.aestronglyMeasurable
      (.of_forall fun u => ?_)
    unfold r324CharacterSin
    simpa only [Real.norm_eq_abs, norm_charT4] using
      Complex.abs_im_le_norm (charT4 beta u)
  have hsinNeg :
      Integrable (fun u => J u * r324CharacterSin (-beta) u)
        paperMeasure := by
    have hweight : Measurable (r324CharacterSin (-beta)) :=
      Complex.measurable_im.comp (continuous_charT4 (-beta)).measurable
    refine hJint.mul_bdd (c := 1) hweight.aestronglyMeasurable
      (.of_forall fun u => ?_)
    unfold r324CharacterSin
    simpa only [Real.norm_eq_abs, norm_charT4] using
      Complex.abs_im_le_norm (charT4 (-beta) u)
  have hexact :=
    data.terminalRawLocalFourierIntegral_eq_step1IntegralWithIncoming
      hε hε1 (by simpa only [J, ctx] using hJint) alpha beta
  have hstep :
      ‖r324Step1IntegralWithIncoming G0 J alpha beta‖ ≤
        r324PaperTorusMass *
          ((budget.stopScale pred *
              ∫ z, invSqKer z ∂paperMeasure) *
            (paperSecondOrderModeDecay beta *
              ‖∫ u,
                ((J u * (r324CharacterCos beta u - 1) : ℝ) : ℂ)
                ∂paperMeasure‖)) := by
    exact r324Step1WithIncoming_norm_le
      (by exact data.certificate.measurable pred)
      (data.certificate.scale_pos pred).le
      (fun z hz => data.certificate.bound pred z hz)
      hJmem alpha beta hcos hsin
  have hphaseCos :
      (∫ u, (J u : ℂ) * (charT4 (-beta) u - 1)
          ∂paperMeasure) =
        ∫ u,
          ((J u * (r324CharacterCos beta u - 1) : ℝ) : ℂ)
          ∂paperMeasure := by
    exact integral_memEClass_mul_characterSubOne_eq_cos
      hJmem (-beta)
      (by simpa only [r324CharacterCos_neg_frequency] using hcos)
      hsinNeg |>.trans (by
        apply integral_congr_ae
        filter_upwards with u
        rw [r324CharacterCos_neg_frequency])
  have hphase :
      paperSecondOrderModeDecay beta *
          ‖∫ u,
            ((J u * (r324CharacterCos beta u - 1) : ℝ) : ℂ)
            ∂paperMeasure‖ ≤
        Jscale * B := by
    have h :=
      data.paperDecay_mul_norm_integral_terminalPrimitiveKernelDiff_le_scaled_inserted
        hε supportConstant primitiveConstant hprimitive hlam hprop beta
    rw [hphaseCos] at h
    simpa only [J, Jscale, B, ctx] using h
  have hincomingNonneg :
      0 ≤ budget.stopScale pred *
        ∫ z, invSqKer z ∂paperMeasure := by
    exact mul_nonneg (data.certificate.scale_pos pred).le
      (integral_nonneg invSqKer_nonneg)
  rw [hexact]
  exact hstep.trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hphase hincomingNonneg)
      r324PaperTorusMass_pos.le)

/-! ## Closing the literal trace scale ledger -/

private theorem initialFullHalfActiveScaleProduct_eq_pow
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q))) (A : ℝ) :
    (∏ _edge ∈
        ({0} ∪
          (r324InitialWithinHalfEdgeState (2 * q)).active.image
            r324InternalVertexEdgeSlot), A) =
      A ^ (2 * q + 1) := by
  have hslots := initial_activeEdgeSlots ρ lam ε κ
  change
    ({0} ∪
        (r324InitialWithinHalfEdgeState (2 * q)).active.image
          r324InternalVertexEdgeSlot : Finset (Fin (2 * q + 1))) =
      Finset.univ at hslots
  rw [hslots]
  simp

/-- The predecessor and all genuine internal terminal scales are no larger
than the complete active budget product.  The missing outgoing factor is
exactly the initial Green scale `A ≥ 1`. -/
theorem terminal_predecessor_mul_internalScale_le_closedForm
    (data : R324FullPairingBudgetTerminalAdapter budget) :
    budget.stopScale
          (r324WithinHalfPredecessorSlot
            data.geometry.trace.stopPrefix.state
            data.geometry.terminalData.terminal) *
        r324WithinHalfInternalEdgeScaleProduct
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton)
          budget.stopScale ≤
      A ^ (2 * q + 1) *
        (C * lam) ^
          (2 *
            (budget.terminalData.proper.map
              (fun step => residualBlockOrder step.2)).sum) *
        K ^ budget.terminalData.proper.length := by
  let res := data.geometry.trace.stopPrefix
  let head := data.geometry.terminalData.terminal
  let ctx :=
    res.headContext head []
      data.geometry.stop_remaining_eq_singleton
  let pred := r324WithinHalfPredecessorSlot res.state head
  let charge :=
    budget.stopScale pred *
      r324WithinHalfInternalEdgeScaleProduct ctx budget.stopScale
  have hout : budget.stopScale ctx.outgoingSlot = A := by
    exact data.reachable.outgoingScale_eq_base
      res rfl head [] data.geometry.stop_remaining_eq_singleton
  have hcharge : 0 ≤ charge := by
    exact mul_nonneg (data.certificate.scale_pos pred).le
      data.certificate.internalEdgeScaleProduct_pos.le
  have hactive :
      charge ≤
        ∏ edge ∈ res.activeEdgeSlots, budget.stopScale edge := by
    rw [data.terminal_activeEdgeScaleProduct_eq]
    dsimp only [charge, pred, ctx]
    rw [hout]
    exact le_mul_of_one_le_right hcharge budget.base_one_le
  have hclosed := data.activeEdgeScaleProduct_eq
  have hinitial :=
    initialFullHalfActiveScaleProduct_eq_pow
      ρ lam ε κ A
  rw [hinitial] at hclosed
  have hactiveEq :
      (∏ edge ∈ res.activeEdgeSlots, budget.stopScale edge) =
        A ^ (2 * q + 1) *
          (C * lam) ^
            (2 *
              (budget.terminalData.proper.map
                (fun step => residualBlockOrder step.2)).sum) *
          K ^ budget.terminalData.proper.length := by
    simpa only [res, R324WithinHalfResidualPrefix.activeEdgeSlots] using
      hclosed
  simpa only [charge, pred, ctx, res] using hactive.trans_eq hactiveEq

private theorem terminalBudgetMultiplier_le_finalEvenPower
    {q ell : ℕ} {A K D : ℝ}
    (hq : 1 ≤ q) (hell : ell ≤ q)
    (hA : 1 ≤ A) (hK : 0 < K) (hD : 0 ≤ D) :
    A ^ (2 * q + 1) * K ^ ell * D ≤
      (A ^ 2 * max 1 K * (D + 1)) ^ (2 * q) := by
  have hAexp : 2 * q + 1 ≤ 2 * (2 * q) := by omega
  have hApow : A ^ (2 * q + 1) ≤ (A ^ 2) ^ (2 * q) := by
    calc
      A ^ (2 * q + 1) ≤ A ^ (2 * (2 * q)) :=
        pow_le_pow_right₀ hA hAexp
      _ = (A ^ 2) ^ (2 * q) := by rw [pow_mul]
  have hell' : ell ≤ 2 * q := hell.trans (by omega)
  have hKpow : K ^ ell ≤ (max 1 K) ^ (2 * q) := by
    exact
      (pow_le_pow_left₀ hK.le (le_max_right 1 K) ell).trans
        (pow_le_pow_right₀ (le_max_left 1 K) hell')
  have hDpow : D ≤ (D + 1) ^ (2 * q) := by
    simpa using
      (mul_constant_le_absorbed_even_pow
        (base := (1 : ℝ)) (K := D) zero_le_one hD hq)
  calc
    A ^ (2 * q + 1) * K ^ ell * D ≤
        (A ^ 2) ^ (2 * q) *
          (max 1 K) ^ (2 * q) *
          (D + 1) ^ (2 * q) := by
      exact mul_le_mul
        (mul_le_mul hApow hKpow (pow_nonneg hK.le ell)
          (pow_nonneg (sq_nonneg A) _))
        hDpow hD
        (mul_nonneg
          (pow_nonneg (sq_nonneg A) _)
          (pow_nonneg (zero_le_one.trans (le_max_left 1 K)) _))
    _ = (A ^ 2 * max 1 K * (D + 1)) ^ (2 * q) := by
      rw [mul_pow, mul_pow]

/-- Public scalar ledger for reusing the complete full-half budget with a
different terminal Fourier calculation.  The Step 4(A) endpoint proof has
the same stop-scale and suffix multiplier as Step 1; only its terminal
factor `D` changes. -/
theorem terminalBudgetMultiplier_le_finalEvenPower_reusable
    {q ell : Nat} {A K D : Real}
    (hq : 1 <= q) (hell : ell <= q)
    (hA : 1 <= A) (hK : 0 < K) (hD : 0 <= D) :
    A ^ (2 * q + 1) * K ^ ell * D <=
      (A ^ 2 * max 1 K * (D + 1)) ^ (2 * q) :=
  terminalBudgetMultiplier_le_finalEvenPower hq hell hA hK hD

/-! ## Uniform complete-half producer -/

/-- **Paper Step 1, complete full-pairing half.**

For the canonical Proposition-4.1 trace, the complete endpoint-signature
half has the paper's uniform `(C λ)^(2q) / |log ε|` bound.  This theorem
contains the finite-fibre producer, every proper-prefix collapse, the
corrected incoming `G₀` form of (4.17), the terminal signed cancellation,
and the final scale/order absorption. -/
theorem exists_fullPairing_half_step1_bound
    (ρ : SmoothCutoff) :
    ∃ Cdet : ℝ, 0 < Cdet ∧
      ∀ (lam ε : ℝ) (q : ℕ)
        (κ : PartialPairing (Fin (2 * q))),
        0 < lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → q ≤ truncOrder ε →
        1 ≤ q → κ.IsFull →
        ∀ alpha beta : Z4,
          ‖(lamEps lam ε : ℂ) ^ (2 * q) *
              ∑ τ : ReductionEndpointFiberAt κ,
                deterministicFullHalfIntegral
                  ρ ε (2 * q) alpha beta τ.1‖ ≤
            (Cdet * lam) ^ (2 * q) / |Real.log ε| := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨K, hK, hlocal⟩ :=
    exists_r324WithinHalf_localBlockClosure hsupport
  obtain ⟨A, hA, hinitial⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate_one_le_uniform
  obtain ⟨Cball, Creg, hCball, hCreg, hmajorant⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  let Q : ℝ :=
    (1 / 2 : ℝ) * max 1 (supportConstant ^ 2)
  let M : ℝ := Cball * supportConstant ^ 2 + 2 * Creg
  let D : ℝ :=
    r324PaperTorusMass *
      (∫ z, invSqKer z ∂paperMeasure) * (Q * M)
  let multiplier : ℝ := A ^ 2 * max 1 K * (D + 1)
  let Cdet : ℝ := C * multiplier
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    exact mul_nonneg (by norm_num)
      (zero_le_one.trans (le_max_left 1 (supportConstant ^ 2)))
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg r324PaperTorusMass_pos.le
        (integral_nonneg invSqKer_nonneg))
      (mul_nonneg hQ hM)
  have hmultiplier : 0 < multiplier := by
    dsimp only [multiplier]
    have hApos : 0 < A := zero_lt_one.trans_le hA
    have hKmax : 0 < max 1 K := zero_lt_one.trans_le (le_max_left 1 K)
    have hDone : 0 < D + 1 := by linarith
    positivity
  refine ⟨Cdet, mul_pos hC hmultiplier, ?_⟩
  intro lam ε q κ hlam hε hε1 hlog htrunc hq hκ alpha beta
  let propProvider :
      R324WithinHalfProp41Provider
        ρ C lam ε supportConstant κ := by
    intro res head tail hremaining H hH
    have hheadSchedule : head ∈ r322AnalyticSchedule κ :=
      (res.headContext head tail hremaining).step_mem_schedule
    have hheadMapped :
        head.2 ∈ (r322AnalyticSchedule κ).map Prod.snd :=
      List.mem_map.mpr ⟨head, hheadSchedule, rfl⟩
    have hheadExtraction : head.2 ∈ extractionBlocks κ :=
      (r322AnalyticSchedule_blocks_perm_extractionBlocks κ)
        |>.mem_iff.mp hheadMapped
    exact hprop lam ε
      (residualBlockOrder head.2)
      (res.headContext head tail hremaining).one_le_blockOrder
      H hlam hε hε1
      (extractionBlockOrder_le_truncOrder
        κ hκ hheadExtraction ε htrunc)
      hH
  let localProvider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κ := by
    intro res head tail hremaining scale hcertificate
    exact hlocal ρ C lam ε (2 * q) κ
      res head tail hremaining scale hcertificate
      hC hlam hε hε1 hlog
      (fun H hH =>
        propProvider res head tail hremaining H hH)
  let budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        ρ C lam ε K A κ :=
    r324WithinHalfBudgetLocalBlockProvider_of_localBlockProvider
      hA localProvider
  obtain ⟨budget⟩ :=
    R324FullPairingBudgetStopTrace.exists_of_initial_certificate
      hq hκ hA budgetProvider (hinitial (2 * q))
  obtain ⟨geometry⟩ :=
    R324FullPairingStopTraceAssembly.exists_of_initial_certificate
      hq hκ hε hε1 localProvider (hinitial (2 * q))
  let data : R324FullPairingBudgetTerminalAdapter budget :=
    R324FullPairingBudgetTerminalAdapter.ofAssembly geometry
  let p : ℕ :=
    residualBlockOrder data.geometry.terminalData.terminal.2
  let s : ℕ :=
    (budget.terminalData.proper.map
      (fun step => residualBlockOrder step.2)).sum
  let ell : ℕ := budget.terminalData.proper.length
  have hp : 1 ≤ p := by
    dsimp only [p]
    exact data.geometry.trace.stopPrefix.head_one_le_blockOrder
      data.geometry.terminalData.terminal []
      data.geometry.stop_remaining_eq_singleton
  have hledger : s + p = q := by
    have hpEq : p =
        residualBlockOrder budget.terminalData.terminal.2 := by
      dsimp only [p]
      rw [data.terminalData_eq]
    simpa only [s, hpEq] using
      budget.terminalData.sum_properBlockOrders_add_terminal hκ
  have hpq : p ≤ q := by omega
  have hptrunc : p ≤ truncOrder ε := hpq.trans htrunc
  have hell : ell ≤ q := by
    have hschedule := length_r322AnalyticSchedule_le_of_full κ hκ
    rw [budget.terminalData.schedule_eq, List.length_append] at hschedule
    simp only [List.length_singleton] at hschedule
    dsimp only [ell]
    omega
  have hpropTerminal :
      ∀ H : Fin (2 * p - 1) → T4 → ℝ,
        IsAdmissiblePrimitiveInput p H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε p
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε p
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                H) ∧
            PrimitiveKernelBounds ρ lam ε p
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              H supportConstant C := by
    intro H hH
    exact hprop lam ε p
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
      H hlam hε hε1 hptrunc hH
  have hterminal :=
    data.norm_terminalRawLocalFourierIntegral_le_insertedScaleLedger
      hε hε1 supportConstant C hC.le hlam.le
      (by simpa only [p] using hpropTerminal) alpha beta
  have hproducer :=
    data.lamEps_pow_sum_deterministicFullHalfIntegral_eq_terminalRawLocal
      hκ hε hε1 alpha beta
  have hscale := data.terminal_predecessor_mul_internalScale_le_closedForm
  have hI :
      (∫ z,
          primitiveInsertedMajorant C lam ε supportConstant p z
          ∂paperMeasure) ≤
        (C * lam) ^ (2 * p) * (M / |Real.log ε|) := by
    simpa only [M] using
      hmajorant C lam ε supportConstant p
        hε hε1 hsupport hlog
  have hI0 :
      0 ≤ ∫ z,
        primitiveInsertedMajorant C lam ε supportConstant p z
        ∂paperMeasure :=
    integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg hC.le hlam.le
  have hlogPos : 0 < |Real.log ε| := zero_lt_one.trans_le hlog
  have hmult := terminalBudgetMultiplier_le_finalEvenPower
    hq hell hA hK hD
  have hpow :
      (C * lam) ^ (2 * s) * (C * lam) ^ (2 * p) =
        (C * lam) ^ (2 * q) := by
    rw [← pow_add]
    congr 1
    omega
  have hscaled :
      ‖data.terminalRawLocalFourierIntegral alpha beta‖ ≤
        ((C * lam) ^ (2 * q) *
          (A ^ (2 * q + 1) * K ^ ell * D)) /
            |Real.log ε| := by
    calc
      ‖data.terminalRawLocalFourierIntegral alpha beta‖ ≤
          r324PaperTorusMass *
            ((budget.stopScale
                (r324WithinHalfPredecessorSlot
                  data.geometry.trace.stopPrefix.state
                  data.geometry.terminalData.terminal) *
                ∫ z, invSqKer z ∂paperMeasure) *
              (r324WithinHalfInternalEdgeScaleProduct
                  (data.geometry.trace.stopPrefix.headContext
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton)
                  budget.stopScale *
                (Q *
                  ∫ z,
                    primitiveInsertedMajorant C lam ε
                      supportConstant p z
                    ∂paperMeasure))) := by
        simpa only [Q, p, mul_assoc] using hterminal
      _ ≤ r324PaperTorusMass *
            (((A ^ (2 * q + 1) *
                  (C * lam) ^ (2 * s) * K ^ ell) *
                ∫ z, invSqKer z ∂paperMeasure) *
              (Q *
                ∫ z,
                  primitiveInsertedMajorant C lam ε
                    supportConstant p z
                  ∂paperMeasure)) := by
        have hIQ : 0 ≤ Q *
            ∫ z,
              primitiveInsertedMajorant C lam ε supportConstant p z
              ∂paperMeasure := mul_nonneg hQ hI0
        have hinv : 0 ≤ ∫ z, invSqKer z ∂paperMeasure :=
          integral_nonneg invSqKer_nonneg
        have hb := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (by simpa only [s, ell] using hscale) hinv)
            hIQ)
          r324PaperTorusMass_pos.le
        have hreorder :
            (budget.stopScale
                (r324WithinHalfPredecessorSlot
                  data.geometry.trace.stopPrefix.state
                  data.geometry.terminalData.terminal) *
                ∫ z, invSqKer z ∂paperMeasure) *
              (r324WithinHalfInternalEdgeScaleProduct
                  (data.geometry.trace.stopPrefix.headContext
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton)
                  budget.stopScale *
                (Q *
                  ∫ z,
                    primitiveInsertedMajorant C lam ε
                      supportConstant p z
                    ∂paperMeasure)) =
              ((budget.stopScale
                    (r324WithinHalfPredecessorSlot
                      data.geometry.trace.stopPrefix.state
                      data.geometry.terminalData.terminal) *
                  r324WithinHalfInternalEdgeScaleProduct
                    (data.geometry.trace.stopPrefix.headContext
                      data.geometry.terminalData.terminal []
                      data.geometry.stop_remaining_eq_singleton)
                    budget.stopScale) *
                ∫ z, invSqKer z ∂paperMeasure) *
                  (Q *
                    ∫ z,
                      primitiveInsertedMajorant C lam ε
                        supportConstant p z
                      ∂paperMeasure) := by
          ring
        rw [hreorder]
        exact hb
      _ ≤ r324PaperTorusMass *
            (((A ^ (2 * q + 1) *
                  (C * lam) ^ (2 * s) * K ^ ell) *
                ∫ z, invSqKer z ∂paperMeasure) *
              (Q * ((C * lam) ^ (2 * p) *
                (M / |Real.log ε|)))) := by
        have houter0 : 0 ≤
            (A ^ (2 * q + 1) * (C * lam) ^ (2 * s) * K ^ ell) *
              ∫ z, invSqKer z ∂paperMeasure := by
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg (pow_nonneg (zero_le_one.trans hA) _)
                (pow_nonneg (mul_nonneg hC.le hlam.le) _))
              (pow_nonneg hK.le _))
            (integral_nonneg invSqKer_nonneg)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hI hQ) houter0)
          r324PaperTorusMass_pos.le
      _ = ((C * lam) ^ (2 * q) *
            (A ^ (2 * q + 1) * K ^ ell * D)) /
              |Real.log ε| := by
        rw [← hpow]
        dsimp only [D]
        field_simp [hlogPos.ne']
  have hnumerator :
      (C * lam) ^ (2 * q) *
          (A ^ (2 * q + 1) * K ^ ell * D) ≤
        (Cdet * lam) ^ (2 * q) := by
    calc
      (C * lam) ^ (2 * q) *
            (A ^ (2 * q + 1) * K ^ ell * D) ≤
          (C * lam) ^ (2 * q) * multiplier ^ (2 * q) :=
        mul_le_mul_of_nonneg_left hmult
          (pow_nonneg (mul_nonneg hC.le hlam.le) _)
      _ = (Cdet * lam) ^ (2 * q) := by
        dsimp only [Cdet, multiplier]
        rw [← mul_pow]
        congr 1
        ring
  rw [hproducer]
  exact hscaled.trans
    (div_le_div_of_nonneg_right hnumerator hlogPos.le)

end R324FullPairingBudgetTerminalAdapter

end R324WithinHalfResidualPrefix

/-! ## Direct closure of the full/full refined fibre -/

/-- **Paper Step 1, full/full refined fibre.**

The exact finite-fibre product factorization is combined with the two
unconditional normalized half estimates above.  Fullness supplies the
even-order witness `m = 2q`; the paper range `1 ≤ m` excludes the empty
`q = 0` trace.  The product has two logarithmic gains, one of which is
discarded using `1 ≤ |log ε|`, and the remaining gain is exactly the
integrated inserted-majorant lower bound.

The statement includes the degenerate coupling `lam = 0`, so downstream
full/full routing needs no separate analytic interface. -/
theorem exists_fullFull_refined_bound_of_normalizedStep1
    (ρ : SmoothCutoff) :
    ∃ primitiveConstant : ℝ, 0 < primitiveConstant ∧
      ∀ (lam ε : ℝ) (m : ℕ) (alpha beta : Z4),
        0 ≤ lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → 1 ≤ m → m ≤ truncOrder ε →
        ∀ {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
          (e0 : MomentContraction m),
          e0 ∈ momentRefinedContractionFiber m s r →
          e0.1.IsFull → e0.2.1.IsFull →
          |lamEps lam ε| ^ (2 * m) *
              ‖momentRefinedDeterministicTermSum
                ρ ε m alpha beta s r‖ ≤
            ∫ z,
              primitiveInsertedMajorant
                primitiveConstant lam ε 1 m z
              ∂paperMeasure := by
  obtain ⟨Cdet, hCdet, hhalf⟩ :=
    R324WithinHalfResidualPrefix.R324FullPairingBudgetTerminalAdapter.exists_fullPairing_half_step1_bound
      ρ
  refine ⟨Cdet, hCdet, ?_⟩
  intro lam ε m alpha beta hlam hε hε1 hlog hm hmtrunc
    s r e0 he0 hp hmFull
  rcases hlam.eq_or_lt with hlamZero | hlamPos
  · subst lam
    have htwoM : 2 * m ≠ 0 := by omega
    have hweight : |lamEps 0 ε| ^ (2 * m) = 0 := by
      simp only [lamEps, zero_div, abs_zero, zero_pow htwoM]
    rw [hweight, zero_mul]
    exact integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg hCdet.le (le_refl 0)
  · obtain ⟨q, hmq⟩ := hp.exists_fin_order_eq_two_mul
    subst m
    have hq : 1 ≤ q := by omega
    have hqtrunc : q ≤ truncOrder ε := by omega
    let leftHalf : ℂ :=
      ∑ kp : ReductionEndpointFiberAt e0.1,
        deterministicFullHalfIntegral
          ρ ε (2 * q) alpha beta kp.1
    let rightHalf : ℂ :=
      ∑ km : ReductionEndpointFiberAt e0.2.1,
        deterministicFullHalfIntegral
          ρ ε (2 * q) (-alpha) (-beta) km.1
    have hleft :
        ‖(lamEps lam ε : ℂ) ^ (2 * q) * leftHalf‖ ≤
          (Cdet * lam) ^ (2 * q) / |Real.log ε| := by
      simpa only [leftHalf] using
        hhalf lam ε q e0.1 hlamPos hε hε1 hlog hqtrunc hq hp
          alpha beta
    have hright :
        ‖(lamEps lam ε : ℂ) ^ (2 * q) * rightHalf‖ ≤
          (Cdet * lam) ^ (2 * q) / |Real.log ε| := by
      simpa only [rightHalf] using
        hhalf lam ε q e0.2.1 hlamPos hε hε1 hlog hqtrunc hq hmFull
          (-alpha) (-beta)
    have hlogPos : 0 < |Real.log ε| := one_pos.trans_le hlog
    have hbase : 0 ≤ (Cdet * lam) ^ (2 * q) :=
      pow_nonneg (mul_nonneg hCdet.le hlamPos.le) _
    have hhalfRhs :
        0 ≤ (Cdet * lam) ^ (2 * q) / |Real.log ε| :=
      div_nonneg hbase hlogPos.le
    have hproduct :
        ‖(lamEps lam ε : ℂ) ^ (2 * q) * leftHalf‖ *
            ‖(lamEps lam ε : ℂ) ^ (2 * q) * rightHalf‖ ≤
          ((Cdet * lam) ^ (2 * q) / |Real.log ε|) ^ 2 := by
      calc
        ‖(lamEps lam ε : ℂ) ^ (2 * q) * leftHalf‖ *
              ‖(lamEps lam ε : ℂ) ^ (2 * q) * rightHalf‖ ≤
            ((Cdet * lam) ^ (2 * q) / |Real.log ε|) *
              ((Cdet * lam) ^ (2 * q) / |Real.log ε|) :=
          mul_le_mul hleft hright (norm_nonneg _) hhalfRhs
        _ = ((Cdet * lam) ^ (2 * q) / |Real.log ε|) ^ 2 := by
          ring
    have hsquareToSingle :
        ((Cdet * lam) ^ (2 * q) / |Real.log ε|) ^ 2 ≤
          (Cdet * lam) ^ (2 * (2 * q)) /
            |Real.log ε| := by
      have hpow :
          ((Cdet * lam) ^ (2 * q)) ^ 2 =
            (Cdet * lam) ^ (2 * (2 * q)) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [div_pow, hpow]
      have hlogSq :
          |Real.log ε| ≤ |Real.log ε| ^ 2 := by
        nlinarith [hlog]
      exact div_le_div_of_nonneg_left
        (pow_nonneg (mul_nonneg hCdet.le hlamPos.le) (2 * (2 * q)))
        hlogPos hlogSq
    have hlower :=
      le_integral_primitiveInsertedMajorant
        Cdet lam ε 1 (2 * q) hε hε1 one_pos
    have hlower' :
        (Cdet * lam) ^ (2 * (2 * q)) /
            |Real.log ε| ≤
          ∫ z,
            primitiveInsertedMajorant Cdet lam ε 1 (2 * q) z
            ∂paperMeasure := by
      change
        (Cdet * lam) ^ (2 * (2 * q)) *
            |Real.log ε|⁻¹ ≤ _
      simpa using hlower
    calc
      |lamEps lam ε| ^ (2 * (2 * q)) *
            ‖momentRefinedDeterministicTermSum
              ρ ε (2 * q) alpha beta s r‖ =
          ‖(lamEps lam ε : ℂ) ^ (2 * q) * leftHalf‖ *
            ‖(lamEps lam ε : ℂ) ^ (2 * q) * rightHalf‖ := by
        simpa only [leftHalf, rightHalf] using
          norm_weighted_momentRefinedDeterministicTermSum_eq_fullFull_product
            ρ hε hε1 lam (2 * q) alpha beta e0 he0 hp hmFull
      _ ≤ ((Cdet * lam) ^ (2 * q) /
            |Real.log ε|) ^ 2 := hproduct
      _ ≤ (Cdet * lam) ^ (2 * (2 * q)) /
            |Real.log ε| := hsquareToSingle
      _ ≤ ∫ z,
            primitiveInsertedMajorant Cdet lam ε 1 (2 * q) z
            ∂paperMeasure := hlower'

/-- **Paper Step 1, full/full refined fibre at an arbitrary positive
support constant.**

The loss `supportConstant² / min supportConstant 1⁴` in the quantitative
inserted-majorant lower bound is independent of the order.  Enlarging the
primitive constant by that loss absorbs it uniformly because `m ≥ 1`.
No new reduction interface is introduced. -/
theorem exists_fullFull_refined_bound_of_normalizedStep1_at_support
    (ρ : SmoothCutoff) {supportConstant : ℝ}
    (hsupport : 0 < supportConstant) :
    ∃ primitiveConstant : ℝ, 0 < primitiveConstant ∧
      ∀ (lam ε : ℝ) (m : ℕ) (alpha beta : Z4),
        0 ≤ lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| → 1 ≤ m → m ≤ truncOrder ε →
        ∀ {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
          (e0 : MomentContraction m),
          e0 ∈ momentRefinedContractionFiber m s r →
          e0.1.IsFull → e0.2.1.IsFull →
          |lamEps lam ε| ^ (2 * m) *
              ‖momentRefinedDeterministicTermSum
                ρ ε m alpha beta s r‖ ≤
            ∫ z,
              primitiveInsertedMajorant
                primitiveConstant lam ε supportConstant m z
              ∂paperMeasure := by
  obtain ⟨Cdet, hCdet, hhalf⟩ :=
    R324WithinHalfResidualPrefix.R324FullPairingBudgetTerminalAdapter.exists_fullPairing_half_step1_bound
      ρ
  let supportLoss : ℝ :=
    supportConstant ^ 2 / min supportConstant 1 ^ 4
  have hsupportLossOne : 1 ≤ supportLoss := by
    dsimp only [supportLoss]
    rcases le_total supportConstant 1 with hs | hs
    · rw [min_eq_left hs, one_le_div (pow_pos hsupport 4)]
      have hs2 : supportConstant ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg supportConstant,
          mul_self_le_mul_self (le_of_lt hsupport) hs]
      calc
        supportConstant ^ 4 =
            supportConstant ^ 2 * supportConstant ^ 2 := by ring
        _ ≤ supportConstant ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hs2 (sq_nonneg supportConstant)
        _ = supportConstant ^ 2 := by ring
    · rw [min_eq_right hs, one_pow, div_one]
      exact one_le_pow₀ hs
  have hsupportLoss : 0 < supportLoss :=
    one_pos.trans_le hsupportLossOne
  let primitiveConstant : ℝ := Cdet * supportLoss
  have hprimitiveConstant : 0 < primitiveConstant := by
    dsimp only [primitiveConstant]
    exact mul_pos hCdet hsupportLoss
  refine ⟨primitiveConstant, hprimitiveConstant, ?_⟩
  intro lam ε m alpha beta hlam hε hε1 hlog hm hmtrunc
    s r e0 he0 hp hmFull
  rcases hlam.eq_or_lt with hlamZero | hlamPos
  · subst lam
    have htwoM : 2 * m ≠ 0 := by omega
    have hweight : |lamEps 0 ε| ^ (2 * m) = 0 := by
      simp only [lamEps, zero_div, abs_zero, zero_pow htwoM]
    rw [hweight, zero_mul]
    exact integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg hprimitiveConstant.le (le_refl 0)
  · obtain ⟨q, hmq⟩ := hp.exists_fin_order_eq_two_mul
    subst m
    have hq : 1 ≤ q := by omega
    have hqtrunc : q ≤ truncOrder ε := by omega
    let leftHalf : ℂ :=
      ∑ kp : ReductionEndpointFiberAt e0.1,
        deterministicFullHalfIntegral
          ρ ε (2 * q) alpha beta kp.1
    let rightHalf : ℂ :=
      ∑ km : ReductionEndpointFiberAt e0.2.1,
        deterministicFullHalfIntegral
          ρ ε (2 * q) (-alpha) (-beta) km.1
    have hleft :
        ‖(lamEps lam ε : ℂ) ^ (2 * q) * leftHalf‖ ≤
          (Cdet * lam) ^ (2 * q) / |Real.log ε| := by
      simpa only [leftHalf] using
        hhalf lam ε q e0.1 hlamPos hε hε1 hlog hqtrunc hq hp
          alpha beta
    have hright :
        ‖(lamEps lam ε : ℂ) ^ (2 * q) * rightHalf‖ ≤
          (Cdet * lam) ^ (2 * q) / |Real.log ε| := by
      simpa only [rightHalf] using
        hhalf lam ε q e0.2.1 hlamPos hε hε1 hlog hqtrunc hq hmFull
          (-alpha) (-beta)
    have hlogPos : 0 < |Real.log ε| := one_pos.trans_le hlog
    have hbase : 0 ≤ (Cdet * lam) ^ (2 * q) :=
      pow_nonneg (mul_nonneg hCdet.le hlamPos.le) _
    have hhalfRhs :
        0 ≤ (Cdet * lam) ^ (2 * q) / |Real.log ε| :=
      div_nonneg hbase hlogPos.le
    have hproduct :
        ‖(lamEps lam ε : ℂ) ^ (2 * q) * leftHalf‖ *
            ‖(lamEps lam ε : ℂ) ^ (2 * q) * rightHalf‖ ≤
          ((Cdet * lam) ^ (2 * q) / |Real.log ε|) ^ 2 := by
      calc
        ‖(lamEps lam ε : ℂ) ^ (2 * q) * leftHalf‖ *
              ‖(lamEps lam ε : ℂ) ^ (2 * q) * rightHalf‖ ≤
            ((Cdet * lam) ^ (2 * q) / |Real.log ε|) *
              ((Cdet * lam) ^ (2 * q) / |Real.log ε|) :=
          mul_le_mul hleft hright (norm_nonneg _) hhalfRhs
        _ = ((Cdet * lam) ^ (2 * q) / |Real.log ε|) ^ 2 := by
          ring
    have hsquareToSingle :
        ((Cdet * lam) ^ (2 * q) / |Real.log ε|) ^ 2 ≤
          (Cdet * lam) ^ (2 * (2 * q)) /
            |Real.log ε| := by
      have hpow :
          ((Cdet * lam) ^ (2 * q)) ^ 2 =
            (Cdet * lam) ^ (2 * (2 * q)) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [div_pow, hpow]
      have hlogSq :
          |Real.log ε| ≤ |Real.log ε| ^ 2 := by
        nlinarith [hlog]
      exact div_le_div_of_nonneg_left
        (pow_nonneg (mul_nonneg hCdet.le hlamPos.le) (2 * (2 * q)))
        hlogPos hlogSq
    have hLossPow :
        supportLoss ≤ supportLoss ^ (2 * (2 * q)) := by
      calc
        supportLoss = supportLoss ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ supportLoss ^ (2 * (2 * q)) :=
          pow_le_pow_right₀ hsupportLossOne (by omega)
    have hweightedLoss :
        (Cdet * lam) ^ (2 * (2 * q)) * supportLoss ≤
          (primitiveConstant * lam) ^ (2 * (2 * q)) := by
      calc
        (Cdet * lam) ^ (2 * (2 * q)) * supportLoss ≤
            (Cdet * lam) ^ (2 * (2 * q)) *
              supportLoss ^ (2 * (2 * q)) :=
          mul_le_mul_of_nonneg_left hLossPow
            (pow_nonneg (mul_nonneg hCdet.le hlamPos.le) _)
        _ = (primitiveConstant * lam) ^ (2 * (2 * q)) := by
          dsimp only [primitiveConstant]
          rw [← mul_pow]
          congr 1
          ring
    have hscalarToSupport :
        (Cdet * lam) ^ (2 * (2 * q)) / |Real.log ε| ≤
          (primitiveConstant * lam) ^ (2 * (2 * q)) *
            (min supportConstant 1 ^ 4 /
              (supportConstant ^ 2 * |Real.log ε|)) := by
      have hden : 0 < supportLoss * |Real.log ε| :=
        mul_pos hsupportLoss hlogPos
      have hdiv :=
        div_le_div_of_nonneg_right hweightedLoss hden.le
      have hsupportNe : supportConstant ≠ 0 := hsupport.ne'
      have hminPos : 0 < min supportConstant 1 :=
        lt_min hsupport one_pos
      have hminNe : min supportConstant 1 ≠ 0 := hminPos.ne'
      have hleftEq :
          ((Cdet * lam) ^ (2 * (2 * q)) * supportLoss) /
              (supportLoss * |Real.log ε|) =
            (Cdet * lam) ^ (2 * (2 * q)) /
              |Real.log ε| := by
        field_simp [hsupportLoss.ne', hlogPos.ne']
      have hrightEq :
          (primitiveConstant * lam) ^ (2 * (2 * q)) /
              (supportLoss * |Real.log ε|) =
            (primitiveConstant * lam) ^ (2 * (2 * q)) *
              (min supportConstant 1 ^ 4 /
                (supportConstant ^ 2 * |Real.log ε|)) := by
        dsimp only [supportLoss]
        field_simp [hsupportNe, hminNe, hlogPos.ne']
      rwa [hleftEq, hrightEq] at hdiv
    have hlower :=
      le_integral_primitiveInsertedMajorant
        primitiveConstant lam ε supportConstant (2 * q)
        hε hε1 hsupport
    calc
      |lamEps lam ε| ^ (2 * (2 * q)) *
            ‖momentRefinedDeterministicTermSum
              ρ ε (2 * q) alpha beta s r‖ =
          ‖(lamEps lam ε : ℂ) ^ (2 * q) * leftHalf‖ *
            ‖(lamEps lam ε : ℂ) ^ (2 * q) * rightHalf‖ := by
        simpa only [leftHalf, rightHalf] using
          norm_weighted_momentRefinedDeterministicTermSum_eq_fullFull_product
            ρ hε hε1 lam (2 * q) alpha beta e0 he0 hp hmFull
      _ ≤ ((Cdet * lam) ^ (2 * q) /
            |Real.log ε|) ^ 2 := hproduct
      _ ≤ (Cdet * lam) ^ (2 * (2 * q)) /
            |Real.log ε| := hsquareToSingle
      _ ≤ (primitiveConstant * lam) ^ (2 * (2 * q)) *
            (min supportConstant 1 ^ 4 /
              (supportConstant ^ 2 * |Real.log ε|)) :=
        hscalarToSupport
      _ ≤ ∫ z,
            primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant (2 * q) z
            ∂paperMeasure := hlower

end

end Anderson4D
