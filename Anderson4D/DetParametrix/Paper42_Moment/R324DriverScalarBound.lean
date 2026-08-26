import Anderson4D.DetParametrix.Paper42_Moment.R324DriverRootInstantiation
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalStep4HeadBound
import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitiveIterationClosure

/-!
# Scalar norm bound for the alternating-driver endgame

The driver root instantiation transports the weighted refined physical
integral to the driver-terminal phased density carrying the accumulated
multiplier.  This module turns that transported identity into scalar
norm estimates:

* a per-stop bound for the collapsed-head factor from the ordinary
  Proposition 4.1 charge, packaged once as a uniform head-collapse
  budget;
* the multiplicative bound for the driver multiplier, proved by the same
  strong recursion on the remaining list that built the driver;
* the unconditional scalarization of the transported identity, with the
  multiplier norm pulled out of the root integral;
* the constructor discharging the integrated residual-refined interface
  from a per-fibre scalar bound.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The paper's Euclidean second-order bracket never exceeds one. -/
theorem paperSecondOrderModeDecay_le_one (k : Z4) :
    paperSecondOrderModeDecay k ≤ 1 := by
  have h0 : 0 ≤ paperModeNormSq k := by
    unfold paperModeNormSq
    positivity
  unfold paperSecondOrderModeDecay
  calc
    (1 + paperModeNormSq k)⁻¹ ≤ (1 : ℝ)⁻¹ :=
      inv_anti₀ one_pos (by linarith)
    _ = 1 := inv_one

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-! ## Per-stop bound for the collapsed-head factor -/

/-- **Per-stop factor bound.**  One collapsed-head factor is one paper
second-order decay times one primitive Step-4 defect; the decay is at
most one and the defect carries the ordinary Proposition 4.1 charge. -/
theorem norm_incomingExceptionalHeadCollapseFactor_le_two_mul
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε)
    (hGmeas :
      ∀ j, Measurable
        ((res.headContext head tail hremaining).internalEdges j))
    (hG :
      ∀ j, MemEClassT4
        ((res.headContext head tail hremaining).internalEdges j))
    (hbound :
      PrimitiveKernelBounds ρ lam ε
        (residualBlockOrder head.2)
        (res.headContext head tail hremaining).one_le_blockOrder
        (res.headContext head tail hremaining).internalEdges
        supportConstant primitiveConstant)
    (k : Z4) :
    ‖res.incomingExceptionalHeadCollapseFactor
        head tail hremaining k‖ ≤
      2 *
        ∫ u : T4,
          primitiveKernelMajorant
            primitiveConstant lam ε supportConstant
            (residualBlockOrder head.2) u
          ∂paperMeasure := by
  have hdefect :=
    norm_incomingExceptionalPrimitiveDefect_le_two_mul_of_bounds
      ρ lam ε (residualBlockOrder head.2)
      (res.headContext head tail hremaining).one_le_blockOrder
      (res.headContext head tail hremaining).internalEdges
      hGmeas hG supportConstant primitiveConstant hε hbound k
  have hdecay :
      ‖((paperSecondOrderModeDecay k : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (paperSecondOrderModeDecay_nonneg k)]
    exact paperSecondOrderModeDecay_le_one k
  unfold incomingExceptionalHeadCollapseFactor
  rw [norm_mul]
  have h :=
    mul_le_mul hdecay hdefect (norm_nonneg _) zero_le_one
  rw [one_mul] at h
  exact h

/-! ## The uniform head-collapse budget -/

/-- Uniform per-stop budget for the alternation: every reachable residual
prefix with a literal remaining head has its collapsed-head factor bounded
by `B`. -/
def R324WithinHalfHeadCollapseBudget
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (pairing : PartialPairing (Fin m))
    (k : Z4) (B : ℝ) : Prop :=
  ∀ (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail),
    ‖res.incomingExceptionalHeadCollapseFactor
        head tail hremaining k‖ ≤ B

/-- Packaged discharge of the uniform budget: pointwise Proposition 4.1
kernel bounds at every reachable head, plus one uniform bound for the
order-indexed majorant integrals. -/
theorem r324WithinHalfHeadCollapseBudget_of_kernelBounds
    (supportConstant primitiveConstant B : ℝ)
    (hε : 0 < ε)
    (huniform :
      ∀ (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
        (head : R322ExtractionStep m)
        (tail : List (R322ExtractionStep m))
        (hremaining : res.remaining = head :: tail),
        (∀ j, Measurable
          ((res.headContext head tail hremaining).internalEdges j)) ∧
        (∀ j, MemEClassT4
          ((res.headContext head tail hremaining).internalEdges j)) ∧
        PrimitiveKernelBounds ρ lam ε
          (residualBlockOrder head.2)
          (res.headContext head tail hremaining).one_le_blockOrder
          (res.headContext head tail hremaining).internalEdges
          supportConstant primitiveConstant)
    (hmaj :
      ∀ n : ℕ, 1 ≤ n →
        2 *
            ∫ u : T4,
              primitiveKernelMajorant
                primitiveConstant lam ε supportConstant n u
              ∂paperMeasure ≤ B)
    (k : Z4) :
    R324WithinHalfHeadCollapseBudget ρ lam ε pairing k B := by
  intro res head tail hremaining
  obtain ⟨hGmeas, hG, hbound⟩ :=
    huniform res head tail hremaining
  exact
    (res.norm_incomingExceptionalHeadCollapseFactor_le_two_mul
      head tail hremaining supportConstant primitiveConstant
      hε hGmeas hG hbound k).trans
      (hmaj (residualBlockOrder head.2)
        (res.headContext head tail hremaining).one_le_blockOrder)

/-! ## Norm of the accumulated driver multiplier -/

/-- The multiplier of the all-ordinary base transport is one. -/
theorem R324WithinHalfCertifiedAnalyticTrace.multiplier_alternatingTransport
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace : R324WithinHalfCertifiedAnalyticTrace res scale)
    (hordinary : trace.OrdinaryAlong) (k : Z4) :
    (trace.alternatingTransport hordinary).multiplier k = 1 := rfl

/-- The multiplier of one composed exceptional stop gains exactly the
collapsed-head factor of the retained head. -/
theorem R324WithinHalfNextExceptionalStop.multiplier_alternatingTransport
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (data : R324WithinHalfNextExceptionalStop res scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (sub :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)) (k : Z4) :
    (data.alternatingTransport hε hε1 sub).multiplier k =
      sub.multiplier k *
        data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq k := rfl

/-- One exceptional stop composed with a bounded transport spends one
budget factor. -/
theorem R324WithinHalfNextExceptionalStop.norm_multiplier_alternatingTransport_le
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (data : R324WithinHalfNextExceptionalStop res scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (sub :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (k : Z4) {B : ℝ} (hB0 : 0 ≤ B)
    (hsub : ‖sub.multiplier k‖ ≤ B ^ data.suffix.length)
    (hfactor :
      ‖data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq k‖ ≤ B) :
    ‖(data.alternatingTransport hε hε1 sub).multiplier k‖ ≤
      B ^ (data.suffix.length + 1) := by
  rw [data.multiplier_alternatingTransport hε hε1 sub k,
    norm_mul, pow_succ]
  exact mul_le_mul hsub hfactor (norm_nonneg _)
    (pow_nonneg hB0 _)

namespace R324WithinHalfAlternatingTransport

/-- **Driver multiplier bound.**  By the strong recursion of the driver:
the base all-ordinary run has multiplier one, and each exceptional stop
multiplies by one collapsed-head factor while consuming at least one
remaining step, so the accumulated multiplier is bounded by the uniform
head-collapse budget raised to the remaining length. -/
theorem norm_of_localBlockProvider_multiplier_le
    {C K : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing)
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale)
    (k : Z4) {B : ℝ} (hB1 : 1 ≤ B)
    (hbudget :
      R324WithinHalfHeadCollapseBudget ρ lam ε pairing k B) :
    ‖(of_localBlockProvider
        hε hε1 provider res scale certificate).multiplier k‖ ≤
      B ^ res.remaining.length := by
  unfold of_localBlockProvider
  by_cases hrun :
      r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining =
        res.remaining.length
  · rw [dif_pos hrun]
    show ‖(1 : ℂ)‖ ≤ B ^ res.remaining.length
    rw [norm_one]
    exact one_le_pow₀ hB1
  · rw [dif_neg hrun]
    refine le_trans
      (R324WithinHalfNextExceptionalStop.norm_multiplier_alternatingTransport_le
        _ hε hε1 _ k (zero_le_one.trans hB1) ?_ ?_) ?_
    · exact
        norm_of_localBlockProvider_multiplier_le
          hε hε1 provider _ _ _ k hB1 hbudget
    · exact hbudget _ _ _ _
    · exact
        pow_le_pow_right₀ hB1
          (Nat.succ_le_of_lt
            (R324WithinHalfNextExceptionalStop.suffix_length_lt _))
termination_by res.remaining.length
decreasing_by
  simp only [R324WithinHalfResidualPrefix.afterHead_remaining]
  exact
    R324WithinHalfResidualPrefix.R324WithinHalfNextExceptionalStop.suffix_length_lt
      _

end R324WithinHalfAlternatingTransport

namespace R324IncomingExceptionalStopTraceAssembly

variable {C K : ℝ} {κp κm : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- The multiplier of the provider-built after-head transport spends at
most one budget factor per retained suffix step. -/
theorem norm_afterHeadAlternatingTransport_multiplier_le
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κp)
    (k : Z4) {B : ℝ} (hB1 : 1 ≤ B)
    (hbudget :
      R324WithinHalfHeadCollapseBudget ρ lam ε κp k B) :
    ‖(data.afterHeadAlternatingTransport
        hε hε1 provider).multiplier k‖ ≤
      B ^ data.suffix.length := by
  unfold afterHeadAlternatingTransport
  exact
    R324WithinHalfAlternatingTransport.norm_of_localBlockProvider_multiplier_le
      hε hε1 provider _ _ _ k hB1 hbudget

/-- **Unconditional scalarization of the driver-terminal identity.**
The norm of the weighted refined physical integral is bounded by the norm
of the accumulated driver multiplier times the root integral of the norm
of the terminal coordinate integral carrying the collapsed-head refined
coefficient alone. -/
theorem norm_lamEps_pow_mul_r324RefinedPhysicalIntegral_le
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (t :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (α β : Z4) :
    ‖(lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        r324RefinedPhysicalIntegral
          ρ ε m α β p‖ ≤
      ‖t.multiplier α‖ *
        ∫ ω :
            R324IncomingExceptionalRootParameter
              ρ lam ε e₀.2.1,
          ‖∫ u :
              t.final.SurvivingCoordinate → T4,
            t.final.incomingPhasedResidualDensity
              (data.incomingExceptionalRefinedRootDriverCoefficient
                t α β e₀.2.2 ω u)
              α ρ ε 0 ω.1.1 u
            ∂Measure.pi fun _ => paperMeasure‖
          ∂r324IncomingExceptionalRootParameterMeasure
            ρ lam ε e₀.2.1 := by
  rw [data.lamEps_pow_r324RefinedPhysicalIntegral_eq_driverTerminal
    p e₀ he₀ t hm hε hε1 hG hint α β]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  have heval :
      (∫ u : t.final.SurvivingCoordinate → T4,
        t.final.incomingPhasedResidualDensity
          (t.multiplier α *
            data.incomingExceptionalRefinedRootDriverCoefficient
              t α β e₀.2.2 ω u)
          α ρ ε 0 ω.1.1 u
        ∂Measure.pi fun _ => paperMeasure) =
      t.multiplier α *
        ∫ u : t.final.SurvivingCoordinate → T4,
          t.final.incomingPhasedResidualDensity
            (data.incomingExceptionalRefinedRootDriverCoefficient
              t α β e₀.2.2 ω u)
            α ρ ε 0 ω.1.1 u
          ∂Measure.pi fun _ => paperMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    exact
      t.final.incomingPhasedResidualDensity_const_mul
        (t.multiplier α)
        (data.incomingExceptionalRefinedRootDriverCoefficient
          t α β e₀.2.2 ω u)
        α ρ ε 0 ω.1.1 u
  rw [heval, norm_mul]

/-- **Scalar bound with the budgeted multiplier.**  The transported
refined physical integral is bounded by the head-collapse budget raised
to the retained suffix length, times the root integral of the terminal
coordinate integral of the collapsed-head refined coefficient. -/
theorem norm_lamEps_pow_mul_r324RefinedPhysicalIntegral_le_budget
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K e₀.1)
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (α β : Z4) {B : ℝ} (hB1 : 1 ≤ B)
    (hbudget :
      R324WithinHalfHeadCollapseBudget ρ lam ε e₀.1 α B) :
    ‖(lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        r324RefinedPhysicalIntegral
          ρ ε m α β p‖ ≤
      B ^ data.suffix.length *
        ∫ ω :
            R324IncomingExceptionalRootParameter
              ρ lam ε e₀.2.1,
          ‖∫ u :
              (data.afterHeadAlternatingTransport
                hε hε1 provider).final.SurvivingCoordinate → T4,
            (data.afterHeadAlternatingTransport
              hε hε1 provider).final.incomingPhasedResidualDensity
              (data.incomingExceptionalRefinedRootDriverCoefficient
                (data.afterHeadAlternatingTransport
                  hε hε1 provider)
                α β e₀.2.2 ω u)
              α ρ ε 0 ω.1.1 u
            ∂Measure.pi fun _ => paperMeasure‖
          ∂r324IncomingExceptionalRootParameterMeasure
            ρ lam ε e₀.2.1 := by
  refine
    (data.norm_lamEps_pow_mul_r324RefinedPhysicalIntegral_le
      p e₀ he₀
      (data.afterHeadAlternatingTransport hε hε1 provider)
      hm hε hε1 hG hint α β).trans ?_
  exact
    mul_le_mul_of_nonneg_right
      (data.norm_afterHeadAlternatingTransport_multiplier_le
        hε hε1 provider α hB1 hbudget)
      (integral_nonneg fun ω => norm_nonneg _)

/-- Norm of the collapsed-head refined driver coefficient: the character
factors are unimodular, leaving the squared decay, the Step-4 defect
charge, and the untouched right initial residual times the cross-cut
primitive factor. -/
theorem norm_incomingExceptionalRefinedRootDriverCoefficient_eq
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (t :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm)
    (u : t.final.SurvivingCoordinate → T4) :
    ‖data.incomingExceptionalRefinedRootDriverCoefficient
        t α β π ω u‖ =
      paperSecondOrderModeDecay α ^ 2 *
        ‖incomingExceptionalPrimitiveDefect ρ lam ε
            (residualBlockOrder data.terminal.2)
            data.stopContext.one_le_blockOrder
            data.stopContext.internalEdges α‖ *
        (|(R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).residualIntegrand
            ρ ε ω.1.2.1 ω.1.2.2
            ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).reconstruct ω.2)| *
          |r324ResidualPrimitiveSumProduct
            ρ ε κp κm π
            (r324TwoHalfRootDoubledReconstruct
              t.final
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κm)
              (u, ω.2))|) := by
  unfold incomingExceptionalRefinedRootDriverCoefficient
    incomingExceptionalRefinedRootDriverPostOuter
  simp only [norm_mul, norm_pow, norm_charT4, Complex.norm_real,
    Real.norm_eq_abs, one_mul, mul_one]
  rw [abs_of_nonneg (paperSecondOrderModeDecay_nonneg α)]

end R324IncomingExceptionalStopTraceAssembly

/-! ## Terminal scalar form of the phased density -/

section TerminalNorm

/-- At a terminal prefix with nonempty active carrier, the norm of the
phased density is the coefficient norm times the surviving signed chain
magnitude. -/
theorem norm_terminal_incomingPhasedResidualDensity
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (coefficient : ℂ) (k : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ) (x y : T4)
    (v : res.SurvivingCoordinate → T4) :
    ‖res.incomingPhasedResidualDensity
        coefficient k ρ' ε' x y v‖ =
      ‖coefficient‖ *
        |res.outgoingBoundaryFactor hactive x y
            (res.reconstruct v) *
          res.endpointErasedSignedChain hactive x y
            (res.reconstruct v)| := by
  rw [res.terminal_incomingPhasedResidualDensity_eq
    hnil hactive coefficient k ρ' ε' x y v]
  rw [norm_mul, norm_mul, norm_charT4, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- Degenerate terminal scalar form: with an empty active carrier the
density norm is the coefficient norm. -/
theorem norm_terminal_incomingPhasedResidualDensity_of_active_empty
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hnil : res.remaining = [])
    (hempty : res.state.active = ∅)
    (coefficient : ℂ) (k : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ) (x y : T4)
    (v : res.SurvivingCoordinate → T4) :
    ‖res.incomingPhasedResidualDensity
        coefficient k ρ' ε' x y v‖ = ‖coefficient‖ := by
  rw [res.terminal_incomingPhasedResidualDensity_eq_of_active_empty
    hnil hempty coefficient k ρ' ε' x y v]
  rw [norm_mul, norm_charT4, mul_one]

/-- **Terminal scalar majorization of the coordinate integral.**  The
norm of the terminal coordinate integral is unconditionally bounded by
the integral of the coefficient norm weighted by the surviving signed
chain magnitude. -/
theorem norm_integral_terminal_incomingPhasedResidualDensity_le
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (coefficient : (res.SurvivingCoordinate → T4) → ℂ)
    (k : Z4) (ρ' : SmoothCutoff) (ε' : ℝ) (x y : T4) :
    ‖∫ v : res.SurvivingCoordinate → T4,
        res.incomingPhasedResidualDensity
          (coefficient v) k ρ' ε' x y v
        ∂Measure.pi fun _ => paperMeasure‖ ≤
      ∫ v : res.SurvivingCoordinate → T4,
        ‖coefficient v‖ *
          |res.outgoingBoundaryFactor hactive x y
              (res.reconstruct v) *
            res.endpointErasedSignedChain hactive x y
              (res.reconstruct v)|
        ∂Measure.pi fun _ => paperMeasure := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with v
  exact
    res.norm_terminal_incomingPhasedResidualDensity
      hnil hactive (coefficient v) k ρ' ε' x y v

end TerminalNorm

end R324WithinHalfResidualPrefix

/-! ## Producer for the integrated residual-refined interface -/

/-- Norm bridge between the complex-weighted driver output and the real
scalar interface consumed by the branch summation. -/
theorem norm_lamEps_pow_mul_eq_abs_pow_mul_norm
    (lam ε : ℝ) (N : ℕ) (I : ℂ) :
    ‖(lamEps lam ε : ℂ) ^ N * I‖ =
      |lamEps lam ε| ^ N * ‖I‖ := by
  rw [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs]

/-- **Constructor for the integrated residual-refined interface.**  A
scalar bound for every genuine refined physical integral, at the full
`2m` weight and against the integrated inserted majorant, discharges
`MomentRefinedIntegratedReductionData.refined_bound` exactly. -/
theorem momentRefinedIntegratedReductionData_of_refinedPhysicalIntegral_bound
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {primitiveConstant supportConstant : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h :
      ∀ p : R324RefinedScheduleIndex m,
        |lamEps lam ε| ^ (2 * m) *
            ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
          ∫ z,
            primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant m z
            ∂paperMeasure) :
    MomentRefinedIntegratedReductionData
      ρ lam ε m α β primitiveConstant supportConstant := by
  refine ⟨fun s hs r hr => ?_⟩
  have hp := h ⟨⟨s, hs⟩, ⟨r, hr⟩⟩
  rw [r324RefinedPhysicalIntegral_eq_sum_contractionTerms
    ρ hε hε1 α β ⟨⟨s, hs⟩, ⟨r, hr⟩⟩] at hp
  exact hp

end

end Anderson4D
