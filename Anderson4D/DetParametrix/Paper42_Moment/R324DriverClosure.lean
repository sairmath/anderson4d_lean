import Anderson4D.DetParametrix.Paper42_Moment.R324DriverScalarBound
import Anderson4D.DetParametrix.Paper42_Moment.R324PhaseAOrderLedgerBridge

/-!
# Driver closure for the R-324 endgame

Three scoped closures on top of the driver scalar bound:

* the ambient exponent ledger for one complete contraction entity: the
  left initial order, the right initial order, and the nested-cross
  order partition the moment order `m`, so the full `2m` coupling weight
  splits into the driver weight and a leftover right/cross weight;
* the uniform head-collapse budget instantiated from the integrated
  Proposition 4.1 kernel majorant, with the `(Cλ)^{2n}` factor absorbed
  by the small-coupling regime;
* the terminal `y`-Fourier evaluation of the driver-terminal phased
  density under the root measure, exchanging one raw outgoing Green leg
  for the paper second-order mode decay in the outgoing mode.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The ambient exponent ledger for one contraction entity -/

/-- The two within-half initial suffixes and the nested-cross initial
suffix of one complete contraction entity partition the ambient moment
order. -/
theorem momentContraction_initial_remainingOrders_eq_ambient
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (e₀ : MomentContraction m) :
    (R324WithinHalfResidualPrefix.initial
        ρ lam ε e₀.1).remainingOrder +
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε e₀.2.1).remainingOrder +
        (R324NestedCrossResidualPrefix.initial
          e₀.1 e₀.2.1 e₀.2.2).remainingOrder =
      m :=
  r324InitialSchedules_remainingOrders_eq_ambient
    ρ lam ε e₀.1 e₀.2.1 e₀.2.2

/-- The doubled ambient exponent splits into the driver exponent and the
leftover right/cross exponents. -/
theorem momentContraction_two_mul_ambient_eq_ledger
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (e₀ : MomentContraction m) :
    2 * m =
      2 *
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε e₀.1).remainingOrder +
        (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1).remainingOrder +
          2 *
            (R324NestedCrossResidualPrefix.initial
              e₀.1 e₀.2.1 e₀.2.2).remainingOrder) := by
  have h :=
    momentContraction_initial_remainingOrders_eq_ambient
      ρ lam ε e₀
  omega

/-- Three-part multiplicative split of the full ambient coupling weight
along the ledger of one contraction entity. -/
theorem abs_lamEps_pow_ambient_eq_three_part
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (e₀ : MomentContraction m) :
    |lamEps lam ε| ^ (2 * m) =
      |lamEps lam ε| ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        (|lamEps lam ε| ^
            (2 *
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).remainingOrder) *
          |lamEps lam ε| ^
            (2 *
              (R324NestedCrossResidualPrefix.initial
                e₀.1 e₀.2.1 e₀.2.2).remainingOrder)) := by
  rw [momentContraction_two_mul_ambient_eq_ledger
    ρ lam ε e₀, pow_add, pow_add]

/-! ## The free Green function's `L¹` mass -/

/-- The paper second-order bracket is strictly positive. -/
theorem paperSecondOrderModeDecay_pos (k : Z4) :
    0 < paperSecondOrderModeDecay k := by
  have h0 : 0 ≤ paperModeNormSq k := by
    unfold paperModeNormSq
    positivity
  unfold paperSecondOrderModeDecay
  positivity

/-- Every second-order mode coefficient is dominated by the raw `L¹`
mass of the free Green function. -/
theorem paperSecondOrderModeDecay_le_integral_abs_greenFn (k : Z4) :
    paperSecondOrderModeDecay k ≤
      ∫ z : T4, |greenFn z| ∂paperMeasure := by
  have h : ‖translatedGreenMode k 0‖ ≤
      ∫ x : T4, |greenFn (x - 0)| ∂paperMeasure := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with x
    rw [norm_mul, norm_charT4, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  rw [norm_translatedGreenMode] at h
  simpa using h

/-- The free Green function has strictly positive `L¹` mass. -/
theorem integral_abs_greenFn_pos :
    0 < ∫ z : T4, |greenFn z| ∂paperMeasure :=
  lt_of_lt_of_le (paperSecondOrderModeDecay_pos 0)
    (paperSecondOrderModeDecay_le_integral_abs_greenFn 0)

/-- Reflection-translation `u ↦ q - u` as a measurable equivalence. -/
private def r324SubLeftMeasurableEquiv (q : T4) : T4 ≃ᵐ T4 :=
  MeasurableEquiv.piCongrRight fun i =>
    (MeasurableEquiv.neg
        (AddCircle (2 * Real.pi))).trans
      (MeasurableEquiv.addLeft (q i))

private theorem r324SubLeftMeasurableEquiv_apply
    (q u : T4) :
    r324SubLeftMeasurableEquiv q u = q - u := by
  funext i
  change
    (Equiv.piCongrRight (fun i =>
      ((MeasurableEquiv.neg
          (AddCircle (2 * Real.pi))).trans
        (MeasurableEquiv.addLeft (q i))).toEquiv) u) i =
      q i - u i
  rw [Equiv.piCongrRight_apply, Pi.map_apply]
  change q i + -u i = q i - u i
  rw [sub_eq_add_neg]

private theorem measurePreserving_r324SubLeft
    (q : T4) :
    MeasurePreserving (r324SubLeftMeasurableEquiv q)
      paperMeasure paperMeasure := by
  rw [paperMeasure_eq_volume]
  have hpi :
      MeasurePreserving
        (fun u : T4 => fun i => q i + -u i)
        (volume : Measure T4) (volume : Measure T4) :=
    measurePreserving_pi
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (f := fun i u => q i + -u) fun i =>
        (measurePreserving_add_left
          (volume : Measure (AddCircle (2 * Real.pi)))
          (q i)).comp
          (Measure.measurePreserving_neg _)
  have hfun :
      (r324SubLeftMeasurableEquiv q : T4 → T4) =
        fun u : T4 => fun i => q i + -u i := by
    funext u i
    rw [r324SubLeftMeasurableEquiv_apply]
    change q i - u i = q i + -u i
    rw [sub_eq_add_neg]
  rw [hfun]
  exact hpi

/-- Reflected-translation invariance of the Green `L¹` mass. -/
theorem integral_abs_greenFn_sub (a : T4) :
    (∫ y : T4, |greenFn (a - y)| ∂paperMeasure) =
      ∫ z : T4, |greenFn z| ∂paperMeasure := by
  calc
    (∫ y : T4, |greenFn (a - y)| ∂paperMeasure) =
        ∫ y : T4,
          |greenFn (r324SubLeftMeasurableEquiv a y)|
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      rw [r324SubLeftMeasurableEquiv_apply]
    _ = _ :=
      (measurePreserving_r324SubLeft a).integral_comp'
        (fun z => |greenFn z|)

/-! ## Regrouping the root parameter around the outgoing endpoint -/

/-- Regroup the root/terminal product so that the free outgoing endpoint
pairs with the terminal coordinates: `((y,zw),vr,u) ↦ ((zw,vr),(y,u))`. -/
def r324DriverTerminalRegroupMeasurableEquiv
    (Y ZW VR U : Type*) [MeasurableSpace Y] [MeasurableSpace ZW]
    [MeasurableSpace VR] [MeasurableSpace U] :
    (((Y × ZW) × VR) × U) ≃ᵐ ((ZW × VR) × (Y × U)) :=
  (MeasurableEquiv.prodAssoc
      (α := Y × ZW) (β := VR) (γ := U)).trans
    ((MeasurableEquiv.prodAssoc
        (α := Y) (β := ZW) (γ := VR × U)).trans
      ((r324MoveMiddleMeasurableEquiv Y ZW (VR × U)).trans
        ((MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl ZW)
            (r324MoveMiddleMeasurableEquiv Y VR U)).trans
          (MeasurableEquiv.prodAssoc
            (α := ZW) (β := VR) (γ := Y × U)).symm)))

@[simp]
theorem r324DriverTerminalRegroupMeasurableEquiv_apply
    {Y ZW VR U : Type*} [MeasurableSpace Y] [MeasurableSpace ZW]
    [MeasurableSpace VR] [MeasurableSpace U]
    (q : ((Y × ZW) × VR) × U) :
    r324DriverTerminalRegroupMeasurableEquiv Y ZW VR U q =
      ((q.1.1.2, q.1.2), (q.1.1.1, q.2)) :=
  rfl

@[simp]
theorem r324DriverTerminalRegroupMeasurableEquiv_symm_apply
    {Y ZW VR U : Type*} [MeasurableSpace Y] [MeasurableSpace ZW]
    [MeasurableSpace VR] [MeasurableSpace U]
    (p : (ZW × VR) × (Y × U)) :
    (r324DriverTerminalRegroupMeasurableEquiv Y ZW VR U).symm p =
      (((p.2.1, p.1.1), p.1.2), p.2.2) :=
  rfl

/-- The outgoing-endpoint regrouping preserves the product measures. -/
theorem measurePreserving_r324DriverTerminalRegroupMeasurableEquiv
    {Y ZW VR U : Type*} [MeasurableSpace Y] [MeasurableSpace ZW]
    [MeasurableSpace VR] [MeasurableSpace U]
    (μY : Measure Y) (μZW : Measure ZW)
    (μVR : Measure VR) (μU : Measure U)
    [SFinite μY] [SFinite μZW] [SFinite μVR] [SFinite μU] :
    MeasurePreserving
      (r324DriverTerminalRegroupMeasurableEquiv Y ZW VR U)
      (((μY.prod μZW).prod μVR).prod μU)
      ((μZW.prod μVR).prod (μY.prod μU)) := by
  refine
    ((measurePreserving_prodAssoc μZW μVR (μY.prod μU)).symm.comp
      (((MeasurePreserving.id μZW).prod
        (measurePreserving_r324MoveMiddleMeasurableEquiv
          μY μVR μU)).comp
        ((measurePreserving_r324MoveMiddleMeasurableEquiv
          μY μZW (μVR.prod μU)).comp
          ((measurePreserving_prodAssoc μY μZW (μVR.prod μU)).comp
            (measurePreserving_prodAssoc
              (μY.prod μZW) μVR μU)))))

/-! ## Uniform kernel-majorant budget in the small-coupling regime -/

/-- **Order-uniform integrated Proposition 4.1 budget.**  In the
small-coupling regime `|Cλ| ≤ 1` the order-dependent factor `(Cλ)^{2n}`
of the integrated kernel majorant is at most one, so a single explicit
`ε⁻²/|log ε|` budget dominates every primitive order at once. -/
theorem exists_uniform_integral_primitiveKernelMajorant_budget :
    ∃ Cball Creg : ℝ, 0 < Cball ∧ 0 < Creg ∧
      ∀ (C lam ε supportConstant : ℝ) (n : ℕ),
        0 < ε → 0 < supportConstant → 1 ≤ |Real.log ε| →
        |C * lam| ≤ 1 →
        2 *
            ∫ u : T4,
              primitiveKernelMajorant C lam ε supportConstant n u
              ∂paperMeasure ≤
          max 1
            (2 *
              ((Cball * supportConstant ^ 2 + Creg) *
                ε⁻¹ ^ (2 : ℕ) / |Real.log ε|)) := by
  obtain ⟨Cball, Creg, hCball, hCreg, h⟩ :=
    exists_integral_primitiveKernelMajorant_le
  refine ⟨Cball, Creg, hCball, hCreg, ?_⟩
  intro C lam ε supportConstant n hε hsupport hlog hsmall
  have h1 := h C lam ε supportConstant n hε hsupport hlog
  have hnonneg : (0 : ℝ) ≤ (C * lam) ^ (2 * n) :=
    (even_two_mul n).pow_nonneg _
  have hpow : (C * lam) ^ (2 * n) ≤ 1 := by
    rw [show (C * lam) ^ (2 * n) = |C * lam| ^ (2 * n) by
      rw [← abs_pow, abs_of_nonneg hnonneg]]
    exact pow_le_one₀ (abs_nonneg _) hsmall
  have hA :
      (0 : ℝ) ≤
        (Cball * supportConstant ^ 2 + Creg) *
          ε⁻¹ ^ (2 : ℕ) / |Real.log ε| := by
    have h0 : (0 : ℝ) < |Real.log ε| := lt_of_lt_of_le one_pos hlog
    positivity
  have h2 :
      (∫ u : T4,
          primitiveKernelMajorant C lam ε supportConstant n u
          ∂paperMeasure) ≤
        (Cball * supportConstant ^ 2 + Creg) *
          ε⁻¹ ^ (2 : ℕ) / |Real.log ε| :=
    h1.trans
      ((mul_le_mul_of_nonneg_right hpow hA).trans_eq (one_mul _))
  calc
    2 *
        ∫ u : T4,
          primitiveKernelMajorant C lam ε supportConstant n u
          ∂paperMeasure ≤
        2 *
          ((Cball * supportConstant ^ 2 + Creg) *
            ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) := by
      linarith
    _ ≤ _ := le_max_right _ _

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- **Gap (c): the head-collapse budget instantiated.**  Pointwise
Proposition 4.1 kernel bounds at every reachable head, the small-coupling
regime, and the logarithmic window discharge the uniform head-collapse
budget with one explicit mode-independent `B ≥ 1`. -/
theorem exists_r324WithinHalfHeadCollapseBudget_of_kernelBounds
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε) (hsupport : 0 < supportConstant)
    (hlog : 1 ≤ |Real.log ε|)
    (hsmall : |primitiveConstant * lam| ≤ 1)
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
          supportConstant primitiveConstant) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ k : Z4,
        R324WithinHalfHeadCollapseBudget ρ lam ε pairing k B := by
  obtain ⟨Cball, Creg, _hCball, _hCreg, h⟩ :=
    exists_uniform_integral_primitiveKernelMajorant_budget
  refine
    ⟨max 1
      (2 *
        ((Cball * supportConstant ^ 2 + Creg) *
          ε⁻¹ ^ (2 : ℕ) / |Real.log ε|)),
      le_max_left _ _, fun k => ?_⟩
  exact
    r324WithinHalfHeadCollapseBudget_of_kernelBounds
      supportConstant primitiveConstant _ hε huniform
      (fun n _hn =>
        h primitiveConstant lam ε supportConstant n
          hε hsupport hlog hsmall)
      k

/-- Terminal density norm with the raw outgoing Green leg split off:
under the direct outgoing geometry the whole `y`-dependence is one
translated free Green factor. -/
theorem norm_terminal_incomingPhasedResidualDensity_eq_greenFn_mul
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge :
      res.state.edges
          (res.terminalOutgoingEdgeSlot hactive) =
        greenFn)
    (coefficient : ℂ) (k : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ) (x y : T4)
    (v : res.SurvivingCoordinate → T4) :
    ‖res.incomingPhasedResidualDensity
        coefficient k ρ' ε' x y v‖ =
      ‖coefficient‖ *
          |res.endpointErasedSignedChain hactive 0 0
            (res.reconstruct v)| *
        |greenFn
          (res.terminalOutgoingAnchor hactive
              (res.reconstruct v) -
            y)| := by
  rw [res.norm_terminal_incomingPhasedResidualDensity
    hnil hactive coefficient k ρ' ε' x y v, abs_mul,
    res.endpointErasedSignedChain_eq_zeroEndpoints hactive x y]
  have hout :
      |res.outgoingBoundaryFactor hactive x y
          (res.reconstruct v)| =
        |greenFn
          (res.terminalOutgoingAnchor hactive
              (res.reconstruct v) -
            y)| := by
    have h :=
      res.outgoingBoundaryFactor_eq_outgoingEndpointKernel
        hnil hactive hedge x y (res.reconstruct v)
    have h' :
        ((res.outgoingBoundaryFactor hactive x y
            (res.reconstruct v) : ℝ) : ℂ) =
          ((greenFn
            (res.terminalOutgoingAnchor hactive
                (res.reconstruct v) -
              y) : ℝ) : ℂ) := by
      rw [h]
      unfold r324OutgoingEndpointKernel
      simp
    have h2 := congrArg norm h'
    rwa [Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs] at h2
  rw [hout]
  ring

/-- Exact `y`-marginal of the terminal density norm: the raw outgoing
Green leg integrates to the Green `L¹` mass, independently of the
terminal coordinates. -/
theorem integral_norm_terminal_incomingPhasedResidualDensity_eq
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge :
      res.state.edges
          (res.terminalOutgoingEdgeSlot hactive) =
        greenFn)
    (coefficient : ℂ) (k : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ) (x : T4)
    (v : res.SurvivingCoordinate → T4) :
    (∫ y : T4,
        ‖res.incomingPhasedResidualDensity
          coefficient k ρ' ε' x y v‖
        ∂paperMeasure) =
      ‖coefficient‖ *
          |res.endpointErasedSignedChain hactive 0 0
            (res.reconstruct v)| *
        ∫ z : T4, |greenFn z| ∂paperMeasure := by
  calc
    (∫ y : T4,
        ‖res.incomingPhasedResidualDensity
          coefficient k ρ' ε' x y v‖
        ∂paperMeasure) =
        ∫ y : T4,
          ‖coefficient‖ *
              |res.endpointErasedSignedChain hactive 0 0
                (res.reconstruct v)| *
            |greenFn
              (res.terminalOutgoingAnchor hactive
                  (res.reconstruct v) -
                y)|
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      rw [res.norm_terminal_incomingPhasedResidualDensity_eq_greenFn_mul
        hnil hactive hedge coefficient k ρ' ε' x y v]
    _ =
        ‖coefficient‖ *
            |res.endpointErasedSignedChain hactive 0 0
              (res.reconstruct v)| *
          ∫ y : T4,
            |greenFn
              (res.terminalOutgoingAnchor hactive
                  (res.reconstruct v) -
                y)|
            ∂paperMeasure :=
      integral_const_mul _ _
    _ = _ := by
      rw [integral_abs_greenFn_sub]

/-- **The `y`-Fourier evaluation under the root measure.**  For a
terminal prefix with the direct outgoing Green geometry, and a
coefficient family carrying the outgoing character `charT4 β` at the
free outgoing endpoint but otherwise independent of it, the joint root
integral of the phased density is damped by the paper second-order mode
decay at `β`, at the price of the raw Green `L¹` mass.  Joint
integrability of the density is the only analytic hypothesis. -/
theorem norm_integral_rootProd_incomingPhasedResidualDensity_le_modeDecay
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hnil : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hedge :
      res.state.edges
          (res.terminalOutgoingEdgeSlot hactive) =
        greenFn)
    {ZW VR : Type*} [MeasurableSpace ZW] [MeasurableSpace VR]
    (μZW : Measure ZW) (μVR : Measure VR)
    [SFinite μZW] [SFinite μVR]
    (red : ZW → VR → (res.SurvivingCoordinate → T4) → ℂ)
    (β k : Z4)
    (hjoint :
      Integrable
        (fun q :
            ((T4 × ZW) × VR) ×
              (res.SurvivingCoordinate → T4) =>
          res.incomingPhasedResidualDensity
            (charT4 β q.1.1.1 * red q.1.1.2 q.1.2 q.2)
            k ρ ε 0 q.1.1.1 q.2)
        (((paperMeasure.prod μZW).prod μVR).prod
          (Measure.pi fun _ => paperMeasure))) :
    ‖∫ q :
        ((T4 × ZW) × VR) ×
          (res.SurvivingCoordinate → T4),
        res.incomingPhasedResidualDensity
          (charT4 β q.1.1.1 * red q.1.1.2 q.1.2 q.2)
          k ρ ε 0 q.1.1.1 q.2
        ∂(((paperMeasure.prod μZW).prod μVR).prod
          (Measure.pi fun _ => paperMeasure))‖ ≤
      paperSecondOrderModeDecay β *
        (∫ z : T4, |greenFn z| ∂paperMeasure)⁻¹ *
        ∫ q :
            ((T4 × ZW) × VR) ×
              (res.SurvivingCoordinate → T4),
          ‖res.incomingPhasedResidualDensity
            (charT4 β q.1.1.1 * red q.1.1.2 q.1.2 q.2)
            k ρ ε 0 q.1.1.1 q.2‖
          ∂(((paperMeasure.prod μZW).prod μVR).prod
            (Measure.pi fun _ => paperMeasure)) := by
  set c := ∫ z : T4, |greenFn z| ∂paperMeasure with hc
  have hc0 : 0 < c := integral_abs_greenFn_pos
  set μU :=
    (Measure.pi fun _ : res.SurvivingCoordinate =>
      paperMeasure) with hμU
  set F :
      (((T4 × ZW) × VR) ×
        (res.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      res.incomingPhasedResidualDensity
        (charT4 β q.1.1.1 * red q.1.1.2 q.1.2 q.2)
        k ρ ε 0 q.1.1.1 q.2 with hF
  set σe :=
    r324DriverTerminalRegroupMeasurableEquiv
      T4 ZW VR (res.SurvivingCoordinate → T4) with hσe
  have hσ :
      MeasurePreserving σe
        (((paperMeasure.prod μZW).prod μVR).prod μU)
        ((μZW.prod μVR).prod (paperMeasure.prod μU)) :=
    measurePreserving_r324DriverTerminalRegroupMeasurableEquiv
      paperMeasure μZW μVR μU
  set G :
      ((ZW × VR) ×
        (T4 × (res.SurvivingCoordinate → T4))) → ℂ :=
    fun p => F (σe.symm p) with hG
  have hGF : ∀ q, G (σe q) = F q := by
    intro q
    show F (σe.symm (σe q)) = F q
    rw [MeasurableEquiv.symm_apply_apply]
  have hGint :
      Integrable G
        ((μZW.prod μVR).prod (paperMeasure.prod μU)) := by
    refine (hσ.integrable_comp_emb σe.measurableEmbedding).mp ?_
    apply hjoint.congr
    filter_upwards with q
    exact (hGF q).symm
  have hint_eq :
      (∫ q, F q
          ∂(((paperMeasure.prod μZW).prod μVR).prod μU)) =
        ∫ p, G p
          ∂((μZW.prod μVR).prod (paperMeasure.prod μU)) := by
    rw [← hσ.integral_comp' G]
    exact
      integral_congr_ae
        (Filter.Eventually.of_forall fun q => (hGF q).symm)
  have hnorm_eq :
      (∫ q, ‖F q‖
          ∂(((paperMeasure.prod μZW).prod μVR).prod μU)) =
        ∫ p, ‖G p‖
          ∂((μZW.prod μVR).prod (paperMeasure.prod μU)) := by
    rw [← hσ.integral_comp' fun p => ‖G p‖]
    refine
      integral_congr_ae
        (Filter.Eventually.of_forall fun q => ?_)
    show ‖F q‖ = ‖G (σe q)‖
    rw [hGF q]
  have hGs :
      ∀ (s : ZW × VR)
        (yu : T4 × (res.SurvivingCoordinate → T4)),
        G (s, yu) =
          res.incomingPhasedResidualDensity
            (charT4 β yu.1 * red s.1 s.2 yu.2)
            k ρ ε 0 yu.1 yu.2 := by
    intro s yu
    rfl
  have hkey :
      ∀ᵐ s ∂(μZW.prod μVR),
        ‖∫ yu, G (s, yu) ∂(paperMeasure.prod μU)‖ ≤
          paperSecondOrderModeDecay β * c⁻¹ *
            ∫ yu, ‖G (s, yu)‖ ∂(paperMeasure.prod μU) := by
    filter_upwards [hGint.prod_right_ae] with s hs
    have hyeval :
        ∀ u,
          (∫ y, G (s, (y, u)) ∂paperMeasure) =
            red s.1 s.2 u *
              charT4 k
                (res.terminalIncomingAnchor
                  (res.reconstruct u)) *
              ((res.endpointErasedSignedChain hactive 0 0
                (res.reconstruct u) : ℝ) : ℂ) *
              translatedGreenMode β
                (res.terminalOutgoingAnchor hactive
                  (res.reconstruct u)) := by
      intro u
      calc
        (∫ y, G (s, (y, u)) ∂paperMeasure) =
            ∫ y,
              charT4 β y *
                res.incomingPhasedResidualDensity
                  (red s.1 s.2 u) k ρ ε 0 y u
              ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with y
          rw [hGs s (y, u)]
          exact
            res.incomingPhasedResidualDensity_const_mul
              (charT4 β y) (red s.1 s.2 u) k ρ ε 0 y u
        _ = _ :=
          res.integral_char_mul_terminal_incomingPhasedResidualDensity_eq
            hnil hactive hedge (red s.1 s.2 u) k β ρ ε 0 u
    have hynorm :
        ∀ u,
          ‖∫ y, G (s, (y, u)) ∂paperMeasure‖ =
            ‖red s.1 s.2 u‖ *
                |res.endpointErasedSignedChain hactive 0 0
                  (res.reconstruct u)| *
              paperSecondOrderModeDecay β := by
      intro u
      rw [hyeval u, norm_mul, norm_mul, norm_mul,
        norm_charT4, norm_translatedGreenMode,
        Complex.norm_real, Real.norm_eq_abs]
      ring
    have hymarg :
        ∀ u,
          (∫ y, ‖G (s, (y, u))‖ ∂paperMeasure) =
            ‖red s.1 s.2 u‖ *
                |res.endpointErasedSignedChain hactive 0 0
                  (res.reconstruct u)| *
              c := by
      intro u
      calc
        (∫ y, ‖G (s, (y, u))‖ ∂paperMeasure) =
            ∫ y,
              ‖red s.1 s.2 u‖ *
                  |res.endpointErasedSignedChain hactive 0 0
                    (res.reconstruct u)| *
                |greenFn
                  (res.terminalOutgoingAnchor hactive
                      (res.reconstruct u) -
                    y)|
              ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with y
          rw [hGs s (y, u),
            res.norm_terminal_incomingPhasedResidualDensity_eq_greenFn_mul
              hnil hactive hedge _ k ρ ε 0 y u,
            norm_mul, norm_charT4, one_mul]
        _ =
            ‖red s.1 s.2 u‖ *
                |res.endpointErasedSignedChain hactive 0 0
                  (res.reconstruct u)| *
              ∫ y,
                |greenFn
                  (res.terminalOutgoingAnchor hactive
                      (res.reconstruct u) -
                    y)|
                ∂paperMeasure :=
          integral_const_mul _ _
        _ = _ := by rw [integral_abs_greenFn_sub]
    have hnormprod :
        (∫ yu, ‖G (s, yu)‖ ∂(paperMeasure.prod μU)) =
          (∫ u,
            ‖red s.1 s.2 u‖ *
              |res.endpointErasedSignedChain hactive 0 0
                (res.reconstruct u)|
            ∂μU) * c := by
      rw [integral_prod_symm _ hs.norm, ← integral_mul_const]
      exact
        integral_congr_ae
          (Filter.Eventually.of_forall fun u => hymarg u)
    rw [integral_prod_symm _ hs]
    calc
      ‖∫ u, ∫ y, G (s, (y, u)) ∂paperMeasure ∂μU‖ ≤
          ∫ u, ‖∫ y, G (s, (y, u)) ∂paperMeasure‖ ∂μU :=
        norm_integral_le_integral_norm _
      _ =
          (∫ u,
            ‖red s.1 s.2 u‖ *
              |res.endpointErasedSignedChain hactive 0 0
                (res.reconstruct u)|
            ∂μU) * paperSecondOrderModeDecay β := by
        rw [← integral_mul_const]
        exact
          integral_congr_ae
            (Filter.Eventually.of_forall fun u => hynorm u)
      _ =
          paperSecondOrderModeDecay β * c⁻¹ *
            ∫ yu, ‖G (s, yu)‖ ∂(paperMeasure.prod μU) := by
        rw [hnormprod]
        have hcne : c ≠ 0 := ne_of_gt hc0
        field_simp
  have hHint :
      Integrable
        (fun s =>
          ∫ yu, ‖G (s, yu)‖ ∂(paperMeasure.prod μU))
        (μZW.prod μVR) :=
    hGint.integral_norm_prod_left
  have hfmeas :
      AEStronglyMeasurable
        (fun s =>
          ∫ yu, G (s, yu) ∂(paperMeasure.prod μU))
        (μZW.prod μVR) :=
    hGint.aestronglyMeasurable.integral_prod_right'
  have hfint :
      Integrable
        (fun s =>
          ‖∫ yu, G (s, yu) ∂(paperMeasure.prod μU)‖)
        (μZW.prod μVR) := by
    refine hHint.mono' hfmeas.norm ?_
    filter_upwards with s
    rw [norm_norm]
    exact norm_integral_le_integral_norm _
  calc
    ‖∫ q, F q
        ∂(((paperMeasure.prod μZW).prod μVR).prod μU)‖ =
        ‖∫ s,
          ∫ yu, G (s, yu) ∂(paperMeasure.prod μU)
          ∂(μZW.prod μVR)‖ := by
      rw [hint_eq, integral_prod _ hGint]
    _ ≤
        ∫ s,
          ‖∫ yu, G (s, yu) ∂(paperMeasure.prod μU)‖
          ∂(μZW.prod μVR) :=
      norm_integral_le_integral_norm _
    _ ≤
        ∫ s,
          paperSecondOrderModeDecay β * c⁻¹ *
            ∫ yu, ‖G (s, yu)‖ ∂(paperMeasure.prod μU)
          ∂(μZW.prod μVR) :=
      integral_mono_ae hfint
        (hHint.const_mul _) hkey
    _ =
        paperSecondOrderModeDecay β * c⁻¹ *
          ∫ s,
            ∫ yu, ‖G (s, yu)‖ ∂(paperMeasure.prod μU)
            ∂(μZW.prod μVR) :=
      integral_const_mul _ _
    _ =
        paperSecondOrderModeDecay β * c⁻¹ *
          ∫ q, ‖F q‖
            ∂(((paperMeasure.prod μZW).prod μVR).prod μU) := by
      rw [← integral_prod _ hGint.norm, hnorm_eq]

namespace R324IncomingExceptionalStopTraceAssembly

variable {C K : ℝ} {κp κm : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- **Gap (b), coefficient form.**  The leftover right/cross coupling
weight lands multiplicatively on the two untouched scalar factors of the
collapsed-head refined driver coefficient: the right initial residual
integrand receives the right-half weight and the cross-cut primitive
factor receives the nested-cross weight. -/
theorem abs_lamEps_pow_mul_norm_incomingExceptionalRefinedRootDriverCoefficient_eq
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
    (u : t.final.SurvivingCoordinate → T4)
    (a b : ℕ) :
    |lamEps lam ε| ^ (2 * a + 2 * b) *
        ‖data.incomingExceptionalRefinedRootDriverCoefficient
          t α β π ω u‖ =
      paperSecondOrderModeDecay α ^ 2 *
          ‖incomingExceptionalPrimitiveDefect ρ lam ε
              (residualBlockOrder data.terminal.2)
              data.stopContext.one_le_blockOrder
              data.stopContext.internalEdges α‖ *
        ((|lamEps lam ε| ^ (2 * a) *
            |(R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).residualIntegrand
              ρ ε ω.1.2.1 ω.1.2.2
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).reconstruct ω.2)|) *
          (|lamEps lam ε| ^ (2 * b) *
            |r324ResidualPrimitiveSumProduct
              ρ ε κp κm π
              (r324TwoHalfRootDoubledReconstruct
                t.final
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε κm)
                (u, ω.2))|)) := by
  rw [data.norm_incomingExceptionalRefinedRootDriverCoefficient_eq
    t α β π ω u, pow_add]
  ring

/-- The multiplier-weighted collapsed-head refined driver coefficient
with the outgoing character `charT4 β` at the free outgoing endpoint
stripped off; it depends on the root parameter only through the two
measured endpoints and the right initial tuple. -/
def incomingExceptionalRefinedRootDriverReducedCoefficient
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
    (zw : T4 × T4)
    (vr :
      (R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).SurvivingCoordinate → T4)
    (u : t.final.SurvivingCoordinate → T4) : ℂ :=
  t.multiplier α *
    ((paperSecondOrderModeDecay α : ℂ) ^ 2 *
      incomingExceptionalPrimitiveDefect ρ lam ε
        (residualBlockOrder data.terminal.2)
        data.stopContext.one_le_blockOrder
        data.stopContext.internalEdges α *
      (charT4 (-α) zw.1 *
        charT4 (-β) zw.2 *
        (((R324WithinHalfResidualPrefix.initial
            ρ lam ε κm).residualIntegrand
          ρ ε zw.1 zw.2
          ((R324WithinHalfResidualPrefix.initial
            ρ lam ε κm).reconstruct vr) : ℂ) *
          (r324ResidualPrimitiveSumProduct
            ρ ε κp κm π
            (r324TwoHalfRootDoubledReconstruct
              t.final
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κm)
              (u, vr)) : ℂ))))

/-- Stripping the outgoing character from the multiplier-weighted driver
coefficient. -/
theorem multiplier_mul_driverCoefficient_eq_char_mul_reduced
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
    t.multiplier α *
        data.incomingExceptionalRefinedRootDriverCoefficient
          t α β π ω u =
      charT4 β ω.1.1 *
        data.incomingExceptionalRefinedRootDriverReducedCoefficient
          t α β π ω.1.2 ω.2 u := by
  unfold incomingExceptionalRefinedRootDriverCoefficient
    incomingExceptionalRefinedRootDriverPostOuter
    incomingExceptionalRefinedRootDriverReducedCoefficient
  ring

/-- Norm of the reduced driver coefficient. -/
theorem norm_incomingExceptionalRefinedRootDriverReducedCoefficient_eq
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
    (zw : T4 × T4)
    (vr :
      (R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).SurvivingCoordinate → T4)
    (u : t.final.SurvivingCoordinate → T4) :
    ‖data.incomingExceptionalRefinedRootDriverReducedCoefficient
        t α β π zw vr u‖ =
      ‖t.multiplier α‖ *
        (paperSecondOrderModeDecay α ^ 2 *
          ‖incomingExceptionalPrimitiveDefect ρ lam ε
              (residualBlockOrder data.terminal.2)
              data.stopContext.one_le_blockOrder
              data.stopContext.internalEdges α‖ *
          (|(R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).residualIntegrand
              ρ ε zw.1 zw.2
              ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).reconstruct vr)| *
            |r324ResidualPrimitiveSumProduct
              ρ ε κp κm π
              (r324TwoHalfRootDoubledReconstruct
                t.final
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε κm)
                (u, vr))|)) := by
  unfold incomingExceptionalRefinedRootDriverReducedCoefficient
  simp only [norm_mul, norm_pow, norm_charT4, Complex.norm_real,
    Real.norm_eq_abs, one_mul, mul_one]
  rw [abs_of_nonneg (paperSecondOrderModeDecay_nonneg α)]

/-- **The gap-(a) interface: joint integrability of the driver-terminal
phased density under the root measure.**  This is the only analytic
input of the terminal `y`-Fourier evaluation. -/
def DriverTerminalJointIntegrable
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
    (π : κp.singles ≃ κm.singles) : Prop :=
  Integrable
    (fun q :
        R324IncomingExceptionalRootParameter
            ρ lam ε κm ×
          (t.final.SurvivingCoordinate → T4) =>
      t.final.incomingPhasedResidualDensity
        (t.multiplier α *
          data.incomingExceptionalRefinedRootDriverCoefficient
            t α β π q.1 q.2)
        α ρ ε 0 q.1.1.1 q.2)
    ((r324IncomingExceptionalRootParameterMeasure
        ρ lam ε κm).prod
      (Measure.pi fun _ => paperMeasure))

/-- **Gap (b), scalar form: the full-ambient-weight budget bound.**  The
`2m`-weighted refined physical integral is bounded by the head-collapse
budget raised to the retained suffix length times the root integral of
the terminal coordinate integral, with the leftover right-half and
nested-cross coupling weights carried inside the root integrand. -/
theorem norm_lamEps_pow_ambient_mul_r324RefinedPhysicalIntegral_le_budget
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
    |lamEps lam ε| ^ (2 * m) *
        ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
      B ^ data.suffix.length *
        ∫ ω :
            R324IncomingExceptionalRootParameter
              ρ lam ε e₀.2.1,
          |lamEps lam ε| ^
              (2 *
                  (R324WithinHalfResidualPrefix.initial
                    ρ lam ε e₀.2.1).remainingOrder +
                2 *
                  (R324NestedCrossResidualPrefix.initial
                    e₀.1 e₀.2.1 e₀.2.2).remainingOrder) *
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
  have hbase :=
    data.norm_lamEps_pow_mul_r324RefinedPhysicalIntegral_le_budget
      p e₀ he₀ hm hε hε1 provider hG hint α β hB1 hbudget
  have hW0 :
      (0 : ℝ) ≤
        |lamEps lam ε| ^
          (2 *
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).remainingOrder +
            2 *
              (R324NestedCrossResidualPrefix.initial
                e₀.1 e₀.2.1 e₀.2.2).remainingOrder) := by
    positivity
  have hsplit :
      |lamEps lam ε| ^ (2 * m) *
          ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ =
        |lamEps lam ε| ^
            (2 *
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε e₀.2.1).remainingOrder +
              2 *
                (R324NestedCrossResidualPrefix.initial
                  e₀.1 e₀.2.1 e₀.2.2).remainingOrder) *
          ‖(lamEps lam ε : ℂ) ^
              (2 *
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε e₀.1).remainingOrder) *
            r324RefinedPhysicalIntegral ρ ε m α β p‖ := by
    rw [norm_lamEps_pow_mul_eq_abs_pow_mul_norm,
      abs_lamEps_pow_ambient_eq_three_part ρ lam ε e₀,
      pow_add]
    ring
  rw [hsplit]
  refine (mul_le_mul_of_nonneg_left hbase hW0).trans (le_of_eq ?_)
  rw [← mul_assoc,
    mul_comm
      (|lamEps lam ε| ^
        (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1).remainingOrder +
          2 *
            (R324NestedCrossResidualPrefix.initial
              e₀.1 e₀.2.1 e₀.2.2).remainingOrder))
      (B ^ data.suffix.length),
    mul_assoc, ← integral_const_mul]

/-- **Gap (a) applied: the mode-decay upgrade of the driver-terminal
scalar bound.**  Under the direct outgoing Green geometry and the joint
integrability of the driver-terminal density under the root measure, the
weighted refined physical integral gains the paper second-order mode
decay in the outgoing mode `β`, at the price of the raw Green `L¹`
mass, against the joint `L¹` mass of the driver-terminal density. -/
theorem norm_lamEps_pow_mul_r324RefinedPhysicalIntegral_le_modeDecay
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
    (α β : Z4)
    (hjoint : data.DriverTerminalJointIntegrable t α β e₀.2.2)
    (hactive : t.final.state.active.Nonempty)
    (hedge :
      t.final.state.edges
          (t.final.terminalOutgoingEdgeSlot hactive) =
        greenFn) :
    ‖(lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        r324RefinedPhysicalIntegral
          ρ ε m α β p‖ ≤
      paperSecondOrderModeDecay β *
        (∫ z : T4, |greenFn z| ∂paperMeasure)⁻¹ *
        ∫ q :
            R324IncomingExceptionalRootParameter
                ρ lam ε e₀.2.1 ×
              (t.final.SurvivingCoordinate → T4),
          ‖t.final.incomingPhasedResidualDensity
            (t.multiplier α *
              data.incomingExceptionalRefinedRootDriverCoefficient
                t α β e₀.2.2 q.1 q.2)
            α ρ ε 0 q.1.1.1 q.2‖
          ∂((r324IncomingExceptionalRootParameterMeasure
              ρ lam ε e₀.2.1).prod
            (Measure.pi fun _ => paperMeasure)) := by
  have hpoint :
      ∀ q :
          R324IncomingExceptionalRootParameter
              ρ lam ε e₀.2.1 ×
            (t.final.SurvivingCoordinate → T4),
        t.final.incomingPhasedResidualDensity
            (t.multiplier α *
              data.incomingExceptionalRefinedRootDriverCoefficient
                t α β e₀.2.2 q.1 q.2)
            α ρ ε 0 q.1.1.1 q.2 =
          t.final.incomingPhasedResidualDensity
            (charT4 β q.1.1.1 *
              data.incomingExceptionalRefinedRootDriverReducedCoefficient
                t α β e₀.2.2 q.1.1.2 q.1.2 q.2)
            α ρ ε 0 q.1.1.1 q.2 := by
    intro q
    rw [data.multiplier_mul_driverCoefficient_eq_char_mul_reduced
      t α β e₀.2.2 q.1 q.2]
  have hstripped :
      Integrable
        (fun q :
            R324IncomingExceptionalRootParameter
                ρ lam ε e₀.2.1 ×
              (t.final.SurvivingCoordinate → T4) =>
          t.final.incomingPhasedResidualDensity
            (charT4 β q.1.1.1 *
              data.incomingExceptionalRefinedRootDriverReducedCoefficient
                t α β e₀.2.2 q.1.1.2 q.1.2 q.2)
            α ρ ε 0 q.1.1.1 q.2)
        ((r324IncomingExceptionalRootParameterMeasure
            ρ lam ε e₀.2.1).prod
          (Measure.pi fun _ => paperMeasure)) :=
    hjoint.congr
      (Filter.Eventually.of_forall fun q => hpoint q)
  have hgen :=
    t.final.norm_integral_rootProd_incomingPhasedResidualDensity_le_modeDecay
      t.final_remaining hactive hedge
      (paperMeasure.prod paperMeasure)
      (Measure.pi fun _ :
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε e₀.2.1).SurvivingCoordinate =>
          paperMeasure)
      (fun zw vr u =>
        data.incomingExceptionalRefinedRootDriverReducedCoefficient
          t α β e₀.2.2 zw vr u)
      β α hstripped
  have hdriver :=
    data.lamEps_pow_r324RefinedPhysicalIntegral_eq_driverTerminal
      p e₀ he₀ t hm hε hε1 hG hint α β
  have hprodint :=
    integral_prod
      (fun q :
          R324IncomingExceptionalRootParameter
              ρ lam ε e₀.2.1 ×
            (t.final.SurvivingCoordinate → T4) =>
        t.final.incomingPhasedResidualDensity
          (t.multiplier α *
            data.incomingExceptionalRefinedRootDriverCoefficient
              t α β e₀.2.2 q.1 q.2)
          α ρ ε 0 q.1.1.1 q.2)
      hjoint
  rw [hdriver, ← hprodint,
    integral_congr_ae
      (Filter.Eventually.of_forall fun q => hpoint q),
    integral_congr_ae
      (μ :=
        (r324IncomingExceptionalRootParameterMeasure
            ρ lam ε e₀.2.1).prod
          (Measure.pi fun _ => paperMeasure))
      (Filter.Eventually.of_forall fun q =>
        congrArg norm (hpoint q))]
  exact hgen

/-- Consumer form of the mode-decay upgrade: the direct-outgoing Green
premise is discharged from the driver-terminal schedule completion and
the boolean shortcut flag of the frozen pairing. -/
theorem norm_lamEps_pow_mul_r324RefinedPhysicalIntegral_le_modeDecay_of_not_shortcut
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
    (α β : Z4)
    (hjoint : data.DriverTerminalJointIntegrable t α β e₀.2.2)
    (hactive : t.final.state.active.Nonempty)
    (hdirect : r324OutgoingIsShortcut e₀.1 = false) :
    ‖(lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        r324RefinedPhysicalIntegral
          ρ ε m α β p‖ ≤
      paperSecondOrderModeDecay β *
        (∫ z : T4, |greenFn z| ∂paperMeasure)⁻¹ *
        ∫ q :
            R324IncomingExceptionalRootParameter
                ρ lam ε e₀.2.1 ×
              (t.final.SurvivingCoordinate → T4),
          ‖t.final.incomingPhasedResidualDensity
            (t.multiplier α *
              data.incomingExceptionalRefinedRootDriverCoefficient
                t α β e₀.2.2 q.1 q.2)
            α ρ ε 0 q.1.1.1 q.2‖
          ∂((r324IncomingExceptionalRootParameterMeasure
              ρ lam ε e₀.2.1).prod
            (Measure.pi fun _ => paperMeasure)) :=
  data.norm_lamEps_pow_mul_r324RefinedPhysicalIntegral_le_modeDecay
    p e₀ he₀ t hm hε hε1 hG hint α β hjoint hactive
    (t.final.state_edges_terminalOutgoingEdgeSlot_eq_greenFn_of_not_shortcut
      hm t.final_processed_eq_schedule hdirect hactive)

/-- **Gaps (a)+(b) combined: the full-ambient-weight mode-decay bound.**
The `2m`-weighted refined physical integral gains the outgoing mode
decay, with the leftover right-half and nested-cross coupling weights
carried against the joint terminal density mass. -/
theorem norm_lamEps_pow_ambient_mul_r324RefinedPhysicalIntegral_le_modeDecay
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
    (α β : Z4)
    (hjoint : data.DriverTerminalJointIntegrable t α β e₀.2.2)
    (hactive : t.final.state.active.Nonempty)
    (hedge :
      t.final.state.edges
          (t.final.terminalOutgoingEdgeSlot hactive) =
        greenFn) :
    |lamEps lam ε| ^ (2 * m) *
        ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
      paperSecondOrderModeDecay β *
        (∫ z : T4, |greenFn z| ∂paperMeasure)⁻¹ *
        ∫ q :
            R324IncomingExceptionalRootParameter
                ρ lam ε e₀.2.1 ×
              (t.final.SurvivingCoordinate → T4),
          |lamEps lam ε| ^
              (2 *
                  (R324WithinHalfResidualPrefix.initial
                    ρ lam ε e₀.2.1).remainingOrder +
                2 *
                  (R324NestedCrossResidualPrefix.initial
                    e₀.1 e₀.2.1 e₀.2.2).remainingOrder) *
            ‖t.final.incomingPhasedResidualDensity
              (t.multiplier α *
                data.incomingExceptionalRefinedRootDriverCoefficient
                  t α β e₀.2.2 q.1 q.2)
              α ρ ε 0 q.1.1.1 q.2‖
          ∂((r324IncomingExceptionalRootParameterMeasure
              ρ lam ε e₀.2.1).prod
            (Measure.pi fun _ => paperMeasure)) := by
  have hbase :=
    data.norm_lamEps_pow_mul_r324RefinedPhysicalIntegral_le_modeDecay
      p e₀ he₀ t hm hε hε1 hG hint α β hjoint hactive hedge
  have hW0 :
      (0 : ℝ) ≤
        |lamEps lam ε| ^
          (2 *
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.2.1).remainingOrder +
            2 *
              (R324NestedCrossResidualPrefix.initial
                e₀.1 e₀.2.1 e₀.2.2).remainingOrder) := by
    positivity
  have hsplit :
      |lamEps lam ε| ^ (2 * m) *
          ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ =
        |lamEps lam ε| ^
            (2 *
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε e₀.2.1).remainingOrder +
              2 *
                (R324NestedCrossResidualPrefix.initial
                  e₀.1 e₀.2.1 e₀.2.2).remainingOrder) *
          ‖(lamEps lam ε : ℂ) ^
              (2 *
                (R324WithinHalfResidualPrefix.initial
                  ρ lam ε e₀.1).remainingOrder) *
            r324RefinedPhysicalIntegral ρ ε m α β p‖ := by
    rw [norm_lamEps_pow_mul_eq_abs_pow_mul_norm,
      abs_lamEps_pow_ambient_eq_three_part ρ lam ε e₀,
      pow_add]
    ring
  rw [hsplit]
  refine (mul_le_mul_of_nonneg_left hbase hW0).trans (le_of_eq ?_)
  rw [← mul_assoc,
    mul_comm
      (|lamEps lam ε| ^
        (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1).remainingOrder +
          2 *
            (R324NestedCrossResidualPrefix.initial
              e₀.1 e₀.2.1 e₀.2.2).remainingOrder))
      (paperSecondOrderModeDecay β *
        (∫ z : T4, |greenFn z| ∂paperMeasure)⁻¹),
    mul_assoc, ← integral_const_mul]

/-- **Gaps (b)+(c) assembled.**  The pointwise Proposition 4.1 kernel
bounds, the small-coupling regime, and the logarithmic window produce a
head-collapse budget `B ≥ 1` for which the full-ambient-weight refined
physical bound holds. -/
theorem exists_norm_lamEps_pow_ambient_mul_r324RefinedPhysicalIntegral_le_budget
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
    (α β : Z4)
    (supportConstant primitiveConstant : ℝ)
    (hsupport : 0 < supportConstant)
    (hlog : 1 ≤ |Real.log ε|)
    (hsmall : |primitiveConstant * lam| ≤ 1)
    (huniform :
      ∀ (res : R324WithinHalfResidualPrefix ρ lam ε e₀.1)
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
          supportConstant primitiveConstant) :
    ∃ B : ℝ, 1 ≤ B ∧
      |lamEps lam ε| ^ (2 * m) *
          ‖r324RefinedPhysicalIntegral ρ ε m α β p‖ ≤
        B ^ data.suffix.length *
          ∫ ω :
              R324IncomingExceptionalRootParameter
                ρ lam ε e₀.2.1,
            |lamEps lam ε| ^
                (2 *
                    (R324WithinHalfResidualPrefix.initial
                      ρ lam ε e₀.2.1).remainingOrder +
                  2 *
                    (R324NestedCrossResidualPrefix.initial
                      e₀.1 e₀.2.1 e₀.2.2).remainingOrder) *
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
  obtain ⟨B, hB1, hbudget⟩ :=
    exists_r324WithinHalfHeadCollapseBudget_of_kernelBounds
      (pairing := e₀.1) supportConstant primitiveConstant
      hε hsupport hlog hsmall huniform
  exact
    ⟨B, hB1,
      data.norm_lamEps_pow_ambient_mul_r324RefinedPhysicalIntegral_le_budget
        p e₀ he₀ hm hε hε1 provider hG hint α β hB1
        (hbudget α)⟩

end R324IncomingExceptionalStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
