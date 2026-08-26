import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalBoundaryLegFourier
import Anderson4D.DetParametrix.Paper42_Moment.R324CertifiedTwoHalfPhysicalCollapse

/-!
# Uniform endpoint-integrated boundary bounds

The terminal edge certificate controls every actual boundary kernel by its
own inverse-square scale.  After the external endpoint variables have been
integrated, this gives a mode-independent `L¹` constant.  No direct-Green
hypothesis and no estimate of the grouped internal core is used here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfEdgeCertificate

/-- A certified named edge is genuinely integrable.  The certificate is
off-diagonal; the only omitted point is null for paper measure. -/
theorem integrable_edge
    {m : ℕ} {state : R324WithinHalfEdgeState m}
    {scale : Fin (m + 1) → ℝ}
    (cert : R324WithinHalfEdgeCertificate state scale)
    (edge : Fin (m + 1)) :
    Integrable (state.edges edge) paperMeasure := by
  refine
    (integrable_invSqKer.const_mul (scale edge)).mono
      (cert.measurable edge).aestronglyMeasurable ?_
  filter_upwards
      [compl_mem_ae_iff.mpr
        (paperMeasure_singleton (0 : T4))] with z hz
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg
      (mul_nonneg (cert.scale_pos edge).le (invSqKer_nonneg z))]
  apply cert.bound edge z
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz

/-- A Fourier character cannot increase the `L¹` bound of a certified
edge translated in the `x - anchor` orientation. -/
theorem norm_integral_char_mul_edge_sub_le
    {m : ℕ} {state : R324WithinHalfEdgeState m}
    {scale : Fin (m + 1) → ℝ}
    (cert : R324WithinHalfEdgeCertificate state scale)
    (edge : Fin (m + 1)) (k : Z4) (anchor : T4) :
    ‖∫ x : T4,
        charT4 k x * (state.edges edge (x - anchor) : ℂ)
        ∂paperMeasure‖ ≤
      scale edge * invSqKerMass := by
  have htranslated :
      Integrable (fun x : T4 => state.edges edge (x - anchor))
        paperMeasure :=
    ((measurePreserving_sub_paper anchor).integrable_comp_emb
      (MeasurableEquiv.subRight anchor).measurableEmbedding).mpr
        (cert.integrable_edge edge)
  have hmajorant :
      Integrable (fun x : T4 => scale edge * invSqKer (x - anchor))
        paperMeasure :=
    (integrable_invSqKer_sub anchor).const_mul (scale edge)
  calc
    ‖∫ x : T4,
        charT4 k x * (state.edges edge (x - anchor) : ℂ)
        ∂paperMeasure‖ ≤
        ∫ x : T4,
          ‖charT4 k x * (state.edges edge (x - anchor) : ℂ)‖
          ∂paperMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ x : T4, |state.edges edge (x - anchor)|
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_mul, norm_charT4, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    _ ≤ ∫ x : T4, scale edge * invSqKer (x - anchor)
          ∂paperMeasure := by
      apply integral_mono_ae htranslated.norm hmajorant
      filter_upwards
          [compl_mem_ae_iff.mpr (paperMeasure_singleton anchor)] with x hx
      have hxa : x ≠ anchor := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
      exact cert.bound edge (x - anchor) (sub_ne_zero.mpr hxa)
    _ = scale edge * invSqKerMass := by
      rw [integral_const_mul]
      have heq :
          (fun x : T4 => invSqKer (x - anchor)) =
            fun x : T4 => invSqKer (anchor - x) := by
        funext x
        exact invSqKer_sub_comm x anchor
      rw [heq, integral_invSqKer_sub_left]

/-- The corresponding bound in the `anchor - x` orientation. -/
theorem norm_integral_char_mul_edge_sub_left_le
    {m : ℕ} {state : R324WithinHalfEdgeState m}
    {scale : Fin (m + 1) → ℝ}
    (cert : R324WithinHalfEdgeCertificate state scale)
    (edge : Fin (m + 1)) (k : Z4) (anchor : T4) :
    ‖∫ x : T4,
        charT4 k x * (state.edges edge (anchor - x) : ℂ)
        ∂paperMeasure‖ ≤
      scale edge * invSqKerMass := by
  have htranslated :
      Integrable (fun x : T4 => state.edges edge (anchor - x))
        paperMeasure := by
    refine
      ((integrable_invSqKer_sub_left anchor).const_mul
        (scale edge)).mono
        ((cert.measurable edge).comp
          (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
    filter_upwards
        [compl_mem_ae_iff.mpr (paperMeasure_singleton anchor)] with x hx
    have hxanchor : x ≠ anchor := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    have hxa : anchor ≠ x := hxanchor.symm
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg (cert.scale_pos edge).le
          (invSqKer_nonneg (anchor - x)))]
    exact cert.bound edge (anchor - x) (sub_ne_zero.mpr hxa)
  have hmajorant :
      Integrable (fun x : T4 => scale edge * invSqKer (anchor - x))
        paperMeasure :=
    (integrable_invSqKer_sub_left anchor).const_mul (scale edge)
  calc
    ‖∫ x : T4,
        charT4 k x * (state.edges edge (anchor - x) : ℂ)
        ∂paperMeasure‖ ≤
        ∫ x : T4,
          ‖charT4 k x * (state.edges edge (anchor - x) : ℂ)‖
          ∂paperMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ x : T4, |state.edges edge (anchor - x)|
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_mul, norm_charT4, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    _ ≤ ∫ x : T4, scale edge * invSqKer (anchor - x)
          ∂paperMeasure := by
      apply integral_mono_ae htranslated.norm hmajorant
      filter_upwards
          [compl_mem_ae_iff.mpr (paperMeasure_singleton anchor)] with x hx
      have hxanchor : x ≠ anchor := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
      have hxa : anchor ≠ x := hxanchor.symm
      exact cert.bound edge (anchor - x)
        (sub_ne_zero.mpr hxa)
    _ = scale edge * invSqKerMass := by
      rw [integral_const_mul, integral_invSqKer_sub_left]

end R324WithinHalfEdgeCertificate

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- At a completed nonempty half, the incoming boundary factor is the
actual stored edge kernel translated from the first surviving anchor. -/
theorem incomingBoundaryFactor_terminal_eq_edgeKernel
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hterminal : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : Fin m → T4) :
    res.incomingBoundaryFactor x y v =
      res.state.edges 0 (x - res.terminalIncomingAnchor v) := by
  unfold incomingBoundaryFactor residualChainEdgeFactor
  rw [if_pos res.zero_mem_activeEdgeSlots]
  have hnotReserved :
      (0 : Fin (m + 1)) ∉ res.remainingOutgoingSlots := by
    unfold remainingOutgoingSlots
    rw [hterminal]
    simp
  rw [if_neg hnotReserved]
  unfold edgeDisplacement
  have hzeroCast :
      (0 : Fin (m + 1)).castSucc = (0 : Fin (m + 2)) := by
    rfl
  rw [hzeroCast, assemble_zero,
    res.assemble_edgeSuccessor_zero_eq_terminalIncomingAnchor hactive]

/-- The outgoing boundary factor is the actual stored terminal-slot kernel
translated from the last surviving anchor. -/
theorem outgoingBoundaryFactor_terminal_eq_edgeKernel
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hterminal : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : Fin m → T4) :
    res.outgoingBoundaryFactor hactive x y v =
      res.state.edges (res.terminalOutgoingEdgeSlot hactive)
        (res.terminalOutgoingAnchor hactive v - y) := by
  unfold outgoingBoundaryFactor residualChainEdgeFactor
  rw [if_pos (res.terminalOutgoingEdgeSlot_mem_activeEdgeSlots hactive)]
  have hnotReserved :
      res.terminalOutgoingEdgeSlot hactive ∉
        res.remainingOutgoingSlots := by
    unfold remainingOutgoingSlots
    rw [hterminal]
    simp
  rw [if_neg hnotReserved]
  unfold edgeDisplacement
  rw [res.assemble_terminalOutgoing_castSucc_eq_terminalOutgoingAnchor
      hactive,
    res.edgeSuccessor_terminalOutgoingEdgeSlot_eq_last hactive,
    assemble_last]

end R324WithinHalfResidualPrefix

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)

/-- The completed left boundary coefficient is exactly the product of the
two Fourier coefficients of its actual stored boundary kernels. -/
theorem leftBoundaryModeCoefficient_eq_terminalEdgeModes
    (hleft : terminal.left.state.active.Nonempty)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4) :
    terminal.leftBoundaryModeCoefficient hleft α β vl =
      (∫ x : T4,
          charT4 α x *
            (terminal.left.state.edges 0
              (x - terminal.left.terminalIncomingAnchor
                (terminal.left.reconstruct vl)) : ℂ)
          ∂paperMeasure) *
        (∫ y : T4,
          charT4 β y *
            (terminal.left.state.edges
              (terminal.left.terminalOutgoingEdgeSlot hleft)
              (terminal.left.terminalOutgoingAnchor hleft
                (terminal.left.reconstruct vl) - y) : ℂ)
          ∂paperMeasure) := by
  unfold leftBoundaryModeCoefficient leftBoundaryModeIntegrand
  simp_rw [terminal.left.incomingBoundaryFactor_terminal_eq_edgeKernel
      terminal.left_remaining hleft,
    terminal.left.outgoingBoundaryFactor_terminal_eq_edgeKernel
      terminal.left_remaining hleft]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]

/-- Right-half analogue, with the literal modes `(-α,-β)`. -/
theorem rightBoundaryModeCoefficient_eq_terminalEdgeModes
    (hright : terminal.right.state.active.Nonempty)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    terminal.rightBoundaryModeCoefficient hright α β vr =
      (∫ z : T4,
          charT4 (-α) z *
            (terminal.right.state.edges 0
              (z - terminal.right.terminalIncomingAnchor
                (terminal.right.reconstruct vr)) : ℂ)
          ∂paperMeasure) *
        (∫ w : T4,
          charT4 (-β) w *
            (terminal.right.state.edges
              (terminal.right.terminalOutgoingEdgeSlot hright)
              (terminal.right.terminalOutgoingAnchor hright
                (terminal.right.reconstruct vr) - w) : ℂ)
          ∂paperMeasure) := by
  unfold rightBoundaryModeCoefficient rightBoundaryModeIntegrand
  simp_rw [terminal.right.incomingBoundaryFactor_terminal_eq_edgeKernel
      terminal.right_remaining hright,
    terminal.right.outgoingBoundaryFactor_terminal_eq_edgeKernel
      terminal.right_remaining hright]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]

/-- Uniform left boundary coefficient bound from an arbitrary terminal
certificate.  It is independent of the external modes and keeps the grouped
internal core entirely outside the estimate. -/
theorem norm_leftBoundaryModeCoefficient_le_terminalScale
    (hleft : terminal.left.state.active.Nonempty)
    {scale : Fin (m + 1) → ℝ}
    (cert : R324WithinHalfEdgeCertificate terminal.left.state scale)
    (α β : Z4)
    (vl : terminal.left.SurvivingCoordinate → T4) :
    ‖terminal.leftBoundaryModeCoefficient hleft α β vl‖ ≤
      scale 0 * scale (terminal.left.terminalOutgoingEdgeSlot hleft) *
        invSqKerMass ^ 2 := by
  rw [terminal.leftBoundaryModeCoefficient_eq_terminalEdgeModes
    hleft α β vl, norm_mul]
  have hin := cert.norm_integral_char_mul_edge_sub_le 0 α
    (terminal.left.terminalIncomingAnchor
      (terminal.left.reconstruct vl))
  have hout := cert.norm_integral_char_mul_edge_sub_left_le
    (terminal.left.terminalOutgoingEdgeSlot hleft) β
    (terminal.left.terminalOutgoingAnchor hleft
      (terminal.left.reconstruct vl))
  calc
    ‖∫ x : T4,
          charT4 α x *
            (terminal.left.state.edges 0
              (x - terminal.left.terminalIncomingAnchor
                (terminal.left.reconstruct vl)) : ℂ)
          ∂paperMeasure‖ *
        ‖∫ y : T4,
          charT4 β y *
            (terminal.left.state.edges
              (terminal.left.terminalOutgoingEdgeSlot hleft)
              (terminal.left.terminalOutgoingAnchor hleft
                (terminal.left.reconstruct vl) - y) : ℂ)
          ∂paperMeasure‖ ≤
        (scale 0 * invSqKerMass) *
          (scale (terminal.left.terminalOutgoingEdgeSlot hleft) *
            invSqKerMass) :=
      calc
        _ ≤ (scale 0 * invSqKerMass) *
              ‖∫ y : T4,
                charT4 β y *
                  (terminal.left.state.edges
                    (terminal.left.terminalOutgoingEdgeSlot hleft)
                    (terminal.left.terminalOutgoingAnchor hleft
                      (terminal.left.reconstruct vl) - y) : ℂ)
                ∂paperMeasure‖ :=
          mul_le_mul_of_nonneg_right hin (norm_nonneg _)
        _ ≤ (scale 0 * invSqKerMass) *
              (scale (terminal.left.terminalOutgoingEdgeSlot hleft) *
                invSqKerMass) :=
          mul_le_mul_of_nonneg_left hout
            (mul_nonneg (cert.scale_pos 0).le invSqKerMass_nonneg)
    _ = scale 0 * scale
          (terminal.left.terminalOutgoingEdgeSlot hleft) *
        invSqKerMass ^ 2 := by ring

/-- Uniform right boundary coefficient bound from its terminal
certificate. -/
theorem norm_rightBoundaryModeCoefficient_le_terminalScale
    (hright : terminal.right.state.active.Nonempty)
    {scale : Fin (m + 1) → ℝ}
    (cert : R324WithinHalfEdgeCertificate terminal.right.state scale)
    (α β : Z4)
    (vr : terminal.right.SurvivingCoordinate → T4) :
    ‖terminal.rightBoundaryModeCoefficient hright α β vr‖ ≤
      scale 0 * scale (terminal.right.terminalOutgoingEdgeSlot hright) *
        invSqKerMass ^ 2 := by
  rw [terminal.rightBoundaryModeCoefficient_eq_terminalEdgeModes
    hright α β vr, norm_mul]
  have hin := cert.norm_integral_char_mul_edge_sub_le 0 (-α)
    (terminal.right.terminalIncomingAnchor
      (terminal.right.reconstruct vr))
  have hout := cert.norm_integral_char_mul_edge_sub_left_le
    (terminal.right.terminalOutgoingEdgeSlot hright) (-β)
    (terminal.right.terminalOutgoingAnchor hright
      (terminal.right.reconstruct vr))
  calc
    ‖∫ z : T4,
          charT4 (-α) z *
            (terminal.right.state.edges 0
              (z - terminal.right.terminalIncomingAnchor
                (terminal.right.reconstruct vr)) : ℂ)
          ∂paperMeasure‖ *
        ‖∫ w : T4,
          charT4 (-β) w *
            (terminal.right.state.edges
              (terminal.right.terminalOutgoingEdgeSlot hright)
              (terminal.right.terminalOutgoingAnchor hright
                (terminal.right.reconstruct vr) - w) : ℂ)
          ∂paperMeasure‖ ≤
        (scale 0 * invSqKerMass) *
          (scale (terminal.right.terminalOutgoingEdgeSlot hright) *
            invSqKerMass) :=
      calc
        _ ≤ (scale 0 * invSqKerMass) *
              ‖∫ w : T4,
                charT4 (-β) w *
                  (terminal.right.state.edges
                    (terminal.right.terminalOutgoingEdgeSlot hright)
                    (terminal.right.terminalOutgoingAnchor hright
                      (terminal.right.reconstruct vr) - w) : ℂ)
                ∂paperMeasure‖ :=
          mul_le_mul_of_nonneg_right hin (norm_nonneg _)
        _ ≤ (scale 0 * invSqKerMass) *
              (scale (terminal.right.terminalOutgoingEdgeSlot hright) *
                invSqKerMass) :=
          mul_le_mul_of_nonneg_left hout
            (mul_nonneg (cert.scale_pos 0).le invSqKerMass_nonneg)
    _ = scale 0 * scale
          (terminal.right.terminalOutgoingEdgeSlot hright) *
        invSqKerMass ^ 2 := by ring

/-! ## Stored-certificate API for certified traces -/

/-- The requested left trace-level interface.  The two scales are exactly
the incoming slot `0` and the outgoing terminal slot stored at the end of
the Phase-A trace. -/
theorem norm_leftBoundaryModeCoefficient_le_storedTerminalScale
    {leftRes : R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes : R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4)
    (vl : leftTrace.terminalPrefix.SurvivingCoordinate → T4) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    ‖terminal.leftBoundaryModeCoefficient hleft α β vl‖ ≤
      leftTrace.terminalScale 0 *
        leftTrace.terminalScale
          (leftTrace.terminalPrefix.terminalOutgoingEdgeSlot hleft) *
        invSqKerMass ^ 2 := by
  dsimp only
  exact
    (R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace).norm_leftBoundaryModeCoefficient_le_terminalScale
        hleft leftTrace.terminalCertificate α β vl

/-- Right trace-level analogue. -/
theorem norm_rightBoundaryModeCoefficient_le_storedTerminalScale
    {leftRes : R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes : R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4)
    (vr : rightTrace.terminalPrefix.SurvivingCoordinate → T4) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    ‖terminal.rightBoundaryModeCoefficient hright α β vr‖ ≤
      rightTrace.terminalScale 0 *
        rightTrace.terminalScale
          (rightTrace.terminalPrefix.terminalOutgoingEdgeSlot hright) *
        invSqKerMass ^ 2 := by
  dsimp only
  exact
    (R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace).norm_rightBoundaryModeCoefficient_le_terminalScale
        hright rightTrace.terminalCertificate α β vr

end R324TwoHalfTerminalData

end

end Anderson4D
