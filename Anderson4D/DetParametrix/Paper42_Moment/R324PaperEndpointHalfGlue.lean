import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfEndpointTerminalGeometry
import Anderson4D.DetParametrix.Paper42_Moment.R324OutgoingExceptionalTerminalBound
import Anderson4D.DetParametrix.Paper42_Moment.R324CertificateScaledPrimitiveDefect
import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalBoundaryLegFourier
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedRoutedEndpointBudget

/-!
# Paper Step 4: the two endpoint operations of one half-chain

Paper §4.2, Step 4 integrates the two external variables of a half-chain
only after the signed primitive-interval removals are complete.  This file is
the small common seam for those endpoint operations.  It deliberately does
not introduce a route, trace, or scale ledger.

There are two ingredients.

* For a completed direct half-chain, both genuine boundary factors are
  Fourier-integrated exactly.  The norm is taken only after both integrals.
* For a retained outgoing shortcut terminal, the endpoint-stop geometry is
  fed directly to the existing fixed-terminal ordinary-`J` theorem.  Thus the
  shortcut branch pays exactly one ordinary-versus-inserted sacrifice, while
  a direct endpoint has sacrifice one.

The remaining global splice is intentionally not hidden here: its source
density must first be identified with the separated endpoint form below (or
with the retained-terminal form) after all interval coordinates have been
removed.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open SmoothCutoff

/-! ## Exact separated two-endpoint operation -/

/-- The two anchors of one half-chain, incoming first and outgoing second.
Each pair consists of the ordinary endpoint anchor and the subtraction
anchor used only in the shortcut branch. -/
abbrev R324PaperHalfEndpointAnchors := Fin 2 → T4 × T4

/-- The two paper endpoint cases of one half-chain. -/
abbrev R324PaperHalfEndpointCases := Fin 2 → R324EndpointReductionCase

/-- The Boolean endpoint-kernel flag represented by a paper endpoint case. -/
def r324PaperEndpointCaseShortcut : R324EndpointReductionCase → Bool
  | .directFourier => false
  | .insertedSacrifice => true

/-- The endpoint-separated signed density for one half-chain.  `core` is the
complete signed primitive fibre left after Steps 1--3; in particular this
definition does not move a norm inside that fibre. -/
def r324PaperHalfEndpointIntegrand
    (incomingMode outgoingMode : Z4)
    (anchors : R324PaperHalfEndpointAnchors)
    (cases : R324PaperHalfEndpointCases)
    (core : ℂ) (x y : T4) : ℂ :=
  (charT4 incomingMode x *
      r324IncomingEndpointKernel
        (anchors 0).1 (anchors 0).2
        (r324PaperEndpointCaseShortcut (cases 0)) x) *
    (charT4 outgoingMode y *
      r324OutgoingEndpointKernel
        (anchors 1).1 (anchors 1).2
        (r324PaperEndpointCaseShortcut (cases 1)) y) *
    core

/-- Both external integrations are evaluated before any norm is taken. -/
theorem integral_r324PaperHalfEndpointIntegrand
    (incomingMode outgoingMode : Z4)
    (anchors : R324PaperHalfEndpointAnchors)
    (cases : R324PaperHalfEndpointCases)
    (core : ℂ) :
    (∫ x : T4, ∫ y : T4,
        r324PaperHalfEndpointIntegrand
          incomingMode outgoingMode anchors cases core x y
        ∂paperMeasure ∂paperMeasure) =
      r324EndpointCoefficient incomingMode
          (anchors 0).1 (anchors 0).2
          (r324PaperEndpointCaseShortcut (cases 0)) *
        (r324EndpointCoefficient outgoingMode
          (anchors 1).1 (anchors 1).2
          (r324PaperEndpointCaseShortcut (cases 1)) * core) := by
  let A : T4 → ℂ := fun x =>
    charT4 incomingMode x *
      r324IncomingEndpointKernel
        (anchors 0).1 (anchors 0).2
        (r324PaperEndpointCaseShortcut (cases 0)) x
  let B : T4 → ℂ := fun y =>
    charT4 outgoingMode y *
      r324OutgoingEndpointKernel
        (anchors 1).1 (anchors 1).2
        (r324PaperEndpointCaseShortcut (cases 1)) y
  let a : ℂ :=
    r324EndpointCoefficient incomingMode
      (anchors 0).1 (anchors 0).2
      (r324PaperEndpointCaseShortcut (cases 0))
  let b : ℂ :=
    r324EndpointCoefficient outgoingMode
      (anchors 1).1 (anchors 1).2
      (r324PaperEndpointCaseShortcut (cases 1))
  change (∫ x : T4, ∫ y : T4, A x * B y * core
      ∂paperMeasure ∂paperMeasure) = a * (b * core)
  have hy (x : T4) :
      (∫ y : T4, A x * B y * core ∂paperMeasure) =
        A x * b * core := by
    rw [integral_mul_const, integral_const_mul]
    dsimp only [B, b]
    rw [integral_char_mul_r324OutgoingEndpointKernel]
  calc
    (∫ x : T4, ∫ y : T4, A x * B y * core
        ∂paperMeasure ∂paperMeasure) =
        ∫ x : T4, A x * b * core ∂paperMeasure := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hy
    _ = (∫ x : T4, A x ∂paperMeasure) * b * core := by
          rw [integral_mul_const, integral_mul_const]
    _ = a * (b * core) := by
          dsimp only [A, a]
          rw [integral_char_mul_r324IncomingEndpointKernel]
          ring

/-- The first norm occurs after the two exact endpoint integrations. -/
theorem norm_integral_r324PaperHalfEndpointIntegrand
    (incomingMode outgoingMode : Z4)
    (anchors : R324PaperHalfEndpointAnchors)
    (cases : R324PaperHalfEndpointCases)
    (core : ℂ) :
    ‖∫ x : T4, ∫ y : T4,
        r324PaperHalfEndpointIntegrand
          incomingMode outgoingMode anchors cases core x y
        ∂paperMeasure ∂paperMeasure‖ =
      ‖r324EndpointCoefficient incomingMode
          (anchors 0).1 (anchors 0).2
          (r324PaperEndpointCaseShortcut (cases 0))‖ *
        ‖r324EndpointCoefficient outgoingMode
          (anchors 1).1 (anchors 1).2
          (r324PaperEndpointCaseShortcut (cases 1))‖ *
        ‖core‖ := by
  rw [integral_r324PaperHalfEndpointIntegrand]
  simp only [norm_mul]
  ring

/-! ## Case-faithful ordinary-`J` sacrifice -/

/-- The product of the two genuine ordinary-versus-inserted costs of one
half-chain.  A direct endpoint contributes exactly one. -/
def r324PaperHalfEndpointSacrifice
    (ε : ℝ) (cases : R324PaperHalfEndpointCases) : ℝ :=
  r324EndpointPrimitiveSacrifice ε (cases 0) *
    r324EndpointPrimitiveSacrifice ε (cases 1)

theorem r324PaperHalfEndpointSacrifice_nonneg
    (ε : ℝ) (cases : R324PaperHalfEndpointCases) :
    0 ≤ r324PaperHalfEndpointSacrifice ε cases := by
  exact mul_nonneg
    (r324EndpointPrimitiveSacrifice_nonneg ε (cases 0))
    (r324EndpointPrimitiveSacrifice_nonneg ε (cases 1))

/-- In the genuinely direct/direct branch the primitive sacrifice is
definitionally one: no hidden uniform `ε⁻²` is charged. -/
theorem r324PaperHalfEndpointSacrifice_eq_one_of_direct
    (ε : ℝ) (cases : R324PaperHalfEndpointCases)
    (hcases : ∀ i, cases i = .directFourier) :
    r324PaperHalfEndpointSacrifice ε cases = 1 := by
  simp [r324PaperHalfEndpointSacrifice, hcases,
    r324EndpointPrimitiveSacrifice]

/-- A single paired terminal endpoint contributes exactly one `ε⁻²`
ordinary-`J` sacrifice. -/
theorem r324PaperHalfEndpointSacrifice_eq_invSq_of_outgoing_inserted
    (ε : ℝ) (cases : R324PaperHalfEndpointCases)
    (hincoming : cases 0 = .directFourier)
    (houtgoing : cases 1 = .insertedSacrifice) :
    r324PaperHalfEndpointSacrifice ε cases = ε⁻¹ ^ (2 : ℕ) := by
  simp [r324PaperHalfEndpointSacrifice, hincoming, houtgoing,
    r324EndpointPrimitiveSacrifice]

/-- Pointwise analytic bridge used after a paired terminal collapse: the
ordinary primitive majorant is converted to the inserted majorant at the
single outgoing endpoint's case cost. -/
theorem r324PaperShortcutPrimitiveMajorant_le_sacrifice_mul_inserted
    (C lam supportConstant : ℝ) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) (z : T4) :
    primitiveKernelMajorant C lam ε supportConstant n z ≤
      r324EndpointPrimitiveSacrifice
          ε .insertedSacrifice *
        primitiveInsertedMajorant
          C lam ε supportConstant n z := by
  simpa [r324EndpointCasePrimitiveMajorant] using
    r324EndpointCasePrimitiveMajorant_le_sacrifice_mul_inserted
      R324EndpointReductionCase.insertedSacrifice
      C lam supportConstant n hε z

/-- At most two exceptional endpoints occur in one half, hence the sharp
uniform half-chain loss is `ε⁻⁴`.  This does not charge a direct endpoint:
its factor remains definitionally one in
`r324PaperHalfEndpointSacrifice`. -/
theorem r324PaperHalfEndpointSacrifice_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (cases : R324PaperHalfEndpointCases) :
    r324PaperHalfEndpointSacrifice ε cases ≤
      ε⁻¹ ^ (4 : ℕ) := by
  have h0 := r324EndpointPrimitiveSacrifice_le hε hε1 (cases 0)
  have h1 := r324EndpointPrimitiveSacrifice_le hε hε1 (cases 1)
  have hnonneg :=
    r324EndpointPrimitiveSacrifice_nonneg ε (cases 1)
  have hinv : 0 ≤ ε⁻¹ ^ (2 : ℕ) := sq_nonneg ε⁻¹
  unfold r324PaperHalfEndpointSacrifice
  calc
    r324EndpointPrimitiveSacrifice ε (cases 0) *
          r324EndpointPrimitiveSacrifice ε (cases 1) ≤
        ε⁻¹ ^ (2 : ℕ) * ε⁻¹ ^ (2 : ℕ) :=
      mul_le_mul h0 h1 hnonneg hinv
    _ = ε⁻¹ ^ (4 : ℕ) := by ring

/-! ## Actual completed direct half-chain -/

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- A completed half-chain whose two boundary edges are still free has the
exact separated two-endpoint form.  This is the direct/direct paper branch,
with no `ε`-loss and no norm before either Fourier integration. -/
theorem integral_two_directBoundaryFactors_eq
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hremaining : res.remaining = [])
    (hactive : res.state.active.Nonempty)
    (hincoming : res.state.edges 0 = greenFn)
    (houtgoing :
      res.state.edges (res.terminalOutgoingEdgeSlot hactive) =
        greenFn)
    (incomingMode outgoingMode : Z4)
    (v : Fin m → T4) (core : ℂ) :
    (∫ x : T4, ∫ y : T4,
        (charT4 incomingMode x *
          (res.incomingBoundaryFactor x y v : ℂ)) *
        (charT4 outgoingMode y *
          (res.outgoingBoundaryFactor hactive x y v : ℂ)) *
        core
      ∂paperMeasure ∂paperMeasure) =
      translatedGreenMode incomingMode
          (res.terminalIncomingAnchor v) *
        (translatedGreenMode outgoingMode
          (res.terminalOutgoingAnchor hactive v) * core) := by
  simp_rw [
    res.incomingBoundaryFactor_eq_incomingEndpointKernel
      hremaining hactive hincoming,
    res.outgoingBoundaryFactor_eq_outgoingEndpointKernel
      hremaining hactive houtgoing]
  let anchors : R324PaperHalfEndpointAnchors := ![
    (res.terminalIncomingAnchor v,
      res.terminalIncomingAnchor v),
    (res.terminalOutgoingAnchor hactive v,
      res.terminalOutgoingAnchor hactive v)]
  let cases : R324PaperHalfEndpointCases := fun _ =>
    R324EndpointReductionCase.directFourier
  have h := integral_r324PaperHalfEndpointIntegrand
    incomingMode outgoingMode anchors cases core
  simpa [r324PaperHalfEndpointIntegrand, anchors, cases,
    r324PaperEndpointCaseShortcut, r324EndpointCoefficient] using h

/-! ## Actual retained outgoing-shortcut terminal -/

namespace R324WithinHalfEndpointTerminalGeometry

/-- Exact outgoing shortcut operation specialized to the endpoint-stop
driver.  Endpoint Fourier integration, internal primitive integration, and
gap integration all occur before the resulting ordinary phase defect is
exposed. -/
theorem integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := ρ) (lam := lam) (ε := ε) pairing)
    (k : Z4) (x first : T4) (outer : ℂ)
    (hint :
      ∀ (gap : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder
                data.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder
                data.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.terminalData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder
                data.terminalData.terminal.2)
              κB.1 data.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder
                  data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (∫ gap : T4,
        (lamEps lam ε : ℂ) ^
            (2 * residualBlockOrder
              data.terminalData.terminal.2) *
          (∫ r : Fin (2 * residualBlockOrder
                data.terminalData.terminal.2 - 2) → T4,
            ∫ y : T4,
              charT4 k y *
                ((data.terminalContext.rawLocalIntegrand
                  ρ ε (x - y)
                  (fun j =>
                    primitiveAssemble
                      (residualBlockOrder
                        data.terminalData.terminal.2)
                      data.terminalContext.one_le_blockOrder
                      first (first - gap) r j - y) : ℂ) *
                  outer)
              ∂paperMeasure
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure) =
      ((data.terminalContext.state.edges
            (r324WithinHalfPredecessorSlot
              data.terminalContext.state
              data.terminalContext.step)
            (x - first) : ℝ) : ℂ) *
        (paperSecondOrderModeDecay k : ℂ) * charT4 k first *
        (∫ gap : T4,
          (primitiveKernelDiff ρ lam ε
              (residualBlockOrder
                data.terminalData.terminal.2)
              data.terminalContext.one_le_blockOrder
              data.terminalContext.internalEdges gap : ℂ) *
            (charT4 (-k) gap - 1)
          ∂paperMeasure) * outer := by
  exact
    data.terminalContext
      |>.integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
        ρ lam ε data.terminalContext_outgoing_eq_greenFn
        k x first outer hint

/-- Certificate-scaled numerical form of the retained outgoing shortcut.
The exact endpoint, internal-coordinate, and terminal-gap integrations are
performed first by the preceding theorem.  Only then is the norm bounded by
the ordinary Proposition 4.1 majorant, retaining the product of the actual
internal edge scales exactly once. -/
theorem norm_integral_lamEps_pow_terminalOutgoingFourier_gap_le_scaled
    {C supportConstant : ℝ}
    (data :
      R324WithinHalfEndpointTerminalGeometry
        (ρ := ρ) (lam := lam) (ε := ε) pairing)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate
        data.terminalContext.state scale)
    (k : Z4) (x first : T4) (outer : ℂ)
    (hint :
      ∀ (gap : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder
                data.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder
                data.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.terminalData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder
                data.terminalData.terminal.2)
              κB.1 data.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder
                  data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hε : 0 < ε) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hprop :
      ∀ (H : Fin (2 * residualBlockOrder
            data.terminalData.terminal.2 - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput
            (residualBlockOrder data.terminalData.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder data.terminalData.terminal.2)
              data.terminalContext.one_le_blockOrder H
              supportConstant C) :
    ‖∫ gap : T4,
        (lamEps lam ε : ℂ) ^
            (2 * residualBlockOrder
              data.terminalData.terminal.2) *
          (∫ r : Fin (2 * residualBlockOrder
                data.terminalData.terminal.2 - 2) → T4,
            ∫ y : T4,
              charT4 k y *
                ((data.terminalContext.rawLocalIntegrand
                  ρ ε (x - y)
                  (fun j =>
                    primitiveAssemble
                      (residualBlockOrder
                        data.terminalData.terminal.2)
                      data.terminalContext.one_le_blockOrder
                      first (first - gap) r j - y) : ℂ) *
                  outer)
              ∂paperMeasure
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure‖ ≤
      |data.terminalContext.state.edges
          (r324WithinHalfPredecessorSlot
            data.terminalContext.state data.terminalContext.step)
          (x - first)| *
        paperSecondOrderModeDecay k *
        (2 * r324WithinHalfInternalEdgeScaleProduct
            data.terminalContext scale *
          ∫ gap : T4,
            primitiveKernelMajorant
              C lam ε supportConstant
              (residualBlockOrder
                data.terminalData.terminal.2) gap
            ∂paperMeasure) * ‖outer‖ := by
  have hdefect :=
    norm_incomingExceptionalPrimitiveDefect_le_scaled_of_certificate
      data.terminalContext scale certificate hε hC hlam hprop k
  rw [data.integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
    k x first outer hint]
  change
    ‖((data.terminalContext.state.edges
          (r324WithinHalfPredecessorSlot
            data.terminalContext.state data.terminalContext.step)
          (x - first) : ℝ) : ℂ) *
        (paperSecondOrderModeDecay k : ℂ) * charT4 k first *
        incomingExceptionalPrimitiveDefect ρ lam ε
          (residualBlockOrder data.terminalData.terminal.2)
          data.terminalContext.one_le_blockOrder
          data.terminalContext.internalEdges k * outer‖ ≤ _
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperSecondOrderModeDecay_nonneg k), norm_charT4,
    mul_one]
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdefect
        (mul_nonneg (abs_nonneg _)
          (paperSecondOrderModeDecay_nonneg k)))
      (norm_nonneg outer)

end R324WithinHalfEndpointTerminalGeometry

end R324WithinHalfResidualPrefix

end

end Anderson4D
