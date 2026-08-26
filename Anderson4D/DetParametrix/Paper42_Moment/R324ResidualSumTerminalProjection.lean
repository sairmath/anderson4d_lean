import Anderson4D.DetParametrix.Paper42_Moment.R324ConcretePhaseATraceAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324WholeRootPointwiseNormalization

/-!
# Terminal projection of the exact R-324 residual primitive sum

The within-half certified traces delete only coordinates belonging to the
within-half extraction blocks.  Consequently the remaining cross-cut
primitive sum reads only coordinates which survive both certified traces.
This file records that fact before any norm or estimate is taken, and
transports the resulting exact physical core to the initial nested-cross
carrier.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- Regard a coordinate surviving the whole certified trace as a coordinate
of the prefix at which the trace starts. -/
def terminalCoordinateEmbedding
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale) :
    trace.terminalPrefix.SurvivingCoordinate →
      res.SurvivingCoordinate :=
  match trace with
  | .terminal .. => fun i => i
  | @R324WithinHalfCertifiedAnalyticTrace.step
      _ _ _ _ _
      current head tail hremaining _ _ _ _ next =>
      fun i =>
        current.postSurvivingCoordinate
          head tail hremaining
          (next.terminalCoordinateEmbedding i)

@[simp]
theorem terminalCoordinateEmbedding_val
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale)
    (i : trace.terminalPrefix.SurvivingCoordinate) :
    (trace.terminalCoordinateEmbedding i).1 = i.1 := by
  induction trace with
  | terminal terminal scale hremaining certificate =>
      rfl
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      change
        (current.postSurvivingCoordinate
          head tail hremaining
          (next.terminalCoordinateEmbedding i)).1 = i.1
      exact ih i

@[simp]
theorem terminalProjection_apply
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale)
    (v : res.SurvivingCoordinate → T4)
    (i : trace.terminalPrefix.SurvivingCoordinate) :
    trace.terminalProjection v i =
      v (trace.terminalCoordinateEmbedding i) := by
  induction trace with
  | terminal terminal scale hremaining certificate =>
      rfl
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      change
        next.terminalProjection
            (current.splitSurvivingPiMeasurableEquiv
              head tail hremaining v).2 i =
          v
            (current.postSurvivingCoordinate
              head tail hremaining
              (next.terminalCoordinateEmbedding i))
      rw [ih]
      exact
        current.splitSurvivingPiMeasurableEquiv_apply_snd
          head tail hremaining v
          (next.terminalCoordinateEmbedding i)

/-- Reconstruction at every terminal coordinate is unchanged by the full
certified terminal projection. -/
theorem reconstruct_terminalProjection
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale)
    (v : res.SurvivingCoordinate → T4)
    (i : trace.terminalPrefix.SurvivingCoordinate) :
    res.reconstruct v i.1 =
      trace.terminalPrefix.reconstruct
        (trace.terminalProjection v) i.1 := by
  calc
    res.reconstruct v i.1 =
        res.reconstruct v
          (trace.terminalCoordinateEmbedding i).1 := by
      exact congrArg (res.reconstruct v)
        (trace.terminalCoordinateEmbedding_val i).symm
    _ = v (trace.terminalCoordinateEmbedding i) :=
      res.reconstruct_surviving
        v (trace.terminalCoordinateEmbedding i)
    _ = trace.terminalProjection v i :=
      (trace.terminalProjection_apply v i).symm
    _ =
        trace.terminalPrefix.reconstruct
          (trace.terminalProjection v) i.1 :=
      (trace.terminalPrefix.reconstruct_surviving
        (trace.terminalProjection v) i).symm

end R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

/-! ## Coordinate support of the residual primitive sum -/

/-- One complete primitive covariance factor reads only coordinates in its
ambient primitive block. -/
theorem primitivePartitionBlockCovarianceFactor_congr_on
    {n : ℕ} {κ : PartialPairing (Fin n)}
    (ρ : SmoothCutoff) (ε : ℝ)
    (P : PrimitiveBlockPartition κ)
    (B : PrimitivePartitionBlockIndex P)
    (σ :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder B.1)) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder B.1)})
    (v w : Fin n → T4)
    (hvw : ∀ i ∈ B.1, v i = w i) :
    primitivePartitionBlockCovarianceFactor
        ρ ε P B σ v =
      primitivePartitionBlockCovarianceFactor
        ρ ε P B σ w := by
  unfold primitivePartitionBlockCovarianceFactor
    primitiveCovarianceProduct
  apply Finset.prod_congr rfl
  intro i hi
  let e :=
    residualPrimitiveBlockOrderIso
      κ B.1 (P.block_fullyPaired B.2)
  change
    ρ.etaEpsT4 ε
        (v (e i).1 - v (e (σ.1 i)).1) =
      ρ.etaEpsT4 ε
        (w (e i).1 - w (e (σ.1 i)).1)
  rw [
    hvw (e i).1 (e i).2,
    hvw (e (σ.1 i)).1 (e (σ.1 i)).2]

/-- The complete primitive-pairing sum on a block reads only coordinates in
that block. -/
theorem r324PrimitivePartitionBlockSum_congr_on
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (v w : Fin (2 * m) → T4)
    (hvw : ∀ i ∈ B, v i = w i) :
    r324PrimitivePartitionBlockSum
        ρ ε κp κm π B v =
      r324PrimitivePartitionBlockSum
        ρ ε κp κm π B w := by
  unfold r324PrimitivePartitionBlockSum
  split_ifs with hB
  · apply Fintype.sum_congr
    intro σ
    exact
      primitivePartitionBlockCovarianceFactor_congr_on
        ρ ε
        (momentPrimitiveBlockPartition κp κm π)
        ⟨B, hB⟩ σ v w hvw
  · rfl

/-- The remaining exact primitive sum depends only on the doubled residual
carrier. -/
theorem r324ResidualPrimitiveSumProduct_congr_on_active
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v w : Fin (2 * m) → T4)
    (hvw :
      ∀ i ∈ momentResidualActive κp κm,
        v i = w i) :
    r324ResidualPrimitiveSumProduct
        ρ ε κp κm π v =
      r324ResidualPrimitiveSumProduct
        ρ ε κp κm π w := by
  unfold r324ResidualPrimitiveSumProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro B hB
  apply r324PrimitivePartitionBlockSum_congr_on
  intro i hi
  exact
    hvw i
      (momentResidualCollapseBlock_subset_active
        (mem_nonemptyMomentResidualCollapseBlocks.mp hB).1 hi)

/-! ## Two-half certified terminal projection -/

/-- Reconstruct a doubled ambient tuple at the starting prefixes of two
certified within-half traces. -/
def r324TwoHalfRootDoubledReconstruct
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp)
    (rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm)
    (p :
      (leftRes.SurvivingCoordinate → T4) ×
        (rightRes.SurvivingCoordinate → T4)) :
    Fin (2 * m) → T4 :=
  fun k =>
    match (momentDoubleFinEquiv m).symm k with
    | Sum.inl i => leftRes.reconstruct p.1 i
    | Sum.inr j => rightRes.reconstruct p.2 j

namespace R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftScale rightScale : Fin (m + 1) → ℝ}

/-- On the doubled residual carrier, reconstruction at the roots of two
certified traces is exactly reconstruction from their terminal
projections. -/
theorem r324TwoHalfRootDoubledReconstruct_eq_terminal_on_active
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        leftRes leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        rightRes rightScale)
    (p :
      (leftRes.SurvivingCoordinate → T4) ×
        (rightRes.SurvivingCoordinate → T4))
    (k : Fin (2 * m))
    (hk : k ∈ momentResidualActive κp κm) :
    r324TwoHalfRootDoubledReconstruct leftRes rightRes p k =
      (R324TwoHalfTerminalData.ofCertifiedTraces
        leftTrace rightTrace).terminalDoubledReconstruct
          (leftTrace.terminalProjection p.1,
            rightTrace.terminalProjection p.2) k := by
  by_cases hleft : k.val < m
  · obtain ⟨i, hi, hki⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive
        hk hleft
    subst k
    let i' :
        leftTrace.terminalPrefix.SurvivingCoordinate :=
      ⟨i, by
        rw [
          leftTrace.terminalPrefix.active_eq_finalActive_of_processed_eq_schedule
            leftTrace.terminalPrefix_processed_eq_schedule]
        exact hi⟩
    unfold r324TwoHalfRootDoubledReconstruct
      R324TwoHalfTerminalData.terminalDoubledReconstruct
    rw [momentDoubleFinEquiv_symm_leftMomentIndex]
    exact leftTrace.reconstruct_terminalProjection p.1 i'
  · obtain ⟨j, hj, hkj⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive
        hk (by omega)
    subst k
    let j' :
        rightTrace.terminalPrefix.SurvivingCoordinate :=
      ⟨j, by
        rw [
          rightTrace.terminalPrefix.active_eq_finalActive_of_processed_eq_schedule
            rightTrace.terminalPrefix_processed_eq_schedule]
        exact hj⟩
    unfold r324TwoHalfRootDoubledReconstruct
      R324TwoHalfTerminalData.terminalDoubledReconstruct
    rw [momentDoubleFinEquiv_symm_rightMomentIndex]
    exact rightTrace.reconstruct_terminalProjection p.2 j'

/-- **Exact terminal-projection theorem for the residual primitive sum.**

The cross-cut primitive factor at the genuine two-half root reads only the
terminal projections of the two certified within-half traces. -/
theorem r324ResidualPrimitiveSumProduct_eq_terminalProjection
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        leftRes leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        rightRes rightScale)
    (π : κp.singles ≃ κm.singles)
    (p :
      (leftRes.SurvivingCoordinate → T4) ×
        (rightRes.SurvivingCoordinate → T4)) :
    r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        (r324TwoHalfRootDoubledReconstruct
          leftRes rightRes p) =
      r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        ((R324TwoHalfTerminalData.ofCertifiedTraces
          leftTrace rightTrace).terminalDoubledReconstruct
            (leftTrace.terminalProjection p.1,
              rightTrace.terminalProjection p.2)) := by
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro k hk
  exact
    leftTrace.r324TwoHalfRootDoubledReconstruct_eq_terminal_on_active
      rightTrace p k hk

/-- Complex-valued form used directly inside the physical integrals. -/
theorem r324ResidualPrimitiveSumProduct_complex_eq_terminalProjection
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        leftRes leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        rightRes rightScale)
    (π : κp.singles ≃ κm.singles)
    (p :
      (leftRes.SurvivingCoordinate → T4) ×
        (rightRes.SurvivingCoordinate → T4)) :
    (r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        (r324TwoHalfRootDoubledReconstruct
          leftRes rightRes p) : ℂ) =
      (r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        ((R324TwoHalfTerminalData.ofCertifiedTraces
          leftTrace rightTrace).terminalDoubledReconstruct
            (leftTrace.terminalProjection p.1,
              rightTrace.terminalProjection p.2)) : ℂ) := by
  exact congrArg (fun t : ℝ => (t : ℂ))
    (leftTrace.r324ResidualPrimitiveSumProduct_eq_terminalProjection
      rightTrace π p)

end R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

/-! ## Exact terminal and nested residual-sum cores -/

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)

/-- The exact residual primitive sum on the completed two-half carrier. -/
def residualSumCrossFactor
    (π : κp.singles ≃ κm.singles)
    (vl : terminal.left.SurvivingCoordinate → T4)
    (vr : terminal.right.SurvivingCoordinate → T4) : ℂ :=
  (r324ResidualPrimitiveSumProduct
    ρ ε κp κm π
    (terminal.terminalDoubledReconstruct (vl, vr)) : ℂ)

/-- The completed two-half physical core with the exact residual primitive
sum retained as a signed factor. -/
def terminalResidualSumPhysicalCore
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) : ℂ :=
  (terminal.left.residualIntegrand ρ ε x y
      (terminal.left.reconstruct p.1) : ℂ) *
    (terminal.right.residualIntegrand ρ ε z w
      (terminal.right.reconstruct p.2) : ℂ) *
    terminal.residualSumCrossFactor π p.1 p.2

/-- Lossless reindexing of the exact terminal residual-sum core onto the
literal initial nested-cross carrier. -/
def initialNestedResidualSumPhysicalCore
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4)
    (v : terminal.NestedCoordinate π → T4) : ℂ :=
  terminal.terminalResidualSumPhysicalCore π x y z w
    ((terminal.terminalProductPiMeasurableEquivNested π).symm v)

@[simp]
theorem initialNestedResidualSumPhysicalCore_reindex
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    terminal.initialNestedResidualSumPhysicalCore
        π x y z w
        (terminal.terminalProductPiMeasurableEquivNested π p) =
      terminal.terminalResidualSumPhysicalCore
        π x y z w p := by
  unfold initialNestedResidualSumPhysicalCore
  rw [MeasurableEquiv.symm_apply_apply]

/-- Exact measure-preserving transport of the signed residual-sum core to
the initial nested-cross coordinate space. -/
theorem integral_terminalResidualSumPhysicalCore_eq_initialNested
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4) :
    (∫ p,
        terminal.terminalResidualSumPhysicalCore
          π x y z w p
        ∂((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate => paperMeasure))) =
      ∫ v,
        terminal.initialNestedResidualSumPhysicalCore
          π x y z w v
        ∂(Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure) := by
  have hp :=
    terminal.measurePreserving_terminalProductPiMeasurableEquivNested π
  calc
    _ =
        ∫ p,
          terminal.initialNestedResidualSumPhysicalCore
            π x y z w
            (terminal.terminalProductPiMeasurableEquivNested π p)
          ∂((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure)) := by
      apply integral_congr_ae
      filter_upwards with p
      exact
        (terminal.initialNestedResidualSumPhysicalCore_reindex
          π x y z w p).symm
    _ = _ := by
      simpa only [Function.comp_apply] using
        hp.integral_comp'
          (fun v =>
            terminal.initialNestedResidualSumPhysicalCore
              π x y z w v)

/-- Fubini identifies the exact terminal product-space core with the
right-then-left iterated integral.  Integrability is kept as an explicit
endpoint-dependent hypothesis. -/
theorem integral_terminalResidualSumPhysicalCore_eq_iterated
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4)
    (hintegrable :
      Integrable
        (terminal.terminalResidualSumPhysicalCore
          π x y z w)
        ((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate =>
              paperMeasure))) :
    (∫ p,
        terminal.terminalResidualSumPhysicalCore
          π x y z w p
        ∂((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate =>
              paperMeasure))) =
      ∫ vr :
          terminal.right.SurvivingCoordinate → T4,
        ((terminal.right.residualIntegrand
            ρ ε z w
            (terminal.right.reconstruct vr) : ℂ) *
          (∫ vl :
              terminal.left.SurvivingCoordinate → T4,
            ((terminal.left.residualIntegrand
                ρ ε x y
                (terminal.left.reconstruct vl) : ℂ) *
              terminal.residualSumCrossFactor π vl vr)
            ∂Measure.pi fun _ => paperMeasure))
        ∂Measure.pi fun _ => paperMeasure := by
  letI :
      IsFiniteMeasure
        (Measure.pi fun _ :
          terminal.left.SurvivingCoordinate =>
            paperMeasure) :=
    Measure.pi.instIsFiniteMeasure _
  letI :
      IsFiniteMeasure
        (Measure.pi fun _ :
          terminal.right.SurvivingCoordinate =>
            paperMeasure) :=
    Measure.pi.instIsFiniteMeasure _
  letI :
      SigmaFinite
        (Measure.pi fun _ :
          terminal.left.SurvivingCoordinate =>
            paperMeasure) :=
    IsFiniteMeasure.toSigmaFinite _
  letI :
      SigmaFinite
        (Measure.pi fun _ :
          terminal.right.SurvivingCoordinate =>
            paperMeasure) :=
    IsFiniteMeasure.toSigmaFinite _
  letI :
      SFinite
        (Measure.pi fun _ :
          terminal.left.SurvivingCoordinate =>
            paperMeasure) :=
    inferInstance
  letI :
      SFinite
        (Measure.pi fun _ :
          terminal.right.SurvivingCoordinate =>
            paperMeasure) :=
    inferInstance
  rw [integral_prod_symm
    (μ := Measure.pi fun _ :
      terminal.left.SurvivingCoordinate =>
        paperMeasure)
    (ν := Measure.pi fun _ :
      terminal.right.SurvivingCoordinate =>
        paperMeasure)
    _ hintegrable]
  apply integral_congr_ae
  filter_upwards with vr
  calc
    (∫ vl,
        terminal.terminalResidualSumPhysicalCore
          π x y z w (vl, vr)
        ∂Measure.pi fun _ => paperMeasure) =
        ∫ vl,
          (terminal.right.residualIntegrand
              ρ ε z w
              (terminal.right.reconstruct vr) : ℂ) *
            ((terminal.left.residualIntegrand
                ρ ε x y
                (terminal.left.reconstruct vl) : ℂ) *
              terminal.residualSumCrossFactor π vl vr)
          ∂Measure.pi fun _ => paperMeasure := by
      apply integral_congr_ae
      filter_upwards with vl
      unfold terminalResidualSumPhysicalCore
      ring
    _ =
        (terminal.right.residualIntegrand
            ρ ε z w
            (terminal.right.reconstruct vr) : ℂ) *
          (∫ vl,
            (terminal.left.residualIntegrand
                ρ ε x y
                (terminal.left.reconstruct vl) : ℂ) *
              terminal.residualSumCrossFactor π vl vr
            ∂Measure.pi fun _ => paperMeasure) := by
      simpa only using
        (integral_const_mul
          (μ := Measure.pi fun _ :
            terminal.left.SurvivingCoordinate =>
              paperMeasure)
          (terminal.right.residualIntegrand
              ρ ε z w
              (terminal.right.reconstruct vr) : ℂ)
          (fun vl :
              terminal.left.SurvivingCoordinate → T4 =>
            (terminal.left.residualIntegrand
                ρ ε x y
                (terminal.left.reconstruct vl) : ℂ) *
              terminal.residualSumCrossFactor π vl vr))

end R324TwoHalfTerminalData

/-! ## Certified two-half collapse of the exact residual-sum core -/

namespace R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {x y z w : T4}
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftScale rightScale : Fin (m + 1) → ℝ}

/-- Exact certified two-half collapse followed by the lossless terminal to
initial-nested transport for the signed residual primitive sum. -/
theorem twoHalf_lamEps_pow_integral_residualSum_eq_initialNested
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        leftRes leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        rightRes rightScale)
    (π : κp.singles ≃ κm.singles)
    (hleft :
      ∀ᵐ vr ∂(Measure.pi fun _ :
          rightRes.SurvivingCoordinate => paperMeasure),
        leftTrace.WeightedIntegrableAlong x y
          (fun vl =>
            (R324TwoHalfTerminalData.ofCertifiedTraces
              leftTrace rightTrace).residualSumCrossFactor
                π vl (rightTrace.terminalProjection vr)))
    (hright :
      rightTrace.WeightedIntegrableAlong z w
        (fun vr =>
          ∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              (R324TwoHalfTerminalData.ofCertifiedTraces
                leftTrace rightTrace).residualSumCrossFactor
                  π vl vr)
            ∂Measure.pi fun _ => paperMeasure))
    (hterminal :
      Integrable
        ((R324TwoHalfTerminalData.ofCertifiedTraces
          leftTrace rightTrace).terminalResidualSumPhysicalCore
            π x y z w)
        ((Measure.pi fun _ :
            leftTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            rightTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure))) :
    (lamEps lam ε : ℂ) ^ (2 * rightRes.remainingOrder) *
        (∫ vr : rightRes.SurvivingCoordinate → T4,
          (rightRes.residualIntegrand ρ ε z w
              (rightRes.reconstruct vr) : ℂ) *
            ((lamEps lam ε : ℂ) ^
                (2 * leftRes.remainingOrder) *
              (∫ vl : leftRes.SurvivingCoordinate → T4,
                (leftRes.residualIntegrand ρ ε x y
                    (leftRes.reconstruct vl) : ℂ) *
                  (R324TwoHalfTerminalData.ofCertifiedTraces
                    leftTrace rightTrace).residualSumCrossFactor
                      π
                      (leftTrace.terminalProjection vl)
                      (rightTrace.terminalProjection vr)
                ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure) =
      ∫ v :
          (R324TwoHalfTerminalData.ofCertifiedTraces
            leftTrace rightTrace).NestedCoordinate π → T4,
        (R324TwoHalfTerminalData.ofCertifiedTraces
          leftTrace rightTrace).initialNestedResidualSumPhysicalCore
            π x y z w v
        ∂Measure.pi fun _ => paperMeasure := by
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace
  calc
    _ =
        ∫ vr :
            rightTrace.terminalPrefix.SurvivingCoordinate → T4,
          ((rightTrace.terminalPrefix.residualIntegrand
              ρ ε z w
              (rightTrace.terminalPrefix.reconstruct vr) : ℂ) *
            (∫ vl :
                leftTrace.terminalPrefix.SurvivingCoordinate → T4,
              ((leftTrace.terminalPrefix.residualIntegrand
                  ρ ε x y
                  (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
                terminal.residualSumCrossFactor π vl vr)
              ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure :=
      twoHalf_lamEps_pow_integral_eq_terminal
        leftTrace rightTrace
        (terminal.residualSumCrossFactor π)
        hleft hright
    _ =
        ∫ p,
          terminal.terminalResidualSumPhysicalCore
            π x y z w p
          ∂((Measure.pi fun _ :
              leftTrace.terminalPrefix.SurvivingCoordinate =>
                paperMeasure).prod
            (Measure.pi fun _ :
              rightTrace.terminalPrefix.SurvivingCoordinate =>
                paperMeasure)) :=
      (terminal.integral_terminalResidualSumPhysicalCore_eq_iterated
        π x y z w hterminal).symm
    _ = _ :=
      terminal.integral_terminalResidualSumPhysicalCore_eq_initialNested
        π x y z w

/-- Root-coordinate form of the exact bridge.  Its cross factor is the
literal `r324ResidualPrimitiveSumProduct` occurring before either
within-half trace is collapsed; the preceding projection theorem is the
only rewrite used to reach the terminal cross factor. -/
theorem twoHalf_lamEps_pow_integral_rootResidualSum_eq_initialNested
    (leftTrace :
      R324WithinHalfCertifiedAnalyticTrace
        leftRes leftScale)
    (rightTrace :
      R324WithinHalfCertifiedAnalyticTrace
        rightRes rightScale)
    (π : κp.singles ≃ κm.singles)
    (hleft :
      ∀ᵐ vr ∂(Measure.pi fun _ :
          rightRes.SurvivingCoordinate => paperMeasure),
        leftTrace.WeightedIntegrableAlong x y
          (fun vl =>
            (R324TwoHalfTerminalData.ofCertifiedTraces
              leftTrace rightTrace).residualSumCrossFactor
                π vl (rightTrace.terminalProjection vr)))
    (hright :
      rightTrace.WeightedIntegrableAlong z w
        (fun vr =>
          ∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              (R324TwoHalfTerminalData.ofCertifiedTraces
                leftTrace rightTrace).residualSumCrossFactor
                  π vl vr)
            ∂Measure.pi fun _ => paperMeasure))
    (hterminal :
      Integrable
        ((R324TwoHalfTerminalData.ofCertifiedTraces
          leftTrace rightTrace).terminalResidualSumPhysicalCore
            π x y z w)
        ((Measure.pi fun _ :
            leftTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            rightTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure))) :
    (lamEps lam ε : ℂ) ^ (2 * rightRes.remainingOrder) *
        (∫ vr : rightRes.SurvivingCoordinate → T4,
          (rightRes.residualIntegrand ρ ε z w
              (rightRes.reconstruct vr) : ℂ) *
            ((lamEps lam ε : ℂ) ^
                (2 * leftRes.remainingOrder) *
              (∫ vl : leftRes.SurvivingCoordinate → T4,
                (leftRes.residualIntegrand ρ ε x y
                    (leftRes.reconstruct vl) : ℂ) *
                  (r324ResidualPrimitiveSumProduct
                    ρ ε κp κm π
                    (r324TwoHalfRootDoubledReconstruct
                      leftRes rightRes (vl, vr)) : ℂ)
                ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure) =
      ∫ v :
          (R324TwoHalfTerminalData.ofCertifiedTraces
            leftTrace rightTrace).NestedCoordinate π → T4,
        (R324TwoHalfTerminalData.ofCertifiedTraces
          leftTrace rightTrace).initialNestedResidualSumPhysicalCore
            π x y z w v
        ∂Measure.pi fun _ => paperMeasure := by
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace
  calc
    _ =
        (lamEps lam ε : ℂ) ^
            (2 * rightRes.remainingOrder) *
          (∫ vr : rightRes.SurvivingCoordinate → T4,
            (rightRes.residualIntegrand ρ ε z w
                (rightRes.reconstruct vr) : ℂ) *
              ((lamEps lam ε : ℂ) ^
                  (2 * leftRes.remainingOrder) *
                (∫ vl : leftRes.SurvivingCoordinate → T4,
                  (leftRes.residualIntegrand ρ ε x y
                      (leftRes.reconstruct vl) : ℂ) *
                    terminal.residualSumCrossFactor
                      π
                      (leftTrace.terminalProjection vl)
                      (rightTrace.terminalProjection vr)
                  ∂Measure.pi fun _ => paperMeasure))
            ∂Measure.pi fun _ => paperMeasure) := by
      apply congrArg
      apply integral_congr_ae
      filter_upwards with vr
      apply congrArg
      apply congrArg
      apply integral_congr_ae
      filter_upwards with vl
      apply congrArg
      unfold R324TwoHalfTerminalData.residualSumCrossFactor
      exact
        leftTrace.r324ResidualPrimitiveSumProduct_complex_eq_terminalProjection
          rightTrace π (vl, vr)
    _ = _ :=
      leftTrace.twoHalf_lamEps_pow_integral_residualSum_eq_initialNested
        rightTrace π hleft hright hterminal

end R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

end

end Anderson4D
