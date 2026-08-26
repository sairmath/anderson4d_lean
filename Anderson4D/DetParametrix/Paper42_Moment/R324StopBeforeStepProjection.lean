import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalStopTraceAssembly

/-!
# Coordinate projection to an arbitrary R-324 stopping step

A certified stop-before-step trace removes only the coordinates belonging
to the genuinely consumed schedule prefix.  This module realizes the
resulting coordinate transport as a literal embedding of stop coordinates
into the carrier at which the trace starts.  It also proves that projection
is pointwise restriction along that embedding and that ambient
reconstruction commutes with the restriction.

Unlike the terminal projection API, the named stop step and its complete
suffix remain unprocessed.  Consequently the stop active carrier need not
equal `finalActive`; the exact generally valid statement is the inclusion
of `finalActive` in the stop carrier.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfResidualPrefix.R324WithinHalfStopBeforeStepTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {terminal : R322ExtractionStep m}
    {suffix : List (R322ExtractionStep m)}

/-- Regard a coordinate surviving to the named stopping step as a
coordinate of the residual prefix at which the trace starts. -/
def stopCoordinateEmbedding
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale) :
    trace.stopPrefix.SurvivingCoordinate →
      res.SurvivingCoordinate :=
  match trace with
  | .stop .. => fun i => i
  | @R324WithinHalfStopBeforeStepTrace.step
      _ _ _ _ _ _ _
      current head tail hremaining _ _ _ _ next =>
      fun i =>
        current.postSurvivingCoordinate
          head tail hremaining
          (next.stopCoordinateEmbedding i)

@[simp]
theorem stopCoordinateEmbedding_val
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (i : trace.stopPrefix.SurvivingCoordinate) :
    (trace.stopCoordinateEmbedding i).1 = i.1 := by
  induction trace with
  | stop stop scale hremaining certificate =>
      rfl
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      change
        (current.postSurvivingCoordinate
          head tail hremaining
          (next.stopCoordinateEmbedding i)).1 = i.1
      exact ih i

/-- The trace projection is pointwise restriction along the concrete stop
coordinate embedding. -/
@[simp]
theorem stopProjection_apply
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (v : res.SurvivingCoordinate → T4)
    (i : trace.stopPrefix.SurvivingCoordinate) :
    trace.stopProjection v i =
      v (trace.stopCoordinateEmbedding i) := by
  induction trace with
  | stop stop scale hremaining certificate =>
      rfl
  | step current head tail hremaining scale internal
      nextScale nextCertificate next ih =>
      change
        next.stopProjection
            (current.splitSurvivingPiMeasurableEquiv
              head tail hremaining v).2 i =
          v
            (current.postSurvivingCoordinate
              head tail hremaining
              (next.stopCoordinateEmbedding i))
      rw [ih]
      exact
        current.splitSurvivingPiMeasurableEquiv_apply_snd
          head tail hremaining v
          (next.stopCoordinateEmbedding i)

/-- Reconstruction at every stop coordinate is unchanged by projecting
through the consumed prefix. -/
theorem reconstruct_stopProjection
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (v : res.SurvivingCoordinate → T4)
    (i : trace.stopPrefix.SurvivingCoordinate) :
    res.reconstruct v i.1 =
      trace.stopPrefix.reconstruct
        (trace.stopProjection v) i.1 := by
  calc
    res.reconstruct v i.1 =
        res.reconstruct v
          (trace.stopCoordinateEmbedding i).1 := by
      exact congrArg (res.reconstruct v)
        (trace.stopCoordinateEmbedding_val i).symm
    _ = v (trace.stopCoordinateEmbedding i) :=
      res.reconstruct_surviving
        v (trace.stopCoordinateEmbedding i)
    _ = trace.stopProjection v i :=
      (trace.stopProjection_apply v i).symm
    _ =
        trace.stopPrefix.reconstruct
          (trace.stopProjection v) i.1 :=
      (trace.stopPrefix.reconstruct_surviving
        (trace.stopProjection v) i).symm

/-- Every terminal residual vertex survives at any earlier named stopping
step.  Equality is generally false because the retained step and suffix
still contribute unprocessed block coordinates. -/
theorem finalActive_subset_stopPrefix_active
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale) :
    finalActive pairing ⊆
      trace.stopPrefix.state.active := by
  intro i hiFinal
  apply
    (mem_r322AnalyticActiveCarrier_iff
      trace.stopPrefix.state.processed i).mpr
  intro step hstep hiStep
  have hstepSchedule :
      step ∈ r322AnalyticSchedule pairing := by
    rw [← trace.stopPrefix_processed_append_eq_schedule]
    exact
      List.mem_append_left
        (terminal :: suffix) hstep
  have hblock :
      step.2 ∈ extractionBlocks pairing := by
    apply
      (r322AnalyticSchedule_blocks_perm_extractionBlocks
        pairing).mem_iff.mp
    exact List.mem_map.mpr
      ⟨step, hstepSchedule, rfl⟩
  have hiRemoved :
      i ∈ finsetUnionList (extractionBlocks pairing) :=
    (mem_finsetUnionList_iff
      (extractionBlocks pairing)).mpr
      ⟨step.2, hblock, hiStep⟩
  exact
    (Finset.disjoint_left.mp
      (extractionBlocks_disjoint_finalActive pairing))
      hiRemoved hiFinal

/-- Embed a terminal residual coordinate into the still-larger carrier at
the named stopping step. -/
def finalActiveCoordinateEmbedding
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale) :
    {i : Fin m // i ∈ finalActive pairing} →
      trace.stopPrefix.SurvivingCoordinate :=
  fun i =>
    ⟨i.1, trace.finalActive_subset_stopPrefix_active i.2⟩

@[simp]
theorem finalActiveCoordinateEmbedding_val
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace
        terminal suffix res scale)
    (i : {i : Fin m // i ∈ finalActive pairing}) :
    (trace.finalActiveCoordinateEmbedding i).1 = i.1 :=
  rfl

end R324WithinHalfResidualPrefix.R324WithinHalfStopBeforeStepTrace

namespace R324WithinHalfResidualPrefix.R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- Consumer form of the terminal-carrier inclusion for an incoming
exceptional stop package. -/
theorem finalActive_subset_stop_active
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    finalActive κ ⊆
      data.trace.stopPrefix.state.active :=
  data.trace.finalActive_subset_stopPrefix_active

end R324WithinHalfResidualPrefix.R324IncomingExceptionalStopTraceAssembly

end

end Anderson4D
