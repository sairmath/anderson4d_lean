import Anderson4D.DetParametrix.Paper42_Moment.R324AlternatingDriver

/-!
# Phased within-half transport stopping before a named terminal step

The complete alternating driver consumes the whole analytic schedule.  In
the outgoing-shortcut branch this is one step too far: the distinguished
terminal block must remain visible for the endpoint Fourier collapse.

This module runs the same ordinary/exceptional alternation only through the
proper prefix before a prescribed final step.  Ordinary runs are represented
by `R324WithinHalfStopBeforeStepTrace`; a slot-zero-fed head is represented by
`R324WithinHalfNextExceptionalStop`.  The recursion is on the length of the
proper prefix before the named terminal.  Consequently the terminal step is
never absorbed.

No norm is taken here.  The exact signed/phased integral, its transported
coefficient, and a quantitative edge certificate at the stop are retained.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-! ## The strictly decreasing terminal-prefix ledger -/

/-- If two decompositions of the same list expose a head strictly before a
named final element, the suffix after that head still ends in the named
element.  This elementary list fact is the termination ledger for the
endpoint-stop driver. -/
private theorem exists_terminalPrefix_of_append_cons_eq_append_singleton
    {α : Type*} {pre₁ pre₂ suffix : List α} {head terminal : α}
    (h : pre₁ ++ head :: suffix = pre₂ ++ [terminal])
    (hlen : pre₁.length < pre₂.length) :
    ∃ post : List α, suffix = post ++ [terminal] := by
  induction pre₁ generalizing pre₂ with
  | nil =>
      cases pre₂ with
      | nil => simp at hlen
      | cons first rest =>
          simp only [List.nil_append, List.cons_append] at h
          injection h with _ hsuffix
          exact ⟨rest, hsuffix⟩
  | cons first rest ih =>
      cases pre₂ with
      | nil => simp at hlen
      | cons first' rest' =>
          simp only [List.cons_append] at h
          injection h with _ htail
          apply ih htail
          simp only [List.length_cons] at hlen
          omega

/-- At a next exceptional stop lying strictly inside the proper prefix
before `terminal`, the after-head suffix again has a proper-prefix/terminal
decomposition, and that new proper prefix is strictly shorter. -/
theorem R324WithinHalfNextExceptionalStop.exists_terminalPrefix_lt
    {terminal : R322ExtractionStep m}
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (data : R324WithinHalfNextExceptionalStop res scale)
    (pre : List (R322ExtractionStep m))
    (hremaining : res.remaining = pre ++ [terminal])
    (hbefore : data.pre.length < pre.length) :
    ∃ post : List (R322ExtractionStep m),
      data.suffix = post ++ [terminal] ∧
        post.length < pre.length := by
  have hdecomp :
      data.pre ++ data.terminal :: data.suffix =
        pre ++ [terminal] :=
    data.remaining_eq.symm.trans hremaining
  obtain ⟨post, hpost⟩ :=
    exists_terminalPrefix_of_append_cons_eq_append_singleton
      hdecomp hbefore
  refine ⟨post, hpost, ?_⟩
  have hlen := congrArg List.length hdecomp
  rw [hpost] at hlen
  simp only [List.length_append, List.length_cons] at hlen
  omega

/-! ## The endpoint-stop transport package -/

/-- Exact phased transport from a reachable residual prefix to the state
immediately before a prescribed final schedule step.  The terminal remains
the singleton remaining list. -/
structure R324WithinHalfEndpointStopAtTerminal
    (terminal : R322ExtractionStep m)
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing) where
  stop : R324WithinHalfResidualPrefix ρ lam ε pairing
  stop_remaining : stop.remaining = [terminal]
  embedding : stop.SurvivingCoordinate → res.SurvivingCoordinate
  embedding_val : ∀ i, (embedding i).1 = i.1
  projection :
    (res.SurvivingCoordinate → T4) →
      (stop.SurvivingCoordinate → T4)
  projection_apply :
    ∀ (v : res.SurvivingCoordinate → T4)
      (i : stop.SurvivingCoordinate),
      projection v i = v (embedding i)
  multiplier : Z4 → ℂ
  stopScale : Fin (m + 1) → ℝ
  stopCertificate :
    R324WithinHalfEdgeCertificate stop.state stopScale
  transport :
    ∀ (x y : T4) (k : Z4)
      (coefficient :
        (stop.SurvivingCoordinate → T4) → ℂ),
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (coefficient (projection w)) k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure) →
      (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
          (∫ w : res.SurvivingCoordinate → T4,
            res.incomingPhasedResidualDensity
              (coefficient (projection w)) k ρ ε x y w
            ∂Measure.pi fun _ => paperMeasure) =
        (lamEps lam ε : ℂ) ^ (2 * stop.remainingOrder) *
          (∫ u : stop.SurvivingCoordinate → T4,
            stop.incomingPhasedResidualDensity
              (multiplier k * coefficient u) k ρ ε x y u
            ∂Measure.pi fun _ => paperMeasure)
  integrable :
    ∀ (x y : T4) (k : Z4)
      (coefficient :
        (stop.SurvivingCoordinate → T4) → ℂ),
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          res.incomingPhasedResidualDensity
            (coefficient (projection w)) k ρ ε x y w)
        (Measure.pi fun _ => paperMeasure) →
      Integrable
        (fun u : stop.SurvivingCoordinate → T4 =>
          stop.incomingPhasedResidualDensity
            (multiplier k * coefficient u) k ρ ε x y u)
        (Measure.pi fun _ => paperMeasure)
  /-- Genuine parameter-carrying integrability.  Paper Step 4(A) keeps the
  untouched opposite-half endpoint variables outside every signed
  elimination, so the retained outgoing terminal needs this joint form for
  the final Fubini exchange. -/
  integrable_joint :
    ∀ {Y : Type} [MeasurableSpace Y]
      (ν : Measure Y) [SFinite ν]
      (x y : Y → T4) (k : Z4)
      (coefficient :
        Y → (stop.SurvivingCoordinate → T4) → ℂ),
      Integrable
        (fun p : Y × (res.SurvivingCoordinate → T4) =>
          res.incomingPhasedResidualDensity
            (coefficient p.1 (projection p.2))
            k ρ ε (x p.1) (y p.1) p.2)
        (ν.prod (Measure.pi fun _ => paperMeasure)) →
      Integrable
        (fun p : Y × (stop.SurvivingCoordinate → T4) =>
          stop.incomingPhasedResidualDensity
            (multiplier k * coefficient p.1 p.2)
            k ρ ε (x p.1) (y p.1) p.2)
        (ν.prod (Measure.pi fun _ => paperMeasure))

namespace R324WithinHalfEndpointStopAtTerminal

variable {terminal : R322ExtractionStep m}
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}

/-- The stopped state still satisfies the exact schedule ledger. -/
theorem stop_processed_append_terminal_eq_schedule
    (data : R324WithinHalfEndpointStopAtTerminal terminal res) :
    data.stop.state.processed ++ [terminal] =
      r322AnalyticSchedule pairing := by
  have hschedule := data.stop.schedule_eq
  rw [data.stop_remaining] at hschedule
  exact hschedule.symm

/-! ## Base case: the proper prefix is wholly ordinary -/

/-- An ordinary stop-before-step trace is already an endpoint-stop
transport, with trivial multiplier and its transported edge certificate. -/
def of_ordinaryTrace
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfStopBeforeStepTrace terminal [] res scale)
    (hordinary : trace.OrdinaryAlong) :
    R324WithinHalfEndpointStopAtTerminal terminal res where
  stop := trace.stopPrefix
  stop_remaining := by
    simpa using trace.stopPrefix_remaining_eq
  embedding := trace.stopCoordinateEmbedding
  embedding_val := trace.stopCoordinateEmbedding_val
  projection := trace.stopProjection
  projection_apply := trace.stopProjection_apply
  multiplier := fun _ => 1
  stopScale := trace.stopScale
  stopCertificate := trace.stopCertificate
  transport := by
    intro x y k coefficient hfull
    have h :=
      trace.lamEps_pow_integral_incomingPhasedResidualDensity_eq_stop
        x y hordinary coefficient k hfull
    simpa only [one_mul] using h
  integrable := by
    intro x y k coefficient hfull
    have h :=
      trace.integrable_stop_incomingPhasedResidualDensity
        x y hordinary coefficient k hfull
    simpa only [one_mul] using h
  integrable_joint := by
    intro Y _ ν _ x y k coefficient hfull
    have h :=
      trace.integrable_joint_stop_incomingPhasedResidualDensity
        ν hordinary x y coefficient k hfull
    simpa only [one_mul] using h

/-! ## Recursive step: one exceptional head before the terminal -/

/-- Compose the ordinary run and exceptional collapse at the next stop
with an endpoint-stop transport of its after-head suffix.  The named
terminal remains untouched in the recursive subtransport. -/
def composeNextExceptionalStop
    {scale : Fin (m + 1) → ℝ}
    (data : R324WithinHalfNextExceptionalStop res scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (sub :
      R324WithinHalfEndpointStopAtTerminal terminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)) :
    R324WithinHalfEndpointStopAtTerminal terminal res where
  stop := sub.stop
  stop_remaining := sub.stop_remaining
  embedding := fun i =>
    data.trace.stopCoordinateEmbedding
      (data.trace.stopPrefix.postSurvivingCoordinate
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        (sub.embedding i))
  embedding_val := by
    intro i
    rw [data.trace.stopCoordinateEmbedding_val]
    exact sub.embedding_val i
  projection := fun v =>
    sub.projection
      ((data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        (data.trace.stopProjection v)).2)
  projection_apply := by
    intro v i
    simp only [sub.projection_apply,
      splitSurvivingPiMeasurableEquiv_apply_snd,
      R324WithinHalfStopBeforeStepTrace.stopProjection_apply]
  multiplier := fun k =>
    sub.multiplier k *
      data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq k
  stopScale := sub.stopScale
  stopCertificate := sub.stopCertificate
  transport := by
    intro x y k coefficient hfull
    have h₁ :=
      data.lamEps_pow_integral_incomingPhasedResidualDensity_eq_afterHead
        hε hε1 x y
        (fun v => coefficient (sub.projection v)) k hfull
    have hpost :=
      data.integrable_afterHead_incomingPhasedResidualDensity
        hε hε1 x y
        (fun v => coefficient (sub.projection v)) k hfull
    have h₂ :=
      sub.transport x y k
        (fun u =>
          data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq k *
            coefficient u)
        hpost
    have h₃ :
        (∫ u : sub.stop.SurvivingCoordinate → T4,
          sub.stop.incomingPhasedResidualDensity
            (sub.multiplier k *
              (data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq k *
                coefficient u))
            k ρ ε x y u
          ∂Measure.pi fun _ => paperMeasure) =
        ∫ u : sub.stop.SurvivingCoordinate → T4,
          sub.stop.incomingPhasedResidualDensity
            ((sub.multiplier k *
              data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq k) *
              coefficient u)
            k ρ ε x y u
          ∂Measure.pi fun _ => paperMeasure := by
      apply integral_congr_ae
      filter_upwards with u
      rw [mul_assoc]
    exact (h₁.trans h₂).trans (congrArg
      (fun z : ℂ =>
        (lamEps lam ε : ℂ) ^ (2 * sub.stop.remainingOrder) * z)
      h₃)
  integrable := by
    intro x y k coefficient hfull
    have hpost :=
      data.integrable_afterHead_incomingPhasedResidualDensity
        hε hε1 x y
        (fun v => coefficient (sub.projection v)) k hfull
    have h :=
      sub.integrable x y k
        (fun u =>
          data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq k *
            coefficient u)
        hpost
    apply h.congr
    filter_upwards with u
    simp only [mul_assoc]
  integrable_joint := by
    intro Y _ ν _ x y k coefficient hfull
    have hpost :=
      data.integrable_joint_afterHead_incomingPhasedResidualDensity
        ν hε hε1 x y
        (fun parameter v => coefficient parameter (sub.projection v))
        k hfull
    have h :=
      sub.integrable_joint ν x y k
        (fun parameter u =>
          data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq k *
            coefficient parameter u)
        hpost
    apply h.congr
    filter_upwards with p
    simp only [mul_assoc]

/-! ## Strong-induction driver -/

/-- **Endpoint-stop driver.**  Starting from an explicit decomposition
`remaining = pre ++ [terminal]`, alternate ordinary runs and exceptional
head collapses only through `pre`.  The recursion terminates because the
proper prefix exposed after every exceptional head is strictly shorter.
The named terminal itself is never consumed. -/
def of_localBlockProvider
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing)
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale)
    (terminal : R322ExtractionStep m)
    (pre : List (R322ExtractionStep m))
    (hremaining : res.remaining = pre ++ [terminal]) :
    R324WithinHalfEndpointStopAtTerminal terminal res :=
  if hrun :
      pre.length ≤
        r324WithinHalfOrdinaryRunLength
          res.state.processed res.remaining then
    let trace :=
      R324WithinHalfStopBeforeStepTrace.of_localBlockProvider
        hε hε1 provider terminal [] pre res scale
        certificate (by simpa using hremaining)
    of_ordinaryTrace trace
      (trace.ordinaryAlong_of_le_ordinaryRunLength
        pre (by simpa using hremaining) hrun)
  else
    have hbefore :
        r324WithinHalfOrdinaryRunLength
            res.state.processed res.remaining <
          pre.length :=
      Nat.lt_of_not_ge hrun
    have hlt :
        r324WithinHalfOrdinaryRunLength
            res.state.processed res.remaining <
          res.remaining.length := by
      exact lt_trans hbefore (by
        rw [hremaining]
        simp only [List.length_append, List.length_singleton]
        omega)
    have data : R324WithinHalfNextExceptionalStop res scale :=
      (nonempty_r324WithinHalfNextExceptionalStop_of_lt_length
        hε hε1 provider res scale certificate hlt).some
    have hdataBefore : data.pre.length < pre.length := by
      rw [data.pre_length_eq]
      exact hbefore
    have hpost :=
      data.exists_terminalPrefix_lt pre hremaining hdataBefore
    let post := hpost.choose
    have hsuffix : data.suffix = post ++ [terminal] :=
      hpost.choose_spec.1
    have hpostlt : post.length < pre.length :=
      hpost.choose_spec.2
    composeNextExceptionalStop data hε hε1
      (of_localBlockProvider hε hε1 provider
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)
        (r324WithinHalfUpdatedEdgeScale
          (data.trace.stopPrefix.headContext
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq)
          data.trace.stopScale C lam K)
        (provider data.trace.stopPrefix
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq
          data.trace.stopScale
          data.trace.stopCertificate).2
        terminal post (by
          rw [R324WithinHalfResidualPrefix.afterHead_remaining]
          exact hsuffix))
termination_by pre.length
decreasing_by exact hpostlt

/-- Headline existence form used by the outgoing-shortcut assembly. -/
theorem exists_r324WithinHalfEndpointStopAtTerminal
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing)
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale)
    (terminal : R322ExtractionStep m)
    (pre : List (R322ExtractionStep m))
    (hremaining : res.remaining = pre ++ [terminal]) :
    Nonempty (R324WithinHalfEndpointStopAtTerminal terminal res) :=
  ⟨of_localBlockProvider hε hε1 provider res scale certificate
      terminal pre hremaining⟩

end R324WithinHalfEndpointStopAtTerminal

end R324WithinHalfResidualPrefix

end

end Anderson4D
