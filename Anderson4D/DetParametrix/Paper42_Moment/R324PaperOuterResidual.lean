import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualStep
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualIntegrability

/-!
# The within-half successive removal, carrying an outer factor

Paper: R-324 — §4.2 Step 2(5) — removal inside (4.18), outer factor carried

Paper §4.2, Step 2(5): *"we successively sum over the primitive pairings
`κ_i` (`i ≥ 1`) and remove each `I_i`, gaining a factor `Cλ` and
introducing new inputs `H`, exactly as in §4.1."*

The §4.1 removal is already available at the level of one half as
`R324WithinHalfResidualPrefix.residualValue_eq_afterHead` and its list
iteration `exists_terminal_residualValue_eq_of_provider`.  What Step 2
needs on top of §4.1 is that the removal takes place **inside** the
`2m+4`-fold integral (4.18): while the left half's blocks are integrated
out, the whole right half, the cross-copy covariances, and the four
endpoint characters are simply *there*, untouched.

This module supplies exactly that.  The point that makes it work is
structural, not analytic:

> Definition 3.1's fully paired subintervals contain **no singles**.  The
> cross-copy covariance factors are indexed by the singles.  Hence every
> factor of (4.18) outside the current half's block is constant in the
> block's coordinates and passes through the block integral as a scalar.

Concretely `R324OuterReadsOnly S Outer` says the outer factor reads the
half's tuple only at the vertices of `S`; when `S` avoids the current
schedule block, `r324Outer_reconstruct_split_eq` shows the outer factor is
literally constant along the block coordinates, and the one-head
transition of `R324WithinHalfResidualStep` carries it through unchanged.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Outer factors that avoid the removed blocks -/

/-- `Outer` reads the within-half internal tuple only at the vertices of
`S`.  In (4.18) the relevant `S` is the set of *singles* of the half's
pairing: those carry the cross-copy covariances, and nothing else in the
other half, in the endpoint characters, or in the cross factors looks at
this half's internal coordinates. -/
def R324OuterReadsOnly {m : ℕ} (S : Finset (Fin m))
    (Outer : (Fin m → T4) → ℂ) : Prop :=
  ∀ u u' : Fin m → T4, (∀ i ∈ S, u i = u' i) → Outer u = Outer u'

theorem R324OuterReadsOnly.mono {m : ℕ} {S S' : Finset (Fin m)}
    {Outer : (Fin m → T4) → ℂ} (h : R324OuterReadsOnly S Outer)
    (hS : S ⊆ S') : R324OuterReadsOnly S' Outer :=
  fun u u' hu => h u u' fun i hi => hu i (hS hi)

/-- A constant outer factor reads nothing. -/
theorem r324OuterReadsOnly_const {m : ℕ} (S : Finset (Fin m)) (c : ℂ) :
    R324OuterReadsOnly S (fun _ => c) :=
  fun _ _ _ => rfl

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)

section Head

variable
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)

include tail hremaining

/-- **Outside the current block the reconstruction does not see the block
coordinates.**  A vertex not in `head.2` is either still active after the
`absorb` — in which case the split reads it from the post tuple — or was
already deleted, in which case both reconstructions return the junk value
`0`.  Either way the value is independent of the block tuple `t`. -/
theorem reconstruct_split_symm_outside_block
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v : (res.afterHead head tail hremaining).SurvivingCoordinate → T4)
    {i : Fin m} (hi : i ∉ head.2) :
    res.reconstruct
        ((res.splitSurvivingPiMeasurableEquiv
          head tail hremaining).symm (t, v)) i =
      (res.afterHead head tail hremaining).reconstruct v i := by
  by_cases hact : i ∈ res.state.active
  · -- still active before the step, and not in the block: post-surviving
    have hpost : i ∈ (res.afterHead head tail hremaining).state.active := by
      have hset :
          (res.afterHead head tail hremaining).state.active =
            res.state.active \ head.2 :=
        (res.headContext head tail hremaining).absorb_active ρ lam ε
      rw [hset]
      exact Finset.mem_sdiff.mpr ⟨hact, hi⟩
    have hkey :=
      res.reconstruct_split_symm_post head tail hremaining t v ⟨i, hpost⟩
    simpa using hkey
  · -- already deleted: both sides are the junk value
    have hpost : i ∉ (res.afterHead head tail hremaining).state.active := by
      have hset :
          (res.afterHead head tail hremaining).state.active =
            res.state.active \ head.2 :=
        (res.headContext head tail hremaining).absorb_active ρ lam ε
      rw [hset]
      exact fun hmem => hact (Finset.mem_sdiff.mp hmem).1
    unfold R324WithinHalfResidualPrefix.reconstruct
    rw [dif_neg hact, dif_neg hpost]

/-- Forward form of the previous lemma: outside the current block the
pre-step reconstruction already agrees with the post-step reconstruction of
the split tuple. -/
theorem reconstruct_outside_block_eq_post
    (v : res.SurvivingCoordinate → T4) {i : Fin m} (hi : i ∉ head.2) :
    res.reconstruct v i =
      (res.afterHead head tail hremaining).reconstruct
        ((res.splitSurvivingPiMeasurableEquiv head tail hremaining) v).2 i := by
  have hkey :=
    res.reconstruct_split_symm_outside_block head tail hremaining
      ((res.splitSurvivingPiMeasurableEquiv head tail hremaining) v).1
      ((res.splitSurvivingPiMeasurableEquiv head tail hremaining) v).2 hi
  rwa [Prod.mk.eta,
    (res.splitSurvivingPiMeasurableEquiv
      head tail hremaining).symm_apply_apply] at hkey

/-- **The outer factor is constant along the block coordinates.**  This is
the whole content of "the rest of (4.18) is untouched by the removal". -/
theorem r324Outer_reconstruct_split_eq
    {S : Finset (Fin m)} {Outer : (Fin m → T4) → ℂ}
    (hOuter : R324OuterReadsOnly S Outer)
    (hdisj : ∀ i ∈ S, i ∉ head.2)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v : (res.afterHead head tail hremaining).SurvivingCoordinate → T4) :
    Outer
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      Outer ((res.afterHead head tail hremaining).reconstruct v) :=
  hOuter _ _ fun i hi =>
    res.reconstruct_split_symm_outside_block head tail hremaining t v
      (hdisj i hi)

end Head

/-! ## The residual value with an outer factor -/

/-- The complete residual value of one half, multiplied by an outer factor
that reads only surviving vertices.  With `Outer = 1` this is the
proved `residualValue`, complexified. -/
def residualValueWithOuter
    (ρ : SmoothCutoff) (lam ε : ℝ) (Outer : (Fin m → T4) → ℂ)
    (x y : T4) : ℂ :=
  (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
    ∫ w : res.SurvivingCoordinate → T4,
      (res.residualIntegrand ρ ε x y (res.reconstruct w) : ℂ) *
        Outer (res.reconstruct w)
      ∂Measure.pi fun _ => paperMeasure

section HeadTransition

variable
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)

include tail hremaining

/-- **One removal of §4.1, performed inside (4.18).**

The exact one-head transition of `R324WithinHalfResidualStep`, with an
arbitrary outer factor riding along.  The outer factor is not integrated
and not estimated: by `r324Outer_reconstruct_split_eq` it is a scalar for
the block integral, so it commutes with the collapse. -/
theorem residualValueWithOuter_eq_afterHead
    {S : Finset (Fin m)} {Outer : (Fin m → T4) → ℂ}
    (hOuter : R324OuterReadsOnly S Outer)
    (hdisj : ∀ i ∈ S, i ∉ head.2)
    (x y : T4)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y (res.reconstruct w) : ℂ) *
            Outer (res.reconstruct w))
        (Measure.pi fun _ => paperMeasure))
    (hstandard :
      ∀ v :
          (res.afterHead head tail hremaining).SurvivingCoordinate → T4,
        Integrable
          ((res.headContext head tail hremaining).localIntegrand ρ ε
            (res.headPredecessorPoint head tail hremaining x y v -
              res.headSuccessorPoint head tail hremaining x y v))
          (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ _v :
          (res.afterHead head tail hremaining).SurvivingCoordinate → T4,
        ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
          ∀ κB :
              {κ : PartialPairing
                  (Fin (2 * residualBlockOrder head.2)) //
                κ ∈ primitiveFullPairings (residualBlockOrder head.2)},
            Integrable
              (fun w : Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
                detJclosedIntegrandWith ρ ε
                  (2 * residualBlockOrder head.2) κB.1
                  (res.headContext head tail hremaining).internalEdges
                  (primitiveAssemble (residualBlockOrder head.2)
                    (res.headContext
                      head tail hremaining).one_le_blockOrder
                    p.1 p.2 w))
              (Measure.pi fun _ => paperMeasure)) :
    res.residualValueWithOuter ρ lam ε Outer x y =
      (res.afterHead head tail hremaining).residualValueWithOuter
        ρ lam ε Outer x y := by
  have hsplit :=
    res.integral_splitSurviving_post_first head tail hremaining
      (fun w : res.SurvivingCoordinate → T4 =>
        (res.residualIntegrand ρ ε x y (res.reconstruct w) : ℂ) *
          Outer (res.reconstruct w))
      hfull
  have hexponent :
      2 * res.remainingOrder =
        2 * (res.afterHead head tail hremaining).remainingOrder +
          2 * residualBlockOrder head.2 := by
    have horder :
        res.remainingOrder =
          residualBlockOrder head.2 +
            (res.afterHead head tail hremaining).remainingOrder :=
      res.remainingOrder_head head tail hremaining
    omega
  unfold residualValueWithOuter
  rw [hexponent, pow_add, hsplit, mul_assoc, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  -- the outer factor is a scalar for the block integral
  have hconst :
      ∀ t : Fin (2 * residualBlockOrder head.2) → T4,
        (res.residualIntegrand ρ ε x y
              (res.reconstruct
                ((res.splitSurvivingPiMeasurableEquiv
                  head tail hremaining).symm (t, v))) : ℂ) *
            Outer
              (res.reconstruct
                ((res.splitSurvivingPiMeasurableEquiv
                  head tail hremaining).symm (t, v))) =
          (res.residualIntegrand ρ ε x y
              (res.reconstruct
                ((res.splitSurvivingPiMeasurableEquiv
                  head tail hremaining).symm (t, v))) : ℂ) *
            Outer ((res.afterHead head tail hremaining).reconstruct v) := by
    intro t
    rw [res.r324Outer_reconstruct_split_eq head tail hremaining
      hOuter hdisj t v]
  simp_rw [hconst]
  rw [integral_mul_const, ← mul_assoc]
  rw [res.lamEps_pow_integral_residualIntegrand_section_eq_afterHead
    head tail hremaining x y v (hstandard v) (hinternal v)]

end HeadTransition

/-! ## Iteration through the whole schedule

The paper removes *all* the fully paired subintervals of the half, one
after another.  This is the same structural list recursion as the
proved `exists_terminal_residualValue_eq_of_provider`, now preserving
the outer factor at every step. -/

/-- The evidence for one outer-carrying removal.  `base` is the proved
Fubini/collapse evidence — the outer factor plays no part in it — `avoid`
is the structural fact that the removed block contains no vertex the outer
factor reads, and `fullOuter` is the joint integrability of the product
actually integrated. -/
structure R324OuterStepReady
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (S : Finset (Fin m)) (Outer : (Fin m → T4) → ℂ)
    (x y : T4) : Prop where
  base : R324WithinHalfResidualStepReady res head tail hremaining x y
  avoid : ∀ i ∈ S, i ∉ head.2
  fullOuter :
    Integrable
      (fun w : res.SurvivingCoordinate → T4 =>
        (res.residualIntegrand ρ ε x y (res.reconstruct w) : ℂ) *
          Outer (res.reconstruct w))
      (Measure.pi fun _ => paperMeasure)

/-- One packaged outer-carrying removal preserves the value. -/
theorem R324OuterStepReady.value_eq_afterHead
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {head : R322ExtractionStep m}
    {tail : List (R322ExtractionStep m)}
    {hremaining : res.remaining = head :: tail}
    {S : Finset (Fin m)} {Outer : (Fin m → T4) → ℂ} {x y : T4}
    (hOuter : R324OuterReadsOnly S Outer)
    (ready : R324OuterStepReady res head tail hremaining S Outer x y) :
    res.residualValueWithOuter ρ lam ε Outer x y =
      (res.afterHead head tail hremaining).residualValueWithOuter
        ρ lam ε Outer x y :=
  res.residualValueWithOuter_eq_afterHead head tail hremaining
    hOuter ready.avoid x y ready.fullOuter
    ready.base.standard ready.base.internal

/-- Uniform provider of the outer-carrying step evidence. -/
def R324OuterStepProvider
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (S : Finset (Fin m)) (Outer : (Fin m → T4) → ℂ) (x y : T4) : Prop :=
  ∀ (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail),
    R324OuterStepReady res head tail hremaining S Outer x y

/-- A proof-relevant exact trace through every remaining schedule block,
carrying the outer factor. -/
inductive R324OuterIterationReady
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (S : Finset (Fin m)) (Outer : (Fin m → T4) → ℂ) (x y : T4) :
    R324WithinHalfResidualPrefix ρ lam ε pairing → Prop
  | terminal
      (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
      (hremaining : res.remaining = []) :
      R324OuterIterationReady S Outer x y res
  | step
      (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
      (head : R322ExtractionStep m)
      (tail : List (R322ExtractionStep m))
      (hremaining : res.remaining = head :: tail)
      (ready : R324OuterStepReady res head tail hremaining S Outer x y)
      (next :
        R324OuterIterationReady S Outer x y
          (res.afterHead head tail hremaining)) :
      R324OuterIterationReady S Outer x y res

/-- A uniform provider constructs the complete trace. -/
theorem R324OuterIterationReady.of_provider
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (S : Finset (Fin m)) (Outer : (Fin m → T4) → ℂ) (x y : T4)
    (provider :
      R324OuterStepProvider (ρ := ρ) (lam := lam) (ε := ε)
        (pairing := pairing) S Outer x y)
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing) :
    R324OuterIterationReady S Outer x y res := by
  cases hremaining : res.remaining with
  | nil => exact R324OuterIterationReady.terminal res hremaining
  | cons head tail =>
      exact
        R324OuterIterationReady.step res head tail hremaining
          (provider res head tail hremaining)
          (R324OuterIterationReady.of_provider S Outer x y provider
            (res.afterHead head tail hremaining))
termination_by res.remaining.length
decreasing_by simp [hremaining]

/-- **All the removals of one half, performed inside (4.18).**

Iterating a ready trace reaches a genuine empty suffix — every fully
paired subinterval of the half has been removed — and the residual value
*with its outer factor* is preserved exactly.  This is paper §4.2
Step 2(5) for one half: absolute values have not been taken, and the
right half, the cross covariances, and the endpoint characters have not
been touched. -/
theorem R324OuterIterationReady.exists_terminal_value_eq
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {S : Finset (Fin m)} {Outer : (Fin m → T4) → ℂ} {x y : T4}
    (hOuter : R324OuterReadsOnly S Outer)
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    (ready : R324OuterIterationReady S Outer x y res) :
    ∃ terminal : R324WithinHalfResidualPrefix ρ lam ε pairing,
      terminal.remaining = [] ∧
      terminal.state.processed = r322AnalyticSchedule pairing ∧
      res.residualValueWithOuter ρ lam ε Outer x y =
        terminal.residualValueWithOuter ρ lam ε Outer x y := by
  induction ready with
  | terminal terminal hremaining =>
      refine ⟨terminal, hremaining, ?_, rfl⟩
      have hschedule := terminal.schedule_eq
      rw [hremaining, List.append_nil] at hschedule
      exact hschedule.symm
  | step current head tail hremaining hstep _next ih =>
      obtain ⟨terminal, hterminal, hprocessed, hvalue⟩ := ih
      exact ⟨terminal, hterminal, hprocessed,
        (hstep.value_eq_afterHead hOuter).trans hvalue⟩

/-- Consumer-facing list iteration from one uniform provider. -/
theorem exists_terminal_residualValueWithOuter_eq_of_provider
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {S : Finset (Fin m)} {Outer : (Fin m → T4) → ℂ}
    (hOuter : R324OuterReadsOnly S Outer) (x y : T4)
    (provider :
      R324OuterStepProvider (ρ := ρ) (lam := lam) (ε := ε)
        (pairing := pairing) S Outer x y)
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing) :
    ∃ terminal : R324WithinHalfResidualPrefix ρ lam ε pairing,
      terminal.remaining = [] ∧
      terminal.state.processed = r322AnalyticSchedule pairing ∧
      res.residualValueWithOuter ρ lam ε Outer x y =
        terminal.residualValueWithOuter ρ lam ε Outer x y :=
  (R324OuterIterationReady.of_provider S Outer x y provider
    res).exists_terminal_value_eq hOuter

/-! ## Bridging an ambient outer factor to the proved certified trace

`R324WithinHalfResidualIntegrability` already iterates the removal with an
outer factor — but one presented as a function of the *terminal* surviving
coordinates (`lamEps_pow_integral_mul_terminalOuter_eq_terminal`).  In
(4.18) the outer factor is not given in that form: it is a function of the
ambient half tuple, namely the other half times the cross-copy covariances
times the endpoint characters.

The two presentations agree exactly when the outer factor avoids every
removed block, which is the structural fact `R324OuterAvoidsSchedule`
below — true for (4.18) because Definition 3.1's subintervals are fully
paired and the cross covariances are indexed by the singles. -/

/-- No block of the analytic schedule meets `S`.  For (4.18), with `S` the
singles of the half's pairing, this holds because every schedule block is
fully paired. -/
def R324OuterAvoidsSchedule {m : ℕ} (pairing : PartialPairing (Fin m))
    (S : Finset (Fin m)) : Prop :=
  ∀ step ∈ r322AnalyticSchedule pairing, ∀ i ∈ S, i ∉ step.2

/-- **The singles avoid every removed block.**

Definition 3.1's fully paired subintervals contain no fixed point of the
pairing (`IsFullyPairedOn` asserts `κ i ≠ i` on the block).  The outer
factor of (4.18) depends on this half only through the cross-copy
covariances, which are indexed by the singles; hence it never reads a
coordinate that a removal integrates out.  This is the hypothesis that
makes the whole "remove inside the integral" step legitimate. -/
theorem r324OuterAvoidsSchedule_singles {m : ℕ}
    (pairing : PartialPairing (Fin m)) :
    R324OuterAvoidsSchedule pairing pairing.singles := by
  intro step hstep i hi hmem
  have hblock : step.2 ∈ extractionBlocks pairing :=
    (r322AnalyticSchedule_blocks_perm_extractionBlocks pairing).mem_iff.mp
      (List.mem_map.mpr ⟨step, hstep, rfl⟩)
  exact
    (extractionBlock_isFullyPairedOn_of_mem pairing step.2 hblock).1 i hmem
      (PartialPairing.mem_singles.mp hi)

/-- Any subset of the singles also avoids every removed block. -/
theorem r324OuterAvoidsSchedule_subset_singles {m : ℕ}
    {pairing : PartialPairing (Fin m)} {S : Finset (Fin m)}
    (hS : S ⊆ pairing.singles) :
    R324OuterAvoidsSchedule pairing S :=
  fun step hstep i hi =>
    r324OuterAvoidsSchedule_singles pairing step hstep i (hS hi)

namespace R324WithinHalfCertifiedAnalyticTrace

/-- **The ambient outer factor is the terminal outer factor.**

Along any certified analytic trace, an outer factor reading only vertices
that no removed block contains takes the same value on the current tuple
and on its terminal projection.  Consequently
`fun w => Outer (trace.terminalPrefix.reconstruct w)` is the
terminal-coordinate presentation required by
`lamEps_pow_integral_mul_terminalOuter_eq_terminal`. -/
theorem outer_reconstruct_eq_terminalProjection
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {S : Finset (Fin m)} {Outer : (Fin m → T4) → ℂ}
    (hOuter : R324OuterReadsOnly S Outer)
    (havoid : R324OuterAvoidsSchedule pairing S)
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace : R324WithinHalfCertifiedAnalyticTrace res scale) :
    ∀ v : res.SurvivingCoordinate → T4,
      Outer (res.reconstruct v) =
        Outer
          (trace.terminalPrefix.reconstruct
            (trace.terminalProjection v)) := by
  induction trace with
  | terminal r s hr c =>
      intro v
      rfl
  | step current head tail hremaining scale internal nextScale
      nextCertificate next ih =>
      intro v
      have hmem : head ∈ r322AnalyticSchedule pairing := by
        rw [current.schedule_eq, hremaining]
        exact List.mem_append_right _ (List.mem_cons_self ..)
      have hstep :
          Outer (current.reconstruct v) =
            Outer
              ((current.afterHead head tail hremaining).reconstruct
                ((current.splitSurvivingPiMeasurableEquiv
                  head tail hremaining) v).2) :=
        hOuter _ _ fun i hi =>
          current.reconstruct_outside_block_eq_post head tail hremaining v
            (havoid head hmem i hi)
      exact hstep.trans (ih _)

/-- **All the removals of one half, inside (4.18), with the ambient outer
factor.**

This is paper §4.2 Step 2(5) for one half in the form Step 2 actually
needs: the value integrated is the half's residual integrand times the
*ambient* outer factor — the other half, the cross covariances, the
endpoint characters — and the conclusion is the same product on the
terminal carrier, where every fully paired subinterval of the half has
been removed and each removal has been replaced by the input `H` of
(4.13).  No absolute value has been taken (Step 2(f)). -/
theorem lamEps_pow_integral_mul_ambientOuter_eq_terminal
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {S : Finset (Fin m)} {Outer : (Fin m → T4) → ℂ}
    (hOuter : R324OuterReadsOnly S Outer)
    (havoid : R324OuterAvoidsSchedule pairing S)
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ} (x y : T4)
    (trace : R324WithinHalfCertifiedAnalyticTrace res scale)
    (hweighted :
      trace.WeightedIntegrableAlong x y
        (fun w => Outer (trace.terminalPrefix.reconstruct w))) :
    res.residualValueWithOuter ρ lam ε Outer x y =
      ∫ v : trace.terminalPrefix.SurvivingCoordinate → T4,
        ((trace.terminalPrefix.residualIntegrand ρ ε x y
            (trace.terminalPrefix.reconstruct v) : ℂ) *
          Outer (trace.terminalPrefix.reconstruct v))
        ∂Measure.pi fun _ => paperMeasure := by
  have hbridge :
      ∀ v : res.SurvivingCoordinate → T4,
        Outer (res.reconstruct v) =
          Outer
            (trace.terminalPrefix.reconstruct
              (trace.terminalProjection v)) :=
    trace.outer_reconstruct_eq_terminalProjection hOuter havoid
  unfold R324WithinHalfResidualPrefix.residualValueWithOuter
  simp_rw [hbridge]
  exact
    trace.lamEps_pow_integral_mul_terminalOuter_eq_terminal x y
      (fun w => Outer (trace.terminalPrefix.reconstruct w)) hweighted

/-- **Step 2(5) for one half, under the paper's own hypothesis.**

Specialization of the previous theorem in which the only requirement on the
outer factor is that it read this half's tuple at the *singles* — which is
exactly what the cross-copy covariances of (4.18) do, the other half and
the four endpoint characters not looking at this half's internal
coordinates at all.  The block-avoidance side condition is then automatic
(`r324OuterAvoidsSchedule_singles`). -/
theorem lamEps_pow_integral_mul_singlesOuter_eq_terminal
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {Outer : (Fin m → T4) → ℂ}
    (hOuter : R324OuterReadsOnly pairing.singles Outer)
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ} (x y : T4)
    (trace : R324WithinHalfCertifiedAnalyticTrace res scale)
    (hweighted :
      trace.WeightedIntegrableAlong x y
        (fun w => Outer (trace.terminalPrefix.reconstruct w))) :
    res.residualValueWithOuter ρ lam ε Outer x y =
      ∫ v : trace.terminalPrefix.SurvivingCoordinate → T4,
        ((trace.terminalPrefix.residualIntegrand ρ ε x y
            (trace.terminalPrefix.reconstruct v) : ℂ) *
          Outer (trace.terminalPrefix.reconstruct v))
        ∂Measure.pi fun _ => paperMeasure :=
  trace.lamEps_pow_integral_mul_ambientOuter_eq_terminal hOuter
    (r324OuterAvoidsSchedule_singles pairing) x y hweighted

end R324WithinHalfCertifiedAnalyticTrace

end R324WithinHalfResidualPrefix

end

end Anderson4D
