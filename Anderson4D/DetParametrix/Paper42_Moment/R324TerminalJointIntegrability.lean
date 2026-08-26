import Anderson4D.DetParametrix.Paper42_Moment.R324DriverClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalJointIntegrabilityProducer
import Anderson4D.DetParametrix.Paper42_Moment.R324InitialTwoHalfRootIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalResidualSumJointIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324FourierIntegrability

/-!
# Discharge of the driver-terminal joint integrability (R-324, gap (a))

`R324DriverClosure` expresses joint integrability for the terminal
`y`-Fourier evaluation as the Prop `DriverTerminalJointIntegrable`.
This file proves it for every
alternating transport whose terminal edge state carries a slotwise
quantitative certificate, and in particular for the canonical driver
transport `afterHeadAlternatingTransport`, whose terminal certificate is
extracted from the `of_localBlockProvider` recursion.

The three analytic ingredients are

* the slot-zero-erased terminal chain is jointly `L¹` in the outgoing
  endpoint and all surviving coordinates (a heterogeneous Haar-path
  argument; the corresponding machinery in
  `R324TerminalJointIntegrabilityProducer` is private and is reproved
  here in the erased form);
* the untouched right initial residual is jointly `L¹` in its two
  endpoints and all initial sparse coordinates (renormalized Green
  skeleton times a bounded primitive block product);
* the residual cross-cut primitive sum is a bounded measurable factor.

The product-measure regrouping is the public
`r324DriverTerminalRegroupMeasurableEquiv` of the driver closure.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Reproved heterogeneous Haar-path lemmas -/

/-- One integrable kernel read against a measurable shift, times an
integrable lift: jointly integrable on the product.  Reproof of the
private producer lemma. -/
theorem r324TJIE_integrable_kernel_sub_mul_lift
    {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν]
    (K : T4 → ℝ) (f : Y → ℝ) (shift : Y → T4)
    (hK : Integrable K paperMeasure)
    (hKmeas : Measurable K)
    (hf : Integrable f ν)
    (hshift : Measurable shift) :
    Integrable
      (fun p : T4 × Y =>
        K (p.1 - shift p.2) * f p.2)
      (paperMeasure.prod ν) := by
  let Knorm : T4 → ℝ := fun z => ‖K z‖
  have hjointMeas :
      AEStronglyMeasurable
        (fun p : T4 × Y =>
          K (p.1 - shift p.2) * f p.2)
        (paperMeasure.prod ν) :=
    (hKmeas.comp
        (measurable_fst.sub
          (hshift.comp measurable_snd))).aestronglyMeasurable.mul
      hf.aestronglyMeasurable.comp_snd
  rw [integrable_prod_iff' hjointMeas]
  constructor
  · filter_upwards with y
    have htranslated :
        Integrable
          (fun x : T4 => K (x - shift y))
          paperMeasure :=
      ((measurePreserving_sub_paper (shift y)).integrable_comp
        hK.aestronglyMeasurable).mpr hK
    exact htranslated.mul_const (f y)
  · have hnormIntegral (y : Y) :
        (∫ x : T4,
            ‖K (x - shift y) * f y‖
            ∂paperMeasure) =
          (∫ x : T4, Knorm x ∂paperMeasure) * ‖f y‖ := by
      calc
        (∫ x : T4,
            ‖K (x - shift y) * f y‖
            ∂paperMeasure) =
            ∫ x : T4,
              Knorm (x - shift y) * ‖f y‖
              ∂paperMeasure := by
                apply integral_congr_ae
                filter_upwards with x
                simp only [norm_mul, Knorm]
        _ =
            (∫ x : T4,
              Knorm (x - shift y)
              ∂paperMeasure) * ‖f y‖ := by
                rw [integral_mul_const]
        _ =
            (∫ x : T4, Knorm x
              ∂paperMeasure) * ‖f y‖ := by
                have hp :
                    MeasurePreserving
                      (MeasurableEquiv.subRight (shift y))
                      paperMeasure paperMeasure :=
                  (measurePreserving_sub_paper (shift y)).congr
                    (MeasurableEquiv.subRight
                      (shift y)).measurable
                    (Filter.Eventually.of_forall fun _ => rfl)
                have hpi := hp.integral_comp' Knorm
                change
                  (∫ x : T4,
                    Knorm (x - shift y)
                    ∂paperMeasure) =
                    ∫ x : T4, Knorm x
                      ∂paperMeasure at hpi
                rw [hpi]
    convert
      hf.norm.const_mul
        (∫ x : T4, Knorm x ∂paperMeasure) using 1
    funext y
    exact hnormIntegral y

/-- A heterogeneous kernel path with a terminal weight, on `n + 1`
ordered coordinates carrying `n` kernels.  Reproof of the private
producer definition. -/
def r324TJIE_terminalWeightedKernelPath
    {n : ℕ}
    (K : Fin n → T4 → ℝ)
    (terminalWeight : T4 → ℝ)
    (x : Fin (n + 1) → T4) : ℝ :=
  (∏ i : Fin n,
      K i (x i.castSucc - x i.succ)) *
    terminalWeight (x (Fin.last n))

/-- Joint integrability of the terminal-weighted heterogeneous kernel
path.  Reproof of the private producer theorem. -/
theorem r324TJIE_integrable_terminalWeightedKernelPath :
    ∀ {n : ℕ}
      (K : Fin n → T4 → ℝ)
      (terminalWeight : T4 → ℝ),
      (∀ i, Integrable (K i) paperMeasure) →
      (∀ i, Measurable (K i)) →
      Integrable terminalWeight paperMeasure →
      Integrable
        (r324TJIE_terminalWeightedKernelPath K terminalWeight)
        (Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure) := by
  intro n
  induction n with
  | zero =>
      intro K terminalWeight _hK _hKmeas hterminal
      let e : (Fin 1 → T4) ≃ᵐ T4 :=
        MeasurableEquiv.funUnique (Fin 1) T4
      have hp :
          MeasurePreserving e
            (Measure.pi fun _ : Fin 1 => paperMeasure)
            paperMeasure :=
        measurePreserving_funUnique paperMeasure (Fin 1)
      have hcomp :
          Integrable (terminalWeight ∘ e)
            (Measure.pi fun _ : Fin 1 => paperMeasure) :=
        (hp.integrable_comp_emb e.measurableEmbedding).mpr
          hterminal
      convert hcomp using 1
      funext x
      simp [r324TJIE_terminalWeightedKernelPath, e]
  | succ n ih =>
      intro K terminalWeight hK hKmeas hterminal
      let tailK : Fin n → T4 → ℝ :=
        fun i => K i.succ
      let μtail :=
        Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure
      let tailPath : (Fin (n + 1) → T4) → ℝ :=
        r324TJIE_terminalWeightedKernelPath
          tailK terminalWeight
      have htail :
          Integrable tailPath μtail := by
        simpa only [tailPath, tailK, μtail] using
          ih tailK terminalWeight
            (fun i => hK i.succ)
            (fun i => hKmeas i.succ)
            hterminal
      let e :=
        MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 2) => T4) 0
      have hp :
          MeasurePreserving e
            (Measure.pi fun _ : Fin (n + 2) =>
              paperMeasure)
            (paperMeasure.prod μtail) := by
        simpa only [e, μtail] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 2) => paperMeasure) 0)
      have htarget :
          Integrable
            (fun p : T4 × (Fin (n + 1) → T4) =>
              K 0 (p.1 - p.2 0) * tailPath p.2)
            (paperMeasure.prod μtail) :=
        r324TJIE_integrable_kernel_sub_mul_lift
          (K 0) tailPath (fun v => v 0)
          (hK 0) (hKmeas 0) htail
          (measurable_pi_apply 0)
      have heinv
          (y : T4) (v : Fin (n + 1) → T4) :
          e.symm (y, v) = Fin.cons y v := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [e]
        · simp [e]
      have htarget' :
          Integrable
            (fun p : T4 × (Fin (n + 1) → T4) =>
              r324TJIE_terminalWeightedKernelPath
                K terminalWeight (e.symm p))
            (paperMeasure.prod μtail) := by
        apply htarget.congr
        filter_upwards with p
        rcases p with ⟨y, v⟩
        rw [heinv y v]
        simp only [r324TJIE_terminalWeightedKernelPath,
          Fin.prod_univ_succ, Fin.cons_succ]
        change
          K 0 (y - v 0) * tailPath v =
            (K 0 (y - v 0) *
              ∏ i : Fin n,
                K i.succ
                  (v i.castSucc - v i.succ)) *
              terminalWeight (v (Fin.last n))
        unfold tailPath
          r324TJIE_terminalWeightedKernelPath tailK
        ring
      have hpull :
          Integrable
            ((fun p : T4 × (Fin (n + 1) → T4) =>
              r324TJIE_terminalWeightedKernelPath
                K terminalWeight (e.symm p)) ∘ e)
            (Measure.pi fun _ : Fin (n + 2) =>
              paperMeasure) :=
        (hp.integrable_comp_emb e.measurableEmbedding).mpr
          htarget'
      convert hpull using 1
      funext x
      simp only [Function.comp_apply,
        e.symm_apply_apply]

/-- Off-diagonal inverse-square domination gives integrability.  Reproof
of the private producer lemma. -/
theorem r324TJIE_integrable_of_offDiagonal_bound
    {K : T4 → ℝ} {C : ℝ}
    (hKmeas : Measurable K)
    (hC : 0 ≤ C)
    (hbound : ∀ z, z ≠ 0 →
      |K z| ≤ C * invSqKer z) :
    Integrable K paperMeasure := by
  refine
    (integrable_invSqKer.const_mul C).mono
      hKmeas.aestronglyMeasurable ?_
  filter_upwards
      [compl_mem_ae_iff.mpr
        (paperMeasure_singleton (0 : T4))] with z hz
  rw [Real.norm_eq_abs,
    Real.norm_eq_abs,
    abs_of_nonneg
      (mul_nonneg hC (invSqKer_nonneg z))]
  apply hbound z
  simpa only [Set.mem_compl_iff,
    Set.mem_singleton_iff] using hz

/-! ## The ordered sparse chain of a completed half, reproved -/

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)

/-- Order the surviving internal vertices.  Reproof of the private
producer definition. -/
def r324TJIE_activeOrder :
    Fin res.state.active.card ≃o
      {i : Fin m // i ∈ res.state.active} :=
  res.state.active.orderIsoOfFin rfl

/-- The zeroth sparse edge is the incoming edge; every later sparse edge
starts at the correspondingly ordered surviving internal vertex. -/
def r324TJIE_edgeSlot
    (i : Fin (res.state.active.card + 1)) :
    Fin (m + 1) :=
  if hi : i.val = 0 then
    0
  else
      r324InternalVertexEdgeSlot
        (r324TJIE_activeOrder res
          ⟨i.val - 1, by
            have hilt := i.isLt
            omega⟩).1

theorem r324TJIE_edgeSlot_mem
    (i : Fin (res.state.active.card + 1)) :
    res.r324TJIE_edgeSlot i ∈
      res.activeEdgeSlots := by
  by_cases hi : i.val = 0
  · rw [r324TJIE_edgeSlot, dif_pos hi]
    exact res.zero_mem_activeEdgeSlots
  · rw [r324TJIE_edgeSlot, dif_neg hi]
    exact
      res.internalVertexEdgeSlot_mem_activeEdgeSlots
        (r324TJIE_activeOrder res
          ⟨i.val - 1, by
            have hilt := i.isLt
            omega⟩).1
        (r324TJIE_activeOrder res
          ⟨i.val - 1, by
            have hilt := i.isLt
            omega⟩).2

theorem r324TJIE_edgeSlot_strictMono :
    StrictMono res.r324TJIE_edgeSlot := by
  intro i j hij
  by_cases hi0 : i.val = 0
  · have hj0 : j.val ≠ 0 := by omega
    simp only [r324TJIE_edgeSlot,
      hi0, hj0, dif_pos]
    change
      (0 : Fin (m + 1)) <
        r324InternalVertexEdgeSlot
          (r324TJIE_activeOrder res
            ⟨j.val - 1, by
              have hjlt := j.isLt
              omega⟩).1
    exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
  · have hj0 : j.val ≠ 0 := by omega
    let a : Fin res.state.active.card :=
      ⟨i.val - 1, by
        have hilt := i.isLt
        omega⟩
    let b : Fin res.state.active.card :=
      ⟨j.val - 1, by
        have hjlt := j.isLt
        omega⟩
    have hab : a < b := Fin.mk_lt_mk.mpr (by
      omega)
    have horder :=
      ((r324TJIE_activeOrder res).lt_iff_lt).mpr hab
    simp only [r324TJIE_edgeSlot,
      hi0, hj0]
    exact Fin.mk_lt_mk.mpr (Nat.succ_lt_succ horder)

theorem r324TJIE_edgeSlot_injective :
    Function.Injective res.r324TJIE_edgeSlot :=
  res.r324TJIE_edgeSlot_strictMono.injective

theorem r324TJIE_edgeSlot_surjective :
    Function.Surjective
      (fun i : Fin (res.state.active.card + 1) =>
        (⟨res.r324TJIE_edgeSlot i,
          res.r324TJIE_edgeSlot_mem i⟩ :
            {edge : Fin (m + 1) //
              edge ∈ res.activeEdgeSlots})) := by
  intro edge
  have hedge := edge.2
  unfold R324WithinHalfResidualPrefix.activeEdgeSlots at hedge
  rw [Finset.mem_union] at hedge
  rcases hedge with hzero | hinter
  · have heq : edge.1 = 0 := by
      simpa only [Finset.mem_singleton] using hzero
    refine ⟨0, ?_⟩
    apply Subtype.ext
    simpa [r324TJIE_edgeSlot] using heq.symm
  · obtain ⟨a, ha, haedge⟩ :=
      Finset.mem_image.mp hinter
    let j : Fin res.state.active.card :=
      (r324TJIE_activeOrder res).symm ⟨a, ha⟩
    let i : Fin (res.state.active.card + 1) :=
      ⟨j.val + 1, by
        have hjlt := j.isLt
        omega⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    have hi0 : i.val ≠ 0 := by
      dsimp only [i]
      omega
    change res.r324TJIE_edgeSlot i = edge.1
    rw [r324TJIE_edgeSlot, dif_neg hi0]
    have hindex :
        (⟨i.val - 1, by
            have hilt := i.isLt
            omega⟩ :
          Fin res.state.active.card) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have horderIndex :=
      congrArg (r324TJIE_activeOrder res) hindex
    rw [horderIndex]
    change
      r324InternalVertexEdgeSlot
          (r324TJIE_activeOrder res j).1 =
        edge.1
    rw [show
      r324TJIE_activeOrder res j = ⟨a, ha⟩ by
        exact
          (r324TJIE_activeOrder res).apply_symm_apply
            ⟨a, ha⟩]
    exact haedge

/-- The ordered enumeration of the active edge slots. -/
def r324TJIE_activeEdgeEquiv :
    Fin (res.state.active.card + 1) ≃
      {edge : Fin (m + 1) //
        edge ∈ res.activeEdgeSlots} :=
  Equiv.ofBijective
    (fun i =>
      ⟨res.r324TJIE_edgeSlot i,
        res.r324TJIE_edgeSlot_mem i⟩)
    ⟨by
      intro i j hij
      exact
        res.r324TJIE_edgeSlot_injective
          (congrArg Subtype.val hij),
      res.r324TJIE_edgeSlot_surjective⟩

/-- The ordered point corresponding to a terminal half-chain. -/
def r324TJIE_orderedVertices
    (x y : T4)
    (v : res.SurvivingCoordinate → T4) :
    Fin (res.state.active.card + 2) → T4 :=
  assemble x y
    (fun j => v (r324TJIE_activeOrder res j))

/-- The ordered named kernels of the terminal state. -/
def r324TJIE_orderedKernel
    (i : Fin (res.state.active.card + 1)) :
    T4 → ℝ :=
  res.state.edges (res.r324TJIE_edgeSlot i)

theorem r324TJIE_edgeSlot_lt_target
    (i : Fin (res.state.active.card + 1))
    (hi : i.val < res.state.active.card) :
    (res.r324TJIE_edgeSlot i).val <
      (varIdx
        (r324TJIE_activeOrder res
          ⟨i.val, hi⟩).1).val := by
  by_cases hi0 : i.val = 0
  · rw [r324TJIE_edgeSlot, dif_pos hi0]
    change
      0 <
        (r324TJIE_activeOrder res
          ⟨i.val, hi⟩).1.val + 1
    omega
  · let j : Fin res.state.active.card :=
      ⟨i.val - 1, by omega⟩
    have hjlt :
        j <
          (⟨i.val, hi⟩ :
            Fin res.state.active.card) :=
      Fin.mk_lt_mk.mpr (by
        omega)
    have horder :=
      ((r324TJIE_activeOrder res).lt_iff_lt).mpr
        hjlt
    rw [r324TJIE_edgeSlot, dif_neg hi0]
    change
      (r324TJIE_activeOrder res
          ⟨i.val - 1, by
            have hilt := i.isLt
            omega⟩).1.val + 1 <
        (r324TJIE_activeOrder res
          ⟨i.val, hi⟩).1.val + 1
    change
      (r324TJIE_activeOrder res j).1.val + 1 <
        (r324TJIE_activeOrder res
          ⟨i.val, hi⟩).1.val + 1
    exact Nat.succ_lt_succ horder

theorem r324TJIE_index_le_of_edgeSlot_lt_varIdx
    (i : Fin (res.state.active.card + 1))
    (a : res.SurvivingCoordinate)
    (h :
      (res.r324TJIE_edgeSlot i).val <
        (varIdx a.1).val) :
    i.val ≤
      ((r324TJIE_activeOrder res).symm a).val := by
  by_cases hi0 : i.val = 0
  · omega
  · let j : Fin res.state.active.card :=
      ⟨i.val - 1, by
        have hilt := i.isLt
        omega⟩
    rw [r324TJIE_edgeSlot, dif_neg hi0] at h
    change
      (r324TJIE_activeOrder res j).1.val + 1 <
        a.1.val + 1 at h
    have hactive :
        r324TJIE_activeOrder res j < a := by
      change
        (r324TJIE_activeOrder res j).1 < a.1
      exact Fin.mk_lt_mk.mpr
        (Nat.lt_of_succ_lt_succ h)
    have hordinal :
        j <
          (r324TJIE_activeOrder res).symm a := by
      apply
        ((r324TJIE_activeOrder res).lt_iff_lt).mp
      rw [(r324TJIE_activeOrder res).apply_symm_apply]
      exact hactive
    have hiVal : i.val = j.val + 1 := by
      dsimp only [j]
      omega
    rw [hiVal]
    exact Nat.succ_le_iff.mpr hordinal

/-- The successor selected by the sparse state is exactly the next ordered
surviving vertex, or the terminal external point after the last edge. -/
theorem r324TJIE_edgeSuccessor
    (i : Fin (res.state.active.card + 1)) :
    res.edgeSuccessor
        (res.r324TJIE_edgeSlot i) =
      if hi : i.val < res.state.active.card then
        varIdx
          (r324TJIE_activeOrder res
            ⟨i.val, hi⟩).1
      else
        Fin.last (m + 1) := by
  unfold edgeSuccessor
  rw [Finset.min'_eq_iff]
  by_cases hi : i.val < res.state.active.card
  · rw [dif_pos hi]
    constructor
    · rw [edgeSuccessorCandidates]
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine
        ⟨(r324TJIE_activeOrder res
            ⟨i.val, hi⟩).1,
          Finset.mem_filter.mpr
            ⟨(r324TJIE_activeOrder res
                ⟨i.val, hi⟩).2,
              res.r324TJIE_edgeSlot_lt_target i hi⟩,
          rfl⟩
    · intro candidate hcandidate
      rw [edgeSuccessorCandidates] at hcandidate
      rcases Finset.mem_union.mp hcandidate with
          hlast | hinter
      · have hc :
            candidate = Fin.last (m + 1) := by
          simpa only [Finset.mem_singleton] using hlast
        rw [hc]
        exact Fin.le_last _
      · obtain ⟨a, ha, hacandidate⟩ :=
          Finset.mem_image.mp hinter
        have hedgeLt :=
          (Finset.mem_filter.mp ha).2
        let a' : res.SurvivingCoordinate :=
          ⟨a, (Finset.mem_filter.mp ha).1⟩
        let j : Fin res.state.active.card :=
          (r324TJIE_activeOrder res).symm a'
        have hijVal : i.val ≤ j.val :=
          res.r324TJIE_index_le_of_edgeSlot_lt_varIdx
            i a' hedgeLt
        have hij : (⟨i.val, hi⟩ :
            Fin res.state.active.card) ≤ j :=
          Fin.mk_le_mk.mpr hijVal
        have hmono :=
          (r324TJIE_activeOrder res).monotone hij
        have hjapply :
            r324TJIE_activeOrder res j = a' :=
          (r324TJIE_activeOrder res).apply_symm_apply a'
        rw [hjapply] at hmono
        rw [← hacandidate]
        exact Fin.mk_le_mk.mpr
          (Nat.succ_le_succ hmono)
  · rw [dif_neg hi]
    constructor
    · rw [edgeSuccessorCandidates]
      exact Finset.mem_union_left _ (by simp)
    · intro candidate hcandidate
      rw [edgeSuccessorCandidates] at hcandidate
      rcases Finset.mem_union.mp hcandidate with
          hlast | hinter
      · have hc :
            candidate = Fin.last (m + 1) := by
          simpa only [Finset.mem_singleton] using hlast
        rw [hc]
      · obtain ⟨a, ha, hacandidate⟩ :=
          Finset.mem_image.mp hinter
        let a' : res.SurvivingCoordinate :=
          ⟨a, (Finset.mem_filter.mp ha).1⟩
        have hle :
            i.val ≤
              ((r324TJIE_activeOrder res).symm a').val :=
          res.r324TJIE_index_le_of_edgeSlot_lt_varIdx
            i a' (Finset.mem_filter.mp ha).2
        have hiLast : i.val = res.state.active.card := by
          have hilt := i.isLt
          omega
        have hjlt :=
          ((r324TJIE_activeOrder res).symm a').isLt
        omega

theorem r324TJIE_edgeSource
    (x y : T4)
    (v : res.SurvivingCoordinate → T4)
    (i : Fin (res.state.active.card + 1)) :
    assemble x y (res.reconstruct v)
        (res.r324TJIE_edgeSlot i).castSucc =
      res.r324TJIE_orderedVertices x y v
        i.castSucc := by
  by_cases hi0 : i.val = 0
  · have hieq : i = 0 := Fin.ext hi0
    subst i
    simp [r324TJIE_edgeSlot,
      r324TJIE_orderedVertices]
  · let j : Fin res.state.active.card :=
      ⟨i.val - 1, by
        have hilt := i.isLt
        omega⟩
    have hslot :
        (res.r324TJIE_edgeSlot i).castSucc =
          varIdx
            (r324TJIE_activeOrder res j).1 := by
      apply Fin.ext
      rw [r324TJIE_edgeSlot, dif_neg hi0]
      rfl
    have hposition :
        i.castSucc =
          varIdx j := by
      apply Fin.ext
      change i.val = j.val + 1
      dsimp only [j]
      omega
    rw [hslot, hposition]
    unfold r324TJIE_orderedVertices
    rw [assemble_varIdx, assemble_varIdx]
    exact res.reconstruct_surviving v
      (r324TJIE_activeOrder res j)

theorem r324TJIE_edgeTarget
    (x y : T4)
    (v : res.SurvivingCoordinate → T4)
    (i : Fin (res.state.active.card + 1)) :
    assemble x y (res.reconstruct v)
        (res.edgeSuccessor
          (res.r324TJIE_edgeSlot i)) =
      res.r324TJIE_orderedVertices x y v
        i.succ := by
  rw [res.r324TJIE_edgeSuccessor i]
  by_cases hi : i.val < res.state.active.card
  · rw [dif_pos hi]
    let j : Fin res.state.active.card :=
      ⟨i.val, hi⟩
    have hposition :
        i.succ = varIdx j := by
      apply Fin.ext
      rfl
    rw [hposition]
    unfold r324TJIE_orderedVertices
    rw [assemble_varIdx, assemble_varIdx]
    exact res.reconstruct_surviving v
      (r324TJIE_activeOrder res j)
  · rw [dif_neg hi]
    have hiLast :
        i.succ =
          Fin.last (res.state.active.card + 1) := by
      apply Fin.ext
      change i.val + 1 = res.state.active.card + 1
      have hilt := i.isLt
      omega
    rw [hiLast]
    unfold r324TJIE_orderedVertices
    rw [assemble_last, assemble_last]

theorem r324TJIE_orderedEdge_eq
    (x y : T4)
    (v : res.SurvivingCoordinate → T4)
    (i : Fin (res.state.active.card + 1)) :
    res.state.edges
        (res.r324TJIE_edgeSlot i)
        (res.edgeDisplacement x y
          (res.reconstruct v)
          (res.r324TJIE_edgeSlot i)) =
      res.r324TJIE_orderedKernel i
        (res.r324TJIE_orderedVertices x y v
            i.castSucc -
          res.r324TJIE_orderedVertices x y v
            i.succ) := by
  unfold edgeDisplacement r324TJIE_orderedKernel
  rw [res.r324TJIE_edgeSource x y v i,
    res.r324TJIE_edgeTarget x y v i]

/-! ## The slot-zero-erased ordered chain -/

/-- The ordered tuple carrying the erased chain: the ordered surviving
internal vertices followed by the outgoing endpoint.  The incoming
endpoint does not appear. -/
def r324TJIE_erasedOrderedTuple
    (y : T4)
    (v : res.SurvivingCoordinate → T4) :
    Fin (res.state.active.card + 1) → T4 :=
  Fin.snoc (fun j => v (r324TJIE_activeOrder res j)) y

/-- Away from the incoming endpoint, the ordered vertices are the erased
ordered tuple, independently of the incoming endpoint. -/
theorem r324TJIE_orderedVertices_succ
    (x y : T4)
    (v : res.SurvivingCoordinate → T4)
    (k : Fin (res.state.active.card + 1)) :
    res.r324TJIE_orderedVertices x y v k.succ =
      res.r324TJIE_erasedOrderedTuple y v k := by
  by_cases hk : k.val < res.state.active.card
  · have hposition :
        k.succ = varIdx (⟨k.val, hk⟩ :
          Fin res.state.active.card) := by
      apply Fin.ext
      rfl
    have hcast :
        k = (⟨k.val, hk⟩ :
          Fin res.state.active.card).castSucc := by
      apply Fin.ext
      rfl
    have hrhs :
        res.r324TJIE_erasedOrderedTuple y v k =
          v (r324TJIE_activeOrder res ⟨k.val, hk⟩) := by
      conv_lhs => rw [hcast]
      unfold r324TJIE_erasedOrderedTuple
      rw [Fin.snoc_castSucc]
    rw [hposition, hrhs]
    unfold r324TJIE_orderedVertices
    rw [assemble_varIdx]
  · have hklast :
        k = Fin.last res.state.active.card := by
      apply Fin.ext
      rw [Fin.val_last]
      have hklt := k.isLt
      omega
    subst hklast
    have hsucc :
        (Fin.last res.state.active.card).succ =
          Fin.last (res.state.active.card + 1) := by
      apply Fin.ext
      rfl
    rw [hsucc]
    unfold r324TJIE_orderedVertices
      r324TJIE_erasedOrderedTuple
    rw [assemble_last, Fin.snoc_last]

/-- **The erased chain is a heterogeneous kernel path.**  At an empty
suffix the slot-zero-erased residual chain is the path of the ordered
kernels past the incoming edge, read on the erased ordered tuple; the
incoming endpoint has disappeared. -/
theorem r324TJIE_incomingErasedChainProduct_eq_path
    (hremaining : res.remaining = [])
    (x y : T4)
    (v : res.SurvivingCoordinate → T4) :
    res.incomingErasedResidualChainProduct
        x y (res.reconstruct v) =
      r324TJIE_terminalWeightedKernelPath
        (fun j : Fin res.state.active.card =>
          res.r324TJIE_orderedKernel j.succ)
        (fun _ => 1)
        (res.r324TJIE_erasedOrderedTuple y v) := by
  unfold incomingErasedResidualChainProduct
  calc
    (∏ edge ∈
        (Finset.univ : Finset (Fin (m + 1))).erase 0,
        res.residualChainEdgeFactor
          x y (res.reconstruct v) edge) =
        ∏ edge ∈ res.activeEdgeSlots.erase 0,
          res.residualChainEdgeFactor
            x y (res.reconstruct v) edge := by
      symm
      apply Finset.prod_subset
        (Finset.erase_subset_erase 0
          (Finset.subset_univ _))
      intro edge _hedgeUniv hedge
      unfold residualChainEdgeFactor
      rw [if_neg]
      intro hactive
      exact hedge
        (Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp _hedgeUniv).1, hactive⟩)
    _ =
        ∏ edge ∈ res.activeEdgeSlots.erase 0,
          res.state.edges edge
            (res.edgeDisplacement x y
              (res.reconstruct v) edge) := by
      apply Finset.prod_congr rfl
      intro edge hedge
      unfold residualChainEdgeFactor
      rw [if_pos (Finset.mem_erase.mp hedge).2]
      have hout :
          edge ∉ res.remainingOutgoingSlots := by
        simp [remainingOutgoingSlots, hremaining]
      rw [if_neg hout]
    _ =
        ∏ j : Fin res.state.active.card,
          res.state.edges
            (res.r324TJIE_edgeSlot j.succ)
            (res.edgeDisplacement x y
              (res.reconstruct v)
              (res.r324TJIE_edgeSlot j.succ)) := by
      have hzeroSlot :
          res.r324TJIE_edgeSlot 0 = 0 := by
        simp [r324TJIE_edgeSlot]
      symm
      refine Finset.prod_bij
        (fun (j : Fin res.state.active.card) _ =>
          res.r324TJIE_edgeSlot j.succ)
        ?_ ?_ ?_ ?_
      · intro j _hj
        apply Finset.mem_erase.mpr
        refine ⟨?_, res.r324TJIE_edgeSlot_mem j.succ⟩
        intro hzero
        rw [← hzeroSlot] at hzero
        exact (Fin.succ_ne_zero j)
          (res.r324TJIE_edgeSlot_injective hzero)
      · intro j₁ _hj₁ j₂ _hj₂ heq
        exact Fin.succ_injective _
          (res.r324TJIE_edgeSlot_injective heq)
      · intro edge hedge
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hedge
        obtain ⟨i, hi⟩ :=
          res.r324TJIE_edgeSlot_surjective ⟨edge, hmem⟩
        have hival : res.r324TJIE_edgeSlot i = edge :=
          congrArg Subtype.val hi
        have hi0 : i ≠ 0 := by
          intro h0
          apply hne
          rw [← hival, h0, hzeroSlot]
        refine ⟨i.pred hi0, Finset.mem_univ _, ?_⟩
        rw [Fin.succ_pred]
        exact hival
      · intro j _hj
        rfl
    _ =
        ∏ j : Fin res.state.active.card,
          res.r324TJIE_orderedKernel j.succ
            (res.r324TJIE_erasedOrderedTuple y v
                j.castSucc -
              res.r324TJIE_erasedOrderedTuple y v
                j.succ) := by
      apply Finset.prod_congr rfl
      intro j _hj
      rw [res.r324TJIE_orderedEdge_eq x y v j.succ]
      have hcast :
          (j.succ).castSucc = (j.castSucc).succ := by
        apply Fin.ext
        rfl
      rw [hcast,
        res.r324TJIE_orderedVertices_succ x y v j.castSucc,
        res.r324TJIE_orderedVertices_succ x y v j.succ]
    _ = _ := by
      unfold r324TJIE_terminalWeightedKernelPath
      simp

/-- At an empty suffix there are no remaining signed differences. -/
theorem r324TJIE_residualDifferenceProduct_eq_one_of_nil
    (hremaining : res.remaining = [])
    (x y : T4) (v : Fin m → T4) :
    res.residualDifferenceProduct x y v = 1 := by
  unfold residualDifferenceProduct
  rw [hremaining]
  rfl

/-- At an empty suffix there are no remaining primitive blocks. -/
theorem r324TJIE_residualPrimitiveProduct_eq_one_of_nil
    (hremaining : res.remaining = [])
    (ρ' : SmoothCutoff) (ε' : ℝ) (v : Fin m → T4) :
    res.residualPrimitiveProduct ρ' ε' v = 1 := by
  unfold residualPrimitiveProduct
  apply Finset.prod_eq_one
  intro j _hj
  exfalso
  have hlt := j.isLt
  have hlen : res.remaining.length = 0 :=
    congrArg List.length hremaining
  omega

/-- At an empty suffix the erased residual core is the erased chain. -/
theorem r324TJIE_incomingErasedResidualIntegrand_eq_chain_of_nil
    (hremaining : res.remaining = [])
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4) (v : Fin m → T4) :
    res.incomingErasedResidualIntegrand ρ' ε' x y v =
      res.incomingErasedResidualChainProduct x y v := by
  unfold incomingErasedResidualIntegrand
  rw [res.r324TJIE_residualDifferenceProduct_eq_one_of_nil
      hremaining,
    res.r324TJIE_residualPrimitiveProduct_eq_one_of_nil
      hremaining,
    mul_one, mul_one]

/-- **Erased-chain joint `L¹` (gap (a), ingredient (i)).**  At an empty
suffix, under a slotwise quantitative certificate, the slot-zero-erased
residual core is jointly integrable in the outgoing endpoint and all
surviving coordinates.  The pinned incoming endpoint does not occur. -/
theorem integrable_terminal_incomingErasedResidualIntegrand
    (hremaining : res.remaining = [])
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (scale : Fin (m + 1) → ℝ)
    (hcert :
      R324WithinHalfEdgeCertificate res.state scale) :
    Integrable
      (fun p : T4 × (res.SurvivingCoordinate → T4) =>
        res.incomingErasedResidualIntegrand ρ' ε' 0 p.1
          (res.reconstruct p.2))
      (paperMeasure.prod
        (Measure.pi fun _ : res.SurvivingCoordinate =>
          paperMeasure)) := by
  let n := res.state.active.card
  let K : Fin n → T4 → ℝ := fun j =>
    res.r324TJIE_orderedKernel j.succ
  let path : (Fin (n + 1) → T4) → ℝ :=
    r324TJIE_terminalWeightedKernelPath K (fun _ => 1)
  have hK (j : Fin n) :
      Integrable (K j) paperMeasure :=
    r324TJIE_integrable_of_offDiagonal_bound
      (hcert.measurable (res.r324TJIE_edgeSlot j.succ))
      (hcert.scale_pos (res.r324TJIE_edgeSlot j.succ)).le
      (hcert.bound (res.r324TJIE_edgeSlot j.succ))
  have hpath :
      Integrable path
        (Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure) :=
    r324TJIE_integrable_terminalWeightedKernelPath
      K (fun _ => 1) hK
      (fun j =>
        hcert.measurable (res.r324TJIE_edgeSlot j.succ))
      (integrable_const 1)
  let e2 :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => T4) (Fin.last n)
  have hp2 :
      MeasurePreserving e2
        (Measure.pi fun _ : Fin (n + 1) => paperMeasure)
        (paperMeasure.prod
          (Measure.pi fun _ : Fin n => paperMeasure)) := by
    simpa only [e2] using
      measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => paperMeasure)
        (Fin.last n)
  have hpair :
      Integrable
        (fun p : T4 × (Fin n → T4) =>
          path (e2.symm p))
        (paperMeasure.prod
          (Measure.pi fun _ : Fin n => paperMeasure)) :=
    (hp2.symm.integrable_comp_emb
      e2.symm.measurableEmbedding).mpr hpath
  let e1 :
      (res.SurvivingCoordinate → T4) ≃ᵐ
        (Fin n → T4) :=
    (MeasurableEquiv.piCongrLeft
      (fun _ : res.SurvivingCoordinate => T4)
      (r324TJIE_activeOrder res).toEquiv).symm
  have hp1 :
      MeasurePreserving e1
        (Measure.pi fun _ : res.SurvivingCoordinate =>
          paperMeasure)
        (Measure.pi fun _ : Fin n => paperMeasure) :=
    (measurePreserving_piCongrLeft
      (fun _ : res.SurvivingCoordinate => paperMeasure)
      (r324TJIE_activeOrder res).toEquiv).symm
  have hpE :
      MeasurePreserving
        (Prod.map (id : T4 → T4) e1)
        (paperMeasure.prod
          (Measure.pi fun _ : res.SurvivingCoordinate =>
            paperMeasure))
        (paperMeasure.prod
          (Measure.pi fun _ : Fin n => paperMeasure)) :=
    (MeasurePreserving.id paperMeasure).prod hp1
  have hembE :
      MeasurableEmbedding
        (Prod.map (id : T4 → T4) e1) :=
    MeasurableEmbedding.id.prodMap
      e1.measurableEmbedding
  have hcomp :
      Integrable
        ((fun p : T4 × (Fin n → T4) =>
          path (e2.symm p)) ∘
          Prod.map (id : T4 → T4) e1)
        (paperMeasure.prod
          (Measure.pi fun _ : res.SurvivingCoordinate =>
            paperMeasure)) :=
    (hpE.integrable_comp_emb hembE).mpr hpair
  have heinv (y : T4) (w : Fin n → T4) :
      e2.symm (y, w) = Fin.snoc w y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [e2, Fin.snoc_last]
    · simp [e2, Fin.snoc_castSucc]
  apply hcomp.congr
  filter_upwards with p
  rcases p with ⟨y, u⟩
  change path (e2.symm (y, e1 u)) = _
  rw [heinv y (e1 u)]
  have htuple :
      Fin.snoc (fun j : Fin n => (e1 u) j) y =
        res.r324TJIE_erasedOrderedTuple y u := rfl
  change
    path (res.r324TJIE_erasedOrderedTuple y u) = _
  rw [res.r324TJIE_incomingErasedResidualIntegrand_eq_chain_of_nil
      hremaining ρ' ε' 0 y (res.reconstruct u),
    res.r324TJIE_incomingErasedChainProduct_eq_path
      hremaining 0 y u]

end R324WithinHalfResidualPrefix

/-! ## Joint `L¹` of the untouched initial residual -/

/-- **Right-half initial residual joint `L¹` (gap (a), ingredient
(iii)).**  The complete initial within-half residual is jointly
integrable in its two endpoints and all initial sparse coordinates:
renormalized Green skeleton times a uniformly bounded measurable
primitive block product. -/
theorem integrable_initial_residualIntegrand_pair
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Integrable
      (fun p : (T4 × T4) ×
          ((R324WithinHalfResidualPrefix.initial
            ρ lam ε κ).SurvivingCoordinate → T4) =>
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κ).residualIntegrand ρ ε p.1.1 p.1.2
          ((R324WithinHalfResidualPrefix.initial
            ρ lam ε κ).reconstruct p.2))
      ((paperMeasure.prod paperMeasure).prod
        (Measure.pi fun _ => paperMeasure)) := by
  obtain ⟨B, _hB0, hbound⟩ :=
    ρ.exists_norm_r324InitialPrimitiveBlockProduct_le
      hε hε1 κ
  have hflat :=
    SmoothCutoff.integrable_renormalizedGreenSkeleton_flat κ
  have hweightMeas :
      Measurable
        (fun p : T4 × (T4 × (Fin m → T4)) =>
          ((∏ B' : ExtractionBlockIndex κ,
            r322ExtractionBlockPrimitiveSum
              ρ ε κ B' p.2.2 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((ρ.measurable_r324InitialPrimitiveBlockProduct
        ε κ).comp
        (measurable_snd.comp measurable_snd))
  have hprod :
      Integrable
        (fun p : T4 × (T4 × (Fin m → T4)) =>
          renormalizedGreenSkeleton κ
              (assemble p.1 p.2.1 p.2.2) *
            ((∏ B' : ExtractionBlockIndex κ,
              r322ExtractionBlockPrimitiveSum
                ρ ε κ B' p.2.2 : ℝ) : ℂ))
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin m => paperMeasure))) :=
    hflat.mul_bdd hweightMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        simpa only [Complex.norm_real] using hbound p.2.2)
  have hflatC :
      Integrable
        (fun p : T4 × (T4 × (Fin m → T4)) =>
          (((R324WithinHalfResidualPrefix.initial
              ρ lam ε κ).residualIntegrand
            ρ ε p.1 p.2.1 p.2.2 : ℝ) : ℂ))
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin m => paperMeasure))) := by
    apply hprod.congr
    filter_upwards with p
    exact
      (R324WithinHalfResidualPrefix.initial_residualIntegrand_complex_eq
        ρ lam ε κ p.1 p.2.1 p.2.2).symm
  have hflatR :
      Integrable
        (fun p : T4 × (T4 × (Fin m → T4)) =>
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κ).residualIntegrand
            ρ ε p.1 p.2.1 p.2.2)
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin m => paperMeasure))) := by
    apply hflatC.re.congr
    filter_upwards with p
    exact RCLike.ofReal_re _
  have hassoc :
      Integrable
        (fun p : (T4 × T4) × (Fin m → T4) =>
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κ).residualIntegrand
            ρ ε p.1.1 p.1.2 p.2)
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ : Fin m => paperMeasure)) := by
    have hp :=
      measurePreserving_prodAssoc paperMeasure paperMeasure
        (Measure.pi fun _ : Fin m => paperMeasure)
    have h :=
      (hp.integrable_comp_emb
        (MeasurableEquiv.prodAssoc
          (α := T4) (β := T4)
          (γ := Fin m → T4)).measurableEmbedding).mpr
        hflatR
    apply h.congr
    filter_upwards with p
    rfl
  let eInit :=
    R324WithinHalfResidualPrefix.initialPiMeasurableEquiv
      ρ lam ε κ
  have hpE :
      MeasurePreserving
        (Prod.map (id : T4 × T4 → T4 × T4) eInit)
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κ).SurvivingCoordinate =>
              paperMeasure))
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ : Fin m => paperMeasure)) :=
    (MeasurePreserving.id
      (paperMeasure.prod paperMeasure)).prod
      (R324WithinHalfResidualPrefix.measurePreserving_initialPiMeasurableEquiv
        ρ lam ε κ)
  have hcomp :
      Integrable
        ((fun p : (T4 × T4) × (Fin m → T4) =>
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κ).residualIntegrand
            ρ ε p.1.1 p.1.2 p.2) ∘
          Prod.map (id : T4 × T4 → T4 × T4) eInit)
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ =>
            paperMeasure)) :=
    (hpE.integrable_comp_emb
      (MeasurableEmbedding.id.prodMap
        eInit.measurableEmbedding)).mpr hassoc
  apply hcomp.congr
  filter_upwards with p
  change
    (R324WithinHalfResidualPrefix.initial
      ρ lam ε κ).residualIntegrand
      ρ ε p.1.1 p.1.2 (eInit p.2) = _
  rw [← R324WithinHalfResidualPrefix.initial_reconstruct_eq
    ρ lam ε κ p.2]

/-! ## Measurability of the doubled root reconstruction -/

/-- The doubled ambient tuple assembled from two sparse carriers is
jointly measurable. -/
theorem measurable_r324TwoHalfRootDoubledReconstruct
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (leftRes : R324WithinHalfResidualPrefix ρ lam ε κp)
    (rightRes : R324WithinHalfResidualPrefix ρ lam ε κm) :
    Measurable
      (r324TwoHalfRootDoubledReconstruct
        leftRes rightRes) := by
  apply measurable_pi_lambda
  intro k
  generalize hs :
      (momentDoubleFinEquiv m).symm k = s
  cases s with
  | inl i =>
      have hleft :
          Measurable
            (fun p :
                (leftRes.SurvivingCoordinate → T4) ×
                  (rightRes.SurvivingCoordinate → T4) =>
              leftRes.reconstruct p.1) :=
        leftRes.measurable_reconstruct.comp measurable_fst
      simp only [r324TwoHalfRootDoubledReconstruct, hs]
      exact (measurable_pi_apply i).comp hleft
  | inr j =>
      have hright :
          Measurable
            (fun p :
                (leftRes.SurvivingCoordinate → T4) ×
                  (rightRes.SurvivingCoordinate → T4) =>
              rightRes.reconstruct p.2) :=
        rightRes.measurable_reconstruct.comp measurable_snd
      simp only [r324TwoHalfRootDoubledReconstruct, hs]
      exact (measurable_pi_apply j).comp hright

/-! ## The terminal certificate of the alternating driver -/

namespace R324WithinHalfResidualPrefix

namespace R324WithinHalfAlternatingTransport

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- Bounded-length form of the terminal-certificate extraction along the
alternating driver recursion. -/
theorem exists_final_edgeCertificate_of_localBlockProvider_of_le
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing) :
    ∀ (N : ℕ)
      (res : R324WithinHalfResidualPrefix ρ lam ε pairing),
      res.remaining.length ≤ N →
      ∀ (scale : Fin (m + 1) → ℝ)
        (certificate :
          R324WithinHalfEdgeCertificate res.state scale),
        ∃ finalScale : Fin (m + 1) → ℝ,
          R324WithinHalfEdgeCertificate
            (of_localBlockProvider
              hε hε1 provider res scale certificate).final.state
            finalScale := by
  intro N
  induction N with
  | zero =>
      intro res hlen scale certificate
      have hrun :
          r324WithinHalfOrdinaryRunLength
              res.state.processed res.remaining =
            res.remaining.length := by
        have hle :=
          r324WithinHalfOrdinaryRunLength_le_length
            res.state.processed res.remaining
        omega
      rw [of_localBlockProvider, dif_pos hrun]
      exact
        ⟨_,
          (R324WithinHalfCertifiedAnalyticTrace.of_localBlockProvider
            hε hε1 provider res scale
            certificate).terminalCertificate⟩
  | succ N ih =>
      intro res hlen scale certificate
      rw [of_localBlockProvider]
      by_cases hrun :
          r324WithinHalfOrdinaryRunLength
              res.state.processed res.remaining =
            res.remaining.length
      · rw [dif_pos hrun]
        exact
          ⟨_,
            (R324WithinHalfCertifiedAnalyticTrace.of_localBlockProvider
              hε hε1 provider res scale
              certificate).terminalCertificate⟩
      · rw [dif_neg hrun]
        apply ih
        rw [R324WithinHalfResidualPrefix.afterHead_remaining]
        have hlt :=
          R324WithinHalfNextExceptionalStop.suffix_length_lt
            ((nonempty_r324WithinHalfNextExceptionalStop_of_lt_length
              hε hε1 provider res scale certificate
              (lt_of_le_of_ne
                (r324WithinHalfOrdinaryRunLength_le_length
                  res.state.processed res.remaining)
                hrun)).some)
        omega

/-- **Terminal certificate of the alternating driver.**  The driver built
from a local block provider carries a slotwise quantitative certificate on
its terminal edge state. -/
theorem exists_final_edgeCertificate_of_localBlockProvider
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing)
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale) :
    ∃ finalScale : Fin (m + 1) → ℝ,
      R324WithinHalfEdgeCertificate
        (of_localBlockProvider
          hε hε1 provider res scale certificate).final.state
        finalScale :=
  exists_final_edgeCertificate_of_localBlockProvider_of_le
    hε hε1 provider res.remaining.length res le_rfl
    scale certificate

end R324WithinHalfAlternatingTransport

end R324WithinHalfResidualPrefix

/-! ## Discharge of the driver-terminal joint integrability -/

namespace R324WithinHalfResidualPrefix

namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- **Gap (a) discharged from a terminal certificate.**  Any alternating
transport whose terminal edge state carries a slotwise quantitative
certificate satisfies the driver-terminal joint integrability: the
phased density is the product of the `L¹` erased terminal chain in
`(y, u)`, the `L¹` untouched right initial residual in `(zw, vr)`, the
bounded measurable cross-cut primitive factor, and a unimodular phase
with constant amplitude. -/
theorem driverTerminalJointIntegrable_of_terminal_certificate
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
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (finalScale : Fin (m + 1) → ℝ)
    (hcert :
      R324WithinHalfEdgeCertificate
        t.final.state finalScale) :
    data.DriverTerminalJointIntegrable t α β π := by
  classical
  have h₁ :=
    integrable_initial_residualIntegrand_pair
      ρ lam hε hε1 κm
  have h₂ :=
    t.final.integrable_terminal_incomingErasedResidualIntegrand
      t.final_remaining ρ ε finalScale hcert
  have hsource :=
    (h₁.ofReal (𝕜 := ℂ)).mul_prod (h₂.ofReal (𝕜 := ℂ))
  let e :=
    r324DriverTerminalRegroupMeasurableEquiv
      T4 (T4 × T4)
      ((R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).SurvivingCoordinate → T4)
      (t.final.SurvivingCoordinate → T4)
  have hp :=
    measurePreserving_r324DriverTerminalRegroupMeasurableEquiv
      paperMeasure (paperMeasure.prod paperMeasure)
      (Measure.pi fun _ :
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κm).SurvivingCoordinate => paperMeasure)
      (Measure.pi fun _ :
        t.final.SurvivingCoordinate => paperMeasure)
  have hbare :=
    (hp.integrable_comp_emb e.measurableEmbedding).mpr
      hsource
  obtain ⟨Bc, _hBc0, hBc⟩ :=
    ρ.exists_norm_r324ResidualPrimitiveSumProduct_le
      hε hε1 κp κm π
  have hXmeas :
      Measurable
        (fun q :
            R324IncomingExceptionalRootParameter
                ρ lam ε κm ×
              (t.final.SurvivingCoordinate → T4) =>
          ((r324ResidualPrimitiveSumProduct
            ρ ε κp κm π
            (r324TwoHalfRootDoubledReconstruct
              t.final
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κm)
              (q.2, q.1.2)) : ℝ) : ℂ)) := by
    apply Complex.measurable_ofReal.comp
    apply (ρ.measurable_r324ResidualPrimitiveSumProduct
      ε κp κm π).comp
    apply (measurable_r324TwoHalfRootDoubledReconstruct
      t.final
      (R324WithinHalfResidualPrefix.initial
        ρ lam ε κm)).comp
    exact measurable_snd.prodMk
      (measurable_snd.comp measurable_fst)
  have hwithCross :=
    hbare.mul_bdd hXmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by
        simpa only [Complex.norm_real] using
          hBc (r324TwoHalfRootDoubledReconstruct
            t.final
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε κm)
            (q.2, q.1.2)))
  let defect : ℂ :=
    incomingExceptionalPrimitiveDefect ρ lam ε
      (residualBlockOrder data.terminal.2)
      data.stopContext.one_le_blockOrder
      data.stopContext.internalEdges α
  let M :
      R324IncomingExceptionalRootParameter
          ρ lam ε κm ×
        (t.final.SurvivingCoordinate → T4) → ℂ :=
    fun q =>
      t.multiplier α *
        ((paperSecondOrderModeDecay α : ℂ) ^ 2 * defect) *
        (charT4 β q.1.1.1 *
          charT4 (-α) q.1.1.2.1 *
          charT4 (-β) q.1.1.2.2 *
          charT4 α
            (t.final.incomingPhaseAnchor 0 q.1.1.1 q.2))
  have hyMeas :
      Measurable
        (fun q :
            R324IncomingExceptionalRootParameter
                ρ lam ε κm ×
              (t.final.SurvivingCoordinate → T4) =>
          q.1.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hanchorMeas :
      Measurable
        (fun q :
            R324IncomingExceptionalRootParameter
                ρ lam ε κm ×
              (t.final.SurvivingCoordinate → T4) =>
          t.final.incomingPhaseAnchor 0 q.1.1.1 q.2) := by
    have hassembleMeas :
        Measurable
          (fun q :
              R324IncomingExceptionalRootParameter
                  ρ lam ε κm ×
                (t.final.SurvivingCoordinate → T4) =>
            assemble (0 : T4) q.1.1.1
              (t.final.reconstruct q.2)) :=
      (measurable_assemble_prod m).comp
        (measurable_const.prodMk
          (hyMeas.prodMk
            (t.final.measurable_reconstruct.comp
              measurable_snd)))
    exact
      (measurable_pi_apply
        (t.final.edgeSuccessor 0)).comp hassembleMeas
  have hMmeas : Measurable M := by
    apply Measurable.mul
    · exact measurable_const
    · apply Measurable.mul
      · apply Measurable.mul
        · apply Measurable.mul
          · exact
              (continuous_charT4 β).measurable.comp hyMeas
          · exact
              (continuous_charT4 (-α)).measurable.comp
                ((measurable_fst.comp
                  (measurable_snd.comp
                    (measurable_fst.comp measurable_fst))))
        · exact
            (continuous_charT4 (-β)).measurable.comp
              ((measurable_snd.comp
                (measurable_snd.comp
                  (measurable_fst.comp measurable_fst))))
      · exact
          (continuous_charT4 α).measurable.comp hanchorMeas
  have hMbound :
      ∀ q, ‖M q‖ ≤
        ‖t.multiplier α‖ *
          (paperSecondOrderModeDecay α ^ 2 * ‖defect‖) := by
    intro q
    dsimp only [M]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
      norm_mul, norm_charT4, norm_charT4, norm_charT4,
      norm_charT4, norm_pow, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (paperSecondOrderModeDecay_nonneg α)]
    simp
  have hfull :=
    hwithCross.bdd_mul hMmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hMbound)
  unfold DriverTerminalJointIntegrable
  apply hfull.congr
  filter_upwards with q
  show
    M q *
        ((((R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).residualIntegrand
            ρ ε
            (e q).1.1.1 (e q).1.1.2
            ((R324WithinHalfResidualPrefix.initial
              ρ lam ε κm).reconstruct (e q).1.2) : ℝ) *
          ((t.final.incomingErasedResidualIntegrand
            ρ ε 0 (e q).2.1
            (t.final.reconstruct (e q).2.2) : ℝ) : ℂ)) *
          ((r324ResidualPrimitiveSumProduct
            ρ ε κp κm π
            (r324TwoHalfRootDoubledReconstruct
              t.final
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κm)
              (q.2, q.1.2)) : ℝ) : ℂ)) = _
  rw [r324DriverTerminalRegroupMeasurableEquiv_apply]
  unfold R324WithinHalfResidualPrefix.incomingPhasedResidualDensity
    incomingExceptionalRefinedRootDriverCoefficient
    incomingExceptionalRefinedRootDriverPostOuter
  dsimp only [M, defect]
  ring

/-- **Gap (a) discharged for the canonical driver transport.**  The
alternating transport constructed by the driver from the local block
provider satisfies the driver-terminal joint integrability; its terminal
certificate is extracted from the `of_localBlockProvider` recursion. -/
theorem driverTerminalJointIntegrable_afterHeadAlternatingTransport
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κp)
    (α β : Z4)
    (π : κp.singles ≃ κm.singles) :
    data.DriverTerminalJointIntegrable
      (data.afterHeadAlternatingTransport hε hε1 provider)
      α β π := by
  obtain ⟨finalScale, hcert⟩ :=
    R324WithinHalfAlternatingTransport.exists_final_edgeCertificate_of_localBlockProvider
      hε hε1 provider
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq)
      (r324WithinHalfUpdatedEdgeScale
        data.stopContext data.stopScale C lam K)
      (provider data.trace.stopPrefix
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        data.stopScale data.stopCertificate).2
  exact
    data.driverTerminalJointIntegrable_of_terminal_certificate
      (data.afterHeadAlternatingTransport hε hε1 provider)
      α β π hε hε1 finalScale hcert

end R324IncomingExceptionalStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
