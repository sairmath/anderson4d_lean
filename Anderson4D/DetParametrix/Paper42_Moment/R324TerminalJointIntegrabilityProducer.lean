import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointJointIntegrabilityAdapter
import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualPrimitiveCoordinateExpansion

/-!
# Terminal joint-integrability producer for R-324

This file supplies the two analytic ingredients needed for the premise
isolated in `R324EndpointJointIntegrabilityAdapter`.  A completed within-half
trace is a finite heterogeneous Haar path.  Its terminal edge certificate
makes every edge genuinely `L¹`; the complete residual primitive sum is a
bounded measurable finite product at positive mollification scale.  A
successor module combines the two half paths with that bounded factor and
performs the remaining product-measure regrouping.

The path argument below is local because the corresponding general theorem
in `R322AnalyticReachableIntegrability` is private.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Local heterogeneous Haar-path theorem -/

private theorem r324TerminalJI_integrable_kernel_sub_mul_lift
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
  have hKnorm : Integrable Knorm paperMeasure := hK.norm
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

private def r324TerminalJI_terminalWeightedKernelPath
    {n : ℕ}
    (K : Fin n → T4 → ℝ)
    (terminalWeight : T4 → ℝ)
    (x : Fin (n + 1) → T4) : ℝ :=
  (∏ i : Fin n,
      K i (x i.castSucc - x i.succ)) *
    terminalWeight (x (Fin.last n))

private theorem r324TerminalJI_integrable_terminalWeightedKernelPath :
    ∀ {n : ℕ}
      (K : Fin n → T4 → ℝ)
      (terminalWeight : T4 → ℝ),
      (∀ i, Integrable (K i) paperMeasure) →
      (∀ i, Measurable (K i)) →
      Integrable terminalWeight paperMeasure →
      Integrable
        (r324TerminalJI_terminalWeightedKernelPath K terminalWeight)
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
      simp [r324TerminalJI_terminalWeightedKernelPath, e]
  | succ n ih =>
      intro K terminalWeight hK hKmeas hterminal
      let tailK : Fin n → T4 → ℝ :=
        fun i => K i.succ
      let μtail :=
        Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure
      let tailPath : (Fin (n + 1) → T4) → ℝ :=
        r324TerminalJI_terminalWeightedKernelPath
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
        r324TerminalJI_integrable_kernel_sub_mul_lift
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
              r324TerminalJI_terminalWeightedKernelPath
                K terminalWeight (e.symm p))
            (paperMeasure.prod μtail) := by
        apply htarget.congr
        filter_upwards with p
        rcases p with ⟨y, v⟩
        rw [heinv y v]
        simp only [r324TerminalJI_terminalWeightedKernelPath,
          Fin.prod_univ_succ, Fin.cons_succ]
        change
          K 0 (y - v 0) * tailPath v =
            (K 0 (y - v 0) *
              ∏ i : Fin n,
                K i.succ
                  (v i.castSucc - v i.succ)) *
              terminalWeight (v (Fin.last n))
        unfold tailPath
          r324TerminalJI_terminalWeightedKernelPath tailK
        ring
      have hpull :
          Integrable
            ((fun p : T4 × (Fin (n + 1) → T4) =>
              r324TerminalJI_terminalWeightedKernelPath
                K terminalWeight (e.symm p)) ∘ e)
            (Measure.pi fun _ : Fin (n + 2) =>
              paperMeasure) :=
        (hp.integrable_comp_emb e.measurableEmbedding).mpr
          htarget'
      convert hpull using 1
      funext x
      simp only [Function.comp_apply,
        e.symm_apply_apply]

private theorem r324TerminalJI_integrable_of_offDiagonal_bound
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

/-! ## The ordered sparse chain of a completed half -/

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)

private def r324TerminalJI_activeOrder :
    Fin res.state.active.card ≃o
      {i : Fin m // i ∈ res.state.active} :=
  res.state.active.orderIsoOfFin rfl

/-- The zeroth sparse edge is the incoming edge; every later sparse edge
starts at the correspondingly ordered surviving internal vertex. -/
private def r324TerminalJI_edgeSlot
    (i : Fin (res.state.active.card + 1)) :
    Fin (m + 1) :=
  if hi : i.val = 0 then
    0
  else
      r324InternalVertexEdgeSlot
        (r324TerminalJI_activeOrder res
          ⟨i.val - 1, by
            have hilt := i.isLt
            omega⟩).1

private theorem r324TerminalJI_edgeSlot_mem
    (i : Fin (res.state.active.card + 1)) :
    res.r324TerminalJI_edgeSlot i ∈
      res.activeEdgeSlots := by
  by_cases hi : i.val = 0
  · rw [r324TerminalJI_edgeSlot, dif_pos hi]
    exact res.zero_mem_activeEdgeSlots
  · rw [r324TerminalJI_edgeSlot, dif_neg hi]
    exact
      res.internalVertexEdgeSlot_mem_activeEdgeSlots
        (r324TerminalJI_activeOrder res
          ⟨i.val - 1, by
            have hilt := i.isLt
            omega⟩).1
        (r324TerminalJI_activeOrder res
          ⟨i.val - 1, by
            have hilt := i.isLt
            omega⟩).2

private theorem r324TerminalJI_edgeSlot_strictMono :
    StrictMono res.r324TerminalJI_edgeSlot := by
  intro i j hij
  by_cases hi0 : i.val = 0
  · have hj0 : j.val ≠ 0 := by omega
    simp only [r324TerminalJI_edgeSlot,
      hi0, hj0, dif_pos]
    change
      (0 : Fin (m + 1)) <
        r324InternalVertexEdgeSlot
          (r324TerminalJI_activeOrder res
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
      ((r324TerminalJI_activeOrder res).lt_iff_lt).mpr hab
    simp only [r324TerminalJI_edgeSlot,
      hi0, hj0]
    exact Fin.mk_lt_mk.mpr (Nat.succ_lt_succ horder)

private theorem r324TerminalJI_edgeSlot_injective :
    Function.Injective res.r324TerminalJI_edgeSlot :=
  res.r324TerminalJI_edgeSlot_strictMono.injective

private theorem r324TerminalJI_edgeSlot_surjective :
    Function.Surjective
      (fun i : Fin (res.state.active.card + 1) =>
        (⟨res.r324TerminalJI_edgeSlot i,
          res.r324TerminalJI_edgeSlot_mem i⟩ :
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
    simpa [r324TerminalJI_edgeSlot] using heq.symm
  · obtain ⟨a, ha, haedge⟩ :=
      Finset.mem_image.mp hinter
    let j : Fin res.state.active.card :=
      (r324TerminalJI_activeOrder res).symm ⟨a, ha⟩
    let i : Fin (res.state.active.card + 1) :=
      ⟨j.val + 1, by
        have hjlt := j.isLt
        omega⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    have hi0 : i.val ≠ 0 := by
      dsimp only [i]
      omega
    change res.r324TerminalJI_edgeSlot i = edge.1
    rw [r324TerminalJI_edgeSlot, dif_neg hi0]
    have hindex :
        (⟨i.val - 1, by
            have hilt := i.isLt
            omega⟩ :
          Fin res.state.active.card) = j := by
      apply Fin.ext
      dsimp only [i]
      omega
    have horderIndex :=
      congrArg (r324TerminalJI_activeOrder res) hindex
    rw [horderIndex]
    change
      r324InternalVertexEdgeSlot
          (r324TerminalJI_activeOrder res j).1 =
        edge.1
    rw [show
      r324TerminalJI_activeOrder res j = ⟨a, ha⟩ by
        exact
          (r324TerminalJI_activeOrder res).apply_symm_apply
            ⟨a, ha⟩]
    exact haedge

private def r324TerminalJI_activeEdgeEquiv :
    Fin (res.state.active.card + 1) ≃
      {edge : Fin (m + 1) //
        edge ∈ res.activeEdgeSlots} :=
  Equiv.ofBijective
    (fun i =>
      ⟨res.r324TerminalJI_edgeSlot i,
        res.r324TerminalJI_edgeSlot_mem i⟩)
    ⟨by
      intro i j hij
      exact
        res.r324TerminalJI_edgeSlot_injective
          (congrArg Subtype.val hij),
      res.r324TerminalJI_edgeSlot_surjective⟩

/-- The ordered point corresponding to a terminal half-chain. -/
private def r324TerminalJI_orderedVertices
    (x y : T4)
    (v : res.SurvivingCoordinate → T4) :
    Fin (res.state.active.card + 2) → T4 :=
  assemble x y
    (fun j => v (r324TerminalJI_activeOrder res j))

private def r324TerminalJI_orderedKernel
    (i : Fin (res.state.active.card + 1)) :
    T4 → ℝ :=
  res.state.edges (res.r324TerminalJI_edgeSlot i)

private theorem r324TerminalJI_edgeSlot_lt_target
    (i : Fin (res.state.active.card + 1))
    (hi : i.val < res.state.active.card) :
    (res.r324TerminalJI_edgeSlot i).val <
      (varIdx
        (r324TerminalJI_activeOrder res
          ⟨i.val, hi⟩).1).val := by
  by_cases hi0 : i.val = 0
  · rw [r324TerminalJI_edgeSlot, dif_pos hi0]
    change
      0 <
        (r324TerminalJI_activeOrder res
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
      ((r324TerminalJI_activeOrder res).lt_iff_lt).mpr
        hjlt
    rw [r324TerminalJI_edgeSlot, dif_neg hi0]
    change
      (r324TerminalJI_activeOrder res
          ⟨i.val - 1, by
            have hilt := i.isLt
            omega⟩).1.val + 1 <
        (r324TerminalJI_activeOrder res
          ⟨i.val, hi⟩).1.val + 1
    change
      (r324TerminalJI_activeOrder res j).1.val + 1 <
        (r324TerminalJI_activeOrder res
          ⟨i.val, hi⟩).1.val + 1
    exact Nat.succ_lt_succ horder

private theorem r324TerminalJI_index_le_of_edgeSlot_lt_varIdx
    (i : Fin (res.state.active.card + 1))
    (a : res.SurvivingCoordinate)
    (h :
      (res.r324TerminalJI_edgeSlot i).val <
        (varIdx a.1).val) :
    i.val ≤
      ((r324TerminalJI_activeOrder res).symm a).val := by
  by_cases hi0 : i.val = 0
  · omega
  · let j : Fin res.state.active.card :=
      ⟨i.val - 1, by
        have hilt := i.isLt
        omega⟩
    rw [r324TerminalJI_edgeSlot, dif_neg hi0] at h
    change
      (r324TerminalJI_activeOrder res j).1.val + 1 <
        a.1.val + 1 at h
    have hactive :
        r324TerminalJI_activeOrder res j < a := by
      change
        (r324TerminalJI_activeOrder res j).1 < a.1
      exact Fin.mk_lt_mk.mpr
        (Nat.lt_of_succ_lt_succ h)
    have hordinal :
        j <
          (r324TerminalJI_activeOrder res).symm a := by
      apply
        ((r324TerminalJI_activeOrder res).lt_iff_lt).mp
      rw [(r324TerminalJI_activeOrder res).apply_symm_apply]
      exact hactive
    have hiVal : i.val = j.val + 1 := by
      dsimp only [j]
      omega
    rw [hiVal]
    exact Nat.succ_le_iff.mpr hordinal

/-- The successor selected by the sparse state is exactly the next ordered
surviving vertex, or the terminal external point after the last edge. -/
private theorem r324TerminalJI_edgeSuccessor
    (i : Fin (res.state.active.card + 1)) :
    res.edgeSuccessor
        (res.r324TerminalJI_edgeSlot i) =
      if hi : i.val < res.state.active.card then
        varIdx
          (r324TerminalJI_activeOrder res
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
        ⟨(r324TerminalJI_activeOrder res
            ⟨i.val, hi⟩).1,
          Finset.mem_filter.mpr
            ⟨(r324TerminalJI_activeOrder res
                ⟨i.val, hi⟩).2,
              res.r324TerminalJI_edgeSlot_lt_target i hi⟩,
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
          (r324TerminalJI_activeOrder res).symm a'
        have hijVal : i.val ≤ j.val :=
          res.r324TerminalJI_index_le_of_edgeSlot_lt_varIdx
            i a' hedgeLt
        have hij : (⟨i.val, hi⟩ :
            Fin res.state.active.card) ≤ j :=
          Fin.mk_le_mk.mpr hijVal
        have hmono :=
          (r324TerminalJI_activeOrder res).monotone hij
        have hjapply :
            r324TerminalJI_activeOrder res j = a' :=
          (r324TerminalJI_activeOrder res).apply_symm_apply a'
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
              ((r324TerminalJI_activeOrder res).symm a').val :=
          res.r324TerminalJI_index_le_of_edgeSlot_lt_varIdx
            i a' (Finset.mem_filter.mp ha).2
        have hiLast : i.val = res.state.active.card := by
          have hilt := i.isLt
          omega
        have hjlt :=
          ((r324TerminalJI_activeOrder res).symm a').isLt
        omega

private theorem r324TerminalJI_edgeSource
    (x y : T4)
    (v : res.SurvivingCoordinate → T4)
    (i : Fin (res.state.active.card + 1)) :
    assemble x y (res.reconstruct v)
        (res.r324TerminalJI_edgeSlot i).castSucc =
      res.r324TerminalJI_orderedVertices x y v
        i.castSucc := by
  by_cases hi0 : i.val = 0
  · have hieq : i = 0 := Fin.ext hi0
    subst i
    simp [r324TerminalJI_edgeSlot,
      r324TerminalJI_orderedVertices]
  · let j : Fin res.state.active.card :=
      ⟨i.val - 1, by
        have hilt := i.isLt
        omega⟩
    have hslot :
        (res.r324TerminalJI_edgeSlot i).castSucc =
          varIdx
            (r324TerminalJI_activeOrder res j).1 := by
      apply Fin.ext
      rw [r324TerminalJI_edgeSlot, dif_neg hi0]
      rfl
    have hposition :
        i.castSucc =
          varIdx j := by
      apply Fin.ext
      change i.val = j.val + 1
      dsimp only [j]
      omega
    rw [hslot, hposition]
    unfold r324TerminalJI_orderedVertices
    rw [assemble_varIdx, assemble_varIdx]
    exact res.reconstruct_surviving v
      (r324TerminalJI_activeOrder res j)

private theorem r324TerminalJI_edgeTarget
    (x y : T4)
    (v : res.SurvivingCoordinate → T4)
    (i : Fin (res.state.active.card + 1)) :
    assemble x y (res.reconstruct v)
        (res.edgeSuccessor
          (res.r324TerminalJI_edgeSlot i)) =
      res.r324TerminalJI_orderedVertices x y v
        i.succ := by
  rw [res.r324TerminalJI_edgeSuccessor i]
  by_cases hi : i.val < res.state.active.card
  · rw [dif_pos hi]
    let j : Fin res.state.active.card :=
      ⟨i.val, hi⟩
    have hposition :
        i.succ = varIdx j := by
      apply Fin.ext
      rfl
    rw [hposition]
    unfold r324TerminalJI_orderedVertices
    rw [assemble_varIdx, assemble_varIdx]
    exact res.reconstruct_surviving v
      (r324TerminalJI_activeOrder res j)
  · rw [dif_neg hi]
    have hiLast :
        i.succ =
          Fin.last (res.state.active.card + 1) := by
      apply Fin.ext
      change i.val + 1 = res.state.active.card + 1
      have hilt := i.isLt
      omega
    rw [hiLast]
    unfold r324TerminalJI_orderedVertices
    rw [assemble_last, assemble_last]

private theorem r324TerminalJI_orderedEdge_eq
    (x y : T4)
    (v : res.SurvivingCoordinate → T4)
    (i : Fin (res.state.active.card + 1)) :
    res.state.edges
        (res.r324TerminalJI_edgeSlot i)
        (res.edgeDisplacement x y
          (res.reconstruct v)
          (res.r324TerminalJI_edgeSlot i)) =
      res.r324TerminalJI_orderedKernel i
        (res.r324TerminalJI_orderedVertices x y v
            i.castSucc -
          res.r324TerminalJI_orderedVertices x y v
            i.succ) := by
  unfold edgeDisplacement r324TerminalJI_orderedKernel
  rw [res.r324TerminalJI_edgeSource x y v i,
    res.r324TerminalJI_edgeTarget x y v i]

/-- At an empty suffix the literal residual chain is exactly the standard
ordered heterogeneous path attached to its certified edge state. -/
private theorem r324TerminalJI_residualChainProduct_eq_path
    (hremaining : res.remaining = [])
    (x y : T4)
    (v : res.SurvivingCoordinate → T4) :
    res.residualChainProduct x y (res.reconstruct v) =
      r324TerminalJI_terminalWeightedKernelPath
        res.r324TerminalJI_orderedKernel
        (fun _ => 1)
        (res.r324TerminalJI_orderedVertices x y v) := by
  unfold residualChainProduct
  calc
    (∏ edge : Fin (m + 1),
        res.residualChainEdgeFactor
          x y (res.reconstruct v) edge) =
        ∏ edge ∈ res.activeEdgeSlots,
          res.residualChainEdgeFactor
            x y (res.reconstruct v) edge := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro edge _hedgeUniv hedge
      unfold residualChainEdgeFactor
      rw [if_neg hedge]
    _ =
        ∏ edge ∈ res.activeEdgeSlots,
          res.state.edges edge
            (res.edgeDisplacement x y
              (res.reconstruct v) edge) := by
      apply Finset.prod_congr rfl
      intro edge hedge
      unfold residualChainEdgeFactor
      rw [if_pos hedge]
      have hout :
          edge ∉ res.remainingOutgoingSlots := by
        simp [remainingOutgoingSlots, hremaining]
      rw [if_neg hout]
    _ =
        ∏ edge :
            {edge : Fin (m + 1) //
              edge ∈ res.activeEdgeSlots},
          res.state.edges edge.1
            (res.edgeDisplacement x y
              (res.reconstruct v) edge.1) := by
      symm
      exact
        Finset.prod_coe_sort res.activeEdgeSlots
          (fun edge =>
            res.state.edges edge
              (res.edgeDisplacement x y
                (res.reconstruct v) edge))
    _ =
        ∏ i : Fin (res.state.active.card + 1),
          res.state.edges
            (res.r324TerminalJI_edgeSlot i)
            (res.edgeDisplacement x y
              (res.reconstruct v)
              (res.r324TerminalJI_edgeSlot i)) := by
      exact
        (Equiv.prod_comp
          res.r324TerminalJI_activeEdgeEquiv
          (fun edge :
              {edge : Fin (m + 1) //
                edge ∈ res.activeEdgeSlots} =>
            res.state.edges edge.1
              (res.edgeDisplacement x y
                (res.reconstruct v) edge.1))).symm
    _ =
        ∏ i : Fin (res.state.active.card + 1),
          res.r324TerminalJI_orderedKernel i
            (res.r324TerminalJI_orderedVertices x y v
                i.castSucc -
              res.r324TerminalJI_orderedVertices x y v
                i.succ) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact res.r324TerminalJI_orderedEdge_eq x y v i
    _ = _ := by
      unfold r324TerminalJI_terminalWeightedKernelPath
      simp

/-! ## Genuine joint integrability of one completed sparse half-chain -/

private def r324TerminalJI_survivingPiMeasurableEquiv :
    (res.SurvivingCoordinate → T4) ≃ᵐ
      (Fin res.state.active.card → T4) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : res.SurvivingCoordinate => T4)
    res.r324TerminalJI_activeOrder.toEquiv).symm

private theorem
    r324TerminalJI_measurePreserving_survivingPiMeasurableEquiv :
    MeasurePreserving
      res.r324TerminalJI_survivingPiMeasurableEquiv
      (Measure.pi fun _ : res.SurvivingCoordinate =>
        paperMeasure)
      (Measure.pi fun _ : Fin res.state.active.card =>
        paperMeasure) := by
  simpa only [r324TerminalJI_survivingPiMeasurableEquiv] using
    (measurePreserving_piCongrLeft
      (fun _ : res.SurvivingCoordinate => paperMeasure)
      res.r324TerminalJI_activeOrder.toEquiv).symm

@[simp]
private theorem r324TerminalJI_survivingPiMeasurableEquiv_apply
    (v : res.SurvivingCoordinate → T4)
    (i : Fin res.state.active.card) :
    res.r324TerminalJI_survivingPiMeasurableEquiv v i =
      v (res.r324TerminalJI_activeOrder i) :=
  rfl

/-- A terminal slotwise inverse-square certificate gives joint `L¹`
control of the literal completed half-chain in both endpoints and all
surviving coordinates. -/
theorem integrable_terminalResidualChainProduct
    (hremaining : res.remaining = [])
    (scale : Fin (m + 1) → ℝ)
    (hcert :
      R324WithinHalfEdgeCertificate res.state scale) :
    Integrable
      (fun p :
          T4 × (T4 ×
            (res.SurvivingCoordinate → T4)) =>
        res.residualChainProduct
          p.1 p.2.1 (res.reconstruct p.2.2))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : res.SurvivingCoordinate =>
            paperMeasure))) := by
  let n := res.state.active.card
  let K : Fin (n + 1) → T4 → ℝ :=
    res.r324TerminalJI_orderedKernel
  let path : (Fin (n + 2) → T4) → ℝ :=
    r324TerminalJI_terminalWeightedKernelPath
      K (fun _ => 1)
  have hK (i : Fin (n + 1)) :
      Integrable (K i) paperMeasure := by
    exact
      r324TerminalJI_integrable_of_offDiagonal_bound
        (hcert.measurable
          (res.r324TerminalJI_edgeSlot i))
        (hcert.scale_pos
          (res.r324TerminalJI_edgeSlot i)).le
        (hcert.bound
          (res.r324TerminalJI_edgeSlot i))
  have hpath :
      Integrable path
        (Measure.pi fun _ : Fin (n + 2) =>
          paperMeasure) := by
    exact
      r324TerminalJI_integrable_terminalWeightedKernelPath
        K (fun _ => 1) hK
        (fun i =>
          hcert.measurable
            (res.r324TerminalJI_edgeSlot i))
        (integrable_const 1)
  let eFlat := r324FlatAssembleMeasurableEquiv n
  let μTuple :=
    Measure.pi fun _ : Fin (n + 2) => paperMeasure
  let μFinFlat :=
    paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : Fin n => paperMeasure))
  have hpFlat :
      MeasurePreserving eFlat μTuple μFinFlat := by
    simpa only [eFlat, μTuple, μFinFlat] using
      measurePreserving_r324FlatAssembleMeasurableEquiv n
  have hFinFlat :
      Integrable
        (fun p : T4 × (T4 × (Fin n → T4)) =>
          path (assemble p.1 p.2.1 p.2.2))
        μFinFlat := by
    have htarget :
        Integrable
          (fun p : T4 × (T4 × (Fin n → T4)) =>
            path (eFlat.symm p))
          μFinFlat := by
      have hiff :=
        hpFlat.integrable_comp_emb
          eFlat.measurableEmbedding
          (g := fun p :
              T4 × (T4 × (Fin n → T4)) =>
            path (eFlat.symm p))
      apply hiff.mp
      convert hpath using 1
      funext tuple
      simp only [Function.comp_apply,
        eFlat, MeasurableEquiv.symm_apply_apply]
    apply htarget.congr
    filter_upwards with p
    rcases p with ⟨x, y, v⟩
    exact congrArg path
      (r324FlatAssembleMeasurableEquiv_symm_apply
        n x y v)
  let eSparse :
      T4 × (T4 ×
          (res.SurvivingCoordinate → T4)) ≃ᵐ
        T4 × (T4 × (Fin n → T4)) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        res.r324TerminalJI_survivingPiMeasurableEquiv)
  let μSparse :=
    paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : res.SurvivingCoordinate =>
          paperMeasure))
  have hpSparse :
      MeasurePreserving eSparse μSparse μFinFlat := by
    exact
      (MeasurePreserving.id paperMeasure).prod
        ((MeasurePreserving.id paperMeasure).prod
          res.r324TerminalJI_measurePreserving_survivingPiMeasurableEquiv)
  have hSparse :
      Integrable
        ((fun p : T4 × (T4 × (Fin n → T4)) =>
          path (assemble p.1 p.2.1 p.2.2)) ∘ eSparse)
        μSparse :=
    (hpSparse.integrable_comp_emb
      eSparse.measurableEmbedding).mpr hFinFlat
  apply hSparse.congr
  filter_upwards with p
  rcases p with ⟨x, y, v⟩
  rw [Function.comp_apply,
    res.r324TerminalJI_residualChainProduct_eq_path
      hremaining x y v]
  rfl

end R324WithinHalfResidualPrefix

/-! ## Bounded measurable grouped residual primitive sum -/

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

private theorem r324TerminalJI_measurable_primitivePartitionBlockSum
    (ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m))) :
    Measurable
      (r324PrimitivePartitionBlockSum
        ρ ε κp κm π B) := by
  unfold r324PrimitivePartitionBlockSum
  split_ifs with hB
  · apply Finset.measurable_sum
    intro σ _hσ
    unfold primitivePartitionBlockCovarianceFactor
    exact
      (measurable_primitiveCovarianceProduct ρ ε
        (residualBlockOrder B) σ.1).comp
        (measurable_pi_lambda _ fun i =>
          measurable_pi_apply
            ((residualPrimitiveBlockOrderIso
              (momentCombinedPairing κp κm π) B
              ((momentPrimitiveBlockPartition κp κm π).block_fullyPaired
                hB) i).1))
  · exact measurable_const

theorem measurable_r324ResidualPrimitiveSumProduct
    (ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    Measurable
      (r324ResidualPrimitiveSumProduct
        ρ ε κp κm π) := by
  unfold r324ResidualPrimitiveSumProduct
  generalize
    nonemptyMomentResidualCollapseBlocks
      κp κm π = blocks
  induction blocks with
  | nil =>
      simp only [List.map_nil, List.prod_nil]
      exact measurable_const
  | cons B blocks ih =>
      simp only [List.map_cons, List.prod_cons]
      exact
        (ρ.r324TerminalJI_measurable_primitivePartitionBlockSum
          ε κp κm π B).mul ih

private theorem
    r324TerminalJI_exists_norm_residualPrimitiveBlockSum_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B :
      {B : Finset (Fin (2 * m)) //
        B ∈
          nonemptyMomentResidualCollapseBlocks
            κp κm π}) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ v : Fin (2 * m) → T4,
        ‖r324PrimitivePartitionBlockSum
          ρ ε κp κm π B.1 v‖ ≤ bound := by
  obtain ⟨Cη, _hCη, hcovariance⟩ :=
    exists_primitiveCovarianceProduct_uniform_bound ρ
  let n := residualBlockOrder B.1
  let A : ℝ :=
    (ε⁻¹ ^ (dim : ℕ) * Cη) ^ n
  let bound : ℝ :=
    ((primitiveFullPairings n).card : ℝ) * A
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  refine
    ⟨bound,
      mul_nonneg (Nat.cast_nonneg _) hA,
      ?_⟩
  intro v
  have hpartition :=
    r324ResidualPrimitiveBlock_mem_partition
      κp κm π B
  rw [r324PrimitivePartitionBlockSum_of_mem
    ρ ε κp κm π B.1 hpartition]
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (Finset.sum_nonneg fun σ _ =>
        primitiveCovarianceProduct_nonneg
          ρ ε n σ.1
          (fun i =>
            v ((residualPrimitiveBlockOrderIso
              (momentCombinedPairing κp κm π) B.1
              ((momentPrimitiveBlockPartition κp κm π).block_fullyPaired
                hpartition) i).1)))]
  calc
    (∑ σ :
        {τ : PartialPairing (Fin (2 * n)) //
          τ ∈ primitiveFullPairings n},
      primitivePartitionBlockCovarianceFactor
        ρ ε (momentPrimitiveBlockPartition κp κm π)
        ⟨B.1, hpartition⟩ σ v) ≤
        ∑ _σ :
            {τ : PartialPairing (Fin (2 * n)) //
              τ ∈ primitiveFullPairings n},
          A := by
      apply Finset.sum_le_sum
      intro σ _hσ
      unfold primitivePartitionBlockCovarianceFactor
      exact
        hcovariance n σ.1
          (mem_primitiveFullPairings.mp σ.2).1
          hε hε1 _
    _ = bound := by
      simp [bound]

theorem exists_norm_r324ResidualPrimitiveSumProduct_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ v : Fin (2 * m) → T4,
        ‖r324ResidualPrimitiveSumProduct
          ρ ε κp κm π v‖ ≤ bound := by
  choose blockBound hblockBoundNonneg hblockBound using
    fun B :
        {B : Finset (Fin (2 * m)) //
          B ∈ nonemptyMomentResidualCollapseBlocks
            κp κm π} =>
      ρ.r324TerminalJI_exists_norm_residualPrimitiveBlockSum_le
        hε hε1 κp κm π B
  let bound : ℝ :=
    ∏ B :
        {B : Finset (Fin (2 * m)) //
          B ∈ nonemptyMomentResidualCollapseBlocks
            κp κm π},
      blockBound B
  refine
    ⟨bound,
      Finset.prod_nonneg fun B _ =>
        hblockBoundNonneg B,
      ?_⟩
  intro v
  unfold r324ResidualPrimitiveSumProduct
  rw [list_map_prod_eq_fintype_prod_subtype
    (nonemptyMomentResidualCollapseBlocks κp κm π)
    (nonemptyMomentResidualCollapseBlocks_nodup
      κp κm π)]
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact
    Finset.prod_le_prod
      (fun B _ => abs_nonneg _)
      (fun B _ => by
        simpa only [Real.norm_eq_abs] using
          hblockBound B v)

end SmoothCutoff

end

end Anderson4D
