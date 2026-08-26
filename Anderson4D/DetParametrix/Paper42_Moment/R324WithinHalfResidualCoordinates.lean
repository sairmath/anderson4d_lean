import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualPrefix

/-!
# Surviving coordinates of an R-324 within-half residual prefix

One genuine analytic head partitions the current surviving internal
coordinates into the coordinates of that block and the coordinates surviving
the corresponding `absorb`.  This module constructs that partition as an
actual equivalence and lifts it to a measure-preserving Fubini reindexing.

Only coordinate spaces are related here.  In particular, no unintegrated
production integrand is identified pointwise with a processed edge state.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix
        ρ lam ε pairing)

/-- Internal vertices which remain genuine spatial variables after the
processed prefix. -/
def SurvivingCoordinate : Type :=
  {i : Fin m // i ∈ res.state.active}

noncomputable instance survivingCoordinateFintype :
    Fintype res.SurvivingCoordinate :=
  show Fintype {i : Fin m // i ∈ res.state.active} from
    inferInstance

/-- Reconstruct an ambient internal tuple from exactly the surviving
coordinates.  Deleted coordinates are set to zero; residual factors read
only surviving coordinates. -/
def reconstruct
    (v : res.SurvivingCoordinate → T4) :
    Fin m → T4 :=
  fun i =>
    if hi : i ∈ res.state.active then
      v ⟨i, hi⟩
    else 0

@[simp]
theorem reconstruct_surviving
    (v : res.SurvivingCoordinate → T4)
    (i : res.SurvivingCoordinate) :
    res.reconstruct v i.1 = v i := by
  unfold reconstruct
  rw [dif_pos i.2]
  apply congrArg v
  apply Subtype.ext
  rfl

section Head

variable
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)

include tail hremaining

private abbrev ctx :
    R324WithinHalfStepContext pairing :=
  res.headContext head tail hremaining

private abbrev post :
    R324WithinHalfResidualPrefix ρ lam ε pairing :=
  res.afterHead head tail hremaining

/-- Every vertex of the literal schedule head is active before that head is
absorbed. -/
theorem head_block_subset_active :
    head.2 ⊆ res.state.active := by
  have hblock :
      head.2 =
        res.state.active ∩
          Finset.Icc head.1.1 head.1.2 := by
    simpa [R324WithinHalfEdgeState.active] using
      r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
        pairing res.state.processed tail head
        (res.headContext head tail hremaining).schedule_eq
  intro i hi
  rw [hblock] at hi
  exact (Finset.mem_inter.mp hi).1

/-- Coordinates of the current head, still carrying their ambient labels. -/
abbrev HeadCoordinate : Type :=
  {i : res.SurvivingCoordinate // i.1 ∈ head.2}

/-- Coordinates outside the current head, still regarded as members of the
pre-step surviving carrier. -/
abbrev OuterCoordinate : Type :=
  {i : res.SurvivingCoordinate // i.1 ∉ head.2}

/-- The ambiently-labelled head coordinates are exactly the standard
primitive-block coordinate type. -/
def headCoordinateEquivStandard :
    res.HeadCoordinate head ≃
      Fin (2 * residualBlockOrder head.2) where
  toFun i :=
    (res.ctx head tail hremaining).blockOrderIso.symm
      ⟨i.1.1, i.2⟩
  invFun j :=
    let i :=
      (res.ctx head tail hremaining).blockOrderIso j
    ⟨⟨i.1, res.head_block_subset_active
      head tail hremaining i.2⟩, i.2⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have h :=
      (res.ctx head tail hremaining).blockOrderIso.apply_symm_apply
        ⟨i.1.1, i.2⟩
    exact congrArg Subtype.val h
  right_inv j :=
    (res.ctx head tail hremaining).blockOrderIso.symm_apply_apply j

/-- The complement of the head in the pre-step carrier is exactly the
post-`absorb` surviving coordinate type. -/
def outerCoordinateEquivPost :
    res.OuterCoordinate head ≃
      (res.post head tail hremaining).SurvivingCoordinate where
  toFun i := by
    refine ⟨i.1.1, ?_⟩
    change
      i.1.1 ∈
        ((res.headContext head tail hremaining).absorb
          ρ lam ε).active
    rw [R324WithinHalfStepContext.absorb_active]
    exact Finset.mem_sdiff.mpr ⟨i.1.2, i.2⟩
  invFun i := by
    have hi :
        i.1 ∈ res.state.active \ head.2 := by
      have hipost :
          i.1 ∈
            ((res.headContext head tail hremaining).absorb
              ρ lam ε).active :=
        i.2
      rw [R324WithinHalfStepContext.absorb_active] at hipost
      change i.1 ∈ res.state.active \ head.2 at hipost
      exact hipost
    exact
      ⟨⟨i.1, (Finset.mem_sdiff.mp hi).1⟩,
        (Finset.mem_sdiff.mp hi).2⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

/-- Exact one-head partition of the current surviving coordinate type. -/
def survivingCoordinateEquivHeadSumPost :
    res.SurvivingCoordinate ≃
      Fin (2 * residualBlockOrder head.2) ⊕
        (res.post head tail hremaining).SurvivingCoordinate :=
  (Equiv.sumCompl
      (fun i : res.SurvivingCoordinate =>
        i.1 ∈ head.2)).symm.trans
    (Equiv.sumCongr
      (res.headCoordinateEquivStandard
        head tail hremaining)
      (res.outerCoordinateEquivPost
        head tail hremaining))

/-- The current surviving coordinate corresponding to one standard head
coordinate. -/
def headSurvivingCoordinate
    (j : Fin (2 * residualBlockOrder head.2)) :
    res.SurvivingCoordinate :=
  let i :=
    (res.ctx head tail hremaining).blockOrderIso j
  ⟨i.1,
    res.head_block_subset_active
      head tail hremaining i.2⟩

/-- Regard one post-`absorb` surviving coordinate as a coordinate of the
pre-step surviving carrier. -/
def postSurvivingCoordinate
    (i :
      (res.post head tail hremaining).SurvivingCoordinate) :
    res.SurvivingCoordinate := by
  have hipost :
      i.1 ∈
        ((res.headContext head tail hremaining).absorb
          ρ lam ε).active :=
    i.2
  rw [R324WithinHalfStepContext.absorb_active] at hipost
  exact ⟨i.1, (Finset.mem_sdiff.mp hipost).1⟩

/-- Split one current surviving tuple into the literal standard head tuple
and the tuple surviving after `absorb`. -/
def splitSurvivingPiMeasurableEquiv :
    (res.SurvivingCoordinate → T4) ≃ᵐ
      (Fin (2 * residualBlockOrder head.2) → T4) ×
        ((res.post head tail hremaining).SurvivingCoordinate → T4) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : res.SurvivingCoordinate => T4)
      (res.survivingCoordinateEquivHeadSumPost
        head tail hremaining).symm).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ :
        Fin (2 * residualBlockOrder head.2) ⊕
          (res.post head tail hremaining).SurvivingCoordinate =>
        T4))

@[simp]
theorem splitSurvivingPiMeasurableEquiv_apply_fst
    (v : res.SurvivingCoordinate → T4)
    (j : Fin (2 * residualBlockOrder head.2)) :
    (res.splitSurvivingPiMeasurableEquiv
        head tail hremaining v).1 j =
      v (res.headSurvivingCoordinate
        head tail hremaining j) := by
  rfl

@[simp]
theorem splitSurvivingPiMeasurableEquiv_apply_snd
    (v : res.SurvivingCoordinate → T4)
    (i :
      (res.post head tail hremaining).SurvivingCoordinate) :
    (res.splitSurvivingPiMeasurableEquiv
        head tail hremaining v).2 i =
      v (res.postSurvivingCoordinate
        head tail hremaining i) := by
  rfl

@[simp]
theorem splitSurvivingPiMeasurableEquiv_symm_head
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.post head tail hremaining).SurvivingCoordinate →
        T4)
    (j : Fin (2 * residualBlockOrder head.2)) :
    (res.splitSurvivingPiMeasurableEquiv
        head tail hremaining).symm (t, v)
        (res.headSurvivingCoordinate
          head tail hremaining j) =
      t j := by
  have h :=
    (res.splitSurvivingPiMeasurableEquiv
      head tail hremaining).apply_symm_apply (t, v)
  have hfst := congrArg Prod.fst h
  exact congrFun hfst j

@[simp]
theorem splitSurvivingPiMeasurableEquiv_symm_post
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.post head tail hremaining).SurvivingCoordinate →
        T4)
    (i :
      (res.post head tail hremaining).SurvivingCoordinate) :
    (res.splitSurvivingPiMeasurableEquiv
        head tail hremaining).symm (t, v)
        (res.postSurvivingCoordinate
          head tail hremaining i) =
      v i := by
  have h :=
    (res.splitSurvivingPiMeasurableEquiv
      head tail hremaining).apply_symm_apply (t, v)
  have hsnd := congrArg Prod.snd h
  exact congrFun hsnd i

/-- Reconstructing the pre-step ambient tuple after the exact split reads
the standard head tuple literally. -/
@[simp]
theorem reconstruct_split_symm_block
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.post head tail hremaining).SurvivingCoordinate →
        T4)
    (j : Fin (2 * residualBlockOrder head.2)) :
    res.reconstruct
        ((res.splitSurvivingPiMeasurableEquiv
          head tail hremaining).symm (t, v))
        ((res.ctx head tail hremaining).blockOrderIso j).1 =
      t j := by
  let i :=
    res.headSurvivingCoordinate
      head tail hremaining j
  have hi :
      i.1 =
        ((res.ctx head tail hremaining).blockOrderIso j).1 :=
    rfl
  rw [← hi, res.reconstruct_surviving]
  exact
    res.splitSurvivingPiMeasurableEquiv_symm_head
      head tail hremaining t v j

/-- Reconstructing the pre-step ambient tuple after the exact split agrees
with the post-state reconstruction at every post-state surviving vertex. -/
@[simp]
theorem reconstruct_split_symm_post
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.post head tail hremaining).SurvivingCoordinate →
        T4)
    (i :
      (res.post head tail hremaining).SurvivingCoordinate) :
    res.reconstruct
        ((res.splitSurvivingPiMeasurableEquiv
          head tail hremaining).symm (t, v)) i.1 =
      (res.post head tail hremaining).reconstruct v i.1 := by
  let preI :=
    res.postSurvivingCoordinate
      head tail hremaining i
  have hval : preI.1 = i.1 := rfl
  rw [← hval, res.reconstruct_surviving]
  rw [res.splitSurvivingPiMeasurableEquiv_symm_post
    head tail hremaining]
  exact
    ((res.post head tail hremaining).reconstruct_surviving
      v i).symm

/-- The exact coordinate split preserves product Haar measure. -/
theorem measurePreserving_splitSurvivingPiMeasurableEquiv :
    MeasurePreserving
      (res.splitSurvivingPiMeasurableEquiv
        head tail hremaining)
      (Measure.pi fun _ : res.SurvivingCoordinate =>
        paperMeasure)
      ((Measure.pi fun _ :
          Fin (2 * residualBlockOrder head.2) =>
            paperMeasure).prod
        (Measure.pi fun _ :
          (res.post head tail hremaining).SurvivingCoordinate =>
            paperMeasure)) := by
  have hcongr :=
    (measurePreserving_piCongrLeft
      (fun _ : res.SurvivingCoordinate => paperMeasure)
      (res.survivingCoordinateEquivHeadSumPost
        head tail hremaining).symm).symm
  have hsum :=
    measurePreserving_sumPiEquivProdPi
      (fun _ :
        Fin (2 * residualBlockOrder head.2) ⊕
          (res.post head tail hremaining).SurvivingCoordinate =>
        paperMeasure)
  exact hsum.comp hcongr

/-- Fubini in the exact current-head/post-prefix coordinate split.  The
post-state appears only as the surviving coordinate space; the integrand
itself is not rewritten pointwise in this theorem. -/
theorem integral_splitSurviving
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (res.SurvivingCoordinate → T4) → E)
    (hf :
      Integrable f
        (Measure.pi fun _ : res.SurvivingCoordinate =>
          paperMeasure)) :
    (∫ v : res.SurvivingCoordinate → T4, f v
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ t :
          Fin (2 * residualBlockOrder head.2) → T4,
        ∫ v :
            (res.post head tail hremaining).SurvivingCoordinate →
              T4,
          f ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))
          ∂Measure.pi fun _ => paperMeasure
        ∂Measure.pi fun _ => paperMeasure := by
  let e :=
    res.splitSurvivingPiMeasurableEquiv
      head tail hremaining
  let μ :=
    Measure.pi fun _ : res.SurvivingCoordinate =>
      paperMeasure
  let μhead :=
    Measure.pi fun _ :
        Fin (2 * residualBlockOrder head.2) =>
      paperMeasure
  let μpost :=
    Measure.pi fun _ :
        (res.post head tail hremaining).SurvivingCoordinate =>
      paperMeasure
  have hp :
      MeasurePreserving e μ (μhead.prod μpost) :=
    res.measurePreserving_splitSurvivingPiMeasurableEquiv
      head tail hremaining
  have hf' :
      Integrable (fun p => f (e.symm p))
        (μhead.prod μpost) := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    have hcomp :
        Integrable
          (((fun p => f (e.symm p)) ∘ e)) μ := by
      convert hf using 1
      funext v
      simp only [Function.comp_apply, e.symm_apply_apply]
    exact hcomp
  calc
    (∫ v, f v ∂μ) =
        ∫ p, f (e.symm p) ∂(μhead.prod μpost) := by
      simpa only [Function.comp_apply,
        e.symm_apply_apply] using
        hp.integral_comp' (fun p => f (e.symm p))
    _ =
        ∫ t, ∫ v, f (e.symm (t, v))
          ∂μpost ∂μhead :=
      integral_prod _ hf'
    _ = _ := rfl

end Head

end R324WithinHalfResidualPrefix

end

end Anderson4D
