import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhaseAClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324BlockCollapse

/-!
# The first genuine signed block update in R-324

This file connects the stable first-left coordinate of the R-324
within-half fibre to the actual deterministic covariance factor carried by
that contraction.  In particular, the primitive coordinate exposed by
`r324FirstLeftReconstruct` is proved to be the ordered pairing seen by the
original integrand; it is not introduced as an unrelated proxy.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The actual selected spatial tuple -/

/-- Increasing block coordinates followed by the left-copy embedding give
an equivalence with the selected doubled-coordinate subtype. -/
def r324FirstLeftSelectedCoordinateEquiv
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft)) ≃
      {i : Fin (2 * m) //
        r324FirstLeftSelected e₀ hleft i} := by
  let B :=
    selectedExtractionBlock e₀.1 Finset.univ hleft
  let eB :
      Fin (2 * residualBlockOrder B) ≃ B :=
    (residualPrimitiveBlockOrderIso e₀.1 B
      (selectRel_isRelFullyPaired
        e₀.1 Finset.univ hleft).isFullyPairedOn).toEquiv
  let eLeft :
      B ≃
        {i : Fin (2 * m) //
          i ∈ B.image leftMomentIndex} :=
    Equiv.ofBijective
      (fun i : B =>
        ⟨leftMomentIndex i.1,
          Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩)
      ⟨by
        intro i j hij
        apply Subtype.ext
        exact leftMomentIndex_injective
          (congrArg Subtype.val hij),
        by
          intro j
          obtain ⟨i, hi, hij⟩ :=
            Finset.mem_image.mp j.2
          refine ⟨⟨i, hi⟩, ?_⟩
          apply Subtype.ext
          exact hij⟩
  exact eB.trans eLeft

@[simp]
theorem r324FirstLeftSelectedCoordinateEquiv_apply_val
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (i : Fin (2 * residualBlockOrder
      (selectedExtractionBlock e₀.1 Finset.univ hleft))) :
    (r324FirstLeftSelectedCoordinateEquiv e₀ hleft i).1 =
      leftMomentIndex
        ((residualPrimitiveBlockOrderIso e₀.1
          (selectedExtractionBlock e₀.1 Finset.univ hleft)
          (selectRel_isRelFullyPaired
            e₀.1 Finset.univ hleft).isFullyPairedOn i).1) := by
  rfl

/-- Reindex selected doubled-coordinate tuples by their canonical
increasing `Fin (2n)` block coordinate. -/
def r324FirstLeftSelectedTupleMeasurableEquiv
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    (Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4) ≃ᵐ
      ((i : {i : Fin (2 * m) //
        r324FirstLeftSelected e₀ hleft i}) → T4) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : {i : Fin (2 * m) //
      r324FirstLeftSelected e₀ hleft i} => T4)
    (r324FirstLeftSelectedCoordinateEquiv e₀ hleft)

@[simp]
theorem r324FirstLeftSelectedTupleMeasurableEquiv_apply
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (v :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft)) → T4)
    (i :
      Fin (2 * residualBlockOrder
        (selectedExtractionBlock e₀.1 Finset.univ hleft))) :
    r324FirstLeftSelectedTupleMeasurableEquiv e₀ hleft v
        (r324FirstLeftSelectedCoordinateEquiv e₀ hleft i) =
      v i := by
  exact
    MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : {i : Fin (2 * m) //
        r324FirstLeftSelected e₀ hleft i} => T4)
      (r324FirstLeftSelectedCoordinateEquiv e₀ hleft) v i

/-- The selected-coordinate reindex preserves exactly the product of paper
measures. -/
theorem measurePreserving_r324FirstLeftSelectedTupleMeasurableEquiv
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    MeasurePreserving
      (r324FirstLeftSelectedTupleMeasurableEquiv e₀ hleft)
      (Measure.pi fun _ :
        Fin (2 * residualBlockOrder
          (selectedExtractionBlock e₀.1 Finset.univ hleft)) =>
            paperMeasure)
      (Measure.pi fun _ :
        {i : Fin (2 * m) //
          r324FirstLeftSelected e₀ hleft i} =>
            paperMeasure) := by
  simpa only [r324FirstLeftSelectedTupleMeasurableEquiv] using
    (measurePreserving_piCongrLeft
      (fun _ : {i : Fin (2 * m) //
        r324FirstLeftSelected e₀ hleft i} =>
          paperMeasure)
      (r324FirstLeftSelectedCoordinateEquiv e₀ hleft))

/-- Bochner-integral form of the concrete selected-tuple reindex. -/
theorem integral_r324FirstLeftSelected_eq_standardBlock
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (f :
      ((i : {i : Fin (2 * m) //
        r324FirstLeftSelected e₀ hleft i}) → T4) → E) :
    (∫ vB, f vB
        ∂Measure.pi fun _ :
          {i : Fin (2 * m) //
            r324FirstLeftSelected e₀ hleft i} =>
          paperMeasure) =
      ∫ u :
          Fin (2 * residualBlockOrder
            (selectedExtractionBlock
              e₀.1 Finset.univ hleft)) → T4,
        f (r324FirstLeftSelectedTupleMeasurableEquiv
          e₀ hleft u)
        ∂Measure.pi fun _ => paperMeasure := by
  exact
    (measurePreserving_r324FirstLeftSelectedTupleMeasurableEquiv
      e₀ hleft).integral_comp' f |>.symm

/-! ## Endpoints and internal coordinates of the primitive block -/

/-- Split a positive-order standard block tuple into its two endpoints and
its internal primitive coordinates. -/
def r324PrimitiveBlockTupleMeasurableEquiv
    (n : ℕ) (hn : 1 ≤ n) :
    (Fin (2 * n) → T4) ≃ᵐ
      (T4 × T4) × (Fin (2 * n - 2) → T4) :=
  ((MeasurableEquiv.piCongrLeft
      (fun _ : Fin ((2 * n - 2) + 2) => T4)
      (finCongr (by omega :
        2 * n = (2 * n - 2) + 2))).trans
    (r322FlatAssembleMeasurableEquiv (2 * n - 2))).trans
      (MeasurableEquiv.prodAssoc
        (α := T4) (β := T4)
        (γ := Fin (2 * n - 2) → T4)).symm

@[simp]
theorem r324PrimitiveBlockTupleMeasurableEquiv_symm_apply
    (n : ℕ) (hn : 1 ≤ n)
    (p : T4 × T4)
    (u : Fin (2 * n - 2) → T4) :
    (r324PrimitiveBlockTupleMeasurableEquiv n hn).symm (p, u) =
      primitiveAssemble n hn p.1 p.2 u := by
  funext i
  change
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin ((2 * n - 2) + 2) => T4)
      (finCongr (by omega :
        2 * n = (2 * n - 2) + 2))).symm
        ((r322FlatAssembleMeasurableEquiv
          (2 * n - 2)).symm (p.1, p.2, u)) i =
      primitiveAssemble n hn p.1 p.2 u i
  rw [r322FlatAssembleMeasurableEquiv_symm_apply]
  change
    (Equiv.piCongrLeft
      (fun _ : Fin ((2 * n - 2) + 2) => T4)
      (finCongr (by omega :
        2 * n = (2 * n - 2) + 2))).symm
        (assemble p.1 p.2 u) i =
      primitiveAssemble n hn p.1 p.2 u i
  simp only [Equiv.piCongrLeft_symm_apply]
  rfl

/-- The endpoint/internal split preserves the full paper product measure. -/
theorem measurePreserving_r324PrimitiveBlockTupleMeasurableEquiv
    (n : ℕ) (hn : 1 ≤ n) :
    MeasurePreserving
      (r324PrimitiveBlockTupleMeasurableEquiv n hn)
      (Measure.pi fun _ : Fin (2 * n) => paperMeasure)
      ((paperMeasure.prod paperMeasure).prod
        (Measure.pi fun _ : Fin (2 * n - 2) =>
          paperMeasure)) := by
  let ecast :
      (Fin (2 * n) → T4) ≃ᵐ
        (Fin ((2 * n - 2) + 2) → T4) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : Fin ((2 * n - 2) + 2) => T4)
      (finCongr (by omega :
        2 * n = (2 * n - 2) + 2))
  have hcast :
      MeasurePreserving ecast
        (Measure.pi fun _ : Fin (2 * n) => paperMeasure)
        (Measure.pi fun _ :
          Fin ((2 * n - 2) + 2) => paperMeasure) := by
    simpa only [ecast] using
      (measurePreserving_piCongrLeft
        (fun _ : Fin ((2 * n - 2) + 2) =>
          paperMeasure)
        (finCongr (by omega :
          2 * n = (2 * n - 2) + 2)))
  have hflat :=
    measurePreserving_r322FlatAssembleMeasurableEquiv
      (2 * n - 2)
  have hassoc :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc
          (α := T4) (β := T4)
          (γ := Fin (2 * n - 2) → T4)).symm
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin (2 * n - 2) =>
              paperMeasure)))
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ : Fin (2 * n - 2) =>
            paperMeasure)) :=
    (measurePreserving_prodAssoc paperMeasure paperMeasure
      (Measure.pi fun _ : Fin (2 * n - 2) =>
        paperMeasure)).symm
  exact hassoc.comp (hflat.comp hcast)

/-- Bochner integral over a positive standard block, with the endpoint pair
outermost and all internal primitive coordinates innermost. -/
theorem integral_standardBlock_eq_integral_endpoints_internal
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (n : ℕ) (hn : 1 ≤ n)
    (f : (Fin (2 * n) → T4) → E)
    (hf :
      Integrable f
        (Measure.pi fun _ : Fin (2 * n) =>
          paperMeasure)) :
    (∫ t, f t
        ∂Measure.pi fun _ : Fin (2 * n) =>
          paperMeasure) =
      ∫ p : T4 × T4,
        ∫ u : Fin (2 * n - 2) → T4,
          f (primitiveAssemble n hn p.1 p.2 u)
          ∂Measure.pi fun _ => paperMeasure
        ∂(paperMeasure.prod paperMeasure) := by
  let e :=
    r324PrimitiveBlockTupleMeasurableEquiv n hn
  let μ :=
    Measure.pi fun _ : Fin (2 * n) => paperMeasure
  let ν :=
    (paperMeasure.prod paperMeasure).prod
      (Measure.pi fun _ : Fin (2 * n - 2) =>
        paperMeasure)
  have hp : MeasurePreserving e μ ν :=
    measurePreserving_r324PrimitiveBlockTupleMeasurableEquiv n hn
  have htarget :
      Integrable (fun q => f (e.symm q)) ν := by
    have hiff :=
      hp.symm.integrable_comp_emb
        e.symm.measurableEmbedding
        (g := f)
    change Integrable (f ∘ e.symm) ν
    exact hiff.mpr hf
  calc
    (∫ t, f t ∂μ) =
        ∫ q, f (e.symm q) ∂ν := by
      symm
      simpa only [Function.comp_apply] using
        hp.symm.integral_comp' f
    _ =
        ∫ p : T4 × T4,
          ∫ u : Fin (2 * n - 2) → T4,
            f (e.symm (p, u))
            ∂Measure.pi fun _ => paperMeasure
          ∂(paperMeasure.prod paperMeasure) :=
      integral_prod _ htarget
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      apply integral_congr_ae
      filter_upwards with u
      rw [r324PrimitiveBlockTupleMeasurableEquiv_symm_apply]

/-! ## Translation of generalized primitive kernels -/

theorem jChainEdgeWith_add_const
    {n : ℕ}
    (G : Fin (n - 1) → T4 → ℝ)
    (x : Fin n → T4) (a : T4)
    (e : Fin (n - 1)) :
    jChainEdgeWith G (fun i => x i + a) e =
      jChainEdgeWith G x e := by
  unfold jChainEdgeWith
  rw [add_sub_add_right_eq_sub]

theorem diffFactorJWith_add_const
    {n : ℕ}
    (G : Fin (n - 1) → T4 → ℝ)
    (x : Fin n → T4) (a : T4)
    (p : Fin n × Fin n) :
    diffFactorJWith G (fun i => x i + a) p =
      diffFactorJWith G x p := by
  unfold diffFactorJWith
  split
  · simp only [add_sub_add_right_eq_sub]
  · rfl

theorem jReplacementList_add_const
    {n : ℕ}
    (G : Fin (n - 1) → T4 → ℝ)
    (x : Fin n → T4) (a : T4)
    (ps : List (Fin n × Fin n)) :
    jReplacementList G (fun i => x i + a) ps =
      jReplacementList G x ps := by
  induction ps with
  | nil =>
      rfl
  | cons p ps ih =>
      unfold jReplacementList
      split
      · rw [diffFactorJWith_add_const, ih]
      · exact ih

/-- The generalized closed primitive integrand contains only spatial
differences, so simultaneous translation of all its vertices is exact. -/
theorem detJclosedIntegrandWith_add_const
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ)
    (σ : PartialPairing (Fin n))
    (G : Fin (n - 1) → T4 → ℝ)
    (x : Fin n → T4) (a : T4) :
    detJclosedIntegrandWith ρ ε n σ G
        (fun i => x i + a) =
      detJclosedIntegrandWith ρ ε n σ G x := by
  have hedges :
      extractedJRightEdges G (fun i => x i + a) (extract σ) =
        extractedJRightEdges G x (extract σ) := by
    unfold extractedJRightEdges
    rw [jReplacementList_add_const]
  unfold detJclosedIntegrandWith
  rw [hedges,
    jReplacementList_add_const G x a (extract σ)]
  apply congrArg₂ (· * ·)
  · apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro e _he
      split_ifs
      · rfl
      · exact jChainEdgeWith_add_const G x a e
    · rfl
  · apply Finset.prod_congr rfl
    intro i _hi
    rw [add_sub_add_right_eq_sub]

theorem primitiveAssemble_add_const
    (n : ℕ) (hn : 1 ≤ n)
    (z w a : T4)
    (u : Fin (2 * n - 2) → T4) :
    primitiveAssemble n hn (z + a) (w + a)
        (fun i => u i + a) =
      fun j => primitiveAssemble n hn z w u j + a := by
  funext j
  unfold primitiveAssemble
  exact assemble_add_const_r322 z w a u _

/-- Simultaneous endpoint translation leaves the generalized selected
primitive kernel unchanged. -/
theorem detJWith_add_const
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (σ : PartialPairing (Fin (2 * n)))
    (z w a : T4) :
    detJWith ρ lam ε n hn G σ (z + a) (w + a) =
      detJWith ρ lam ε n hn G σ z w := by
  unfold detJWith
  apply congrArg
    (fun t : ℝ => lamEps lam ε ^ (2 * n) * t)
  let shift :
      (Fin (2 * n - 2) → T4) ≃ᵐ
        (Fin (2 * n - 2) → T4) :=
    MeasurableEquiv.piCongrRight fun _ =>
      MeasurableEquiv.addRight a
  have hcoord (_i : Fin (2 * n - 2)) :
      MeasurePreserving (fun x : T4 => x + a)
        paperMeasure paperMeasure := by
    rw [paperMeasure_eq_volume]
    exact
      measurePreserving_add_right
        (volume : Measure T4) a
  have hp :
      MeasurePreserving shift
        (Measure.pi fun _ : Fin (2 * n - 2) =>
          paperMeasure)
        (Measure.pi fun _ : Fin (2 * n - 2) =>
          paperMeasure) := by
    change
      MeasurePreserving
        (fun u i => u i + a)
        (Measure.pi fun _ : Fin (2 * n - 2) =>
          paperMeasure)
        (Measure.pi fun _ : Fin (2 * n - 2) =>
          paperMeasure)
    exact measurePreserving_pi
      (fun _ : Fin (2 * n - 2) => paperMeasure)
      (fun _ : Fin (2 * n - 2) => paperMeasure)
      hcoord
  let fLeft : (Fin (2 * n - 2) → T4) → ℝ :=
    fun u =>
      detJclosedIntegrandWith ρ ε (2 * n) σ G
        (primitiveAssemble n hn (z + a) (w + a) u)
  let fRight : (Fin (2 * n - 2) → T4) → ℝ :=
    fun u =>
      detJclosedIntegrandWith ρ ε (2 * n) σ G
        (primitiveAssemble n hn z w u)
  calc
    (∫ u,
        detJclosedIntegrandWith ρ ε (2 * n) σ G
          (primitiveAssemble n hn (z + a) (w + a) u)
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ u, fLeft (shift u)
        ∂Measure.pi fun _ => paperMeasure := by
          exact (hp.integral_comp' fLeft).symm
    _ = ∫ u, fRight u
        ∂Measure.pi fun _ => paperMeasure := by
      apply integral_congr_ae
      filter_upwards with u
      unfold fLeft fRight
      change
        detJclosedIntegrandWith ρ ε (2 * n) σ G
            (primitiveAssemble n hn
              (z + a) (w + a)
              (fun i => u i + a)) =
          detJclosedIntegrandWith ρ ε (2 * n) σ G
            (primitiveAssemble n hn z w u)
      rw [primitiveAssemble_add_const,
        detJclosedIntegrandWith_add_const]

/-- Difference form used literally by `r322CollapseIntegrand`. -/
theorem detJWith_eq_diff
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (σ : PartialPairing (Fin (2 * n)))
    (z w : T4) :
    detJWith ρ lam ε n hn G σ z w =
      detJWith ρ lam ε n hn G σ (z - w) 0 := by
  have h :=
    detJWith_add_const
      ρ lam ε n hn G σ (z - w) 0 w
  simpa using h

/-! ## The reconstructed contraction really carries the exposed pairing -/

@[simp]
theorem r324FirstLeftReconstruct_leftPairing
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft) :
    (r324FirstLeftReconstruct e₀ hleft ω κB).1.1 =
      ((reductionEndpointFiberEquivBlockComplement
        e₀.1 hleft).symm (κB, ω.1)).1 := by
  rfl

@[simp]
theorem r324FirstLeftReconstruct_rightPairing
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft) :
    (r324FirstLeftReconstruct e₀ hleft ω κB).1.2.1 =
      ω.2.1.1 := by
  rfl

/-- The endpoint-fibre member used by the actual reconstruction has first
block coordinate exactly `κB`. -/
theorem r324FirstLeftEndpointFiber_blockCoordinate
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft) :
    ((reductionEndpointFiberEquivBlockComplement
        e₀.1 hleft)
      ((reductionEndpointFiberEquivBlockComplement
        e₀.1 hleft).symm (κB, ω.1))).1 =
      κB := by
  exact congrArg Prod.fst
    ((reductionEndpointFiberEquivBlockComplement
      e₀.1 hleft).apply_symm_apply (κB, ω.1))

/-! ## Actual selected covariance factor -/

/-- On the selected tuple, the covariance factor of the actual
reconstructed contraction is exactly the standard primitive covariance
factor indexed by `κB`. -/
theorem
    r324FirstLeftReconstruct_selectedCovariance_eq_primitiveCoordinate
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft)
    (v : Fin (2 * m) → T4) :
    pairingCovarianceProductOn ρ ε
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
        (selectedExtractionBlock
          e₀.1 Finset.univ hleft)
        (fun i => v (leftMomentIndex i)) =
      primitiveCovarianceProduct ρ ε
        (residualBlockOrder
          (selectedExtractionBlock
            e₀.1 Finset.univ hleft))
        κB.1
        (fun i =>
          v (leftMomentIndex
            ((residualPrimitiveBlockOrderIso e₀.1
              (selectedExtractionBlock
                e₀.1 Finset.univ hleft)
              (selectRel_isRelFullyPaired
                e₀.1 Finset.univ hleft).isFullyPairedOn i).1))) := by
  rw [r324FirstLeftReconstruct_leftPairing]
  rw [pairingCovarianceProductOn_endpointFiber_eq_firstCoordinate]
  rw [r324FirstLeftEndpointFiber_blockCoordinate]

/-- The complementary within-left covariance factor is genuinely
independent of the exposed primitive coordinate. -/
theorem r324FirstLeftReconstruct_complementCovariance_eq_reference
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft)
    (v : Fin (2 * m) → T4) :
    pairingCovarianceProductOn ρ ε
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
        ((Finset.univ : Finset (Fin m)) \
          selectedExtractionBlock e₀.1 Finset.univ hleft)
        (fun i => v (leftMomentIndex i)) =
      pairingCovarianceProductOn ρ ε
        (firstBlockReferenceEndpointFiber
          e₀.1 hleft ω.1).1
        ((Finset.univ : Finset (Fin m)) \
          selectedExtractionBlock e₀.1 Finset.univ hleft)
        (fun i => v (leftMomentIndex i)) := by
  rw [r324FirstLeftReconstruct_leftPairing]
  unfold firstBlockReferenceEndpointFiber
  exact pairingCovarianceProductOn_complement_eq_of_blockCoordinate
    ρ ε e₀.1 (m - 1) Finset.univ hleft
    κB
    (selectedExtractionPrimitivePairing
      e₀.1 Finset.univ hleft)
    ω.1 (fun i => v (leftMomentIndex i))

/-- Exact selected-block/complement factorization of the actual
reconstructed within-left covariance product. -/
theorem r324FirstLeftReconstruct_leftCovariance_eq_primitive_mul_reference
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft)
    (v : Fin (2 * m) → T4) :
    pairingCovarianceProductOn ρ ε
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
        Finset.univ
        (fun i => v (leftMomentIndex i)) =
      primitiveCovarianceProduct ρ ε
          (residualBlockOrder
            (selectedExtractionBlock
              e₀.1 Finset.univ hleft))
          κB.1
          (fun i =>
            v (leftMomentIndex
              ((residualPrimitiveBlockOrderIso e₀.1
                (selectedExtractionBlock
                  e₀.1 Finset.univ hleft)
                (selectRel_isRelFullyPaired
                  e₀.1 Finset.univ hleft).isFullyPairedOn i).1))) *
        pairingCovarianceProductOn ρ ε
          (firstBlockReferenceEndpointFiber
            e₀.1 hleft ω.1).1
          ((Finset.univ : Finset (Fin m)) \
            selectedExtractionBlock e₀.1 Finset.univ hleft)
          (fun i => v (leftMomentIndex i)) := by
  let B :=
    selectedExtractionBlock e₀.1 Finset.univ hleft
  have hB : B ⊆ (Finset.univ : Finset (Fin m)) :=
    Finset.subset_univ B
  change
    pairingCovarianceProductOn ρ ε
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
        Finset.univ
        (fun i => v (leftMomentIndex i)) =
      primitiveCovarianceProduct ρ ε
          (residualBlockOrder B)
          κB.1
          (fun i =>
            v (leftMomentIndex
              ((residualPrimitiveBlockOrderIso e₀.1 B
                (selectRel_isRelFullyPaired
                  e₀.1 Finset.univ hleft).isFullyPairedOn i).1))) *
        pairingCovarianceProductOn ρ ε
          (firstBlockReferenceEndpointFiber
            e₀.1 hleft ω.1).1
          (Finset.univ \ B)
          (fun i => v (leftMomentIndex i))
  have hsplit :
      pairingCovarianceProductOn ρ ε
          (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
          Finset.univ
          (fun i => v (leftMomentIndex i)) =
        pairingCovarianceProductOn ρ ε
            (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
            B (fun i => v (leftMomentIndex i)) *
          pairingCovarianceProductOn ρ ε
            (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
            (Finset.univ \ B)
            (fun i => v (leftMomentIndex i)) := by
    rw [← pairingCovarianceProductOn_union
      ρ ε
      (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
      B (Finset.univ \ B) Finset.disjoint_sdiff]
    rw [Finset.union_sdiff_of_subset hB]
  rw [hsplit]
  rw [
    r324FirstLeftReconstruct_selectedCovariance_eq_primitiveCoordinate,
    r324FirstLeftReconstruct_complementCovariance_eq_reference]

/-! ## The stabilized cross coordinate is analytically unchanged -/

/-- Value-preserving transport of the subtype of left singles does not
change the actual cross-covariance product. -/
theorem momentCrossCovarianceProduct_transport_leftSingles
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κp' κm : PartialPairing (Fin m))
    (hsingles : κp.singles = κp'.singles)
    (π : κp'.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    momentCrossCovarianceProduct ρ ε m κp κm
        ((finsetSubtypeEquivOfEq hsingles).trans π) v =
      momentCrossCovarianceProduct ρ ε m κp' κm π v := by
  unfold momentCrossCovarianceProduct
  apply Fintype.prod_equiv
    (finsetSubtypeEquivOfEq hsingles)
  intro i
  simp only [Equiv.trans_apply,
    finsetSubtypeEquivOfEq_apply_val]

/-- The cross-covariance factor of the reconstructed contraction is
independent of `κB`; the transport used in
`r324FirstLeftReconstruct` preserves every ambient endpoint. -/
theorem r324FirstLeftReconstruct_crossCovariance_eq_reference
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft)
    (v : Fin (2 * m) → T4) :
    momentCrossCovarianceProduct ρ ε m
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.2.1
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.2.2 v =
      momentCrossCovarianceProduct ρ ε m
        (firstBlockReferenceEndpointFiber
          e₀.1 hleft ω.1).1
        ω.2.1.1 ω.2.2 v := by
  change
    momentCrossCovarianceProduct ρ ε m
        ((reductionEndpointFiberEquivBlockComplement
          e₀.1 hleft).symm (κB, ω.1)).1
        ω.2.1.1
        ((firstBlockCrossEquivStabilization
          e₀.1 hleft κB ω.1 ω.2.1.1).symm ω.2.2) v =
      _
  rw [firstBlockCrossEquivStabilization_symm_apply]
  exact
    momentCrossCovarianceProduct_transport_leftSingles
      ρ ε
      ((reductionEndpointFiberEquivBlockComplement
        e₀.1 hleft).symm (κB, ω.1)).1
      (firstBlockReferenceEndpointFiber
        e₀.1 hleft ω.1).1
      ω.2.1.1
      (reductionEndpointFiberEquivBlockComplement_symm_singles_eq
        e₀.1 hleft κB
          (selectedExtractionPrimitivePairing
            e₀.1 Finset.univ hleft)
        ω.1)
      ω.2.2 v

/-! ## All remaining factors are a genuine outer coordinate -/

/-- Generic whole-carrier form of the within-copy covariance product. -/
theorem pairingCovarianceProductOn_univ_eq_pairSupport
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m)) (v : Fin m → T4) :
    pairingCovarianceProductOn ρ ε κ Finset.univ v =
      ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
        ρ.etaEpsT4 ε (v i - v (κ i)) := by
  unfold pairingCovarianceProductOn
  apply Finset.prod_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      PartialPairing.mem_pairSupport]
    constructor
    · intro hi
      exact ⟨ne_of_gt hi, hi⟩
    · exact fun hi => hi.2
  · intro i _hi
    rfl

/-- The signed left Green skeleton of the actual reconstructed contraction
is the reference skeleton stored by the outer coordinate. -/
theorem r324FirstLeftReconstruct_greenSkeleton_eq_reference
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft) :
    renormalizedGreenSkeleton
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.1 =
      renormalizedGreenSkeleton
        (firstBlockReferenceEndpointFiber
          e₀.1 hleft ω.1).1 := by
  let τ :=
    (reductionEndpointFiberEquivBlockComplement
      e₀.1 hleft).symm (κB, ω.1)
  let τ₀ :=
    firstBlockReferenceEndpointFiber
      e₀.1 hleft ω.1
  change renormalizedGreenSkeleton τ.1 =
    renormalizedGreenSkeleton τ₀.1
  exact
    renormalizedGreenSkeleton_eq_of_reductionEndpointSignature_eq
      τ.1 τ₀.1 (τ.2.trans τ₀.2.symm)

/-- Every factor other than the selected primitive covariance coordinate.
This is built from the actual reference contraction carried by `ω`, not
from an arbitrary replacement integrand. -/
def r324FirstLeftOuterFactor
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  momentFourierPhase α β x y z w *
    renormalizedGreenSkeleton
      (firstBlockReferenceEndpointFiber
        e₀.1 hleft ω.1).1
      (assemble x y fun i => v (leftMomentIndex i)) *
    renormalizedGreenSkeleton ω.2.1.1
      (assemble z w fun i => v (rightMomentIndex i)) *
    ((pairingCovarianceProductOn ρ ε
          (firstBlockReferenceEndpointFiber
            e₀.1 hleft ω.1).1
          ((Finset.univ : Finset (Fin m)) \
            selectedExtractionBlock e₀.1 Finset.univ hleft)
          (fun i => v (leftMomentIndex i)) *
        pairingCovarianceProductOn ρ ε ω.2.1.1 Finset.univ
          (fun i => v (rightMomentIndex i)) *
        momentCrossCovarianceProduct ρ ε m
          (firstBlockReferenceEndpointFiber
            e₀.1 hleft ω.1).1
          ω.2.1.1 ω.2.2 v : ℝ) : ℂ)

/-- **Actual pointwise first-left identification.**

The original deterministic moment integrand evaluated at the contraction
reconstructed from `(ω, κB)` is the `κB`-independent outer factor times the
standard primitive covariance factor on the selected spatial tuple. -/
theorem deterministicMomentIntegrand_r324FirstLeftReconstruct_eq
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    deterministicMomentIntegrand ρ ε m α β
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.2.1
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.2.2
        x y z w v =
      r324FirstLeftOuterFactor ρ ε α β e₀ hleft ω
          x y z w v *
        (primitiveCovarianceProduct ρ ε
          (residualBlockOrder
            (selectedExtractionBlock
              e₀.1 Finset.univ hleft))
          κB.1
          (fun i =>
            v (leftMomentIndex
              ((residualPrimitiveBlockOrderIso e₀.1
                (selectedExtractionBlock
                  e₀.1 Finset.univ hleft)
                (selectRel_isRelFullyPaired
                  e₀.1 Finset.univ hleft).isFullyPairedOn i).1))) :
            ℂ) := by
  let e :=
    (r324FirstLeftReconstruct e₀ hleft ω κB).1
  rw [deterministicMomentIntegrand_eq_skeletons_mul_fullCovariance]
  rw [primitiveCovarianceProduct_momentCombinedPairing]
  rw [← pairingCovarianceProductOn_univ_eq_pairSupport
    ρ ε e.1 (fun i => v (leftMomentIndex i))]
  rw [← pairingCovarianceProductOn_univ_eq_pairSupport
    ρ ε e.2.1 (fun i => v (rightMomentIndex i))]
  change
    momentFourierPhase α β x y z w *
        renormalizedGreenSkeleton
          (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
          (assemble x y fun i => v (leftMomentIndex i)) *
        renormalizedGreenSkeleton
          (r324FirstLeftReconstruct e₀ hleft ω κB).1.2.1
          (assemble z w fun i => v (rightMomentIndex i)) *
        ((pairingCovarianceProductOn ρ ε
              (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
              Finset.univ
              (fun i => v (leftMomentIndex i)) *
            pairingCovarianceProductOn ρ ε
              (r324FirstLeftReconstruct e₀ hleft ω κB).1.2.1
              Finset.univ
              (fun i => v (rightMomentIndex i)) *
            momentCrossCovarianceProduct ρ ε m
              (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
              (r324FirstLeftReconstruct e₀ hleft ω κB).1.2.1
              (r324FirstLeftReconstruct e₀ hleft ω κB).1.2.2 v :
            ℝ) : ℂ) =
      _
  rw [
    r324FirstLeftReconstruct_greenSkeleton_eq_reference,
    r324FirstLeftReconstruct_crossCovariance_eq_reference]
  rw [
    r324FirstLeftReconstruct_rightPairing,
    r324FirstLeftReconstruct_leftCovariance_eq_primitive_mul_reference]
  unfold r324FirstLeftOuterFactor
  push_cast
  ring

/-- Summing the actual reconstructed integrands over the complete primitive
coordinate therefore forms the signed primitive covariance sum before any
norm is taken. -/
theorem sum_deterministicMomentIntegrand_r324FirstLeftReconstruct_eq
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    (∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
      deterministicMomentIntegrand ρ ε m α β
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.2.1
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.2.2
        x y z w v) =
      r324FirstLeftOuterFactor ρ ε α β e₀ hleft ω
          x y z w v *
        ∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
          (primitiveCovarianceProduct ρ ε
            (residualBlockOrder
              (selectedExtractionBlock
                e₀.1 Finset.univ hleft))
            κB.1
            (fun i =>
              v (leftMomentIndex
                ((residualPrimitiveBlockOrderIso e₀.1
                  (selectedExtractionBlock
                    e₀.1 Finset.univ hleft)
                  (selectRel_isRelFullyPaired
                    e₀.1 Finset.univ hleft).isFullyPairedOn i).1))) :
              ℂ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κB _hκB
  exact
    deterministicMomentIntegrand_r324FirstLeftReconstruct_eq
      ρ ε α β e₀ hleft ω κB x y z w v

end

end Anderson4D
