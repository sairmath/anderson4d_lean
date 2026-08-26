import Anderson4D.DetParametrix.Paper42_Moment.R324FirstLeftAnalyticReorder

/-!
# Shifted Green-chain adapter for the genuine first-left R-324 fibre

An R-324 pairing lives on `Fin m`, while its production Green skeleton is
evaluated on `(x,v₀,…,vₘ₋₁,y) : Fin (m+2) → T4`.  Thus a selected pairing
vertex `i` occurs at Green-chain vertex `varIdx i = i+1`, and its physical
coordinate in the doubled moment tuple is `leftMomentIndex i`.

This file makes both shifts explicit and factors the production
`renormalizedGreenSkeleton` into the chain edges touching the genuine
first-left block and the remaining edges.  No parallel skeleton and no
Fourier or absolute-value representation is introduced.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The selected block in the `(m+2)` Green-chain carrier -/

/-- The actual first-left block, shifted past the incoming external
endpoint into the production Green-chain carrier. -/
def r324FirstLeftShiftedBlock
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    Finset (Fin (m + 2)) :=
  (selectedExtractionBlock
    e₀.1 Finset.univ hleft).image varIdx

theorem varIdx_injective {m : ℕ} :
    Function.Injective (@varIdx m) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [varIdx_val] at hval
  omega

@[simp]
theorem varIdx_mem_r324FirstLeftShiftedBlock_iff
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (i : Fin m) :
    varIdx i ∈ r324FirstLeftShiftedBlock e₀ hleft ↔
      i ∈ selectedExtractionBlock
        e₀.1 Finset.univ hleft := by
  unfold r324FirstLeftShiftedBlock
  constructor
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    exact (varIdx_injective hji).symm ▸ hj
  · intro hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- Increasing standard block coordinates, now regarded as the internal
vertices of the production `(m+2)` Green chain. -/
def r324FirstLeftShiftedCoordinateEquiv
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    Fin (2 * residualBlockOrder
      (selectedExtractionBlock
        e₀.1 Finset.univ hleft)) ≃
      {j : Fin (m + 2) //
        j ∈ r324FirstLeftShiftedBlock e₀ hleft} := by
  let B :=
    selectedExtractionBlock e₀.1 Finset.univ hleft
  let eB : Fin (2 * residualBlockOrder B) ≃ B :=
    (residualPrimitiveBlockOrderIso e₀.1 B
      (selectRel_isRelFullyPaired
        e₀.1 Finset.univ hleft).isFullyPairedOn).toEquiv
  let eShift :
      B ≃
        {j : Fin (m + 2) //
          j ∈ B.image varIdx} :=
    Equiv.ofBijective
      (fun i : B =>
        ⟨varIdx i.1,
          Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩)
      ⟨by
        intro i j hij
        apply Subtype.ext
        exact varIdx_injective
          (congrArg Subtype.val hij),
        by
          intro j
          obtain ⟨i, hi, hij⟩ :=
            Finset.mem_image.mp j.2
          refine ⟨⟨i, hi⟩, ?_⟩
          apply Subtype.ext
          exact hij⟩
  exact eB.trans eShift

@[simp]
theorem r324FirstLeftShiftedCoordinateEquiv_apply_val
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (i : Fin (2 * residualBlockOrder
      (selectedExtractionBlock
        e₀.1 Finset.univ hleft))) :
    (r324FirstLeftShiftedCoordinateEquiv e₀ hleft i).1 =
      varIdx
        ((residualPrimitiveBlockOrderIso e₀.1
          (selectedExtractionBlock
            e₀.1 Finset.univ hleft)
          (selectRel_isRelFullyPaired
            e₀.1 Finset.univ hleft).isFullyPairedOn i).1) :=
  rfl

/-- The shifted equivalence preserves the strict order.  The first `+1`
is the R-324 external-endpoint shift; no order information is lost. -/
theorem r324FirstLeftShiftedCoordinateEquiv_lt_iff
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (i j : Fin (2 * residualBlockOrder
      (selectedExtractionBlock
        e₀.1 Finset.univ hleft))) :
    (r324FirstLeftShiftedCoordinateEquiv e₀ hleft i).1 <
        (r324FirstLeftShiftedCoordinateEquiv e₀ hleft j).1 ↔
      i < j := by
  let e :=
    residualPrimitiveBlockOrderIso e₀.1
      (selectedExtractionBlock
        e₀.1 Finset.univ hleft)
      (selectRel_isRelFullyPaired
        e₀.1 Finset.univ hleft).isFullyPairedOn
  rw [
    r324FirstLeftShiftedCoordinateEquiv_apply_val,
    r324FirstLeftShiftedCoordinateEquiv_apply_val]
  change (e i).1.val + 1 < (e j).1.val + 1 ↔ i.val < j.val
  rw [Nat.add_lt_add_iff_right]
  exact e.lt_iff_lt

/-- On the production assembled tuple, the shifted block vertex reads
exactly the `leftMomentIndex` coordinate used by the original first-left
Fubini fibre. -/
theorem assemble_leftMoment_shiftedCoordinate
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y : T4) (v : Fin (2 * m) → T4)
    (i : Fin (2 * residualBlockOrder
      (selectedExtractionBlock
        e₀.1 Finset.univ hleft))) :
    assemble x y (fun k => v (leftMomentIndex k))
        (r324FirstLeftShiftedCoordinateEquiv
          e₀ hleft i).1 =
      v (leftMomentIndex
        ((residualPrimitiveBlockOrderIso e₀.1
          (selectedExtractionBlock
            e₀.1 Finset.univ hleft)
          (selectRel_isRelFullyPaired
            e₀.1 Finset.univ hleft).isFullyPairedOn i).1)) := by
  rw [r324FirstLeftShiftedCoordinateEquiv_apply_val,
    assemble_varIdx]

/-! ## Exact factorization of the production Green skeleton -/

/-- A production Green-chain edge is exterior to the selected shifted
block when neither endpoint is one of its internal vertices. -/
def R324FirstLeftChainEdgeOutside
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (edge : Fin (m + 1)) : Prop :=
  edge.castSucc ∉ r324FirstLeftShiftedBlock e₀ hleft ∧
    edge.succ ∉ r324FirstLeftShiftedBlock e₀ hleft

instance instDecidableR324FirstLeftChainEdgeOutside
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (edge : Fin (m + 1)) :
    Decidable
      (R324FirstLeftChainEdgeOutside
        e₀ hleft edge) := by
  unfold R324FirstLeftChainEdgeOutside
  infer_instance

/-- All factors of the production difference product whose chain edge
touches the shifted first-left block. -/
def r324FirstLeftTouchingGreenProduct
    {m : ℕ} (κ : PartialPairing (Fin m))
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (xt : Fin (m + 2) → T4) : ℂ :=
  ∏ edge : Fin (m + 1),
    if R324FirstLeftChainEdgeOutside e₀ hleft edge then
      1
    else
      originalGreenEdge xt edge -
        extractedShortcutGreenEdge κ xt edge

/-- The complementary production Green factors, with both coordinate
reads outside the shifted first-left block. -/
def r324FirstLeftExteriorGreenProduct
    {m : ℕ} (κ : PartialPairing (Fin m))
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (xt : Fin (m + 2) → T4) : ℂ :=
  ∏ edge : Fin (m + 1),
    if R324FirstLeftChainEdgeOutside e₀ hleft edge then
      originalGreenEdge xt edge -
        extractedShortcutGreenEdge κ xt edge
    else
      1

/-- Exact touching/exterior split of the production
`renormalizedGreenSkeleton`. -/
theorem renormalizedGreenSkeleton_eq_firstLeftTouching_mul_exterior
    {m : ℕ} (κ : PartialPairing (Fin m))
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (xt : Fin (m + 2) → T4) :
    renormalizedGreenSkeleton κ xt =
      r324FirstLeftTouchingGreenProduct
          κ e₀ hleft xt *
        r324FirstLeftExteriorGreenProduct
          κ e₀ hleft xt := by
  rw [renormalizedGreenSkeleton_eq_differenceProduct]
  unfold expandedGreenDifferenceProduct
    r324FirstLeftTouchingGreenProduct
    r324FirstLeftExteriorGreenProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro edge _hedge
  by_cases hout :
      R324FirstLeftChainEdgeOutside e₀ hleft edge
  · simp only [hout, if_true, one_mul]
  · simp only [hout, if_false, mul_one]

/-- Specialization to the actual reconstructed member of the original
first-left moment fibre.  In particular the left side is the same
production skeleton occurring in `deterministicMomentIntegrand`. -/
theorem r324FirstLeftReconstruct_greenSkeleton_shifted_factorization
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft)
    (x y : T4) (v : Fin (2 * m) → T4) :
    renormalizedGreenSkeleton
        (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
        (assemble x y
          (fun i => v (leftMomentIndex i))) =
      r324FirstLeftTouchingGreenProduct
          (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
          e₀ hleft
          (assemble x y
            (fun i => v (leftMomentIndex i))) *
        r324FirstLeftExteriorGreenProduct
          (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
          e₀ hleft
          (assemble x y
            (fun i => v (leftMomentIndex i))) :=
  renormalizedGreenSkeleton_eq_firstLeftTouching_mul_exterior
    _ e₀ hleft _

end

end Anderson4D
