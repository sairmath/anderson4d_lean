import Anderson4D.DetParametrix.Paper42_Moment.R324FirstLeftShiftedGreenAdapter
/-! # Carrier-relative edges of the genuine first-left R-324 block -/
set_option warningAsError true
set_option autoImplicit false
namespace Anderson4D
noncomputable section
open scoped BigOperators

theorem r324FirstLeft_selectedBlock_eq_Icc
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b) :
    selectedExtractionBlock e₀.1 Finset.univ hleft =
      Finset.Icc
        (selectRel e₀.1 Finset.univ hleft).1
        (selectRel e₀.1 Finset.univ hleft).2 := by
  unfold selectedExtractionBlock
  ext i
  simp [relIcc]

theorem r324FirstLeft_endpoint_span
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b) :
    (selectRel e₀.1 Finset.univ hleft).2.val + 1 -
        (selectRel e₀.1 Finset.univ hleft).1.val =
      2 * residualBlockOrder
        (selectedExtractionBlock
          e₀.1 Finset.univ hleft) := by
  let p := selectRel e₀.1 Finset.univ hleft
  let B := selectedExtractionBlock e₀.1 Finset.univ hleft
  have hcard :
      B.card = 2 * residualBlockOrder B :=
    (Nat.two_mul_div_two_of_even
      (residualBlock_card_even e₀.1 B
        (selectRel_isRelFullyPaired
          e₀.1 Finset.univ hleft).isFullyPairedOn)).symm
  calc
    p.2.val + 1 - p.1.val =
        (Finset.Icc p.1 p.2).card := by
      rw [Fin.card_Icc]
    _ = B.card := by
      dsimp only [p, B]
      rw [r324FirstLeft_selectedBlock_eq_Icc]
    _ = _ := hcard

def r324FirstLeftPredecessorEdge
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b) :
    Fin (m + 1) :=
  ⟨(selectRel e₀.1 Finset.univ hleft).1.val, by
    exact Nat.lt_succ_of_lt
      (selectRel e₀.1 Finset.univ hleft).1.isLt⟩

def r324FirstLeftOutgoingEdge
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b) :
    Fin (m + 1) :=
  extractedRightEdge
    (selectRel e₀.1 Finset.univ hleft)

theorem mem_r324FirstLeftShiftedBlock_iff_bounds
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (j : Fin (m + 2)) :
    j ∈ r324FirstLeftShiftedBlock e₀ hleft ↔
      (selectRel e₀.1 Finset.univ hleft).1.val + 1 ≤ j.val ∧
        j.val ≤
          (selectRel e₀.1 Finset.univ hleft).2.val + 1 := by
  let p := selectRel e₀.1 Finset.univ hleft
  constructor
  · intro hj
    unfold r324FirstLeftShiftedBlock at hj
    obtain ⟨i, hi, hij⟩ :=
      Finset.mem_image.mp hj
    have hi' :
        i ∈ Finset.Icc p.1 p.2 := by
      rwa [← r324FirstLeft_selectedBlock_eq_Icc
        e₀ hleft]
    have hb := Finset.mem_Icc.mp hi'
    dsimp only [p] at hb
    have hv := congrArg Fin.val hij
    simp only [varIdx_val] at hv
    omega
  · intro hj
    let i : Fin m :=
      ⟨j.val - 1, by
        have hb :=
          (selectRel e₀.1 Finset.univ hleft).2.isLt
        omega⟩
    have hi :
        i ∈ selectedExtractionBlock
          e₀.1 Finset.univ hleft := by
      rw [r324FirstLeft_selectedBlock_eq_Icc]
      apply Finset.mem_Icc.mpr
      change
        (selectRel e₀.1 Finset.univ hleft).1.val ≤
            j.val - 1 ∧
          j.val - 1 ≤
            (selectRel e₀.1 Finset.univ hleft).2.val
      omega
    unfold r324FirstLeftShiftedBlock
    apply Finset.mem_image.mpr
    refine ⟨i, hi, ?_⟩
    apply Fin.ext
    change j.val - 1 + 1 = j.val
    omega

theorem not_chainEdgeOutside_iff_firstLeft_range
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (edge : Fin (m + 1)) :
    ¬R324FirstLeftChainEdgeOutside e₀ hleft edge ↔
      (r324FirstLeftPredecessorEdge e₀ hleft).val ≤ edge.val ∧
        edge.val ≤
          (r324FirstLeftOutgoingEdge e₀ hleft).val := by
  unfold R324FirstLeftChainEdgeOutside
  simp only [not_and_or, not_not]
  rw [mem_r324FirstLeftShiftedBlock_iff_bounds,
    mem_r324FirstLeftShiftedBlock_iff_bounds]
  change
    (((selectRel e₀.1 Finset.univ hleft).1.val + 1 ≤ edge.val ∧
        edge.val ≤
          (selectRel e₀.1 Finset.univ hleft).2.val + 1) ∨
      ((selectRel e₀.1 Finset.univ hleft).1.val + 1 ≤ edge.val + 1 ∧
        edge.val + 1 ≤
          (selectRel e₀.1 Finset.univ hleft).2.val + 1)) ↔
      (selectRel e₀.1 Finset.univ hleft).1.val ≤ edge.val ∧
        edge.val ≤
          (selectRel e₀.1 Finset.univ hleft).2.val + 1
  have hb :=
    (selectRel e₀.1 Finset.univ hleft).2.isLt
  have ha :=
    (selectRel e₀.1 Finset.univ hleft).1.isLt
  have he : edge.val ≤ m := Nat.lt_succ_iff.mp edge.isLt
  have hab :=
    (selectRel_isRelFullyPaired
      e₀.1 Finset.univ hleft).le
  omega

def r324FirstLeftTouchingEdge
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (k : Fin (2 * residualBlockOrder
      (selectedExtractionBlock
        e₀.1 Finset.univ hleft) + 1)) :
    Fin (m + 1) :=
  ⟨(selectRel e₀.1 Finset.univ hleft).1.val + k.val, by
    have hk := k.isLt
    have hspan := r324FirstLeft_endpoint_span e₀ hleft
    have hb :=
      (selectRel e₀.1 Finset.univ hleft).2.isLt
    omega⟩

theorem r324FirstLeftTouchingGreenProduct_eq_edgeEnumeration
    {m : ℕ} (κ : PartialPairing (Fin m))
    (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (xt : Fin (m + 2) → T4) :
    r324FirstLeftTouchingGreenProduct κ e₀ hleft xt =
      ∏ k : Fin (2 * residualBlockOrder
        (selectedExtractionBlock
          e₀.1 Finset.univ hleft) + 1),
        (originalGreenEdge xt
            (r324FirstLeftTouchingEdge e₀ hleft k) -
          extractedShortcutGreenEdge κ xt
            (r324FirstLeftTouchingEdge e₀ hleft k)) := by
  classical
  let active : Fin (m + 1) → Prop :=
    fun edge =>
      ¬R324FirstLeftChainEdgeOutside e₀ hleft edge
  have hinj :
      Function.Injective
        (r324FirstLeftTouchingEdge e₀ hleft) := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change
      (selectRel e₀.1 Finset.univ hleft).1.val + i.val =
        (selectRel e₀.1 Finset.univ hleft).1.val + j.val at hv
    omega
  have hmem :
      ∀ k,
        active (r324FirstLeftTouchingEdge e₀ hleft k) := by
    intro k
    apply
      (not_chainEdgeOutside_iff_firstLeft_range
        e₀ hleft _).mpr
    simp only [r324FirstLeftTouchingEdge,
      r324FirstLeftPredecessorEdge,
      r324FirstLeftOutgoingEdge, extractedRightEdge_val]
    have hk := k.isLt
    have hspan := r324FirstLeft_endpoint_span e₀ hleft
    have hab :=
      (selectRel_isRelFullyPaired
        e₀.1 Finset.univ hleft).le
    omega
  have hsurj :
      ∀ edge ∈ Finset.univ.filter active,
        ∃ k, r324FirstLeftTouchingEdge e₀ hleft k = edge := by
    intro edge hedge
    have hrange :=
      (not_chainEdgeOutside_iff_firstLeft_range
        e₀ hleft edge).mp
        (Finset.mem_filter.mp hedge).2
    let k : Fin (2 * residualBlockOrder
        (selectedExtractionBlock
          e₀.1 Finset.univ hleft) + 1) :=
      ⟨edge.val -
          (selectRel e₀.1 Finset.univ hleft).1.val, by
        have hspan := r324FirstLeft_endpoint_span e₀ hleft
        have hab :=
          (selectRel_isRelFullyPaired
            e₀.1 Finset.univ hleft).le
        simp only [r324FirstLeftPredecessorEdge,
          r324FirstLeftOutgoingEdge,
          extractedRightEdge_val] at hrange
        omega⟩
    refine ⟨k, ?_⟩
    apply Fin.ext
    change
      (selectRel e₀.1 Finset.univ hleft).1.val +
          (edge.val -
            (selectRel e₀.1 Finset.univ hleft).1.val) =
        edge.val
    simpa only [r324FirstLeftPredecessorEdge] using
      Nat.add_sub_of_le hrange.1
  unfold r324FirstLeftTouchingGreenProduct
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul]
  symm
  exact Finset.prod_bij
    (fun k _ => r324FirstLeftTouchingEdge e₀ hleft k)
    (fun k _ =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem k⟩)
    (fun i _ j _ hij => hinj hij)
    (fun edge hedge => by
      obtain ⟨k, hk⟩ := hsurj edge hedge
      exact ⟨k, Finset.mem_univ _, hk⟩)
    (fun _ _ => rfl)

theorem r324FirstLeftReconstruct_greenSkeleton_eq_carrierEdges
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft)
    (x y : T4) (v : Fin (2 * m) → T4) :
    let κ := (r324FirstLeftReconstruct e₀ hleft ω κB).1.1
    let xt := assemble x y (fun i => v (leftMomentIndex i))
    renormalizedGreenSkeleton κ xt =
      (∏ k : Fin (2 * residualBlockOrder
          (selectedExtractionBlock e₀.1 Finset.univ hleft) + 1),
        (originalGreenEdge xt
            (r324FirstLeftTouchingEdge e₀ hleft k) -
          extractedShortcutGreenEdge κ xt
            (r324FirstLeftTouchingEdge e₀ hleft k))) *
        r324FirstLeftExteriorGreenProduct κ e₀ hleft xt := by
  dsimp only
  rw [r324FirstLeftReconstruct_greenSkeleton_shifted_factorization,
    r324FirstLeftTouchingGreenProduct_eq_edgeEnumeration]

theorem extracted_predecessor_belongs_disjoint_analyticPrefix
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft : ∃ a b, IsRelFullyPaired e₀.1
      (Finset.univ : Finset (Fin m)) a b)
    (hextracted :
      r324FirstLeftPredecessorEdge e₀ hleft ∈
        extractedRightEdges e₀.1) :
    ∃ pre step post,
      r322AnalyticSchedule e₀.1 =
          pre ++ r324FirstLeftSelectedStep e₀ hleft :: post ∧
        step ∈ pre ∧
        Disjoint step.2
          (selectedExtractionBlock
            e₀.1 Finset.univ hleft) ∧
        extractedRightEdge step.1 =
          r324FirstLeftPredecessorEdge e₀ hleft := by
  obtain ⟨p, hp, hedge⟩ :=
    exists_extractedPairOfRightEdge e₀.1
      (r324FirstLeftPredecessorEdge e₀ hleft) hextracted
  have hpSchedule :
      p ∈ (r322AnalyticSchedule e₀.1).map Prod.fst :=
    (r322AnalyticSchedule_endpoints_perm_extract e₀.1).mem_iff.mpr hp
  obtain ⟨step, hstep, hstepEndpoint⟩ :=
    List.mem_map.mp hpSchedule
  obtain ⟨pre, post, hschedule, hdisjoint⟩ :=
    exists_r324FirstLeft_analytic_decomposition e₀ hleft
  have hright :
      step.1.2 <
        (r324FirstLeftSelectedStep e₀ hleft).1.2 := by
    rw [hstepEndpoint]
    have hv := congrArg Fin.val hedge
    simp only [extractedRightEdge_val,
      r324FirstLeftPredecessorEdge] at hv
    simp only [r324FirstLeftSelectedStep_endpoint]
    have hab :=
      (selectRel_isRelFullyPaired
        e₀.1 Finset.univ hleft).le
    omega
  have hpre :
      step ∈ pre :=
    r322AnalyticSchedule_mem_prefix_of_right_lt
      e₀.1 pre post
      (r324FirstLeftSelectedStep e₀ hleft)
      step hschedule hstep hright
  exact
    ⟨pre, step, post, hschedule, hpre,
      hdisjoint step hpre,
      hstepEndpoint ▸ hedge⟩

end

end Anderson4D
