import Anderson4D.PermSum.SingleScalePosition
import Anderson4D.PermSum.SingleScaleTargetLedger
import Anderson4D.PermSum.SingleScaleAnchorGlue

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-!
# Precise gain glue

The target ledger records precise-pair gains in traversal order.  On the
left of the anchor this is the reverse of the original word order; on the
right it is the original forward order.  This module identifies every
retained original edge with a concrete precise ledger block and compares
the two products without ever comparing a forward ratio pointwise with its
reverse.
-/

noncomputable local instance locatedNXParityBlockDecidableEq
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    DecidableEq (LocatedNXParityBlock (m := m) Nm mu) :=
  Classical.decEq _

/-- The upper endpoint of an original adjacency edge. -/
def adjacentRightPosition {m : ℕ}
    (edge : AdjacentIndex m) : Fin m :=
  ⟨edge.1.1 + 1, edge.2⟩

/--
The dyadic ratio on an original edge, oriented outward from the anchor.
Strictly left edges use the reversed original ratio; right edges use the
ordinary forward ratio.
-/
noncomputable def finAnchorOrientedDyadicEdgeGain
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (anchor : Fin m) (cls : Fin m → ActiveNXClass Nm mu)
    (edge : AdjacentIndex m) : ℝ :=
  if edge.1.1 < anchor.1 then
    dyadicForwardGain
      (singleScaleSigma2 Nm mu (cls (adjacentRightPosition edge)).1)
      (singleScaleSigma2 Nm mu (cls edge.1).1)
  else
    dyadicForwardGain
      (singleScaleSigma2 Nm mu (cls edge.1).1)
      (singleScaleSigma2 Nm mu (cls (adjacentRightPosition edge)).1)

/-- On the left, the outward gain is the original-edge ratio with its
endpoint order reversed. -/
theorem finAnchorOrientedDyadicEdgeGain_left_eq_reverseOriginal
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (anchor : Fin m) (cls : Fin m → ActiveNXClass Nm mu)
    (edge : AdjacentIndex m) (hleft : edge.1.1 < anchor.1) :
    finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge =
      dyadicForwardGain
        (singleScaleSigma2 Nm mu
          (cls (adjacentRightPosition edge)).1)
        (singleScaleSigma2 Nm mu (cls edge.1).1) := by
  simp [finAnchorOrientedDyadicEdgeGain, hleft]

/-- On the right, the outward gain is the ordinary original-edge forward
ratio. -/
theorem finAnchorOrientedDyadicEdgeGain_right_eq_forwardOriginal
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (anchor : Fin m) (cls : Fin m → ActiveNXClass Nm mu)
    (edge : AdjacentIndex m) (hright : anchor.1 ≤ edge.1.1) :
    finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge =
      dyadicForwardGain
        (singleScaleSigma2 Nm mu (cls edge.1).1)
        (singleScaleSigma2 Nm mu
          (cls (adjacentRightPosition edge)).1) := by
  simp [finAnchorOrientedDyadicEdgeGain, not_lt_of_ge hright]

/-- The selected phase edges which were not charged to a coarse block. -/
def finAnchorRetainedPhaseEdges
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    Finset (AdjacentIndex m) :=
  finAnchorPositionPhaseCarrierWithPhases
      leftPhase rightPhase anchor \
    finAnchorNXExceptionalEdgesWithPhases Nm mu
      leftPhase rightPhase anchor cls O

@[simp] theorem mem_finAnchorRetainedPhaseEdges
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) (edge : AdjacentIndex m) :
    edge ∈ finAnchorRetainedPhaseEdges Nm mu
        leftPhase rightPhase anchor cls O ↔
      edge ∈ finAnchorPositionPhaseCarrierWithPhases
          leftPhase rightPhase anchor ∧
        edge ∉ finAnchorNXExceptionalEdgesWithPhases Nm mu
          leftPhase rightPhase anchor cls O := by
  simp [finAnchorRetainedPhaseEdges]

private theorem nodup_of_map_nodup
    {α β : Type*} (f : α → β) (xs : List α)
    (h : (xs.map f).Nodup) :
    xs.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.nodup_cons] at h ⊢
      refine ⟨?_, ih h.2⟩
      intro hx
      exact h.1 (List.mem_map_of_mem hx)

/-- No block is repeated when all of its position occurrences are unique. -/
private theorem positionBlocks_nodup_of_flatten_nodup
    {α : Type*} (bs : List (PositionBlock α))
    (hflat : (bs.flatMap PositionBlock.entries).Nodup) :
    bs.Nodup := by
  classical
  induction bs with
  | nil => simp
  | cons b bs ih =>
      rw [List.flatMap_cons, List.nodup_append] at hflat
      rcases hflat with ⟨_hhead, htail, hcross⟩
      rw [List.nodup_cons]
      refine ⟨?_, ih htail⟩
      intro hb
      cases b with
      | single x =>
          exact hcross x (by simp [PositionBlock.entries])
            x (by
              rw [List.mem_flatMap]
              exact ⟨PositionBlock.single x, hb,
                by simp [PositionBlock.entries]⟩) rfl
      | pair x y =>
          exact hcross x (by simp [PositionBlock.entries])
            x (by
              rw [List.mem_flatMap]
              exact ⟨PositionBlock.pair x y, hb,
                by simp [PositionBlock.entries]⟩) rfl

/-- The concrete coarse ledger has no repeated located block. -/
theorem finAnchorNXLocatedCoarseLedgerWithPhases_nodup
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O).Nodup := by
  apply nodup_of_map_nodup LocatedNXParityBlock.positionBlock
  rw [map_positionBlock_finAnchorNXLocatedCoarseLedgerWithPhases]
  apply positionBlocks_nodup_of_flatten_nodup
  exact nodup_flatten_finAnchorPositionScheduleWithPhases
    leftPhase rightPhase anchor

private theorem retained_edge_has_precise_block
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) (edge : AdjacentIndex m)
    (hedge : edge ∈ finAnchorRetainedPhaseEdges Nm mu
      leftPhase rightPhase anchor cls O) :
    ∃ b : LocatedNXParityBlock (m := m) Nm mu,
      b ∈ finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O ∧
        ∃ (i j : Fin m) (p : NXPairBlock Nm mu),
          b = LocatedNXParityBlock.pair i j p ∧
          p.left = cls i ∧
          p.right = cls j ∧
          ((i ∈ leftAnchorPositions anchor ∧
              j ∈ leftAnchorPositions anchor ∧
              edge.1 = j ∧
              j.1 + 1 = i.1 ∧
              p.skipRight = decide (edge ∈ O)) ∨
            (i ∈ rightAnchorPositions anchor ∧
              j ∈ rightAnchorPositions anchor ∧
              edge.1 = i ∧
              i.1 + 1 = j.1 ∧
              p.skipRight = decide (edge ∈ O))) := by
  have h := (mem_finAnchorRetainedPhaseEdges
    Nm mu leftPhase rightPhase anchor cls O edge).mp hedge
  obtain ⟨i, j, p, hmem, hpLeft, hpRight, hside⟩ :=
    finAnchorNX_retained_phaseCarrier_mem_precisePair
      Nm mu leftPhase rightPhase anchor cls O edge h.1 h.2
  exact ⟨LocatedNXParityBlock.pair i j p, hmem,
    i, j, p, rfl, hpLeft, hpRight, hside⟩

/--
Choose the concrete precise coarse-ledger block which accounts for a
retained edge.  The fallback branch is unreachable on the retained finset.
-/
noncomputable def retainedEdgePreciseBlock
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) (edge : AdjacentIndex m) :
    LocatedNXParityBlock (m := m) Nm mu :=
  if hedge : edge ∈ finAnchorRetainedPhaseEdges Nm mu
      leftPhase rightPhase anchor cls O then
    Classical.choose
      (retained_edge_has_precise_block Nm mu
        leftPhase rightPhase anchor cls O edge hedge)
  else
    LocatedNXParityBlock.single anchor (cls anchor) false

theorem retainedEdgePreciseBlock_spec
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) (edge : AdjacentIndex m)
    (hedge : edge ∈ finAnchorRetainedPhaseEdges Nm mu
      leftPhase rightPhase anchor cls O) :
    retainedEdgePreciseBlock Nm mu
        leftPhase rightPhase anchor cls O edge ∈
        finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O ∧
      ∃ (i j : Fin m) (p : NXPairBlock Nm mu),
        retainedEdgePreciseBlock Nm mu
            leftPhase rightPhase anchor cls O edge =
            LocatedNXParityBlock.pair i j p ∧
        p.left = cls i ∧
        p.right = cls j ∧
        ((i ∈ leftAnchorPositions anchor ∧
            j ∈ leftAnchorPositions anchor ∧
            edge.1 = j ∧
            j.1 + 1 = i.1 ∧
            p.skipRight = decide (edge ∈ O)) ∨
          (i ∈ rightAnchorPositions anchor ∧
            j ∈ rightAnchorPositions anchor ∧
            edge.1 = i ∧
            i.1 + 1 = j.1 ∧
            p.skipRight = decide (edge ∈ O))) := by
  rw [retainedEdgePreciseBlock, dif_pos hedge]
  exact Classical.choose_spec
    (retained_edge_has_precise_block Nm mu
      leftPhase rightPhase anchor cls O edge hedge)

private theorem retainedEdgePreciseBlock_injectiveOn
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    Set.InjOn
      (retainedEdgePreciseBlock Nm mu
        leftPhase rightPhase anchor cls O)
      (finAnchorRetainedPhaseEdges Nm mu
        leftPhase rightPhase anchor cls O) := by
  intro edge₁ hedge₁ edge₂ hedge₂ heq
  obtain ⟨_hmem₁, i₁, j₁, p₁, hb₁,
      _hpLeft₁, _hpRight₁, hside₁⟩ :=
    retainedEdgePreciseBlock_spec Nm mu
      leftPhase rightPhase anchor cls O edge₁ hedge₁
  obtain ⟨_hmem₂, i₂, j₂, p₂, hb₂,
      _hpLeft₂, _hpRight₂, hside₂⟩ :=
    retainedEdgePreciseBlock_spec Nm mu
      leftPhase rightPhase anchor cls O edge₂ hedge₂
  have hpairs :
      LocatedNXParityBlock.pair i₁ j₁ p₁ =
        LocatedNXParityBlock.pair i₂ j₂ p₂ := by
    rw [← hb₁, ← hb₂, heq]
  cases hpairs
  apply Subtype.ext
  apply Fin.ext
  rcases hside₁ with hleft₁ | hright₁ <;>
    rcases hside₂ with hleft₂ | hright₂
  · exact congrArg Fin.val (hleft₁.2.2.1.trans hleft₂.2.2.1.symm)
  · have hiLeft :=
      (mem_leftAnchorPositions_iff anchor i₁).mp hleft₁.1
    have hiRight :=
      (mem_rightAnchorPositions_iff anchor i₁).mp hright₂.1
    omega
  · have hiRight :=
      (mem_rightAnchorPositions_iff anchor i₁).mp hright₁.1
    have hiLeft :=
      (mem_leftAnchorPositions_iff anchor i₁).mp hleft₂.1
    omega
  · exact congrArg Fin.val (hright₁.2.2.1.trans hright₂.2.2.1.symm)

theorem retainedEdgePreciseBlock_gain_eq
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) (edge : AdjacentIndex m)
    (hedge : edge ∈ finAnchorRetainedPhaseEdges Nm mu
      leftPhase rightPhase anchor cls O) :
    locatedBlockPreciseGain Nm mu
        (retainedEdgePreciseBlock Nm mu
          leftPhase rightPhase anchor cls O edge) =
      finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge := by
  obtain ⟨_hmem, i, j, p, hb, hpLeft, hpRight, hside⟩ :=
    retainedEdgePreciseBlock_spec Nm mu
      leftPhase rightPhase anchor cls O edge hedge
  rw [hb]
  simp only [locatedBlockPreciseGain]
  rcases hside with hleft | hright
  · obtain ⟨hiLeft, hjLeft, hedgej, hadj, _hskip⟩ := hleft
    have hedgeLeft : edge.1.1 < anchor.1 := by
      rw [hedgej]
      exact (mem_leftAnchorPositions_iff anchor j).mp hjLeft
    have hrightEndpoint : adjacentRightPosition edge = i := by
      apply Fin.ext
      simp only [adjacentRightPosition]
      omega
    rw [hpLeft, hpRight, finAnchorOrientedDyadicEdgeGain,
      if_pos hedgeLeft, hrightEndpoint, hedgej]
  · obtain ⟨hiRight, hjRight, hedgei, hadj, _hskip⟩ := hright
    have hedgeRight : ¬edge.1.1 < anchor.1 := by
      rw [hedgei]
      exact not_lt_of_ge
        (Nat.le_of_lt
          ((mem_rightAnchorPositions_iff anchor i).mp hiRight))
    have hrightEndpoint : adjacentRightPosition edge = j := by
      apply Fin.ext
      simp only [adjacentRightPosition]
      omega
    rw [hpLeft, hpRight, finAnchorOrientedDyadicEdgeGain,
      if_neg hedgeRight, hrightEndpoint, hedgei]

/-- Concrete precise blocks selected by the retained original edges. -/
noncomputable def retainedPreciseBlocks
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    Finset (LocatedNXParityBlock (m := m) Nm mu) := by
  classical
  exact
    (finAnchorRetainedPhaseEdges Nm mu
      leftPhase rightPhase anchor cls O).image
        (retainedEdgePreciseBlock Nm mu
          leftPhase rightPhase anchor cls O)

private theorem retainedPreciseBlocks_subset_coarse
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    retainedPreciseBlocks Nm mu
        leftPhase rightPhase anchor cls O ⊆
      (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O).toFinset := by
  classical
  intro b hb
  rw [retainedPreciseBlocks, Finset.mem_image] at hb
  obtain ⟨edge, hedge, rfl⟩ := hb
  exact List.mem_toFinset.mpr
    (retainedEdgePreciseBlock_spec Nm mu
      leftPhase rightPhase anchor cls O edge hedge).1

private theorem locatedBlockPreciseGain_le_one
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (b : LocatedNXParityBlock (m := m) Nm mu) :
    locatedBlockPreciseGain Nm mu b ≤ 1 := by
  cases b with
  | single _ _ _ | roughPair _ _ _ =>
      simp [locatedBlockPreciseGain]
  | pair _ _ p =>
      exact min_le_left _ _

private theorem finset_prod_le_prod_of_subset_of_le_one
    {α : Type*} [DecidableEq α]
    (f : α → ℝ) (s t : Finset α) (hsub : s ⊆ t)
    (hnonneg : ∀ x ∈ t, 0 ≤ f x)
    (hle : ∀ x ∈ t, f x ≤ 1) :
    ∏ x ∈ t, f x ≤ ∏ x ∈ s, f x := by
  have hdiff :
      ∏ x ∈ t \ s, f x ≤ 1 :=
    Finset.prod_le_one
      (fun x hx => hnonneg x (Finset.mem_sdiff.mp hx).1)
      (fun x hx => hle x (Finset.mem_sdiff.mp hx).1)
  have hsnonneg :
      0 ≤ ∏ x ∈ s, f x :=
    Finset.prod_nonneg fun x hx => hnonneg x (hsub hx)
  calc
    (∏ x ∈ t, f x) =
        (∏ x ∈ t \ s, f x) * ∏ x ∈ s, f x :=
      (Finset.prod_sdiff hsub).symm
    _ ≤ 1 * ∏ x ∈ s, f x :=
      mul_le_mul_of_nonneg_right hdiff hsnonneg
    _ = ∏ x ∈ s, f x := one_mul _

theorem retainedPreciseBlocks_gainProduct_eq
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    ∏ b ∈ retainedPreciseBlocks Nm mu
          leftPhase rightPhase anchor cls O,
        locatedBlockPreciseGain Nm mu b =
      ∏ edge ∈ finAnchorRetainedPhaseEdges Nm mu
          leftPhase rightPhase anchor cls O,
        finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge := by
  classical
  rw [retainedPreciseBlocks,
    Finset.prod_image
      (retainedEdgePreciseBlock_injectiveOn Nm mu
        leftPhase rightPhase anchor cls O)]
  apply Finset.prod_congr rfl
  intro edge hedge
  exact retainedEdgePreciseBlock_gain_eq Nm mu
    leftPhase rightPhase anchor cls O edge hedge

/--
The concrete precise-gain ledger is bounded by the product on exactly the
retained original phase edges.  This is the direction required for the
upper estimate: any additional precise ledger factors are in `[0,1]`.

The left factors are definitionally reverse original-edge ratios, while
the right factors are forward ratios; no forward/reverse comparison is
used.
-/
theorem finAnchorNXCoarse_preciseGainProduct_le_retainedPhaseProduct
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    locatedLedgerPreciseGainProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) ≤
      ∏ edge ∈ finAnchorRetainedPhaseEdges Nm mu
          leftPhase rightPhase anchor cls O,
        finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge := by
  classical
  let coarse :=
    finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O
  have hnodup : coarse.Nodup := by
    exact finAnchorNXLocatedCoarseLedgerWithPhases_nodup
      Nm mu leftPhase rightPhase anchor cls O
  calc
    locatedLedgerPreciseGainProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) =
        ∏ b ∈ coarse.toFinset, locatedBlockPreciseGain Nm mu b := by
      rw [locatedLedgerPreciseGainProduct]
      symm
      exact List.prod_toFinset
        (locatedBlockPreciseGain Nm mu) hnodup
    _ ≤ ∏ b ∈ retainedPreciseBlocks Nm mu
          leftPhase rightPhase anchor cls O,
        locatedBlockPreciseGain Nm mu b := by
      apply finset_prod_le_prod_of_subset_of_le_one
      · exact retainedPreciseBlocks_subset_coarse Nm mu
          leftPhase rightPhase anchor cls O
      · intro b hb
        exact locatedBlockPreciseGain_nonneg Nm mu b
      · intro b hb
        exact locatedBlockPreciseGain_le_one Nm mu b
    _ = ∏ edge ∈ finAnchorRetainedPhaseEdges Nm mu
          leftPhase rightPhase anchor cls O,
        finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge :=
      retainedPreciseBlocks_gainProduct_eq Nm mu
        leftPhase rightPhase anchor cls O

/-- Literal carrier-minus-exception form of the precise-gain bound. -/
theorem
    finAnchorNXCoarse_preciseGainProduct_le_phaseCarrier_sdiff_exception
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    locatedLedgerPreciseGainProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) ≤
      ∏ edge ∈
          finAnchorPositionPhaseCarrierWithPhases
              leftPhase rightPhase anchor \
            finAnchorNXExceptionalEdgesWithPhases Nm mu
              leftPhase rightPhase anchor cls O,
        finAnchorOrientedDyadicEdgeGain Nm mu anchor cls edge := by
  simpa [finAnchorRetainedPhaseEdges] using
    finAnchorNXCoarse_preciseGainProduct_le_retainedPhaseProduct
      Nm mu leftPhase rightPhase anchor cls O

end XYCluster

end

end Anderson4D
