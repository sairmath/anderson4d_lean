import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticHeadSkeletonFactorization
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticHeadPointwiseFactorization
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticBlockFubini
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticBlockOrder
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhaseAProperBlockUpdate
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhaseATerminalBlockUpdate

/-!
# The actual proper-head collapse for R-322

This module connects the first proper step of the paper-order analytic
schedule to the existing `endpointFiberDetJSum`.  The first structural issue
is essential: the standard primitive kernel can be read from the touching
ambient chain only after proving that the first analytic block has no holes.
That fact is derived below from the actual selector recursion, rather than
assumed as a parallel interface.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## A missing interval point was removed at an earlier selector step -/

/-- Endpoint/block steps before sorting into paper order. -/
def r322ExtractionTraceAux
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m)) :
    List (R322ExtractionStep m) :=
  (extractAux κ fuel active).zip
    (extractionBlocksAux κ fuel active)

/-- If a point starts active, lies between the endpoints of a later
selector step, but is absent from that step's concrete trace, then it lies
in the concrete block of a strictly earlier selector step. -/
theorem exists_previous_extractionStep_of_mem_Icc_not_mem
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (i : Fin m) (hiActive : i ∈ active)
    (s : R322ExtractionStep m)
    (hs : s ∈ r322ExtractionTraceAux κ fuel active)
    (hiIcc : i ∈ Finset.Icc s.1.1 s.1.2)
    (hiBlock : i ∉ s.2) :
    ∃ pre post,
      r322ExtractionTraceAux κ fuel active =
          pre ++ s :: post ∧
        ∃ earlier ∈ pre, i ∈ earlier.2 := by
  induction fuel generalizing active with
  | zero =>
      simp [r322ExtractionTraceAux] at hs
  | succ fuel ih =>
      by_cases h :
          ∃ a b, IsRelFullyPaired κ active a b
      · let p := selectRel κ active h
        let B := relIcc active p.1 p.2
        let active' := active \ B
        have htrace :
            r322ExtractionTraceAux κ (fuel + 1) active =
              (p, B) ::
                r322ExtractionTraceAux κ fuel active' := by
          simp only [r322ExtractionTraceAux,
            extractAux_succ_pos fuel h,
            extractionBlocksAux_succ_pos fuel h,
            List.zip_cons_cons]
          rfl
        rw [htrace] at hs
        rcases List.mem_cons.mp hs with hsCurrent | hsTail
        · subst s
          exfalso
          apply hiBlock
          exact mem_relIcc.mpr
            ⟨hiActive,
              (Finset.mem_Icc.mp hiIcc).1,
              (Finset.mem_Icc.mp hiIcc).2⟩
        · by_cases hiB : i ∈ B
          · obtain ⟨pre, post, htail⟩ :=
              List.mem_iff_append.mp hsTail
            refine
              ⟨(p, B) :: pre, post, ?_, ?_⟩
            · rw [htrace, htail]
              rfl
            · exact
                ⟨(p, B), List.mem_cons_self, hiB⟩
          · have hiActive' : i ∈ active' :=
              Finset.mem_sdiff.mpr ⟨hiActive, hiB⟩
            obtain
              ⟨pre, post, htail,
                  earlier, hearlier, hiEarlier⟩ :=
              ih active' hiActive' hsTail
            refine
              ⟨(p, B) :: pre, post, ?_, ?_⟩
            · rw [htrace, htail]
              rfl
            · exact
                ⟨earlier,
                  List.mem_cons_of_mem _ hearlier,
                  hiEarlier⟩
      · have htrace :
            r322ExtractionTraceAux κ (fuel + 1) active =
              [] := by
          simp [r322ExtractionTraceAux,
            extractAux_succ_neg fuel h,
            extractionBlocksAux_succ_neg fuel h]
        rw [htrace] at hs
        simp at hs

/-! ## The first analytic block has no holes -/

/-- The unsorted paired extraction trace inherits the directional endpoint
geometry of the selector recursion. -/
theorem r322ExtractionTraceAux_pairwise_earlierCompatible
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m)) :
    (r322ExtractionTraceAux κ fuel active).Pairwise
      (fun s t =>
        EarlierReductionIntervalCompatible s.1 t.1) := by
  rw [← List.pairwise_map]
  have haligned :=
    extractAux_extractionBlocksAux_aligned
      κ fuel active
  have hlength :
      (extractAux κ fuel active).length ≤
        (extractionBlocksAux κ fuel active).length :=
    Nat.le_of_eq haligned.length_eq
  have hprojection :
      (r322ExtractionTraceAux κ fuel active).map
          Prod.fst =
        extractAux κ fuel active := by
    exact List.map_fst_zip hlength
  rw [hprojection]
  exact
    extractAux_pairwise_earlierCompatible
      κ fuel active

/-- The head of the right-endpoint-sorted schedule is a genuine ambient
interval.  Any hole would have been removed by an earlier selector block
strictly nested inside it, hence would have a smaller right endpoint and
would have sorted before the alleged head. -/
theorem r322AnalyticSchedule_head_block_eq_Icc
    {m : ℕ} (κ : PartialPairing (Fin m))
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail) :
    head.2 = Finset.Icc head.1.1 head.1.2 := by
  have hheadMem :
      head ∈ r322AnalyticSchedule κ := by
    rw [hschedule]
    simp
  have hheadAligned :
      ExtractionPairBlockAligned head.1 head.2 :=
    r322AnalyticSchedule_forall_aligned κ head hheadMem
  apply Finset.Subset.antisymm
  · intro i hi
    exact Finset.mem_Icc.mpr
      (hheadAligned.2.2 i hi)
  · intro i hiIcc
    by_contra hiBlock
    have hheadRaw :
        head ∈ r322ExtractionTraceAux κ m Finset.univ := by
      have hraw :
          head ∈
            (extract κ).zip (extractionBlocks κ) :=
        (List.mem_insertionSort R322StepRightLE).mp
          hheadMem
      simpa only [r322ExtractionTraceAux,
        extract, extractionBlocks] using hraw
    obtain
        ⟨pre, post, hrawDecomp,
          earlier, hearlierPre, hiEarlier⟩ :=
      exists_previous_extractionStep_of_mem_Icc_not_mem
        κ m Finset.univ i (by simp) head hheadRaw
        hiIcc hiBlock
    have hearlierRaw :
        earlier ∈
          r322ExtractionTraceAux κ m Finset.univ := by
      rw [hrawDecomp]
      exact List.mem_append_left _ hearlierPre
    have hearlierMem :
        earlier ∈ r322AnalyticSchedule κ := by
      apply
        (List.mem_insertionSort R322StepRightLE).mpr
      simpa only [r322ExtractionTraceAux,
        extract, extractionBlocks] using hearlierRaw
    have hearlierAligned :
        ExtractionPairBlockAligned
          earlier.1 earlier.2 :=
      r322AnalyticSchedule_forall_aligned
        κ earlier hearlierMem
    have hrawPairwise :=
      r322ExtractionTraceAux_pairwise_earlierCompatible
        κ m Finset.univ
    rw [hrawDecomp, List.pairwise_append] at hrawPairwise
    have hcompatible :
        EarlierReductionIntervalCompatible
          earlier.1 head.1 :=
      hrawPairwise.2.2 earlier hearlierPre
        head (by simp)
    have hiEarlierBounds :=
      hearlierAligned.2.2 i hiEarlier
    have hearlierRightLt :
        earlier.1.2 < head.1.2 := by
      rcases hcompatible with hleft | hright | hnested
      · have hiHeadBounds :=
          Finset.mem_Icc.mp hiIcc
        exfalso
        omega
      · have hiHeadBounds :=
          Finset.mem_Icc.mp hiIcc
        exfalso
        omega
      · exact hnested.2
    have hearlierTail : earlier ∈ tail := by
      rw [hschedule, List.mem_cons] at hearlierMem
      rcases hearlierMem with heq | htail
      · subst earlier
        exact (lt_irrefl _ hearlierRightLt).elim
      · exact htail
    have hheadBeforeEarlier :
        head.1.2 < earlier.1.2 :=
      (List.pairwise_cons.mp
        (by
          rw [← hschedule]
          exact
            r322AnalyticSchedule_pairwise_right_lt κ)).1
        earlier hearlierTail
    exact (not_lt_of_ge hearlierRightLt.le)
      hheadBeforeEarlier

/-! ## Proper-head coordinates are precisely internal coordinates -/

/-- A proper head of a non-splitting schedule meets neither global
endpoint. -/
theorem r322AnalyticProperHead_endpoint_bounds
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    0 < head.1.1.val ∧
      head.1.2.val < 2 * q - 1 := by
  have hheadMem :
      head ∈ r322AnalyticSchedule κ := by
    rw [hschedule]
    simp
  have hendpointMem :
      head.1 ∈ extract κ :=
    r322AnalyticSchedule_endpoint_mem_extract
      κ hheadMem
  have hwholeIff :=
    extracted_meets_global_endpoint_iff_whole
      hq (mem_nonSplitPairings.mp hκ)
      head.1 hendpointMem
  have hnotMeet :
      ¬(head.1.1 =
            (⟨0, by omega⟩ :
              Fin (2 * q)) ∨
          head.1.2 =
            (⟨2 * q - 1, by omega⟩ :
              Fin (2 * q))) := by
    intro hmeet
    apply hproper
    have hwhole := hwholeIff.mp hmeet
    simpa only [r322WholeEndpoint] using hwhole
  constructor
  · have hne :
        head.1.1.val ≠ 0 := by
      intro hzero
      apply hnotMeet
      left
      apply Fin.ext
      exact hzero
    omega
  · have hne :
        head.1.2.val ≠ 2 * q - 1 := by
      intro hlast
      apply hnotMeet
      right
      apply Fin.ext
      exact hlast
    have hlt := head.1.2.isLt
    omega

/-- Every vertex of a proper analytic head block is one of the internal
coordinates of the ambient `detJ`. -/
theorem r322AnalyticProperHead_block_vertex_bounds
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (i : Fin (2 * q)) (hi : i ∈ head.2) :
    0 < i.val ∧ i.val < 2 * q - 1 := by
  have hblock :=
    r322AnalyticSchedule_head_block_eq_Icc
      κ head tail hschedule
  have hiBounds :
      head.1.1 ≤ i ∧ i ≤ head.1.2 := by
    rw [hblock] at hi
    exact Finset.mem_Icc.mp hi
  have hendpointBounds :=
    r322AnalyticProperHead_endpoint_bounds
      hq κ hκ head tail hschedule hproper
  omega

/-- Internal ambient coordinates selected by the proper head are
equivalent to the concrete head block itself. -/
def r322AnalyticProperHeadInternalCoordinateEquiv
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    {i : Fin (2 * q - 2) //
        r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} ≃
      head.2 := by
  let f :
      {i : Fin (2 * q - 2) //
          r322SelectedFinPredicate
            (r322InternalCoordinatesOfBlock
              q hq head.2) i} →
        head.2 :=
    fun i =>
      ⟨primitiveInternalIdx q hq i.1,
        (mem_r322InternalCoordinatesOfBlock
          q hq head.2 i.1).mp i.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hval :=
      congrArg (fun b : head.2 => b.1.val) hij
    change i.1.val + 1 = j.1.val + 1 at hval
    omega
  · intro b
    have hbBounds :=
      r322AnalyticProperHead_block_vertex_bounds
        hq κ hκ head tail hschedule hproper b.1 b.2
    let i : Fin (2 * q - 2) :=
      ⟨b.1.val - 1, by omega⟩
    have hidx :
        primitiveInternalIdx q hq i = b.1 := by
      apply Fin.ext
      change i.val + 1 = b.1.val
      dsimp only [i]
      omega
    let selected :
        {i : Fin (2 * q - 2) //
          r322SelectedFinPredicate
            (r322InternalCoordinatesOfBlock
              q hq head.2) i} :=
      ⟨i, by
        exact
          (mem_r322InternalCoordinatesOfBlock
            q hq head.2 i).mpr
            (hidx ▸ b.2)⟩
    refine ⟨selected, ?_⟩
    apply Subtype.ext
    exact hidx

/-- Increasing standard block coordinates are exactly the selected internal
ambient coordinates of a proper analytic head. -/
def r322AnalyticProperHeadSelectedCoordinateEquiv
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    Fin (2 * residualBlockOrder head.2) ≃
      {i : Fin (2 * q - 2) //
        r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} :=
  (residualPrimitiveBlockOrderIso κ head.2
      (extractionBlock_isFullyPairedOn_of_mem
        κ head.2 (by
          apply
            (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mp
          exact
            List.mem_map.mpr
              ⟨head, by
                rw [hschedule]
                simp, rfl⟩))).toEquiv.trans
    (r322AnalyticProperHeadInternalCoordinateEquiv
      hq κ hκ head tail hschedule hproper).symm

@[simp]
theorem r322AnalyticProperHeadSelectedCoordinateEquiv_apply_ambient
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (j : Fin (2 * residualBlockOrder head.2)) :
    primitiveInternalIdx q hq
        (r322AnalyticProperHeadSelectedCoordinateEquiv
          hq κ hκ head tail hschedule hproper j).1 =
      (residualPrimitiveBlockOrderIso κ head.2
        (extractionBlock_isFullyPairedOn_of_mem
          κ head.2 (by
            apply
              (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mp
            exact
              List.mem_map.mpr
                ⟨head, by
                  rw [hschedule]
                  simp, rfl⟩)) j).1 := by
  let hB :
      head.2 ∈ extractionBlocks κ := by
    apply
      (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mp
    exact
      List.mem_map.mpr
        ⟨head, by
          rw [hschedule]
          simp, rfl⟩
  let eB :=
    (residualPrimitiveBlockOrderIso κ head.2
      (extractionBlock_isFullyPairedOn_of_mem
        κ head.2 hB)).toEquiv
  let eI :=
    r322AnalyticProperHeadInternalCoordinateEquiv
      hq κ hκ head tail hschedule hproper
  have happly :
      eI (eI.symm (eB j)) = eB j :=
    eI.apply_symm_apply (eB j)
  have hval :=
    congrArg Subtype.val happly
  change
    primitiveInternalIdx q hq
        (eI.symm (eB j)).1 =
      (eB j).1 at hval
  change
    primitiveInternalIdx q hq
        ((eB.trans eI.symm) j).1 =
      (eB j).1
  simpa only [Equiv.trans_apply] using hval

/-- The endpoint span of the proper analytic head is exactly twice its
residual perturbative order. -/
theorem r322AnalyticProperHead_endpoint_span
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (_hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (_hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    head.1.2.val + 1 - head.1.1.val =
      2 * residualBlockOrder head.2 := by
  let hB : head.2 ∈ extractionBlocks κ := by
    apply
      (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mp
    exact
      List.mem_map.mpr
        ⟨head, by
          rw [hschedule]
          simp, rfl⟩
  have hcard :
      head.2.card =
        2 * residualBlockOrder head.2 :=
    (Nat.two_mul_div_two_of_even
      (residualBlock_card_even κ head.2
        (extractionBlock_isFullyPairedOn_of_mem
          κ head.2 hB))).symm
  calc
    head.1.2.val + 1 - head.1.1.val =
        (Finset.Icc head.1.1 head.1.2).card := by
      rw [Fin.card_Icc]
    _ = head.2.card := by
      rw [r322AnalyticSchedule_head_block_eq_Icc
        κ head tail hschedule]
    _ = 2 * residualBlockOrder head.2 := hcard

/-- The canonical increasing enumeration of the first analytic block is
the literal affine interval enumeration `a + j`. -/
theorem r322AnalyticProperHead_residualOrderIso_apply_val
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (j : Fin (2 * residualBlockOrder head.2)) :
    (residualPrimitiveBlockOrderIso κ head.2
        (extractionBlock_isFullyPairedOn_of_mem
          κ head.2 (by
            apply
              (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mp
            exact
              List.mem_map.mpr
                ⟨head, by
                  rw [hschedule]
                  simp, rfl⟩)) j).1.val =
      head.1.1.val + j.val := by
  let hB : head.2 ∈ extractionBlocks κ := by
    apply
      (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mp
    exact
      List.mem_map.mpr
        ⟨head, by
          rw [hschedule]
          simp, rfl⟩
  let hfull : IsFullyPairedOn κ head.2 :=
    extractionBlock_isFullyPairedOn_of_mem κ head.2 hB
  let hcard :
      head.2.card =
        2 * residualBlockOrder head.2 :=
    (Nat.two_mul_div_two_of_even
      (residualBlock_card_even κ head.2 hfull)).symm
  have hspan :=
    r322AnalyticProperHead_endpoint_span
      hq κ hκ head tail hschedule hproper
  let f :
      Fin (2 * residualBlockOrder head.2) →
        Fin (2 * q) :=
    fun i =>
      ⟨head.1.1.val + i.val, by
        have hi := i.isLt
        have hr := head.1.2.isLt
        omega⟩
  have hfmem :
      ∀ i, f i ∈ head.2 := by
    intro i
    rw [r322AnalyticSchedule_head_block_eq_Icc
      κ head tail hschedule]
    apply Finset.mem_Icc.mpr
    constructor
    · exact Fin.mk_le_mk.mpr (Nat.le_add_right _ _)
    · apply Fin.mk_le_mk.mpr
      have hi := i.isLt
      have haligned :=
        r322AnalyticSchedule_forall_aligned κ head
          (by rw [hschedule]; simp)
      have hleftRight : head.1.1.val ≤ head.1.2.val :=
        (haligned.2.2 head.1.1 haligned.1).2
      have hsuble :
          head.1.1.val ≤ head.1.2.val + 1 := by
        omega
      have heq :
          head.1.2.val + 1 =
            (head.1.2.val + 1 - head.1.1.val) +
              head.1.1.val :=
        (Nat.sub_add_cancel hsuble).symm
      rw [hspan] at heq
      have hsum :
          head.1.1.val +
              2 * residualBlockOrder head.2 =
            head.1.2.val + 1 := by
        rw [Nat.add_comm]
        exact heq.symm
      have hlt :
          head.1.1.val + i.val <
            head.1.2.val + 1 := by
        rw [← hsum]
        exact Nat.add_lt_add_left hi head.1.1.val
      exact Nat.lt_succ_iff.mp
        (by simpa [Nat.succ_eq_add_one] using hlt)
  have hfmono : StrictMono f := by
    intro i k hik
    apply Fin.mk_lt_mk.mpr
    exact Nat.add_lt_add_left hik head.1.1.val
  have henum :
      f =
        head.2.orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard hfmem hfmono
  change
    ((head.2.orderIsoOfFin _ j : head.2).1.val =
      head.1.1.val + j.val)
  rw [Finset.coe_orderIsoOfFin_apply]
  rw [← congrFun henum j]

/-! ## The exact local chain interval -/

/-- An ambient chain edge survives in the touching local product of a
proper analytic head exactly when its left index lies in
`[a - 1, b)`.  In particular the incoming edge is `a - 1`, while the
scheduled right edge `b` is already removed. -/
theorem r322AnalyticProperHead_activeLocalEdge_iff
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (e : Fin (2 * q - 1)) :
    (¬R322ChainEdgeOutside head.2 e ∧
        e.val ∉
          ((r322AnalyticSchedule κ).map
            (fun s => s.1.2.val))) ↔
      head.1.1.val - 1 ≤ e.val ∧
        e.val < head.1.2.val := by
  have hblock :=
    r322AnalyticSchedule_head_block_eq_Icc
      κ head tail hschedule
  have hbounds :=
    r322AnalyticProperHead_endpoint_bounds
      hq κ hκ head tail hschedule hproper
  have hheadMem :
      head ∈ r322AnalyticSchedule κ := by
    rw [hschedule]
    simp
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      κ head hheadMem
  have hab :
      head.1.1.val ≤ head.1.2.val :=
    (haligned.2.2 head.1.1 haligned.1).2
  constructor
  · rintro ⟨hnotOutside, hnotRight⟩
    have htouch :
        r322JChainEdgeLeft e ∈ head.2 ∨
          r322JChainEdgeRight e ∈ head.2 := by
      unfold R322ChainEdgeOutside at hnotOutside
      by_cases hleft :
          r322JChainEdgeLeft e ∈ head.2
      · exact Or.inl hleft
      · right
        by_contra hright
        exact hnotOutside ⟨hleft, hright⟩
    have htouchBounds :
        (head.1.1.val ≤ e.val ∧
            e.val ≤ head.1.2.val) ∨
          (head.1.1.val ≤ e.val + 1 ∧
            e.val + 1 ≤ head.1.2.val) := by
      rcases htouch with hleft | hright
      · left
        rw [hblock] at hleft
        have hb := Finset.mem_Icc.mp hleft
        change
          head.1.1.val ≤ e.val ∧
            e.val ≤ head.1.2.val at hb
        exact hb
      · right
        rw [hblock] at hright
        have hb := Finset.mem_Icc.mp hright
        change
          head.1.1.val ≤ e.val + 1 ∧
            e.val + 1 ≤ head.1.2.val at hb
        exact hb
    have hne :
        e.val ≠ head.1.2.val := by
      intro heq
      apply hnotRight
      rw [hschedule]
      simp [heq]
    omega
  · rintro ⟨hlower, hupper⟩
    constructor
    · unfold R322ChainEdgeOutside
      intro hout
      by_cases hae : head.1.1.val ≤ e.val
      · apply hout.1
        rw [hblock]
        apply Finset.mem_Icc.mpr
        constructor
        · exact Fin.mk_le_mk.mpr hae
        · exact Fin.mk_le_mk.mpr hupper.le
      · apply hout.2
        rw [hblock]
        apply Finset.mem_Icc.mpr
        constructor <;> apply Fin.mk_le_mk.mpr
        · calc
            head.1.1.val =
                head.1.1.val - 1 + 1 := by
              omega
            _ ≤ e.val + 1 :=
              Nat.add_le_add_right hlower 1
        · exact
            (by
              simpa [Nat.succ_eq_add_one] using
                (Nat.succ_le_iff.mpr hupper))
    · rw [hschedule]
      simp only [List.map_cons, List.mem_cons, not_or]
      constructor
      · exact ne_of_lt hupper
      · intro heTail
        obtain ⟨later, hlater, heq⟩ :=
          List.mem_map.mp heTail
        have hright :
            head.1.2 < later.1.2 :=
          (List.pairwise_cons.mp
            (by
              rw [← hschedule]
              exact
                r322AnalyticSchedule_pairwise_right_lt κ)).1
            later hlater
        change later.1.2.val = e.val at heq
        omega

/-- Every displayed analytic head carries a positive primitive order. -/
theorem r322AnalyticHead_one_le_residualBlockOrder
    {q : ℕ}
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail) :
    1 ≤ residualBlockOrder head.2 := by
  let hB : head.2 ∈ extractionBlocks κ := by
    apply
      (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mp
    exact
      List.mem_map.mpr
        ⟨head, by
          rw [hschedule]
          simp, rfl⟩
  exact
    (extractionPrimitiveBlockPartition κ
      (mem_nonSplitPairings.mp hκ).1).one_le_blockOrder hB

/-- The ambient vertex occupied by standard head-block coordinate `j`. -/
def r322AnalyticProperHeadVertex
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (j : Fin (2 * residualBlockOrder head.2)) :
    Fin (2 * q) :=
  ⟨head.1.1.val + j.val, by
    have hj := j.isLt
    have hspan :=
      r322AnalyticProperHead_endpoint_span
        hq κ hκ head tail hschedule hproper
    have haligned :=
      r322AnalyticSchedule_forall_aligned κ head
        (by rw [hschedule]; simp)
    have hab : head.1.1.val ≤ head.1.2.val :=
      (haligned.2.2 head.1.1 haligned.1).2
    have hsuble :
        head.1.1.val ≤ head.1.2.val + 1 := by
      omega
    have heq :
        head.1.2.val + 1 =
          2 * residualBlockOrder head.2 +
            head.1.1.val := by
      rw [← hspan]
      exact (Nat.sub_add_cancel hsuble).symm
    have hr := head.1.2.isLt
    omega⟩

@[simp]
theorem r322AnalyticProperHeadVertex_val
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (j : Fin (2 * residualBlockOrder head.2)) :
    (r322AnalyticProperHeadVertex
      hq κ hκ head tail hschedule hproper j).val =
      head.1.1.val + j.val :=
  rfl

/-- The affine vertex is the existing canonical residual-block
enumeration, not a parallel coordinate convention. -/
theorem r322AnalyticProperHead_residualOrderIso_apply
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (j : Fin (2 * residualBlockOrder head.2)) :
    (residualPrimitiveBlockOrderIso κ head.2
        (extractionBlock_isFullyPairedOn_of_mem
          κ head.2 (by
            apply
              (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mp
            exact
              List.mem_map.mpr
                ⟨head, by
                  rw [hschedule]
                  simp, rfl⟩)) j).1 =
      r322AnalyticProperHeadVertex
        hq κ hκ head tail hschedule hproper j := by
  apply Fin.ext
  exact
    r322AnalyticProperHead_residualOrderIso_apply_val
      hq κ hκ head tail hschedule hproper j

/-- The standard head tuple, read in increasing ambient order. -/
def r322AnalyticProperHeadStandardTuple
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (x : Fin (2 * q) → T4) :
    Fin (2 * residualBlockOrder head.2) → T4 :=
  fun j =>
    x (r322AnalyticProperHeadVertex
      hq κ hκ head tail hschedule hproper j)

/-- The incoming chain slot immediately preceding a proper head. -/
def r322AnalyticProperHeadPredecessorEdge
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    Fin (2 * q - 1) :=
  ⟨head.1.1.val - 1, by
    have hbounds :=
      r322AnalyticProperHead_endpoint_bounds
        hq κ hκ head tail hschedule hproper
    have haligned :=
      r322AnalyticSchedule_forall_aligned κ head
        (by rw [hschedule]; simp)
    have hab : head.1.1.val ≤ head.1.2.val :=
      (haligned.2.2 head.1.1 haligned.1).2
    omega⟩

@[simp]
theorem r322AnalyticProperHeadPredecessorEdge_val
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    (r322AnalyticProperHeadPredecessorEdge
      hq κ hκ head tail hschedule hproper).val =
      head.1.1.val - 1 :=
  rfl

/-- Ambient chain slot of the `j`th internal edge of the proper head. -/
def r322AnalyticProperHeadInternalEdge
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (j : Fin (2 * residualBlockOrder head.2 - 1)) :
    Fin (2 * q - 1) :=
  ⟨head.1.1.val + j.val, by
    have hj := j.isLt
    have hspan :=
      r322AnalyticProperHead_endpoint_span
        hq κ hκ head tail hschedule hproper
    have haligned :=
      r322AnalyticSchedule_forall_aligned κ head
        (by rw [hschedule]; simp)
    have hab : head.1.1.val ≤ head.1.2.val :=
      (haligned.2.2 head.1.1 haligned.1).2
    have hsuble :
        head.1.1.val ≤ head.1.2.val + 1 := by
      omega
    have heq :
        head.1.2.val + 1 =
          2 * residualBlockOrder head.2 +
            head.1.1.val := by
      rw [← hspan]
      exact (Nat.sub_add_cancel hsuble).symm
    have hbounds :=
      r322AnalyticProperHead_endpoint_bounds
        hq κ hκ head tail hschedule hproper
    omega⟩

@[simp]
theorem r322AnalyticProperHeadInternalEdge_val
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (j : Fin (2 * residualBlockOrder head.2 - 1)) :
    (r322AnalyticProperHeadInternalEdge
      hq κ hκ head tail hschedule hproper j).val =
      head.1.1.val + j.val :=
  rfl

/-- The touching analytic chain at a proper head is exactly its incoming
predecessor edge followed by the standard primitive chain on the head
tuple.  This is the structural recognition needed before `detJWith` can be
used; it is false for a sparse block with holes. -/
theorem r322AnalyticProperHeadLocalChainProductWith_eq
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (G : Fin (2 * q - 1) → T4 → ℝ)
    (x : Fin (2 * q) → T4) :
    r322AnalyticHeadLocalChainProductWith
        G κ head x =
      jChainEdgeWith G x
          (r322AnalyticProperHeadPredecessorEdge
            hq κ hκ head tail hschedule hproper) *
        primitiveChainProduct
          (residualBlockOrder head.2)
          (r322AnalyticHead_one_le_residualBlockOrder
            κ hκ head tail hschedule)
          (fun j =>
            G (r322AnalyticProperHeadInternalEdge
              hq κ hκ head tail hschedule hproper j))
          (r322AnalyticProperHeadStandardTuple
            hq κ hκ head tail hschedule hproper x) := by
  classical
  let nB := residualBlockOrder head.2
  have hnB : 1 ≤ nB :=
    r322AnalyticHead_one_le_residualBlockOrder
      κ hκ head tail hschedule
  have hbounds :=
    r322AnalyticProperHead_endpoint_bounds
      hq κ hκ head tail hschedule hproper
  have hspan :=
    r322AnalyticProperHead_endpoint_span
      hq κ hκ head tail hschedule hproper
  have haligned :=
    r322AnalyticSchedule_forall_aligned κ head
      (by rw [hschedule]; simp)
  have hab : head.1.1.val ≤ head.1.2.val :=
    (haligned.2.2 head.1.1 haligned.1).2
  have hsuble :
      head.1.1.val ≤ head.1.2.val + 1 := by
    omega
  have hsum :
      head.1.1.val + 2 * nB =
        head.1.2.val + 1 := by
    rw [Nat.add_comm]
    change
      2 * residualBlockOrder head.2 +
          head.1.1.val =
        head.1.2.val + 1
    rw [← hspan]
    exact Nat.sub_add_cancel hsuble
  let edgeAt :
      Fin ((2 * nB - 1) + 1) → Fin (2 * q - 1) :=
    fun k =>
      ⟨head.1.1.val - 1 + k.val, by
        have hk := k.isLt
        have ha :
            head.1.1.val - 1 + 1 =
              head.1.1.val := by
          omega
        omega⟩
  let active : Fin (2 * q - 1) → Prop :=
    fun e =>
      ¬R322ChainEdgeOutside head.2 e ∧
        e.val ∉
          ((r322AnalyticSchedule κ).map
            (fun s => s.1.2.val))
  have hedgeAtActive :
      ∀ k, active (edgeAt k) := by
    intro k
    apply
      (r322AnalyticProperHead_activeLocalEdge_iff
        hq κ hκ head tail hschedule hproper
        (edgeAt k)).mpr
    constructor
    · change
        head.1.1.val - 1 ≤
          head.1.1.val - 1 + k.val
      exact Nat.le_add_right _ _
    · change
        head.1.1.val - 1 + k.val <
          head.1.2.val
      have hk := k.isLt
      have ha :
          head.1.1.val - 1 + 1 =
            head.1.1.val := by
        omega
      omega
  have hedgeAtInjective : Function.Injective edgeAt := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change
      head.1.1.val - 1 + i.val =
        head.1.1.val - 1 + j.val at hv
    omega
  have hedgeAtSurjective :
      ∀ e ∈ Finset.univ.filter active,
        ∃ k, ∃ (_hk : k ∈
          (Finset.univ :
            Finset (Fin ((2 * nB - 1) + 1)))),
          edgeAt k = e := by
    intro e he
    have heActive : active e :=
      (Finset.mem_filter.mp he).2
    have herange :=
      (r322AnalyticProperHead_activeLocalEdge_iff
        hq κ hκ head tail hschedule hproper e).mp
        heActive
    let k : Fin ((2 * nB - 1) + 1) :=
      ⟨e.val - (head.1.1.val - 1), by
        have ha :
            head.1.1.val - 1 + 1 =
              head.1.1.val := by
          omega
        omega⟩
    refine ⟨k, by simp, ?_⟩
    apply Fin.ext
    change
      head.1.1.val - 1 +
          (e.val - (head.1.1.val - 1)) =
        e.val
    exact Nat.add_sub_of_le herange.1
  have hprodReindex :
      (∏ k : Fin ((2 * nB - 1) + 1),
          jChainEdgeWith G x (edgeAt k)) =
        ∏ e ∈ Finset.univ.filter active,
          jChainEdgeWith G x e := by
    simpa only [Finset.mem_univ, true_implies] using
      (Finset.prod_bij
        (s := (Finset.univ :
          Finset (Fin ((2 * nB - 1) + 1))))
        (t := Finset.univ.filter active)
        (fun k _hk => edgeAt k)
        (fun k _hk =>
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hedgeAtActive k⟩)
        (fun i _hi j _hj hij =>
          hedgeAtInjective hij)
        hedgeAtSurjective
        (fun _k _hk => rfl))
  have hlocalFilter :
      r322AnalyticHeadLocalChainProductWith
          G κ head x =
        ∏ e ∈ Finset.univ.filter active,
          jChainEdgeWith G x e := by
    unfold r322AnalyticHeadLocalChainProductWith
      r322AnalyticChainEdgeFactorWith
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro e _he
    by_cases hout : R322ChainEdgeOutside head.2 e
    · simp [hout]
    · by_cases hright :
          e.val ∈
            ((r322AnalyticSchedule κ).map
              (fun s => s.1.2.val))
      · simp [hout, hright]
      · simp [hout, hright]
  rw [hlocalFilter, ← hprodReindex]
  rw [Fin.prod_univ_succ]
  have hedgeZero :
      edgeAt 0 =
        r322AnalyticProperHeadPredecessorEdge
          hq κ hκ head tail hschedule hproper := by
    apply Fin.ext
    change head.1.1.val - 1 + 0 =
      head.1.1.val - 1
    omega
  rw [hedgeZero]
  congr 1
  unfold primitiveChainProduct
  apply Finset.prod_congr rfl
  intro j _hj
  have hedgeSucc :
      edgeAt j.succ =
        r322AnalyticProperHeadInternalEdge
          hq κ hκ head tail hschedule hproper j := by
    apply Fin.ext
    change
      head.1.1.val - 1 + (j.val + 1) =
        head.1.1.val + j.val
    omega
  rw [hedgeSucc]
  unfold jChainEdgeWith
  apply congrArg
    (G (r322AnalyticProperHeadInternalEdge
      hq κ hκ head tail hschedule hproper j))
  apply congrArg₂ (· - ·)
  · apply congrArg x
    apply Fin.ext
    change
      head.1.1.val + j.val =
        head.1.1.val + j.val
    rfl
  · apply congrArg x
    apply Fin.ext
    change
      head.1.1.val + j.val + 1 =
        head.1.1.val + (j.val + 1)
    omega

/-! ## Recognition of the head covariance coordinate -/

/-- The actual primitive covariance sum assigned to the analytic head is
the standard complete primitive sum evaluated on the standard head tuple. -/
theorem r322AnalyticHeadPrimitiveSum_eq_standardTuple
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (x : Fin (2 * q) → T4) :
    r322ExtractionBlockPrimitiveSum ρ ε κ
        (r322AnalyticHeadBlockIndex κ hschedule) x =
      ∑ σ :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder head.2)) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder head.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder head.2) σ.1
          (r322AnalyticProperHeadStandardTuple
            hq κ hκ head tail hschedule hproper x) := by
  let hB : head.2 ∈ extractionBlocks κ := by
    apply
      (r322AnalyticSchedule_blocks_perm_extractionBlocks κ).mem_iff.mp
    exact
      List.mem_map.mpr
        ⟨head, by
          rw [hschedule]
          simp, rfl⟩
  have hindex :
      r322AnalyticHeadBlockIndex κ hschedule =
        (⟨head.2, hB⟩ : ExtractionBlockIndex κ) := by
    apply Subtype.ext
    exact r322AnalyticHeadBlockIndex_val κ hschedule
  unfold r322ExtractionBlockPrimitiveSum
    extractionBlockPrimitiveCovarianceFactor
  rw [hindex]
  apply Finset.sum_congr rfl
  intro σ _hσ
  apply congrArg
    (primitiveCovarianceProduct ρ ε
      (residualBlockOrder head.2) σ.1)
  funext j
  apply congrArg x
  exact
    r322AnalyticProperHead_residualOrderIso_apply
      hq κ hκ head tail hschedule hproper j

/-! ## Exact standard-block proper collapse -/

/-- A complete standard primitive block, with an incoming endpoint kernel
and the signed outgoing endpoint difference, integrates exactly to the
named predecessor-edge replacement.  Integrability of the internal
primitive section is required only for product-Haar almost every endpoint
pair, which is precisely what joint integrability and Fubini provide. -/
theorem
    lamEps_pow_integral_standardCompletePrimitive_eq_replacementEdge
    {ι : Type*} [DecidableEq ι]
    (edges : ι → T4 → ℝ) (slot : ι)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (Gp Gr : T4 → ℝ) (u : T4)
    (hstandard :
      Integrable
        (fun t : Fin (2 * n) → T4 =>
          Gp (u - t (⟨0, by omega⟩ : Fin (2 * n))) *
            (∑ κB :
                {κ : PartialPairing (Fin (2 * n)) //
                  κ ∈ primitiveFullPairings n},
              detJclosedIntegrandWith
                ρ ε (2 * n) κB.1 G t) *
            (Gr (t (primitiveLast n hn)) -
              Gr (t (⟨0, by omega⟩ : Fin (2 * n)))))
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing (Fin (2 * n)) //
              κ ∈ primitiveFullPairings n},
          Integrable
            (fun v : Fin (2 * n - 2) → T4 =>
              detJclosedIntegrandWith ρ ε (2 * n)
                κB.1 G
                (primitiveAssemble n hn p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    lamEps lam ε ^ (2 * n) *
        (∫ t : Fin (2 * n) → T4,
          Gp (u - t (⟨0, by omega⟩ : Fin (2 * n))) *
            (∑ κB :
                {κ : PartialPairing (Fin (2 * n)) //
                  κ ∈ primitiveFullPairings n},
              detJclosedIntegrandWith
                ρ ε (2 * n) κB.1 G t) *
            (Gr (t (primitiveLast n hn)) -
              Gr (t (⟨0, by omega⟩ : Fin (2 * n))))
          ∂Measure.pi fun _ => paperMeasure) =
      r322ReplaceEdge edges slot Gp
        (primitiveKernelDiff ρ lam ε n hn G)
        Gr slot u := by
  rw [
    integral_standardBlock_eq_integral_endpoints_internal
      n hn _ hstandard,
    ← integral_completePrimitiveAtEndpoints_eq_replacementEdge
      edges slot ρ lam ε n hn G Gp Gr u,
    ← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hinternal] with p hp
  have hinner :
      lamEps lam ε ^ (2 * n) *
          (∫ v : Fin (2 * n - 2) → T4,
            ∑ κB :
                {κ : PartialPairing (Fin (2 * n)) //
                  κ ∈ primitiveFullPairings n},
              detJclosedIntegrandWith ρ ε (2 * n)
                κB.1 G
                (primitiveAssemble n hn p.1 p.2 v)
            ∂Measure.pi fun _ => paperMeasure) =
        ∑ κB :
            {κ : PartialPairing (Fin (2 * n)) //
              κ ∈ primitiveFullPairings n},
          detJWith ρ lam ε n hn G κB.1 p.1 p.2 := by
    calc
      lamEps lam ε ^ (2 * n) *
          (∫ v : Fin (2 * n - 2) → T4,
            ∑ κB :
                {κ : PartialPairing (Fin (2 * n)) //
                  κ ∈ primitiveFullPairings n},
              detJclosedIntegrandWith ρ ε (2 * n)
                κB.1 G
                (primitiveAssemble n hn p.1 p.2 v)
            ∂Measure.pi fun _ => paperMeasure) =
          primitiveKernel ρ lam ε n hn G p.1 p.2 :=
        integral_sum_terminal_detJclosedIntegrandWith_eq_primitiveKernel
          ρ lam ε n hn G p.1 p.2
            hp
      _ =
          ∑ κB :
              {κ : PartialPairing (Fin (2 * n)) //
                κ ∈ primitiveFullPairings n},
            detJWith ρ lam ε n hn G κB.1 p.1 p.2 := by
        rw [← sum_detJWith_primitive_eq_primitiveKernel
          ρ lam ε n hn G p.1 p.2]
        apply Finset.sum_subtype
        intro κ
        rfl
  simp only [primitiveAssemble_zero,
    primitiveAssemble_last]
  rw [MeasureTheory.integral_mul_const,
    MeasureTheory.integral_const_mul]
  calc
    lamEps lam ε ^ (2 * n) *
        (Gp (u - p.1) *
            (∫ v : Fin (2 * n - 2) → T4,
              ∑ κB :
                  {κ : PartialPairing (Fin (2 * n)) //
                    κ ∈ primitiveFullPairings n},
                detJclosedIntegrandWith ρ ε (2 * n)
                  κB.1 G
                  (primitiveAssemble n hn p.1 p.2 v)
              ∂Measure.pi fun _ => paperMeasure) *
          (Gr p.2 - Gr p.1)) =
        Gp (u - p.1) *
          (lamEps lam ε ^ (2 * n) *
            (∫ v : Fin (2 * n - 2) → T4,
              ∑ κB :
                  {κ : PartialPairing (Fin (2 * n)) //
                    κ ∈ primitiveFullPairings n},
                detJclosedIntegrandWith ρ ε (2 * n)
                  κB.1 G
                  (primitiveAssemble n hn p.1 p.2 v)
              ∂Measure.pi fun _ => paperMeasure)) *
          (Gr p.2 - Gr p.1) := by
      ring
    _ = _ := by rw [hinner]

/-! ## The actual selected-coordinate reconstruction -/

/-- Plain-function form of the selected-coordinate reindex. -/
def r322AnalyticProperHeadSelectedTuple
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (t : Fin (2 * residualBlockOrder head.2) → T4) :
    {i : Fin (2 * q - 2) //
      r322SelectedFinPredicate
        (r322InternalCoordinatesOfBlock q hq head.2) i} → T4 :=
  fun i =>
    t ((r322AnalyticProperHeadSelectedCoordinateEquiv
      hq κ hκ head tail hschedule hproper).symm i)

@[simp]
theorem r322AnalyticProperHeadSelectedTuple_apply
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (j : Fin (2 * residualBlockOrder head.2)) :
    r322AnalyticProperHeadSelectedTuple
        hq κ hκ head tail hschedule hproper t
        (r322AnalyticProperHeadSelectedCoordinateEquiv
          hq κ hκ head tail hschedule hproper j) =
      t j := by
  unfold r322AnalyticProperHeadSelectedTuple
  rw [Equiv.symm_apply_apply]

/-- Reconstruct the ambient `detJ` tuple from a standard proper-head tuple
and the fixed complementary internal coordinates. -/
def r322AnalyticProperHeadReconstruct
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4) :
    Fin (2 * q) → T4 :=
  primitiveAssemble q hq z 0
    (r322MergeSelectedFinCoordinates
      (r322InternalCoordinatesOfBlock q hq head.2)
      (r322AnalyticProperHeadSelectedTuple
        hq κ hκ head tail hschedule hproper t)
      vC)

/-- Reading the reconstructed ambient tuple on the head interval returns
the supplied standard head tuple literally. -/
theorem r322AnalyticProperHeadStandardTuple_reconstruct
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4) :
    r322AnalyticProperHeadStandardTuple
        hq κ hκ head tail hschedule hproper
        (r322AnalyticProperHeadReconstruct
          hq κ hκ head tail hschedule hproper z vC t) =
      t := by
  funext j
  unfold r322AnalyticProperHeadStandardTuple
    r322AnalyticProperHeadReconstruct
  have hvertex :
      r322AnalyticProperHeadVertex
          hq κ hκ head tail hschedule hproper j =
        primitiveInternalIdx q hq
          (r322AnalyticProperHeadSelectedCoordinateEquiv
            hq κ hκ head tail hschedule hproper j).1 := by
    have hambient :=
      r322AnalyticProperHeadSelectedCoordinateEquiv_apply_ambient
        hq κ hκ head tail hschedule hproper j
    have hiso :=
      r322AnalyticProperHead_residualOrderIso_apply
        hq κ hκ head tail hschedule hproper j
    rw [hiso] at hambient
    exact hambient.symm
  rw [hvertex, primitiveAssemble_internal]
  rw [r322MergeSelectedFinCoordinates_apply_mem
    _ _ _
    (r322AnalyticProperHeadSelectedCoordinateEquiv
      hq κ hκ head tail hschedule hproper j).1
    (r322AnalyticProperHeadSelectedCoordinateEquiv
      hq κ hκ head tail hschedule hproper j).2]
  exact
    r322AnalyticProperHeadSelectedTuple_apply
      hq κ hκ head tail hschedule hproper t j

/-- Changing the standard head tuple leaves every ambient coordinate
outside the concrete head block unchanged. -/
theorem r322AnalyticProperHeadReconstruct_eq_of_not_mem
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4)
    (s t : Fin (2 * residualBlockOrder head.2) → T4)
    (i : Fin (2 * q)) (hi : i ∉ head.2) :
    r322AnalyticProperHeadReconstruct
        hq κ hκ head tail hschedule hproper z vC s i =
      r322AnalyticProperHeadReconstruct
        hq κ hκ head tail hschedule hproper z vC t i := by
  unfold r322AnalyticProperHeadReconstruct
  by_cases hiZero : i.val = 0
  · have hiEq :
        i = (⟨0, by omega⟩ : Fin (2 * q)) :=
      Fin.ext hiZero
    rw [hiEq, primitiveAssemble_zero,
      primitiveAssemble_zero]
  by_cases hiLast : i.val = 2 * q - 1
  · have hiEq :
        i = primitiveLast q hq := by
      apply Fin.ext
      simpa only [primitiveLast] using hiLast
    rw [hiEq, primitiveAssemble_last,
      primitiveAssemble_last]
  have hiPos : 0 < i.val := by omega
  let j : Fin (2 * q - 2) :=
    ⟨i.val - 1, by
      have hii := i.isLt
      omega⟩
  have hjAmbient :
      primitiveInternalIdx q hq j = i := by
    apply Fin.ext
    change j.val + 1 = i.val
    dsimp only [j]
    omega
  have hjNotSelected :
      j ∉ r322InternalCoordinatesOfBlock
        q hq head.2 := by
    intro hj
    apply hi
    exact hjAmbient ▸
      (mem_r322InternalCoordinatesOfBlock
        q hq head.2 j).mp hj
  have hjNotSelected' :
      ¬r322SelectedFinPredicate
        (r322InternalCoordinatesOfBlock
          q hq head.2) j :=
    hjNotSelected
  rw [← hjAmbient, primitiveAssemble_internal,
    primitiveAssemble_internal]
  rw [
    r322MergeSelectedFinCoordinates_apply_not_mem
      _ _ _ j hjNotSelected',
    r322MergeSelectedFinCoordinates_apply_not_mem
      _ _ _ j hjNotSelected']

/-! ## Proper-head endpoint geometry in reconstructed coordinates -/

/-- The first standard head vertex is the selected left endpoint. -/
theorem r322AnalyticProperHeadVertex_zero
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    r322AnalyticProperHeadVertex
        hq κ hκ head tail hschedule hproper
        (⟨0, by
          have hn :=
            r322AnalyticHead_one_le_residualBlockOrder
              κ hκ head tail hschedule
          omega⟩) =
      head.1.1 := by
  apply Fin.ext
  simp

/-- The last standard head vertex is the selected right endpoint. -/
theorem r322AnalyticProperHeadVertex_last
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    r322AnalyticProperHeadVertex
        hq κ hκ head tail hschedule hproper
        (primitiveLast
          (residualBlockOrder head.2)
          (r322AnalyticHead_one_le_residualBlockOrder
            κ hκ head tail hschedule)) =
      head.1.2 := by
  apply Fin.ext
  have hspan :=
    r322AnalyticProperHead_endpoint_span
      hq κ hκ head tail hschedule hproper
  have haligned :=
    r322AnalyticSchedule_forall_aligned κ head
      (by rw [hschedule]; simp)
  have hab : head.1.1.val ≤ head.1.2.val :=
    (haligned.2.2 head.1.1 haligned.1).2
  have hsuble :
      head.1.1.val ≤ head.1.2.val + 1 := by
    omega
  have heq :
      head.1.2.val + 1 =
        2 * residualBlockOrder head.2 +
          head.1.1.val := by
    rw [← hspan]
    exact (Nat.sub_add_cancel hsuble).symm
  change
    head.1.1.val +
        (2 * residualBlockOrder head.2 - 1) =
      head.1.2.val
  have hn :=
    r322AnalyticHead_one_le_residualBlockOrder
      κ hκ head tail hschedule
  omega

/-- Ambient vertex immediately to the right of a proper head. -/
def r322AnalyticProperHeadSuccessorVertex
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    Fin (2 * q) :=
  ⟨head.1.2.val + 1, by
    have hbounds :=
      r322AnalyticProperHead_endpoint_bounds
        hq κ hκ head tail hschedule hproper
    omega⟩

/-- The predecessor edge enters the head at its left endpoint. -/
theorem r322AnalyticProperHeadPredecessorEdge_right
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    r322JChainEdgeRight
        (r322AnalyticProperHeadPredecessorEdge
          hq κ hκ head tail hschedule hproper) =
      head.1.1 := by
  apply Fin.ext
  change head.1.1.val - 1 + 1 =
    head.1.1.val
  have hbounds :=
    r322AnalyticProperHead_endpoint_bounds
      hq κ hκ head tail hschedule hproper
  omega

/-- The predecessor coordinate is outside the head block. -/
theorem r322AnalyticProperHeadPredecessorVertex_not_mem
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    r322JChainEdgeLeft
        (r322AnalyticProperHeadPredecessorEdge
          hq κ hκ head tail hschedule hproper) ∉
      head.2 := by
  rw [r322AnalyticSchedule_head_block_eq_Icc
    κ head tail hschedule]
  intro hmem
  have hleft := (Finset.mem_Icc.mp hmem).1
  change
    head.1.1.val ≤ head.1.1.val - 1 at hleft
  have hbounds :=
    r322AnalyticProperHead_endpoint_bounds
      hq κ hκ head tail hschedule hproper
  omega

/-- The successor coordinate is outside the head block. -/
theorem r322AnalyticProperHeadSuccessorVertex_not_mem
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    r322AnalyticProperHeadSuccessorVertex
        hq κ hκ head tail hschedule hproper ∉
      head.2 := by
  rw [r322AnalyticSchedule_head_block_eq_Icc
    κ head tail hschedule]
  intro hmem
  have hright := (Finset.mem_Icc.mp hmem).2
  change
    head.1.2.val + 1 ≤ head.1.2.val at hright
  omega

/-- Fixed complementary reference tuple used to name the predecessor and
successor values during the head integration. -/
def r322AnalyticProperHeadReferenceTuple
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4) :
    Fin (2 * q) → T4 :=
  r322AnalyticProperHeadReconstruct
    hq κ hκ head tail hschedule hproper z vC
    (fun _ => 0)

/-- Fixed predecessor coordinate feeding the proper head. -/
def r322AnalyticProperHeadPredecessorPoint
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4) :
    T4 :=
  r322AnalyticProperHeadReferenceTuple
      hq κ hκ head tail hschedule hproper z vC
    (r322JChainEdgeLeft
      (r322AnalyticProperHeadPredecessorEdge
        hq κ hκ head tail hschedule hproper))

/-- Fixed successor coordinate used by the signed outgoing difference. -/
def r322AnalyticProperHeadSuccessorPoint
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4) :
    T4 :=
  r322AnalyticProperHeadReferenceTuple
      hq κ hκ head tail hschedule hproper z vC
    (r322AnalyticProperHeadSuccessorVertex
      hq κ hκ head tail hschedule hproper)

/-- Outgoing endpoint kernel with the fixed successor coordinate inserted. -/
def r322AnalyticProperHeadOutgoingKernel
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4) :
    T4 → ℝ :=
  fun y =>
    greenFn
      (y - r322AnalyticProperHeadSuccessorPoint
        hq κ hκ head tail hschedule hproper z vC)

/-- The actual local endpoint-fibre factor on reconstructed selected
coordinates is the complete standard primitive-collapse integrand. -/
theorem r322AnalyticHeadLocalIntegrandFactor_reconstruct_eq_standard
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4) :
    r322AnalyticHeadLocalIntegrandFactor
        ρ ε κ head tail hschedule
        (r322AnalyticProperHeadReconstruct
          hq κ hκ head tail hschedule hproper z vC t) =
      greenFn
          (r322AnalyticProperHeadPredecessorPoint
              hq κ hκ head tail hschedule hproper z vC -
            t (⟨0, by
              have hn :=
                r322AnalyticHead_one_le_residualBlockOrder
                  κ hκ head tail hschedule
              omega⟩)) *
        (∑ κB :
            {σ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              σ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          detJclosedIntegrandWith ρ ε
            (2 * residualBlockOrder head.2) κB.1
            (fun _ => greenFn) t) *
        (r322AnalyticProperHeadOutgoingKernel
              hq κ hκ head tail hschedule hproper z vC
              (t (primitiveLast
                (residualBlockOrder head.2)
                (r322AnalyticHead_one_le_residualBlockOrder
                  κ hκ head tail hschedule))) -
          r322AnalyticProperHeadOutgoingKernel
              hq κ hκ head tail hschedule hproper z vC
              (t (⟨0, by
                have hn :=
                  r322AnalyticHead_one_le_residualBlockOrder
                    κ hκ head tail hschedule
                omega⟩))) := by
  let nB := residualBlockOrder head.2
  have hnB : 1 ≤ nB :=
    r322AnalyticHead_one_le_residualBlockOrder
      κ hκ head tail hschedule
  let x :=
    r322AnalyticProperHeadReconstruct
      hq κ hκ head tail hschedule hproper z vC t
  let xRef :=
    r322AnalyticProperHeadReferenceTuple
      hq κ hκ head tail hschedule hproper z vC
  let pred :=
    r322AnalyticProperHeadPredecessorEdge
      hq κ hκ head tail hschedule hproper
  let succ :=
    r322AnalyticProperHeadSuccessorVertex
      hq κ hκ head tail hschedule hproper
  have htuple :
      r322AnalyticProperHeadStandardTuple
          hq κ hκ head tail hschedule hproper x =
        t :=
    r322AnalyticProperHeadStandardTuple_reconstruct
      hq κ hκ head tail hschedule hproper z vC t
  have hleft :
      x head.1.1 = t (⟨0, by omega⟩ : Fin (2 * nB)) := by
    have h := congrFun htuple
      (⟨0, by omega⟩ : Fin (2 * nB))
    change
      x (r322AnalyticProperHeadVertex
        hq κ hκ head tail hschedule hproper
        (⟨0, by omega⟩ : Fin (2 * nB))) =
        t (⟨0, by omega⟩ : Fin (2 * nB)) at h
    rw [r322AnalyticProperHeadVertex_zero
      hq κ hκ head tail hschedule hproper] at h
    exact h
  have hright :
      x head.1.2 =
        t (primitiveLast nB hnB) := by
    have h := congrFun htuple
      (primitiveLast nB hnB)
    change
      x (r322AnalyticProperHeadVertex
        hq κ hκ head tail hschedule hproper
        (primitiveLast nB hnB)) =
        t (primitiveLast nB hnB) at h
    rw [r322AnalyticProperHeadVertex_last
      hq κ hκ head tail hschedule hproper] at h
    exact h
  have hpred :
      x (r322JChainEdgeLeft pred) =
        xRef (r322JChainEdgeLeft pred) := by
    exact
      r322AnalyticProperHeadReconstruct_eq_of_not_mem
        hq κ hκ head tail hschedule hproper z vC
        t (fun _ => 0)
        (r322JChainEdgeLeft pred)
        (r322AnalyticProperHeadPredecessorVertex_not_mem
          hq κ hκ head tail hschedule hproper)
  have hsucc :
      x succ = xRef succ := by
    exact
      r322AnalyticProperHeadReconstruct_eq_of_not_mem
        hq κ hκ head tail hschedule hproper z vC
        t (fun _ => 0) succ
        (r322AnalyticProperHeadSuccessorVertex_not_mem
          hq κ hκ head tail hschedule hproper)
  have hincoming :
      jChainEdgeWith
          (fun _ : Fin (2 * q - 1) => greenFn) x pred =
        greenFn
          (xRef (r322JChainEdgeLeft pred) -
            t (⟨0, by omega⟩ : Fin (2 * nB))) := by
    unfold jChainEdgeWith
    change
      greenFn
          (x (r322JChainEdgeLeft pred) -
            x (r322JChainEdgeRight pred)) =
        greenFn
          (xRef (r322JChainEdgeLeft pred) -
            t (⟨0, by omega⟩ : Fin (2 * nB)))
    rw [hpred,
      r322AnalyticProperHeadPredecessorEdge_right
        hq κ hκ head tail hschedule hproper,
      hleft]
  have hguard : head.1.2.val + 1 < 2 * q := by
    have hb :=
      r322AnalyticProperHead_endpoint_bounds
        hq κ hκ head tail hschedule hproper
    omega
  have haligned :=
    r322AnalyticSchedule_forall_aligned κ head
      (by rw [hschedule]; simp)
  have hdiffRaw :=
    (r322AnalyticHead_diffFactorJWith_eq
      (fun _ : Fin (2 * q - 1) => greenFn)
      x head haligned hguard).2
  have hdiff :
      diffFactorJWith
          (fun _ : Fin (2 * q - 1) => greenFn)
          x head.1 =
        (r322AnalyticProperHeadOutgoingKernel
            hq κ hκ head tail hschedule hproper z vC
            (t (primitiveLast nB hnB)) -
          r322AnalyticProperHeadOutgoingKernel
            hq κ hκ head tail hschedule hproper z vC
            (t (⟨0, by omega⟩ : Fin (2 * nB)))) := by
    rw [hdiffRaw, hright, hleft]
    unfold r322AnalyticProperHeadOutgoingKernel
      r322AnalyticProperHeadSuccessorPoint
    change
      greenFn (t (primitiveLast nB hnB) - x succ) -
          greenFn
            (t (⟨0, by omega⟩ : Fin (2 * nB)) - x succ) =
        greenFn (t (primitiveLast nB hnB) - xRef succ) -
          greenFn
            (t (⟨0, by omega⟩ : Fin (2 * nB)) -
              xRef succ)
    rw [hsucc]
  have hchain :=
    r322AnalyticProperHeadLocalChainProductWith_eq
      hq κ hκ head tail hschedule hproper
      (fun _ : Fin (2 * q - 1) => greenFn) x
  rw [htuple] at hchain
  have hcov :=
    r322AnalyticHeadPrimitiveSum_eq_standardTuple
      hq ρ ε κ hκ head tail hschedule hproper x
  rw [htuple] at hcov
  have hclosed :
      primitiveChainProduct nB hnB
          (fun _ : Fin (2 * nB - 1) => greenFn) t *
          (∑ κB :
              {σ : PartialPairing (Fin (2 * nB)) //
                σ ∈ primitiveFullPairings nB},
            primitiveCovarianceProduct ρ ε nB κB.1 t) =
        ∑ κB :
            {σ : PartialPairing (Fin (2 * nB)) //
              σ ∈ primitiveFullPairings nB},
          detJclosedIntegrandWith ρ ε (2 * nB)
            κB.1 (fun _ => greenFn) t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro κB _hκB
    obtain ⟨hfull, hprimitive⟩ :=
      mem_primitiveFullPairings.mp κB.2
    rw [detJclosedIntegrandWith_eq_primitiveIntegrand_of_full_primitive
      ρ ε nB hnB (fun _ => greenFn)
      κB.1 hfull hprimitive t]
    rfl
  unfold r322AnalyticHeadLocalIntegrandFactor
    r322AnalyticHeadLocalFactorWith
  rw [hchain, hincoming, hdiff, hcov]
  change
    greenFn
          (xRef (r322JChainEdgeLeft pred) -
            t (⟨0, by omega⟩ : Fin (2 * nB))) *
        primitiveChainProduct nB hnB
          (fun _ : Fin (2 * nB - 1) => greenFn) t *
        (r322AnalyticProperHeadOutgoingKernel
              hq κ hκ head tail hschedule hproper z vC
              (t (primitiveLast nB hnB)) -
          r322AnalyticProperHeadOutgoingKernel
              hq κ hκ head tail hschedule hproper z vC
              (t (⟨0, by omega⟩ : Fin (2 * nB)))) *
        (∑ κB :
            {σ : PartialPairing (Fin (2 * nB)) //
              σ ∈ primitiveFullPairings nB},
          primitiveCovarianceProduct ρ ε nB κB.1 t) =
      (greenFn
            (xRef (r322JChainEdgeLeft pred) -
              t (⟨0, by omega⟩ : Fin (2 * nB))) *
          (∑ κB :
              {σ : PartialPairing (Fin (2 * nB)) //
                σ ∈ primitiveFullPairings nB},
            detJclosedIntegrandWith ρ ε (2 * nB)
              κB.1 (fun _ => greenFn) t)) *
        (r322AnalyticProperHeadOutgoingKernel
              hq κ hκ head tail hschedule hproper z vC
              (t (primitiveLast nB hnB)) -
          r322AnalyticProperHeadOutgoingKernel
              hq κ hκ head tail hschedule hproper z vC
              (t (⟨0, by omega⟩ : Fin (2 * nB))))
  calc
    greenFn
          (xRef (r322JChainEdgeLeft pred) -
            t (⟨0, by omega⟩ : Fin (2 * nB))) *
        primitiveChainProduct nB hnB
          (fun _ : Fin (2 * nB - 1) => greenFn) t *
        (r322AnalyticProperHeadOutgoingKernel
              hq κ hκ head tail hschedule hproper z vC
              (t (primitiveLast nB hnB)) -
          r322AnalyticProperHeadOutgoingKernel
              hq κ hκ head tail hschedule hproper z vC
              (t (⟨0, by omega⟩ : Fin (2 * nB)))) *
        (∑ κB :
            {σ : PartialPairing (Fin (2 * nB)) //
              σ ∈ primitiveFullPairings nB},
          primitiveCovarianceProduct ρ ε nB κB.1 t) =
      greenFn
          (xRef (r322JChainEdgeLeft pred) -
            t (⟨0, by omega⟩ : Fin (2 * nB))) *
        (primitiveChainProduct nB hnB
            (fun _ : Fin (2 * nB - 1) => greenFn) t *
          (∑ κB :
              {σ : PartialPairing (Fin (2 * nB)) //
                σ ∈ primitiveFullPairings nB},
            primitiveCovarianceProduct ρ ε nB κB.1 t)) *
        (r322AnalyticProperHeadOutgoingKernel
              hq κ hκ head tail hschedule hproper z vC
              (t (primitiveLast nB hnB)) -
          r322AnalyticProperHeadOutgoingKernel
              hq κ hκ head tail hschedule hproper z vC
              (t (⟨0, by omega⟩ : Fin (2 * nB)))) := by
      ring
    _ = _ := by rw [hclosed]

/-! ## Measure-preserving selected-tuple reindex -/

/-- Reindex the selected ambient internal coordinates by the increasing
standard coordinates of the head block. -/
def r322AnalyticProperHeadSelectedTupleMeasurableEquiv
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    (Fin (2 * residualBlockOrder head.2) → T4) ≃ᵐ
      ((i : {i : Fin (2 * q - 2) //
        r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i}) → T4) :=
  MeasurableEquiv.piCongrLeft
    (fun _ :
      {i : Fin (2 * q - 2) //
        r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} => T4)
    (r322AnalyticProperHeadSelectedCoordinateEquiv
      hq κ hκ head tail hschedule hproper)

@[simp]
theorem r322AnalyticProperHeadSelectedTupleMeasurableEquiv_apply
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (u : Fin (2 * residualBlockOrder head.2) → T4)
    (j : Fin (2 * residualBlockOrder head.2)) :
    r322AnalyticProperHeadSelectedTupleMeasurableEquiv
        hq κ hκ head tail hschedule hproper u
        (r322AnalyticProperHeadSelectedCoordinateEquiv
          hq κ hκ head tail hschedule hproper j) =
      u j := by
  exact
    MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ :
        {i : Fin (2 * q - 2) //
          r322SelectedFinPredicate
            (r322InternalCoordinatesOfBlock
              q hq head.2) i} => T4)
      (r322AnalyticProperHeadSelectedCoordinateEquiv
        hq κ hκ head tail hschedule hproper)
      u j

/-- The selected-tuple reindex preserves the exact paper product measure. -/
theorem
    measurePreserving_r322AnalyticProperHeadSelectedTupleMeasurableEquiv
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq) :
    MeasurePreserving
      (r322AnalyticProperHeadSelectedTupleMeasurableEquiv
        hq κ hκ head tail hschedule hproper)
      (Measure.pi fun _ :
        Fin (2 * residualBlockOrder head.2) =>
          paperMeasure)
      (Measure.pi fun _ :
        {i : Fin (2 * q - 2) //
          r322SelectedFinPredicate
            (r322InternalCoordinatesOfBlock
              q hq head.2) i} =>
          paperMeasure) := by
  simpa only [
    r322AnalyticProperHeadSelectedTupleMeasurableEquiv] using
      (measurePreserving_piCongrLeft
        (fun _ :
          {i : Fin (2 * q - 2) //
            r322SelectedFinPredicate
              (r322InternalCoordinatesOfBlock
                q hq head.2) i} =>
          paperMeasure)
        (r322AnalyticProperHeadSelectedCoordinateEquiv
          hq κ hκ head tail hschedule hproper))

/-- Exact Bochner integral reindex from the selected ambient tuple to the
standard increasing head-block tuple. -/
theorem integral_r322AnalyticProperHeadSelected_eq_standardBlock
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (f :
      ((i : {i : Fin (2 * q - 2) //
        r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i}) → T4) → E) :
    (∫ vB, f vB
        ∂Measure.pi fun _ :
          {i : Fin (2 * q - 2) //
            r322SelectedFinPredicate
              (r322InternalCoordinatesOfBlock
                q hq head.2) i} =>
          paperMeasure) =
      ∫ u : Fin (2 * residualBlockOrder head.2) → T4,
        f
          (r322AnalyticProperHeadSelectedTupleMeasurableEquiv
            hq κ hκ head tail hschedule hproper u)
        ∂Measure.pi fun _ => paperMeasure := by
  exact
    (measurePreserving_r322AnalyticProperHeadSelectedTupleMeasurableEquiv
      hq κ hκ head tail hschedule hproper).integral_comp' f |>.symm

/-! ## Actual proper-head integral collapse -/

/-- The measurable selected-tuple reindex has the same underlying function
as the explicit reconstruction reindex used above. -/
theorem r322AnalyticProperHeadSelectedTupleMeasurableEquiv_eq_plain
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (t : Fin (2 * residualBlockOrder head.2) → T4) :
    r322AnalyticProperHeadSelectedTupleMeasurableEquiv
        hq κ hκ head tail hschedule hproper t =
      r322AnalyticProperHeadSelectedTuple
        hq κ hκ head tail hschedule hproper t := by
  funext i
  obtain ⟨j, rfl⟩ :=
    (r322AnalyticProperHeadSelectedCoordinateEquiv
      hq κ hκ head tail hschedule hproper).surjective i
  rw [
    r322AnalyticProperHeadSelectedTupleMeasurableEquiv_apply,
    r322AnalyticProperHeadSelectedTuple_apply]

/-- Standard closed-integrand form of the actual proper head. -/
def r322AnalyticProperHeadStandardClosedIntegrand
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4) :
    ℝ :=
  greenFn
      (r322AnalyticProperHeadPredecessorPoint
          hq κ hκ head tail hschedule hproper z vC -
        t (⟨0, by
          have hn :=
            r322AnalyticHead_one_le_residualBlockOrder
              κ hκ head tail hschedule
          omega⟩)) *
    (∑ κB :
        {σ : PartialPairing
            (Fin (2 * residualBlockOrder head.2)) //
          σ ∈ primitiveFullPairings
            (residualBlockOrder head.2)},
      detJclosedIntegrandWith ρ ε
        (2 * residualBlockOrder head.2) κB.1
        (fun _ => greenFn) t) *
    (r322AnalyticProperHeadOutgoingKernel
          hq κ hκ head tail hschedule hproper z vC
          (t (primitiveLast
            (residualBlockOrder head.2)
            (r322AnalyticHead_one_le_residualBlockOrder
              κ hκ head tail hschedule))) -
      r322AnalyticProperHeadOutgoingKernel
          hq κ hκ head tail hschedule hproper z vC
          (t (⟨0, by
            have hn :=
              r322AnalyticHead_one_le_residualBlockOrder
                κ hκ head tail hschedule
            omega⟩)))

/-- Pointwise recognition packaged only as a definitional abbreviation. -/
theorem r322AnalyticHeadLocalIntegrandFactor_reconstruct_eq_closed
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4) :
    r322AnalyticHeadLocalIntegrandFactor
        ρ ε κ head tail hschedule
        (r322AnalyticProperHeadReconstruct
          hq κ hκ head tail hschedule hproper z vC t) =
      r322AnalyticProperHeadStandardClosedIntegrand
        hq ρ ε κ hκ head tail hschedule hproper z vC t := by
  exact
    r322AnalyticHeadLocalIntegrandFactor_reconstruct_eq_standard
      hq ρ ε κ hκ head tail hschedule hproper z vC t

/-- Integrating the actual local proper-head factor writes the collapsed
kernel into the predecessor slot `a - 1`. -/
theorem
    lamEps_pow_integral_r322AnalyticProperHeadLocal_eq_replacementEdge
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4)
    (hstandard :
      Integrable
        (r322AnalyticProperHeadStandardClosedIntegrand
          hq ρ ε κ hκ head tail hschedule hproper z vC)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {σ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              σ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder head.2) κB.1
                (fun _ => greenFn)
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (r322AnalyticHead_one_le_residualBlockOrder
                    κ hκ head tail hschedule)
                  p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    lamEps lam ε ^
          (2 * residualBlockOrder head.2) *
        (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
          r322AnalyticHeadLocalIntegrandFactor
            ρ ε κ head tail hschedule
            (r322AnalyticProperHeadReconstruct
              hq κ hκ head tail hschedule hproper z vC t)
          ∂Measure.pi fun _ => paperMeasure) =
      r322ReplaceEdge
        (fun _ : Fin (2 * q - 1) => greenFn)
        (r322AnalyticProperHeadPredecessorEdge
          hq κ hκ head tail hschedule hproper)
        greenFn
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder head.2)
          (r322AnalyticHead_one_le_residualBlockOrder
            κ hκ head tail hschedule)
          (fun _ => greenFn))
        (r322AnalyticProperHeadOutgoingKernel
          hq κ hκ head tail hschedule hproper z vC)
        (r322AnalyticProperHeadPredecessorEdge
          hq κ hκ head tail hschedule hproper)
        (r322AnalyticProperHeadPredecessorPoint
          hq κ hκ head tail hschedule hproper z vC) := by
  let nB := residualBlockOrder head.2
  have hnB : 1 ≤ nB :=
    r322AnalyticHead_one_le_residualBlockOrder
      κ hκ head tail hschedule
  calc
    lamEps lam ε ^ (2 * nB) *
        (∫ t : Fin (2 * nB) → T4,
          r322AnalyticHeadLocalIntegrandFactor
            ρ ε κ head tail hschedule
            (r322AnalyticProperHeadReconstruct
              hq κ hκ head tail hschedule hproper z vC t)
          ∂Measure.pi fun _ => paperMeasure) =
      lamEps lam ε ^ (2 * nB) *
        (∫ t : Fin (2 * nB) → T4,
          r322AnalyticProperHeadStandardClosedIntegrand
            hq ρ ε κ hκ head tail hschedule hproper z vC t
          ∂Measure.pi fun _ => paperMeasure) := by
      apply congrArg
        (fun a : ℝ => lamEps lam ε ^ (2 * nB) * a)
      apply integral_congr_ae
      filter_upwards with t
      exact
        r322AnalyticHeadLocalIntegrandFactor_reconstruct_eq_closed
          hq ρ ε κ hκ head tail hschedule hproper z vC t
    _ = _ := by
      simpa only [
        r322AnalyticProperHeadStandardClosedIntegrand] using
        (lamEps_pow_integral_standardCompletePrimitive_eq_replacementEdge
          (fun _ : Fin (2 * q - 1) => greenFn)
          (r322AnalyticProperHeadPredecessorEdge
            hq κ hκ head tail hschedule hproper)
          ρ lam ε nB hnB
          (fun _ : Fin (2 * nB - 1) => greenFn)
          greenFn
          (r322AnalyticProperHeadOutgoingKernel
            hq κ hκ head tail hschedule hproper z vC)
          (r322AnalyticProperHeadPredecessorPoint
            hq κ hκ head tail hschedule hproper z vC)
          hstandard hinternal)

/-- Selected-coordinate form consumed directly by the spatial Fubini
identity for `endpointFiberDetJSum`. -/
theorem
    lamEps_pow_integral_r322AnalyticProperHeadSelected_eq_replacementEdge
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4)
    (hstandard :
      Integrable
        (r322AnalyticProperHeadStandardClosedIntegrand
          hq ρ ε κ hκ head tail hschedule hproper z vC)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {σ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              σ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder head.2) κB.1
                (fun _ => greenFn)
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (r322AnalyticHead_one_le_residualBlockOrder
                    κ hκ head tail hschedule)
                  p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    lamEps lam ε ^
          (2 * residualBlockOrder head.2) *
        (∫ vB :
            {i : Fin (2 * q - 2) //
              r322SelectedFinPredicate
                (r322InternalCoordinatesOfBlock
                  q hq head.2) i} → T4,
          r322AnalyticHeadLocalIntegrandFactor
            ρ ε κ head tail hschedule
            (primitiveAssemble q hq z 0
              (r322MergeSelectedFinCoordinates
                (r322InternalCoordinatesOfBlock
                  q hq head.2)
                vB vC))
          ∂Measure.pi fun _ => paperMeasure) =
      r322ReplaceEdge
        (fun _ : Fin (2 * q - 1) => greenFn)
        (r322AnalyticProperHeadPredecessorEdge
          hq κ hκ head tail hschedule hproper)
        greenFn
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder head.2)
          (r322AnalyticHead_one_le_residualBlockOrder
            κ hκ head tail hschedule)
          (fun _ => greenFn))
        (r322AnalyticProperHeadOutgoingKernel
          hq κ hκ head tail hschedule hproper z vC)
        (r322AnalyticProperHeadPredecessorEdge
          hq κ hκ head tail hschedule hproper)
        (r322AnalyticProperHeadPredecessorPoint
          hq κ hκ head tail hschedule hproper z vC) := by
  rw [integral_r322AnalyticProperHeadSelected_eq_standardBlock
    hq κ hκ head tail hschedule hproper]
  simp_rw [
    r322AnalyticProperHeadSelectedTupleMeasurableEquiv_eq_plain
      hq κ hκ head tail hschedule hproper]
  exact
    lamEps_pow_integral_r322AnalyticProperHeadLocal_eq_replacementEdge
      hq ρ lam ε κ hκ head tail hschedule hproper z vC
      hstandard hinternal

/-- Standard-coordinate inner integral of the **actual endpoint-fibre
sum**: one proper head is replaced at slot `a - 1`, and the complete outer
factor is left unchanged. -/
theorem
    lamEps_pow_integral_sum_endpointFiber_detJintegrand_properHead_eq
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4)
    (hstandard :
      Integrable
        (r322AnalyticProperHeadStandardClosedIntegrand
          hq ρ ε κ hκ head tail hschedule hproper z vC)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {σ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              σ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder head.2) κB.1
                (fun _ => greenFn)
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (r322AnalyticHead_one_le_residualBlockOrder
                    κ hκ head tail hschedule)
                  p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    lamEps lam ε ^
          (2 * residualBlockOrder head.2) *
        (∫ t : Fin (2 * residualBlockOrder head.2) → T4,
          ∑ τ : ReductionEndpointFiberAt κ,
            detJintegrand ρ ε q τ.1
              (r322AnalyticProperHeadReconstruct
                hq κ hκ head tail hschedule hproper z vC t)
          ∂Measure.pi fun _ => paperMeasure) =
      r322ReplaceEdge
          (fun _ : Fin (2 * q - 1) => greenFn)
          (r322AnalyticProperHeadPredecessorEdge
            hq κ hκ head tail hschedule hproper)
          greenFn
          (primitiveKernelDiff ρ lam ε
            (residualBlockOrder head.2)
            (r322AnalyticHead_one_le_residualBlockOrder
              κ hκ head tail hschedule)
            (fun _ => greenFn))
          (r322AnalyticProperHeadOutgoingKernel
            hq κ hκ head tail hschedule hproper z vC)
          (r322AnalyticProperHeadPredecessorEdge
            hq κ hκ head tail hschedule hproper)
          (r322AnalyticProperHeadPredecessorPoint
            hq κ hκ head tail hschedule hproper z vC) *
        r322AnalyticHeadOuterIntegrandFactor
          ρ ε κ head tail hschedule
          (r322AnalyticProperHeadReferenceTuple
            hq κ hκ head tail hschedule hproper z vC) := by
  let nB := residualBlockOrder head.2
  let xRef :=
    r322AnalyticProperHeadReferenceTuple
      hq κ hκ head tail hschedule hproper z vC
  let outer :=
    r322AnalyticHeadOuterIntegrandFactor
      ρ ε κ head tail hschedule xRef
  have hpoint :
      ∀ t : Fin (2 * nB) → T4,
        (∑ τ : ReductionEndpointFiberAt κ,
            detJintegrand ρ ε q τ.1
              (r322AnalyticProperHeadReconstruct
                hq κ hκ head tail hschedule hproper z vC t)) =
          r322AnalyticHeadLocalIntegrandFactor
              ρ ε κ head tail hschedule
              (r322AnalyticProperHeadReconstruct
                hq κ hκ head tail hschedule hproper z vC t) *
            outer := by
    intro t
    let x :=
      r322AnalyticProperHeadReconstruct
        hq κ hκ head tail hschedule hproper z vC t
    rw [
      sum_endpointFiber_detJintegrand_eq_analyticHead_mul_outer
        ρ ε κ (mem_nonSplitPairings.mp hκ).1
        head tail hschedule x]
    apply congrArg
      (fun a : ℝ =>
        r322AnalyticHeadLocalIntegrandFactor
          ρ ε κ head tail hschedule x * a)
    exact
      r322AnalyticHeadOuterIntegrandFactor_eq
        ρ ε κ x xRef head tail hschedule
        (fun i hi =>
          r322AnalyticProperHeadReconstruct_eq_of_not_mem
            hq κ hκ head tail hschedule hproper z vC
            t (fun _ => 0) i hi)
  have hlocal :=
    lamEps_pow_integral_r322AnalyticProperHeadLocal_eq_replacementEdge
      hq ρ lam ε κ hκ head tail hschedule hproper z vC
      hstandard hinternal
  calc
    lamEps lam ε ^ (2 * nB) *
        (∫ t : Fin (2 * nB) → T4,
          ∑ τ : ReductionEndpointFiberAt κ,
            detJintegrand ρ ε q τ.1
              (r322AnalyticProperHeadReconstruct
                hq κ hκ head tail hschedule hproper z vC t)
          ∂Measure.pi fun _ => paperMeasure) =
      lamEps lam ε ^ (2 * nB) *
        (∫ t : Fin (2 * nB) → T4,
          r322AnalyticHeadLocalIntegrandFactor
              ρ ε κ head tail hschedule
              (r322AnalyticProperHeadReconstruct
                hq κ hκ head tail hschedule hproper z vC t) *
            outer
          ∂Measure.pi fun _ => paperMeasure) := by
      apply congrArg
        (fun a : ℝ => lamEps lam ε ^ (2 * nB) * a)
      apply integral_congr_ae
      filter_upwards with t
      exact hpoint t
    _ =
      (lamEps lam ε ^ (2 * nB) *
        (∫ t : Fin (2 * nB) → T4,
          r322AnalyticHeadLocalIntegrandFactor
            ρ ε κ head tail hschedule
            (r322AnalyticProperHeadReconstruct
              hq κ hκ head tail hschedule hproper z vC t)
          ∂Measure.pi fun _ => paperMeasure)) *
        outer := by
      rw [MeasureTheory.integral_mul_const]
      ring
    _ = _ := by rw [hlocal]

/-- Selected-coordinate version of the actual endpoint-fibre proper-head
collapse, matching the inner integral produced by
`endpointFiberDetJSum_eq_analyticStepSpatialFubini`. -/
theorem
    lamEps_pow_integral_selected_sum_endpointFiber_detJintegrand_properHead_eq
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (vC :
      {i : Fin (2 * q - 2) //
        ¬r322SelectedFinPredicate
          (r322InternalCoordinatesOfBlock
            q hq head.2) i} → T4)
    (hstandard :
      Integrable
        (r322AnalyticProperHeadStandardClosedIntegrand
          hq ρ ε κ hκ head tail hschedule hproper z vC)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {σ : PartialPairing
                (Fin (2 * residualBlockOrder head.2)) //
              σ ∈ primitiveFullPairings
                (residualBlockOrder head.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder head.2) κB.1
                (fun _ => greenFn)
                (primitiveAssemble
                  (residualBlockOrder head.2)
                  (r322AnalyticHead_one_le_residualBlockOrder
                    κ hκ head tail hschedule)
                  p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    lamEps lam ε ^
          (2 * residualBlockOrder head.2) *
        (∫ vB :
            {i : Fin (2 * q - 2) //
              r322SelectedFinPredicate
                (r322InternalCoordinatesOfBlock
                  q hq head.2) i} → T4,
          ∑ τ : ReductionEndpointFiberAt κ,
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0
                (r322MergeSelectedFinCoordinates
                  (r322InternalCoordinatesOfBlock
                    q hq head.2)
                  vB vC))
          ∂Measure.pi fun _ => paperMeasure) =
      r322ReplaceEdge
          (fun _ : Fin (2 * q - 1) => greenFn)
          (r322AnalyticProperHeadPredecessorEdge
            hq κ hκ head tail hschedule hproper)
          greenFn
          (primitiveKernelDiff ρ lam ε
            (residualBlockOrder head.2)
            (r322AnalyticHead_one_le_residualBlockOrder
              κ hκ head tail hschedule)
            (fun _ => greenFn))
          (r322AnalyticProperHeadOutgoingKernel
            hq κ hκ head tail hschedule hproper z vC)
          (r322AnalyticProperHeadPredecessorEdge
            hq κ hκ head tail hschedule hproper)
          (r322AnalyticProperHeadPredecessorPoint
            hq κ hκ head tail hschedule hproper z vC) *
        r322AnalyticHeadOuterIntegrandFactor
          ρ ε κ head tail hschedule
          (r322AnalyticProperHeadReferenceTuple
            hq κ hκ head tail hschedule hproper z vC) := by
  rw [integral_r322AnalyticProperHeadSelected_eq_standardBlock
    hq κ hκ head tail hschedule hproper]
  simp_rw [
    r322AnalyticProperHeadSelectedTupleMeasurableEquiv_eq_plain
      hq κ hκ head tail hschedule hproper]
  exact
    lamEps_pow_integral_sum_endpointFiber_detJintegrand_properHead_eq
      hq ρ lam ε κ hκ head tail hschedule hproper z vC
      hstandard hinternal

end

end Anderson4D
