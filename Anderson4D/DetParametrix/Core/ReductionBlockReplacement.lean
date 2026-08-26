import Anderson4D.DetParametrix.Paper42_Moment.R324BlockPairingSum

/-!
# Primitive-block replacement preserves endpoint extraction

The fixed-signature collapse in paper §4.2 requires a converse to the
already proved extraction facts.  Once the selector has exposed a primitive
fully paired block, the pairing inside that block may be replaced by any
other primitive full pairing without changing the selected endpoint or the
remainder of the extraction.

This file proves that statement directly from the smallest-then-leftmost
selector.  The key order fact is that a fully paired relative interval
meeting a primitive closed relative block must contain the whole block.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

/-- Agreement of two pairings on the active carrier preserves every
relative fully-paired predicate on that carrier. -/
theorem isRelFullyPaired_iff_of_eq_on_active
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    {active : Finset (Fin m)}
    (hagree : ∀ i ∈ active, κ i = κ' i)
    (a b : Fin m) :
    IsRelFullyPaired κ active a b ↔
      IsRelFullyPaired κ' active a b := by
  have hfull :
      IsFullyPairedOn κ (relIcc active a b) ↔
        IsFullyPairedOn κ' (relIcc active a b) := by
    constructor
    · intro h
      constructor
      · intro i hi hfix
        apply h.ne_of_mem hi
        rw [hagree i (mem_relIcc.mp hi).1]
        exact hfix
      · intro i hi
        rw [← hagree i (mem_relIcc.mp hi).1]
        exact h.apply_mem hi
    · intro h
      constructor
      · intro i hi hfix
        apply h.ne_of_mem hi
        rw [← hagree i (mem_relIcc.mp hi).1]
        exact hfix
      · intro i hi
        rw [hagree i (mem_relIcc.mp hi).1]
        exact h.apply_mem hi
  unfold IsRelFullyPaired
  rw [hfull]

/-- If the relative candidate predicates agree, the deterministic
smallest-then-leftmost selectors agree as well. -/
theorem selectRel_eq_of_candidates_iff
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    {active : Finset (Fin m)}
    (hcand :
      ∀ a b, IsRelFullyPaired κ active a b ↔
        IsRelFullyPaired κ' active a b)
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (h' : ∃ a b, IsRelFullyPaired κ' active a b) :
    selectRel κ active h = selectRel κ' active h' := by
  have hκ' :
      IsRelFullyPaired κ' active
        (selectRel κ active h).1
        (selectRel κ active h).2 :=
    (hcand _ _).mp
      (selectRel_isRelFullyPaired κ active h)
  have hκ :
      IsRelFullyPaired κ active
        (selectRel κ' active h').1
        (selectRel κ' active h').2 :=
    (hcand _ _).mpr
      (selectRel_isRelFullyPaired κ' active h')
  have hle :
      candKey active
          (selectRel κ active h).1
          (selectRel κ active h).2 ≤
        candKey active
          (selectRel κ' active h').1
          (selectRel κ' active h').2 :=
    candKey_selectRel_le h hκ
  have hge :
      candKey active
          (selectRel κ' active h').1
          (selectRel κ' active h').2 ≤
        candKey active
          (selectRel κ active h).1
          (selectRel κ active h).2 :=
    candKey_selectRel_le h' hκ'
  obtain ⟨hfst, hsnd⟩ :=
    candKey_inj (le_antisymm hle hge)
  exact Prod.ext hfst hsnd

/-- Pairings agreeing on the active carrier have identical extraction
recursions from that carrier. -/
theorem extractAux_eq_of_eq_on_active
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    (fuel : ℕ) (active : Finset (Fin m))
    (hagree : ∀ i ∈ active, κ i = κ' i) :
    extractAux κ fuel active =
      extractAux κ' fuel active := by
  induction fuel generalizing active with
  | zero =>
      rfl
  | succ fuel ih =>
      have hcand := isRelFullyPaired_iff_of_eq_on_active
        hagree
      by_cases h : ∃ a b, IsRelFullyPaired κ active a b
      · have h' : ∃ a b, IsRelFullyPaired κ' active a b := by
          obtain ⟨a, b, hab⟩ := h
          exact ⟨a, b, (hcand a b).mp hab⟩
        have hselect :
            selectRel κ active h =
              selectRel κ' active h' :=
          selectRel_eq_of_candidates_iff hcand h h'
        rw [extractAux_succ_pos fuel h,
          extractAux_succ_pos fuel h', hselect]
        congr 1
        apply ih
        intro i hi
        exact hagree i (Finset.sdiff_subset hi)
      · have h' :
          ¬∃ a b, IsRelFullyPaired κ' active a b := by
          rintro ⟨a, b, hab⟩
          exact h ⟨a, b, (hcand a b).mpr hab⟩
        rw [extractAux_succ_neg fuel h,
          extractAux_succ_neg fuel h']

/-- Agreement on the active carrier also preserves the concrete list of
traces recorded alongside endpoint extraction. -/
theorem extractionBlocksAux_eq_of_eq_on_active
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    (fuel : ℕ) (active : Finset (Fin m))
    (hagree : ∀ i ∈ active, κ i = κ' i) :
    extractionBlocksAux κ fuel active =
      extractionBlocksAux κ' fuel active := by
  induction fuel generalizing active with
  | zero =>
      rfl
  | succ fuel ih =>
      have hcand := isRelFullyPaired_iff_of_eq_on_active
        hagree
      by_cases h : ∃ a b, IsRelFullyPaired κ active a b
      · have h' : ∃ a b, IsRelFullyPaired κ' active a b := by
          obtain ⟨a, b, hab⟩ := h
          exact ⟨a, b, (hcand a b).mp hab⟩
        have hselect :
            selectRel κ active h =
              selectRel κ' active h' :=
          selectRel_eq_of_candidates_iff hcand h h'
        rw [extractionBlocksAux_succ_pos fuel h,
          extractionBlocksAux_succ_pos fuel h', hselect]
        congr 1
        apply ih
        intro i hi
        exact hagree i (Finset.sdiff_subset hi)
      · have h' :
          ¬∃ a b, IsRelFullyPaired κ' active a b := by
          rintro ⟨a, b, hab⟩
          exact h ⟨a, b, (hcand a b).mpr hab⟩
        rw [extractionBlocksAux_succ_neg fuel h,
          extractionBlocksAux_succ_neg fuel h']

/-- The intersection of two relative intervals on the same active carrier
is the relative interval with the maximum left and minimum right endpoint. -/
theorem relIcc_inter_relIcc
    {m : ℕ} (active : Finset (Fin m))
    (a b c d : Fin m) :
    relIcc active a b ∩ relIcc active c d =
      relIcc active (max a c) (min b d) := by
  ext i
  simp only [Finset.mem_inter, mem_relIcc, max_le_iff,
    le_min_iff]
  aesop

/-- A fully paired set disjoint from the replacement block remains fully
paired when the pairings agree outside that block. -/
theorem isFullyPairedOn_of_disjoint_of_eq_outside
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    {B R : Finset (Fin m)}
    (hdisjoint : Disjoint B R)
    (hagree : ∀ i, i ∉ B → κ i = κ' i)
    (hR : IsFullyPairedOn κ R) :
    IsFullyPairedOn κ' R := by
  have hout : ∀ i ∈ R, i ∉ B := by
    intro i hiR hiB
    exact (Finset.disjoint_left.mp hdisjoint) hiB hiR
  constructor
  · intro i hi hfix
    apply hR.ne_of_mem hi
    rw [hagree i (hout i hi)]
    exact hfix
  · intro i hi
    rw [← hagree i (hout i hi)]
    exact hR.apply_mem hi

/-- Any fully paired relative interval meeting a primitive fully paired
relative block contains that entire block.  This is the laminarity fact
which makes primitive-block replacement invisible to the selector. -/
theorem relPrimitiveBlock_subset_of_not_disjoint
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} {p q a b : Fin m}
    (hB : IsRelFullyPaired κ active p q)
    (hprim :
      IsRelPrimitiveOn κ (relIcc active p q))
    (hR : IsRelFullyPaired κ active a b)
    (hinter :
      ¬ Disjoint (relIcc active p q)
        (relIcc active a b)) :
    relIcc active p q ⊆ relIcc active a b := by
  let c : Fin m := max p a
  let d : Fin m := min q b
  rw [Finset.not_disjoint_iff] at hinter
  obtain ⟨x, hxB, hxR⟩ := hinter
  have hxp := (mem_relIcc.mp hxB).2.1
  have hxq := (mem_relIcc.mp hxB).2.2
  have hxa := (mem_relIcc.mp hxR).2.1
  have hxb := (mem_relIcc.mp hxR).2.2
  have hcActive : c ∈ active := by
    rcases le_total p a with hpa | hap
    · rw [show c = a by
        exact max_eq_right hpa]
      exact hR.left_mem
    · rw [show c = p by
        exact max_eq_left hap]
      exact hB.left_mem
  have hdActive : d ∈ active := by
    rcases le_total q b with hqb | hbq
    · rw [show d = q by
        exact min_eq_left hqb]
      exact hB.right_mem
    · rw [show d = b by
        exact min_eq_right hbq]
      exact hR.right_mem
  have hcx : c ≤ x := by
    exact max_le hxp hxa
  have hxd : x ≤ d := by
    exact le_min hxq hxb
  have hcd : c ≤ d := hcx.trans hxd
  have hcB : c ∈ relIcc active p q := by
    exact mem_relIcc.mpr
      ⟨hcActive, le_max_left _ _, hcx.trans hxq⟩
  have hdB : d ∈ relIcc active p q := by
    exact mem_relIcc.mpr
      ⟨hdActive, hxp.trans hxd, min_le_left _ _⟩
  have htrace :
      relIcc (relIcc active p q) c d =
        relIcc active p q ∩ relIcc active a b := by
    have houter :=
      relIcc_residualIntervalTrace
        (p := (p, q)) hcB hdB
    rw [show relIcc (relIcc active p q) c d =
        relIcc active c d by
      simpa only [residualIntervalTrace] using houter]
    exact (relIcc_inter_relIcc active p q a b).symm
  have hinterFull :
      IsFullyPairedOn κ
        (relIcc active p q ∩ relIcc active a b) := by
    constructor
    · intro i hi
      exact hB.isFullyPairedOn.ne_of_mem
        (Finset.mem_inter.mp hi).1
    · intro i hi
      exact Finset.mem_inter.mpr
        ⟨hB.isFullyPairedOn.apply_mem
            (Finset.mem_inter.mp hi).1,
          hR.isFullyPairedOn.apply_mem
            (Finset.mem_inter.mp hi).2⟩
  have hrelative :
      IsRelFullyPaired κ (relIcc active p q) c d := by
    refine ⟨hcB, hdB, hcd, ?_⟩
    rw [htrace]
    exact hinterFull
  have hwhole :=
    hprim c d hrelative
  intro i hiB
  have hiInter :
      i ∈ relIcc active p q ∩ relIcc active a b := by
    rw [← htrace, hwhole]
    exact hiB
  exact (Finset.mem_inter.mp hiInter).2

/-- A candidate for the replaced pairing whose trace is no larger than the
primitive replacement block was already a candidate for the original
pairing.  It is either disjoint from the block or equal to the block. -/
theorem isRelFullyPaired_of_card_le_primitiveBlockReplacement
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    {active : Finset (Fin m)} {p q a b : Fin m}
    (hB : IsRelFullyPaired κ active p q)
    (hB' : IsRelFullyPaired κ' active p q)
    (hprim' :
      IsRelPrimitiveOn κ' (relIcc active p q))
    (hagree :
      ∀ i, i ∉ relIcc active p q → κ i = κ' i)
    (hR' : IsRelFullyPaired κ' active a b)
    (hcard :
      (relIcc active a b).card ≤
        (relIcc active p q).card) :
    IsRelFullyPaired κ active a b := by
  refine
    ⟨hR'.left_mem, hR'.right_mem, hR'.le, ?_⟩
  by_cases hdisjoint :
      Disjoint (relIcc active p q)
        (relIcc active a b)
  · exact isFullyPairedOn_of_disjoint_of_eq_outside
      hdisjoint
      (fun i hi => (hagree i hi).symm)
      hR'.isFullyPairedOn
  · have hsub :
        relIcc active p q ⊆ relIcc active a b :=
      relPrimitiveBlock_subset_of_not_disjoint
        hB' hprim' hR' hdisjoint
    have heq :
        relIcc active a b = relIcc active p q :=
      (Finset.eq_of_subset_of_card_le hsub hcard).symm
    rw [heq]
    exact hB.isFullyPairedOn

/-- Replacing the pairing inside the currently selected trace by an
arbitrary primitive full pairing leaves the deterministic selector
unchanged. -/
theorem selectRel_eq_of_primitive_selectedBlockReplacement
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    {active : Finset (Fin m)}
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (h' : ∃ a b, IsRelFullyPaired κ' active a b)
    (hB' :
      IsFullyPairedOn κ'
        (relIcc active
          (selectRel κ active h).1
          (selectRel κ active h).2))
    (hprim' :
      IsRelPrimitiveOn κ'
        (relIcc active
          (selectRel κ active h).1
          (selectRel κ active h).2))
    (hagree :
      ∀ i,
        i ∉ relIcc active
            (selectRel κ active h).1
            (selectRel κ active h).2 →
          κ i = κ' i) :
    selectRel κ active h =
      selectRel κ' active h' := by
  let p := selectRel κ active h
  let p' := selectRel κ' active h'
  let B := relIcc active p.1 p.2
  let R := relIcc active p'.1 p'.2
  have hp := selectRel_isRelFullyPaired κ active h
  have hp' := selectRel_isRelFullyPaired κ' active h'
  have hBcandidate' :
      IsRelFullyPaired κ' active p.1 p.2 :=
    ⟨hp.left_mem, hp.right_mem, hp.le, hB'⟩
  have hcard : R.card ≤ B.card := by
    exact selectRel_card_le h' hBcandidate'
  have hpOriginal :
      IsRelFullyPaired κ active p'.1 p'.2 := by
    exact
      isRelFullyPaired_of_card_le_primitiveBlockReplacement
        hp hBcandidate' hprim' hagree hp' hcard
  have hle :
      candKey active p.1 p.2 ≤
        candKey active p'.1 p'.2 :=
    candKey_selectRel_le h hpOriginal
  have hge :
      candKey active p'.1 p'.2 ≤
        candKey active p.1 p.2 :=
    candKey_selectRel_le h' hBcandidate'
  obtain ⟨hfst, hsnd⟩ :=
    candKey_inj (le_antisymm hle hge)
  exact Prod.ext hfst hsnd

/-- One primitive replacement step preserves the complete endpoint
extraction recursion: the selected block is unchanged, and after removing
it the pairings agree on the remaining active carrier. -/
theorem extractAux_eq_of_primitive_selectedBlockReplacement
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (hB' :
      IsFullyPairedOn κ'
        (relIcc active
          (selectRel κ active h).1
          (selectRel κ active h).2))
    (hprim' :
      IsRelPrimitiveOn κ'
        (relIcc active
          (selectRel κ active h).1
          (selectRel κ active h).2))
    (hagree :
      ∀ i,
        i ∉ relIcc active
            (selectRel κ active h).1
            (selectRel κ active h).2 →
          κ i = κ' i) :
    extractAux κ (fuel + 1) active =
      extractAux κ' (fuel + 1) active := by
  let p := selectRel κ active h
  let B := relIcc active p.1 p.2
  have hp := selectRel_isRelFullyPaired κ active h
  have hp' : IsRelFullyPaired κ' active p.1 p.2 :=
    ⟨hp.left_mem, hp.right_mem, hp.le, hB'⟩
  have h' : ∃ a b, IsRelFullyPaired κ' active a b :=
    ⟨p.1, p.2, hp'⟩
  have hselect :
      selectRel κ active h =
        selectRel κ' active h' :=
    selectRel_eq_of_primitive_selectedBlockReplacement
      h h' hB' hprim' hagree
  rw [extractAux_succ_pos fuel h,
    extractAux_succ_pos fuel h', hselect]
  congr 1
  apply extractAux_eq_of_eq_on_active
  intro i hi
  apply hagree i
  simpa only [hselect] using (Finset.mem_sdiff.mp hi).2

/-- Concrete-trace counterpart of
`extractAux_eq_of_primitive_selectedBlockReplacement`. -/
theorem extractionBlocksAux_eq_of_primitive_selectedBlockReplacement
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (hB' :
      IsFullyPairedOn κ'
        (relIcc active
          (selectRel κ active h).1
          (selectRel κ active h).2))
    (hprim' :
      IsRelPrimitiveOn κ'
        (relIcc active
          (selectRel κ active h).1
          (selectRel κ active h).2))
    (hagree :
      ∀ i,
        i ∉ relIcc active
            (selectRel κ active h).1
            (selectRel κ active h).2 →
          κ i = κ' i) :
    extractionBlocksAux κ (fuel + 1) active =
      extractionBlocksAux κ' (fuel + 1) active := by
  let p := selectRel κ active h
  let B := relIcc active p.1 p.2
  have hp := selectRel_isRelFullyPaired κ active h
  have hp' : IsRelFullyPaired κ' active p.1 p.2 :=
    ⟨hp.left_mem, hp.right_mem, hp.le, hB'⟩
  have h' : ∃ a b, IsRelFullyPaired κ' active a b :=
    ⟨p.1, p.2, hp'⟩
  have hselect :
      selectRel κ active h =
        selectRel κ' active h' :=
    selectRel_eq_of_primitive_selectedBlockReplacement
      h h' hB' hprim' hagree
  rw [extractionBlocksAux_succ_pos fuel h,
    extractionBlocksAux_succ_pos fuel h', hselect]
  congr 1
  apply extractionBlocksAux_eq_of_eq_on_active
  intro i hi
  apply hagree i
  simpa only [hselect] using (Finset.mem_sdiff.mp hi).2

/-! ## Concrete replacement by a standard primitive pairing -/

/-- The trace selected at the current extraction state. -/
def selectedExtractionBlock
    {m : ℕ} (κ : PartialPairing (Fin m))
    (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    Finset (Fin m) :=
  relIcc active
    (selectRel κ active h).1
    (selectRel κ active h).2

/-- Replace the currently selected block by one standard primitive pairing,
retaining the original pairing on the complementary carrier.  The exact
block/complement equivalence makes this a multiplicity-free operation. -/
def selectedPrimitiveClosedOnReplacement
    {m : ℕ} (κ : PartialPairing (Fin m))
    (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ active h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ active h))}) :
    PrimitiveClosedOn
      (residualBlockOrder
        (selectedExtractionBlock κ active h))
      (selectedExtractionBlock κ active h)
      (residualPrimitiveBlockOrderIso κ
        (selectedExtractionBlock κ active h)
        (selectRel_isRelFullyPaired κ active h).isFullyPairedOn) :=
  (primitiveClosedOnEquiv
    (residualBlockOrder
      (selectedExtractionBlock κ active h))
    (selectedExtractionBlock κ active h)
    (residualPrimitiveBlockOrderIso κ
      (selectedExtractionBlock κ active h)
      (selectRel_isRelFullyPaired κ active h).isFullyPairedOn)).symm
    (κB,
      PartialPairing.restrictCompl κ
        (selectRel_isRelFullyPaired κ active h).isFullyPairedOn.2)

/-- Ambient pairing obtained from
`selectedPrimitiveClosedOnReplacement`. -/
def selectedPrimitiveReplacement
    {m : ℕ} (κ : PartialPairing (Fin m))
    (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ active h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ active h))}) :
    PartialPairing (Fin m) :=
  (selectedPrimitiveClosedOnReplacement
    κ active h κB).1.1

theorem selectedPrimitiveReplacement_eq_outside
    {m : ℕ} (κ : PartialPairing (Fin m))
    (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ active h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ active h))})
    (i : Fin m)
    (hi : i ∉ selectedExtractionBlock κ active h) :
    selectedPrimitiveReplacement κ active h κB i =
      κ i := by
  let replacement :=
    selectedPrimitiveClosedOnReplacement κ active h κB
  let ic :
      {i : Fin m //
        i ∉ selectedExtractionBlock κ active h} :=
    ⟨i, hi⟩
  have hsnd :
      (primitiveClosedOnEquiv
        (residualBlockOrder
          (selectedExtractionBlock κ active h))
        (selectedExtractionBlock κ active h)
        (residualPrimitiveBlockOrderIso κ
          (selectedExtractionBlock κ active h)
          (selectRel_isRelFullyPaired κ active h).isFullyPairedOn)
        replacement).2 =
      PartialPairing.restrictCompl κ
        (selectRel_isRelFullyPaired κ active h).isFullyPairedOn.2 := by
    exact Equiv.apply_symm_apply _ _ |>
      congrArg Prod.snd
  have happly :=
    congrArg
      (fun τ :
        PartialPairing
          {i : Fin m //
            i ∉ selectedExtractionBlock κ active h} =>
        (τ ic).1)
      hsnd
  change replacement.1.1 i = κ i at happly
  change replacement.1.1 i = κ i
  exact happly

/-- The concrete standard-pairing replacement preserves the endpoint
extraction recursion from the current active state. -/
theorem extractAux_selectedPrimitiveReplacement
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ active h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ active h))}) :
    extractAux κ (fuel + 1) active =
      extractAux
        (selectedPrimitiveReplacement κ active h κB)
        (fuel + 1) active := by
  let replacement :=
    selectedPrimitiveClosedOnReplacement κ active h κB
  apply extractAux_eq_of_primitive_selectedBlockReplacement
  · exact replacement.isFullyPairedOn
  · exact replacement.isRelPrimitiveOn
  · intro i hi
    exact
      selectedPrimitiveReplacement_eq_outside
        κ active h κB i hi |>.symm

/-- Concrete-trace counterpart of
`extractAux_selectedPrimitiveReplacement`. -/
theorem extractionBlocksAux_selectedPrimitiveReplacement
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ active h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ active h))}) :
    extractionBlocksAux κ (fuel + 1) active =
      extractionBlocksAux
        (selectedPrimitiveReplacement κ active h κB)
        (fuel + 1) active := by
  let replacement :=
    selectedPrimitiveClosedOnReplacement κ active h κB
  apply extractionBlocksAux_eq_of_primitive_selectedBlockReplacement
  · exact replacement.isFullyPairedOn
  · exact replacement.isRelPrimitiveOn
  · intro i hi
    exact
      selectedPrimitiveReplacement_eq_outside
        κ active h κB i hi |>.symm

/-- At the public initial state, replacing the first primitive block
preserves the complete endpoint extraction list. -/
theorem extract_selectedPrimitiveReplacement
    {m : ℕ} (κ : PartialPairing (Fin m))
    (h : ∃ a b,
      IsRelFullyPaired κ
        (Finset.univ : Finset (Fin m)) a b)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))}) :
    extract κ =
      extract
        (selectedPrimitiveReplacement
          κ Finset.univ h κB) := by
  have hm : 1 ≤ m := by
    obtain ⟨a, b, hab⟩ := h
    have htwo := hab.two_le_card
    have hcard :=
      Finset.card_le_card
        (relIcc_subset_active
          (Finset.univ : Finset (Fin m)) a b)
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have hmEq : m - 1 + 1 = m :=
    Nat.sub_add_cancel hm
  unfold extract
  simpa only [hmEq] using
    (extractAux_selectedPrimitiveReplacement
      κ (m - 1) Finset.univ h κB)

/-- Public concrete-trace list is likewise unchanged. -/
theorem extractionBlocks_selectedPrimitiveReplacement
    {m : ℕ} (κ : PartialPairing (Fin m))
    (h : ∃ a b,
      IsRelFullyPaired κ
        (Finset.univ : Finset (Fin m)) a b)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))}) :
    extractionBlocks κ =
      extractionBlocks
        (selectedPrimitiveReplacement
          κ Finset.univ h κB) := by
  have hm : 1 ≤ m := by
    obtain ⟨a, b, hab⟩ := h
    have htwo := hab.two_le_card
    have hcard :=
      Finset.card_le_card
        (relIcc_subset_active
          (Finset.univ : Finset (Fin m)) a b)
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have hmEq : m - 1 + 1 = m :=
    Nat.sub_add_cancel hm
  unfold extractionBlocks
  simpa only [hmEq] using
    (extractionBlocksAux_selectedPrimitiveReplacement
      κ (m - 1) Finset.univ h κB)

/-- In particular, first-block replacement stays in the same endpoint
signature fiber used by both R-322 and the within-half part of R-324. -/
theorem reductionEndpointSignature_selectedPrimitiveReplacement
    {m : ℕ} (κ : PartialPairing (Fin m))
    (h : ∃ a b,
      IsRelFullyPaired κ
        (Finset.univ : Finset (Fin m)) a b)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))}) :
    reductionEndpointSignature κ =
      reductionEndpointSignature
        (selectedPrimitiveReplacement
          κ Finset.univ h κB) := by
  unfold reductionEndpointSignature leftEndpoints rightEndpoints
  rw [extract_selectedPrimitiveReplacement κ h κB]

/-! ## Block-coordinate form of replacement invariance -/

/-- Equality with a nonempty extraction step forces existence of a
candidate on the other pairing. -/
theorem exists_candidate_of_extractAux_eq
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (hextract :
      extractAux κ' (fuel + 1) active =
        extractAux κ (fuel + 1) active) :
    ∃ a b, IsRelFullyPaired κ' active a b := by
  by_contra h'
  rw [extractAux_succ_neg fuel h',
    extractAux_succ_pos fuel h] at hextract
  simp at hextract

/-- Equality of two nonempty extraction recursions identifies their first
selected endpoints. -/
theorem selectRel_eq_of_extractAux_eq
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (h' : ∃ a b, IsRelFullyPaired κ' active a b)
    (hextract :
      extractAux κ' (fuel + 1) active =
        extractAux κ (fuel + 1) active) :
    selectRel κ' active h' =
      selectRel κ active h := by
  rw [extractAux_succ_pos fuel h',
    extractAux_succ_pos fuel h] at hextract
  exact (List.cons.inj hextract).1

/-- Hence equal nonempty extraction recursions have the same concrete
first trace. -/
theorem selectedExtractionBlock_eq_of_extractAux_eq
    {m : ℕ} {κ κ' : PartialPairing (Fin m)}
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (h' : ∃ a b, IsRelFullyPaired κ' active a b)
    (hextract :
      extractAux κ' (fuel + 1) active =
        extractAux κ (fuel + 1) active) :
    selectedExtractionBlock κ' active h' =
      selectedExtractionBlock κ active h := by
  unfold selectedExtractionBlock
  rw [selectRel_eq_of_extractAux_eq
    fuel active h h' hextract]

/-- Equality of the complementary coordinate in
`primitiveClosedOnEquiv` is exactly equality of the ambient pairings away
from the block. -/
theorem PrimitiveClosedOn.eq_outside_of_complement_eq
    {m q : ℕ} {B : Finset (Fin m)}
    {e : Fin (2 * q) ≃o B}
    (κ κ' : PrimitiveClosedOn q B e)
    (hcomp :
      (primitiveClosedOnEquiv q B e κ).2 =
        (primitiveClosedOnEquiv q B e κ').2)
    (i : Fin m) (hi : i ∉ B) :
    κ.1.1 i = κ'.1.1 i := by
  let ic : {i : Fin m // i ∉ B} := ⟨i, hi⟩
  have happly :=
    congrArg
      (fun τ : PartialPairing {i : Fin m // i ∉ B} =>
        (τ ic).1)
      hcomp
  change κ.1.1 i = κ'.1.1 i at happly
  exact happly

/-- Two ambient pairings which differ only in the primitive coordinate of
the currently selected block have identical endpoint extraction. -/
theorem extractAux_eq_of_primitiveClosedOn_sameComplement
    {m q : ℕ} {B : Finset (Fin m)}
    {e : Fin (2 * q) ≃o B}
    (κ κ' : PrimitiveClosedOn q B e)
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ.1.1 active a b)
    (hB :
      B = selectedExtractionBlock κ.1.1 active h)
    (hcomp :
      (primitiveClosedOnEquiv q B e κ).2 =
        (primitiveClosedOnEquiv q B e κ').2) :
    extractAux κ.1.1 (fuel + 1) active =
      extractAux κ'.1.1 (fuel + 1) active := by
  unfold selectedExtractionBlock at hB
  apply extractAux_eq_of_primitive_selectedBlockReplacement
  · rw [← hB]
    exact κ'.isFullyPairedOn
  · rw [← hB]
    exact κ'.isRelPrimitiveOn
  · intro i hi
    apply κ.eq_outside_of_complement_eq κ' hcomp i
    simpa only [hB] using hi

/-- Concrete-trace counterpart of
`extractAux_eq_of_primitiveClosedOn_sameComplement`. -/
theorem extractionBlocksAux_eq_of_primitiveClosedOn_sameComplement
    {m q : ℕ} {B : Finset (Fin m)}
    {e : Fin (2 * q) ≃o B}
    (κ κ' : PrimitiveClosedOn q B e)
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ.1.1 active a b)
    (hB :
      B = selectedExtractionBlock κ.1.1 active h)
    (hcomp :
      (primitiveClosedOnEquiv q B e κ).2 =
        (primitiveClosedOnEquiv q B e κ').2) :
    extractionBlocksAux κ.1.1 (fuel + 1) active =
      extractionBlocksAux κ'.1.1 (fuel + 1) active := by
  unfold selectedExtractionBlock at hB
  apply extractionBlocksAux_eq_of_primitive_selectedBlockReplacement
  · rw [← hB]
    exact κ'.isFullyPairedOn
  · rw [← hB]
    exact κ'.isRelPrimitiveOn
  · intro i hi
    apply κ.eq_outside_of_complement_eq κ' hcomp i
    simpa only [hB] using hi

/-! ## Exact fiber factorization at one extraction step -/

/-- Pairings with exactly the same remaining endpoint extraction as a fixed
reference pairing. -/
abbrev ExtractionFiberAt
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m)) :=
  {τ : PartialPairing (Fin m) //
    extractAux τ (fuel + 1) active =
      extractAux κ (fuel + 1) active}

/-- Every member of a nonempty extraction fiber carries the fixed first
trace as a primitive closed block. -/
def extractionFiberPrimitiveClosedOn
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (τ : ExtractionFiberAt κ fuel active) :
    PrimitiveClosedOn
      (residualBlockOrder
        (selectedExtractionBlock κ active h))
      (selectedExtractionBlock κ active h)
      (residualPrimitiveBlockOrderIso κ
        (selectedExtractionBlock κ active h)
        (selectRel_isRelFullyPaired κ active h).isFullyPairedOn) := by
  have hτ :
      ∃ a b, IsRelFullyPaired τ.1 active a b :=
    exists_candidate_of_extractAux_eq
      fuel active h τ.2
  have hblock :
      selectedExtractionBlock τ.1 active hτ =
        selectedExtractionBlock κ active h :=
    selectedExtractionBlock_eq_of_extractAux_eq
      fuel active h hτ τ.2
  have hfull :
      IsFullyPairedOn τ.1
        (selectedExtractionBlock κ active h) := by
    rw [← hblock]
    exact
      (selectRel_isRelFullyPaired
        τ.1 active hτ).isFullyPairedOn
  have hprim :
      IsRelPrimitiveOn τ.1
        (selectedExtractionBlock κ active h) := by
    rw [← hblock]
    exact selectRel_trace_isRelPrimitiveOn
      τ.1 active hτ
  refine ⟨⟨τ.1, hfull.2⟩, ?_⟩
  change
    orderedBlockPairing τ.1
        (selectedExtractionBlock κ active h) hfull
        (residualPrimitiveBlockOrderIso κ
          (selectedExtractionBlock κ active h)
          (selectRel_isRelFullyPaired
            κ active h).isFullyPairedOn) ∈
      primitiveFullPairings
        (residualBlockOrder
          (selectedExtractionBlock κ active h))
  rw [mem_primitiveFullPairings]
  exact
    ⟨orderedBlockPairing_isFull τ.1
        (selectedExtractionBlock κ active h) hfull _,
      orderedBlockPairing_isPrimitive τ.1
        (selectedExtractionBlock κ active h)
        hfull hprim _⟩

/-- Forgetting the primitive-block certificate recovers the original
extraction-fiber member. -/
def extractionFiberEquivPrimitiveClosedOn
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    ExtractionFiberAt κ fuel active ≃
      {τ :
        PrimitiveClosedOn
          (residualBlockOrder
            (selectedExtractionBlock κ active h))
          (selectedExtractionBlock κ active h)
          (residualPrimitiveBlockOrderIso κ
            (selectedExtractionBlock κ active h)
            (selectRel_isRelFullyPaired
              κ active h).isFullyPairedOn) //
        extractAux τ.1.1 (fuel + 1) active =
          extractAux κ (fuel + 1) active} where
  toFun τ :=
    ⟨extractionFiberPrimitiveClosedOn
      κ fuel active h τ, τ.2⟩
  invFun τ := ⟨τ.1.1.1, τ.2⟩
  left_inv τ := by
    apply Subtype.ext
    rfl
  right_inv τ := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The reference pairing's standard primitive first-block coordinate. -/
def selectedExtractionPrimitivePairing
    {m : ℕ} (κ : PartialPairing (Fin m))
    (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    {τ : PartialPairing
        (Fin (2 * residualBlockOrder
          (selectedExtractionBlock κ active h))) //
      τ ∈ primitiveFullPairings
        (residualBlockOrder
          (selectedExtractionBlock κ active h))} :=
  ⟨residualPrimitiveBlockPairing κ
      (selectedExtractionBlock κ active h)
      (selectRel_isRelFullyPaired
        κ active h).isFullyPairedOn,
    residualPrimitiveBlockPairing_mem κ
      (selectedExtractionBlock κ active h)
      (selectRel_isRelFullyPaired
        κ active h).isFullyPairedOn
      (selectRel_trace_isRelPrimitiveOn
        κ active h)⟩

/-- The extraction-fiber predicate on a primitive closed block. -/
def IsInPrimitiveExtractionFiber
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (τ :
      PrimitiveClosedOn
        (residualBlockOrder
          (selectedExtractionBlock κ active h))
        (selectedExtractionBlock κ active h)
        (residualPrimitiveBlockOrderIso κ
          (selectedExtractionBlock κ active h)
          (selectRel_isRelFullyPaired
            κ active h).isFullyPairedOn)) : Prop :=
  extractAux τ.1.1 (fuel + 1) active =
    extractAux κ (fuel + 1) active

instance instDecidableIsInPrimitiveExtractionFiber
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (τ :
      PrimitiveClosedOn
        (residualBlockOrder
          (selectedExtractionBlock κ active h))
        (selectedExtractionBlock κ active h)
        (residualPrimitiveBlockOrderIso κ
          (selectedExtractionBlock κ active h)
          (selectRel_isRelFullyPaired
            κ active h).isFullyPairedOn)) :
    Decidable
      (IsInPrimitiveExtractionFiber κ fuel active h τ) := by
  unfold IsInPrimitiveExtractionFiber
  infer_instance

/-- Membership in the fixed extraction fiber is independent of the
primitive first-block coordinate once the complement is fixed. -/
theorem isInPrimitiveExtractionFiber_invariant
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (κB κB' :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ active h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ active h))})
    (κC :
      PartialPairing
        {i : Fin m //
          i ∉ selectedExtractionBlock κ active h}) :
    IsInPrimitiveExtractionFiber κ fuel active h
        ((primitiveClosedOnEquiv
          (residualBlockOrder
            (selectedExtractionBlock κ active h))
          (selectedExtractionBlock κ active h)
          (residualPrimitiveBlockOrderIso κ
            (selectedExtractionBlock κ active h)
            (selectRel_isRelFullyPaired
              κ active h).isFullyPairedOn)).symm
          (κB, κC)) ↔
      IsInPrimitiveExtractionFiber κ fuel active h
        ((primitiveClosedOnEquiv
          (residualBlockOrder
            (selectedExtractionBlock κ active h))
          (selectedExtractionBlock κ active h)
          (residualPrimitiveBlockOrderIso κ
            (selectedExtractionBlock κ active h)
            (selectRel_isRelFullyPaired
              κ active h).isFullyPairedOn)).symm
          (κB', κC)) := by
  let q :=
    residualBlockOrder
      (selectedExtractionBlock κ active h)
  let B := selectedExtractionBlock κ active h
  let e :=
    residualPrimitiveBlockOrderIso κ B
      (selectRel_isRelFullyPaired
        κ active h).isFullyPairedOn
  let τ : PrimitiveClosedOn q B e :=
    (primitiveClosedOnEquiv q B e).symm (κB, κC)
  let τ' : PrimitiveClosedOn q B e :=
    (primitiveClosedOnEquiv q B e).symm (κB', κC)
  have hcomp :
      (primitiveClosedOnEquiv q B e τ).2 =
        (primitiveClosedOnEquiv q B e τ').2 := by
    simp only [τ, τ', Equiv.apply_symm_apply]
  constructor
  · intro hτfiber
    have hτcand :
        ∃ a b, IsRelFullyPaired τ.1.1 active a b :=
      exists_candidate_of_extractAux_eq
        fuel active h hτfiber
    have hblock :
        B = selectedExtractionBlock τ.1.1 active hτcand := by
      exact
        (selectedExtractionBlock_eq_of_extractAux_eq
          fuel active h hτcand hτfiber).symm
    have hsame :=
      extractAux_eq_of_primitiveClosedOn_sameComplement
        τ τ' fuel active hτcand hblock hcomp
    exact hsame.symm.trans hτfiber
  · intro hτ'fiber
    have hτ'cand :
        ∃ a b, IsRelFullyPaired τ'.1.1 active a b :=
      exists_candidate_of_extractAux_eq
        fuel active h hτ'fiber
    have hblock :
        B = selectedExtractionBlock τ'.1.1 active hτ'cand := by
      exact
        (selectedExtractionBlock_eq_of_extractAux_eq
          fuel active h hτ'cand hτ'fiber).symm
    have hsame :=
      extractAux_eq_of_primitiveClosedOn_sameComplement
        τ' τ fuel active hτ'cand hblock hcomp.symm
    exact hsame.symm.trans hτ'fiber

/-- Complementary-coordinate fiber left after the complete primitive sum
on the current first block has been exposed. -/
abbrev ExtractionComplementFiberAt
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b) :=
  {κC :
    PartialPairing
      {i : Fin m //
        i ∉ selectedExtractionBlock κ active h} //
    IsInPrimitiveExtractionFiber κ fuel active h
      ((primitiveClosedOnEquiv
        (residualBlockOrder
          (selectedExtractionBlock κ active h))
        (selectedExtractionBlock κ active h)
        (residualPrimitiveBlockOrderIso κ
          (selectedExtractionBlock κ active h)
          (selectRel_isRelFullyPaired
            κ active h).isFullyPairedOn)).symm
        (selectedExtractionPrimitivePairing κ active h, κC))}

/-- One exact recursive step of fixed-signature factorization: a pairing
fiber is a complete primitive-pairing coordinate on the current block times
one complementary extraction fiber. -/
def extractionFiberEquivBlockComplement
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    ExtractionFiberAt κ fuel active ≃
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ active h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ active h))} ×
      ExtractionComplementFiberAt κ fuel active h :=
  (extractionFiberEquivPrimitiveClosedOn
    κ fuel active h).trans
      (primitiveClosedOnFiberEquiv
        (residualBlockOrder
          (selectedExtractionBlock κ active h))
        (selectedExtractionBlock κ active h)
        (residualPrimitiveBlockOrderIso κ
          (selectedExtractionBlock κ active h)
          (selectRel_isRelFullyPaired
            κ active h).isFullyPairedOn)
        (selectedExtractionPrimitivePairing κ active h)
        (IsInPrimitiveExtractionFiber κ fuel active h)
        (isInPrimitiveExtractionFiber_invariant
          κ fuel active h))

/-- Exact finite-sum form of
`extractionFiberEquivBlockComplement`; no block cardinality or factorial
factor is introduced. -/
theorem sum_extractionFiber_eq_sum_block_complement
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    {M : Type*} [AddCommMonoid M]
    (F : ExtractionFiberAt κ fuel active → M) :
    (∑ τ : ExtractionFiberAt κ fuel active, F τ) =
      ∑ κB :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder
                (selectedExtractionBlock κ active h))) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder
                (selectedExtractionBlock κ active h))},
        ∑ κC : ExtractionComplementFiberAt
            κ fuel active h,
          F ((extractionFiberEquivBlockComplement
            κ fuel active h).symm (κB, κC)) := by
  let E := extractionFiberEquivBlockComplement
    κ fuel active h
  calc
    (∑ τ : ExtractionFiberAt κ fuel active, F τ) =
        ∑ x :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder
                (selectedExtractionBlock κ active h))) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder
                (selectedExtractionBlock κ active h))} ×
          ExtractionComplementFiberAt κ fuel active h,
          F (E.symm x) :=
      (E.symm.sum_comp F).symm
    _ = ∑ κB :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder
                (selectedExtractionBlock κ active h))) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder
                (selectedExtractionBlock κ active h))},
        ∑ κC : ExtractionComplementFiberAt
            κ fuel active h,
          F (E.symm (κB, κC)) := by
      rw [Fintype.sum_prod_type]

end

end Anderson4D
