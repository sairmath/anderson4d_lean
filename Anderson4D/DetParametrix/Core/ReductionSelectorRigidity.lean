import Anderson4D.DetParametrix.Core.ReductionBlockReplacement
import Anderson4D.DetParametrix.Paper42_Moment.R324BlockCollapse

/-!
# Rigidity of the smallest-leftmost extraction order

The endpoint signature initially determines the interval family only up to
`List.Perm`.  For the exact R-324 fibre factorization we also need the
concrete recursive order, because each step removes a sparse relative trace.

The key observation is that every interval selected later in the recursion
was already fully paired in the earlier active carrier.  A disjoint earlier
trace does not change it, while a nested earlier trace is itself a closed
fully-paired component of the larger interval.  Therefore two extraction
lists which are permutations have the same smallest-key head; recursion then
forces equality of the lists and of their concrete trace blocks.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

/-- A later relative candidate remains a candidate before an earlier,
compatible fully-paired trace is removed. -/
theorem IsRelFullyPaired.lift_before_compatible_removal
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)}
    {p q : Fin m × Fin m}
    (hp : IsRelFullyPaired κ active p.1 p.2)
    (hq :
      IsRelFullyPaired κ
        (active \ relIcc active p.1 p.2) q.1 q.2)
    (hcompat : EarlierReductionIntervalCompatible p q) :
    IsRelFullyPaired κ active q.1 q.2 := by
  let R := relIcc active p.1 p.2
  let active' := active \ R
  have hqLeft : q.1 ∈ active :=
    Finset.sdiff_subset hq.left_mem
  have hqRight : q.2 ∈ active :=
    Finset.sdiff_subset hq.right_mem
  refine ⟨hqLeft, hqRight, hq.le, ?_⟩
  rcases hcompat with hleft | hright | hnested
  · have htrace :
        relIcc active q.1 q.2 =
          relIcc active' q.1 q.2 := by
      ext i
      constructor
      · intro hi
        rw [mem_relIcc] at hi ⊢
        refine
          ⟨Finset.mem_sdiff.mpr ⟨hi.1, ?_⟩,
            hi.2.1, hi.2.2⟩
        intro hiR
        change i ∈ relIcc active p.1 p.2 at hiR
        have hip := (mem_relIcc.mp hiR).2
        omega
      · intro hi
        rw [mem_relIcc] at hi ⊢
        exact
          ⟨Finset.sdiff_subset hi.1,
            hi.2.1, hi.2.2⟩
    rw [htrace]
    exact hq.isFullyPairedOn
  · have htrace :
        relIcc active q.1 q.2 =
          relIcc active' q.1 q.2 := by
      ext i
      constructor
      · intro hi
        rw [mem_relIcc] at hi ⊢
        refine
          ⟨Finset.mem_sdiff.mpr ⟨hi.1, ?_⟩,
            hi.2.1, hi.2.2⟩
        intro hiR
        change i ∈ relIcc active p.1 p.2 at hiR
        have hip := (mem_relIcc.mp hiR).2
        omega
      · intro hi
        rw [mem_relIcc] at hi ⊢
        exact
          ⟨Finset.sdiff_subset hi.1,
            hi.2.1, hi.2.2⟩
    rw [htrace]
    exact hq.isFullyPairedOn
  · have htrace :
        relIcc active q.1 q.2 =
          R ∪ relIcc active' q.1 q.2 := by
      ext i
      constructor
      · intro hi
        by_cases hiR : i ∈ R
        · exact Finset.mem_union_left _ hiR
        · apply Finset.mem_union_right
          rw [mem_relIcc] at hi ⊢
          exact
            ⟨Finset.mem_sdiff.mpr ⟨hi.1, hiR⟩,
              hi.2.1, hi.2.2⟩
      · intro hi
        rcases Finset.mem_union.mp hi with hiR | hiRest
        · change i ∈ relIcc active p.1 p.2 at hiR
          rw [mem_relIcc] at hiR ⊢
          exact
            ⟨hiR.1,
              hnested.1.le.trans hiR.2.1,
              hiR.2.2.trans hnested.2.le⟩
        · exact
            (by
              rw [mem_relIcc] at hiRest ⊢
              exact
                ⟨Finset.sdiff_subset hiRest.1,
                  hiRest.2.1, hiRest.2.2⟩)
    rw [htrace]
    exact hp.isFullyPairedOn.union hq.isFullyPairedOn

/-- Every endpoint pair appearing later in an extraction recursion was
already a fully-paired relative interval in the initial active carrier. -/
theorem extractAux_mem_isRelFullyPaired
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ (active : Finset (Fin m))
      (p : Fin m × Fin m),
      p ∈ extractAux κ fuel active →
        IsRelFullyPaired κ active p.1 p.2 := by
  induction fuel with
  | zero =>
      intro active p hp
      simp at hp
  | succ fuel ih =>
      intro active p hp
      by_cases h :
          ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractAux_succ_pos fuel h] at hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact selectRel_isRelFullyPaired κ active h
        · have hlater :=
            ih
              (active \ relIcc active
                (selectRel κ active h).1
                (selectRel κ active h).2)
              p hp
          have hpairwise :=
            extractAux_pairwise_earlierCompatible
              κ (fuel + 1) active
          rw [extractAux_succ_pos fuel h,
            List.pairwise_cons] at hpairwise
          exact
            IsRelFullyPaired.lift_before_compatible_removal
              (selectRel_isRelFullyPaired κ active h)
              hlater
              (hpairwise.1 p hp)
      · rw [extractAux_succ_neg fuel h] at hp
        simp at hp

/-- Permutation of two nonempty extraction recursions forces equality of
their smallest-key selectors. -/
theorem selectRel_eq_of_extractAux_perm
    {m fuel : ℕ} {κ κ' : PartialPairing (Fin m)}
    {active : Finset (Fin m)}
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    (h' : ∃ a b, IsRelFullyPaired κ' active a b)
    (hperm :
      List.Perm
        (extractAux κ (fuel + 1) active)
        (extractAux κ' (fuel + 1) active)) :
    selectRel κ active h =
      selectRel κ' active h' := by
  let p := selectRel κ active h
  let p' := selectRel κ' active h'
  have hpMem :
      p ∈ extractAux κ (fuel + 1) active := by
    rw [extractAux_succ_pos fuel h]
    exact List.mem_cons_self
  have hp'Mem :
      p' ∈ extractAux κ' (fuel + 1) active := by
    rw [extractAux_succ_pos fuel h']
    exact List.mem_cons_self
  have hpForκ' :
      IsRelFullyPaired κ' active p.1 p.2 :=
    extractAux_mem_isRelFullyPaired
      κ' (fuel + 1) active p
      (hperm.subset hpMem)
  have hp'Forκ :
      IsRelFullyPaired κ active p'.1 p'.2 :=
    extractAux_mem_isRelFullyPaired
      κ (fuel + 1) active p'
      (hperm.symm.subset hp'Mem)
  have hle :
      candKey active p.1 p.2 ≤
        candKey active p'.1 p'.2 :=
    candKey_selectRel_le h hp'Forκ
  have hge :
      candKey active p'.1 p'.2 ≤
        candKey active p.1 p.2 :=
    candKey_selectRel_le h' hpForκ'
  obtain ⟨hfst, hsnd⟩ :=
    candKey_inj (le_antisymm hle hge)
  exact Prod.ext hfst hsnd

/-- The deterministic smallest-leftmost recursion is rigid: if two output
lists are permutations, then they are equal in their actual recursion
order. -/
theorem extractAux_eq_of_perm
    {m : ℕ} (κ κ' : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      List.Perm
          (extractAux κ fuel active)
          (extractAux κ' fuel active) →
        extractAux κ fuel active =
          extractAux κ' fuel active := by
  induction fuel with
  | zero =>
      intro active _hperm
      rfl
  | succ fuel ih =>
      intro active hperm
      by_cases h :
          ∃ a b, IsRelFullyPaired κ active a b
      · have h' :
          ∃ a b, IsRelFullyPaired κ' active a b := by
          by_contra h'
          rw [extractAux_succ_pos fuel h,
            extractAux_succ_neg fuel h'] at hperm
          exact List.not_perm_nil_cons _ _ hperm.symm
        have hselect :
            selectRel κ active h =
              selectRel κ' active h' :=
          selectRel_eq_of_extractAux_perm h h' hperm
        rw [extractAux_succ_pos fuel h,
          extractAux_succ_pos fuel h', ← hselect] at hperm ⊢
        congr 1
        exact ih _ hperm.cons_inv
      · have h' :
          ¬∃ a b, IsRelFullyPaired κ' active a b := by
          intro h'
          rw [extractAux_succ_neg fuel h,
            extractAux_succ_pos fuel h'] at hperm
          exact List.not_perm_nil_cons _ _ hperm
        rw [extractAux_succ_neg fuel h,
          extractAux_succ_neg fuel h']

/-- Endpoint signatures determine the actual extraction list, not merely
its unordered interval family. -/
theorem extract_eq_of_reductionEndpointSignature_eq
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hsignature :
      reductionEndpointSignature κ =
        reductionEndpointSignature κ') :
    extract κ = extract κ' := by
  exact extractAux_eq_of_perm κ κ' m Finset.univ
    (extract_perm_of_reductionEndpointSignature_eq
      κ κ' hsignature)

/-- Equality of endpoint extraction recursions determines the concrete
sparse traces removed at every step. -/
theorem extractionBlocksAux_eq_of_extractAux_eq
    {m : ℕ} (κ κ' : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      extractAux κ fuel active =
          extractAux κ' fuel active →
        extractionBlocksAux κ fuel active =
          extractionBlocksAux κ' fuel active := by
  induction fuel with
  | zero =>
      intro active _hextract
      rfl
  | succ fuel ih =>
      intro active hextract
      by_cases h :
          ∃ a b, IsRelFullyPaired κ active a b
      · have h' :
          ∃ a b, IsRelFullyPaired κ' active a b := by
          by_contra h'
          rw [extractAux_succ_pos fuel h,
            extractAux_succ_neg fuel h'] at hextract
          simp at hextract
        rw [extractAux_succ_pos fuel h,
          extractAux_succ_pos fuel h'] at hextract
        have hselect :
            selectRel κ active h =
              selectRel κ' active h' :=
          (List.cons.inj hextract).1
        have htail := (List.cons.inj hextract).2
        rw [← hselect] at htail
        rw [extractionBlocksAux_succ_pos fuel h,
          extractionBlocksAux_succ_pos fuel h', ← hselect]
        congr 1
        exact ih _ htail
      · have h' :
          ¬∃ a b, IsRelFullyPaired κ' active a b := by
          intro h'
          rw [extractAux_succ_neg fuel h,
            extractAux_succ_pos fuel h'] at hextract
          simp at hextract
        rw [extractionBlocksAux_succ_neg fuel h,
          extractionBlocksAux_succ_neg fuel h']

/-- Endpoint signatures determine the concrete primitive trace blocks in
their actual extraction order. -/
theorem extractionBlocks_eq_of_reductionEndpointSignature_eq
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hsignature :
      reductionEndpointSignature κ =
        reductionEndpointSignature κ') :
    extractionBlocks κ = extractionBlocks κ' := by
  unfold extractionBlocks
  exact extractionBlocksAux_eq_of_extractAux_eq
    κ κ' m Finset.univ
    (extract_eq_of_reductionEndpointSignature_eq
      κ κ' hsignature)

/-! ## Consequences for fixed R-324 moment signatures -/

/-- Equality of doubled moment signatures fixes both concrete within-half
block lists, including their recursive order and sparse traces. -/
theorem momentExtractionBlocks_eq_of_momentContractionSignature_eq
    {m : ℕ} (e e' : MomentContraction m)
    (hsignature :
      momentContractionSignature e =
        momentContractionSignature e') :
    momentLeftExtractionBlocks e.1 =
        momentLeftExtractionBlocks e'.1 ∧
      momentRightExtractionBlocks e.2.1 =
        momentRightExtractionBlocks e'.2.1 := by
  obtain ⟨hleft, hright⟩ :=
    reductionEndpointSignatures_eq_of_momentContractionSignature_eq
      e e' hsignature
  constructor
  · unfold momentLeftExtractionBlocks
    rw [extractionBlocks_eq_of_reductionEndpointSignature_eq
      e.1 e'.1 hleft]
  · unfold momentRightExtractionBlocks
    rw [extractionBlocks_eq_of_reductionEndpointSignature_eq
      e.2.1 e'.2.1 hright]

/-- The terminal active carrier is the complement of the union of the
concrete extraction blocks. -/
theorem finalActive_eq_sdiff_extractionBlocks
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    finalActive κ =
      (Finset.univ : Finset (Fin m)) \
        finsetUnionList (extractionBlocks κ) := by
  ext i
  constructor
  · intro hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    intro hremoved
    exact
      (Finset.disjoint_left.mp
        (extractionBlocks_disjoint_finalActive κ))
        hremoved hi
  · intro hi
    have hcover :
        i ∈ finsetUnionList (extractionBlocks κ) ∪
          finalActive κ := by
      rw [finsetUnionList_extractionBlocks_union_finalActive]
      exact Finset.mem_univ i
    rcases Finset.mem_union.mp hcover with hremoved | hfinal
    · exact (Finset.mem_sdiff.mp hi).2 hremoved |>.elim
    · exact hfinal

/-- An endpoint signature therefore fixes the terminal active carrier. -/
theorem finalActive_eq_of_reductionEndpointSignature_eq
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hsignature :
      reductionEndpointSignature κ =
        reductionEndpointSignature κ') :
    finalActive κ = finalActive κ' := by
  rw [finalActive_eq_sdiff_extractionBlocks,
    finalActive_eq_sdiff_extractionBlocks,
    extractionBlocks_eq_of_reductionEndpointSignature_eq
      κ κ' hsignature]

/-- A doubled moment signature fixes the left and right residual carriers
on which the cross-copy contraction is subsequently collapsed. -/
theorem momentFinalActive_eq_of_momentContractionSignature_eq
    {m : ℕ} (e e' : MomentContraction m)
    (hsignature :
      momentContractionSignature e =
        momentContractionSignature e') :
    finalActive e.1 = finalActive e'.1 ∧
      finalActive e.2.1 = finalActive e'.2.1 := by
  obtain ⟨hleft, hright⟩ :=
    reductionEndpointSignatures_eq_of_momentContractionSignature_eq
      e e' hsignature
  exact
    ⟨finalActive_eq_of_reductionEndpointSignature_eq
        e.1 e'.1 hleft,
      finalActive_eq_of_reductionEndpointSignature_eq
        e.2.1 e'.2.1 hright⟩

/-! ## Exact first-block factorization of an endpoint-signature fibre -/

/-- The finite fibre of partial pairings with the same complete reduction
endpoint signature as `κ`. -/
abbrev ReductionEndpointFiberAt
    {m : ℕ} (κ : PartialPairing (Fin m)) :=
  {τ : PartialPairing (Fin m) //
    reductionEndpointSignature τ =
      reductionEndpointSignature κ}

/-- Equality of the ordered extraction lists immediately implies equality
of endpoint-role signatures. -/
theorem reductionEndpointSignature_eq_of_extract_eq
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hextract : extract κ = extract κ') :
    reductionEndpointSignature κ =
      reductionEndpointSignature κ' := by
  unfold reductionEndpointSignature leftEndpoints rightEndpoints
  rw [hextract]

/-- A nonempty candidate set implies that public fuel `m` is a successor,
so it can be used by the one-step `ExtractionFiberAt` interface. -/
theorem pred_add_one_eq_of_exists_relFullyPaired
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)}
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    m - 1 + 1 = m := by
  obtain ⟨a, b, hab⟩ := h
  have htwo := hab.two_le_card
  have hcard :
      (relIcc active a b).card ≤ m := by
    calc
      (relIcc active a b).card ≤ active.card :=
        Finset.card_le_card
          (relIcc_subset_active active a b)
      _ ≤ (Finset.univ : Finset (Fin m)).card :=
        Finset.card_le_card (Finset.subset_univ active)
      _ = m := by simp
  omega

/-- The endpoint-signature fibre is exactly the fixed ordered-extraction
fibre used by the primitive replacement engine. -/
def reductionEndpointFiberEquivExtractionFiber
    {m : ℕ} (κ : PartialPairing (Fin m))
    (h :
      ∃ a b,
        IsRelFullyPaired κ
          (Finset.univ : Finset (Fin m)) a b) :
    ReductionEndpointFiberAt κ ≃
      ExtractionFiberAt κ (m - 1) Finset.univ where
  toFun τ :=
    ⟨τ.1, by
      rw [pred_add_one_eq_of_exists_relFullyPaired h]
      exact
        extract_eq_of_reductionEndpointSignature_eq
          τ.1 κ τ.2⟩
  invFun τ :=
    ⟨τ.1, by
      apply reductionEndpointSignature_eq_of_extract_eq
      unfold extract
      let hsucc :=
        pred_add_one_eq_of_exists_relFullyPaired h
      calc
        extractAux τ.1 m Finset.univ =
            extractAux τ.1 (m - 1 + 1) Finset.univ :=
          congrArg
            (fun fuel => extractAux τ.1 fuel Finset.univ)
            hsucc.symm
        _ = extractAux κ (m - 1 + 1) Finset.univ :=
          τ.2
        _ = extractAux κ m Finset.univ :=
          congrArg
            (fun fuel => extractAux κ fuel Finset.univ)
            hsucc⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact first recursive coordinate of a nonempty endpoint-signature
fibre: a complete primitive pairing on the selected block, times the
remaining complementary extraction fibre. -/
def reductionEndpointFiberEquivBlockComplement
    {m : ℕ} (κ : PartialPairing (Fin m))
    (h :
      ∃ a b,
        IsRelFullyPaired κ
          (Finset.univ : Finset (Fin m)) a b) :
    ReductionEndpointFiberAt κ ≃
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder
            (selectedExtractionBlock κ Finset.univ h))} ×
      ExtractionComplementFiberAt
        κ (m - 1) Finset.univ h :=
  (reductionEndpointFiberEquivExtractionFiber κ h).trans
    (extractionFiberEquivBlockComplement
      κ (m - 1) Finset.univ h)

/-- Finite-sum form of the exact first-block endpoint-fibre
factorization.  In particular, no cardinality factor is introduced. -/
theorem sum_reductionEndpointFiber_eq_sum_block_complement
    {m : ℕ} (κ : PartialPairing (Fin m))
    (h :
      ∃ a b,
        IsRelFullyPaired κ
          (Finset.univ : Finset (Fin m)) a b)
    {M : Type*} [AddCommMonoid M]
    (F : ReductionEndpointFiberAt κ → M) :
    (∑ τ : ReductionEndpointFiberAt κ, F τ) =
      ∑ κB :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder
                (selectedExtractionBlock κ Finset.univ h))) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder
                (selectedExtractionBlock κ Finset.univ h))},
        ∑ κC :
            ExtractionComplementFiberAt
              κ (m - 1) Finset.univ h,
          F ((reductionEndpointFiberEquivBlockComplement
            κ h).symm (κB, κC)) := by
  let E :=
    reductionEndpointFiberEquivBlockComplement κ h
  calc
    (∑ τ : ReductionEndpointFiberAt κ, F τ) =
        ∑ x :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder
                (selectedExtractionBlock κ Finset.univ h))) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder
                (selectedExtractionBlock κ Finset.univ h))} ×
          ExtractionComplementFiberAt
            κ (m - 1) Finset.univ h,
          F (E.symm x) :=
      (E.symm.sum_comp F).symm
    _ = ∑ κB :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder
                (selectedExtractionBlock κ Finset.univ h))) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder
                (selectedExtractionBlock κ Finset.univ h))},
        ∑ κC :
            ExtractionComplementFiberAt
              κ (m - 1) Finset.univ h,
          F (E.symm (κB, κC)) := by
      rw [Fintype.sum_prod_type]

end

end Anderson4D
