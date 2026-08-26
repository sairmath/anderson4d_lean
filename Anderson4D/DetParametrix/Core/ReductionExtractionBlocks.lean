import Anderson4D.DetParametrix.Paper42_Moment.R324CovarianceBlocks

/-!
# Concrete blocks removed by Definition 3.1

`extract` records only the endpoint pair chosen at each reduction step.
For the R-322/R-324 analytic iteration one also needs the actual trace in
the then-current carrier.  This file runs the same recursion while recording
those traces and proves:

* they are pairwise disjoint and cover the complement of `finalActive`;
* every recorded trace is fully paired;
* minimality of `selectRel` makes every recorded trace relatively primitive;
* the covariance product factors exactly over the recorded traces and the
  terminal active carrier.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Finite union commutes with mapping every block by the same finset
image. -/
theorem finsetUnionList_map_image
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (blocks : List (Finset α)) :
    finsetUnionList (blocks.map fun B => B.image f) =
      (finsetUnionList blocks).image f := by
  induction blocks with
  | nil =>
      simp [finsetUnionList]
  | cons B blocks ih =>
      simp only [List.map_cons, finsetUnionList,
        Finset.image_union, ih]

/-- An injective image preserves pairwise disjointness of a block list. -/
theorem list_map_image_pairwise_disjoint
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f)
    (blocks : List (Finset α))
    (hblocks : blocks.Pairwise Disjoint) :
    (blocks.map fun B => B.image f).Pairwise Disjoint := by
  induction blocks with
  | nil =>
      simp
  | cons B blocks ih =>
      rw [List.map_cons, List.pairwise_cons]
      have hpair := List.pairwise_cons.mp hblocks
      constructor
      · intro C hC
        obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
        exact (Finset.disjoint_image hf).mpr
          (hpair.1 D hD)
      · exact ih hpair.2

/-- The actual fully-paired trace removed at each execution of
Definition 3.1. -/
def extractionBlocksAux
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    ℕ → Finset (Fin m) → List (Finset (Fin m))
  | 0, _ => []
  | fuel + 1, active =>
      if h : ∃ a b, IsRelFullyPaired κ active a b then
        relIcc active
            (selectRel κ active h).1
            (selectRel κ active h).2 ::
          extractionBlocksAux κ fuel
            (active \ relIcc active
              (selectRel κ active h).1
              (selectRel κ active h).2)
      else []

@[simp]
theorem extractionBlocksAux_zero
    {m : ℕ} (κ : PartialPairing (Fin m))
    (active : Finset (Fin m)) :
    extractionBlocksAux κ 0 active = [] :=
  rfl

@[simp]
theorem extractionBlocksAux_succ_pos
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} (fuel : ℕ)
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    extractionBlocksAux κ (fuel + 1) active =
      relIcc active
          (selectRel κ active h).1
          (selectRel κ active h).2 ::
        extractionBlocksAux κ fuel
          (active \ relIcc active
            (selectRel κ active h).1
            (selectRel κ active h).2) := by
  rw [extractionBlocksAux, dif_pos h]

@[simp]
theorem extractionBlocksAux_succ_neg
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} (fuel : ℕ)
    (h : ¬∃ a b, IsRelFullyPaired κ active a b) :
    extractionBlocksAux κ (fuel + 1) active = [] := by
  rw [extractionBlocksAux, dif_neg h]

/-- Public block list for the full Definition 3.1 run. -/
def extractionBlocks
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    List (Finset (Fin m)) :=
  extractionBlocksAux κ m Finset.univ

/-- Every block produced from `active` remains inside `active`. -/
theorem extractionBlocksAux_forall_subset
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      (extractionBlocksAux κ fuel active).Forall
        fun B => B ⊆ active := by
  induction fuel with
  | zero =>
      intro active
      simp
  | succ fuel ih =>
      intro active
      by_cases h : ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractionBlocksAux_succ_pos fuel h,
          List.forall_cons]
        constructor
        · exact relIcc_subset_active _ _ _
        · exact (ih _).imp fun B hB =>
            hB.trans Finset.sdiff_subset
      · rw [extractionBlocksAux_succ_neg fuel h]
        simp

/-- The recorded blocks are pairwise disjoint. -/
theorem extractionBlocksAux_pairwise_disjoint
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      (extractionBlocksAux κ fuel active).Pairwise Disjoint := by
  induction fuel with
  | zero =>
      intro active
      simp
  | succ fuel ih =>
      intro active
      by_cases h : ∃ a b, IsRelFullyPaired κ active a b
      · let R := relIcc active
          (selectRel κ active h).1
          (selectRel κ active h).2
        rw [extractionBlocksAux_succ_pos fuel h,
          List.pairwise_cons]
        constructor
        · intro B hB
          have hBsub :
              B ⊆ active \ R := by
            exact
              (List.forall_iff_forall_mem.mp
                (extractionBlocksAux_forall_subset
                  κ fuel (active \ R))) B hB
          exact Disjoint.mono_right hBsub
            Finset.disjoint_sdiff
        · exact ih _
      · rw [extractionBlocksAux_succ_neg fuel h]
        simp

/-- Every recorded block is closed under the pairing and contains no
single. -/
theorem extractionBlocksAux_forall_isFullyPairedOn
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      (extractionBlocksAux κ fuel active).Forall
        (IsFullyPairedOn κ) := by
  induction fuel with
  | zero =>
      intro active
      simp
  | succ fuel ih =>
      intro active
      by_cases h : ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractionBlocksAux_succ_pos fuel h,
          List.forall_cons]
        exact
          ⟨(selectRel_isRelFullyPaired κ active h).isFullyPairedOn,
            ih _⟩
      · rw [extractionBlocksAux_succ_neg fuel h]
        simp

/-- A relative interval with both endpoints in an outer relative interval
is a subset of that outer interval. -/
theorem relIcc_subset_relIcc_of_endpoints_mem
    {m : ℕ} {active : Finset (Fin m)}
    {a b c d : Fin m}
    (hc : c ∈ relIcc active a b)
    (hd : d ∈ relIcc active a b) :
    relIcc active c d ⊆ relIcc active a b := by
  intro x hx
  obtain ⟨hxactive, hcx, hxd⟩ := mem_relIcc.mp hx
  obtain ⟨_hcactive, hac, _hcb⟩ := mem_relIcc.mp hc
  obtain ⟨_hdactive, _had, hdb⟩ := mem_relIcc.mp hd
  exact mem_relIcc.mpr
    ⟨hxactive, hac.trans hcx, hxd.trans hdb⟩

/-- Minimality of the Definition 3.1 selector implies that its selected
trace is primitive on its sparse carrier. -/
theorem selectRel_trace_isRelPrimitiveOn
    {m : ℕ} (κ : PartialPairing (Fin m))
    (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    IsRelPrimitiveOn κ
      (relIcc active
        (selectRel κ active h).1
        (selectRel κ active h).2) := by
  let p := selectRel κ active h
  let R := relIcc active p.1 p.2
  intro c d hcd
  have hcR : c ∈ R := hcd.left_mem
  have hdR : d ∈ R := hcd.right_mem
  have htrace :
      relIcc R c d = relIcc active c d := by
    simpa only [R, residualIntervalTrace] using
      (relIcc_residualIntervalTrace hcR hdR)
  have hcdActive :
      IsRelFullyPaired κ active c d := by
    refine
      ⟨(mem_relIcc.mp hcR).1,
        (mem_relIcc.mp hdR).1,
        hcd.le, ?_⟩
    rw [← htrace]
    simpa only [R, p] using hcd.isFullyPairedOn
  have hsub :
      relIcc active c d ⊆ R :=
    relIcc_subset_relIcc_of_endpoints_mem hcR hdR
  have hcardLe :
      R.card ≤ (relIcc active c d).card := by
    exact selectRel_card_le h hcdActive
  have heq :
      relIcc active c d = R :=
    Finset.eq_of_subset_of_card_le hsub hcardLe
  rw [htrace, heq]

/-- Every block produced by Definition 3.1 is relatively primitive. -/
theorem extractionBlocksAux_forall_isRelPrimitiveOn
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      (extractionBlocksAux κ fuel active).Forall
        (IsRelPrimitiveOn κ) := by
  induction fuel with
  | zero =>
      intro active
      simp
  | succ fuel ih =>
      intro active
      by_cases h : ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractionBlocksAux_succ_pos fuel h,
          List.forall_cons]
        exact
          ⟨selectRel_trace_isRelPrimitiveOn κ active h,
            ih _⟩
      · rw [extractionBlocksAux_succ_neg fuel h]
        simp

/-- Removed blocks together with the terminal active carrier cover the
initial active carrier exactly. -/
theorem finsetUnionList_extractionBlocksAux_union_final
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      finsetUnionList (extractionBlocksAux κ fuel active) ∪
          (extractAuxS κ fuel active).2 =
        active := by
  induction fuel with
  | zero =>
      intro active
      simp [finsetUnionList]
  | succ fuel ih =>
      intro active
      by_cases h : ∃ a b, IsRelFullyPaired κ active a b
      · let R := relIcc active
          (selectRel κ active h).1
          (selectRel κ active h).2
        rw [extractionBlocksAux_succ_pos fuel h,
          extractAuxS_succ_pos fuel h, finsetUnionList]
        dsimp only [Prod.snd]
        rw [Finset.union_assoc, ih]
        exact Finset.union_sdiff_of_subset
          (relIcc_subset_active active
            (selectRel κ active h).1
            (selectRel κ active h).2)
      · rw [extractionBlocksAux_succ_neg fuel h,
          extractAuxS_succ_neg fuel h]
        simp [finsetUnionList]

/-- The terminal active carrier remains a subset of the carrier supplied to
the recursion. -/
theorem extractAuxS_final_subset
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      (extractAuxS κ fuel active).2 ⊆ active := by
  induction fuel with
  | zero =>
      intro active
      exact Finset.Subset.rfl
  | succ fuel ih =>
      intro active
      by_cases h : ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractAuxS_succ_pos fuel h]
        exact (ih _).trans Finset.sdiff_subset
      · simpa only [extractAuxS_succ_neg fuel h] using
          (Finset.Subset.rfl : active ⊆ active)

/-- The union of all removed blocks is disjoint from the terminal active
carrier. -/
theorem extractionBlocksAux_disjoint_final
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      Disjoint
        (finsetUnionList (extractionBlocksAux κ fuel active))
        (extractAuxS κ fuel active).2 := by
  induction fuel with
  | zero =>
      intro active
      simp [finsetUnionList]
  | succ fuel ih =>
      intro active
      by_cases h : ∃ a b, IsRelFullyPaired κ active a b
      · let R := relIcc active
          (selectRel κ active h).1
          (selectRel κ active h).2
        let active' := active \ R
        rw [extractionBlocksAux_succ_pos fuel h,
          extractAuxS_succ_pos fuel h, finsetUnionList]
        dsimp only [Prod.snd]
        rw [Finset.disjoint_left]
        intro i hiBlocks hiFinal
        rcases Finset.mem_union.mp hiBlocks with hiR | hiRest
        · have hiActive' :
              i ∈ active' :=
            extractAuxS_final_subset κ fuel active' hiFinal
          exact (Finset.mem_sdiff.mp hiActive').2 hiR
        · exact
            (Finset.disjoint_left.mp (ih active'))
              hiRest hiFinal
      · rw [extractionBlocksAux_succ_neg fuel h,
          extractAuxS_succ_neg fuel h]
        simp [finsetUnionList]

/-- The public extraction blocks cover precisely the complement of
`finalActive`. -/
theorem finsetUnionList_extractionBlocks_union_finalActive
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    finsetUnionList (extractionBlocks κ) ∪ finalActive κ =
      Finset.univ := by
  exact
    finsetUnionList_extractionBlocksAux_union_final
      κ m Finset.univ

/-- The terminal carrier is disjoint from every removed block. -/
theorem extractionBlocks_disjoint_finalActive
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Disjoint
      (finsetUnionList (extractionBlocks κ))
      (finalActive κ) := by
  exact extractionBlocksAux_disjoint_final
    κ m Finset.univ

theorem extractionBlocks_pairwise_disjoint
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (extractionBlocks κ).Pairwise Disjoint :=
  extractionBlocksAux_pairwise_disjoint
    κ m Finset.univ

theorem extractionBlocks_forall_isFullyPairedOn
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (extractionBlocks κ).Forall
      (IsFullyPairedOn κ) :=
  extractionBlocksAux_forall_isFullyPairedOn
    κ m Finset.univ

theorem extractionBlocks_forall_isRelPrimitiveOn
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (extractionBlocks κ).Forall
      (IsRelPrimitiveOn κ) :=
  extractionBlocksAux_forall_isRelPrimitiveOn
    κ m Finset.univ

theorem extractionBlock_isFullyPairedOn_of_mem
    {m : ℕ} (κ : PartialPairing (Fin m))
    (B : Finset (Fin m))
    (hB : B ∈ extractionBlocks κ) :
    IsFullyPairedOn κ B :=
  (List.forall_iff_forall_mem.mp
    (extractionBlocks_forall_isFullyPairedOn κ)) B hB

theorem extractionBlock_isRelPrimitiveOn_of_mem
    {m : ℕ} (κ : PartialPairing (Fin m))
    (B : Finset (Fin m))
    (hB : B ∈ extractionBlocks κ) :
    IsRelPrimitiveOn κ B :=
  (List.forall_iff_forall_mem.mp
    (extractionBlocks_forall_isRelPrimitiveOn κ)) B hB

/-- Every concrete Definition 3.1 block transports to an actual member of
the primitive full-pairing family used by Proposition 4.1. -/
theorem extractionBlock_residualPrimitiveBlockPairing_mem
    {m : ℕ} (κ : PartialPairing (Fin m))
    (B : Finset (Fin m))
    (hB : B ∈ extractionBlocks κ) :
    residualPrimitiveBlockPairing κ B
        (extractionBlock_isFullyPairedOn_of_mem κ B hB) ∈
      primitiveFullPairings (residualBlockOrder B) := by
  exact residualPrimitiveBlockPairing_mem κ B
    (extractionBlock_isFullyPairedOn_of_mem κ B hB)
    (extractionBlock_isRelPrimitiveOn_of_mem κ B hB)

/-- Exact covariance factorization into all Definition 3.1 primitive
blocks and the terminal carrier. -/
theorem pairingCovarianceProductOn_univ_eq_extractionBlocks_mul_final
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin m)) (v : Fin m → T4) :
    pairingCovarianceProductOn ρ ε κ Finset.univ v =
      ((extractionBlocks κ).map fun B =>
        pairingCovarianceProductOn ρ ε κ B v).prod *
      pairingCovarianceProductOn ρ ε κ (finalActive κ) v := by
  rw [← finsetUnionList_extractionBlocks_union_finalActive κ,
    pairingCovarianceProductOn_union ρ ε κ
      (finsetUnionList (extractionBlocks κ))
      (finalActive κ)
      (extractionBlocks_disjoint_finalActive κ) v,
    pairingCovarianceProductOn_finsetUnionList
      ρ ε κ (extractionBlocks κ)
      (extractionBlocks_pairwise_disjoint κ) v]

/-- For a full pairing the terminal carrier is empty, so its entire
covariance product is the product of the primitive extraction-block
factors. -/
theorem primitiveCovarianceProduct_eq_prod_extractionBlocks_of_full
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (κ : PartialPairing (Fin (2 * q))) (hκ : κ.IsFull)
    (v : Fin (2 * q) → T4) :
    primitiveCovarianceProduct ρ ε q κ v =
      ((extractionBlocks κ).map fun B =>
        pairingCovarianceProductOn ρ ε κ B v).prod := by
  rw [← pairingCovarianceProductOn_univ ρ ε q κ v,
    pairingCovarianceProductOn_univ_eq_extractionBlocks_mul_final,
    finalActive_eq_empty_of_full hκ,
    pairingCovarianceProductOn_empty,
    mul_one]

end

end Anderson4D
