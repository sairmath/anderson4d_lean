import Anderson4D.DetParametrix.Core.FinalBound
import Anderson4D.DetParametrix.Core.ReductionSelectorRigidity
import Anderson4D.DetParametrix.Paper41_Renorm.R322OneBlockCollapse

/-!
# The concrete endpoint fibre for R-322

This file connects the endpoint-signature grouping used in the statement of
the deterministic renormalization bound to the exact finite fibre exposed by
the primitive-block replacement engine.

The non-split filter cannot simply be discarded: doing so would enlarge a
signed sum and destroy the cancellation supplied by Proposition 4.1.  We
therefore prove that fullness and the absence of a fully paired proper prefix
are invariants of the complete reduction endpoint signature.  Consequently a
realized non-split endpoint fibre is exactly `ReductionEndpointFiberAt`, and
its first primitive coordinate is exposed with no cardinality loss.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## Fullness is fixed by the endpoint signature -/

/-- If the reduction endpoint signature agrees with that of a full pairing,
then the second pairing is full as well. -/
theorem isFull_of_reductionEndpointSignature_eq
    {m : ℕ} (κ τ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (hsignature :
      reductionEndpointSignature τ =
        reductionEndpointSignature κ) :
    τ.IsFull := by
  have hfinal :
      finalActive τ = ∅ := by
    rw [finalActive_eq_of_reductionEndpointSignature_eq
      τ κ hsignature, finalActive_eq_empty_of_full hκ]
  rw [PartialPairing.isFull_iff_singles_eq_empty]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨i, hi⟩
  have hiFinal : i ∈ finalActive τ :=
    singles_subset_finalActive τ hi
  rw [hfinal] at hiFinal
  exact Finset.notMem_empty i hiFinal

/-! ## Fully paired intervals are fixed by the block signature -/

/-- The intersection of a sparse carrier with an ordinary interval is the
relative interval between the minimum and maximum points of the
intersection. -/
theorem relIcc_min'_max'_eq_inter_Icc
    {m : ℕ} (B : Finset (Fin m)) (a b : Fin m)
    (hne : (B ∩ Finset.Icc a b).Nonempty) :
    relIcc B
        ((B ∩ Finset.Icc a b).min' hne)
        ((B ∩ Finset.Icc a b).max' hne) =
      B ∩ Finset.Icc a b := by
  let I := B ∩ Finset.Icc a b
  let c : Fin m := I.min' hne
  let d : Fin m := I.max' hne
  have hcI : c ∈ I := Finset.min'_mem I hne
  have hdI : d ∈ I := Finset.max'_mem I hne
  have hcB : c ∈ B := (Finset.mem_inter.mp hcI).1
  have hdB : d ∈ B := (Finset.mem_inter.mp hdI).1
  have hac : a ≤ c := (Finset.mem_Icc.mp
    (Finset.mem_inter.mp hcI).2).1
  have hdb : d ≤ b := (Finset.mem_Icc.mp
    (Finset.mem_inter.mp hdI).2).2
  ext i
  constructor
  · intro hi
    obtain ⟨hiB, hci, hid⟩ := mem_relIcc.mp hi
    exact Finset.mem_inter.mpr
      ⟨hiB, Finset.mem_Icc.mpr
        ⟨hac.trans hci, hid.trans hdb⟩⟩
  · intro hi
    have hiI : i ∈ I := hi
    exact mem_relIcc.mpr
      ⟨(Finset.mem_inter.mp hi).1,
        Finset.min'_le I i hiI,
        Finset.le_max' I i hiI⟩

/-- On a full pairing, the concrete extraction blocks cover every index. -/
theorem mem_extractionBlock_of_full
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull) (i : Fin m) :
    ∃ B ∈ extractionBlocks κ, i ∈ B := by
  have hiUnion :
      i ∈ finsetUnionList (extractionBlocks κ) := by
    have hcover :=
      finsetUnionList_extractionBlocks_union_finalActive κ
    have hi :
        i ∈ finsetUnionList (extractionBlocks κ) ∪
          finalActive κ := by
      rw [hcover]
      exact Finset.mem_univ i
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hi
    · rw [finalActive_eq_empty_of_full hκ] at hi
      exact (Finset.notMem_empty i hi).elim
  exact (mem_finsetUnionList_iff
    (blocks := extractionBlocks κ) (x := i)).mp hiUnion

/-- If two full pairings have the same concrete primitive blocks, every
ordinary interval fully paired by the second pairing is fully paired by the
first.  The proof uses relative primitivity: a block which meets a fully
paired interval must lie wholly inside it. -/
theorem isFullyPairedOn_Icc_of_extractionBlocks_eq
    {m : ℕ} (κ τ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (hblocks : extractionBlocks τ = extractionBlocks κ)
    (a b : Fin m)
    (hIτ : IsFullyPairedOn τ (Finset.Icc a b)) :
    IsFullyPairedOn κ (Finset.Icc a b) := by
  constructor
  · intro i _hi
    exact hκ i
  · intro i hi
    obtain ⟨B, hBκ, hiB⟩ :=
      mem_extractionBlock_of_full κ hκ i
    have hBτ : B ∈ extractionBlocks τ := by
      rw [hblocks]
      exact hBκ
    have hBfullτ :
        IsFullyPairedOn τ B :=
      extractionBlock_isFullyPairedOn_of_mem τ B hBτ
    have hBprimτ :
        IsRelPrimitiveOn τ B :=
      extractionBlock_isRelPrimitiveOn_of_mem τ B hBτ
    have hne : (B ∩ Finset.Icc a b).Nonempty :=
      ⟨i, Finset.mem_inter.mpr ⟨hiB, hi⟩⟩
    have hinterFull :
        IsFullyPairedOn τ (B ∩ Finset.Icc a b) :=
      hBfullτ.inter hIτ
    let c : Fin m := (B ∩ Finset.Icc a b).min' hne
    let d : Fin m := (B ∩ Finset.Icc a b).max' hne
    have hcd :
        IsRelFullyPaired τ B c d := by
      have hc :
          c ∈ B ∩ Finset.Icc a b :=
        Finset.min'_mem _ hne
      have hd :
          d ∈ B ∩ Finset.Icc a b :=
        Finset.max'_mem _ hne
      refine
        ⟨(Finset.mem_inter.mp hc).1,
          (Finset.mem_inter.mp hd).1,
          Finset.min'_le _ d hd, ?_⟩
      rw [relIcc_min'_max'_eq_inter_Icc B a b hne]
      exact hinterFull
    have hBsub :
        B ⊆ Finset.Icc a b := by
      have hwhole := hBprimτ c d hcd
      rw [relIcc_min'_max'_eq_inter_Icc B a b hne] at hwhole
      intro j hj
      have :
          j ∈ B ∩ Finset.Icc a b := by
        rw [hwhole]
        exact hj
      exact (Finset.mem_inter.mp this).2
    have hκiB :
        κ i ∈ B :=
      (extractionBlock_isFullyPairedOn_of_mem
        κ B hBκ).apply_mem hiB
    exact hBsub hκiB

/-- Endpoint-signature equality preserves every fully paired ordinary
interval, in either direction, once one (hence both) pairing is full. -/
theorem isFullyPairedOn_Icc_iff_of_reductionEndpointSignature_eq
    {m : ℕ} (κ τ : PartialPairing (Fin m))
    (hκ : κ.IsFull)
    (hsignature :
      reductionEndpointSignature τ =
        reductionEndpointSignature κ)
    (a b : Fin m) :
    IsFullyPairedOn τ (Finset.Icc a b) ↔
      IsFullyPairedOn κ (Finset.Icc a b) := by
  have hτ :=
    isFull_of_reductionEndpointSignature_eq
      κ τ hκ hsignature
  have hblocks :
      extractionBlocks τ = extractionBlocks κ :=
    extractionBlocks_eq_of_reductionEndpointSignature_eq
      τ κ hsignature
  constructor
  · exact isFullyPairedOn_Icc_of_extractionBlocks_eq
      κ τ hκ hblocks a b
  · exact isFullyPairedOn_Icc_of_extractionBlocks_eq
      τ κ hτ hblocks.symm a b

/-! ## The non-split filter is fixed by the endpoint signature -/

/-- The paper's prefix set is an ordinary interval from zero. -/
theorem univ_filter_val_le_eq_Icc
    {m p : ℕ} (hp : p < m) :
    (Finset.univ.filter
        (fun i : Fin m => i.val ≤ p)) =
      Finset.Icc
        (⟨0, Nat.zero_lt_of_lt hp⟩ : Fin m)
        ⟨p, hp⟩ := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_Icc]
  change i.val ≤ p ↔ 0 ≤ i.val ∧ i.val ≤ p
  omega

/-- `IsNonSplit` is an invariant of the complete reduction endpoint
signature. -/
theorem isNonSplit_of_reductionEndpointSignature_eq
    {q : ℕ} (κ τ : PartialPairing (Fin (2 * q)))
    (hκ : IsNonSplit κ)
    (hsignature :
      reductionEndpointSignature τ =
        reductionEndpointSignature κ) :
    IsNonSplit τ := by
  refine
    ⟨isFull_of_reductionEndpointSignature_eq
        κ τ hκ.1 hsignature, ?_⟩
  rintro ⟨p, hpRange, hpProper, hpτ⟩
  have hpLt : p < 2 * q := by omega
  let z0 : Fin (2 * q) :=
    ⟨0, Nat.zero_lt_of_lt hpLt⟩
  have hpτIcc :
      IsFullyPairedOn τ
        (Finset.Icc z0 ⟨p, hpLt⟩) := by
    rw [← univ_filter_val_le_eq_Icc hpLt]
    exact hpτ
  have hpκIcc :
      IsFullyPairedOn κ
        (Finset.Icc z0 ⟨p, hpLt⟩) :=
    (isFullyPairedOn_Icc_iff_of_reductionEndpointSignature_eq
      κ τ hκ.1 hsignature z0 ⟨p, hpLt⟩).mp hpτIcc
  apply hκ.2
  refine ⟨p, hpRange, hpProper, ?_⟩
  rw [univ_filter_val_le_eq_Icc hpLt]
  exact hpκIcc

/-! ## Exact identification of the grouped finite sum -/

/-- A realized non-split endpoint fibre is exactly the complete endpoint
signature fibre used by the replacement engine. -/
def reductionEndpointFiberEquivNonSplitFinset
    {q : ℕ} (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q) :
    ReductionEndpointFiberAt κ ≃
      ↥((nonSplitPairings q).filter fun τ =>
        reductionEndpointSignature τ =
          reductionEndpointSignature κ) where
  toFun τ :=
    ⟨τ.1, Finset.mem_filter.mpr
      ⟨mem_nonSplitPairings.mpr
          (isNonSplit_of_reductionEndpointSignature_eq
            κ τ.1 (mem_nonSplitPairings.mp hκ) τ.2),
        τ.2⟩⟩
  invFun τ :=
    ⟨τ.1, (Finset.mem_filter.mp τ.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The definition-level endpoint sum is a genuine `Fintype` sum over the
complete signature fibre, with no omitted or extra pairings. -/
theorem endpointFiberDetJSum_eq_fintype
    (ρ : SmoothCutoff) (lam ε : ℝ) {q : ℕ}
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q) (z : T4) :
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
      ∑ τ : ReductionEndpointFiberAt κ,
        detJ ρ lam ε q τ.1 z 0 := by
  let S :=
    (nonSplitPairings q).filter fun τ =>
      reductionEndpointSignature τ =
        reductionEndpointSignature κ
  let E :=
    reductionEndpointFiberEquivNonSplitFinset κ hκ
  unfold endpointFiberDetJSum
  change
    (∑ τ ∈ S, detJ ρ lam ε q τ z 0) =
      ∑ τ : ReductionEndpointFiberAt κ,
        detJ ρ lam ε q τ.1 z 0
  calc
    (∑ τ ∈ S, detJ ρ lam ε q τ z 0) =
        ∑ τ : ↥S,
          detJ ρ lam ε q τ.1 z 0 := by
      simpa only [← Finset.univ_eq_attach S] using
        (Finset.sum_attach S
          (fun τ => detJ ρ lam ε q τ z 0)).symm
    _ =
        ∑ τ : ReductionEndpointFiberAt κ,
          detJ ρ lam ε q τ.1 z 0 := by
      calc
        (∑ τ : ↥S,
            detJ ρ lam ε q τ.1 z 0) =
            ∑ τ : ReductionEndpointFiberAt κ,
              detJ ρ lam ε q (E τ).1 z 0 :=
          (E.sum_comp
            (fun τ : ↥S =>
              detJ ρ lam ε q τ.1 z 0)).symm
        _ =
            ∑ τ : ReductionEndpointFiberAt κ,
              detJ ρ lam ε q τ.1 z 0 := by
          apply Finset.sum_congr rfl
          intro τ _hτ
          rfl

/-- First exact R-322 coordinate of the grouped kernel sum.  This is the
concrete bridge from `endpointFiberDetJSum` to a complete primitive block
sum, without absolute values or multiplicity factors. -/
theorem endpointFiberDetJSum_eq_firstBlock
    (ρ : SmoothCutoff) (lam ε : ℝ) {q : ℕ}
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (h :
      ∃ a b,
        IsRelFullyPaired κ
          (Finset.univ : Finset (Fin (2 * q))) a b)
    (z : T4) :
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
      ∑ κB :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder
                (selectedExtractionBlock κ Finset.univ h))) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder
                (selectedExtractionBlock κ Finset.univ h))},
        ∑ κC :
            ExtractionComplementFiberAt
              κ (2 * q - 1) Finset.univ h,
          detJ ρ lam ε q
            ((reductionEndpointFiberEquivBlockComplement
              κ h).symm (κB, κC)).1 z 0 := by
  rw [endpointFiberDetJSum_eq_fintype
    ρ lam ε κ hκ z]
  exact
    sum_reductionEndpointFiber_eq_sum_block_complement
      κ h (fun τ =>
        detJ ρ lam ε q τ.1 z 0)

end

end Anderson4D
