import Anderson4D.PermSum.Inductive
import Anderson4D.PermSum.MergeConstants
import Anderson4D.PermSum.MergeProfileRegroup
import Anderson4D.PermSum.MergeRHSApplication
import Anderson4D.PermSum.MergeWeightBridge

/-!
# The permutation-sum estimate

Run compression reduces Proposition 5.7 to Proposition 5.9.  The source
sum is regrouped first by compressed word and then by compressed
multiplicity profile.  The two finite ledgers cost `4^(2n)`, the
factorial comparison costs `4^n`, and the resulting `64^n` is absorbed
into one absolute constant.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- The exact P-5.7 `paperSum` is the primitive valid-word family used by
the run-compression regrouping, with the original factorial ledger kept
outside each compressed chain weight. -/
theorem paperSum_primitiveChainWeight_eq_primitiveMergeWordFamily
    {t : PlaneTree} {M : ℕ}
    (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) :
    paperSum (M := M) (leafMultiplicity mu)
        (primitiveChainWeight z) =
      ∑ w ∈ primitiveMergeWordFamily
          (M := M) (leafMultiplicity mu),
        (∏ l : HeppLeaf t,
          ((leafMultiplicity mu l).factorial : ℝ)) *
          heppChainWeight z
            (listWord
              (mergedProfileOutcome
                (leafMultiplicity mu) w).2) := by
  let L : ℝ :=
    ∏ l : HeppLeaf t,
      ((leafMultiplicity mu l).factorial : ℝ)
  unfold paperSum wordSum
  rw [Finset.mul_sum]
  calc
    (∑ w ∈ validWords (M := M) (leafMultiplicity mu),
        L * primitiveChainWeight z w) =
        ∑ w : MergeValidWord
            (M := M) (leafMultiplicity mu),
          L * primitiveChainWeight z w.1 := by
      apply Finset.sum_subtype
      intro w
      rfl
    _ =
        ∑ w ∈ primitiveMergeWordFamily
            (M := M) (leafMultiplicity mu),
          L *
            heppChainWeight z
              (listWord
                (mergedProfileOutcome
                  (leafMultiplicity mu) w).2) := by
      unfold primitiveMergeWordFamily
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hprimitive : NoProperLeafBlock w.1
      · rw [if_pos hprimitive]
        unfold primitiveChainWeight
        rw [if_pos hprimitive]
        congr 1
        exact
          (heppChainWeight_listWord_mergedWordList
            z w.1).symm
      · rw [if_neg hprimitive]
        unfold primitiveChainWeight
        rw [if_neg hprimitive]
        simp

/-- One realized compressed profile is controlled uniformly by the
P-5.9 estimate and the factorial comparison. -/
theorem primitiveProfileFiber_le_uniformTarget
    {C0 D : ℝ} (hinductive : InductiveEstimate C0 D)
    {t : PlaneTree} {R n : ℕ}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t)
    (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hadmissible : IsAdmissible Nm R z)
    (htotal : totalMultiplicity mu = 2 * n)
    (p : MergeMultiplicityProfile (leafMultiplicity mu))
    (hp : p ∈
      mergeMultiplicityProfileImage
        (leafMultiplicity mu)
        (primitiveMergeWordFamily
          (M := 2 * n) (leafMultiplicity mu))) :
    (∑ q ∈
        (mergeProfileOutcomeImage
          (leafMultiplicity mu)
          (primitiveMergeWordFamily
            (M := 2 * n) (leafMultiplicity mu))).filter
            (fun q => q.1 = p),
      (∏ l : HeppLeaf t,
        ((leafMultiplicity mu l).factorial : ℝ)) *
        heppChainWeight z (listWord q.2)) ≤
      C0 ^ (2 * n) *
        D ^ (BranchNodes t).card *
        (4 : ℝ) ^ n *
        ∑ W ∈ (nonrootBranches t).powerset,
          permSumSummand n Nm mu W := by
  obtain ⟨w₀, hw₀, hp₀⟩ := Finset.mem_image.mp hp
  have hprimitive : NoProperLeafBlock w₀.1 :=
    (Finset.mem_filter.mp hw₀).2
  have hvalid :
      w₀.1 ∈ validWords (leafMultiplicity mu) :=
    w₀.2
  let mu' : Multiplicities t :=
    mergedMultiplicities hroot mu w₀.1 hvalid hprimitive
  have htotal' :
      totalMultiplicity mu' =
        (mergedWordList w₀.1).length := by
    exact totalMultiplicity_mergedMultiplicities
      hroot mu w₀.1 hvalid hprimitive
  have hP59 :
      paperSum (M := (mergedWordList w₀.1).length)
          (leafMultiplicity mu')
          (primitiveSeparatedChainWeight z) ≤
        inductiveRHS C0 D (mergedWordList w₀.1).length
          t Nm mu' ∅ := by
    exact hinductive.2.2
      (mergedWordList w₀.1).length t Nm mu' ∅ z
      ht hroot (by simp) htotal'
      hadmissible.isSeparatedEmbedding
      (hadmissible.satisfiesSubtreeDiameter mu')
  have hprofileTotal :
      p.total = (mergedWordList w₀.1).length := by
    unfold MergeMultiplicityProfile.total
    rw [← hp₀]
    exact
      sum_mergedMultiplicityProfile
        (leafMultiplicity mu) w₀
  have hprofileMultiplicity :
      p.toNat = leafMultiplicity mu' := by
    rw [← hp₀]
    funext l
    simp [mu']
  have hprofileWords :=
    sum_primitiveProfileFiber_chainWeight_le_wordSum
      (M := 2 * n) (leafMultiplicity mu) p z
  have hledgerNonneg :
      0 ≤
        ∏ l : HeppLeaf t,
          ((leafMultiplicity mu l).factorial : ℝ) := by
    positivity
  have hscaledWords :
      (∏ l : HeppLeaf t,
          ((leafMultiplicity mu l).factorial : ℝ)) *
          (∑ q :
            ↥(primitiveProfileOutcomeFiber
              (M := 2 * n) (leafMultiplicity mu) p),
            heppChainWeight z (listWord q.1.2)) ≤
        (∏ l : HeppLeaf t,
          ((leafMultiplicity mu l).factorial : ℝ)) *
          wordSum (M := p.total) p.toNat
            (primitiveSeparatedChainWeight z) :=
    mul_le_mul_of_nonneg_left hprofileWords hledgerNonneg
  have hledgerPaper :
      (∏ l : HeppLeaf t,
          ((leafMultiplicity mu l).factorial : ℝ)) *
          wordSum (M := p.total) p.toNat
            (primitiveSeparatedChainWeight z) =
        mergeLedgerRatio
            (leafMultiplicity mu) p.toNat *
          paperSum (M := p.total) p.toNat
            (primitiveSeparatedChainWeight z) := by
    exact
      (mergeLedgerRatio_mul_paperSum
        (M := p.total)
        (leafMultiplicity mu) p.toNat
        (primitiveSeparatedChainWeight z)).symm
  have hratioNonneg :
      0 ≤ mergeLedgerRatio
        (leafMultiplicity mu) p.toNat :=
    mergeLedgerRatio_nonneg _ _
  have hP59scaled :
      mergeLedgerRatio
            (leafMultiplicity mu) p.toNat *
          paperSum (M := p.total) p.toNat
            (primitiveSeparatedChainWeight z) ≤
        mergeLedgerRatio
            (leafMultiplicity mu) p.toNat *
          inductiveRHS C0 D (mergedWordList w₀.1).length
            t Nm mu' ∅ := by
    apply mul_le_mul_of_nonneg_left
    · rw [hprofileTotal, hprofileMultiplicity]
      exact hP59
    · exact hratioNonneg
  have hRHS :=
    mergeLedgerRatio_mul_inductiveRHS_le
      (C0 := C0) (D := D)
      (le_trans (by norm_num) hinductive.1.le)
      (by
        rw [hinductive.2.1]
        positivity)
      ht hroot Nm mu w₀.1 hvalid hprimitive htotal
  have hm :
      (mergedWordList w₀.1).length ≤ 2 * n :=
    mergedWordList_length_le w₀.1
  have hC0one : 1 ≤ C0 := by linarith [hinductive.1]
  have htargetNonneg :
      0 ≤
        D ^ (BranchNodes t).card *
          (4 : ℝ) ^ n *
          ∑ W ∈ (nonrootBranches t).powerset,
            permSumSummand n Nm mu W := by
    have hDpos : 0 < D := by
      rw [hinductive.2.1]
      positivity
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hDpos.le _) (by positivity))
      (sum_permSumSummand_nonneg n Nm mu)
  have huniform :
      C0 ^ (mergedWordList w₀.1).length *
          D ^ (BranchNodes t).card *
          (4 : ℝ) ^ n *
          ∑ W ∈ (nonrootBranches t).powerset,
            permSumSummand n Nm mu W ≤
        C0 ^ (2 * n) *
          D ^ (BranchNodes t).card *
          (4 : ℝ) ^ n *
          ∑ W ∈ (nonrootBranches t).powerset,
            permSumSummand n Nm mu W := by
    calc
      C0 ^ (mergedWordList w₀.1).length *
            D ^ (BranchNodes t).card *
            (4 : ℝ) ^ n *
            ∑ W ∈ (nonrootBranches t).powerset,
              permSumSummand n Nm mu W =
          C0 ^ (mergedWordList w₀.1).length *
            (D ^ (BranchNodes t).card *
              (4 : ℝ) ^ n *
              ∑ W ∈ (nonrootBranches t).powerset,
                permSumSummand n Nm mu W) := by ring
      _ ≤ C0 ^ (2 * n) *
            (D ^ (BranchNodes t).card *
              (4 : ℝ) ^ n *
              ∑ W ∈ (nonrootBranches t).powerset,
                permSumSummand n Nm mu W) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hC0one hm) htargetNonneg
      _ = C0 ^ (2 * n) *
            D ^ (BranchNodes t).card *
            (4 : ℝ) ^ n *
            ∑ W ∈ (nonrootBranches t).powerset,
              permSumSummand n Nm mu W := by ring
  calc
    (∑ q ∈
        (mergeProfileOutcomeImage
          (leafMultiplicity mu)
          (primitiveMergeWordFamily
            (M := 2 * n) (leafMultiplicity mu))).filter
            (fun q => q.1 = p),
      (∏ l : HeppLeaf t,
        ((leafMultiplicity mu l).factorial : ℝ)) *
        heppChainWeight z (listWord q.2)) =
        (∏ l : HeppLeaf t,
          ((leafMultiplicity mu l).factorial : ℝ)) *
          ∑ q :
            ↥(primitiveProfileOutcomeFiber
              (M := 2 * n) (leafMultiplicity mu) p),
            heppChainWeight z (listWord q.1.2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_subtype
      intro q
      rfl
    _ ≤
        (∏ l : HeppLeaf t,
          ((leafMultiplicity mu l).factorial : ℝ)) *
          wordSum (M := p.total) p.toNat
            (primitiveSeparatedChainWeight z) :=
      hscaledWords
    _ =
        mergeLedgerRatio
            (leafMultiplicity mu) p.toNat *
          paperSum (M := p.total) p.toNat
            (primitiveSeparatedChainWeight z) :=
      hledgerPaper
    _ ≤
        mergeLedgerRatio
            (leafMultiplicity mu) p.toNat *
          inductiveRHS C0 D (mergedWordList w₀.1).length
            t Nm mu' ∅ :=
      hP59scaled
    _ ≤
        C0 ^ (mergedWordList w₀.1).length *
          D ^ (BranchNodes t).card *
          (4 : ℝ) ^ n *
          ∑ W ∈ (nonrootBranches t).powerset,
            permSumSummand n Nm mu W := by
      simpa [mu', hprofileMultiplicity] using hRHS
    _ ≤
        C0 ^ (2 * n) *
          D ^ (BranchNodes t).card *
          (4 : ℝ) ^ n *
          ∑ W ∈ (nonrootBranches t).powerset,
            permSumSummand n Nm mu W :=
      huniform

/-- **Proposition 5.7 / (5.15).** -/
theorem permSum_estimate :
    ∃ C : ℝ, PermSumEstimate C := by
  obtain ⟨C0, D, hinductive⟩ := inductive_estimate
  let C : ℝ := mergeGlobalConstant C0 D
  refine ⟨C, ?_⟩
  unfold PermSumEstimate
  refine ⟨lt_of_lt_of_le zero_lt_one
    (one_le_mergeGlobalConstant C0 D), ?_⟩
  intro n R t Nm mu z hn ht hroot htotal _heven hadmissible
  let L : ℝ :=
    ∏ l : HeppLeaf t,
      ((leafMultiplicity mu l).factorial : ℝ)
  let target : ℝ :=
    ∑ W ∈ (nonrootBranches t).powerset,
      permSumSummand n Nm mu W
  let B : ℝ :=
    C0 ^ (2 * n) *
      D ^ (BranchNodes t).card *
      (4 : ℝ) ^ n * target
  have hsumMultiplicity :
      (∑ l : HeppLeaf t, leafMultiplicity mu l) = 2 * n := by
    exact htotal
  have hB : 0 ≤ B := by
    have hC0 : 0 ≤ C0 := by linarith [hinductive.1]
    have hD : 0 ≤ D := by
      rw [hinductive.2.1]
      positivity
    have htarget : 0 ≤ target :=
      sum_permSumSummand_nonneg n Nm mu
    dsimp only [B]
    positivity
  have hregroup :=
    primitive_merge_regroup_le_four_pow
      (M := 2 * n) (leafMultiplicity mu)
      hsumMultiplicity
      (fun q =>
        L * heppChainWeight z (listWord q.2))
      B hB
      (fun q hq => by
        exact mul_nonneg
          (by
            dsimp only [L]
            positivity)
          (heppChainWeight_nonneg z (listWord q.2)))
      (fun p hp =>
        primitiveProfileFiber_le_uniformTarget
          hinductive ht hroot Nm mu z hadmissible
          htotal p hp)
  have hconstants :
      C0 ^ (2 * n) *
          D ^ (BranchNodes t).card *
          (64 : ℝ) ^ n ≤
        C ^ n := by
    exact mergeGlobalConstant_absorbs_tree_sixtyFour
      ht hroot mu C0 D hinductive.1 hinductive.2.1
      n (2 * n) htotal le_rfl
  have htargetNonneg : 0 ≤ target :=
    sum_permSumSummand_nonneg n Nm mu
  have hmergePowers :
      (4 : ℝ) ^ (2 * n) * (4 : ℝ) ^ n =
        (64 : ℝ) ^ n := by
    calc
      (4 : ℝ) ^ (2 * n) * (4 : ℝ) ^ n =
          (4 : ℝ) ^ (2 * n + n) := by rw [pow_add]
      _ = (4 : ℝ) ^ (3 * n) := by
        congr 1
        omega
      _ = ((4 : ℝ) ^ 3) ^ n := by rw [pow_mul]
      _ = (64 : ℝ) ^ n := by norm_num
  calc
    paperSum (M := 2 * n) (leafMultiplicity mu)
          (primitiveChainWeight z) =
        ∑ w ∈ primitiveMergeWordFamily
            (M := 2 * n) (leafMultiplicity mu),
          L *
            heppChainWeight z
              (listWord
                (mergedProfileOutcome
                  (leafMultiplicity mu) w).2) := by
      exact
        paperSum_primitiveChainWeight_eq_primitiveMergeWordFamily
          mu z
    _ ≤ (4 : ℝ) ^ (2 * n) * B := hregroup
    _ =
        (C0 ^ (2 * n) *
          D ^ (BranchNodes t).card *
          (64 : ℝ) ^ n) * target := by
      dsimp only [B]
      calc
        (4 : ℝ) ^ (2 * n) *
            (C0 ^ (2 * n) *
              D ^ (BranchNodes t).card *
              (4 : ℝ) ^ n * target) =
            (C0 ^ (2 * n) *
              D ^ (BranchNodes t).card *
              ((4 : ℝ) ^ (2 * n) * (4 : ℝ) ^ n)) *
              target := by ring
        _ = _ := by rw [hmergePowers]
    _ ≤ C ^ n * target :=
      mul_le_mul_of_nonneg_right hconstants htargetNonneg
    _ = permSumRHS C n t Nm mu := by
      exact (permSumRHS_eq_factored C n t Nm mu).symm

end

end Anderson4D
