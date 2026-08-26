import Anderson4D.PermSum.CollapseSkippedBranches

/-!
# Regrouping skipped-branch sets after collapse

For fixed `r` and `s`, the map `W ↦ liftWPrime r s W` embeds the contracted
non-root-branch powerset into the original one.  Consequently the induction
sum can be reindexed without a fibre-cardinality loss.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## Injectivity -/

/-- Mapping a finite set along the retained-vertex embedding is injective. -/
theorem liftContractFinset_injective
    {t : PlaneTree} {p : Pos} (hp : IsPos t p) :
    Function.Injective (liftContractFinset hp) := by
  intro W₁ W₂ h
  exact Finset.map_injective (contractVertexEmbedding hp) h

/-- On contracted non-root branch sets, `W ↦ W'` is injective.  In the
`s = 1` case the inserted vertex `r` can be erased because it is absent from
both lifted contracted sets. -/
theorem liftWPrime_injective_of_subset
    {t : PlaneTree} (r : VPos t) (s : ℕ)
    {W₁ W₂ : Finset (VPos (contractAt t r.1))}
    (hW₁ : W₁ ⊆ nonrootBranches (contractAt t r.1))
    (hW₂ : W₂ ⊆ nonrootBranches (contractAt t r.1))
    (h : liftWPrime r s W₁ = liftWPrime r s W₂) :
    W₁ = W₂ := by
  by_cases hs : s = 1
  · have hnot₁ :
        r ∉ liftContractFinset r.2 W₁ :=
      not_mem_liftContractFinset_of_subset_nonrootBranches r hW₁
    have hnot₂ :
        r ∉ liftContractFinset r.2 W₂ :=
      not_mem_liftContractFinset_of_subset_nonrootBranches r hW₂
    simp only [liftWPrime, hs, if_pos] at h
    have herase :=
      congrArg (fun U : Finset (VPos t) => U.erase r) h
    have hlift :
        liftContractFinset r.2 W₁ =
          liftContractFinset r.2 W₂ := by
      simpa [hnot₁, hnot₂] using herase
    exact liftContractFinset_injective r.2 hlift
  · simp only [liftWPrime, hs] at h
    exact liftContractFinset_injective r.2 h

/-- Set-theoretic injectivity on the contracted non-root powerset. -/
theorem liftWPrime_injOn_powerset
    {t : PlaneTree} (r : VPos t) (s : ℕ) :
    Set.InjOn (liftWPrime r s)
      (nonrootBranches (contractAt t r.1)).powerset := by
  intro W₁ hW₁ W₂ hW₂ h
  exact liftWPrime_injective_of_subset r s
    (Finset.mem_powerset.mp hW₁)
    (Finset.mem_powerset.mp hW₂) h

/-! ## Landing in the original powerset -/

/-- A contracted non-root branch subset maps to an original non-root branch
subset. -/
theorem liftWPrime_mem_original_powerset
    {t : PlaneTree} (r : VPos t)
    (hr : r ∈ nonrootBranches t) (s : ℕ)
    {W : Finset (VPos (contractAt t r.1))}
    (hW :
      W ∈ (nonrootBranches (contractAt t r.1)).powerset) :
    liftWPrime r s W ∈ (nonrootBranches t).powerset := by
  rw [Finset.mem_powerset]
  exact liftWPrime_subset_nonrootBranches r hr s
    (Finset.mem_powerset.mp hW)

/-- The image of the contracted powerset is contained in the original
powerset. -/
theorem image_liftWPrime_powerset_subset
    {t : PlaneTree} (r : VPos t)
    (hr : r ∈ nonrootBranches t) (s : ℕ) :
    (nonrootBranches (contractAt t r.1)).powerset.image
        (liftWPrime r s) ⊆
      (nonrootBranches t).powerset := by
  intro W' hW'
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hW'
  exact liftWPrime_mem_original_powerset r hr s hW

/-! ## Exact reindexing and the sum upper bound -/

/-- Exact reindexing onto the image; injectivity means there is no fibre
multiplicity. -/
theorem sum_liftWPrime_eq_sum_image
    {t : PlaneTree} (r : VPos t) (s : ℕ)
    (g : Finset (VPos t) → ℝ) :
    (∑ W ∈ (nonrootBranches (contractAt t r.1)).powerset,
        g (liftWPrime r s W)) =
      ∑ W' ∈
          (nonrootBranches (contractAt t r.1)).powerset.image
            (liftWPrime r s),
        g W' := by
  exact
    (Finset.sum_image (liftWPrime_injOn_powerset r s)).symm

/-- Generic no-fibre-loss regrouping bound.  Only the target summands need
to be nonnegative in order to enlarge the image to the full original
powerset; the source summands may be arbitrary. -/
theorem sum_contracted_powerset_le_sum_original_powerset
    {t : PlaneTree} (r : VPos t)
    (hr : r ∈ nonrootBranches t) (s : ℕ)
    (f : Finset (VPos (contractAt t r.1)) → ℝ)
    (g : Finset (VPos t) → ℝ)
    (hfg :
      ∀ W ∈ (nonrootBranches (contractAt t r.1)).powerset,
        f W ≤ g (liftWPrime r s W))
    (hg :
      ∀ W' ∈ (nonrootBranches t).powerset, 0 ≤ g W') :
    (∑ W ∈ (nonrootBranches (contractAt t r.1)).powerset,
        f W) ≤
      ∑ W' ∈ (nonrootBranches t).powerset, g W' := by
  calc
    (∑ W ∈ (nonrootBranches (contractAt t r.1)).powerset,
          f W) ≤
        ∑ W ∈ (nonrootBranches (contractAt t r.1)).powerset,
          g (liftWPrime r s W) := by
      exact Finset.sum_le_sum fun W hW => hfg W hW
    _ =
        ∑ W' ∈
            (nonrootBranches (contractAt t r.1)).powerset.image
              (liftWPrime r s),
          g W' :=
      sum_liftWPrime_eq_sum_image r s g
    _ ≤ ∑ W' ∈ (nonrootBranches t).powerset, g W' := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (image_liftWPrime_powerset_subset r hr s)
        (fun W' hW' _ => hg W' hW')

end
end Anderson4D
