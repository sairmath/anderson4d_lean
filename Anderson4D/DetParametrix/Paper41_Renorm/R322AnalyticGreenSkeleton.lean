import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticSchedule
import Anderson4D.DetParametrix.Paper41_Renorm.R322BlockIntegrand

/-!
# Reordering the signed R-322 Green skeleton

The combinatorial extraction list and the analytic collapse schedule contain
the same endpoint intervals in different orders.  The closed-form Green
skeleton only uses the set of replaced right edges and the commutative product
of difference factors, so it is exactly invariant under this reordering.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The closed signed Green skeleton written in the paper's analytic
inside-to-outside order. -/
def r322AnalyticGreenSkeleton
    {n : ℕ} (κ : PartialPairing (Fin n))
    (x : Fin n → T4) : ℝ :=
  (∏ e : Fin (n - 1),
      if e.val ∈
          ((r322AnalyticSchedule κ).map
            (fun s => s.1.2.val)) then
        1
      else if h : e.val + 1 < n then
        greenFn
          (x ⟨e.val, by omega⟩ -
            x ⟨e.val + 1, h⟩)
      else
        1) *
    ((r322AnalyticSchedule κ).map
      (fun s => diffFactorJ x s.1)).prod

/-- Reordering the extraction intervals into analytic execution order does
not alter the signed Green/difference skeleton. -/
theorem r322AnalyticGreenSkeleton_eq_renormalized
    {n : ℕ} (κ : PartialPairing (Fin n))
    (x : Fin n → T4) :
    r322AnalyticGreenSkeleton κ x =
      renormalizedJGreenSkeleton κ x := by
  have hp :
      List.Perm
        ((r322AnalyticSchedule κ).map Prod.fst)
        (extract κ) :=
    r322AnalyticSchedule_endpoints_perm_extract κ
  have hright :
      List.Perm
        ((r322AnalyticSchedule κ).map
          (fun s => s.1.2.val))
        ((extract κ).map fun p => p.2.val) := by
    simpa only [List.map_map, Function.comp_def] using
      (hp.map fun p => p.2.val)
  have hdiff :
      ((r322AnalyticSchedule κ).map
          (fun s => diffFactorJ x s.1)).prod =
        ((extract κ).map (diffFactorJ x)).prod := by
    simpa only [List.map_map, Function.comp_def] using
      (hp.map (diffFactorJ x)).prod_eq
  unfold r322AnalyticGreenSkeleton
    renormalizedJGreenSkeleton
  rw [hdiff]
  congr 1
  apply Finset.prod_congr rfl
  intro e _he
  have hmem :
      e.val ∈
          ((r322AnalyticSchedule κ).map
            (fun s => s.1.2.val)) ↔
        e.val ∈ ((extract κ).map fun p => p.2.val) :=
    hright.mem_iff
  by_cases hm :
      e.val ∈
        ((r322AnalyticSchedule κ).map
          (fun s => s.1.2.val))
  · have hm' :
        e.val ∈ ((extract κ).map fun p => p.2.val) :=
      hmem.mp hm
    simp only [hm, hm', if_true]
  · have hm' :
        e.val ∉ ((extract κ).map fun p => p.2.val) := by
      exact fun h => hm (hmem.mpr h)
    simp only [hm, hm', if_false]

end

end Anderson4D
