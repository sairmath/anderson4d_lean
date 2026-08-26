import Anderson4D.DetParametrix.Core.ResidualCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324MarkerPreservingResidualCollapse

/-!
# Every cross-cut primitive block carries a cross pair

Paper: R-324 — §4.2 Step 3, the nested blocks straddle the cut

Paper §4.2 Step 3(b) proves that every surviving fully paired subinterval
of `κ₀` contains `{p, p+1}`, i.e. straddles the cut between the two copies.
The blocks of the nested cross schedule therefore all satisfy
`R324CrossCutCarrier`.

This module records the elementary consequence that the schedule needs: a
block which straddles the cut, is fully paired, and is *relatively
primitive* must actually pair some site below the cut to a site above it.
Without that, the part below the cut would be a proper fully paired
relative subinterval, which relative primitivity forbids.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- **A cross-cut, fully paired, relatively primitive block pairs across
the cut.**

The part of `B` below the cut is a relative interval — it is `relIcc B a b`
for `a` the least element of `B` and `b` the greatest element below the cut
— so if it were closed under the pairing it would be a proper fully paired
relative subinterval of `B`, contradicting `IsRelPrimitiveOn`. -/
theorem exists_cross_pair_of_crossCut_primitive
    {m : ℕ} (κ : PartialPairing (Fin (2 * m)))
    (B : Finset (Fin (2 * m)))
    (hfull : IsFullyPairedOn κ B)
    (hprim : IsRelPrimitiveOn κ B)
    {l r : Fin (2 * m)} (hl : l ∈ B) (hr : r ∈ B)
    (hlm : (l : ℕ) < m) (hrm : m ≤ (r : ℕ)) :
    ∃ i ∈ B, (i : ℕ) < m ∧ m ≤ ((κ i : Fin (2 * m)) : ℕ) := by
  classical
  by_contra hno
  have hno' : ∀ i ∈ B, (i : ℕ) < m → ((κ i : Fin (2 * m)) : ℕ) < m := by
    intro i hi him
    by_contra hge
    exact hno ⟨i, hi, him, not_lt.mp hge⟩
  -- the part of `B` below the cut
  have hLne : (B.filter fun i : Fin (2 * m) => (i : ℕ) < m).Nonempty :=
    ⟨l, Finset.mem_filter.mpr ⟨hl, hlm⟩⟩
  have hBne : B.Nonempty := ⟨l, hl⟩
  have hbL : (B.filter fun i : Fin (2 * m) => (i : ℕ) < m).max' hLne ∈
      B.filter fun i : Fin (2 * m) => (i : ℕ) < m :=
    Finset.max'_mem _ hLne
  obtain ⟨hbB, hbm⟩ := Finset.mem_filter.mp hbL
  have haB : B.min' hBne ∈ B := Finset.min'_mem _ hBne
  have hab : B.min' hBne ≤
      (B.filter fun i : Fin (2 * m) => (i : ℕ) < m).max' hLne :=
    Finset.min'_le _ _ hbB
  -- the relative interval `[min B, max L]` of `B` is exactly `L`
  have hrelL :
      relIcc B (B.min' hBne)
          ((B.filter fun i : Fin (2 * m) => (i : ℕ) < m).max' hLne) =
        B.filter fun i : Fin (2 * m) => (i : ℕ) < m := by
    ext i
    rw [mem_relIcc, Finset.mem_filter]
    constructor
    · rintro ⟨hiB, _, hib⟩
      refine ⟨hiB, lt_of_le_of_lt ?_ hbm⟩
      exact_mod_cast hib
    · rintro ⟨hiB, him⟩
      exact ⟨hiB, Finset.min'_le _ _ hiB,
        Finset.le_max' _ i (Finset.mem_filter.mpr ⟨hiB, him⟩)⟩
  -- under the assumption, that relative interval is closed under `κ`
  have hLfull :
      IsFullyPairedOn κ
        (relIcc B (B.min' hBne)
          ((B.filter fun i : Fin (2 * m) => (i : ℕ) < m).max' hLne)) := by
    rw [hrelL]
    refine ⟨fun i hi => hfull.1 i (Finset.mem_filter.mp hi).1, fun i hi => ?_⟩
    obtain ⟨hiB, him⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hfull.2 i hiB, hno' i hiB him⟩
  -- relative primitivity forces `L = B`, which the right witness denies
  have hEq :
      relIcc B (B.min' hBne)
          ((B.filter fun i : Fin (2 * m) => (i : ℕ) < m).max' hLne) = B :=
    hprim _ _ ⟨haB, hbB, hab, hLfull⟩
  rw [hrelL] at hEq
  have hrL : r ∈ B.filter fun i : Fin (2 * m) => (i : ℕ) < m := by
    rw [hEq]; exact hr
  have hrlt : (r : ℕ) < m := (Finset.mem_filter.mp hrL).2
  omega

/-- A site below the cut whose partner is above it is the left copy of a
*single* of the left half: within-copy pairs stay below the cut. -/
theorem exists_leftSingle_of_cross_pair
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    {i : Fin (2 * m)} (him : (i : ℕ) < m)
    (hcross :
      m ≤ ((momentCombinedPairing κp κm π i : Fin (2 * m)) : ℕ)) :
    ∃ j : Fin m, ∃ _ : j ∈ κp.singles, leftMomentIndex j = i := by
  classical
  refine ⟨⟨(i : ℕ), him⟩, ?_, ?_⟩
  · by_contra hj
    have hpair :=
      momentCombinedPairing_left_pair κp κm π ⟨(i : ℕ), him⟩ hj
    have hli : leftMomentIndex (⟨(i : ℕ), him⟩ : Fin m) = i := by
      apply Fin.ext; rfl
    rw [hli] at hpair
    rw [hpair] at hcross
    have : ((leftMomentIndex (κp ⟨(i : ℕ), him⟩) : Fin (2 * m)) : ℕ) < m :=
      (κp ⟨(i : ℕ), him⟩).isLt
    omega
  · apply Fin.ext; rfl

/-- **Every block of the nested cross schedule is the marked block of some
residual covariance slot.**

Combining the two previous lemmas with the uniqueness in
`existsUnique_residualBlock_mem_of_marked`: a cross-cut, fully paired,
relatively primitive block contains a cross pair, hence the left copy of a
single of the left half, and that single's marked block is the block
itself. -/
theorem exists_selected_markedBlock_eq
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    {B : Finset (Fin (2 * m))}
    (hmem : B ∈ nonemptyMomentResidualCollapseBlocks κp κm π)
    (hfull : IsFullyPairedOn (momentCombinedPairing κp κm π) B)
    (hprim : IsRelPrimitiveOn (momentCombinedPairing κp κm π) B)
    {l r : Fin (2 * m)} (hl : l ∈ B) (hr : r ∈ B)
    (hlm : (l : ℕ) < m) (hrm : m ≤ (r : ℕ)) :
    ∃ selected : R324ResidualCovarianceSlot κp,
      r324MarkedResidualBlock κp κm π selected = B := by
  classical
  obtain ⟨i, hiB, him, hcross⟩ :=
    exists_cross_pair_of_crossCut_primitive
      (momentCombinedPairing κp κm π) B hfull hprim hl hr hlm hrm
  obtain ⟨j, hj, hji⟩ :=
    exists_leftSingle_of_cross_pair κp κm π him hcross
  refine ⟨⟨j, hj⟩, ?_⟩
  have hlow :
      r324ResidualMarkedLowerEndpoint (κp := κp) ⟨j, hj⟩ ∈ B := by
    change leftMomentIndex j ∈ B
    rw [hji]
    exact hiB
  exact
    (existsUnique_residualBlock_mem_of_marked κp κm π ⟨j, hj⟩).unique
      ⟨r324MarkedResidualBlock_mem κp κm π ⟨j, hj⟩,
        r324ResidualMarkedLowerEndpoint_mem_markedBlock κp κm π ⟨j, hj⟩⟩
      ⟨hmem, hlow⟩

end Anderson4D
