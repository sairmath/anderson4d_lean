import Anderson4D.DetParametrix.Core.FinalBound
import Anderson4D.DetParametrix.Paper42_Moment.R324ProjectedCovariance

/-!
# A single projected residual covariance slot for R-324

This file isolates the safe algebraic and counting part of paper
Section 4.2, Step 4.

The residual covariance slots are the cross-copy factors already present
in `momentCrossCovarianceProduct`.  A single marked slot is replaced by
`r324ProjectedCovarianceC`; every other slot remains the complete spatial
covariance `etaEpsT4`.  In particular, this file never replaces the whole
covariance product by a configuration in which every Fourier mode is
fixed.

There is intentionally no theorem here identifying the original R-324
moment with the single-projected series.  That later bridge must be proved
from the post-phase-A residual expansion and its frequency-conservation
identity.  The declarations below provide only:

* the exact first large-increment selector;
* its coverage of every routed nonzero configuration;
* the concrete one-slot covariance replacement; and
* the triangle/counting bound for an already constructed summable family
  of one-slot projected terms.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## The first large increment -/

/-- The slots which meet the truncation-scale routing threshold. -/
def r324LargeResidualIncrementSlots
    {E : Type*} [SeminormedAddCommGroup E]
    {N : ℕ} (ε : ℝ) (δ : Fin N → E) :
    Finset (Fin N) :=
  Finset.univ.filter fun i =>
    (Real.sqrt ε / 2) * ‖∑ j, δ j‖ ≤ ‖δ i‖

/-- At least one slot meets the truncation-scale threshold. -/
theorem r324LargeResidualIncrementSlots_nonempty
    {E : Type*} [SeminormedAddCommGroup E]
    {N : ℕ} (hN : 0 < N)
    (δ : Fin N → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hNtrunc : N ≤ truncOrder ε) :
    (r324LargeResidualIncrementSlots ε δ).Nonempty := by
  obtain ⟨i, hi⟩ :=
    exists_frequency_increment_at_truncation_scale
      N hN δ ε hε hε1 hNtrunc
  exact
    ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, hi⟩⟩

/-- The canonical routed slot is the least slot satisfying the large
increment condition.  Choosing the least slot makes the later fibres
disjoint and avoids paying for the same configuration more than once. -/
def r324FirstLargeResidualIncrementSlot
    {E : Type*} [SeminormedAddCommGroup E]
    {N : ℕ} (hN : 0 < N)
    (δ : Fin N → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hNtrunc : N ≤ truncOrder ε) :
    Fin N :=
  (r324LargeResidualIncrementSlots ε δ).min'
    (r324LargeResidualIncrementSlots_nonempty
      hN δ hε hε1 hNtrunc)

theorem r324FirstLargeResidualIncrementSlot_mem
    {E : Type*} [SeminormedAddCommGroup E]
    {N : ℕ} (hN : 0 < N)
    (δ : Fin N → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hNtrunc : N ≤ truncOrder ε) :
    r324FirstLargeResidualIncrementSlot
        hN δ hε hε1 hNtrunc ∈
      r324LargeResidualIncrementSlots ε δ := by
  exact Finset.min'_mem _ _

/-- The selected slot has the required large increment. -/
theorem r324FirstLargeResidualIncrementSlot_spec
    {E : Type*} [SeminormedAddCommGroup E]
    {N : ℕ} (hN : 0 < N)
    (δ : Fin N → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hNtrunc : N ≤ truncOrder ε) :
    (Real.sqrt ε / 2) * ‖∑ j, δ j‖ ≤
      ‖δ (r324FirstLargeResidualIncrementSlot
        hN δ hε hε1 hNtrunc)‖ := by
  exact
    (Finset.mem_filter.mp
      (r324FirstLargeResidualIncrementSlot_mem
        hN δ hε hε1 hNtrunc)).2

/-- The selector really is the first large slot. -/
theorem r324FirstLargeResidualIncrementSlot_le
    {E : Type*} [SeminormedAddCommGroup E]
    {N : ℕ} (hN : 0 < N)
    (δ : Fin N → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hNtrunc : N ≤ truncOrder ε)
    (i : Fin N)
    (hi :
      (Real.sqrt ε / 2) * ‖∑ j, δ j‖ ≤ ‖δ i‖) :
    r324FirstLargeResidualIncrementSlot
        hN δ hε hε1 hNtrunc ≤ i := by
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩

/-- Frequency conservation rewrites the selected-slot bound in terms of
the external shift. -/
theorem r324FirstLargeResidualIncrementSlot_spec_of_sum
    {E : Type*} [SeminormedAddCommGroup E]
    {N : ℕ} (hN : 0 < N)
    (δ : Fin N → E) (external : E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hNtrunc : N ≤ truncOrder ε)
    (hsum : (∑ j, δ j) = external) :
    (Real.sqrt ε / 2) * ‖external‖ ≤
      ‖δ (r324FirstLargeResidualIncrementSlot
        hN δ hε hε1 hNtrunc)‖ := by
  simpa only [hsum] using
    r324FirstLargeResidualIncrementSlot_spec
      hN δ hε hε1 hNtrunc

/-- The configurations relevant to a routed series. -/
abbrev R324NonzeroResidualConfiguration
    {Ω : Type*} (term : Ω → ℂ) :=
  {ω : Ω // term ω ≠ 0}

/-- Every nonzero routed configuration is covered by its canonical
selected slot.  The statement is stronger than needed analytically:
the selector exists for zero terms too, but the subtype records the exact
consumer boundary. -/
theorem r324NonzeroResidualConfiguration_selectedSlot_spec
    {E Ω : Type*} [SeminormedAddCommGroup E]
    {N : ℕ} (hN : 0 < N)
    (term : Ω → ℂ)
    (increment : Ω → Fin N → E)
    (external : E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hNtrunc : N ≤ truncOrder ε)
    (hsum : ∀ ω, (∑ j, increment ω j) = external)
    (ω : R324NonzeroResidualConfiguration term) :
    (Real.sqrt ε / 2) * ‖external‖ ≤
      ‖increment ω.1
        (r324FirstLargeResidualIncrementSlot
          hN (increment ω.1) hε hε1 hNtrunc)‖ := by
  exact
    r324FirstLargeResidualIncrementSlot_spec_of_sum
      hN (increment ω.1) external hε hε1 hNtrunc
      (hsum ω.1)

/-! ## The existing residual covariance slots -/

/-- After the within-half phase-A collapses, the remaining covariance
slots are indexed by the left singles and paired across the cut by `π`. -/
abbrev R324ResidualCovarianceSlot
    {m : ℕ} (κp : PartialPairing (Fin m)) :=
  ↥κp.singles

/-- Standard finite enumeration of the residual cross-covariance slots. -/
def r324ResidualCovarianceSlotEquiv
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    Fin κp.singles.card ≃ R324ResidualCovarianceSlot κp :=
  κp.singles.equivFin.symm

theorem card_r324ResidualCovarianceSlot
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    Fintype.card (R324ResidualCovarianceSlot κp) =
      κp.singles.card := by
  rw [← Fintype.card_fin κp.singles.card]
  exact
    (Fintype.card_congr
      (r324ResidualCovarianceSlotEquiv κp)).symm

/-- There are at most `m` residual covariance slots. -/
theorem card_r324ResidualCovarianceSlot_le
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    Fintype.card (R324ResidualCovarianceSlot κp) ≤ m := by
  rw [card_r324ResidualCovarianceSlot]
  simpa using Finset.card_le_univ κp.singles

/-- Spatial displacement carried by one residual cross covariance. -/
def r324ResidualCovarianceDisplacement
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4)
    (i : R324ResidualCovarianceSlot κp) : T4 :=
  v (leftMomentIndex i.1) -
    v (rightMomentIndex (π i).1)

/-- Replace exactly one residual covariance factor by its high-frequency
projection.  Every unselected factor is literally the complete
`etaEpsT4` covariance. -/
def SmoothCutoff.r324SingleProjectedResidualCovarianceFactor
    {m : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4)
    (selected i : R324ResidualCovarianceSlot κp) : ℂ :=
  if i = selected then
    ρ.r324ProjectedCovarianceC ε L
      (r324ResidualCovarianceDisplacement κp κm π v i)
  else
    (ρ.etaEpsT4 ε
      (r324ResidualCovarianceDisplacement κp κm π v i) : ℂ)

@[simp]
theorem SmoothCutoff.r324SingleProjectedResidualCovarianceFactor_selected
    {m : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4)
    (selected : R324ResidualCovarianceSlot κp) :
    ρ.r324SingleProjectedResidualCovarianceFactor
        ε L κp κm π v selected selected =
      ρ.r324ProjectedCovarianceC ε L
        (r324ResidualCovarianceDisplacement
          κp κm π v selected) := by
  simp [SmoothCutoff.r324SingleProjectedResidualCovarianceFactor]

@[simp]
theorem SmoothCutoff.r324SingleProjectedResidualCovarianceFactor_other
    {m : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4)
    (selected i : R324ResidualCovarianceSlot κp)
    (hi : i ≠ selected) :
    ρ.r324SingleProjectedResidualCovarianceFactor
        ε L κp κm π v selected i =
      (ρ.etaEpsT4 ε
        (r324ResidualCovarianceDisplacement
          κp κm π v i) : ℂ) := by
  simp [SmoothCutoff.r324SingleProjectedResidualCovarianceFactor,
    hi]

/-- The residual product with one and only one projected covariance. -/
def SmoothCutoff.r324SingleProjectedResidualCovarianceProduct
    {m : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4)
    (selected : R324ResidualCovarianceSlot κp) : ℂ :=
  ∏ i : R324ResidualCovarianceSlot κp,
    ρ.r324SingleProjectedResidualCovarianceFactor
      ε L κp κm π v selected i

/-- Explicit factorization: the selected projected covariance times the
product of all complete unselected `etaEpsT4` factors. -/
theorem SmoothCutoff.r324SingleProjectedResidualCovarianceProduct_eq
    {m : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4)
    (selected : R324ResidualCovarianceSlot κp) :
    ρ.r324SingleProjectedResidualCovarianceProduct
        ε L κp κm π v selected =
      ρ.r324ProjectedCovarianceC ε L
          (r324ResidualCovarianceDisplacement
            κp κm π v selected) *
        ∏ i ∈
            (Finset.univ :
              Finset (R324ResidualCovarianceSlot κp)).erase selected,
          (ρ.etaEpsT4 ε
            (r324ResidualCovarianceDisplacement
              κp κm π v i) : ℂ) := by
  classical
  unfold SmoothCutoff.r324SingleProjectedResidualCovarianceProduct
  rw [← Finset.mul_prod_erase
    (Finset.univ :
      Finset (R324ResidualCovarianceSlot κp))
    (fun i =>
      ρ.r324SingleProjectedResidualCovarianceFactor
        ε L κp κm π v selected i)
    (Finset.mem_univ selected)]
  rw [
    ρ.r324SingleProjectedResidualCovarianceFactor_selected]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact
    ρ.r324SingleProjectedResidualCovarianceFactor_other
      ε L κp κm π v selected i
      (Finset.ne_of_mem_erase hi)

/-! ## Countable grouping by the single selected slot -/

/-- Absolute mass of the fibre whose canonical projected slot is `i`. -/
def r324SingleProjectedSlotMass
    {Ω ι : Type*} [Fintype ι]
    (selected : Ω → ι) (term : Ω → ℂ)
    (i : ι) : ℝ :=
  ∑' ω : ↥(selected ⁻¹' ({i} : Set ι)), ‖term ω.1‖

theorem r324SingleProjectedSlotMass_nonneg
    {Ω ι : Type*} [Fintype ι]
    (selected : Ω → ι) (term : Ω → ℂ)
    (i : ι) :
    0 ≤ r324SingleProjectedSlotMass selected term i := by
  exact tsum_nonneg fun _ => norm_nonneg _

/-- A summable family of already constructed one-slot projected terms
costs only the finite sum over possible selected slots.  The fibres are
disjoint because `selected` is a function (in the routed application it
is the least-large-increment selector above). -/
theorem norm_tsum_le_sum_singleProjectedSlotMass
    {Ω ι : Type*} [Fintype ι]
    (selected : Ω → ι) (term : Ω → ℂ)
    (hterm : Summable term) :
    ‖∑' ω, term ω‖ ≤
      ∑ i : ι,
        r324SingleProjectedSlotMass selected term i := by
  have hfiber :
      HasSum
        (fun i : ι =>
          r324SingleProjectedSlotMass selected term i)
        (∑' ω, ‖term ω‖) := by
    simpa only [r324SingleProjectedSlotMass] using
      hterm.norm.hasSum.tsum_fiberwise selected
  calc
    ‖∑' ω, term ω‖ ≤ ∑' ω, ‖term ω‖ :=
      norm_tsum_le_tsum_norm hterm.norm
    _ = ∑' i : ι,
          r324SingleProjectedSlotMass selected term i :=
      hfiber.tsum_eq.symm
    _ = ∑ i : ι,
          r324SingleProjectedSlotMass selected term i := by
      rw [tsum_fintype]

/-- A concrete family in which each term has one projected residual
covariance and all other residual covariances remain complete `etaEpsT4`
factors. -/
def SmoothCutoff.r324SingleProjectedResidualTerm
    {Ω : Type*} {m : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (L : Ω → ℝ)
    (v : Ω → Fin (2 * m) → T4)
    (amplitude : Ω → ℂ)
    (selected : Ω → R324ResidualCovarianceSlot κp)
    (ω : Ω) : ℂ :=
  amplitude ω *
    ρ.r324SingleProjectedResidualCovarianceProduct
      ε (L ω) κp κm π (v ω) (selected ω)

/-- The concrete single-projected residual series is bounded by a sum
over at most `κp.singles.card ≤ m` slot fibres.  This theorem does not
claim that the original moment equals this series. -/
theorem SmoothCutoff.norm_tsum_r324SingleProjectedResidualTerm_le
    {Ω : Type*} {m : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (L : Ω → ℝ)
    (v : Ω → Fin (2 * m) → T4)
    (amplitude : Ω → ℂ)
    (selected : Ω → R324ResidualCovarianceSlot κp)
    (hterm :
      Summable
        (ρ.r324SingleProjectedResidualTerm
          ε κp κm π L v amplitude selected)) :
    ‖∑' ω,
        ρ.r324SingleProjectedResidualTerm
          ε κp κm π L v amplitude selected ω‖ ≤
      ∑ i : R324ResidualCovarianceSlot κp,
        r324SingleProjectedSlotMass selected
          (ρ.r324SingleProjectedResidualTerm
            ε κp κm π L v amplitude selected) i := by
  exact
    norm_tsum_le_sum_singleProjectedSlotMass
      selected
      (ρ.r324SingleProjectedResidualTerm
        ε κp κm π L v amplitude selected)
      hterm

end

end Anderson4D
