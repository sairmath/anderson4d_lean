import Anderson4D.DetParametrix.Paper42_Moment.R324BlockCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324ProjectedCovariance

/-!
# Fourier configurations of an R-324 covariance product

For one full doubled pairing, the covariance part of the deterministic
moment integrand is a finite product of cutoff covariances.  This file
expands that product as one absolutely convergent `tsum` over a finite
assignment of lattice modes.  It is the concrete Fourier-configuration
space used in paper §4.2, Step 4.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- The lower endpoints used to count every pair exactly once. -/
abbrev R324PairIndex
    {m : ℕ} (κ : PartialPairing (Fin (2 * m))) :=
  {i : Fin (2 * m) //
    i ∈ κ.pairSupport.filter (fun j => j < κ j)}

/-- A deterministic enumeration of the lower endpoints of a pairing. -/
def r324PairFinEquiv
    {m : ℕ} (κ : PartialPairing (Fin (2 * m))) :
    Fin (κ.pairSupport.filter (fun j => j < κ j)).card ≃
      R324PairIndex κ :=
  (κ.pairSupport.filter (fun j => j < κ j)).equivFin.symm

/-- The covariance Fourier mode attached to one enumerated pair. -/
def r324PairModeTerm
    {m : ℕ} (ε : ℝ)
    (κ : PartialPairing (Fin (2 * m)))
    (v : Fin (2 * m) → T4)
    (j : Fin (κ.pairSupport.filter (fun i => i < κ i)).card)
    (k : Z4) : ℂ :=
  let i := (r324PairFinEquiv κ j).1
  ρ.r324CovarianceModeTerm ε (v i - v (κ i)) k

/-- One Fourier configuration of a complete covariance product. -/
def r324CovarianceFourierConfigurationTerm
    {m : ℕ} (ε : ℝ)
    (κ : PartialPairing (Fin (2 * m)))
    (v : Fin (2 * m) → T4)
    (q :
      Fin (κ.pairSupport.filter (fun i => i < κ i)).card → Z4) :
    ℂ :=
  finSeriesAssignmentTerm
    (κ.pairSupport.filter (fun i => i < κ i)).card
    (ρ.r324PairModeTerm ε κ v) q

/-- Every individual pair-mode series is absolutely convergent. -/
theorem summable_norm_r324PairModeTerm
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (κ : PartialPairing (Fin (2 * m)))
    (v : Fin (2 * m) → T4)
    (j : Fin (κ.pairSupport.filter (fun i => i < κ i)).card) :
    Summable fun k : Z4 =>
      ‖ρ.r324PairModeTerm ε κ v j k‖ := by
  unfold r324PairModeTerm
  exact
    (ρ.summable_r324CovarianceModeTerm hε
      (v (r324PairFinEquiv κ j).1 -
        v (κ (r324PairFinEquiv κ j).1))).norm

/-- The full configuration series is absolutely convergent. -/
theorem summable_norm_r324CovarianceFourierConfigurationTerm
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (κ : PartialPairing (Fin (2 * m)))
    (v : Fin (2 * m) → T4) :
    Summable fun q =>
      ‖ρ.r324CovarianceFourierConfigurationTerm ε κ v q‖ := by
  exact summable_norm_finSeriesAssignmentTerm
    (κ.pairSupport.filter (fun i => i < κ i)).card
    (ρ.r324PairModeTerm ε κ v)
    (ρ.summable_norm_r324PairModeTerm hε κ v)

/-- In particular the complex configuration series is summable. -/
theorem summable_r324CovarianceFourierConfigurationTerm
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (κ : PartialPairing (Fin (2 * m)))
    (v : Fin (2 * m) → T4) :
    Summable
      (ρ.r324CovarianceFourierConfigurationTerm ε κ v) :=
  Summable.of_norm
    (ρ.summable_norm_r324CovarianceFourierConfigurationTerm
      hε κ v)

/-- Exact Fourier expansion of every covariance factor in a doubled
pairing.  No Fubini across physical integration is used here: this is a
pointwise, absolutely convergent identity. -/
theorem primitiveCovarianceProduct_eq_r324_configuration_tsum
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (κ : PartialPairing (Fin (2 * m)))
    (v : Fin (2 * m) → T4) :
    (primitiveCovarianceProduct ρ ε m κ v : ℂ) =
      ∑' q,
        ρ.r324CovarianceFourierConfigurationTerm ε κ v q := by
  let A : Finset (Fin (2 * m)) :=
    κ.pairSupport.filter (fun i => i < κ i)
  let e : Fin A.card ≃ {i : Fin (2 * m) // i ∈ A} :=
    A.equivFin.symm
  have hseries :
      ∀ j : Fin A.card,
        Summable fun k : Z4 =>
          ‖ρ.r324CovarianceModeTerm ε
            (v (e j).1 - v (κ (e j).1)) k‖ := by
    intro j
    exact
      (ρ.summable_r324CovarianceModeTerm hε
        (v (e j).1 - v (κ (e j).1))).norm
  calc
    (primitiveCovarianceProduct ρ ε m κ v : ℂ) =
        ∏ i : {i : Fin (2 * m) // i ∈ A},
          (ρ.etaEpsT4 ε (v i.1 - v (κ i.1)) : ℂ) := by
      unfold primitiveCovarianceProduct
      change
        ((∏ i ∈ A,
          ρ.etaEpsT4 ε (v i - v (κ i))) : ℝ) =
          ∏ i : {i : Fin (2 * m) // i ∈ A},
            (ρ.etaEpsT4 ε (v i.1 - v (κ i.1)) : ℂ)
      push_cast
      exact
        (Finset.prod_coe_sort A
          (fun i =>
            (ρ.etaEpsT4 ε (v i - v (κ i)) : ℂ))).symm
    _ = ∏ i : {i : Fin (2 * m) // i ∈ A},
          ∑' k : Z4,
            ρ.r324CovarianceModeTerm ε
              (v i.1 - v (κ i.1)) k := by
      apply Fintype.prod_congr
      intro i
      exact
        (ρ.complexFourierCovarianceT4_eq_etaEpsT4
          hε (v i.1 - v (κ i.1))).symm
    _ = ∏ j : Fin A.card,
          ∑' k : Z4,
            ρ.r324CovarianceModeTerm ε
              (v (e j).1 - v (κ (e j).1)) k := by
      exact
        (e.prod_comp
          (fun i : {i : Fin (2 * m) // i ∈ A} =>
            ∑' k : Z4,
              ρ.r324CovarianceModeTerm ε
                (v i.1 - v (κ i.1)) k)).symm
    _ = ∑' q : Fin A.card → Z4,
          finSeriesAssignmentTerm A.card
            (fun j k =>
              ρ.r324CovarianceModeTerm ε
                (v (e j).1 - v (κ (e j).1)) k) q := by
      exact
        (tsum_finSeriesAssignmentTerm A.card
          (fun j k =>
            ρ.r324CovarianceModeTerm ε
              (v (e j).1 - v (κ (e j).1)) k)
          hseries).symm
    _ = ∑' q,
          ρ.r324CovarianceFourierConfigurationTerm ε κ v q := by
      apply tsum_congr
      intro q
      rfl

end SmoothCutoff

end

end Anderson4D
