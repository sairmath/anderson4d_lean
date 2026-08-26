import Anderson4D.DetParametrix.Paper42_Moment.R324FrequencyConservation

/-!
# Countable full-pairing configurations for R-324

A full pairing on the doubled `2m` carrier has exactly `m` covariance
pairs.  This file reindexes its dependent Fourier-assignment type by
`Fin m → ℤ⁴`, then by `ℕ` when `m > 0`.  It also defines the signed
Euclidean increments whose sum is the external shift on every nonzero
integrated configuration.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- A full pairing of the doubled carrier has exactly `m` lower pair
representatives. -/
theorem r324FullPairCardEq
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card = m :=
  card_primitiveCovarianceRepresentatives κ.1 κ.2

/-- Canonical cast between the standard `Fin m` pair index and the
dependent lower-endpoint enumeration. -/
def r324FullPairIndexEquiv
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    Fin m ≃
      Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card :=
  (Fin.castOrderIso (r324FullPairCardEq κ).symm).toEquiv

/-- Transport a standard `m`-tuple of lattice modes to the dependent
assignment type of the covariance expansion. -/
def r324FullConfigurationOfStandard
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) :
    Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card → Z4 :=
  q ∘ (r324FullPairIndexEquiv κ).symm

/-- Exact equivalence between standard and dependent full-pairing
configurations. -/
def r324FullConfigurationEquiv
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    (Fin m → Z4) ≃
      (Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card → Z4) :=
  Equiv.arrowCongr (r324FullPairIndexEquiv κ) (Equiv.refl Z4)

@[simp]
theorem r324FullConfigurationEquiv_apply
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) :
    r324FullConfigurationEquiv κ q =
      r324FullConfigurationOfStandard κ q := by
  rfl

/-! ## Signed Euclidean increments -/

/-- The lattice-to-Euclidean frequency map as an additive homomorphism. -/
def z4EuclideanFrequencyAddHom :
    Z4 →+ EuclideanSpace ℝ (Fin dim) where
  toFun := z4EuclideanFrequency
  map_zero' := by
    apply PiLp.ext
    intro i
    simp [z4EuclideanFrequency]
  map_add' k l := by
    apply PiLp.ext
    intro i
    simp [z4EuclideanFrequency]

/-- One signed pair contribution, with sign reversed so that the total
equals `α+β` rather than its negative. -/
def r324StandardPairIncrement
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) (i : Fin m) :
    EuclideanSpace ℝ (Fin dim) :=
  z4EuclideanFrequency
    (-r324LeftPairModeContribution κ.1
      (r324FullConfigurationOfStandard κ q)
      (r324FullPairIndexEquiv κ i))

/-- The standard increments telescope to the negative signed left-mode
sum before frequency conservation is imposed. -/
theorem sum_r324StandardPairIncrement
    {m : ℕ}
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4) :
    (∑ i, r324StandardPairIncrement κ q i) =
      z4EuclideanFrequency
        (-r324LeftModeSum κ.1
          (r324FullConfigurationOfStandard κ q)) := by
  let e := r324FullPairIndexEquiv κ
  let f :
      Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card →
        Z4 :=
    fun j =>
      r324LeftPairModeContribution κ.1
        (r324FullConfigurationOfStandard κ q) j
  have hsum :
      (∑ i : Fin m, -f (e i)) = -(∑ j, f j) := by
    calc
      (∑ i : Fin m, -f (e i)) =
          -(∑ i : Fin m, f (e i)) := by
        rw [Finset.sum_neg_distrib]
      _ = -(∑ j, f j) := by
        rw [e.sum_comp f]
  calc
    (∑ i : Fin m,
      z4EuclideanFrequency (-f (e i))) =
        z4EuclideanFrequency
          (∑ i : Fin m, -f (e i)) := by
      change
        (∑ i : Fin m,
          z4EuclideanFrequencyAddHom (-f (e i))) =
            z4EuclideanFrequencyAddHom
              (∑ i : Fin m, -f (e i))
      rw [map_sum]
    _ = z4EuclideanFrequency (-(∑ j, f j)) :=
      congrArg z4EuclideanFrequency hsum

/-- On a nonzero integrated configuration, the increments sum exactly to
the external Fourier shift. -/
theorem sum_r324StandardPairIncrement_eq_external_of_integral_ne_zero
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q : Fin m → Z4)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β κ
        (r324FullConfigurationOfStandard κ q) ≠ 0) :
    (∑ i, r324StandardPairIncrement κ q i) =
      z4EuclideanFrequency (α + β) := by
  rw [sum_r324StandardPairIncrement]
  rw [ρ.r324LeftModeSum_eq_neg_external_of_integral_ne_zero
    ε α β κ (r324FullConfigurationOfStandard κ q) hne]
  simp only [neg_neg]

/-! ## Natural-number enumeration -/

/-- For `m > 0`, the standard configuration type is denumerable. -/
def r324NatEquivStandardConfigurations
    {m : ℕ} (hm : 0 < m) :
    ℕ ≃ (Fin m → Z4) := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  letI : Infinite (Fin m → Z4) := inferInstance
  letI : Denumerable (Fin m → Z4) :=
    Denumerable.ofEncodableOfInfinite _
  exact (Denumerable.eqv (Fin m → Z4)).symm

/-- The `a`-th integrated Fourier configuration of one full pairing. -/
def r324NatFullPairingFourierTerm
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (a : ℕ) : ℂ :=
  ρ.r324FullPairingFourierIntegral ε α β κ
    (r324FullConfigurationOfStandard κ
      (r324NatEquivStandardConfigurations hm a))

/-- The Euclidean increments attached to the `a`-th natural-number
configuration. -/
def r324NatFullPairingIncrement
    {m : ℕ} (hm : 0 < m)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (a : ℕ) (i : Fin m) :
    EuclideanSpace ℝ (Fin dim) :=
  r324StandardPairIncrement κ
    (r324NatEquivStandardConfigurations hm a) i

/-- The natural-number configuration series is summable. -/
theorem summable_r324NatFullPairingFourierTerm
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    Summable
      (ρ.r324NatFullPairingFourierTerm hm ε α β κ) := by
  have horiginal :
      Summable fun q =>
        ‖ρ.r324FullPairingFourierIntegral ε α β κ q‖ := by
    exact
      (ρ.summable_integral_norm_r324FullPairingFourierIntegrand
        hε α β κ).of_nonneg_of_le
        (fun q => norm_nonneg _)
        (fun q => norm_integral_le_integral_norm _)
  have hstandard :
      Summable fun q : Fin m → Z4 =>
        ‖ρ.r324FullPairingFourierIntegral ε α β κ
          (r324FullConfigurationOfStandard κ q)‖ := by
    exact
      ((r324FullConfigurationEquiv κ).summable_iff).2
        horiginal
  have hnat :
      Summable fun a : ℕ =>
        ‖ρ.r324NatFullPairingFourierTerm hm ε α β κ a‖ := by
    exact
      ((r324NatEquivStandardConfigurations hm).summable_iff).2
        hstandard
  exact Summable.of_norm hnat

/-- Exact natural-number `tsum` representation of one full-pairing
physical integral. -/
theorem integral_momentFullPairingPhysicalIntegrand_eq_nat_tsum
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull}) :
    (∫ p,
      r324Flatten
        (momentFullPairingPhysicalIntegrand
          ρ ε m α β κ) p
      ∂(r324PhysicalMeasure m)) =
      ∑' a : ℕ,
        ρ.r324NatFullPairingFourierTerm
          hm ε α β κ a := by
  rw [
    ρ.integral_momentFullPairingPhysicalIntegrand_eq_configuration_tsum
      hε α β κ]
  calc
    (∑' q,
      ρ.r324FullPairingFourierIntegral ε α β κ q) =
        ∑' q : Fin m → Z4,
          ρ.r324FullPairingFourierIntegral ε α β κ
            (r324FullConfigurationOfStandard κ q) := by
      exact
        ((r324FullConfigurationEquiv κ).tsum_eq
          (ρ.r324FullPairingFourierIntegral ε α β κ)).symm
    _ = ∑' a : ℕ,
        ρ.r324NatFullPairingFourierTerm
          hm ε α β κ a := by
      exact
        ((r324NatEquivStandardConfigurations hm).tsum_eq
          (fun q : Fin m → Z4 =>
            ρ.r324FullPairingFourierIntegral ε α β κ
              (r324FullConfigurationOfStandard κ q))).symm

/-- Every nonzero natural-number configuration has the exact external
increment sum. -/
theorem sum_r324NatFullPairingIncrement_eq_external_of_ne_zero
    {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (a : ℕ)
    (hne :
      ρ.r324NatFullPairingFourierTerm
        hm ε α β κ a ≠ 0) :
    (∑ i, r324NatFullPairingIncrement hm κ a i) =
      z4EuclideanFrequency (α + β) := by
  exact
    ρ.sum_r324StandardPairIncrement_eq_external_of_integral_ne_zero
      ε α β κ (r324NatEquivStandardConfigurations hm a) hne

end SmoothCutoff

end

end Anderson4D
