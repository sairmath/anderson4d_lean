import Anderson4D.DetParametrix.Paper42_Moment.R324ConfigurationDecay

/-!
# Natural-number covariance configurations for one full pairing

This small module packages the two configuration equivalences behind
opaque natural-number terms.  Downstream finite-fibre arguments can use
the resulting shallow declarations without repeatedly elaborating the
dependent Fourier-assignment type.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- The `a`-th pointwise covariance Fourier configuration of one full
pairing. -/
def r324NatCovarianceConfigurationTerm
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (κ : R324FullPairingIndex m) (a : ℕ)
    (v : Fin (2 * m) → T4) : ℂ :=
  ρ.r324CovarianceFourierConfigurationTerm ε κ.1 v
    (r324FullConfigurationOfStandard κ
      (r324NatEquivStandardConfigurations hm a))

/-- Coordinate-independent norm weight of the preceding natural
configuration. -/
def r324NatCovarianceConfigurationWeight
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (κ : R324FullPairingIndex m) (a : ℕ) : ℝ :=
  ρ.r324CovarianceConfigurationWeight ε κ.1
    (r324FullConfigurationOfStandard κ
      (r324NatEquivStandardConfigurations hm a))

theorem norm_r324NatCovarianceConfigurationTerm
    {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (κ : R324FullPairingIndex m) (a : ℕ)
    (v : Fin (2 * m) → T4) :
    ‖ρ.r324NatCovarianceConfigurationTerm
        hm ε κ a v‖ =
      ρ.r324NatCovarianceConfigurationWeight
        hm ε κ a := by
  exact
    ρ.norm_r324CovarianceFourierConfigurationTerm
      ε κ.1 v
      (r324FullConfigurationOfStandard κ
        (r324NatEquivStandardConfigurations hm a))

/-- Standardized configuration weights remain summable. -/
theorem summable_r324StandardCovarianceConfigurationWeight
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (κ : R324FullPairingIndex m) :
    Summable fun q : Fin m → Z4 =>
      ρ.r324CovarianceConfigurationWeight ε κ.1
        (r324FullConfigurationOfStandard κ q) := by
  have h :=
    (ρ.summable_r324CovarianceConfigurationWeight hε κ.1).comp_injective
      (r324FullConfigurationEquiv κ).injective
  exact h.congr fun q => by rfl

/-- Natural-number covariance weights remain summable. -/
theorem summable_r324NatCovarianceConfigurationWeight
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (κ : R324FullPairingIndex m) :
    Summable
      (ρ.r324NatCovarianceConfigurationWeight hm ε κ) := by
  have h :=
    (ρ.summable_r324StandardCovarianceConfigurationWeight
      hε κ).comp_injective
        (r324NatEquivStandardConfigurations hm).injective
  exact h

theorem summable_norm_r324NatCovarianceConfigurationTerm
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (κ : R324FullPairingIndex m)
    (v : Fin (2 * m) → T4) :
    Summable fun a =>
      ‖ρ.r324NatCovarianceConfigurationTerm
        hm ε κ a v‖ := by
  exact
    (ρ.summable_r324NatCovarianceConfigurationWeight
      hm hε κ).congr fun a =>
        (ρ.norm_r324NatCovarianceConfigurationTerm
          hm ε κ a v).symm

theorem summable_r324NatCovarianceConfigurationTerm
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (κ : R324FullPairingIndex m)
    (v : Fin (2 * m) → T4) :
    Summable
      (ρ.r324NatCovarianceConfigurationTerm
        hm ε κ · v) :=
  Summable.of_norm
    (ρ.summable_norm_r324NatCovarianceConfigurationTerm
      hm hε κ v)

/-- The natural series is the complete covariance product of the full
pairing. -/
theorem tsum_r324NatCovarianceConfigurationTerm
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (κ : R324FullPairingIndex m)
    (v : Fin (2 * m) → T4) :
    (∑' a,
      ρ.r324NatCovarianceConfigurationTerm
        hm ε κ a v) =
      (primitiveCovarianceProduct
        ρ ε m κ.1 v : ℂ) := by
  calc
    (∑' a,
      ρ.r324NatCovarianceConfigurationTerm
        hm ε κ a v) =
        ∑' q : Fin m → Z4,
          ρ.r324CovarianceFourierConfigurationTerm
            ε κ.1 v
            (r324FullConfigurationOfStandard κ q) := by
      exact
        (r324NatEquivStandardConfigurations hm).tsum_eq
          (fun q : Fin m → Z4 =>
            ρ.r324CovarianceFourierConfigurationTerm
              ε κ.1 v
              (r324FullConfigurationOfStandard κ q))
    _ = ∑' q,
          ρ.r324CovarianceFourierConfigurationTerm
            ε κ.1 v q := by
      exact
        (r324FullConfigurationEquiv κ).tsum_eq
          (ρ.r324CovarianceFourierConfigurationTerm
            ε κ.1 v)
    _ = (primitiveCovarianceProduct
          ρ ε m κ.1 v : ℂ) := by
      exact
        (ρ.primitiveCovarianceProduct_eq_r324_configuration_tsum
          hε κ.1 v).symm

/-- Signed left-increment key of the `a`-th natural configuration. -/
def r324NatCovarianceIncrementKey
    {m : ℕ} (hm : 0 < m)
    (κ : R324FullPairingIndex m) (a : ℕ) :
    Fin m → Z4 :=
  let q := r324NatEquivStandardConfigurations hm a
  fun i =>
    -r324LeftPairModeContribution κ.1
      (r324FullConfigurationOfStandard κ q)
      (r324FullPairIndexEquiv κ i)

@[simp]
theorem z4EuclideanFrequency_r324NatCovarianceIncrementKey
    {m : ℕ} (hm : 0 < m)
    (κ : R324FullPairingIndex m) (a : ℕ)
    (i : Fin m) :
    z4EuclideanFrequency
        (r324NatCovarianceIncrementKey hm κ a i) =
      r324NatFullPairingIncrement hm κ a i := by
  rfl

end SmoothCutoff

end

end Anderson4D
