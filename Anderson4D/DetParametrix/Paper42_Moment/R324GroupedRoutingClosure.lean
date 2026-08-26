import Anderson4D.DetParametrix.Paper42_Moment.R324ConfigurationDecay
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointAggregate
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedFiber

/-!
# Grouped residual routing closure for R-324

This file bridges the absolutely convergent raw Fourier expansion to the
paper-faithful residual-refined grouping.  The raw full-pairing series is
recorded first as an exact equality, without taking norms.  The final
consumer is indexed by refined primitive schedules, so all cancellation
inside one compatible primitive fiber occurs before its routed weight is
formed.
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

/-! ## Exact raw series before regrouping -/

theorem summable_r324RawMomentFourierTerm
    {m : ℕ} (hm : 0 < m)
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε)
    (α β : Z4) :
    Summable
      (ρ.r324RawMomentFourierTerm hm lam ε α β) := by
  let scalar : ℂ := (lamEps lam ε ^ (2 * m) : ℂ)
  let f : R324FullPairingIndex m × ℕ → ℂ := fun p =>
    scalar *
      ρ.r324NatFullPairingFourierTerm
        hm ε α β p.1 p.2
  have hfnorm : Summable fun p => ‖f p‖ := by
    rw [summable_prod_of_nonneg (fun p => norm_nonneg (f p))]
    constructor
    · intro κ
      have h :=
        (ρ.summable_r324NatFullPairingFourierTerm
          hm hε α β κ).norm.mul_left ‖scalar‖
      exact h.congr fun a => by
        unfold f
        rw [norm_mul]
    · exact Summable.of_finite
  have hf : Summable f := Summable.of_norm hfnorm
  change
    Summable
      (f ∘ r324NatEquivRawFullPairingConfigurations m)
  exact
    ((r324NatEquivRawFullPairingConfigurations m).summable_iff).2
      hf

/-- Exact full-pairing/Fourier reindexing.  No triangle inequality is
used here; the result is therefore safe to regroup by refined primitive
schedule. -/
theorem deterministicMomentPairingSum_eq_rawMomentFourier_tsum
    {m : ℕ} (hm : 0 < m)
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4) :
    deterministicMomentPairingSum ρ lam ε m α β =
      ∑' a : ℕ,
        ρ.r324RawMomentFourierTerm
          hm lam ε α β a := by
  let scalar : ℂ := (lamEps lam ε ^ (2 * m) : ℂ)
  let physical : R324FullPairingIndex m → ℂ := fun κ =>
    ∫ p,
      r324Flatten
        (momentFullPairingPhysicalIntegrand
          ρ ε m α β κ) p
      ∂(r324PhysicalMeasure m)
  have hintegrable :
      ∀ e : MomentContraction m,
        R324MomentIntegrable ρ ε m α β e :=
    r324MomentIntegrable_all ρ hε hε1 α β
  have hcontraction :
      (∑ e : MomentContraction m,
          deterministicMomentContractionTerm
            ρ ε m α β e) =
        ∑ κ : R324FullPairingIndex m, physical κ := by
    calc
      (∑ e : MomentContraction m,
          deterministicMomentContractionTerm
            ρ ε m α β e) =
          ∑ e : MomentContraction m,
            physical (momentContractionEquivFullPairing m e) := by
        apply Finset.sum_congr rfl
        intro e _he
        unfold physical
        have hfun :
            r324Flatten
                (momentFullPairingPhysicalIntegrand
                  ρ ε m α β
                    (momentContractionEquivFullPairing m e)) =
              r324Flatten
                (deterministicMomentIntegrand
                  ρ ε m α β e.1 e.2.1 e.2.2) := by
          funext p
          unfold r324Flatten
          exact
            momentFullPairingPhysicalIntegrand_momentContraction
              ρ ε m α β e
              p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
        rw [hfun]
        exact
          (integral_r324Flatten_deterministicMomentIntegrand
            ρ ε m α β e (hintegrable e)).symm
      _ = ∑ κ : R324FullPairingIndex m, physical κ :=
        momentContractionEquivFullPairing m |>.sum_comp physical
  have hphysical (κ : R324FullPairingIndex m) :
      physical κ =
        ∑' a : ℕ,
          ρ.r324NatFullPairingFourierTerm
            hm ε α β κ a := by
    unfold physical
    exact
      ρ.integral_momentFullPairingPhysicalIntegrand_eq_nat_tsum
        hm hε α β κ
  let f : R324FullPairingIndex m × ℕ → ℂ := fun p =>
    scalar *
      ρ.r324NatFullPairingFourierTerm
        hm ε α β p.1 p.2
  have hf : Summable f := by
    have hfnorm : Summable fun p => ‖f p‖ := by
      rw [summable_prod_of_nonneg (fun p => norm_nonneg (f p))]
      constructor
      · intro κ
        have h :=
          (ρ.summable_r324NatFullPairingFourierTerm
            hm hε α β κ).norm.mul_left ‖scalar‖
        exact h.congr fun a => by
          unfold f
          rw [norm_mul]
      · exact Summable.of_finite
    exact Summable.of_norm hfnorm
  rw [deterministicMomentPairingSum_eq_contractionTerms,
    hcontraction]
  change scalar * (∑ κ, physical κ) = _
  calc
    scalar * (∑ κ, physical κ) =
        ∑ κ : R324FullPairingIndex m,
          scalar * physical κ := by
      rw [Finset.mul_sum]
    _ = ∑ κ : R324FullPairingIndex m,
          ∑' a : ℕ, f (κ, a) := by
      apply Finset.sum_congr rfl
      intro κ _hκ
      calc
        scalar * physical κ =
            scalar *
              ∑' a : ℕ,
                ρ.r324NatFullPairingFourierTerm
                  hm ε α β κ a := by
          rw [hphysical]
        _ = ∑' a : ℕ,
              scalar *
                ρ.r324NatFullPairingFourierTerm
                  hm ε α β κ a := by
          rw [tsum_mul_left]
        _ = ∑' a : ℕ, f (κ, a) := by
          rfl
    _ = ∑' κ : R324FullPairingIndex m,
          ∑' a : ℕ, f (κ, a) := by
      rw [tsum_fintype]
    _ = ∑' p : R324FullPairingIndex m × ℕ, f p :=
      hf.tsum_prod.symm
    _ = ∑' a : ℕ,
          ρ.r324RawMomentFourierTerm
            hm lam ε α β a := by
      change
        (∑' p : R324FullPairingIndex m × ℕ, f p) =
          ∑' a : ℕ,
            f (r324NatEquivRawFullPairingConfigurations m a)
      exact
        ((r324NatEquivRawFullPairingConfigurations m).tsum_eq
          f).symm

end SmoothCutoff

end

end Anderson4D
