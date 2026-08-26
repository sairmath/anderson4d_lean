import Anderson4D.Parametrix.IdentityGradedComparison
import Anderson4D.Parametrix.PerrPhysicalBridge

/-!
# From kernel comparison to Fourier-coefficient agreement

The bounded-operator parametrix uses the graded word expansion, while the
probabilistic moment estimate uses the paper's partial-pairing expansion.
This file records the exact downstream bridge: almost-everywhere equality
of their kernels implies equality of every paper Fourier coefficient.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace PartialPairing

/-- Almost-everywhere equality of the pairing and graded kernels through a
finite order gives the coefficient agreement consumed by the physical
operator bridge. -/
theorem parametrixGradedCoefficientAgreement_of_ae_kernel_eq
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (ω : M.Ω)
    (hkernel :
      ∀ n, n ≤ A →
        ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
          parametrixP M ρ lam ε n x y ω =
            gradedParametrix M ρ lam ε n x y ω) :
    ParametrixGradedCoefficientAgreement
      M ρ lam ε A ω := by
  intro n hn α β
  unfold paperKernelCoeff pmCoeff
  apply integral_congr_ae
  filter_upwards [hkernel n hn] with x hx
  apply integral_congr_ae
  filter_upwards [hx] with y hxy
  rw [gradedParametrixKernelC_eq_ofReal, ← hxy]

/-- The existing pointwise Proposition 3.4 ledger therefore implies the
integrated coefficient agreement.  The endpoint diagonal is discarded
using its zero paper-Haar measure. -/
theorem parametrixGradedCoefficientAgreement_of_integrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (ω : M.Ω)
    (hint :
      ParametrixIdentityIntegrability
        M ρ lam ε ω) :
    ParametrixGradedCoefficientAgreement
      M ρ lam ε A ω := by
  apply parametrixGradedCoefficientAgreement_of_ae_kernel_eq
  intro n _hn
  filter_upwards with x
  filter_upwards
    [compl_mem_ae_iff.mpr
      (paperMeasure_singleton x)] with y hy
  have hyx : y ≠ x := by
    simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using hy
  exact
    parametrixP_eq_gradedParametrix_of_integrability
      M ρ lam ε ω hint n x y (Ne.symm hyx)

end PartialPairing

end

end Anderson4D
