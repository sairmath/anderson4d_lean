import Anderson4D.Continuum.GreenBounds
import Anderson4D.Parametrix.IdentityRightOperator

/-!
# Right parametrix identity from kernel symmetry

The random Schrödinger kernel and every finite parametrix order are
symmetric in their external variables.  This module isolates the exact
consequence needed for paper (3.17): once that orderwise symmetry is
available, the right-composition identity is the left-composition identity
with the external variables exchanged.  Thus the Wick head-case analysis
does not have to be duplicated at the tail of the chain.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-- Symmetry of one random parametrix order in its two external variables. -/
def ParametrixKernelSymmetric
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (ω : M.Ω) : Prop :=
  ∀ x y : T4,
    parametrixP M ρ lam ε n x y ω =
      parametrixP M ρ lam ε n y x ω

/-- Orderwise symmetry through a fixed truncation order. -/
def ParametrixKernelSymmetricThrough
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (N : ℕ) (ω : M.Ω) : Prop :=
  ∀ n ≤ N, ParametrixKernelSymmetric M ρ lam ε n ω

/-- The right noise composition is the left noise composition with the
external variables exchanged. -/
theorem rightParametrixNoiseSource_eq_left_swap
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hsymm :
      ParametrixKernelSymmetric M ρ lam ε n ω) :
    rightParametrixNoiseSource
        M ρ lam ε n x y ω =
      leftParametrixNoiseSource
        M ρ lam ε n y x ω := by
  unfold rightParametrixNoiseSource
  unfold leftParametrixNoiseSource
  apply congrArg (lamEps lam ε * ·)
  apply integral_congr_ae
  filter_upwards with z
  have hgreen :
      greenFn (z - y) = greenFn (y - z) := by
    simpa only [neg_sub] using
      (greenFn_memE.neg_invariant (z - y)).symm
  rw [hsymm x z, hgreen]
  ring

/-- The right counterterm block is the transposed left counterterm block. -/
theorem caseThreeRightCountertermBlock_eq_left_swap
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω)
    (hsymm :
      ParametrixKernelSymmetric M ρ lam ε r ω) :
    caseThreeRightCountertermBlock
        M ρ lam ε q r x y ω =
      caseThreeCountertermBlock
        M ρ lam ε q r y x ω := by
  rw [
    caseThreeRightCountertermBlock_eq,
    caseThreeCountertermBlock_eq]
  apply congrArg (renormC2q ρ lam ε q * ·)
  apply integral_congr_ae
  filter_upwards with z
  have hgreen :
      greenFn (z - y) = greenFn (y - z) := by
    simpa only [neg_sub] using
      (greenFn_memE.neg_invariant (z - y)).symm
  rw [hsymm x z, hgreen]
  ring

/-- The fixed-order right counterterm sum, in the same range as paper
(3.16)--(3.17). -/
def rightOrderCountertermSum
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
    caseThreeRightCountertermBlock
      M ρ lam ε q (n + 1 - 2 * q) x y ω

/-- Transpose the complete fixed-order left identity to obtain the right
identity.  Symmetry is only required through the new order `n+1`. -/
theorem
    rightParametrixNoiseSource_eq_parametrix_succ_add_counterterms_of_left
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hsymm :
      ParametrixKernelSymmetricThrough
        M ρ lam ε (n + 1) ω)
    (hleft :
      leftParametrixNoiseSource
          M ρ lam ε n y x ω =
        parametrixP M ρ lam ε (n + 1) y x ω +
          leftOrderCountertermSum
            M ρ lam ε n y x ω) :
    rightParametrixNoiseSource
        M ρ lam ε n x y ω =
      parametrixP M ρ lam ε (n + 1) x y ω +
        rightOrderCountertermSum
          M ρ lam ε n x y ω := by
  rw [
    rightParametrixNoiseSource_eq_left_swap
      M ρ lam ε n x y ω (hsymm n (by omega)),
    hleft,
    hsymm (n + 1) (by omega) y x]
  congr 1
  unfold leftOrderCountertermSum
  unfold rightOrderCountertermSum
  apply Finset.sum_congr rfl
  intro q hq
  exact
    (caseThreeRightCountertermBlock_eq_left_swap
      M ρ lam ε q (n + 1 - 2 * q) x y ω
      (hsymm (n + 1 - 2 * q)
        (Nat.sub_le (n + 1) (2 * q)))).symm

/-- The complete postconditioned remainder identity follows from the left
fixed-order identities and symmetry through the truncation order. -/
theorem
    rightPreconditionedParametrixAction_eq_green_add_remainder_of_left
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (x y : T4) (ω : M.Ω)
    (hsymm :
      ParametrixKernelSymmetricThrough
        M ρ lam ε A ω)
    (hleft :
      ∀ m ∈ Finset.Icc 1 A,
        leftParametrixNoiseSource
            M ρ lam ε (m - 1) y x ω =
          parametrixP M ρ lam ε m y x ω +
            leftOrderCountertermSum
              M ρ lam ε (m - 1) y x ω) :
    rightPreconditionedParametrixAction
        M ρ lam ε A x y ω =
      greenFn (x - y) +
        rightPreconditionedRemainder
          M ρ lam ε A x y ω := by
  apply
    rightPreconditionedParametrixAction_eq_green_add_remainder
      M ρ lam ε A x y ω
  intro m hm
  have hthrough :
      ParametrixKernelSymmetricThrough
        M ρ lam ε ((m - 1) + 1) ω := by
    intro r hr
    exact hsymm r (hr.trans (by
      have hmBounds := Finset.mem_Icc.mp hm
      omega))
  have hsucc : m - 1 + 1 = m := by
    have hmBounds := Finset.mem_Icc.mp hm
    omega
  have horder :=
    rightParametrixNoiseSource_eq_parametrix_succ_add_counterterms_of_left
      M ρ lam ε (m - 1) x y ω
      hthrough (by
        simpa only [hsucc] using hleft m hm)
  simpa only [rightOrderCountertermSum, hsucc] using horder

end PartialPairing

end

end Anderson4D
