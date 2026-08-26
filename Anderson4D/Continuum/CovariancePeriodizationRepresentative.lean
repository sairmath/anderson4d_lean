import Anderson4D.Continuum.CovarianceSymmetry

/-!
# Arbitrary representatives for the periodized covariance

The canonical lift of a quotient point need not equal the Euclidean point
used to define it.  This file records that the two representatives differ
by an integer period vector and transports representative independence of
the covariance periodization across that equality.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

namespace SmoothCutoff

/-- The canonical lift of an arbitrary Euclidean point modulo `2π` differs
from that point by an integer period vector. -/
theorem exists_periodVector_torusLift_periodizeR4 (x : R4) :
    ∃ a : Z4,
      torusLift (periodizeR4 x) = x + covariancePeriodVector a := by
  classical
  have hmem : ∀ i : Fin dim,
      torusLift (periodizeR4 x) i - x i ∈
        AddSubgroup.zmultiples (2 * Real.pi) := by
    intro i
    apply QuotientAddGroup.eq_iff_sub_mem.mp
    calc
      ((torusLift (periodizeR4 x) i : ℝ) :
          AddCircle (2 * Real.pi)) =
          (periodizeR4 x) i :=
        AddCircle.coe_equivIco
      _ = ((x i : ℝ) : AddCircle (2 * Real.pi)) := rfl
  choose a ha using fun i =>
    AddSubgroup.mem_zmultiples_iff.mp (hmem i)
  refine ⟨a, ?_⟩
  funext i
  have hi := ha i
  simp only [zsmul_eq_mul] at hi
  simp only [Pi.add_apply, covariancePeriodVector]
  linarith

/-- Evaluating the torus covariance at the quotient of any Euclidean
representative agrees with periodization based at that representative. -/
theorem etaEpsT4_periodizeR4_eq_etaPeriodizationR4
    (ρ : SmoothCutoff) (ε : ℝ) (x : R4) :
    ρ.etaEpsT4 ε (periodizeR4 x) =
      ρ.etaPeriodizationR4 ε x := by
  obtain ⟨a, ha⟩ :=
    exists_periodVector_torusLift_periodizeR4 x
  rw [etaEpsT4_eq_etaPeriodizationR4, ha,
    etaPeriodizationR4_add_period]

/-- The arbitrary-representative periodization is `2π`-periodic in each
Euclidean coordinate. -/
theorem etaPeriodizationR4_update_add_two_pi
    (ρ : SmoothCutoff) (ε : ℝ) (x : R4)
    (i : Fin dim) (t : ℝ) :
    ρ.etaPeriodizationR4 ε
        (Function.update x i (t + 2 * Real.pi)) =
      ρ.etaPeriodizationR4 ε (Function.update x i t) := by
  let a : Z4 := Function.update 0 i 1
  have hupdate :
      Function.update x i (t + 2 * Real.pi) =
        Function.update x i t + covariancePeriodVector a := by
    funext j
    rcases eq_or_ne j i with rfl | hji
    · simp [a, covariancePeriodVector]
    · simp [a, covariancePeriodVector, Function.update_of_ne hji]
  rw [hupdate, etaPeriodizationR4_add_period]

end SmoothCutoff

end

end Anderson4D
