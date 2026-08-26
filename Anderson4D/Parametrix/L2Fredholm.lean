import Anderson4D.Parametrix.L2ParametrixInverse
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# One-sided compact-parametrix inversion

The paper estimates the physical identity `P L = 1 + R'`.  After
factorizing `P = Q G`, this is the bounded identity

`Q (1 - G M) = 1 + R'`.

For an arbitrary bounded operator a small one-sided residual is not
enough for invertibility.  Here `G M` is compact, however, so the
Fredholm alternative upgrades the resulting injectivity to an honest
unit.  This avoids imposing an additional residual estimate not present
in paper (3.21)--(3.33).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped InnerProductSpace

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A small left parametrix residual excludes eigenvalue `1` for the
compact operator `K`. -/
theorem not_hasEigenvalue_one_of_leftParametrix
    (K Q R : H →L[ℂ] H)
    (hQA : Q * (1 - K) = 1 + R)
    (hR : ‖R‖ < 1) :
    ¬ Module.End.HasEigenvalue (K : Module.End ℂ H) 1 := by
  let L := correctedParametrixLeftInverse Q R hR
  have hleft : L * (1 - K) = 1 :=
    correctedParametrixLeftInverse_spec
      (1 - K) Q R hQA hR
  rw [Module.End.hasEigenvalue_iff]
  apply not_ne_iff.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx
  have hAx : (1 - K) x = 0 := by
    simp only [sub_apply, one_smul] at hx ⊢
    exact sub_eq_zero.mpr hx.symm
  calc
    x = (1 : H →L[ℂ] H) x := rfl
    _ = (L * (1 - K)) x := by rw [hleft]
    _ = L ((1 - K) x) := rfl
    _ = 0 := by rw [hAx, map_zero]

/-- **One-sided Fredholm inversion.**  If `K` is compact and
`Q (1-K)` differs from the identity by a norm-small residual, then
`1-K` is a unit. -/
theorem isUnit_one_sub_of_compact_leftParametrix
    (K Q R : H →L[ℂ] H)
    (hcompact : IsCompactOperator K)
    (hQA : Q * (1 - K) = 1 + R)
    (hR : ‖R‖ < 1) :
    IsUnit (1 - K) := by
  have hnoeig :=
    not_hasEigenvalue_one_of_leftParametrix K Q R hQA hR
  rcases
      hcompact.hasEigenvalue_or_mem_resolventSet
        (μ := (1 : ℂ)) one_ne_zero with
    heig | hres
  · exact (hnoeig heig).elim
  · have hunit :
        IsUnit
          ((algebraMap ℂ (H →L[ℂ] H)) 1 - K) :=
      spectrum.mem_resolventSet_iff.mp hres
    simpa using hunit

/-- The inverse selected by Fredholm is the corrected one-sided
parametrix. -/
theorem inverseUnit_eq_correctedParametrixLeftInverse_of_compact
    (K Q R : H →L[ℂ] H)
    (hcompact : IsCompactOperator K)
    (hQA : Q * (1 - K) = 1 + R)
    (hR : ‖R‖ < 1) :
    (((isUnit_one_sub_of_compact_leftParametrix
          K Q R hcompact hQA hR).unit⁻¹ :
        (H →L[ℂ] H)ˣ) : H →L[ℂ] H) =
      correctedParametrixLeftInverse Q R hR := by
  let hunit :=
    isUnit_one_sub_of_compact_leftParametrix
      K Q R hcompact hQA hR
  let L := correctedParametrixLeftInverse Q R hR
  have hval : (hunit.unit : H →L[ℂ] H) = 1 - K :=
    hunit.unit_spec
  have hleft : L * (1 - K) = 1 :=
    correctedParametrixLeftInverse_spec
      (1 - K) Q R hQA hR
  have hright :
      (1 - K) *
          ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) :
            H →L[ℂ] H) =
        1 := by
    calc
      (1 - K) *
            ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) :
              H →L[ℂ] H) =
          (hunit.unit : H →L[ℂ] H) *
            ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) :
              H →L[ℂ] H) := by rw [hval]
      _ = 1 := by exact_mod_cast hunit.unit.mul_inv
  symm
  calc
    L = L * 1 := (mul_one L).symm
    _ =
        L * ((1 - K) *
          ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) :
            H →L[ℂ] H)) := by rw [hright]
    _ =
        (L * (1 - K)) *
          ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) :
            H →L[ℂ] H) := mul_assoc _ _ _
    _ =
        ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) :
          H →L[ℂ] H) := by rw [hleft, one_mul]

/-- Anderson specialization of one-sided Fredholm inversion. -/
theorem lopInvertible_of_compact_leftParametrix
    (G M Q R : H →L[ℂ] H)
    (hcompact : IsCompactOperator (Kop G M))
    (hleft : Q * (1 - Kop G M) = 1 + R)
    (hR : ‖R‖ < 1) :
    LopInvertible G M :=
  isUnit_one_sub_of_compact_leftParametrix
    (Kop G M) Q R hcompact hleft hR

/-- The physical inverse is the corrected left factor followed by
`G`. -/
theorem inverseGreen_eq_correctedLeftParametrix_mul_of_compact
    (G M Q R : H →L[ℂ] H)
    (hcompact : IsCompactOperator (Kop G M))
    (hleft : Q * (1 - Kop G M) = 1 + R)
    (hR : ‖R‖ < 1) :
    inverseGreen G M
        (lopInvertible_of_compact_leftParametrix
          G M Q R hcompact hleft hR) =
      correctedParametrixLeftInverse Q R hR * G := by
  unfold inverseGreen
  let hunit :=
    lopInvertible_of_compact_leftParametrix
      G M Q R hcompact hleft hR
  have hproof :
      lopInvertible_of_compact_leftParametrix
          G M Q R hcompact hleft hR =
        isUnit_one_sub_of_compact_leftParametrix
          (Kop G M) Q R hcompact hleft hR :=
    Subsingleton.elim _ _
  rw [hproof]
  rw [inverseUnit_eq_correctedParametrixLeftInverse_of_compact
    (Kop G M) Q R hcompact hleft hR]

/-- Exact factorization of the one-sided correction error. -/
theorem correctedParametrixLeftInverse_mul_sub
    (Q R G : H →L[ℂ] H)
    (hR : ‖R‖ < 1) :
    correctedParametrixLeftInverse Q R hR * G -
        Q * G =
      (oneAddNeumannInverse R hR - 1) * (Q * G) := by
  unfold correctedParametrixLeftInverse
  noncomm_ring

section Nontrivial

variable [Nontrivial H]

/-- Quantitative one-sided error bound in terms of the physical
parametrix norm `‖QG‖`, exactly the norm controlled in paper (3.31). -/
theorem norm_inverseGreen_sub_parametrix_mul_le_of_compact
    (G M Q R : H →L[ℂ] H)
    (hcompact : IsCompactOperator (Kop G M))
    (hleft : Q * (1 - Kop G M) = 1 + R)
    (hR : ‖R‖ < 1) :
    ‖inverseGreen G M
          (lopInvertible_of_compact_leftParametrix
            G M Q R hcompact hleft hR) -
        Q * G‖ ≤
      ((1 - ‖R‖)⁻¹ * ‖R‖) * ‖Q * G‖ := by
  rw [inverseGreen_eq_correctedLeftParametrix_mul_of_compact
    G M Q R hcompact hleft hR]
  rw [correctedParametrixLeftInverse_mul_sub Q R G hR]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_oneAddNeumannInverse_sub_one_le R hR)
      (norm_nonneg (Q * G)))

/-- Half-ball form used by the paper-scale good event. -/
theorem norm_inverseGreen_sub_parametrix_mul_le_two_of_compact
    (G M Q R : H →L[ℂ] H)
    (hcompact : IsCompactOperator (Kop G M))
    (hleft : Q * (1 - Kop G M) = 1 + R)
    (hRhalf : ‖R‖ < 1 / 2) :
    ‖inverseGreen G M
          (lopInvertible_of_compact_leftParametrix
            G M Q R hcompact hleft
              (hRhalf.trans (by norm_num))) -
        Q * G‖ ≤
      2 * ‖Q * G‖ * ‖R‖ := by
  let hR : ‖R‖ < 1 := hRhalf.trans (by norm_num)
  have hden : 0 < 1 - ‖R‖ := sub_pos.mpr hR
  have hinv : (1 - ‖R‖)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hden]
    nlinarith
  calc
    ‖inverseGreen G M
          (lopInvertible_of_compact_leftParametrix
            G M Q R hcompact hleft hR) -
        Q * G‖ ≤
      ((1 - ‖R‖)⁻¹ * ‖R‖) * ‖Q * G‖ :=
        norm_inverseGreen_sub_parametrix_mul_le_of_compact
          G M Q R hcompact hleft hR
    _ ≤ (2 * ‖R‖) * ‖Q * G‖ := by
      gcongr
    _ = 2 * ‖Q * G‖ * ‖R‖ := by ring

end Nontrivial

end

end Anderson4D
