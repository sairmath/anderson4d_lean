import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointZeroShift

/-!
# Common numerical exit from the paper's inserted majorant

Both parts of paper Step 4 end, after every signed primitive removal, with
one integrated `primitiveInsertedMajorant`.  The analytic factor in front
is different (endpoint decay alone in Step 4(A), endpoint times central
decay in Step 4(B)), but the conversion from the full
`|lambda_epsilon|^(2m)` weight to `K^m |log epsilon|^(m-1)` is identical.

This file records that scalar conversion once.  It contains no physical
integral, pairing sum, selector, or triangle inequality.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- A paper-weighted estimate by one inserted primitive majorant converts
to the standard capped-order ledger.  `decay` is an arbitrary nonnegative
factor, so the same theorem applies before or after the central-frequency
payoff has been extracted. -/
theorem exists_r324PaperWeightedMajorantBase
    {primitiveConstant supportConstant : Real}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    exists K : Real, 0 < K ∧
      forall {epsilon : Real} (m : Nat) (decay value : Real),
        0 < epsilon → epsilon <= 1 / 4 →
        1 <= abs (Real.log epsilon) → 2 <= m →
        0 <= decay →
        abs (lamEps 1 epsilon) ^ (2 * m) * value <=
          decay *
            (epsilon⁻¹ ^ (8 : Nat) *
              ∫ z, primitiveInsertedMajorant
                primitiveConstant 1 epsilon supportConstant m z
                ∂paperMeasure) →
        value <=
          decay *
            ((m : Real) ^ 8 * K ^ m *
              abs (Real.log epsilon) ^ (m - 1) *
                epsilon⁻¹ ^ (8 : Nat)) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hmajorant⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  let D : Real := Cball * supportConstant ^ 2 + 2 * Creg
  let K : Real := (primitiveConstant * (D + 1)) ^ 2
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro epsilon m decay value hepsilon hepsilonSmall hlog hm2 hdecay
    hweighted
  let L : Real := abs (Real.log epsilon)
  have hepsilonOne : epsilon <= 1 :=
    hepsilonSmall.trans (by norm_num)
  have hLpos : 0 < L := by
    dsimp only [L]
    exact one_pos.trans_le hlog
  have hLne : L ≠ 0 := hLpos.ne'
  have hmajorantBound :=
    hmajorant primitiveConstant 1 epsilon supportConstant m
      hepsilon hepsilonOne hsupport hlog
  have habsorb :
      primitiveConstant ^ (2 * m) * D <= K ^ m := by
    have h := mul_constant_le_absorbed_even_pow
      (base := primitiveConstant) (K := D) (q := m)
      hprimitive.le hD.le (by omega)
    calc
      primitiveConstant ^ (2 * m) * D <=
          (primitiveConstant * (D + 1)) ^ (2 * m) := h
      _ = K ^ m := by
        dsimp only [K]
        rw [pow_mul]
  have hweightedMajorant :
      abs (lamEps 1 epsilon) ^ (2 * m) * value <=
        decay *
          (epsilon⁻¹ ^ (8 : Nat) *
            (primitiveConstant ^ (2 * m) * (D / L))) := by
    exact hweighted.trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (by simpa only [D, L, one_mul, mul_one] using hmajorantBound)
          (by positivity))
        hdecay)
  have hcoefficient :
      primitiveConstant ^ (2 * m) * (D / L) <= K ^ m / L := by
    calc
      primitiveConstant ^ (2 * m) * (D / L) =
          (primitiveConstant ^ (2 * m) * D) / L := by ring
      _ <= K ^ m / L :=
        div_le_div_of_nonneg_right habsorb hLpos.le
  have hweightedK :
      abs (lamEps 1 epsilon) ^ (2 * m) * value <=
        decay * (epsilon⁻¹ ^ (8 : Nat) * (K ^ m / L)) :=
    hweightedMajorant.trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcoefficient (by positivity))
        hdecay)
  have hweight :
      abs (lamEps 1 epsilon) ^ (2 * m) = 1 / L ^ m := by
    simpa only [one_pow, L] using
      (abs_lamEps_even_pow (lam := (1 : Real))
        (ε := epsilon) m hLpos)
  have hLpow : L ^ m = L * L ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hscaledIdentity :
      decay * (epsilon⁻¹ ^ (8 : Nat) * (K ^ m / L)) =
        abs (lamEps 1 epsilon) ^ (2 * m) *
          (decay *
            (K ^ m * L ^ (m - 1) * epsilon⁻¹ ^ (8 : Nat))) := by
    rw [hweight, hLpow]
    field_simp [hLne]
  have hbasic :
      value <=
        decay *
          (K ^ m * L ^ (m - 1) * epsilon⁻¹ ^ (8 : Nat)) := by
    apply le_of_mul_le_mul_left
      (hweightedK.trans_eq hscaledIdentity)
    rw [hweight]
    positivity
  have hmOne : (1 : Real) <= (m : Real) := by
    exact_mod_cast (show 1 <= m by omega)
  have hmPow : (1 : Real) <= (m : Real) ^ 8 :=
    one_le_pow₀ hmOne
  have htail :
      K ^ m * L ^ (m - 1) * epsilon⁻¹ ^ (8 : Nat) <=
        (m : Real) ^ 8 * K ^ m * L ^ (m - 1) *
          epsilon⁻¹ ^ (8 : Nat) := by
    have hKL :
        0 <= K ^ m * L ^ (m - 1) * epsilon⁻¹ ^ (8 : Nat) := by
      positivity
    calc
      K ^ m * L ^ (m - 1) * epsilon⁻¹ ^ (8 : Nat) <=
          (m : Real) ^ 8 *
            (K ^ m * L ^ (m - 1) * epsilon⁻¹ ^ (8 : Nat)) :=
        le_mul_of_one_le_left hKL hmPow
      _ = (m : Real) ^ 8 * K ^ m * L ^ (m - 1) *
          epsilon⁻¹ ^ (8 : Nat) := by ring
  exact hbasic.trans
    (mul_le_mul_of_nonneg_left
      (by simpa only [L] using htail) hdecay)

end

end Anderson4D
