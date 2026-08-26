import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointZeroShift

/-!
# Numerical closure of paper Step 4(A)

After all signed primitive removals and the four endpoint integrations, the
physical argument leaves one inserted primitive majorant at the ambient
order, together with the four ordinary-`J` endpoint sacrifices.  Each
sacrifice costs at most `epsilon^(-2)`, so the producer boundary retains the
paper's total `epsilon^(-8)` loss explicitly.  This file performs only the
final scalar calculation: divide out the full `|lambda_epsilon|^(2m)`
weight, integrate the majorant, and absorb its order-independent mass into
one geometric base.

There is no physical integral, pairing sum, or triangle inequality here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The exact paper-facing producer boundary after all signed removals and
four endpoint integrations.  It deliberately retains the complete
`|lambda_epsilon|^(2m)` weight and the final inserted majorant. -/
def R324PaperEndpointWeightedMajorantBound
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  ∀ {epsilon : Real} (m : Nat) (alpha beta : Z4),
    0 < epsilon → epsilon <= 1 / 4 →
      1 <= abs (Real.log epsilon) → 2 <= m →
        m <= truncOrder epsilon → alpha + beta = 0 →
          ∀ p : R324RefinedScheduleIndex m,
            abs (lamEps 1 epsilon) ^ (2 * m) *
                  norm (r324RefinedPhysicalIntegral
                    rho epsilon m alpha beta p) <=
                (paperFourthOrderModeDecay alpha *
                    paperFourthOrderModeDecay beta) *
                  (epsilon⁻¹ ^ (8 : Nat) *
                    ∫ z, primitiveInsertedMajorant
                      primitiveConstant 1 epsilon supportConstant m z
                      ∂paperMeasure)

/-- A complete weighted endpoint-to-majorant estimate implies the literal
Step 4(A) physical bound.  This is the common numerical consumer for the
full/full and residual endpoint case splits. -/
theorem exists_r324PaperEndpointBase_of_weightedMajorant
    (rho : SmoothCutoff) {primitiveConstant supportConstant : Real}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ K : Real, 0 < K ∧
      ∀ {epsilon : Real} (m : Nat) (alpha beta : Z4),
        0 < epsilon → epsilon <= 1 / 4 →
        1 <= abs (Real.log epsilon) → 2 <= m →
        m <= truncOrder epsilon →
        ∀ p : R324RefinedScheduleIndex m,
          abs (lamEps 1 epsilon) ^ (2 * m) *
                norm (r324RefinedPhysicalIntegral
                  rho epsilon m alpha beta p) <=
              (paperFourthOrderModeDecay alpha *
                  paperFourthOrderModeDecay beta) *
                (epsilon⁻¹ ^ (8 : Nat) *
                  ∫ z, primitiveInsertedMajorant
                    primitiveConstant 1 epsilon supportConstant m z
                    ∂paperMeasure) →
          norm (r324RefinedPhysicalIntegral
              rho epsilon m alpha beta p) <=
            (paperFourthOrderModeDecay alpha *
                paperFourthOrderModeDecay beta) *
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
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 _hmtrunc p
    hweighted
  let L : Real := abs (Real.log epsilon)
  have hepsilonOne : epsilon <= 1 :=
    hepsilonSmall.trans (by norm_num)
  have hLpos : 0 < L := by
    dsimp only [L]
    exact one_pos.trans_le hlog
  have hLne : L ≠ 0 := hLpos.ne'
  have hendpoint :
      0 <= paperFourthOrderModeDecay alpha *
        paperFourthOrderModeDecay beta :=
    mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
      (paperFourthOrderModeDecay_nonneg beta)
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
      abs (lamEps 1 epsilon) ^ (2 * m) *
            norm (r324RefinedPhysicalIntegral
              rho epsilon m alpha beta p) <=
        (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          (epsilon⁻¹ ^ (8 : Nat) *
            (primitiveConstant ^ (2 * m) * (D / L))) := by
    exact hweighted.trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (by simpa only [D, L, one_mul, mul_one] using hmajorantBound)
          (by positivity))
        hendpoint)
  have hcoefficient :
      primitiveConstant ^ (2 * m) * (D / L) <= K ^ m / L := by
    calc
      primitiveConstant ^ (2 * m) * (D / L) =
          (primitiveConstant ^ (2 * m) * D) / L := by ring
      _ <= K ^ m / L :=
        div_le_div_of_nonneg_right habsorb hLpos.le
  have hweightedK :
      abs (lamEps 1 epsilon) ^ (2 * m) *
            norm (r324RefinedPhysicalIntegral
              rho epsilon m alpha beta p) <=
        (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          (epsilon⁻¹ ^ (8 : Nat) * (K ^ m / L)) :=
    hweightedMajorant.trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcoefficient (by positivity))
        hendpoint)
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
      (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
            (epsilon⁻¹ ^ (8 : Nat) * (K ^ m / L)) =
        abs (lamEps 1 epsilon) ^ (2 * m) *
          ((paperFourthOrderModeDecay alpha *
              paperFourthOrderModeDecay beta) *
            (K ^ m * L ^ (m - 1) *
              epsilon⁻¹ ^ (8 : Nat))) := by
    rw [hweight, hLpow]
    field_simp [hLne]
  have hbasic :
      norm (r324RefinedPhysicalIntegral
          rho epsilon m alpha beta p) <=
        (paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          (K ^ m * L ^ (m - 1) *
            epsilon⁻¹ ^ (8 : Nat)) := by
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
        (le_mul_of_one_le_left hKL hmPow)
      _ = (m : Real) ^ 8 * K ^ m * L ^ (m - 1) *
          epsilon⁻¹ ^ (8 : Nat) := by ring
  exact hbasic.trans
    (mul_le_mul_of_nonneg_left
      (by simpa only [L] using htail) hendpoint)

/-- Packaging the preceding scalar lemma: a uniform weighted-majorant
producer closes Step 4(A) with one positive geometric base. -/
theorem R324PaperEndpointWeightedMajorantBound.toPhysicalBound
    {rho : SmoothCutoff} {primitiveConstant supportConstant : Real}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (h : R324PaperEndpointWeightedMajorantBound
      rho primitiveConstant supportConstant) :
    ∃ K : Real, 0 < K ∧ R324PaperEndpointPhysicalBound rho K := by
  obtain ⟨K, hK, hnumeric⟩ :=
    exists_r324PaperEndpointBase_of_weightedMajorant
      rho hprimitive hsupport
  refine ⟨K, hK, ?_⟩
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hexternal p
  exact hnumeric m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc p
    (h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc hexternal p)

end

end Anderson4D
