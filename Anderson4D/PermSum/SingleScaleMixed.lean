import Anderson4D.PermSum.SingleScaleInner

/-!
# Mixed skipped single-scale bounds

This file isolates the three numerical estimates used in (5.93)--(5.98).
The hypothesis `RNDominance K R c` is the honest local form of
`R / N ≳ X Y`: it says `N * X * Y ≤ K * R`, with the comparison constant
visible.  `MixedScaleCertificate` is the interface expected from Stage 1.

The analytic estimates below deliberately use the stronger threshold
`max a.N b.N` on the second edge.  This is what permits the summation order
to be chosen in the left-skipped/right-unskipped case, as in the paper.
-/

namespace Anderson4D

namespace XYCluster

/-- The explicit, constant-carrying version of `R / N ≳ X Y`. -/
def RNDominance (K R : ℝ) (c : XYCluster) : Prop :=
  c.N * c.X * c.Y ≤ K * R

/-- The gain on the right-hand side of (5.91). -/
noncomputable def forwardGain (a b : XYCluster) : ℝ :=
  min 1 ((b.P / a.P) ^ (1 / 8 : ℝ))

/-- The reciprocal gain appearing in (5.93), (5.96), and (5.98). -/
noncomputable def reverseGain (a b : XYCluster) : ℝ :=
  max 1 ((a.P / b.P) ^ (1 / 8 : ℝ))

/-- The factor `Ξ` from (5.91). -/
noncomputable def skipXi (c : XYCluster) (skipped : Bool) : ℝ :=
  if skipped then (Real.sqrt (c.X * c.Y))⁻¹ else 1

/-- The second edge, with the scale cutoff required in the mixed cases. -/
noncomputable def strongLambda (a b : XYCluster) (R : ℝ) (skipped : Bool)
    (x y : Fin 4 → ℤ) : ℝ :=
  if skipped then R⁻¹ ^ 2
  else if max a.N b.N ≤ znorm (x - y) then (znorm (x - y))⁻¹ ^ 2 else 0

/-- The two-edge local sum whose four skip cases are assembled below. -/
noncomputable def mixedPairInner (a b : XYCluster) (R : ℝ)
    (skipA skipB : Bool) (u : Fin 4 → ℤ) : ℝ :=
  a.X * b.X *
    ∑ x ∈ a.points, a.lambda R skipA u x *
      ∑ y ∈ b.points, strongLambda a b R skipB x y

/-- The right-hand side of (5.91), before its universal constant. -/
noncomputable def mixedTarget (a b : XYCluster) (skipA skipB : Bool) : ℝ :=
  (a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2) *
    (b.X * Real.sqrt b.Y * b.N⁻¹ ^ 2) *
      skipXi a skipA * skipXi b skipB * forwardGain a b

/-- The numerical condition displayed in (5.93), with constant `K`. -/
def Line593 (K R : ℝ) (a b : XYCluster) : Prop :=
  (Real.sqrt a.X * a.Y) * (Real.sqrt b.X * b.Y) * reverseGain a b ≤
    K * ((R / a.N) ^ 2 * (R / b.N) ^ 2)

/-- The numerical condition displayed in (5.96), with constant `K`. -/
def Line596 (K R : ℝ) (a b : XYCluster) : Prop :=
  Real.sqrt b.X * b.Y * reverseGain a b ≤ K * (R / b.N) ^ 2

/-- The numerical condition displayed in (5.98), with constant `K`. -/
def Line598 (K R : ℝ) (a b : XYCluster) : Prop :=
  Real.sqrt (a.X * a.Y) * max (Real.sqrt a.Y) (Real.sqrt b.Y) *
      reverseGain a b ≤
    K * (R / min a.N b.N) ^ 2

/--
Stage 1's explicit interface to the mixed-case proof.

The first two fields record the genuine input `N X Y ≤ Kdom R`; the final
three fields are the numerical consequences (5.93), (5.96), and (5.98).
Keeping both is intentional: it prevents a later stage from silently treating
separation as if it implied the required mass domination.
-/
structure MixedScaleCertificate (Kdom Knum R : ℝ) (a b : XYCluster) : Prop where
  a_dominance : RNDominance Kdom R a
  b_dominance : RNDominance Kdom R b
  line593 : Line593 Knum R a b
  line596 : Line596 Knum R a b
  line598 : Line598 Knum R a b

private theorem max_one_rpow_eighth_le {x r : ℝ}
    (hx : 0 ≤ x) (hr : 1 ≤ r) (hxr : x ≤ r ^ 8) :
    max 1 (x ^ (1 / 8 : ℝ)) ≤ r := by
  rw [max_le_iff]
  refine ⟨hr, ?_⟩
  calc
    x ^ (1 / 8 : ℝ) ≤ (r ^ 8) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow hx hxr (by norm_num)
    _ = r := by
      convert Real.pow_rpow_inv_natCast (zero_le_one.trans hr)
        (by norm_num : (8 : ℕ) ≠ 0) using 1
      all_goals norm_num

theorem Y_pos_of_nonempty {c : XYCluster} (hc : c.points.Nonempty) : 0 < c.Y := by
  simp only [Y]
  exact_mod_cast Finset.card_pos.mpr hc

theorem P_pos_of_nonempty {c : XYCluster} (hc : c.points.Nonempty) : 0 < c.P := by
  unfold P
  exact mul_pos (Y_pos_of_nonempty hc) (pow_pos (lt_of_lt_of_le zero_lt_one c.one_le_N) 4)

theorem P_nonneg' (c : XYCluster) : 0 ≤ c.P := by
  unfold P Y
  positivity

theorem one_le_Y_of_nonempty {c : XYCluster} (hc : c.points.Nonempty) : 1 ≤ c.Y := by
  simp only [Y]
  exact_mod_cast Finset.one_le_card.mpr hc

theorem mass_le_R_div_N {R : ℝ} {c : XYCluster}
    (hdom : RNDominance 1 R c) : c.X * c.Y ≤ R / c.N := by
  have hN : 0 < c.N := lt_of_lt_of_le zero_lt_one c.one_le_N
  rw [le_div_iff₀ hN]
  calc
    c.X * c.Y * c.N = c.N * c.X * c.Y := by ring
    _ ≤ R := by simpa [RNDominance] using hdom

private theorem scale_le_R {R : ℝ} {c : XYCluster}
    (hX : 1 ≤ c.X) (hc : c.points.Nonempty)
    (hdom : RNDominance 1 R c) : c.N ≤ R := by
  have hY : 1 ≤ c.Y := one_le_Y_of_nonempty hc
  calc
    c.N = c.N * 1 := by ring
    _ ≤ c.N * (c.X * c.Y) :=
      mul_le_mul_of_nonneg_left
        (one_le_mul_of_one_le_of_one_le hX hY)
        (le_trans zero_le_one c.one_le_N)
    _ = c.N * c.X * c.Y := by ring
    _ ≤ R := by simpa [RNDominance] using hdom

private theorem one_le_R_div_N {R : ℝ} {c : XYCluster}
    (hX : 1 ≤ c.X) (hc : c.points.Nonempty)
    (hdom : RNDominance 1 R c) : 1 ≤ R / c.N := by
  have hN : 0 < c.N := lt_of_lt_of_le zero_lt_one c.one_le_N
  exact (le_div_iff₀ hN).2 (by simpa using scale_le_R hX hc hdom)

private theorem reverseGain_le_max_div {R : ℝ} {a b : XYCluster}
    (haX : 1 ≤ a.X) (hbX : 1 ≤ b.X)
    (ha : a.points.Nonempty) (hb : b.points.Nonempty)
    (hda : RNDominance 1 R a) (hdb : RNDominance 1 R b) :
    reverseGain a b ≤ max (R / a.N) (R / b.N) := by
  let r := max (R / a.N) (R / b.N)
  have hra1 : 1 ≤ R / a.N := one_le_R_div_N haX ha hda
  have hrb1 : 1 ≤ R / b.N := one_le_R_div_N hbX hb hdb
  have hr1 : 1 ≤ r := le_trans hra1 (le_max_left _ _)
  have hr0 : 0 ≤ r := zero_le_one.trans hr1
  have hYa : a.Y ≤ R / a.N := by
    calc
      a.Y = 1 * a.Y := by ring
      _ ≤ a.X * a.Y :=
        mul_le_mul_of_nonneg_right haX (by simp [Y])
      _ ≤ R / a.N := mass_le_R_div_N hda
  have hYar : a.Y ≤ r := hYa.trans (le_max_left _ _)
  have hNaR : a.N ≤ R := scale_le_R haX ha hda
  have hRrbN : R ≤ (R / b.N) * b.N := by
    have hbN : 0 < b.N := lt_of_lt_of_le zero_lt_one b.one_le_N
    field_simp
    rfl
  have hNarbN : a.N ≤ r * b.N := by
    calc
      a.N ≤ R := hNaR
      _ ≤ (R / b.N) * b.N := hRrbN
      _ ≤ r * b.N :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (le_trans zero_le_one b.one_le_N)
  have hNaPow : a.N ^ 4 ≤ (r * b.N) ^ 4 :=
    pow_le_pow_left₀ (le_trans zero_le_one a.one_le_N) hNarbN 4
  have hPb : 0 < b.P := P_pos_of_nonempty hb
  have hP :
      a.P / b.P ≤ r ^ 8 := by
    rw [div_le_iff₀ hPb]
    calc
      a.P = a.Y * a.N ^ 4 := rfl
      _ ≤ r * (r * b.N) ^ 4 :=
        mul_le_mul hYar hNaPow (pow_nonneg (le_trans zero_le_one a.one_le_N) 4) hr0
      _ = r ^ 5 * b.N ^ 4 := by ring
      _ ≤ r ^ 8 * b.N ^ 4 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr1 (by omega))
          (pow_nonneg (le_trans zero_le_one b.one_le_N) 4)
      _ ≤ r ^ 8 * (b.Y * b.N ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 8)
        calc
          b.N ^ 4 = 1 * b.N ^ 4 := by ring
          _ ≤ b.Y * b.N ^ 4 :=
            mul_le_mul_of_nonneg_right (one_le_Y_of_nonempty hb)
              (pow_nonneg (le_trans zero_le_one b.one_le_N) 4)
      _ = r ^ 8 * b.P := rfl
  exact max_one_rpow_eighth_le
    (div_nonneg (P_nonneg' a) (P_nonneg' b)) hr1 hP

private theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  rw [Real.sqrt_le_iff]
  refine ⟨zero_le_one.trans hx, ?_⟩
  calc
    x = x * 1 := by ring
    _ ≤ x * x := mul_le_mul_of_nonneg_left hx (zero_le_one.trans hx)
    _ = x ^ 2 := by ring

theorem line593_of_dominance_one {R : ℝ} {a b : XYCluster}
    (haX : 1 ≤ a.X) (hbX : 1 ≤ b.X)
    (ha : a.points.Nonempty) (hb : b.points.Nonempty)
    (hda : RNDominance 1 R a) (hdb : RNDominance 1 R b) :
    Line593 1 R a b := by
  have hra1 : 1 ≤ R / a.N := one_le_R_div_N haX ha hda
  have hrb1 : 1 ≤ R / b.N := one_le_R_div_N hbX hb hdb
  have hra0 : 0 ≤ R / a.N := zero_le_one.trans hra1
  have hrb0 : 0 ≤ R / b.N := zero_le_one.trans hrb1
  have hfa : Real.sqrt a.X * a.Y ≤ R / a.N := by
    calc
      Real.sqrt a.X * a.Y ≤ a.X * a.Y :=
        mul_le_mul_of_nonneg_right (sqrt_le_self_of_one_le haX) (by simp [Y])
      _ ≤ R / a.N := mass_le_R_div_N hda
  have hfb : Real.sqrt b.X * b.Y ≤ R / b.N := by
    calc
      Real.sqrt b.X * b.Y ≤ b.X * b.Y :=
        mul_le_mul_of_nonneg_right (sqrt_le_self_of_one_le hbX) (by simp [Y])
      _ ≤ R / b.N := mass_le_R_div_N hdb
  have hg := reverseGain_le_max_div haX hbX ha hb hda hdb
  have hrprod :
      max (R / a.N) (R / b.N) ≤ (R / a.N) * (R / b.N) := by
    rw [max_le_iff]
    exact ⟨by
      calc
        R / a.N = (R / a.N) * 1 := by ring
        _ ≤ (R / a.N) * (R / b.N) :=
          mul_le_mul_of_nonneg_left hrb1 hra0,
      by
        calc
          R / b.N = 1 * (R / b.N) := by ring
          _ ≤ (R / a.N) * (R / b.N) :=
            mul_le_mul_of_nonneg_right hra1 hrb0⟩
  unfold Line593
  calc
    Real.sqrt a.X * a.Y * (Real.sqrt b.X * b.Y) * reverseGain a b ≤
        ((R / a.N) * (R / b.N)) *
          max (R / a.N) (R / b.N) := by
      apply mul_le_mul
      · exact mul_le_mul hfa hfb
          (mul_nonneg (Real.sqrt_nonneg _) (by simp [Y])) hra0
      · exact hg
      · exact le_trans zero_le_one (le_max_left _ _)
      · exact mul_nonneg hra0 hrb0
    _ ≤ ((R / a.N) * (R / b.N)) *
          ((R / a.N) * (R / b.N)) :=
      mul_le_mul_of_nonneg_left hrprod (mul_nonneg hra0 hrb0)
    _ = 1 * ((R / a.N) ^ 2 * (R / b.N) ^ 2) := by ring

private theorem reverseGain_le_right_div {R : ℝ} {a b : XYCluster}
    (haX : 1 ≤ a.X) (hbX : 1 ≤ b.X)
    (ha : a.points.Nonempty) (hb : b.points.Nonempty)
    (hda : RNDominance 1 R a) (hdb : RNDominance 1 R b) :
    reverseGain a b ≤ R / b.N := by
  have haN : 0 < a.N := lt_of_lt_of_le zero_lt_one a.one_le_N
  have hbN : 0 < b.N := lt_of_lt_of_le zero_lt_one b.one_le_N
  have hRpos : 0 < R := lt_of_lt_of_le haN (scale_le_R haX ha hda)
  have hrb1 : 1 ≤ R / b.N := one_le_R_div_N hbX hb hdb
  by_cases hba : b.N ≤ a.N
  · have hdiv : R / a.N ≤ R / b.N :=
      div_le_div_of_nonneg_left hRpos.le hbN hba
    have hmax : max (R / a.N) (R / b.N) = R / b.N := max_eq_right hdiv
    simpa only [hmax] using reverseGain_le_max_div haX hbX ha hb hda hdb
  · have hab : a.N ≤ b.N := le_of_not_ge hba
    have hYa : a.Y * a.N ≤ R := by
      have hm := mass_le_R_div_N hda
      rw [le_div_iff₀ haN] at hm
      calc
        a.Y * a.N ≤ (a.X * a.Y) * a.N := by
          apply mul_le_mul_of_nonneg_right _ haN.le
          calc
            a.Y = 1 * a.Y := by ring
            _ ≤ a.X * a.Y :=
              mul_le_mul_of_nonneg_right haX (by simp [Y])
        _ ≤ R := hm
    have hpow : a.N ^ 3 ≤ b.N ^ 3 := pow_le_pow_left₀ haN.le hab 3
    have hPa :
        a.P ≤ (R / b.N) * b.P := by
      calc
        a.P = (a.Y * a.N) * a.N ^ 3 := by
          simp only [P]
          ring
        _ ≤ R * a.N ^ 3 :=
          mul_le_mul_of_nonneg_right hYa (pow_nonneg haN.le 3)
        _ ≤ R * b.N ^ 3 :=
          mul_le_mul_of_nonneg_left hpow hRpos.le
        _ ≤ R * (b.Y * b.N ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ hRpos.le
          calc
            b.N ^ 3 = 1 * b.N ^ 3 := by ring
            _ ≤ b.Y * b.N ^ 3 :=
              mul_le_mul_of_nonneg_right (one_le_Y_of_nonempty hb)
                (pow_nonneg hbN.le 3)
        _ = (R / b.N) * b.P := by
          unfold P
          field_simp
    have hratio : a.P / b.P ≤ R / b.N :=
      (div_le_iff₀ (P_pos_of_nonempty hb)).2 hPa
    have hratio8 : a.P / b.P ≤ (R / b.N) ^ 8 := by
      exact hratio.trans (by
        simpa only [pow_one] using
          (pow_le_pow_right₀ hrb1 (by omega : (1 : ℕ) ≤ 8)))
    exact max_one_rpow_eighth_le
      (div_nonneg (P_nonneg' a) (P_nonneg' b)) hrb1 hratio8

theorem line596_of_dominance_one {R : ℝ} {a b : XYCluster}
    (haX : 1 ≤ a.X) (hbX : 1 ≤ b.X)
    (ha : a.points.Nonempty) (hb : b.points.Nonempty)
    (hda : RNDominance 1 R a) (hdb : RNDominance 1 R b) :
    Line596 1 R a b := by
  have hrb0 : 0 ≤ R / b.N :=
    zero_le_one.trans (one_le_R_div_N hbX hb hdb)
  have hfb : Real.sqrt b.X * b.Y ≤ R / b.N := by
    calc
      Real.sqrt b.X * b.Y ≤ b.X * b.Y :=
        mul_le_mul_of_nonneg_right (sqrt_le_self_of_one_le hbX) (by simp [Y])
      _ ≤ R / b.N := mass_le_R_div_N hdb
  have hg := reverseGain_le_right_div haX hbX ha hb hda hdb
  unfold Line596
  calc
    Real.sqrt b.X * b.Y * reverseGain a b ≤
        (R / b.N) * (R / b.N) :=
      mul_le_mul hfb hg (le_trans zero_le_one (le_max_left _ _)) hrb0
    _ = 1 * (R / b.N) ^ 2 := by ring

theorem line598_of_dominance_one {R : ℝ} {a b : XYCluster}
    (haX : 1 ≤ a.X) (hbX : 1 ≤ b.X)
    (ha : a.points.Nonempty) (hb : b.points.Nonempty)
    (hda : RNDominance 1 R a) (hdb : RNDominance 1 R b) :
    Line598 1 R a b := by
  let r := max (R / a.N) (R / b.N)
  have hra1 : 1 ≤ R / a.N := one_le_R_div_N haX ha hda
  have hrb1 : 1 ≤ R / b.N := one_le_R_div_N hbX hb hdb
  have hr1 : 1 ≤ r := le_trans hra1 (le_max_left _ _)
  have hr0 : 0 ≤ r := zero_le_one.trans hr1
  have hXYa : a.X * a.Y ≤ r :=
    (mass_le_R_div_N hda).trans (le_max_left _ _)
  have hYa : a.Y ≤ r := by
    calc
      a.Y = 1 * a.Y := by ring
      _ ≤ a.X * a.Y :=
        mul_le_mul_of_nonneg_right haX (by simp [Y])
      _ ≤ r := hXYa
  have hYb : b.Y ≤ r := by
    calc
      b.Y = 1 * b.Y := by ring
      _ ≤ b.X * b.Y :=
        mul_le_mul_of_nonneg_right hbX (by simp [Y])
      _ ≤ R / b.N := mass_le_R_div_N hdb
      _ ≤ r := le_max_right _ _
  have hsXY : Real.sqrt (a.X * a.Y) ≤ Real.sqrt r :=
    Real.sqrt_le_sqrt hXYa
  have hsY :
      max (Real.sqrt a.Y) (Real.sqrt b.Y) ≤ Real.sqrt r := by
    rw [max_le_iff]
    exact ⟨Real.sqrt_le_sqrt hYa, Real.sqrt_le_sqrt hYb⟩
  have hfirst :
      Real.sqrt (a.X * a.Y) *
          max (Real.sqrt a.Y) (Real.sqrt b.Y) ≤ r := by
    calc
      _ ≤ Real.sqrt r * Real.sqrt r :=
        mul_le_mul hsXY hsY
          ((Real.sqrt_nonneg a.Y).trans (le_max_left _ _))
          (Real.sqrt_nonneg _)
      _ = r := Real.mul_self_sqrt hr0
  have hg : reverseGain a b ≤ r :=
    reverseGain_le_max_div haX hbX ha hb hda hdb
  have hRpos : 0 < R :=
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one a.one_le_N)
      (scale_le_R haX ha hda)
  have hdiv : R / min a.N b.N = r := by
    dsimp [r]
    by_cases hab : a.N ≤ b.N
    · have hbaDiv : R / b.N ≤ R / a.N :=
        div_le_div_of_nonneg_left hRpos.le
          (lt_of_lt_of_le zero_lt_one a.one_le_N) hab
      rw [min_eq_left hab, max_eq_left hbaDiv]
    · have hba : b.N ≤ a.N := le_of_not_ge hab
      have habDiv : R / a.N ≤ R / b.N :=
        div_le_div_of_nonneg_left hRpos.le
          (lt_of_lt_of_le zero_lt_one b.one_le_N) hba
      rw [min_eq_right hba, max_eq_right habDiv]
  unfold Line598
  calc
    Real.sqrt (a.X * a.Y) * max (Real.sqrt a.Y) (Real.sqrt b.Y) *
        reverseGain a b ≤ r * r :=
      mul_le_mul hfirst hg (le_trans zero_le_one (le_max_left _ _)) hr0
    _ = 1 * (R / min a.N b.N) ^ 2 := by rw [hdiv]; ring

/-- Direct constructor from the exact constant-one Stage-1 mass bounds. -/
theorem mixedScaleCertificate_of_dominance_one {R : ℝ} {a b : XYCluster}
    (haX : 1 ≤ a.X) (hbX : 1 ≤ b.X)
    (ha : a.points.Nonempty) (hb : b.points.Nonempty)
    (hda : RNDominance 1 R a) (hdb : RNDominance 1 R b) :
    MixedScaleCertificate 1 1 R a b :=
  ⟨hda, hdb, line593_of_dominance_one haX hbX ha hb hda hdb,
    line596_of_dominance_one haX hbX ha hb hda hdb,
    line598_of_dominance_one haX hbX ha hb hda hdb⟩

/--
Constant-carrying constructor used by the single-scale assembly.

The dyadic bucket has fewer than twice its recorded `Y` points, so the
root-scale budget naturally supplies `RNDominance 2 R`.  Viewing this as
constant-one dominance at radius `2 * R` gives factors `16`, `4`, and `4`
in (5.93), (5.96), and (5.98), respectively; the latter two are enlarged
to the common numerical constant `16`.
-/
theorem mixedScaleCertificate_of_dominance_two {R : ℝ} {a b : XYCluster}
    (haX : 1 ≤ a.X) (hbX : 1 ≤ b.X)
    (ha : a.points.Nonempty) (hb : b.points.Nonempty)
    (hda : RNDominance 2 R a) (hdb : RNDominance 2 R b) :
    MixedScaleCertificate 2 16 R a b := by
  have hda' : RNDominance 1 (2 * R) a := by
    simpa [RNDominance] using hda
  have hdb' : RNDominance 1 (2 * R) b := by
    simpa [RNDominance] using hdb
  have h593' := line593_of_dominance_one haX hbX ha hb hda' hdb'
  have h596' := line596_of_dominance_one haX hbX ha hb hda' hdb'
  have h598' := line598_of_dominance_one haX hbX ha hb hda' hdb'
  have h593 : Line593 16 R a b := by
    unfold Line593 at h593' ⊢
    convert h593' using 1
    all_goals ring
  have h596four : Line596 4 R a b := by
    unfold Line596 at h596' ⊢
    convert h596' using 1
    all_goals ring
  have h596 : Line596 16 R a b := by
    unfold Line596 at h596four ⊢
    exact h596four.trans (by
      have hsq : 0 ≤ (R / b.N) ^ 2 := sq_nonneg _
      nlinarith)
  have h598four : Line598 4 R a b := by
    unfold Line598 at h598' ⊢
    convert h598' using 1
    all_goals ring
  have h598 : Line598 16 R a b := by
    unfold Line598 at h598four ⊢
    exact h598four.trans (by
      have hsq : 0 ≤ (R / min a.N b.N) ^ 2 := sq_nonneg _
      nlinarith)
  exact ⟨hda, hdb, h593, h596, h598⟩

theorem forwardGain_nonneg (a b : XYCluster) : 0 ≤ forwardGain a b := by
  unfold forwardGain
  exact le_min zero_le_one
    (Real.rpow_nonneg (div_nonneg (P_nonneg' b) (P_nonneg' a)) _)

theorem reverseGain_one_le (a b : XYCluster) : 1 ≤ reverseGain a b := by
  exact le_max_left _ _

theorem forwardGain_mul_reverseGain {a b : XYCluster}
    (ha : a.points.Nonempty) (hb : b.points.Nonempty) :
    forwardGain a b * reverseGain a b = 1 := by
  have hpa : 0 < a.P := P_pos_of_nonempty ha
  have hpb : 0 < b.P := P_pos_of_nonempty hb
  have habpos : 0 < a.P / b.P := div_pos hpa hpb
  have hbapos : 0 < b.P / a.P := div_pos hpb hpa
  have hprod : (b.P / a.P) * (a.P / b.P) = 1 := by
    field_simp
  by_cases hab : a.P ≤ b.P
  · have hba : 1 ≤ b.P / a.P := (le_div_iff₀ hpa).2 (by simpa [one_mul])
    have hab' : a.P / b.P ≤ 1 := (div_le_one hpb).2 hab
    have hrba : 1 ≤ (b.P / a.P) ^ (1 / 8 : ℝ) :=
      Real.one_le_rpow hba (by norm_num)
    have hrab : (a.P / b.P) ^ (1 / 8 : ℝ) ≤ 1 :=
      Real.rpow_le_one (le_of_lt habpos) hab' (by norm_num)
    rw [forwardGain, reverseGain, min_eq_left hrba, max_eq_left hrab]
    simp
  · have hba : b.P ≤ a.P := le_of_not_ge hab
    have hrab : 1 ≤ (a.P / b.P) ^ (1 / 8 : ℝ) :=
      Real.one_le_rpow ((le_div_iff₀ hpb).2 (by simpa [one_mul])) (by norm_num)
    have hrba : (b.P / a.P) ^ (1 / 8 : ℝ) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hbapos) ((div_le_one hpa).2 hba) (by norm_num)
    rw [forwardGain, reverseGain, min_eq_right hrba, max_eq_right hrab]
    rw [← Real.mul_rpow (le_of_lt hbapos) (le_of_lt habpos), hprod]
    simp

/-- The false/false branch of (5.91), directly from Lemma 5.14. -/
theorem mixedPairInner_le_unskipped :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : XYCluster) (R : ℝ) (u : Fin 4 → ℤ),
      mixedPairInner a b R false false u ≤ C * mixedTarget a b false false := by
  obtain ⟨C, hC, h⟩ := pairInner_le_5_91_unskipped
  refine ⟨C, hC, fun a b R u => ?_⟩
  calc
    mixedPairInner a b 1 false false u =
        a.X * b.X *
          (∑ x ∈ a.points.filter (fun x => a.N ≤ znorm (u - x)),
            ∑ y ∈ b.points.filter (fun y => max a.N b.N ≤ znorm (x - y)),
              (znorm (u - x))⁻¹ ^ 2 * (znorm (x - y))⁻¹ ^ 2) := by
      unfold mixedPairInner strongLambda lambda
      simp only [Bool.false_eq_true, if_false]
      rw [Finset.sum_filter]
      apply congrArg (a.X * b.X * ·)
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hax : a.N ≤ znorm (u - x)
      · simp only [hax, if_true]
        rw [Finset.mul_sum]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hby : max a.N b.N ≤ znorm (x - y)
        · simp [hby]
        · simp [hby]
      · simp [hax]
    _ ≤ C * a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2 *
          b.X * Real.sqrt b.Y * b.N⁻¹ ^ 2 * forwardGain a b := by
      simpa only [forwardGain] using h a b u
    _ = C * mixedTarget a b false false := by
      simp [mixedTarget, skipXi]
      ring

/-- Exact rough value in the both-skipped branch, the left side of (5.93). -/
theorem mixedPairInner_bothSkipped (a b : XYCluster) (R : ℝ)
    (u : Fin 4 → ℤ) :
    mixedPairInner a b R true true u =
      a.X * b.X * a.Y * b.Y * R⁻¹ ^ 4 := by
  unfold mixedPairInner strongLambda lambda Y
  simp only [if_true, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The analytic summation used before applying the numerical condition (5.96). -/
theorem mixedPairInner_rightSkipped_rough :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : XYCluster) (R : ℝ) (u : Fin 4 → ℤ),
      mixedPairInner a b R false true u ≤
        C * (a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2) *
          (b.X * b.Y * R⁻¹ ^ 2) := by
  obtain ⟨C, hC, hsum⟩ := sum_inv_sq_le
  refine ⟨C, hC, fun a b R u => ?_⟩
  have hs := hsum a.points a.N a.one_le_N a.separated u
  have hfac : 0 ≤ a.X * b.X * (b.Y * R⁻¹ ^ 2) := by
    exact mul_nonneg (mul_nonneg a.X_nonneg b.X_nonneg)
      (mul_nonneg (by simp [Y]) (sq_nonneg _))
  calc
    mixedPairInner a b R false true u =
        (a.X * b.X) *
          (∑ x ∈ a.points.filter (fun x => a.N ≤ znorm (u - x)),
            (znorm (u - x))⁻¹ ^ 2) * (b.Y * R⁻¹ ^ 2) := by
      unfold mixedPairInner strongLambda lambda Y
      simp only [Bool.false_eq_true, if_false, if_true, Finset.sum_const,
        nsmul_eq_mul]
      rw [← Finset.sum_mul]
      rw [Finset.sum_filter]
      ring
    _ ≤ (a.X * b.X) *
          (C * Real.sqrt (a.points.card : ℝ) * a.N⁻¹ ^ 2) *
            (b.Y * R⁻¹ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hs hfac
      nlinarith
    _ = C * (a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2) *
          (b.X * b.Y * R⁻¹ ^ 2) := by
      simp only [Y]
      ring

/--
The analytic summation used before (5.98).  The branch records exactly the
paper's instruction to sum the variable belonging to the larger scale.
-/
theorem mixedPairInner_leftSkipped_rough :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : XYCluster) (R : ℝ) (u : Fin 4 → ℤ),
      mixedPairInner a b R true false u ≤
        C * a.X * b.X * R⁻¹ ^ 2 *
          (if a.N ≤ b.N then a.Y * Real.sqrt b.Y * b.N⁻¹ ^ 2
           else b.Y * Real.sqrt a.Y * a.N⁻¹ ^ 2) := by
  obtain ⟨C, hC, hsum⟩ := sum_inv_sq_le
  refine ⟨C, hC, fun a b R u => ?_⟩
  by_cases hab : a.N ≤ b.N
  · have hs : ∀ x : Fin 4 → ℤ,
        ∑ y ∈ b.points,
          (if b.N ≤ znorm (x - y) then (znorm (x - y))⁻¹ ^ 2 else 0) ≤
            C * Real.sqrt (b.points.card : ℝ) * b.N⁻¹ ^ 2 := by
      intro x
      have hx := hsum b.points b.N b.one_le_N b.separated x
      rwa [Finset.sum_filter] at hx
    calc
      mixedPairInner a b R true false u =
          a.X * b.X * ∑ x ∈ a.points, R⁻¹ ^ 2 *
            ∑ y ∈ b.points,
              (if b.N ≤ znorm (x - y) then (znorm (x - y))⁻¹ ^ 2 else 0) := by
        unfold mixedPairInner strongLambda lambda
        simp only [if_true, Bool.false_eq_true, if_false, max_eq_right hab]
      _ ≤ a.X * b.X * ∑ _x ∈ a.points, R⁻¹ ^ 2 *
            (C * Real.sqrt (b.points.card : ℝ) * b.N⁻¹ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg a.X_nonneg b.X_nonneg)
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hs x) (sq_nonneg _)
      _ = C * a.X * b.X * R⁻¹ ^ 2 *
            (if a.N ≤ b.N then a.Y * Real.sqrt b.Y * b.N⁻¹ ^ 2
             else b.Y * Real.sqrt a.Y * a.N⁻¹ ^ 2) := by
        simp only [hab, if_true, Finset.sum_const, nsmul_eq_mul, Y]
        ring
  · have hba : b.N ≤ a.N := le_of_not_ge hab
    have hs : ∀ y : Fin 4 → ℤ,
        ∑ x ∈ a.points,
          (if a.N ≤ znorm (y - x) then (znorm (y - x))⁻¹ ^ 2 else 0) ≤
            C * Real.sqrt (a.points.card : ℝ) * a.N⁻¹ ^ 2 := by
      intro y
      have hy := hsum a.points a.N a.one_le_N a.separated y
      rwa [Finset.sum_filter] at hy
    calc
      mixedPairInner a b R true false u =
          a.X * b.X * ∑ y ∈ b.points, R⁻¹ ^ 2 *
            ∑ x ∈ a.points,
              (if a.N ≤ znorm (y - x) then (znorm (y - x))⁻¹ ^ 2 else 0) := by
        unfold mixedPairInner strongLambda lambda
        simp only [if_true, Bool.false_eq_true, if_false, max_eq_left hba]
        apply congrArg (a.X * b.X * ·)
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro x hx
        rw [znorm_sub_comm x y]
      _ ≤ a.X * b.X * ∑ _y ∈ b.points, R⁻¹ ^ 2 *
            (C * Real.sqrt (a.points.card : ℝ) * a.N⁻¹ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg a.X_nonneg b.X_nonneg)
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_left (hs y) (sq_nonneg _)
      _ = C * a.X * b.X * R⁻¹ ^ 2 *
            (if a.N ≤ b.N then a.Y * Real.sqrt b.Y * b.N⁻¹ ^ 2
             else b.Y * Real.sqrt a.Y * a.N⁻¹ ^ 2) := by
        simp only [hab, if_false, Finset.sum_const, nsmul_eq_mul, Y]
        ring

private theorem mixedTarget_bothSkipped {a b : XYCluster}
    (haX : 0 < a.X) (hbX : 0 < b.X)
    (ha : a.points.Nonempty) (hb : b.points.Nonempty) :
    mixedTarget a b true true =
      Real.sqrt a.X * Real.sqrt b.X * a.N⁻¹ ^ 2 * b.N⁻¹ ^ 2 *
        forwardGain a b := by
  have haY : 0 < a.Y := Y_pos_of_nonempty ha
  have hbY : 0 < b.Y := Y_pos_of_nonempty hb
  have hsaX : 0 < Real.sqrt a.X := Real.sqrt_pos.2 haX
  have hsbX : 0 < Real.sqrt b.X := Real.sqrt_pos.2 hbX
  have hsaY : 0 < Real.sqrt a.Y := Real.sqrt_pos.2 haY
  have hsbY : 0 < Real.sqrt b.Y := Real.sqrt_pos.2 hbY
  unfold mixedTarget skipXi
  simp only [if_true]
  rw [Real.sqrt_mul haX.le, Real.sqrt_mul hbX.le]
  field_simp
  rw [← Real.sq_sqrt haX.le, ← Real.sq_sqrt hbX.le]
  simp

private theorem mixedTarget_rightSkipped {a b : XYCluster}
    (hbX : 0 < b.X) (hb : b.points.Nonempty) :
    mixedTarget a b false true =
      (a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2) *
        (Real.sqrt b.X * b.N⁻¹ ^ 2) * forwardGain a b := by
  have hbY : 0 < b.Y := Y_pos_of_nonempty hb
  have hsbX : 0 < Real.sqrt b.X := Real.sqrt_pos.2 hbX
  have hsbY : 0 < Real.sqrt b.Y := Real.sqrt_pos.2 hbY
  unfold mixedTarget skipXi
  simp only [Bool.false_eq_true, if_false, if_true, mul_one]
  rw [Real.sqrt_mul hbX.le]
  field_simp
  rw [← Real.sq_sqrt hbX.le]
  simp

private theorem mixedTarget_leftSkipped {a b : XYCluster}
    (haX : 0 < a.X) (ha : a.points.Nonempty) :
    mixedTarget a b true false =
      (Real.sqrt a.X * a.N⁻¹ ^ 2) *
        (b.X * Real.sqrt b.Y * b.N⁻¹ ^ 2) * forwardGain a b := by
  have haY : 0 < a.Y := Y_pos_of_nonempty ha
  have hsaX : 0 < Real.sqrt a.X := Real.sqrt_pos.2 haX
  have hsaY : 0 < Real.sqrt a.Y := Real.sqrt_pos.2 haY
  unfold mixedTarget skipXi
  simp only [if_true, Bool.false_eq_true, if_false, mul_one]
  rw [Real.sqrt_mul haX.le]
  field_simp
  rw [← Real.sq_sqrt haX.le]
  simp
  ring

theorem bothSkipped_le_of_line593 {K R : ℝ} {a b : XYCluster}
    (haX : 0 < a.X) (hbX : 0 < b.X)
    (ha : a.points.Nonempty) (hb : b.points.Nonempty)
    (hR : 0 < R) (h593 : Line593 K R a b) (u : Fin 4 → ℤ) :
    mixedPairInner a b R true true u ≤ K * mixedTarget a b true true := by
  have hsa : 0 ≤ Real.sqrt a.X := Real.sqrt_nonneg _
  have hsb : 0 ≤ Real.sqrt b.X := Real.sqrt_nonneg _
  have hg : 0 ≤ forwardGain a b := forwardGain_nonneg a b
  have hq : 0 ≤ Real.sqrt a.X * Real.sqrt b.X * R⁻¹ ^ 4 * forwardGain a b := by
    positivity
  have hm := mul_le_mul_of_nonneg_right h593 hq
  rw [mixedPairInner_bothSkipped]
  calc
    a.X * b.X * a.Y * b.Y * R⁻¹ ^ 4 =
        (Real.sqrt a.X * a.Y * (Real.sqrt b.X * b.Y) * reverseGain a b) *
          (Real.sqrt a.X * Real.sqrt b.X * R⁻¹ ^ 4 * forwardGain a b) := by
      symm
      calc
        _ = Real.sqrt a.X ^ 2 * Real.sqrt b.X ^ 2 * a.Y * b.Y * R⁻¹ ^ 4 *
              (forwardGain a b * reverseGain a b) := by ring
        _ = Real.sqrt a.X ^ 2 * Real.sqrt b.X ^ 2 * a.Y * b.Y * R⁻¹ ^ 4 := by
          rw [forwardGain_mul_reverseGain ha hb, mul_one]
        _ = _ := by rw [Real.sq_sqrt haX.le, Real.sq_sqrt hbX.le]
    _ ≤ (K * ((R / a.N) ^ 2 * (R / b.N) ^ 2)) *
          (Real.sqrt a.X * Real.sqrt b.X * R⁻¹ ^ 4 * forwardGain a b) := hm
    _ = K * mixedTarget a b true true := by
      rw [mixedTarget_bothSkipped haX hbX ha hb]
      have haN : 0 < a.N := lt_of_lt_of_le zero_lt_one a.one_le_N
      have hbN : 0 < b.N := lt_of_lt_of_le zero_lt_one b.one_le_N
      field_simp

/-- The false/true branch of (5.91), using precisely the sufficient condition (5.96). -/
theorem mixedPairInner_rightSkipped_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (K R : ℝ) (a b : XYCluster) (u : Fin 4 → ℤ),
      a.points.Nonempty → b.points.Nonempty → 0 < b.X → 0 < R →
      Line596 K R a b →
      mixedPairInner a b R false true u ≤
        C * K * mixedTarget a b false true := by
  obtain ⟨C, hC, hrough⟩ := mixedPairInner_rightSkipped_rough
  refine ⟨C, hC, fun K R a b u ha hb hbX hR h596 => ?_⟩
  have habase : 0 ≤ a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2 :=
    mul_nonneg (mul_nonneg a.X_nonneg (Real.sqrt_nonneg _)) (sq_nonneg _)
  have hq : 0 ≤ C * (a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2) *
      Real.sqrt b.X * R⁻¹ ^ 2 * forwardGain a b :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hC.le habase) (Real.sqrt_nonneg _)) (sq_nonneg _))
      (forwardGain_nonneg a b)
  have hm := mul_le_mul_of_nonneg_right h596 hq
  calc
    mixedPairInner a b R false true u ≤
        C * (a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2) *
          (b.X * b.Y * R⁻¹ ^ 2) := hrough a b R u
    _ = (Real.sqrt b.X * b.Y * reverseGain a b) *
          (C * (a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2) *
            Real.sqrt b.X * R⁻¹ ^ 2 * forwardGain a b) := by
      symm
      calc
        _ = C * (a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2) *
              (Real.sqrt b.X ^ 2 * b.Y * R⁻¹ ^ 2) *
                (forwardGain a b * reverseGain a b) := by ring
        _ = C * (a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2) *
              (Real.sqrt b.X ^ 2 * b.Y * R⁻¹ ^ 2) := by
          rw [forwardGain_mul_reverseGain ha hb, mul_one]
        _ = _ := by rw [Real.sq_sqrt hbX.le]
    _ ≤ (K * (R / b.N) ^ 2) *
          (C * (a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2) *
            Real.sqrt b.X * R⁻¹ ^ 2 * forwardGain a b) := hm
    _ = C * K * mixedTarget a b false true := by
      rw [mixedTarget_rightSkipped hbX hb]
      have hbN : 0 < b.N := lt_of_lt_of_le zero_lt_one b.one_le_N
      field_simp

private theorem line598_left_of_scale_le {K R : ℝ} {a b : XYCluster}
    (hab : a.N ≤ b.N) (h598 : Line598 K R a b) :
    Real.sqrt a.X * a.Y * reverseGain a b ≤ K * (R / a.N) ^ 2 := by
  have haY : 0 ≤ a.Y := by simp [Y]
  have hsmall :
      Real.sqrt a.X * a.Y ≤
        Real.sqrt (a.X * a.Y) * max (Real.sqrt a.Y) (Real.sqrt b.Y) := by
    calc
      Real.sqrt a.X * a.Y =
          Real.sqrt (a.X * a.Y) * Real.sqrt a.Y := by
        rw [Real.sqrt_mul a.X_nonneg]
        nth_rewrite 1 [← Real.sq_sqrt haY]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg _)
  calc
    Real.sqrt a.X * a.Y * reverseGain a b ≤
        (Real.sqrt (a.X * a.Y) * max (Real.sqrt a.Y) (Real.sqrt b.Y)) *
          reverseGain a b :=
      mul_le_mul_of_nonneg_right hsmall (le_trans zero_le_one (reverseGain_one_le a b))
    _ ≤ K * (R / min a.N b.N) ^ 2 := h598
    _ = K * (R / a.N) ^ 2 := by rw [min_eq_left hab]

private theorem line598_right_of_scale_le {K R : ℝ} {a b : XYCluster}
    (hba : b.N ≤ a.N) (h598 : Line598 K R a b) :
    Real.sqrt (a.X * a.Y) * Real.sqrt b.Y * reverseGain a b ≤
      K * (R / b.N) ^ 2 := by
  have hsmall :
      Real.sqrt (a.X * a.Y) * Real.sqrt b.Y ≤
        Real.sqrt (a.X * a.Y) * max (Real.sqrt a.Y) (Real.sqrt b.Y) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _)
  calc
    Real.sqrt (a.X * a.Y) * Real.sqrt b.Y * reverseGain a b ≤
        (Real.sqrt (a.X * a.Y) * max (Real.sqrt a.Y) (Real.sqrt b.Y)) *
          reverseGain a b :=
      mul_le_mul_of_nonneg_right hsmall (le_trans zero_le_one (reverseGain_one_le a b))
    _ ≤ K * (R / min a.N b.N) ^ 2 := h598
    _ = K * (R / b.N) ^ 2 := by rw [min_eq_right hba]

/-- The true/false branch of (5.91), with the two summation orders in (5.98). -/
theorem mixedPairInner_leftSkipped_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (K R : ℝ) (a b : XYCluster) (u : Fin 4 → ℤ),
      a.points.Nonempty → b.points.Nonempty → 0 < a.X → 0 < R →
      Line598 K R a b →
      mixedPairInner a b R true false u ≤
        C * K * mixedTarget a b true false := by
  obtain ⟨C, hC, hrough⟩ := mixedPairInner_leftSkipped_rough
  refine ⟨C, hC, fun K R a b u ha hb haX hR h598 => ?_⟩
  by_cases hab : a.N ≤ b.N
  · have hline := line598_left_of_scale_le hab h598
    have hq : 0 ≤ C * Real.sqrt a.X * b.X * Real.sqrt b.Y * b.N⁻¹ ^ 2 *
        R⁻¹ ^ 2 * forwardGain a b := by
      have h1 : 0 ≤ C * Real.sqrt a.X :=
        mul_nonneg hC.le (Real.sqrt_nonneg _)
      have h2 : 0 ≤ C * Real.sqrt a.X * b.X := mul_nonneg h1 b.X_nonneg
      have h3 : 0 ≤ C * Real.sqrt a.X * b.X * Real.sqrt b.Y :=
        mul_nonneg h2 (Real.sqrt_nonneg _)
      have h4 : 0 ≤ C * Real.sqrt a.X * b.X * Real.sqrt b.Y * b.N⁻¹ ^ 2 :=
        mul_nonneg h3 (sq_nonneg _)
      have h5 : 0 ≤ C * Real.sqrt a.X * b.X * Real.sqrt b.Y * b.N⁻¹ ^ 2 *
          R⁻¹ ^ 2 := mul_nonneg h4 (sq_nonneg _)
      exact mul_nonneg h5 (forwardGain_nonneg a b)
    have hm := mul_le_mul_of_nonneg_right hline hq
    calc
      mixedPairInner a b R true false u ≤
          C * a.X * b.X * R⁻¹ ^ 2 *
            (a.Y * Real.sqrt b.Y * b.N⁻¹ ^ 2) := by
        simpa only [hab, if_true] using hrough a b R u
      _ = (Real.sqrt a.X * a.Y * reverseGain a b) *
            (C * Real.sqrt a.X * b.X * Real.sqrt b.Y * b.N⁻¹ ^ 2 *
              R⁻¹ ^ 2 * forwardGain a b) := by
        symm
        calc
          _ = C * Real.sqrt a.X ^ 2 * b.X * a.Y * Real.sqrt b.Y *
                b.N⁻¹ ^ 2 * R⁻¹ ^ 2 *
                  (forwardGain a b * reverseGain a b) := by ring
          _ = C * Real.sqrt a.X ^ 2 * b.X * a.Y * Real.sqrt b.Y *
                b.N⁻¹ ^ 2 * R⁻¹ ^ 2 := by
            rw [forwardGain_mul_reverseGain ha hb, mul_one]
          _ = _ := by
            rw [Real.sq_sqrt haX.le]
            ring
      _ ≤ (K * (R / a.N) ^ 2) *
            (C * Real.sqrt a.X * b.X * Real.sqrt b.Y * b.N⁻¹ ^ 2 *
              R⁻¹ ^ 2 * forwardGain a b) := hm
      _ = C * K * mixedTarget a b true false := by
        rw [mixedTarget_leftSkipped haX ha]
        have haN : 0 < a.N := lt_of_lt_of_le zero_lt_one a.one_le_N
        field_simp
  · have hba : b.N ≤ a.N := le_of_not_ge hab
    have hline := line598_right_of_scale_le hba h598
    have hq : 0 ≤ C * Real.sqrt a.X * a.N⁻¹ ^ 2 * b.X * Real.sqrt b.Y *
        R⁻¹ ^ 2 * forwardGain a b := by
      have h1 : 0 ≤ C * Real.sqrt a.X :=
        mul_nonneg hC.le (Real.sqrt_nonneg _)
      have h2 : 0 ≤ C * Real.sqrt a.X * a.N⁻¹ ^ 2 :=
        mul_nonneg h1 (sq_nonneg _)
      have h3 : 0 ≤ C * Real.sqrt a.X * a.N⁻¹ ^ 2 * b.X :=
        mul_nonneg h2 b.X_nonneg
      have h4 : 0 ≤ C * Real.sqrt a.X * a.N⁻¹ ^ 2 * b.X * Real.sqrt b.Y :=
        mul_nonneg h3 (Real.sqrt_nonneg _)
      have h5 : 0 ≤ C * Real.sqrt a.X * a.N⁻¹ ^ 2 * b.X * Real.sqrt b.Y *
          R⁻¹ ^ 2 := mul_nonneg h4 (sq_nonneg _)
      exact mul_nonneg h5 (forwardGain_nonneg a b)
    have hm := mul_le_mul_of_nonneg_right hline hq
    calc
      mixedPairInner a b R true false u ≤
          C * a.X * b.X * R⁻¹ ^ 2 *
            (b.Y * Real.sqrt a.Y * a.N⁻¹ ^ 2) := by
        simpa only [hab, if_false] using hrough a b R u
      _ = (Real.sqrt (a.X * a.Y) * Real.sqrt b.Y * reverseGain a b) *
            (C * Real.sqrt a.X * a.N⁻¹ ^ 2 * b.X * Real.sqrt b.Y *
              R⁻¹ ^ 2 * forwardGain a b) := by
        rw [Real.sqrt_mul a.X_nonneg]
        symm
        calc
          _ = C * Real.sqrt a.X ^ 2 * b.X * Real.sqrt a.Y *
                Real.sqrt b.Y ^ 2 * a.N⁻¹ ^ 2 * R⁻¹ ^ 2 *
                  (forwardGain a b * reverseGain a b) := by ring
          _ = C * Real.sqrt a.X ^ 2 * b.X * Real.sqrt a.Y *
                Real.sqrt b.Y ^ 2 * a.N⁻¹ ^ 2 * R⁻¹ ^ 2 := by
            rw [forwardGain_mul_reverseGain ha hb, mul_one]
          _ = _ := by
            rw [Real.sq_sqrt haX.le, Real.sq_sqrt (by simp [Y])]
            ring
      _ ≤ (K * (R / b.N) ^ 2) *
            (C * Real.sqrt a.X * a.N⁻¹ ^ 2 * b.X * Real.sqrt b.Y *
              R⁻¹ ^ 2 * forwardGain a b) := hm
      _ = C * K * mixedTarget a b true false := by
        rw [mixedTarget_leftSkipped haX ha]
        have hbN : 0 < b.N := lt_of_lt_of_le zero_lt_one b.one_le_N
        field_simp

theorem mixedTarget_nonneg (a b : XYCluster) (skipA skipB : Bool) :
    0 ≤ mixedTarget a b skipA skipB := by
  have haBase : 0 ≤ a.X * Real.sqrt a.Y * a.N⁻¹ ^ 2 :=
    mul_nonneg (mul_nonneg a.X_nonneg (Real.sqrt_nonneg _)) (sq_nonneg _)
  have hbBase : 0 ≤ b.X * Real.sqrt b.Y * b.N⁻¹ ^ 2 :=
    mul_nonneg (mul_nonneg b.X_nonneg (Real.sqrt_nonneg _)) (sq_nonneg _)
  have hxiA : 0 ≤ skipXi a skipA := by
    cases skipA <;> simp [skipXi]
  have hxiB : 0 ≤ skipXi b skipB := by
    cases skipB <;> simp [skipXi]
  unfold mixedTarget
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg haBase hbBase) hxiA) hxiB)
    (forwardGain_nonneg a b)

/--
Uniform local bound (5.91), ready for the parity assembly.

`Kdom` is carried only by the explicit Stage-1 dominance fields of `cert`;
`Knum` is the constant in the three numerical consequences (5.93), (5.96),
and (5.98).  Thus the conclusion never hides a comparison constant.
-/
theorem mixedPairInner_le_5_91 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Kdom Knum R : ℝ) (a b : XYCluster) (skipA skipB : Bool)
        (u : Fin 4 → ℤ),
        0 ≤ Knum → 1 ≤ a.X → 1 ≤ b.X →
        a.points.Nonempty → b.points.Nonempty → 0 < R →
        MixedScaleCertificate Kdom Knum R a b →
        mixedPairInner a b R skipA skipB u ≤
          C * max 1 Knum * mixedTarget a b skipA skipB := by
  obtain ⟨Cu, hCu, hu⟩ := mixedPairInner_le_unskipped
  obtain ⟨Cr, hCr, hr⟩ := mixedPairInner_rightSkipped_le
  obtain ⟨Cl, hCl, hl⟩ := mixedPairInner_leftSkipped_le
  let C := max 1 (max Cu (max Cr Cl))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hCuC : Cu ≤ C :=
    le_trans (le_max_left Cu (max Cr Cl)) (le_max_right 1 (max Cu (max Cr Cl)))
  have hCrC : Cr ≤ C :=
    le_trans (le_trans (le_max_left Cr Cl) (le_max_right Cu (max Cr Cl)))
      (le_max_right 1 (max Cu (max Cr Cl)))
  have hClC : Cl ≤ C :=
    le_trans (le_trans (le_max_right Cr Cl) (le_max_right Cu (max Cr Cl)))
      (le_max_right 1 (max Cu (max Cr Cl)))
  refine ⟨C, hC, ?_⟩
  intro Kdom Knum R a b skipA skipB u hK haX hbX ha hb hR cert
  have haXpos : 0 < a.X := lt_of_lt_of_le zero_lt_one haX
  have hbXpos : 0 < b.X := lt_of_lt_of_le zero_lt_one hbX
  have hmax0 : 0 ≤ max 1 Knum := le_trans zero_le_one (le_max_left _ _)
  have hKmax : Knum ≤ max 1 Knum := le_max_right _ _
  cases skipA with
  | false =>
      cases skipB with
      | false =>
          have h0 := hu a b R u
          have hcoef : Cu ≤ C * max 1 Knum := by
            calc
              Cu ≤ C := hCuC
              _ = C * 1 := by ring
              _ ≤ C * max 1 Knum := mul_le_mul_of_nonneg_left (le_max_left _ _) hC.le
          exact h0.trans
            (mul_le_mul_of_nonneg_right hcoef (mixedTarget_nonneg a b false false))
      | true =>
          have h0 := hr Knum R a b u ha hb hbXpos hR cert.line596
          have hcoef : Cr * Knum ≤ C * max 1 Knum :=
            mul_le_mul hCrC hKmax hK hC.le
          exact h0.trans
            (mul_le_mul_of_nonneg_right hcoef (mixedTarget_nonneg a b false true))
  | true =>
      cases skipB with
      | false =>
          have h0 := hl Knum R a b u ha hb haXpos hR cert.line598
          have hcoef : Cl * Knum ≤ C * max 1 Knum :=
            mul_le_mul hClC hKmax hK hC.le
          exact h0.trans
            (mul_le_mul_of_nonneg_right hcoef (mixedTarget_nonneg a b true false))
      | true =>
          have h0 := bothSkipped_le_of_line593 haXpos hbXpos ha hb hR
            cert.line593 u
          have hcoef : Knum ≤ C * max 1 Knum := by
            calc
              Knum ≤ max 1 Knum := hKmax
              _ = 1 * max 1 Knum := by ring
              _ ≤ C * max 1 Knum := mul_le_mul_of_nonneg_right hC1 hmax0
          exact h0.trans
            (mul_le_mul_of_nonneg_right hcoef (mixedTarget_nonneg a b true true))

/--
Normalized constant-one convenience form of the local estimate.

The actual dyadic-bucket assembly uses
`mixedPairInner_le_5_91_of_dominance_two` below, because the cluster stores
the actual point-cardinality while the setup budget stores its dyadic floor.
-/
theorem mixedPairInner_le_5_91_of_dominance_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ (R : ℝ) (a b : XYCluster) (skipA skipB : Bool) (u : Fin 4 → ℤ),
        1 ≤ a.X → 1 ≤ b.X →
        a.points.Nonempty → b.points.Nonempty →
        RNDominance 1 R a → RNDominance 1 R b →
        mixedPairInner a b R skipA skipB u ≤
          C * mixedTarget a b skipA skipB := by
  obtain ⟨C, hC, hlocal⟩ := mixedPairInner_le_5_91
  refine ⟨C, hC, fun R a b skipA skipB u haX hbX ha hb hda hdb => ?_⟩
  have hR : 0 < R :=
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one a.one_le_N)
      (scale_le_R haX ha hda)
  have cert : MixedScaleCertificate 1 1 R a b :=
    mixedScaleCertificate_of_dominance_one haX hbX ha hb hda hdb
  simpa using hlocal 1 1 R a b skipA skipB u (by norm_num) haX hbX ha hb hR cert

/--
Assembly-facing form of (5.91).

The factor `2` in the root-scale dominance accounts for replacing the
dyadic bucket size by the actual number of points.  The induced numerical
constant `16` is absorbed into the universal constant in the conclusion.
-/
theorem mixedPairInner_le_5_91_of_dominance_two :
    ∃ C : ℝ, 0 < C ∧
      ∀ (R : ℝ) (a b : XYCluster) (skipA skipB : Bool) (u : Fin 4 → ℤ),
        1 ≤ a.X → 1 ≤ b.X →
        a.points.Nonempty → b.points.Nonempty →
        RNDominance 2 R a → RNDominance 2 R b →
        mixedPairInner a b R skipA skipB u ≤
          C * mixedTarget a b skipA skipB := by
  obtain ⟨C, hC, hlocal⟩ := mixedPairInner_le_5_91
  refine ⟨16 * C, by positivity, ?_⟩
  intro R a b skipA skipB u haX hbX ha hb hda hdb
  have hda' : RNDominance 1 (2 * R) a := by
    simpa [RNDominance] using hda
  have hR : 0 < R := by
    have haN : 0 < a.N := lt_of_lt_of_le zero_lt_one a.one_le_N
    have hscale : a.N ≤ 2 * R := scale_le_R haX ha hda'
    nlinarith
  have cert : MixedScaleCertificate 2 16 R a b :=
    mixedScaleCertificate_of_dominance_two haX hbX ha hb hda hdb
  have hbound :=
    hlocal 2 16 R a b skipA skipB u (by norm_num) haX hbX ha hb hR cert
  rw [max_eq_right (by norm_num : (1 : ℝ) ≤ 16)] at hbound
  calc
    mixedPairInner a b R skipA skipB u ≤
        C * 16 * mixedTarget a b skipA skipB := hbound
    _ = (16 * C) * mixedTarget a b skipA skipB := by ring

end XYCluster

end Anderson4D
