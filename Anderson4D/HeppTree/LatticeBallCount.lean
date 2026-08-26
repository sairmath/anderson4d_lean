import Anderson4D.PermSum.Local

/-!
# Absolute lattice-ball counts for the Hepp-tree volume estimate

This file isolates the geometric counting input in paper §5.3, Step 5.
Unlike the ambient-box bound used elsewhere to enumerate admissible
embeddings, these estimates are uniform in the box cutoff `M`.

The norm is `Anderson4D.znorm`, hence the sup norm on `ℤ⁴`.  We enumerate a
real-radius ball by filtering a finite coordinate box, then apply the
unit-separation packing estimate from `PermSum.Local`.  The resulting
absolute constant is `16`.  A union of `k` balls and the specialization
needed in paper (5.23) are provided at the end.
-/

open scoped BigOperators
open Finset

namespace Anderson4D

abbrev LatticePoint := Fin 4 → ℤ

/-! ## A finite set representing a real-radius lattice ball -/

/-- The finite set of integer points in the closed `znorm`-ball of radius
`R` around `c`.  The outer coordinate box is deliberately only an
enumeration device; membership is exactly the norm inequality. -/
noncomputable def latticeBallReal (c : LatticePoint) (R : ℝ) :
    Finset LatticePoint :=
  (Fintype.piFinset fun i : Fin 4 =>
    Finset.Icc (c i + ⌊-R⌋) (c i + ⌊R⌋)).filter
      fun x => znorm (x - c) ≤ R

@[simp] theorem mem_latticeBallReal {c x : LatticePoint} {R : ℝ} :
    x ∈ latticeBallReal c R ↔ znorm (x - c) ≤ R := by
  rw [latticeBallReal, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hx
    refine ⟨?_, hx⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hcoord := (znorm_coord_le (x - c) i).trans hx
    have habs :
        |(x i : ℝ) - (c i : ℝ)| ≤ R := by
      simpa only [Pi.sub_apply, Int.cast_sub] using hcoord
    rw [abs_le] at habs
    constructor
    · have hfloor : ((⌊-R⌋ : ℤ) : ℝ) ≤ -R := Int.floor_le _
      have hreal :
          ((c i + ⌊-R⌋ : ℤ) : ℝ) ≤ (x i : ℝ) := by
        push_cast
        linarith [hfloor, habs.1]
      exact_mod_cast hreal
    · have hdiff :
          (((x i - c i : ℤ) : ℝ)) ≤ R := by
        push_cast
        exact habs.2
      have hint : x i - c i ≤ ⌊R⌋ := Int.le_floor.mpr hdiff
      omega

/-- Distinct integer lattice points are `1`-separated in `znorm`. -/
theorem one_le_znorm_sub_of_ne {x y : LatticePoint} (hxy : x ≠ y) :
    1 ≤ znorm (x - y) := by
  by_contra h
  have hlt : znorm (x - y) < 1 := lt_of_not_ge h
  have hcoord := (znorm_lt_iff (x - y) 1 one_pos).mp hlt
  apply hxy
  funext i
  by_contra hi
  have honeInt : 1 ≤ |x i - y i| := Int.one_le_abs (sub_ne_zero.mpr hi)
  have honeReal :
      (1 : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)| := by
    exact_mod_cast honeInt
  have hsmall := hcoord i
  have hsmall' : |(x i : ℝ) - (y i : ℝ)| < 1 := by
    simpa only [Pi.sub_apply, Int.cast_sub] using hsmall
  exact (not_le_of_gt hsmall') honeReal

/-- Absolute real-radius lattice-ball count.  The constant `16` is
independent of the center, radius, and any ambient lattice cutoff. -/
theorem card_latticeBallReal_le (c : LatticePoint) (R : ℝ) :
    ((latticeBallReal c R).card : ℝ) ≤ 16 * (1 + R) ^ 4 := by
  let box : Finset LatticePoint :=
    Fintype.piFinset fun i : Fin 4 =>
      Finset.Icc (c i + ⌊-R⌋) (c i + ⌊R⌋)
  have hsep :
      ∀ x ∈ box, ∀ y ∈ box, x ≠ y → (1 : ℝ) ≤ znorm (x - y) :=
    fun x _ y _ hxy => one_le_znorm_sub_of_ne hxy
  have hpack := card_ball_center_le c box 1 (by norm_num) hsep R
  have hfilter :
      box.filter (fun x => znorm (c - x) ≤ R) =
        latticeBallReal c R := by
    apply Finset.ext
    intro x
    simp only [box, latticeBallReal, Finset.mem_filter,
      Fintype.mem_piFinset, Finset.mem_Icc]
    rw [znorm_sub_comm c x]
  rw [hfilter] at hpack
  calc
    ((latticeBallReal c R).card : ℝ)
        ≤ 16 * min (box.card : ℝ) ((R / 1 + 1) ^ 4) := hpack
    _ ≤ 16 * (R / 1 + 1) ^ 4 :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
    _ = 16 * (1 + R) ^ 4 := by ring

/-! ## A directly usable natural-radius version -/

/-- Natural-radius spelling of `latticeBallReal`. -/
noncomputable def latticeBallNat (c : LatticePoint) (R : ℕ) :
    Finset LatticePoint :=
  latticeBallReal c (R : ℝ)

@[simp] theorem mem_latticeBallNat {c x : LatticePoint} {R : ℕ} :
    x ∈ latticeBallNat c R ↔ znorm (x - c) ≤ R := by
  simp [latticeBallNat]

/-- Natural-number cardinality bound for a natural-radius ball. -/
theorem card_latticeBallNat_le (c : LatticePoint) (R : ℕ) :
    (latticeBallNat c R).card ≤ 16 * (R + 1) ^ 4 := by
  have h := card_latticeBallReal_le c (R : ℝ)
  change (((latticeBallNat c R).card : ℕ) : ℝ)
      ≤ 16 * (1 + (R : ℝ)) ^ 4 at h
  have hn : (latticeBallNat c R).card ≤ 16 * (1 + R) ^ 4 := by
    exact_mod_cast h
  simpa [Nat.add_comm] using hn

/-! ## Unions of balls and the paper (5.23) specialization -/

/-- Union of equal-radius lattice balls about a finite set of fixed
centers. -/
noncomputable def latticeBallUnion (centers : Finset LatticePoint) (R : ℝ) :
    Finset LatticePoint :=
  centers.biUnion fun c => latticeBallReal c R

@[simp] theorem mem_latticeBallUnion {centers : Finset LatticePoint}
    {R : ℝ} {x : LatticePoint} :
    x ∈ latticeBallUnion centers R ↔
      ∃ c ∈ centers, znorm (x - c) ≤ R := by
  simp [latticeBallUnion]

/-- A union of `k` fixed balls costs at most `k` times the absolute
single-ball bound. -/
theorem card_latticeBallUnion_le (centers : Finset LatticePoint) (R : ℝ) :
    ((latticeBallUnion centers R).card : ℝ)
      ≤ 16 * (centers.card : ℝ) * (1 + R) ^ 4 := by
  have hcardNat :
      (latticeBallUnion centers R).card
        ≤ ∑ c ∈ centers, (latticeBallReal c R).card := by
    exact Finset.card_biUnion_le
  calc
    ((latticeBallUnion centers R).card : ℝ)
        ≤ (((∑ c ∈ centers, (latticeBallReal c R).card) : ℕ) : ℝ) := by
          exact_mod_cast hcardNat
    _ = ∑ c ∈ centers, ((latticeBallReal c R).card : ℝ) := by
      simp
    _ ≤ ∑ _c ∈ centers, 16 * (1 + R) ^ 4 :=
      Finset.sum_le_sum fun c _ => card_latticeBallReal_le c R
    _ = 16 * (centers.card : ℝ) * (1 + R) ^ 4 := by
      simp
      ring

/-- Absolute constant used by the normalized Step-5 lattice count. -/
def step5LatticeConstant : ℕ := 3888

/-- Paper §5.3 Step 5, equation (5.23), in a form directly consumable when
the covering centers form a `Finset`.

The hypotheses encode:

* `Nr ≥ 1`;
* nonnegative subtree lengths `Ti,Tj`;
* at most `3(1 + Ti/Nr)` covering centers;
* radius `2(Nr+Tj)`.

The conclusion has exactly the normalized factors of (5.23), with the
absolute explicit constant `3888 = 16 · 3 · 3⁴`. -/
theorem card_latticeBallUnion_step5_le
    (centers : Finset LatticePoint) (Nr Ti Tj : ℝ)
    (hNr : 1 ≤ Nr) (hTi : 0 ≤ Ti) (hTj : 0 ≤ Tj)
    (hcenters :
      (centers.card : ℝ) ≤ 3 * (1 + Ti / Nr)) :
    ((latticeBallUnion centers (2 * (Nr + Tj))).card : ℝ)
      ≤ step5LatticeConstant * Nr ^ 4 *
        (1 + Ti / Nr) * (1 + Tj / Nr) ^ 4 := by
  have hNr0 : 0 < Nr := lt_of_lt_of_le one_pos hNr
  have hi0 : 0 ≤ 1 + Ti / Nr := by positivity
  have hj0 : 0 ≤ 1 + Tj / Nr := by positivity
  have hbase0 : 0 ≤ 1 + 2 * (Nr + Tj) := by positivity
  have hscale :
      1 + 2 * (Nr + Tj) ≤ 3 * Nr * (1 + Tj / Nr) := by
    calc
      1 + 2 * (Nr + Tj) ≤ 3 * (Nr + Tj) := by
        nlinarith
      _ = 3 * Nr * (1 + Tj / Nr) := by
        field_simp [ne_of_gt hNr0]
  have hpow :
      (1 + 2 * (Nr + Tj)) ^ 4
        ≤ (3 * Nr * (1 + Tj / Nr)) ^ 4 :=
    pow_le_pow_left₀ hbase0 hscale 4
  calc
    ((latticeBallUnion centers (2 * (Nr + Tj))).card : ℝ)
        ≤ 16 * (centers.card : ℝ) *
            (1 + 2 * (Nr + Tj)) ^ 4 :=
      card_latticeBallUnion_le centers _
    _ ≤ 16 * (3 * (1 + Ti / Nr)) *
          (1 + 2 * (Nr + Tj)) ^ 4 := by
      gcongr
    _ ≤ 16 * (3 * (1 + Ti / Nr)) *
          (3 * Nr * (1 + Tj / Nr)) ^ 4 := by
      gcongr
    _ = step5LatticeConstant * Nr ^ 4 *
          (1 + Ti / Nr) * (1 + Tj / Nr) ^ 4 := by
      norm_num [step5LatticeConstant]
      ring

/-! Indexed-center wrappers, convenient when the `k` centers are supplied
as a function rather than as a duplicate-free `Finset`. -/

/-- Union of the balls centered at an indexed family of `k` points. -/
noncomputable def latticeBallUnionFin {k : ℕ}
    (center : Fin k → LatticePoint) (R : ℝ) : Finset LatticePoint :=
  latticeBallUnion (Finset.univ.image center) R

@[simp] theorem mem_latticeBallUnionFin {k : ℕ}
    {center : Fin k → LatticePoint} {R : ℝ} {x : LatticePoint} :
    x ∈ latticeBallUnionFin center R ↔
      ∃ i : Fin k, znorm (x - center i) ≤ R := by
  simp [latticeBallUnionFin]

/-- The direct `k`-indexed union bound. -/
theorem card_latticeBallUnionFin_le {k : ℕ}
    (center : Fin k → LatticePoint) (R : ℝ) :
    ((latticeBallUnionFin center R).card : ℝ)
      ≤ 16 * k * (1 + R) ^ 4 := by
  have hcentersNat : (Finset.univ.image center).card ≤ k := by
    simpa using
      (Finset.card_image_le
        (s := (Finset.univ : Finset (Fin k))) (f := center))
  have hcentersReal :
      ((Finset.univ.image center).card : ℝ) ≤ k := by
    exact_mod_cast hcentersNat
  calc
    ((latticeBallUnionFin center R).card : ℝ)
        ≤ 16 * ((Finset.univ.image center).card : ℝ) * (1 + R) ^ 4 :=
      card_latticeBallUnion_le _ _
    _ ≤ 16 * k * (1 + R) ^ 4 := by
      gcongr

/-- Indexed-center form of (5.23). -/
theorem card_latticeBallUnionFin_step5_le {k : ℕ}
    (center : Fin k → LatticePoint) (Nr Ti Tj : ℝ)
    (hNr : 1 ≤ Nr) (hTi : 0 ≤ Ti) (hTj : 0 ≤ Tj)
    (hk : (k : ℝ) ≤ 3 * (1 + Ti / Nr)) :
    ((latticeBallUnionFin center (2 * (Nr + Tj))).card : ℝ)
      ≤ step5LatticeConstant * Nr ^ 4 *
        (1 + Ti / Nr) * (1 + Tj / Nr) ^ 4 := by
  have hcentersNat : (Finset.univ.image center).card ≤ k := by
    simpa using
      (Finset.card_image_le
        (s := (Finset.univ : Finset (Fin k))) (f := center))
  have hcenters :
      ((Finset.univ.image center).card : ℝ)
        ≤ 3 * (1 + Ti / Nr) := by
    exact (by exact_mod_cast hcentersNat : 
      ((Finset.univ.image center).card : ℝ) ≤ (k : ℝ)).trans hk
  exact card_latticeBallUnion_step5_le
    (Finset.univ.image center) Nr Ti Tj hNr hTi hTj hcenters

end Anderson4D
