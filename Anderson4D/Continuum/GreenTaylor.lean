import Anderson4D.Continuum.GreenRemainder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Local Taylor estimates for the four-dimensional Green kernel

The derivative formulas in `GreenRemainder` are stated at the origin of a
coordinate line.  The reduction in paper (4.9), however, needs derivatives
at every point of a short segment.  This file first transports those
formulas to an arbitrary parameter on a coordinate line and then proves a
one-dimensional quadratic Taylor estimate from the Hessian bound.

The hypotheses of the Green-kernel theorem are geometric: the whole
coordinate segment must stay in the open principal cube and a positive
distance from the singularity.  No Taylor estimate is assumed.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Real Set
open scoped Topology

/-! ## A scalar Taylor estimate -/

/-- A scalar function whose second derivative is bounded on the unordered
interval between `a` and `b` has a quadratic first-order Taylor remainder.

The constant `1` (rather than the sharp `1/2`) is convenient for the
paper's `≲` estimates and follows directly from two applications of the
mean-value inequality. -/
theorem abs_sub_sub_deriv_mul_le_of_abs_secondDeriv_le
    {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hM : 0 ≤ M)
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ uIcc a b, HasDerivAt f' (f'' t) t)
    (hbound : ∀ t ∈ uIcc a b, |f'' t| ≤ M) :
    |f b - f a - f' a * (b - a)| ≤ M * |b - a| ^ 2 := by
  have hLip :
      ∀ t ∈ uIcc a b, |f' t - f' a| ≤ M * |t - a| := by
    intro t ht
    have hmv :=
      (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x hx => (hf' x hx).hasDerivWithinAt)
        (fun x hx => by
          simpa only [Real.norm_eq_abs] using hbound x hx)
        left_mem_uIcc ht
    simpa only [Real.norm_eq_abs] using hmv
  let g : ℝ → ℝ := fun t => f t - f' a * (t - a)
  let g' : ℝ → ℝ := fun t => f' t - f' a
  have hg :
      ∀ t ∈ uIcc a b, HasDerivWithinAt g (g' t) (uIcc a b) t := by
    intro t ht
    have hlinear :
        HasDerivAt (fun s : ℝ => f' a * (s - a)) (f' a) t := by
      simpa using
        ((hasDerivAt_id t).sub_const a).const_mul (f' a)
    change HasDerivWithinAt
      (fun s => f s - f' a * (s - a))
      (f' t - f' a) (uIcc a b) t
    exact ((hf t ht).sub hlinear).hasDerivWithinAt
  have hgBound :
      ∀ t ∈ uIcc a b, ‖g' t‖ ≤ M * |b - a| := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact (hLip t ht).trans
      (mul_le_mul_of_nonneg_left
        (abs_sub_left_of_mem_uIcc ht) hM)
  have hmv :=
    (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      hg hgBound left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  calc
    |f b - f a - f' a * (b - a)| =
        |g b - g a| := by
          simp only [g, sub_self, mul_zero, sub_zero]
          congr 1
          ring
    _ ≤ (M * |b - a|) * |b - a| := hmv
    _ = M * |b - a| ^ 2 := by ring

/-- The classical closed-interval Lipschitz estimate, stated with
derivatives only on the open interval. -/
theorem abs_sub_le_of_continuousOn_of_abs_deriv_le
    {f f' : ℝ → ℝ} {a b C : ℝ}
    (hab : a < b)
    (hfcont : ContinuousOn f (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, |f' t| ≤ C) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |f x - f y| ≤ C * |x - y| := by
  have hinterior :
      ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b,
        |f x - f y| ≤ C * |x - y| := by
    intro x hx y hy
    have hsegment : uIcc x y ⊆ Ioo a b := by
      rw [← segment_eq_uIcc]
      exact (convex_Ioo a b).segment_subset hx hy
    have hmv :=
      (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun z hz => (hf z (hsegment hz)).hasDerivWithinAt)
        (fun z hz => by
          rw [Real.norm_eq_abs]
          exact hbound z (hsegment hz))
        left_mem_uIcc right_mem_uIcc
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    calc
      |f x - f y| = |f y - f x| := abs_sub_comm _ _
      _ ≤ C * |y - x| := hmv
      _ = C * |x - y| := by rw [abs_sub_comm]
  have hfirst :
      ∀ y ∈ Ioo a b, ∀ x ∈ Icc a b,
        |f x - f y| ≤ C * |x - y| := by
    intro y hy x hx
    have hxcl : x ∈ closure (Ioo a b) := by
      rw [closure_Ioo hab.ne]
      exact hx
    apply le_on_closure
      (s := Ioo a b)
      (fun z hz => hinterior z hz y hy)
    · rw [closure_Ioo hab.ne]
      exact (hfcont.sub continuousOn_const).abs
    · rw [closure_Ioo hab.ne]
      exact continuousOn_const.mul
        (continuousOn_id.sub continuousOn_const).abs
    · exact hxcl
  intro x hx y hy
  have hycl : y ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact hy
  apply le_on_closure
    (s := Ioo a b)
    (fun z hz => hfirst z hz x hx)
  · rw [closure_Ioo hab.ne]
    exact (continuousOn_const.sub hfcont).abs
  · rw [closure_Ioo hab.ne]
    exact continuousOn_const.mul
      (continuousOn_const.sub continuousOn_id).abs
  · exact hycl

/-- Closed-interval variant of the scalar Taylor estimate.  Derivatives
are required only in the open interval; continuity of `f` and `f'`
identifies the one-sided derivatives at the endpoints.  This is the
form needed when a Green coordinate path ends on a fundamental-cell
face. -/
theorem abs_sub_sub_deriv_mul_le_of_continuousOn
    {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hab : a < b) (hM : 0 ≤ M)
    (hfcont : ContinuousOn f (Icc a b))
    (hf'cont : ContinuousOn f' (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f' (f'' t) t)
    (hbound : ∀ t ∈ Ioo a b, |f'' t| ≤ M) :
    |f b - f a - f' a * (b - a)| ≤ M * (b - a) ^ 2 := by
  have closed_lipschitz :
      ∀ (g g' : ℝ → ℝ) (C : ℝ),
        0 ≤ C →
        ContinuousOn g (Icc a b) →
        (∀ t ∈ Ioo a b, HasDerivAt g (g' t) t) →
        (∀ t ∈ Ioo a b, |g' t| ≤ C) →
        ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
          |g x - g y| ≤ C * |x - y| := by
    intro g g' C hC hgcont hg hgbound
    have hinterior :
        ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b,
          |g x - g y| ≤ C * |x - y| := by
      intro x hx y hy
      have hsegment : uIcc x y ⊆ Ioo a b := by
        rw [← segment_eq_uIcc]
        exact (convex_Ioo a b).segment_subset hx hy
      have hmv :=
        (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun z hz => (hg z (hsegment hz)).hasDerivWithinAt)
          (fun z hz => by
            rw [Real.norm_eq_abs]
            exact hgbound z (hsegment hz))
          left_mem_uIcc right_mem_uIcc
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
      calc
        |g x - g y| = |g y - g x| := abs_sub_comm _ _
        _ ≤ C * |y - x| := hmv
        _ = C * |x - y| := by rw [abs_sub_comm]
    have hfirst :
        ∀ y ∈ Ioo a b, ∀ x ∈ Icc a b,
          |g x - g y| ≤ C * |x - y| := by
      intro y hy x hx
      have hxcl : x ∈ closure (Ioo a b) := by
        rw [closure_Ioo hab.ne]
        exact hx
      apply le_on_closure
        (s := Ioo a b)
        (fun z hz => hinterior z hz y hy)
      · rw [closure_Ioo hab.ne]
        exact (hgcont.sub continuousOn_const).abs
      · rw [closure_Ioo hab.ne]
        exact continuousOn_const.mul
          (continuousOn_id.sub continuousOn_const).abs
      · exact hxcl
    intro x hx y hy
    have hycl : y ∈ closure (Ioo a b) := by
      rw [closure_Ioo hab.ne]
      exact hy
    apply le_on_closure
      (s := Ioo a b)
      (fun z hz => hfirst z hz x hx)
    · rw [closure_Ioo hab.ne]
      exact (continuousOn_const.sub hgcont).abs
    · rw [closure_Ioo hab.ne]
      exact continuousOn_const.mul
        (continuousOn_const.sub continuousOn_id).abs
    · exact hycl
  have hLip :
      ∀ t ∈ Icc a b, |f' t - f' a| ≤ M * |t - a| := by
    intro t ht
    exact closed_lipschitz f' f'' M hM hf'cont hf' hbound
      t ht a (left_mem_Icc.mpr hab.le)
  let g : ℝ → ℝ := fun t => f t - f' a * (t - a)
  let g' : ℝ → ℝ := fun t => f' t - f' a
  have hgcont : ContinuousOn g (Icc a b) :=
    hfcont.sub
      (continuousOn_const.mul
        (continuousOn_id.sub continuousOn_const))
  have hg :
      ∀ t ∈ Ioo a b, HasDerivAt g (g' t) t := by
    intro t ht
    have hlinear :
        HasDerivAt (fun s : ℝ => f' a * (s - a)) (f' a) t := by
      simpa using ((hasDerivAt_id t).sub_const a).const_mul (f' a)
    exact (hf t ht).sub hlinear
  have hgBound :
      ∀ t ∈ Ioo a b, |g' t| ≤ M * (b - a) := by
    intro t ht
    exact (hLip t (Ioo_subset_Icc_self ht)).trans
      (mul_le_mul_of_nonneg_left
        (by
          rw [abs_of_pos (sub_pos.mpr ht.1)]
          linarith [ht.2]) hM)
  have hcoef : 0 ≤ M * (b - a) :=
    mul_nonneg hM (sub_nonneg.mpr hab.le)
  have hmv :=
    closed_lipschitz g g' (M * (b - a))
      hcoef hgcont hg hgBound
      b (right_mem_Icc.mpr hab.le)
      a (left_mem_Icc.mpr hab.le)
  calc
    |f b - f a - f' a * (b - a)| =
        |g b - g a| := by
      simp only [g, sub_self, mul_zero, sub_zero]
      congr 1
      ring
    _ ≤ (M * (b - a)) * |b - a| := hmv
    _ = M * (b - a) ^ 2 := by
      rw [abs_of_pos (sub_pos.mpr hab)]
      ring

/-- Reverse-orientation form of the closed-interval Taylor estimate.  The
factor `2` pays for moving the linearization point from the left endpoint
to the right endpoint. -/
theorem abs_sub_sub_deriv_mul_le_of_continuousOn_rev
    {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hab : a < b) (hM : 0 ≤ M)
    (hfcont : ContinuousOn f (Icc a b))
    (hf'cont : ContinuousOn f' (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Ioo a b, HasDerivAt f' (f'' t) t)
    (hbound : ∀ t ∈ Ioo a b, |f'' t| ≤ M) :
    |f a - f b - f' b * (a - b)| ≤
      (2 * M) * (b - a) ^ 2 := by
  have hforward :=
    abs_sub_sub_deriv_mul_le_of_continuousOn
      hab hM hfcont hf'cont hf hf' hbound
  have hgrad :=
    abs_sub_le_of_continuousOn_of_abs_deriv_le
      hab hf'cont hf' hbound
      b (right_mem_Icc.mpr hab.le)
      a (left_mem_Icc.mpr hab.le)
  have hdecomp :
      f a - f b - f' b * (a - b) =
        -(f b - f a - f' a * (b - a)) +
          (f' b - f' a) * (b - a) := by ring
  rw [hdecomp]
  calc
    |-(f b - f a - f' a * (b - a)) +
        (f' b - f' a) * (b - a)| ≤
        |f b - f a - f' a * (b - a)| +
          |(f' b - f' a) * (b - a)| := by
      simpa only [abs_neg] using abs_add_le
        (-(f b - f a - f' a * (b - a)))
        ((f' b - f' a) * (b - a))
    _ ≤ M * (b - a) ^ 2 +
        (M * |b - a|) * |b - a| := by
      rw [abs_mul]
      exact add_le_add hforward
        (mul_le_mul_of_nonneg_right hgrad
          (abs_nonneg (b - a)))
    _ = (2 * M) * (b - a) ^ 2 := by
      rw [abs_of_pos (sub_pos.mpr hab)]
      ring

/-! ## Coordinate-line transport -/

theorem coordLine_add_taylor
    (x : R4) (i : Fin dim) (s t : ℝ) :
    coordLine (coordLine x i s) i t =
      coordLine x i (s + t) := by
  unfold coordLine
  module

theorem hasDerivAt_greenLocalLift_coord_at
    {x : R4} (i : Fin dim) {t : ℝ}
    (hopen : InOpenPrincipalCube (coordLine x i t))
    (hne : euclideanDistSq (coordLine x i t) ≠ 0) :
    HasDerivAt
      (fun s => greenLocalLift (coordLine x i s))
      (greenLocalGrad (coordLine x i t) i) t := by
  have hbase :=
    hasDerivAt_greenLocalLift_coord hopen hne i
  have hshift :
      HasDerivAt
        (fun s =>
          greenLocalLift
            (coordLine (coordLine x i t) i (s - t)))
        (greenLocalGrad (coordLine x i t) i) t := by
    have hc :=
      hbase.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
    simpa only [Function.comp_def, id, mul_one] using hc
  convert hshift using 1
  funext s
  rw [coordLine_add_taylor]
  congr 2
  ring

theorem hasDerivAt_greenLocalGrad_coord_at
    {x : R4} (i j : Fin dim) {t : ℝ}
    (hopen : InOpenPrincipalCube (coordLine x j t))
    (hne : euclideanDistSq (coordLine x j t) ≠ 0) :
    HasDerivAt
      (fun s => greenLocalGrad (coordLine x j s) i)
      (greenLocalHess (coordLine x j t) i j) t := by
  have hbase :=
    hasDerivAt_greenLocalGrad_coord hopen hne i j
  have hshift :
      HasDerivAt
        (fun s =>
          greenLocalGrad
            (coordLine (coordLine x j t) j (s - t)) i)
        (greenLocalHess (coordLine x j t) i j) t := by
    have hc :=
      hbase.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
    simpa only [Function.comp_def, id, mul_one] using hc
  convert hshift using 1
  funext s
  rw [coordLine_add_taylor]
  congr 3
  ring

/-! ## Green-kernel Taylor estimate on one coordinate segment -/

/-- Coordinate-line Taylor estimate with an explicit Hessian majorant. -/
theorem greenLocalLift_coord_taylor
    {x : R4} (i : Fin dim) {s M : ℝ}
    (hM : 0 ≤ M)
    (hopen : ∀ t ∈ uIcc 0 s,
      InOpenPrincipalCube (coordLine x i t))
    (hne : ∀ t ∈ uIcc 0 s,
      euclideanDistSq (coordLine x i t) ≠ 0)
    (hhess : ∀ t ∈ uIcc 0 s,
      |greenLocalHess (coordLine x i t) i i| ≤ M) :
    |greenLocalLift (coordLine x i s) - greenLocalLift x -
        greenLocalGrad x i * s| ≤
      M * |s| ^ 2 := by
  have h :=
    abs_sub_sub_deriv_mul_le_of_abs_secondDeriv_le
      (f := fun t => greenLocalLift (coordLine x i t))
      (f' := fun t => greenLocalGrad (coordLine x i t) i)
      (f'' := fun t => greenLocalHess (coordLine x i t) i i)
      (a := 0) (b := s) hM
      (fun t ht =>
        hasDerivAt_greenLocalLift_coord_at i
          (hopen t ht) (hne t ht))
      (fun t ht =>
        hasDerivAt_greenLocalGrad_coord_at i i
          (hopen t ht) (hne t ht))
      hhess
  simpa [coordLine] using h

theorem greenLocalHessSingularBound_nonneg :
    0 ≤ greenLocalHessSingularBound := by
  unfold greenLocalHessSingularBound
  apply add_nonneg
  · positivity
  · exact mul_nonneg (by positivity)
      nonzeroLatticeRemainderBound_nonneg

/-- The preceding Taylor estimate with its Hessian bound discharged from
the explicit `|x|⁻⁴` estimate.  The radius hypothesis says that the whole
coordinate segment stays at Euclidean distance at least `r` from the
singularity. -/
theorem greenLocalLift_coord_taylor_of_radius
    {x : R4} (i : Fin dim) {s r : ℝ}
    (hr : 0 < r)
    (hopen : ∀ t ∈ uIcc 0 s,
      InOpenPrincipalCube (coordLine x i t))
    (hradius : ∀ t ∈ uIcc 0 s,
      r ≤ √(euclideanDistSq (coordLine x i t))) :
    |greenLocalLift (coordLine x i s) - greenLocalLift x -
        greenLocalGrad x i * s| ≤
      (greenLocalHessSingularBound * r⁻¹ ^ 4) * |s| ^ 2 := by
  have hne :
      ∀ t ∈ uIcc 0 s,
        euclideanDistSq (coordLine x i t) ≠ 0 := by
    intro t ht hzero
    have hsqrt :
        √(euclideanDistSq (coordLine x i t)) = 0 := by
      rw [hzero, Real.sqrt_zero]
    have := hradius t ht
    rw [hsqrt] at this
    linarith
  apply greenLocalLift_coord_taylor
    (M := greenLocalHessSingularBound * r⁻¹ ^ 4)
    i
  · exact mul_nonneg greenLocalHessSingularBound_nonneg
      (pow_nonneg (inv_nonneg.mpr hr.le) _)
  · exact hopen
  · exact hne
  · intro t ht
    let d : ℝ := √(euclideanDistSq (coordLine x i t))
    have hd : 0 < d := lt_of_lt_of_le hr (hradius t ht)
    have hinv : d⁻¹ ≤ r⁻¹ :=
      (inv_le_inv₀ hd hr).2 (hradius t ht)
    have hinvpow : d⁻¹ ^ 4 ≤ r⁻¹ ^ 4 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hinv 4
    have hclosed :
        InClosedPrincipalCube (coordLine x i t) := by
      intro j
      exact (hopen t ht j).le
    calc
      |greenLocalHess (coordLine x i t) i i| ≤
          greenLocalHessSingularBound * d⁻¹ ^ 4 := by
        exact abs_greenLocalHess_singular
          hclosed (hne t ht) i i
      _ ≤ greenLocalHessSingularBound * r⁻¹ ^ 4 :=
        mul_le_mul_of_nonneg_left hinvpow
          greenLocalHessSingularBound_nonneg

/-! ## The four-coordinate rectangular path -/

/-- The corner obtained by replacing the first `k` coordinates of `a` by
the corresponding coordinates of `b`.  The five values `k = 0, ..., 4`
form the rectangular path used below. -/
def coordinateCorner (a b : R4) (k : Fin (dim + 1)) : R4 :=
  fun i => if i.val < k.val then b i else a i

@[simp]
theorem coordinateCorner_zero (a b : R4) :
    coordinateCorner a b 0 = a := by
  funext i
  simp [coordinateCorner]

@[simp]
theorem coordinateCorner_last (a b : R4) :
    coordinateCorner a b
        (⟨dim, by omega⟩ : Fin (dim + 1)) = b := by
  funext i
  simp [coordinateCorner, i.isLt]

/-- Consecutive corners differ by exactly one coordinate line. -/
theorem coordinateCorner_succ (a b : R4) (i : Fin dim) :
    coordinateCorner a b i.succ =
      coordLine (coordinateCorner a b i.castSucc) i
        (b i - a i) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [coordinateCorner, coordLine]
  · have hval : j.val ≠ i.val := by
      intro h
      exact hji (Fin.ext h)
    by_cases hlt : j.val < i.val
    · have hlt' : j.val < i.val + 1 := by omega
      simp [coordinateCorner, coordLine, hji, hlt, hlt']
    · have hlt' : ¬j.val < i.val + 1 := by omega
      simp [coordinateCorner, coordLine, hji, hlt, hlt']

/-- Exact telescoping of a function along the four-coordinate rectangular
path. -/
theorem coordinateCorner_telescope
    (f : R4 → ℝ) (a b : R4) :
    f b - f a =
      ∑ i : Fin dim,
        (f (coordinateCorner a b i.succ) -
          f (coordinateCorner a b i.castSucc)) := by
  change f b - f a =
    ∑ i : Fin 4,
      (f (coordinateCorner a b i.succ) -
        f (coordinateCorner a b i.castSucc))
  have hlast :
      coordinateCorner a b (4 : Fin 5) = b := by
    exact coordinateCorner_last a b
  simp [Fin.sum_univ_succ, hlast]
  ring

/-- Prefix form of the telescoping identity. -/
theorem coordinateCorner_prefix_telescope
    (f : R4 → ℝ) (a b : R4) (k : Fin (dim + 1)) :
    f (coordinateCorner a b k) - f a =
      ∑ i : Fin dim with i.val < k.val,
        (f (coordinateCorner a b i.succ) -
          f (coordinateCorner a b i.castSucc)) := by
  change f (coordinateCorner a b k) - f a =
    ∑ i : Fin 4 with i.val < k.val,
      (f (coordinateCorner a b i.succ) -
        f (coordinateCorner a b i.castSucc))
  fin_cases k <;>
    rw [Finset.sum_filter] <;>
    simp [Fin.sum_univ_succ]
  ring

/-- The coordinate expression for the linear Taylor term at `a`. -/
def coordinateLinearTerm
    (df : R4 → Fin dim → ℝ) (a b : R4) : ℝ :=
  ∑ i, df a i * (b i - a i)

/-- Exact decomposition into the four one-coordinate Taylor remainders and
the cost of moving the gradient from each intermediate corner back to the
initial point. -/
theorem coordinateTaylor_decomposition
    (f : R4 → ℝ) (df : R4 → Fin dim → ℝ) (a b : R4) :
    f b - f a - coordinateLinearTerm df a b =
      (∑ i : Fin dim,
        (f (coordinateCorner a b i.succ) -
          f (coordinateCorner a b i.castSucc) -
          df (coordinateCorner a b i.castSucc) i *
            (b i - a i))) +
      ∑ i : Fin dim,
        (df (coordinateCorner a b i.castSucc) i - df a i) *
          (b i - a i) := by
  have hgradient :
      (∑ i : Fin dim,
          (df (coordinateCorner a b i.castSucc) i - df a i) *
            (b i - a i)) =
        (∑ i : Fin dim,
          df (coordinateCorner a b i.castSucc) i *
            (b i - a i)) -
        ∑ i : Fin dim, df a i * (b i - a i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [coordinateCorner_telescope]
  unfold coordinateLinearTerm
  rw [hgradient]
  simp only [Finset.sum_sub_distrib]
  ring

/-- The `ℓ¹` length of the displacement used by the rectangular path. -/
def coordinateL1Dist (a b : R4) : ℝ :=
  ∑ i, |b i - a i|

theorem coordinateL1Dist_nonneg (a b : R4) :
    0 ≤ coordinateL1Dist a b := by
  unfold coordinateL1Dist
  positivity

private theorem sum_abs_sq_le_coordinateL1Dist_sq (a b : R4) :
    (∑ i : Fin dim, |b i - a i| ^ 2) ≤
      coordinateL1Dist a b ^ 2 := by
  have hcoord :
      ∀ i : Fin dim, |b i - a i| ≤ coordinateL1Dist a b := by
    intro i
    unfold coordinateL1Dist
    exact Finset.single_le_sum
      (fun j (_hj : j ∈ Finset.univ) => abs_nonneg (b j - a j))
      (Finset.mem_univ i)
  calc
    (∑ i : Fin dim, |b i - a i| ^ 2) ≤
        ∑ i : Fin dim,
          |b i - a i| * coordinateL1Dist a b := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (hcoord i)
        (abs_nonneg (b i - a i))
    _ = coordinateL1Dist a b ^ 2 := by
      rw [← Finset.sum_mul]
      unfold coordinateL1Dist
      ring

/-- A quantitative rectangular-path Taylor lemma.  It separates the two
analytic inputs needed later:

* a quadratic remainder on each coordinate edge;
* a Lipschitz estimate comparing the gradient at an intermediate corner
  to the gradient at the initial point.

For the Green kernel, both inputs follow from its Hessian estimate. -/
theorem coordinateTaylor_bound
    (f : R4 → ℝ) (df : R4 → Fin dim → ℝ)
    (a b : R4) {M : ℝ}
    (hM : 0 ≤ M)
    (hremainder : ∀ i : Fin dim,
      |f (coordinateCorner a b i.succ) -
          f (coordinateCorner a b i.castSucc) -
          df (coordinateCorner a b i.castSucc) i *
            (b i - a i)| ≤
        M * |b i - a i| ^ 2)
    (hgradient : ∀ i : Fin dim,
      |df (coordinateCorner a b i.castSucc) i - df a i| ≤
        M * coordinateL1Dist a b) :
    |f b - f a - coordinateLinearTerm df a b| ≤
      (2 * M) * coordinateL1Dist a b ^ 2 := by
  let rem : Fin dim → ℝ := fun i =>
    f (coordinateCorner a b i.succ) -
      f (coordinateCorner a b i.castSucc) -
      df (coordinateCorner a b i.castSucc) i *
        (b i - a i)
  let gradMove : Fin dim → ℝ := fun i =>
    (df (coordinateCorner a b i.castSucc) i - df a i) *
      (b i - a i)
  have hrem :
      |∑ i, rem i| ≤ M * coordinateL1Dist a b ^ 2 := by
    calc
      |∑ i, rem i| ≤ ∑ i, |rem i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, M * |b i - a i| ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hremainder i
      _ = M * ∑ i, |b i - a i| ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ M * coordinateL1Dist a b ^ 2 :=
        mul_le_mul_of_nonneg_left
          (sum_abs_sq_le_coordinateL1Dist_sq a b) hM
  have hgrad :
      |∑ i, gradMove i| ≤ M * coordinateL1Dist a b ^ 2 := by
    calc
      |∑ i, gradMove i| ≤ ∑ i, |gradMove i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i,
          (M * coordinateL1Dist a b) * |b i - a i| := by
        apply Finset.sum_le_sum
        intro i _hi
        change
          |(df (coordinateCorner a b i.castSucc) i - df a i) *
              (b i - a i)| ≤
            (M * coordinateL1Dist a b) * |b i - a i|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (hgradient i) (abs_nonneg (b i - a i))
      _ = M * coordinateL1Dist a b ^ 2 := by
        rw [← Finset.mul_sum]
        unfold coordinateL1Dist
        ring
  rw [coordinateTaylor_decomposition]
  change |(∑ i, rem i) + ∑ i, gradMove i| ≤ _
  calc
    |(∑ i, rem i) + ∑ i, gradMove i| ≤
        |∑ i, rem i| + |∑ i, gradMove i| :=
      abs_add_le _ _
    _ ≤ M * coordinateL1Dist a b ^ 2 +
        M * coordinateL1Dist a b ^ 2 :=
      add_le_add hrem hgrad
    _ = (2 * M) * coordinateL1Dist a b ^ 2 := by ring

/-! ## Moving the Green gradient along the rectangular path -/

/-- A coordinate entry of the Green gradient is Lipschitz along one
coordinate segment, with the Lipschitz constant supplied by the singular
Hessian estimate. -/
theorem greenLocalGrad_coord_lipschitz_of_radius
    {x : R4} (i j : Fin dim) {s r : ℝ}
    (hr : 0 < r)
    (hopen : ∀ t ∈ uIcc 0 s,
      InOpenPrincipalCube (coordLine x j t))
    (hradius : ∀ t ∈ uIcc 0 s,
      r ≤ √(euclideanDistSq (coordLine x j t))) :
    |greenLocalGrad (coordLine x j s) i - greenLocalGrad x i| ≤
      (greenLocalHessSingularBound * r⁻¹ ^ 4) * |s| := by
  let M : ℝ := greenLocalHessSingularBound * r⁻¹ ^ 4
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg greenLocalHessSingularBound_nonneg
      (pow_nonneg (inv_nonneg.mpr hr.le) _)
  have hne :
      ∀ t ∈ uIcc 0 s,
        euclideanDistSq (coordLine x j t) ≠ 0 := by
    intro t ht hzero
    have hsqrt :
        √(euclideanDistSq (coordLine x j t)) = 0 := by
      rw [hzero, Real.sqrt_zero]
    have := hradius t ht
    rw [hsqrt] at this
    linarith
  have hhess :
      ∀ t ∈ uIcc 0 s,
        |greenLocalHess (coordLine x j t) i j| ≤ M := by
    intro t ht
    let d : ℝ := √(euclideanDistSq (coordLine x j t))
    have hd : 0 < d := lt_of_lt_of_le hr (hradius t ht)
    have hinv : d⁻¹ ≤ r⁻¹ :=
      (inv_le_inv₀ hd hr).2 (hradius t ht)
    have hinvpow : d⁻¹ ^ 4 ≤ r⁻¹ ^ 4 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hinv 4
    have hclosed :
        InClosedPrincipalCube (coordLine x j t) := by
      intro k
      exact (hopen t ht k).le
    calc
      |greenLocalHess (coordLine x j t) i j| ≤
          greenLocalHessSingularBound * d⁻¹ ^ 4 := by
        exact abs_greenLocalHess_singular
          hclosed (hne t ht) i j
      _ ≤ M := by
        dsimp only [M]
        exact mul_le_mul_of_nonneg_left hinvpow
          greenLocalHessSingularBound_nonneg
  have hmv :=
    (convex_uIcc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t => greenLocalGrad (coordLine x j t) i)
      (f' := fun t => greenLocalHess (coordLine x j t) i j)
      (fun t ht =>
        (hasDerivAt_greenLocalGrad_coord_at i j
          (hopen t ht) (hne t ht)).hasDerivWithinAt)
      (fun t ht => by
        simpa only [Real.norm_eq_abs] using hhess t ht)
      left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  simpa only [coordLine, zero_smul, add_zero, sub_zero] using hmv

/-- One edge of the rectangular path, in the form used to compare
intermediate gradients. -/
theorem greenLocalGrad_coordinateCorner_edge
    (a b : R4) (i j : Fin dim) {r : ℝ}
    (hr : 0 < r)
    (hopen : ∀ t ∈ uIcc 0 (b j - a j),
      InOpenPrincipalCube
        (coordLine (coordinateCorner a b j.castSucc) j t))
    (hradius : ∀ t ∈ uIcc 0 (b j - a j),
      r ≤ √(euclideanDistSq
        (coordLine (coordinateCorner a b j.castSucc) j t))) :
    |greenLocalGrad (coordinateCorner a b j.succ) i -
        greenLocalGrad (coordinateCorner a b j.castSucc) i| ≤
      (greenLocalHessSingularBound * r⁻¹ ^ 4) *
        |b j - a j| := by
  rw [coordinateCorner_succ]
  exact greenLocalGrad_coord_lipschitz_of_radius
    i j hr hopen hradius

/-- Every intermediate rectangular-path gradient differs from the initial
gradient by at most the Hessian constant times the full `ℓ¹` path length.
The proof uses the exact prefix telescope and then enlarges the prefix to
all four nonnegative edge contributions. -/
theorem greenLocalGrad_coordinateCorner_le
    (a b : R4) (i : Fin dim) {r : ℝ}
    (hr : 0 < r)
    (hopen : ∀ j : Fin dim, ∀ t ∈ uIcc 0 (b j - a j),
      InOpenPrincipalCube
        (coordLine (coordinateCorner a b j.castSucc) j t))
    (hradius : ∀ j : Fin dim, ∀ t ∈ uIcc 0 (b j - a j),
      r ≤ √(euclideanDistSq
        (coordLine (coordinateCorner a b j.castSucc) j t))) :
    |greenLocalGrad (coordinateCorner a b i.castSucc) i -
        greenLocalGrad a i| ≤
      (greenLocalHessSingularBound * r⁻¹ ^ 4) *
        coordinateL1Dist a b := by
  let edge : Fin dim → ℝ := fun j =>
    greenLocalGrad (coordinateCorner a b j.succ) i -
      greenLocalGrad (coordinateCorner a b j.castSucc) i
  rw [coordinateCorner_prefix_telescope
    (fun x => greenLocalGrad x i) a b i.castSucc]
  calc
    |∑ j : Fin dim with j.val < i.castSucc.val, edge j| ≤
        ∑ j : Fin dim with j.val < i.castSucc.val, |edge j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin dim, |edge j| := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun j _hj _hnot => abs_nonneg (edge j))
    _ ≤ ∑ j : Fin dim,
        (greenLocalHessSingularBound * r⁻¹ ^ 4) *
          |b j - a j| := by
      apply Finset.sum_le_sum
      intro j _hj
      exact greenLocalGrad_coordinateCorner_edge
        a b i j hr (hopen j) (hradius j)
    _ = (greenLocalHessSingularBound * r⁻¹ ^ 4) *
        coordinateL1Dist a b := by
      unfold coordinateL1Dist
      rw [Finset.mul_sum]

/-- Four-dimensional local Taylor estimate for the Green kernel.  All
analytic hypotheses are now geometric: every edge of the rectangular path
stays in the open principal cube and at distance at least `r` from the
singularity. -/
theorem greenLocalLift_rectangular_taylor_of_radius
    (a b : R4) {r : ℝ}
    (hr : 0 < r)
    (hopen : ∀ j : Fin dim, ∀ t ∈ uIcc 0 (b j - a j),
      InOpenPrincipalCube
        (coordLine (coordinateCorner a b j.castSucc) j t))
    (hradius : ∀ j : Fin dim, ∀ t ∈ uIcc 0 (b j - a j),
      r ≤ √(euclideanDistSq
        (coordLine (coordinateCorner a b j.castSucc) j t))) :
    |greenLocalLift b - greenLocalLift a -
        coordinateLinearTerm greenLocalGrad a b| ≤
      (2 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
        coordinateL1Dist a b ^ 2 := by
  apply coordinateTaylor_bound
    greenLocalLift greenLocalGrad a b
    (M := greenLocalHessSingularBound * r⁻¹ ^ 4)
  · exact mul_nonneg greenLocalHessSingularBound_nonneg
      (pow_nonneg (inv_nonneg.mpr hr.le) _)
  · intro i
    rw [coordinateCorner_succ]
    exact greenLocalLift_coord_taylor_of_radius
      i hr (hopen i) (hradius i)
  · intro i
    exact greenLocalGrad_coordinateCorner_le
      a b i hr hopen hradius

/-! ## Torus-valued endpoints -/

@[simp]
theorem greenLocalPoint_torusLift (z : T4) :
    greenLocalPoint (torusLift z) = z := by
  funext i
  exact AddCircle.coe_equivIco

@[simp]
theorem greenLocalLift_torusLift (z : T4) :
    greenLocalLift (torusLift z) = greenFn z := by
  rw [greenLocalLift_eq, greenLocalPoint_torusLift]

/-- Torus form of the rectangular Taylor estimate.  The hypotheses expose
the exact chart-safety facts which a later geometric region decomposition
must establish; the conclusion is already about `greenFn`, not an
auxiliary Euclidean kernel. -/
theorem greenFn_rectangular_taylor_of_safe_lifts
    (u v : T4) {r : ℝ}
    (hr : 0 < r)
    (hopen : ∀ j : Fin dim,
      ∀ t ∈ uIcc 0 (torusLift v j - torusLift u j),
        InOpenPrincipalCube
          (coordLine
            (coordinateCorner (torusLift u) (torusLift v)
              j.castSucc) j t))
    (hradius : ∀ j : Fin dim,
      ∀ t ∈ uIcc 0 (torusLift v j - torusLift u j),
        r ≤ √(euclideanDistSq
          (coordLine
            (coordinateCorner (torusLift u) (torusLift v)
              j.castSucc) j t))) :
    |greenFn v - greenFn u -
        coordinateLinearTerm greenLocalGrad
          (torusLift u) (torusLift v)| ≤
      (2 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
        coordinateL1Dist (torusLift u) (torusLift v) ^ 2 := by
  simpa only [greenLocalLift_torusLift] using
    greenLocalLift_rectangular_taylor_of_radius
      (torusLift u) (torusLift v) hr hopen hradius

/-! ## Periodicity of the differentiated lattice sum -/

/-- The full scalar lattice sum.  This representation is used only to
control limits at the boundary of the half-open fundamental cell. -/
def fullLatticeGreenValue (x : R4) : ℝ :=
  ∑' k : Z4, latticeBesselTerm x k

/-- The full first-derivative lattice sum.  Unlike the zero-plus-remainder
presentation of `greenLocalGrad`, this form makes periodic reindexing
transparent. -/
def fullLatticeGreenGrad (x : R4) (i : Fin dim) : ℝ :=
  ∑' k : Z4, latticeBesselGrad x k i

/-- The full second-derivative lattice sum. -/
def fullLatticeGreenHess
    (x : R4) (i j : Fin dim) : ℝ :=
  ∑' k : Z4, latticeBesselHess x k i j

private def nzEquivComplZeroTaylor :
    NZ4 ≃ {k : Z4 // k ∉ ({0} : Finset Z4)} where
  toFun k := ⟨k, by simpa using k.property⟩
  invFun k := ⟨k, by simpa using k.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem summable_fullLatticeGreenValue
    {x : R4} (hx : InClosedPrincipalCube x) :
    Summable fun k : Z4 => latticeBesselTerm x k := by
  have hnz := summable_latticeBesselTerm hx
  have hcompl :
      Summable fun k : {k : Z4 // k ∉ ({0} : Finset Z4)} =>
        latticeBesselTerm x k := by
    rw [← nzEquivComplZeroTaylor.summable_iff]
    exact hnz
  exact Summable.add_compl
    (s := ({0} : Finset Z4))
    Summable.of_finite hcompl

private theorem summable_fullLatticeGreenGrad
    {x : R4} (hx : InClosedPrincipalCube x)
    (i : Fin dim) :
    Summable fun k : Z4 => latticeBesselGrad x k i := by
  have hnz := summable_latticeBesselGrad hx i
  have hcompl :
      Summable fun k : {k : Z4 // k ∉ ({0} : Finset Z4)} =>
        latticeBesselGrad x k i := by
    rw [← nzEquivComplZeroTaylor.summable_iff]
    exact hnz
  exact Summable.add_compl
    (s := ({0} : Finset Z4))
    Summable.of_finite hcompl

private theorem summable_fullLatticeGreenHess
    {x : R4} (hx : InClosedPrincipalCube x)
    (i j : Fin dim) :
    Summable fun k : Z4 => latticeBesselHess x k i j := by
  have hnz := summable_latticeBesselHess hx i j
  have hcompl :
      Summable fun k : {k : Z4 // k ∉ ({0} : Finset Z4)} =>
        latticeBesselHess x k i j := by
    rw [← nzEquivComplZeroTaylor.summable_iff]
    exact hnz
  exact Summable.add_compl
    (s := ({0} : Finset Z4))
    Summable.of_finite hcompl

theorem fullLatticeGreenValue_eq_of_mem_Ico
    {x : R4} (hx : ∀ i, x i ∈ Ico (-π) π)
    (hne : euclideanDistSq x ≠ 0) :
    fullLatticeGreenValue x = greenLocalLift x := by
  have hall :=
    summable_fullLatticeGreenValue
      (x := x) (fun i => abs_le.mpr ⟨(hx i).1, (hx i).2.le⟩)
  have hsplit :=
    hall.sum_add_tsum_subtype_compl ({0} : Finset Z4)
  rw [greenLocalLift_eq_bessel_add_nonzeroRemainder hx hne]
  unfold fullLatticeGreenValue nonzeroLatticeRemainder
  rw [← hsplit, Finset.sum_singleton]
  have hzero :
      latticeTranslate x (0 : Z4) = x := by
    funext i
    simp [latticeTranslate]
  rw [show latticeBesselTerm x (0 : Z4) =
      euclideanBessel4 x by
    unfold latticeBesselTerm
    rw [hzero]]
  congr 1
  exact (nzEquivComplZeroTaylor.tsum_eq
    (fun k : {k : Z4 // k ∉ ({0} : Finset Z4)} =>
      latticeBesselTerm x k)).symm

theorem fullLatticeGreenGrad_eq
    {x : R4} (hx : InClosedPrincipalCube x)
    (i : Fin dim) :
    fullLatticeGreenGrad x i = greenLocalGrad x i := by
  have hall := summable_fullLatticeGreenGrad hx i
  have hsplit :=
    hall.sum_add_tsum_subtype_compl ({0} : Finset Z4)
  unfold fullLatticeGreenGrad greenLocalGrad
  rw [← hsplit, Finset.sum_singleton]
  have hzero :
      latticeTranslate x (0 : Z4) = x := by
    funext j
    simp [latticeTranslate]
  rw [show latticeBesselGrad x (0 : Z4) i =
      euclideanBesselGrad x i by
    unfold latticeBesselGrad
    rw [hzero]]
  congr 1
  exact (nzEquivComplZeroTaylor.tsum_eq
    (fun k : {k : Z4 // k ∉ ({0} : Finset Z4)} =>
      latticeBesselGrad x k i)).symm

theorem fullLatticeGreenHess_eq
    {x : R4} (hx : InClosedPrincipalCube x)
    (i j : Fin dim) :
    fullLatticeGreenHess x i j =
      greenLocalHess x i j := by
  have hall := summable_fullLatticeGreenHess hx i j
  have hsplit :=
    hall.sum_add_tsum_subtype_compl ({0} : Finset Z4)
  unfold fullLatticeGreenHess greenLocalHess
  rw [← hsplit, Finset.sum_singleton]
  have hzero :
      latticeTranslate x (0 : Z4) = x := by
    funext k
    simp [latticeTranslate]
  rw [show latticeBesselHess x (0 : Z4) i j =
      euclideanBesselHess x i j by
    unfold latticeBesselHess
    rw [hzero]]
  congr 1
  exact (nzEquivComplZeroTaylor.tsum_eq
    (fun k : {k : Z4 // k ∉ ({0} : Finset Z4)} =>
      latticeBesselHess x k i j)).symm

/-- Real representative of an integer period shift. -/
def realPeriodShift (m : Z4) : R4 :=
  fun i => 2 * π * (m i : ℝ)

private theorem latticeTranslate_add_period
    (x : R4) (m k : Z4) :
    latticeTranslate (x + realPeriodShift m) k =
      latticeTranslate x (m + k) := by
  funext i
  unfold latticeTranslate realPeriodShift
  simp only [Pi.add_apply, Int.cast_add]
  ring

theorem fullLatticeGreenGrad_add_period
    (x : R4) (m : Z4) (i : Fin dim) :
    fullLatticeGreenGrad (x + realPeriodShift m) i =
      fullLatticeGreenGrad x i := by
  unfold fullLatticeGreenGrad latticeBesselGrad
  calc
    (∑' k : Z4,
        euclideanBesselGrad
          (latticeTranslate (x + realPeriodShift m) k) i) =
        ∑' k : Z4,
          euclideanBesselGrad
            (latticeTranslate x (m + k)) i := by
      apply tsum_congr
      intro k
      rw [latticeTranslate_add_period]
    _ = ∑' k : Z4,
        euclideanBesselGrad (latticeTranslate x k) i := by
      exact ((Equiv.addLeft m : Z4 ≃ Z4).tsum_eq
        (fun k : Z4 =>
          euclideanBesselGrad (latticeTranslate x k) i))

theorem fullLatticeGreenHess_add_period
    (x : R4) (m : Z4) (i j : Fin dim) :
    fullLatticeGreenHess (x + realPeriodShift m) i j =
      fullLatticeGreenHess x i j := by
  unfold fullLatticeGreenHess latticeBesselHess
  calc
    (∑' k : Z4,
        euclideanBesselHess
          (latticeTranslate (x + realPeriodShift m) k) i j) =
        ∑' k : Z4,
          euclideanBesselHess
            (latticeTranslate x (m + k)) i j := by
      apply tsum_congr
      intro k
      rw [latticeTranslate_add_period]
    _ = ∑' k : Z4,
        euclideanBesselHess
          (latticeTranslate x k) i j := by
      exact ((Equiv.addLeft m : Z4 ≃ Z4).tsum_eq
        (fun k : Z4 =>
          euclideanBesselHess (latticeTranslate x k) i j))

theorem fullLatticeGreenValue_add_period
    (x : R4) (m : Z4) :
    fullLatticeGreenValue (x + realPeriodShift m) =
      fullLatticeGreenValue x := by
  unfold fullLatticeGreenValue latticeBesselTerm
  calc
    (∑' k : Z4,
        euclideanBessel4
          (latticeTranslate (x + realPeriodShift m) k)) =
        ∑' k : Z4,
          euclideanBessel4
            (latticeTranslate x (m + k)) := by
      apply tsum_congr
      intro k
      rw [latticeTranslate_add_period]
    _ = ∑' k : Z4,
        euclideanBessel4 (latticeTranslate x k) := by
      exact ((Equiv.addLeft m : Z4 ≃ Z4).tsum_eq
        (fun k : Z4 =>
          euclideanBessel4 (latticeTranslate x k)))

/-- The pulled-back Green value is globally periodic, directly from the
quotient definition. -/
theorem greenLocalLift_add_period
    (x : R4) (m : Z4) :
    greenLocalLift (x + realPeriodShift m) =
      greenLocalLift x := by
  unfold greenLocalLift realPeriodShift
  congr 2
  funext i
  simp only [Pi.add_apply]
  rw [show x i + 2 * π * (m i : ℝ) =
      x i + (m i : ℤ) • (2 * π) by
    simp
    ring]
  exact QuotientAddGroup.eq_iff_sub_mem.mpr (by
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨m i, ?_⟩
    ring)

theorem greenLocalPoint_add_period
    (x : R4) (m : Z4) :
    greenLocalPoint (x + realPeriodShift m) =
      greenLocalPoint x := by
  funext i
  unfold greenLocalPoint realPeriodShift
  simp only [Pi.add_apply]
  rw [show x i + 2 * π * (m i : ℝ) =
      x i + (m i : ℤ) • (2 * π) by
    simp
    ring]
  exact QuotientAddGroup.eq_iff_sub_mem.mpr (by
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨m i, ?_⟩
    ring)

theorem greenLocalGrad_add_period_of_closed
    {x : R4} (m : Z4)
    (hx : InClosedPrincipalCube x)
    (hshift :
      InClosedPrincipalCube (x + realPeriodShift m))
    (i : Fin dim) :
    greenLocalGrad (x + realPeriodShift m) i =
      greenLocalGrad x i := by
  rw [← fullLatticeGreenGrad_eq hshift i,
    fullLatticeGreenGrad_add_period,
    fullLatticeGreenGrad_eq hx i]

/-! A closed fundamental cell differs from the half-open canonical cell
only at coordinates equal to `π`.  The following explicit replacement is
useful for transporting identities to those boundary faces. -/

def halfOpenRepresentative (x : R4) : R4 :=
  fun i => if x i = π then -π else x i

def halfOpenPeriodShift (x : R4) : Z4 :=
  fun i => if x i = π then -1 else 0

theorem add_halfOpenPeriodShift (x : R4) :
    x + realPeriodShift (halfOpenPeriodShift x) =
      halfOpenRepresentative x := by
  funext i
  by_cases hi : x i = π
  · simp [halfOpenRepresentative, halfOpenPeriodShift,
      realPeriodShift, hi]
    ring
  · simp [halfOpenRepresentative, halfOpenPeriodShift,
      realPeriodShift, hi]

theorem halfOpenRepresentative_mem_Ico
    {x : R4} (hx : InClosedPrincipalCube x) :
    ∀ i, halfOpenRepresentative x i ∈ Ico (-π) π := by
  intro i
  by_cases hi : x i = π
  · simp [halfOpenRepresentative, hi, Real.pi_pos]
  · have hxi := hx i
    rw [abs_le] at hxi
    simp only [halfOpenRepresentative, hi, if_false]
    exact ⟨hxi.1, lt_of_le_of_ne hxi.2 hi⟩

theorem euclideanDistSq_halfOpenRepresentative
    (x : R4) :
    euclideanDistSq (halfOpenRepresentative x) =
      euclideanDistSq x := by
  unfold euclideanDistSq
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases h : x i = π
  · simp [halfOpenRepresentative, h]
  · simp [halfOpenRepresentative, h]

theorem torusDistSq_greenLocalPoint_of_closed
    {x : R4} (hx : InClosedPrincipalCube x) :
    torusDistSq (greenLocalPoint x) =
      euclideanDistSq x := by
  let y := halfOpenRepresentative x
  have hyIco : ∀ i, y i ∈ Ico (-π) π :=
    halfOpenRepresentative_mem_Ico hx
  have hpoint :
      greenLocalPoint y = greenLocalPoint x := by
    change greenLocalPoint (halfOpenRepresentative x) =
      greenLocalPoint x
    rw [← add_halfOpenPeriodShift x]
    exact greenLocalPoint_add_period x (halfOpenPeriodShift x)
  calc
    torusDistSq (greenLocalPoint x) =
        torusDistSq (greenLocalPoint y) := by rw [hpoint]
    _ = euclideanDistSq y := by
      unfold torusDistSq euclideanDistSq
      rw [torusLift_greenLocalPoint hyIco]
    _ = euclideanDistSq x :=
      euclideanDistSq_halfOpenRepresentative x

theorem torusLift_greenLocalPoint_of_closed
    {x : R4} (hx : InClosedPrincipalCube x) :
    torusLift (greenLocalPoint x) =
      halfOpenRepresentative x := by
  let y := halfOpenRepresentative x
  have hyIco : ∀ i, y i ∈ Ico (-π) π :=
    halfOpenRepresentative_mem_Ico hx
  have hpoint :
      greenLocalPoint y = greenLocalPoint x := by
    change greenLocalPoint (halfOpenRepresentative x) =
      greenLocalPoint x
    rw [← add_halfOpenPeriodShift x]
    exact greenLocalPoint_add_period x (halfOpenPeriodShift x)
  rw [← hpoint]
  exact torusLift_greenLocalPoint hyIco

theorem greenLocalGrad_halfOpenRepresentative
    {x : R4} (hx : InClosedPrincipalCube x)
    (i : Fin dim) :
    greenLocalGrad (halfOpenRepresentative x) i =
      greenLocalGrad x i := by
  have hy :
      InClosedPrincipalCube (halfOpenRepresentative x) := by
    intro j
    exact abs_le.mpr
      ⟨(halfOpenRepresentative_mem_Ico hx j).1,
        (halfOpenRepresentative_mem_Ico hx j).2.le⟩
  have hshift :
      x + realPeriodShift (halfOpenPeriodShift x) =
        halfOpenRepresentative x :=
    add_halfOpenPeriodShift x
  have hshiftClosed :
      InClosedPrincipalCube
        (x + realPeriodShift (halfOpenPeriodShift x)) := by
    rw [hshift]
    exact hy
  calc
    greenLocalGrad (halfOpenRepresentative x) i =
        greenLocalGrad
          (x + realPeriodShift (halfOpenPeriodShift x)) i := by
      rw [hshift]
    _ = greenLocalGrad x i :=
      greenLocalGrad_add_period_of_closed
        (halfOpenPeriodShift x) hx hshiftClosed i

theorem greenLocalLift_halfOpenRepresentative
    (x : R4) :
    greenLocalLift (halfOpenRepresentative x) =
      greenLocalLift x := by
  unfold greenLocalLift halfOpenRepresentative
  congr 1
  funext i
  by_cases hi : x i = π
  · simp only [hi, if_true]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨(-1 : ℤ), ?_⟩
    simp
    ring
  · simp [hi]

/-- The full scalar lattice sum agrees with the pulled-back Green kernel
also on the closed faces of the principal cube. -/
theorem fullLatticeGreenValue_eq
    {x : R4} (hx : InClosedPrincipalCube x)
    (hne : euclideanDistSq x ≠ 0) :
    fullLatticeGreenValue x = greenLocalLift x := by
  let y := halfOpenRepresentative x
  let m := halfOpenPeriodShift x
  have hyIco : ∀ i, y i ∈ Ico (-π) π :=
    halfOpenRepresentative_mem_Ico hx
  have hyne : euclideanDistSq y ≠ 0 := by
    simpa [y, euclideanDistSq_halfOpenRepresentative] using hne
  have hshift : x + realPeriodShift m = y := by
    exact add_halfOpenPeriodShift x
  calc
    fullLatticeGreenValue x =
        fullLatticeGreenValue (x + realPeriodShift m) :=
      (fullLatticeGreenValue_add_period x m).symm
    _ = fullLatticeGreenValue y := by rw [hshift]
    _ = greenLocalLift y :=
      fullLatticeGreenValue_eq_of_mem_Ico hyIco hyne
    _ = greenLocalLift x :=
      greenLocalLift_halfOpenRepresentative x

/-- The two boundary representatives `-π` and `π` give the same Green
gradient.  This is the gluing identity needed when a short coordinate
segment wraps around the fundamental cell. -/
theorem greenLocalGrad_lower_upper_boundary
    {x : R4} (hx : InClosedPrincipalCube x)
    (j i : Fin dim) (hxj : x j = -π) :
    greenLocalGrad (coordLine x j (2 * π)) i =
      greenLocalGrad x i := by
  have hy : InClosedPrincipalCube
      (coordLine x j (2 * π)) := by
    intro k
    by_cases hkj : k = j
    · subst k
      rw [show coordLine x j (2 * π) j =
          x j + 2 * π by simp [coordLine],
        hxj, show -π + 2 * π = π by ring,
        abs_of_pos Real.pi_pos]
    · simpa [coordLine, hkj] using hx k
  let m : Z4 := Pi.single j 1
  have hshift :
      x + realPeriodShift m =
        coordLine x j (2 * π) := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp [m, realPeriodShift, coordLine]
    · simp [m, realPeriodShift, coordLine, hkj]
  calc
    greenLocalGrad (coordLine x j (2 * π)) i =
        fullLatticeGreenGrad
          (coordLine x j (2 * π)) i :=
      (fullLatticeGreenGrad_eq hy i).symm
    _ = fullLatticeGreenGrad
          (x + realPeriodShift m) i := by rw [hshift]
    _ = fullLatticeGreenGrad x i :=
      fullLatticeGreenGrad_add_period x m i
    _ = greenLocalGrad x i :=
      fullLatticeGreenGrad_eq hx i

theorem greenLocalHess_lower_upper_boundary
    {x : R4} (hx : InClosedPrincipalCube x)
    (j i k : Fin dim) (hxj : x j = -π) :
    greenLocalHess (coordLine x j (2 * π)) i k =
      greenLocalHess x i k := by
  have hy : InClosedPrincipalCube
      (coordLine x j (2 * π)) := by
    intro l
    by_cases hlj : l = j
    · subst l
      rw [show coordLine x j (2 * π) j =
          x j + 2 * π by simp [coordLine],
        hxj, show -π + 2 * π = π by ring,
        abs_of_pos Real.pi_pos]
    · simpa [coordLine, hlj] using hx l
  let m : Z4 := Pi.single j 1
  have hshift :
      x + realPeriodShift m =
        coordLine x j (2 * π) := by
    funext l
    by_cases hlj : l = j
    · subst l
      simp [m, realPeriodShift, coordLine]
    · simp [m, realPeriodShift, coordLine, hlj]
  calc
    greenLocalHess (coordLine x j (2 * π)) i k =
        fullLatticeGreenHess
          (coordLine x j (2 * π)) i k :=
      (fullLatticeGreenHess_eq hy i k).symm
    _ = fullLatticeGreenHess
          (x + realPeriodShift m) i k := by rw [hshift]
    _ = fullLatticeGreenHess x i k :=
      fullLatticeGreenHess_add_period x m i k
    _ = greenLocalHess x i k :=
      fullLatticeGreenHess_eq hx i k

/-! ## One-dimensional continuity up to the cell boundary

The Taylor path may meet a face of the closed principal cube.  The
following lemmas give the missing endpoint continuity directly from the
uniformly summable lattice series.  They deliberately concern a single
coordinate line; this is exactly what is needed to glue the finitely many
pieces of a wrapped rectangular path. -/

private theorem latticeTranslate_coordLine_taylor
    (x : R4) (k : Z4) (j : Fin dim) (s : ℝ) :
    latticeTranslate (coordLine x j s) k =
      coordLine (latticeTranslate x k) j s := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [latticeTranslate, coordLine]
    ring
  · simp [latticeTranslate, coordLine, hij]

private theorem latticeTranslate_distSq_ne_zero_taylor
    {x : R4} (hx : InClosedPrincipalCube x)
    {k : Z4} (hk : k ≠ 0) :
    euclideanDistSq (latticeTranslate x k) ≠ 0 := by
  have hlow :
      π ^ 2 * latticeSq k ≤
        euclideanDistSq (latticeTranslate x k) := by
    simpa [latticeSq] using latticeTranslate_sq_lower hx k
  have hpos : 0 < π ^ 2 * latticeSq k :=
    mul_pos (sq_pos_of_pos Real.pi_pos)
      (lt_of_lt_of_le zero_lt_one (one_le_lattice_sq hk))
  exact ne_of_gt (hpos.trans_le hlow)

private theorem hasDerivAt_latticeBesselTerm_coord_taylor
    {x : R4} (hx : InClosedPrincipalCube x)
    {k : Z4} (hk : k ≠ 0) (j : Fin dim) :
    HasDerivAt
      (fun s => latticeBesselTerm (coordLine x j s) k)
      (latticeBesselGrad x k j) 0 := by
  have hbase :=
    hasDerivAt_euclideanBessel4_coord
      (latticeTranslate_distSq_ne_zero_taylor hx hk) j
  unfold latticeBesselTerm latticeBesselGrad
  convert hbase using 1
  funext s
  rw [← latticeTranslate_coordLine_taylor]

private theorem hasDerivAt_latticeBesselGrad_coord_taylor
    {x : R4} (hx : InClosedPrincipalCube x)
    {k : Z4} (hk : k ≠ 0) (i j : Fin dim) :
    HasDerivAt
      (fun s => latticeBesselGrad (coordLine x j s) k i)
      (latticeBesselHess x k i j) 0 := by
  have hbase :=
    hasDerivAt_euclideanBesselGrad_coord
      (latticeTranslate_distSq_ne_zero_taylor hx hk) i j
  unfold latticeBesselGrad latticeBesselHess
  convert hbase using 1
  funext s
  rw [← latticeTranslate_coordLine_taylor]

private theorem hasDerivAt_latticeBesselTerm_coord_taylor_at
    {x : R4} {k : Z4} (hk : k ≠ 0)
    (j : Fin dim) (s : ℝ)
    (hxs : InClosedPrincipalCube (coordLine x j s)) :
    HasDerivAt
      (fun r => latticeBesselTerm (coordLine x j r) k)
      (latticeBesselGrad (coordLine x j s) k j) s := by
  have hbase :=
    hasDerivAt_latticeBesselTerm_coord_taylor
      (x := coordLine x j s) hxs hk j
  have hshift :=
    hbase.comp_of_eq s
      ((hasDerivAt_id s).sub_const s) (by simp)
  have heq :
      (fun r => latticeBesselTerm (coordLine x j r) k) =
        (fun r =>
          latticeBesselTerm
            (coordLine (coordLine x j s) j r) k) ∘
          (fun r => r - s) := by
    funext r
    simp only [Function.comp_apply]
    rw [coordLine_add_taylor]
    congr 3
    ring
  rw [heq]
  simpa only [mul_one, id_eq] using hshift

private theorem hasDerivAt_latticeBesselGrad_coord_taylor_at
    {x : R4} {k : Z4} (hk : k ≠ 0)
    (i j : Fin dim) (s : ℝ)
    (hxs : InClosedPrincipalCube (coordLine x j s)) :
    HasDerivAt
      (fun r => latticeBesselGrad (coordLine x j r) k i)
      (latticeBesselHess (coordLine x j s) k i j) s := by
  have hbase :=
    hasDerivAt_latticeBesselGrad_coord_taylor
      (x := coordLine x j s) hxs hk i j
  have hshift :=
    hbase.comp_of_eq s
      ((hasDerivAt_id s).sub_const s) (by simp)
  have heq :
      (fun r => latticeBesselGrad (coordLine x j r) k i) =
        (fun r =>
          latticeBesselGrad
            (coordLine (coordLine x j s) j r) k i) ∘
          (fun r => r - s) := by
    funext r
    simp only [Function.comp_apply]
    rw [coordLine_add_taylor]
    congr 4
    ring
  rw [heq]
  simpa only [mul_one, id_eq] using hshift

private theorem greenLocalLift_eq_bessel_add_nonzero_closed
    {x : R4} (hx : InClosedPrincipalCube x)
    (hne : euclideanDistSq x ≠ 0) :
    greenLocalLift x =
      euclideanBessel4 x + nonzeroLatticeRemainder x := by
  have heq := fullLatticeGreenValue_eq hx hne
  have hall := summable_fullLatticeGreenValue hx
  have hsplit :=
    hall.sum_add_tsum_subtype_compl ({0} : Finset Z4)
  have hzero :
      latticeTranslate x (0 : Z4) = x := by
    funext i
    simp [latticeTranslate]
  have hzeroTerm :
      latticeBesselTerm x (0 : Z4) = euclideanBessel4 x := by
    unfold latticeBesselTerm
    rw [hzero]
  have hnz :
      (∑' k : {k : Z4 // k ∉ ({0} : Finset Z4)},
          latticeBesselTerm x k) =
        nonzeroLatticeRemainder x := by
    unfold nonzeroLatticeRemainder
    exact (nzEquivComplZeroTaylor.tsum_eq
      (fun k : {k : Z4 // k ∉ ({0} : Finset Z4)} =>
        latticeBesselTerm x k)).symm
  rw [← heq]
  unfold fullLatticeGreenValue
  rw [← hsplit, Finset.sum_singleton, hzeroTerm, hnz]

private theorem coordLine_closed_of_closed_strict
    {x : R4} (hx : InClosedPrincipalCube x)
    (j : Fin dim) {s : ℝ}
    (hs : s ∈ Ioo (-π - x j) (π - x j)) :
    InClosedPrincipalCube (coordLine x j s) := by
  intro i
  by_cases hij : i = j
  · subst i
    rw [abs_le]
    simp only [coordLine, Pi.add_apply, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one]
    constructor <;> linarith [hs.1, hs.2]
  · simpa [coordLine, hij] using hx i

private theorem hasDerivAt_nonzeroLatticeRemainder_coord_closed
    {x : R4} (hx : InClosedPrincipalCube x)
    (j : Fin dim) (hxj : |x j| < π) :
    HasDerivAt
      (fun s => nonzeroLatticeRemainder (coordLine x j s))
      (nonzeroLatticeRemainderGrad x j) 0 := by
  let t : Set ℝ := Ioo (-π - x j) (π - x j)
  have hzero : (0 : ℝ) ∈ t := by
    dsimp only [t]
    rw [abs_lt] at hxj
    constructor <;> linarith
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := fun k : NZ4 => latticeGeomWeight k)
    (t := t)
    (g := fun k : NZ4 => fun s =>
      latticeBesselTerm (coordLine x j s) k)
    (g' := fun k : NZ4 => fun s =>
      latticeBesselGrad (coordLine x j s) k j)
    (y₀ := 0) (y := 0)
    summable_nz_latticeGeomWeight
    isOpen_Ioo isPreconnected_Ioo
    (fun k s hs =>
      hasDerivAt_latticeBesselTerm_coord_taylor_at
        k.property j s
        (coordLine_closed_of_closed_strict hx j hs))
    (fun k s hs => by
      rw [Real.norm_eq_abs]
      exact abs_latticeBesselGrad_le
        (coordLine_closed_of_closed_strict hx j hs)
        k.property j)
    hzero (by
      simpa [coordLine] using summable_latticeBesselTerm hx) hzero
  simpa [nonzeroLatticeRemainder,
    nonzeroLatticeRemainderGrad, coordLine] using hmain

private theorem hasDerivAt_nonzeroLatticeRemainderGrad_coord_closed
    {x : R4} (hx : InClosedPrincipalCube x)
    (i j : Fin dim) (hxj : |x j| < π) :
    HasDerivAt
      (fun s =>
        nonzeroLatticeRemainderGrad (coordLine x j s) i)
      (nonzeroLatticeRemainderHess x i j) 0 := by
  let t : Set ℝ := Ioo (-π - x j) (π - x j)
  have hzero : (0 : ℝ) ∈ t := by
    dsimp only [t]
    rw [abs_lt] at hxj
    constructor <;> linarith
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := fun k : NZ4 => 2 * latticeGeomWeight k)
    (t := t)
    (g := fun k : NZ4 => fun s =>
      latticeBesselGrad (coordLine x j s) k i)
    (g' := fun k : NZ4 => fun s =>
      latticeBesselHess (coordLine x j s) k i j)
    (y₀ := 0) (y := 0)
    (summable_nz_latticeGeomWeight.mul_left 2)
    isOpen_Ioo isPreconnected_Ioo
    (fun k s hs =>
      hasDerivAt_latticeBesselGrad_coord_taylor_at
        k.property i j s
        (coordLine_closed_of_closed_strict hx j hs))
    (fun k s hs => by
      rw [Real.norm_eq_abs]
      exact abs_latticeBesselHess_le
        (coordLine_closed_of_closed_strict hx j hs)
        k.property i j)
    hzero (by
      simpa [coordLine] using summable_latticeBesselGrad hx i) hzero
  simpa [nonzeroLatticeRemainderGrad,
    nonzeroLatticeRemainderHess, coordLine] using hmain

/-- Coordinate derivative of the pulled-back Green kernel at a point of
the closed cell whose moving coordinate is not on a face.  Other
coordinates are allowed to lie on faces. -/
theorem hasDerivAt_greenLocalLift_coord_closed
    {x : R4} (hx : InClosedPrincipalCube x)
    (hne : euclideanDistSq x ≠ 0)
    (j : Fin dim) (hxj : |x j| < π) :
    HasDerivAt (fun s => greenLocalLift (coordLine x j s))
      (greenLocalGrad x j) 0 := by
  have hsing := hasDerivAt_euclideanBessel4_coord hne j
  have hreg :=
    hasDerivAt_nonzeroLatticeRemainder_coord_closed hx j hxj
  have hsum := hsing.add hreg
  unfold greenLocalGrad greenLocalRemainderGrad
  refine hsum.congr_of_eventuallyEq ?_
  have hopen :
      Ioo (-π - x j) (π - x j) ∈ 𝓝 (0 : ℝ) := by
    apply isOpen_Ioo.mem_nhds
    rw [abs_lt] at hxj
    constructor <;> linarith
  have hcont :
      ContinuousAt
        (fun s => euclideanDistSq (coordLine x j s)) 0 := by
    unfold euclideanDistSq coordLine
    fun_prop
  have hne0 :
      euclideanDistSq (coordLine x j 0) ≠ 0 := by
    simpa [coordLine] using hne
  filter_upwards [hopen, hcont.eventually_ne hne0] with s hs hsne
  exact (greenLocalLift_eq_bessel_add_nonzero_closed
    (coordLine_closed_of_closed_strict hx j hs) hsne)

theorem hasDerivAt_greenLocalGrad_coord_closed
    {x : R4} (hx : InClosedPrincipalCube x)
    (hne : euclideanDistSq x ≠ 0)
    (i j : Fin dim) (hxj : |x j| < π) :
    HasDerivAt (fun s => greenLocalGrad (coordLine x j s) i)
      (greenLocalHess x i j) 0 := by
  have hsing := hasDerivAt_euclideanBesselGrad_coord hne i j
  have hreg :=
    hasDerivAt_nonzeroLatticeRemainderGrad_coord_closed
      hx i j hxj
  change HasDerivAt
    ((fun s => euclideanBesselGrad (coordLine x j s) i) +
      fun s =>
        nonzeroLatticeRemainderGrad (coordLine x j s) i)
    (euclideanBesselHess x i j +
      nonzeroLatticeRemainderHess x i j) 0
  exact hsing.add hreg

theorem hasDerivAt_greenLocalLift_coord_closed_at
    {x : R4} (j : Fin dim) {t : ℝ}
    (hclosed :
      InClosedPrincipalCube (coordLine x j t))
    (hne : euclideanDistSq (coordLine x j t) ≠ 0)
    (hcoord : |coordLine x j t j| < π) :
    HasDerivAt
      (fun s => greenLocalLift (coordLine x j s))
      (greenLocalGrad (coordLine x j t) j) t := by
  have hbase :=
    hasDerivAt_greenLocalLift_coord_closed
      hclosed hne j hcoord
  have hshift :=
    hbase.comp_of_eq t
      ((hasDerivAt_id t).sub_const t) (by simp)
  have heq :
      (fun s => greenLocalLift (coordLine x j s)) =
        (fun s =>
          greenLocalLift
            (coordLine (coordLine x j t) j s)) ∘
          (fun s => s - t) := by
    funext s
    simp only [Function.comp_apply]
    rw [coordLine_add_taylor]
    congr 2
    ring
  rw [heq]
  simpa only [mul_one, id_eq] using hshift

theorem hasDerivAt_greenLocalGrad_coord_closed_at
    {x : R4} (i j : Fin dim) {t : ℝ}
    (hclosed :
      InClosedPrincipalCube (coordLine x j t))
    (hne : euclideanDistSq (coordLine x j t) ≠ 0)
    (hcoord : |coordLine x j t j| < π) :
    HasDerivAt
      (fun s => greenLocalGrad (coordLine x j s) i)
      (greenLocalHess (coordLine x j t) i j) t := by
  have hbase :=
    hasDerivAt_greenLocalGrad_coord_closed
      hclosed hne i j hcoord
  have hshift :=
    hbase.comp_of_eq t
      ((hasDerivAt_id t).sub_const t) (by simp)
  have heq :
      (fun s => greenLocalGrad (coordLine x j s) i) =
        (fun s =>
          greenLocalGrad
            (coordLine (coordLine x j t) j s) i) ∘
          (fun s => s - t) := by
    funext s
    simp only [Function.comp_apply]
    rw [coordLine_add_taylor]
    congr 3
    ring
  rw [heq]
  simpa only [mul_one, id_eq] using hshift

theorem continuousOn_nonzeroLatticeRemainder_coord
    {x : R4} (j : Fin dim) {s : Set ℝ}
    (hclosed : ∀ t ∈ s,
      InClosedPrincipalCube (coordLine x j t)) :
    ContinuousOn
      (fun t => nonzeroLatticeRemainder (coordLine x j t)) s := by
  unfold nonzeroLatticeRemainder
  apply continuousOn_tsum
  · intro k t ht
    have h :=
      hasDerivAt_latticeBesselTerm_coord_taylor
        (hclosed t ht) k.property j
    have hshift :=
      h.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
    convert hshift.continuousAt.continuousWithinAt using 1
    funext r
    simp only [Function.comp_apply, id_eq]
    rw [coordLine_add_taylor]
    congr 3
    ring
  · exact summable_nz_latticeGeomWeight
  · intro k t ht
    rw [Real.norm_eq_abs]
    exact abs_latticeBesselTerm_le
      (hclosed t ht) k.property

theorem continuousOn_nonzeroLatticeRemainderGrad_coord
    {x : R4} (i j : Fin dim) {s : Set ℝ}
    (hclosed : ∀ t ∈ s,
      InClosedPrincipalCube (coordLine x j t)) :
    ContinuousOn
      (fun t =>
        nonzeroLatticeRemainderGrad (coordLine x j t) i) s := by
  unfold nonzeroLatticeRemainderGrad
  apply continuousOn_tsum
  · intro k t ht
    have h :=
      hasDerivAt_latticeBesselGrad_coord_taylor
        (hclosed t ht) k.property i j
    have hshift :=
      h.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
    convert hshift.continuousAt.continuousWithinAt using 1
    funext r
    simp only [Function.comp_apply, id_eq]
    rw [coordLine_add_taylor]
    congr 4
    ring
  · exact summable_nz_latticeGeomWeight
  · intro k t ht
    rw [Real.norm_eq_abs]
    exact abs_latticeBesselGrad_le
      (hclosed t ht) k.property i

theorem continuousOn_greenLocalLift_coord_closed
    {x : R4} (j : Fin dim) {s : Set ℝ}
    (hclosed : ∀ t ∈ s,
      InClosedPrincipalCube (coordLine x j t))
    (hne : ∀ t ∈ s,
      euclideanDistSq (coordLine x j t) ≠ 0) :
    ContinuousOn (fun t => greenLocalLift (coordLine x j t)) s := by
  have hsing :
      ContinuousOn
        (fun t => euclideanBessel4 (coordLine x j t)) s := by
    intro t ht
    have hbase :=
      hasDerivAt_euclideanBessel4_coord (hne t ht) j
    have hshift :=
      hbase.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
    convert hshift.continuousAt.continuousWithinAt using 1
    funext r
    simp only [Function.comp_apply, id_eq]
    rw [coordLine_add_taylor]
    congr 2
    ring
  have hreg :=
    continuousOn_nonzeroLatticeRemainder_coord j hclosed
  have hsum :
      ContinuousOn
        (fun t =>
          euclideanBessel4 (coordLine x j t) +
            nonzeroLatticeRemainder (coordLine x j t)) s :=
    hsing.add hreg
  apply hsum.congr
  intro t ht
  have heq :=
    fullLatticeGreenValue_eq (hclosed t ht) (hne t ht)
  have hall :=
    summable_fullLatticeGreenValue (hclosed t ht)
  have hsplit :=
    hall.sum_add_tsum_subtype_compl ({0} : Finset Z4)
  have hzero :
      latticeTranslate (coordLine x j t) (0 : Z4) =
        coordLine x j t := by
    funext i
    simp [latticeTranslate]
  have hnz :
      (∑' k : {k : Z4 // k ∉ ({0} : Finset Z4)},
          latticeBesselTerm (coordLine x j t) k) =
        nonzeroLatticeRemainder (coordLine x j t) := by
    unfold nonzeroLatticeRemainder
    exact (nzEquivComplZeroTaylor.tsum_eq
      (fun k : {k : Z4 // k ∉ ({0} : Finset Z4)} =>
        latticeBesselTerm (coordLine x j t) k)).symm
  have hzeroTerm :
      latticeBesselTerm (coordLine x j t) (0 : Z4) =
        euclideanBessel4 (coordLine x j t) := by
    unfold latticeBesselTerm
    rw [hzero]
  change greenLocalLift (coordLine x j t) =
    euclideanBessel4 (coordLine x j t) +
      nonzeroLatticeRemainder (coordLine x j t)
  calc
    greenLocalLift (coordLine x j t) =
        fullLatticeGreenValue (coordLine x j t) := heq.symm
    _ = latticeBesselTerm (coordLine x j t) 0 +
        (∑' k : {k : Z4 // k ∉ ({0} : Finset Z4)},
          latticeBesselTerm (coordLine x j t) k) := by
      unfold fullLatticeGreenValue
      rw [← hsplit, Finset.sum_singleton]
    _ = _ := by rw [hzeroTerm, hnz]

theorem continuousOn_greenLocalGrad_coord_closed
    {x : R4} (i j : Fin dim) {s : Set ℝ}
    (hclosed : ∀ t ∈ s,
      InClosedPrincipalCube (coordLine x j t))
    (hne : ∀ t ∈ s,
      euclideanDistSq (coordLine x j t) ≠ 0) :
    ContinuousOn
      (fun t => greenLocalGrad (coordLine x j t) i) s := by
  have hsing :
      ContinuousOn
        (fun t => euclideanBesselGrad (coordLine x j t) i) s := by
    intro t ht
    have hbase :=
      hasDerivAt_euclideanBesselGrad_coord (hne t ht) i j
    have hshift :=
      hbase.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
    convert hshift.continuousAt.continuousWithinAt using 1
    funext r
    simp only [Function.comp_apply, id_eq]
    rw [coordLine_add_taylor]
    congr 3
    ring
  have hreg :=
    continuousOn_nonzeroLatticeRemainderGrad_coord i j hclosed
  exact (hsing.add hreg).congr fun t _ht => by
    rfl

/-- Taylor estimate on a coordinate interval contained in the closed
principal cell.  The endpoints may lie on cell faces; only interior
points must have their moving coordinate in the open cell. -/
theorem greenLocalLift_coord_taylor_closed_interval_of_radius
    {x : R4} (j : Fin dim) {a b r : ℝ}
    (hab : a < b) (hr : 0 < r)
    (hclosed : ∀ t ∈ Icc a b,
      InClosedPrincipalCube (coordLine x j t))
    (hcoord : ∀ t ∈ Ioo a b,
      |coordLine x j t j| < π)
    (hradius : ∀ t ∈ Icc a b,
      r ≤ √(euclideanDistSq (coordLine x j t))) :
    |greenLocalLift (coordLine x j b) -
        greenLocalLift (coordLine x j a) -
        greenLocalGrad (coordLine x j a) j * (b - a)| ≤
      (greenLocalHessSingularBound * r⁻¹ ^ 4) *
        (b - a) ^ 2 := by
  let M := greenLocalHessSingularBound * r⁻¹ ^ 4
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg greenLocalHessSingularBound_nonneg
      (pow_nonneg (inv_nonneg.mpr hr.le) _)
  have hne :
      ∀ t ∈ Icc a b,
        euclideanDistSq (coordLine x j t) ≠ 0 := by
    intro t ht hzero
    have hsqrt :
        √(euclideanDistSq (coordLine x j t)) = 0 := by
      rw [hzero, Real.sqrt_zero]
    have := hradius t ht
    rw [hsqrt] at this
    linarith
  apply abs_sub_sub_deriv_mul_le_of_continuousOn
    (f := fun t => greenLocalLift (coordLine x j t))
    (f' := fun t => greenLocalGrad (coordLine x j t) j)
    (f'' := fun t => greenLocalHess (coordLine x j t) j j)
    hab hM
  · exact continuousOn_greenLocalLift_coord_closed
      j hclosed hne
  · exact continuousOn_greenLocalGrad_coord_closed
      j j hclosed hne
  · intro t ht
    exact hasDerivAt_greenLocalLift_coord_closed_at
      j (hclosed t (Ioo_subset_Icc_self ht))
      (hne t (Ioo_subset_Icc_self ht)) (hcoord t ht)
  · intro t ht
    exact hasDerivAt_greenLocalGrad_coord_closed_at
      j j (hclosed t (Ioo_subset_Icc_self ht))
      (hne t (Ioo_subset_Icc_self ht)) (hcoord t ht)
  · intro t ht
    let d := √(euclideanDistSq (coordLine x j t))
    have hd : 0 < d :=
      lt_of_lt_of_le hr
        (hradius t (Ioo_subset_Icc_self ht))
    have hinv : d⁻¹ ≤ r⁻¹ :=
      (inv_le_inv₀ hd hr).2
        (hradius t (Ioo_subset_Icc_self ht))
    have hinvpow : d⁻¹ ^ 4 ≤ r⁻¹ ^ 4 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hinv 4
    calc
      |greenLocalHess (coordLine x j t) j j| ≤
          greenLocalHessSingularBound * d⁻¹ ^ 4 := by
        exact abs_greenLocalHess_singular
          (hclosed t (Ioo_subset_Icc_self ht))
          (hne t (Ioo_subset_Icc_self ht)) j j
      _ ≤ M := by
        dsimp only [M]
        exact mul_le_mul_of_nonneg_left hinvpow
          greenLocalHessSingularBound_nonneg

/-- Gradient Lipschitz estimate on the same closed coordinate interval. -/
theorem greenLocalGrad_coord_lipschitz_closed_interval_of_radius
    {x : R4} (i j : Fin dim) {a b r : ℝ}
    (hab : a < b) (hr : 0 < r)
    (hclosed : ∀ t ∈ Icc a b,
      InClosedPrincipalCube (coordLine x j t))
    (hcoord : ∀ t ∈ Ioo a b,
      |coordLine x j t j| < π)
    (hradius : ∀ t ∈ Icc a b,
      r ≤ √(euclideanDistSq (coordLine x j t))) :
    |greenLocalGrad (coordLine x j b) i -
        greenLocalGrad (coordLine x j a) i| ≤
      (greenLocalHessSingularBound * r⁻¹ ^ 4) *
        (b - a) := by
  let M := greenLocalHessSingularBound * r⁻¹ ^ 4
  have hne :
      ∀ t ∈ Icc a b,
        euclideanDistSq (coordLine x j t) ≠ 0 := by
    intro t ht hzero
    have hsqrt :
        √(euclideanDistSq (coordLine x j t)) = 0 := by
      rw [hzero, Real.sqrt_zero]
    have := hradius t ht
    rw [hsqrt] at this
    linarith
  have hbound :
      ∀ t ∈ Ioo a b,
        |greenLocalHess (coordLine x j t) i j| ≤ M := by
    intro t ht
    let d := √(euclideanDistSq (coordLine x j t))
    have hd : 0 < d :=
      lt_of_lt_of_le hr
        (hradius t (Ioo_subset_Icc_self ht))
    have hinv : d⁻¹ ≤ r⁻¹ :=
      (inv_le_inv₀ hd hr).2
        (hradius t (Ioo_subset_Icc_self ht))
    have hinvpow : d⁻¹ ^ 4 ≤ r⁻¹ ^ 4 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hd.le) hinv 4
    calc
      |greenLocalHess (coordLine x j t) i j| ≤
          greenLocalHessSingularBound * d⁻¹ ^ 4 := by
        exact abs_greenLocalHess_singular
          (hclosed t (Ioo_subset_Icc_self ht))
          (hne t (Ioo_subset_Icc_self ht)) i j
      _ ≤ M := by
        dsimp only [M]
        exact mul_le_mul_of_nonneg_left hinvpow
          greenLocalHessSingularBound_nonneg
  have h :=
    abs_sub_le_of_continuousOn_of_abs_deriv_le
      (f := fun t => greenLocalGrad (coordLine x j t) i)
      (f' := fun t => greenLocalHess (coordLine x j t) i j)
      hab
      (continuousOn_greenLocalGrad_coord_closed
        i j hclosed hne)
      (fun t ht =>
        hasDerivAt_greenLocalGrad_coord_closed_at
          i j (hclosed t (Ioo_subset_Icc_self ht))
          (hne t (Ioo_subset_Icc_self ht)) (hcoord t ht))
      hbound
      b (right_mem_Icc.mpr hab.le)
      a (left_mem_Icc.mpr hab.le)
  simpa [M, abs_of_pos (sub_pos.mpr hab)] using h

/-- Reverse traversal of a closed coordinate interval, linearized at the
right endpoint. -/
theorem greenLocalLift_coord_taylor_closed_interval_rev_of_radius
    {x : R4} (j : Fin dim) {a b r : ℝ}
    (hab : a < b) (hr : 0 < r)
    (hclosed : ∀ t ∈ Icc a b,
      InClosedPrincipalCube (coordLine x j t))
    (hcoord : ∀ t ∈ Ioo a b,
      |coordLine x j t j| < π)
    (hradius : ∀ t ∈ Icc a b,
      r ≤ √(euclideanDistSq (coordLine x j t))) :
    |greenLocalLift (coordLine x j a) -
        greenLocalLift (coordLine x j b) -
        greenLocalGrad (coordLine x j b) j * (a - b)| ≤
      (2 * (greenLocalHessSingularBound * r⁻¹ ^ 4)) *
        (b - a) ^ 2 := by
  let M := greenLocalHessSingularBound * r⁻¹ ^ 4
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg greenLocalHessSingularBound_nonneg
      (pow_nonneg (inv_nonneg.mpr hr.le) _)
  have hforward :=
    greenLocalLift_coord_taylor_closed_interval_of_radius
      (x := x) j hab hr hclosed hcoord hradius
  have hgrad :=
    greenLocalGrad_coord_lipschitz_closed_interval_of_radius
      (x := x) j j hab hr hclosed hcoord hradius
  have hdecomp :
      greenLocalLift (coordLine x j a) -
          greenLocalLift (coordLine x j b) -
          greenLocalGrad (coordLine x j b) j * (a - b) =
        -(greenLocalLift (coordLine x j b) -
          greenLocalLift (coordLine x j a) -
          greenLocalGrad (coordLine x j a) j * (b - a)) +
        (greenLocalGrad (coordLine x j b) j -
          greenLocalGrad (coordLine x j a) j) * (b - a) := by
    ring
  rw [hdecomp]
  calc
    |-(greenLocalLift (coordLine x j b) -
          greenLocalLift (coordLine x j a) -
          greenLocalGrad (coordLine x j a) j * (b - a)) +
        (greenLocalGrad (coordLine x j b) j -
          greenLocalGrad (coordLine x j a) j) * (b - a)| ≤
        |greenLocalLift (coordLine x j b) -
          greenLocalLift (coordLine x j a) -
          greenLocalGrad (coordLine x j a) j * (b - a)| +
        |(greenLocalGrad (coordLine x j b) j -
          greenLocalGrad (coordLine x j a) j) * (b - a)| := by
      simpa only [abs_neg] using abs_add_le
        (-(greenLocalLift (coordLine x j b) -
          greenLocalLift (coordLine x j a) -
          greenLocalGrad (coordLine x j a) j * (b - a)))
        ((greenLocalGrad (coordLine x j b) j -
          greenLocalGrad (coordLine x j a) j) * (b - a))
    _ ≤ M * (b - a) ^ 2 +
        (M * (b - a)) * |b - a| := by
      rw [abs_mul]
      exact add_le_add
        (by simpa only [M] using hforward)
        (mul_le_mul_of_nonneg_right
          (by simpa only [M] using hgrad)
          (abs_nonneg (b - a)))
    _ = (2 * M) * (b - a) ^ 2 := by
      rw [abs_of_pos (sub_pos.mpr hab)]
      ring

end

end Anderson4D
