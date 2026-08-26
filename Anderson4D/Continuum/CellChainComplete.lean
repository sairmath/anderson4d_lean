import Anderson4D.Continuum.LocalTripleScale
import Anderson4D.Continuum.PeriodicCellBridge

/-!
# Complete cell-chain dichotomy for paper §5.1

This file closes the analytic gap between the one-sided estimates in
`CellSingular.lean` and the per-cell chain estimate used in (5.3)--(5.4).
The integration order is centred at a selected pivot:

* in the far branch, all variables are integrated from the two endpoints
  towards a pointwise far edge;
* in the all-near branch, all outer variables are integrated towards the
  three-edge local convolution proved in `LocalTripleScale.lean`.

The elementary lattice predicate `latticePathAllNear` is proved to be
complementary to `latticePathHasFarEdge`; the case split is therefore not
an analytic hypothesis in disguise.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set
open scoped ENNReal

/-! ## The exhaustive lattice case split -/

/-- Every edge of the lattice path
`y :: internal ++ [e]` has length at most `4R`. -/
def latticePathAllNear (R : ℝ) (y e : Z4) : List Z4 → Prop
  | [] => znorm (y - e) ≤ 4 * R
  | y' :: ys =>
      znorm (y - y') ≤ 4 * R ∧ latticePathAllNear R y' e ys

/-- At least one edge of the lattice path
`y :: internal ++ [e]` has length at least `4R`. -/
def latticePathHasFarEdge (R : ℝ) (y e : Z4) : List Z4 → Prop
  | [] => 4 * R ≤ znorm (y - e)
  | y' :: ys =>
      4 * R ≤ znorm (y - y') ∨ latticePathHasFarEdge R y' e ys

/-- The near and far alternatives in the proof of (5.3) cover every
lattice path.  No geometric alternative is left as an assumption. -/
theorem latticePath_allNear_or_hasFarEdge
    (R : ℝ) (y e : Z4) (ys : List Z4) :
    latticePathAllNear R y e ys ∨
      latticePathHasFarEdge R y e ys := by
  induction ys generalizing y with
  | nil =>
      simp only [latticePathAllNear, latticePathHasFarEdge]
      exact le_total _ _
  | cons y' ys ih =>
      by_cases h : znorm (y - y') ≤ 4 * R
      · rcases ih y' with htail | htail
        · exact Or.inl ⟨h, htail⟩
        · exact Or.inr (Or.inr htail)
      · exact Or.inr (Or.inl (le_of_not_ge h))

/-- Last vertex reached by following a finite path from a starting
vertex.  This recursive form is convenient when stripping path edges. -/
def walkEnd {α : Type*} (a : α) : List α → α
  | [] => a
  | b :: bs => walkEnd b bs

@[simp] theorem walkEnd_nil {α : Type*} (a : α) :
    walkEnd a [] = a := rfl

@[simp] theorem walkEnd_cons {α : Type*} (a b : α) (bs : List α) :
    walkEnd a (b :: bs) = walkEnd b bs := rfl

theorem walkEnd_append {α : Type*} (a : α) (xs ys : List α) :
    walkEnd a (xs ++ ys) = walkEnd (walkEnd a xs) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simpa only [List.cons_append, walkEnd_cons] using ih b

@[simp] theorem walkEnd_reverse_cons {α : Type*}
    (a b : α) (bs : List α) :
    walkEnd a (b :: bs).reverse = b := by
  rw [List.reverse_cons, walkEnd_append]
  rfl

/-! ## A pivot-ordered full chain -/

/-- The full chain integral, ordered from both fixed endpoints towards
one pivot edge.  The path represented by `(left,right)` is
`x -- left -- pivot -- reverse right -- z`.

This is an honest iterated integral of the chain product, not a numerical
majorant. -/
def twoSidedCellChain (r : ℝ) (x z : T4) :
    List T4 → List T4 → ℝ
  | [], [] => invSqKer (x - z)
  | c :: cs, right =>
      ∫ u in Metric.ball c r,
        invSqKer (x - u) * twoSidedCellChain r u z cs right
          ∂paperMeasure
  | [], c :: cs =>
      ∫ u in Metric.ball c r,
        invSqKer (z - u) * twoSidedCellChain r x u [] cs
          ∂paperMeasure

theorem twoSidedCellChain_nonneg (r : ℝ) :
    ∀ (x z : T4) (left right : List T4),
      0 ≤ twoSidedCellChain r x z left right := by
  intro x z left
  induction left generalizing x z with
  | nil =>
      intro right
      induction right generalizing z with
      | nil =>
          simpa [twoSidedCellChain.eq_def] using
            (invSqKer_nonneg (x - z))
      | cons c cs ih =>
          rw [twoSidedCellChain.eq_def]
          exact integral_nonneg fun u =>
            mul_nonneg (invSqKer_nonneg _) (ih u)
  | cons c cs ih =>
      intro right
      rw [twoSidedCellChain.eq_def]
      exact integral_nonneg fun u =>
        mul_nonneg (invSqKer_nonneg _) (ih u z right)

/-- With no vertices assigned to the right side, the pivot ordering is
definitionally the original fixed-terminal chain from
`CellSingular.lean`. -/
theorem twoSidedCellChain_right_nil (r : ℝ) (x z : T4)
    (left : List T4) :
    twoSidedCellChain r x z left [] =
      terminalCellChain r x z left := by
  induction left generalizing x with
  | nil =>
      rw [twoSidedCellChain.eq_def]
      rfl
  | cons c cs ih =>
      rw [twoSidedCellChain.eq_def, terminalCellChain]
      apply integral_congr_ae
      filter_upwards with u
      rw [ih u]

/-! ## Tonelli-safe chain representation -/

/-- Nonnegative Lebesgue-integral version of the fixed-terminal chain.
Unlike the Bochner integral, it has no junk value when integrability has
not yet been established. -/
def terminalCellLIntegral (r : ℝ) (x z : T4) : List T4 → ℝ≥0∞
  | [] => ENNReal.ofReal (invSqKer (x - z))
  | c :: cs =>
      ∫⁻ u in Metric.ball c r,
        ENNReal.ofReal (invSqKer (x - u)) *
          terminalCellLIntegral r u z cs ∂paperMeasure

/-- Tonelli-safe version of the two-sided pivot ordering. -/
def twoSidedCellLIntegral (r : ℝ) (x z : T4) :
    List T4 → List T4 → ℝ≥0∞
  | [], [] => ENNReal.ofReal (invSqKer (x - z))
  | c :: cs, right =>
      ∫⁻ u in Metric.ball c r,
        ENNReal.ofReal (invSqKer (x - u)) *
          twoSidedCellLIntegral r u z cs right ∂paperMeasure
  | [], c :: cs =>
      ∫⁻ u in Metric.ball c r,
        ENNReal.ofReal (invSqKer (z - u)) *
          twoSidedCellLIntegral r x u [] cs ∂paperMeasure

theorem measurable_terminalCellLIntegral (r : ℝ) (cs : List T4) :
    Measurable fun p : T4 × T4 =>
      terminalCellLIntegral r p.1 p.2 cs := by
  induction cs with
  | nil =>
      rw [show (fun p : T4 × T4 =>
          terminalCellLIntegral r p.1 p.2 []) =
        fun p => ENNReal.ofReal (invSqKer (p.1 - p.2)) by
          funext p
          rw [terminalCellLIntegral.eq_def]]
      exact (measurable_invSqKer.comp
        (measurable_fst.sub measurable_snd)).ennreal_ofReal
  | cons c cs ih =>
      rw [show (fun p : T4 × T4 =>
          terminalCellLIntegral r p.1 p.2 (c :: cs)) =
        fun p => ∫⁻ u in Metric.ball c r,
          ENNReal.ofReal (invSqKer (p.1 - u)) *
            terminalCellLIntegral r u p.2 cs ∂paperMeasure by
          funext p
          rw [terminalCellLIntegral.eq_def]]
      apply Measurable.lintegral_prod_right
      have hker : Measurable fun q : (T4 × T4) × T4 =>
          ENNReal.ofReal (invSqKer (q.1.1 - q.2)) :=
        (measurable_invSqKer.comp
          ((measurable_fst.comp measurable_fst).sub
            measurable_snd)).ennreal_ofReal
      have htail : Measurable fun q : (T4 × T4) × T4 =>
          terminalCellLIntegral r q.2 q.1.2 cs :=
        ih.comp
          (measurable_snd.prodMk
            (measurable_snd.comp measurable_fst))
      exact hker.mul htail

/-- Tonelli moves a final integrated vertex to the outside of the
fixed-terminal chain.  No integrability premise is needed because this is
an equality of nonnegative Lebesgue integrals. -/
theorem terminalCellLIntegral_append_singleton
    (r : ℝ) (x z c : T4) (cs : List T4) :
    terminalCellLIntegral r x z (cs ++ [c]) =
      ∫⁻ u in Metric.ball c r,
        ENNReal.ofReal (invSqKer (z - u)) *
          terminalCellLIntegral r x u cs ∂paperMeasure := by
  induction cs generalizing x with
  | nil =>
      simp only [List.nil_append]
      rw [terminalCellLIntegral.eq_def]
      apply lintegral_congr
      intro u
      rw [terminalCellLIntegral.eq_def, invSqKer_sub_comm u z]
      exact mul_comm _ _
  | cons d ds ih =>
      rw [List.cons_append, terminalCellLIntegral.eq_def]
      have hKx : Measurable fun v : T4 =>
          ENNReal.ofReal (invSqKer (x - v)) :=
        (measurable_invSqKer.comp
          (measurable_const.sub measurable_id)).ennreal_ofReal
      have hKz : Measurable fun u : T4 =>
          ENNReal.ofReal (invSqKer (z - u)) :=
        (measurable_invSqKer.comp
          (measurable_const.sub measurable_id)).ennreal_ofReal
      have htail :
          Measurable fun q : T4 × T4 =>
            terminalCellLIntegral r q.1 q.2 ds :=
        measurable_terminalCellLIntegral r ds
      have hjoint : Measurable fun q : T4 × T4 =>
          ENNReal.ofReal (invSqKer (x - q.1)) *
            (ENNReal.ofReal (invSqKer (z - q.2)) *
              terminalCellLIntegral r q.1 q.2 ds) :=
        (hKx.comp measurable_fst).mul
          ((hKz.comp measurable_snd).mul htail)
      calc
        (∫⁻ v in Metric.ball d r,
            ENNReal.ofReal (invSqKer (x - v)) *
              terminalCellLIntegral r v z (ds ++ [c])
              ∂paperMeasure)
            = ∫⁻ v in Metric.ball d r,
                ∫⁻ u in Metric.ball c r,
                  ENNReal.ofReal (invSqKer (x - v)) *
                    (ENNReal.ofReal (invSqKer (z - u)) *
                      terminalCellLIntegral r v u ds)
                    ∂paperMeasure ∂paperMeasure := by
                apply lintegral_congr
                intro v
                rw [ih v]
                symm
                exact lintegral_const_mul''
                  (ENNReal.ofReal (invSqKer (x - v)))
                  ((hKz.mul
                    ((measurable_terminalCellLIntegral r ds).comp
                      (measurable_const.prodMk measurable_id))).aemeasurable)
        _ = ∫⁻ u in Metric.ball c r,
              ∫⁻ v in Metric.ball d r,
                ENNReal.ofReal (invSqKer (x - v)) *
                  (ENNReal.ofReal (invSqKer (z - u)) *
                    terminalCellLIntegral r v u ds)
                  ∂paperMeasure ∂paperMeasure :=
              lintegral_lintegral_swap hjoint.aemeasurable
        _ = ∫⁻ u in Metric.ball c r,
              ENNReal.ofReal (invSqKer (z - u)) *
                terminalCellLIntegral r x u (d :: ds)
              ∂paperMeasure := by
                apply lintegral_congr
                intro u
                rw [terminalCellLIntegral.eq_def]
                dsimp only
                calc
                  (∫⁻ v in Metric.ball d r,
                      ENNReal.ofReal (invSqKer (x - v)) *
                        (ENNReal.ofReal (invSqKer (z - u)) *
                          terminalCellLIntegral r v u ds)
                        ∂paperMeasure)
                      = ∫⁻ v in Metric.ball d r,
                          ENNReal.ofReal (invSqKer (z - u)) *
                            (ENNReal.ofReal (invSqKer (x - v)) *
                              terminalCellLIntegral r v u ds)
                          ∂paperMeasure := by
                            apply lintegral_congr
                            intro v
                            ring
                  _ = ENNReal.ofReal (invSqKer (z - u)) *
                        ∫⁻ v in Metric.ball d r,
                          ENNReal.ofReal (invSqKer (x - v)) *
                            terminalCellLIntegral r v u ds
                          ∂paperMeasure :=
                        lintegral_const_mul''
                          (ENNReal.ofReal (invSqKer (z - u)))
                          ((hKx.mul
                            ((measurable_terminalCellLIntegral r ds).comp
                              (measurable_id.prodMk
                                measurable_const))).aemeasurable)

/-- **Tonelli reordering for the selected pivot.**  The two-sided
integration order is exactly the original fixed-terminal chain on
`left ++ reverse right`.  This is unconditional: all swaps took place in
`ℝ≥0∞` above, before any finiteness or Bochner-integrability claim. -/
theorem twoSidedCellLIntegral_eq_terminal
    (r : ℝ) (x z : T4) (left right : List T4) :
    twoSidedCellLIntegral r x z left right =
      terminalCellLIntegral r x z (left ++ right.reverse) := by
  induction left generalizing x z with
  | nil =>
      induction right generalizing z with
      | nil =>
          rw [twoSidedCellLIntegral.eq_def]
          rfl
      | cons c cs ih =>
          rw [twoSidedCellLIntegral.eq_def, List.nil_append]
          calc
            (∫⁻ u in Metric.ball c r,
                ENNReal.ofReal (invSqKer (z - u)) *
                  twoSidedCellLIntegral r x u [] cs
                ∂paperMeasure)
                = ∫⁻ u in Metric.ball c r,
                    ENNReal.ofReal (invSqKer (z - u)) *
                      terminalCellLIntegral r x u cs.reverse
                    ∂paperMeasure := by
                      apply lintegral_congr
                      intro u
                      exact congrArg
                        (fun t => ENNReal.ofReal (invSqKer (z - u)) * t)
                        (by simpa only [List.nil_append] using ih u)
            _ = terminalCellLIntegral r x z (cs.reverse ++ [c]) :=
              (terminalCellLIntegral_append_singleton
                r x z c cs.reverse).symm
            _ = terminalCellLIntegral r x z (c :: cs).reverse := by
              rw [List.reverse_cons]
  | cons c cs ih =>
      rw [twoSidedCellLIntegral.eq_def, List.cons_append,
        terminalCellLIntegral.eq_def]
      apply lintegral_congr
      intro u
      rw [ih u z]

/-- A reusable nonnegative one-step estimate.  It converts an ordinary
integrable kernel bound and a uniform bound on the remaining
`ℝ≥0∞`-chain into a bound for the next Lebesgue integral. -/
theorem lintegral_ofReal_mul_le_of_le_const
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {g : α → ℝ≥0∞} {K B : ℝ}
    (hf : Integrable f μ)
    (hfnn : ∀ᵐ a ∂μ, 0 ≤ f a)
    (hK : 0 ≤ K)
    (hB : ∫ a, f a ∂μ ≤ B)
    (hg : ∀ᵐ a ∂μ, g a ≤ ENNReal.ofReal K) :
    (∫⁻ a, ENNReal.ofReal (f a) * g a ∂μ) ≤
      ENNReal.ofReal (K * B) := by
  have hInt : 0 ≤ ∫ a, f a ∂μ := integral_nonneg_of_ae hfnn
  calc
    (∫⁻ a, ENNReal.ofReal (f a) * g a ∂μ)
        ≤ ∫⁻ a, ENNReal.ofReal (f a) * ENNReal.ofReal K ∂μ :=
      lintegral_mono_ae (hg.mono fun a ha =>
        mul_right_mono ha)
    _ = (∫⁻ a, ENNReal.ofReal (f a) ∂μ) * ENNReal.ofReal K :=
      lintegral_mul_const''
        (ENNReal.ofReal K) hf.aemeasurable.ennreal_ofReal
    _ = ENNReal.ofReal (∫ a, f a ∂μ) * ENNReal.ofReal K := by
      rw [ofReal_integral_eq_lintegral_ofReal hf hfnn]
    _ = ENNReal.ofReal ((∫ a, f a ∂μ) * K) := by
      rw [ENNReal.ofReal_mul hInt]
    _ ≤ ENNReal.ofReal (K * B) := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_comm (∫ a, f a ∂μ) K]
      exact mul_le_mul_of_nonneg_left hB hK

/-- Lattice product along the same pivot-ordered path, including the
pivot edge. -/
def latticeTwoSidedPathWeight (y e : Z4) :
    List Z4 → List Z4 → ℝ
  | [], [] => latticeEdgeWeight y e
  | y' :: ys, right =>
      latticeEdgeWeight y y' *
        latticeTwoSidedPathWeight y' e ys right
  | [], e' :: es =>
      latticeEdgeWeight e e' *
        latticeTwoSidedPathWeight y e' [] es

theorem latticeEdgeWeight_nonneg_complete (y e : Z4) :
    0 ≤ latticeEdgeWeight y e := by
  unfold latticeEdgeWeight
  positivity

theorem latticeTwoSidedPathWeight_nonneg (y e : Z4) :
    ∀ (left right : List Z4),
      0 ≤ latticeTwoSidedPathWeight y e left right := by
  intro left
  induction left generalizing y e with
  | nil =>
      intro right
      induction right generalizing e with
      | nil =>
          rw [latticeTwoSidedPathWeight.eq_def]
          change 0 ≤ latticeEdgeWeight y e
          exact latticeEdgeWeight_nonneg_complete y e
      | cons e' es ih =>
          rw [latticeTwoSidedPathWeight.eq_def]
          change 0 ≤ latticeEdgeWeight e e' *
            latticeTwoSidedPathWeight y e' [] es
          exact mul_nonneg
            (latticeEdgeWeight_nonneg_complete e e') (ih e')
  | cons y' ys ih =>
      intro right
      rw [latticeTwoSidedPathWeight.eq_def]
      change 0 ≤ latticeEdgeWeight y y' *
        latticeTwoSidedPathWeight y' e ys right
      exact mul_nonneg (latticeEdgeWeight_nonneg_complete y y')
        (ih y' e right)

/-- Exact no-wrapping data for all integrated outer edges and for the
remaining pivot edge. -/
def LatticeTwoSidedNoWrap (ε : ℝ) (y e : Z4)
    (left right : List Z4) : Prop :=
  LatticeCellPathNoWrap ε y left ∧
    LatticeCellPathNoWrap ε e right ∧
      dist (latticeTorusCenter ε (walkEnd y left))
          (latticeTorusCenter ε (walkEnd e right)) =
        ε * znorm (walkEnd y left - walkEnd e right)

/-- The selected pivot is a far edge. -/
def LatticeTwoSidedPivotFar (R : ℝ) (y e : Z4)
    (left right : List Z4) : Prop :=
  4 * R ≤ znorm (walkEnd y left - walkEnd e right)

/-- A far edge in a linearly ordered path can be selected as the central
edge of a two-sided pivot ordering.  Together with
`latticePath_allNear_or_hasFarEdge`, this removes the last possible
"assume a suitable pivot exists" shortcut from the (5.3) reduction. -/
theorem latticePathHasFarEdge_exists_twoSidedPivot
    {R : ℝ} {y e : Z4} {ys : List Z4}
    (h : latticePathHasFarEdge R y e ys) :
    ∃ left right : List Z4,
      ys = left ++ right.reverse ∧
        LatticeTwoSidedPivotFar R y e left right := by
  induction ys generalizing y with
  | nil =>
      rw [latticePathHasFarEdge.eq_def] at h
      refine ⟨[], [], rfl, ?_⟩
      simpa [LatticeTwoSidedPivotFar] using h
  | cons y' ys ih =>
      rw [latticePathHasFarEdge.eq_def] at h
      rcases h with hhead | htail
      · refine ⟨[], (y' :: ys).reverse, ?_, ?_⟩
        · simp
        · unfold LatticeTwoSidedPivotFar
          simp only [walkEnd_nil, walkEnd_reverse_cons]
          exact hhead
      · obtain ⟨left, right, hdecomp, hpivot⟩ := ih htail
        refine ⟨y' :: left, right, ?_, ?_⟩
        · simp only [List.cons_append, hdecomp]
        · simpa [LatticeTwoSidedPivotFar] using hpivot

/-- Final exhaustive form used by the analytic assembly: either every
edge is near, or the same internal path has a concrete two-sided
decomposition with a far central pivot. -/
theorem latticePath_allNear_or_exists_twoSidedPivot
    (R : ℝ) (y e : Z4) (ys : List Z4) :
    latticePathAllNear R y e ys ∨
      ∃ left right : List Z4,
        ys = left ++ right.reverse ∧
          LatticeTwoSidedPivotFar R y e left right := by
  rcases latticePath_allNear_or_hasFarEdge R y e ys with hnear | hfar
  · exact Or.inl hnear
  · exact Or.inr (latticePathHasFarEdge_exists_twoSidedPivot hfar)

/-! ## Extracting the all-near three-edge core -/

/-- A path with at least two internal vertices has a unique-enough
decomposition into an outer prefix and its final two vertices. -/
theorem exists_eq_append_pair_of_two_le_length
    {α : Type*} {xs : List α} (h : 2 ≤ xs.length) :
    ∃ pre : List α, ∃ a b : α, xs = pre ++ [a, b] := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      cases xs with
      | nil => simp at h
      | cons y ys =>
          by_cases hys : ys = []
          · subst ys
            exact ⟨[], x, y, rfl⟩
          · have htail : 2 ≤ (y :: ys).length := by
              simp only [List.length_cons]
              have : 0 < ys.length := List.length_pos_of_ne_nil hys
              omega
            obtain ⟨pre, a, b, hdecomp⟩ := ih htail
            exact ⟨x :: pre, a, b, by
              simp only [List.cons_append, hdecomp]⟩

/-- Splitting a no-wrap path at a list append. -/
theorem latticeCellPathNoWrap_append_iff
    (ε : ℝ) (y : Z4) (xs zs : List Z4) :
    LatticeCellPathNoWrap ε y (xs ++ zs) ↔
      LatticeCellPathNoWrap ε y xs ∧
        LatticeCellPathNoWrap ε (walkEnd y xs) zs := by
  induction xs generalizing y with
  | nil =>
      simp only [List.nil_append, walkEnd_nil]
      constructor
      · exact fun h => ⟨trivial, h⟩
      · exact fun h => h.2
  | cons x xs ih =>
      rw [List.cons_append, LatticeCellPathNoWrap.eq_def,
        LatticeCellPathNoWrap.eq_def]
      dsimp only
      rw [walkEnd_cons]
      rw [ih x]
      tauto

/-- Reverse a no-wrap segment whose final endpoint is exposed.  Besides
the reversed outer path, the conclusion records the final (pivot) edge
with exactly the orientation used by `LatticeTwoSidedNoWrap`. -/
theorem latticeCellPathNoWrap_reverse_endpoint
    (ε : ℝ) (p e : Z4) (right : List Z4)
    (hnowrap :
      LatticeCellPathNoWrap ε p (right.reverse ++ [e])) :
    LatticeCellPathNoWrap ε e right ∧
      dist (latticeTorusCenter ε p)
          (latticeTorusCenter ε (walkEnd e right)) =
        ε * znorm (p - walkEnd e right) := by
  induction right generalizing p e with
  | nil =>
      simp only [List.reverse_nil, List.nil_append] at hnowrap
      rw [LatticeCellPathNoWrap.eq_def] at hnowrap
      exact ⟨trivial, by
        simpa only [walkEnd_nil] using hnowrap.1⟩
  | cons c cs ih =>
      have hfull :
          LatticeCellPathNoWrap ε p
            (cs.reverse ++ [c, e]) := by
        simpa only [List.reverse_cons, List.append_assoc,
          List.cons_append, List.nil_append] using hnowrap
      obtain ⟨hprefix, htail⟩ :=
        (latticeCellPathNoWrap_append_iff
          ε p cs.reverse [c, e]).mp hfull
      rw [LatticeCellPathNoWrap.eq_def] at htail
      dsimp only at htail
      rw [LatticeCellPathNoWrap.eq_def] at htail
      dsimp only at htail
      have htoC :
          LatticeCellPathNoWrap ε p
            (cs.reverse ++ [c]) :=
        (latticeCellPathNoWrap_append_iff
          ε p cs.reverse [c]).mpr
            ⟨hprefix, by
              rw [LatticeCellPathNoWrap.eq_def]
              exact ⟨htail.1, trivial⟩⟩
      obtain ⟨hreverseTail, hpivot⟩ := ih p c htoC
      constructor
      · rw [LatticeCellPathNoWrap.eq_def]
        exact ⟨by
          simpa only [dist_comm, znorm_sub_comm] using htail.2.1,
          hreverseTail⟩
      · simpa only [walkEnd_cons] using hpivot

/-- A far edge selected from an actual no-wrap full path carries all the
geometry needed by the two-sided analytic estimate. -/
theorem latticePathHasFarEdge_exists_twoSidedGeometry
    {ε R : ℝ} {y e : Z4} {ys : List Z4}
    (hfar : latticePathHasFarEdge R y e ys)
    (hnowrap : LatticeCellPathNoWrap ε y (ys ++ [e])) :
    ∃ left right : List Z4,
      ys = left ++ right.reverse ∧
        LatticeTwoSidedNoWrap ε y e left right ∧
          LatticeTwoSidedPivotFar R y e left right := by
  obtain ⟨left, right, hdecomp, hpivotFar⟩ :=
    latticePathHasFarEdge_exists_twoSidedPivot hfar
  have hfull :
      LatticeCellPathNoWrap ε y
        (left ++ (right.reverse ++ [e])) := by
    rw [← List.append_assoc, ← hdecomp]
    exact hnowrap
  obtain ⟨hleft, htail⟩ :=
    (latticeCellPathNoWrap_append_iff
      ε y left (right.reverse ++ [e])).mp hfull
  obtain ⟨hright, hpivot⟩ :=
    latticeCellPathNoWrap_reverse_endpoint
      ε (walkEnd y left) e right htail
  exact ⟨left, right, hdecomp,
    ⟨hleft, hright, hpivot⟩, hpivotFar⟩

/-- Exhaustive geometric split for one actual no-wrap lattice path.  The
near branch is the original `latticePathAllNear` predicate; the far branch
contains a concrete decomposition and no extra geometric assumptions. -/
theorem latticePath_allNear_or_exists_twoSidedGeometry
    (ε R : ℝ) (y e : Z4) (ys : List Z4)
    (hnowrap : LatticeCellPathNoWrap ε y (ys ++ [e])) :
    latticePathAllNear R y e ys ∨
      ∃ left right : List Z4,
        ys = left ++ right.reverse ∧
          LatticeTwoSidedNoWrap ε y e left right ∧
            LatticeTwoSidedPivotFar R y e left right := by
  rcases latticePath_allNear_or_hasFarEdge R y e ys with hnear | hfar
  · exact Or.inl hnear
  · exact Or.inr
      (latticePathHasFarEdge_exists_twoSidedGeometry hfar hnowrap)

/-- If an all-near path is written with its final two internal vertices
exposed, its last three edges are `4R`-near. -/
theorem latticePathAllNear_append_pair
    {R : ℝ} {y e a b : Z4} {pre : List Z4}
    (h : latticePathAllNear R y e (pre ++ [a, b])) :
    znorm (walkEnd y pre - a) ≤ 4 * R ∧
      znorm (a - b) ≤ 4 * R ∧
        znorm (b - e) ≤ 4 * R := by
  induction pre generalizing y with
  | nil =>
      rw [List.nil_append, latticePathAllNear.eq_def] at h
      dsimp only at h
      rw [latticePathAllNear.eq_def] at h
      dsimp only at h
      rw [latticePathAllNear.eq_def] at h
      dsimp only at h
      simpa only [walkEnd_nil] using h
  | cons c cs ih =>
      rw [List.cons_append, latticePathAllNear.eq_def] at h
      simpa only [walkEnd_cons] using ih h.2

/-! ## The far-pivot estimate -/

/-- A far pivot with `k` integrated vertices gives `k` ordinary
`ε²⟨Δy⟩⁻²` factors and one pointwise `ε⁻²⟨Δy⟩⁻²` factor.  This is the
general (pivot-at-an-arbitrary-edge) form of the far branch in (5.3). -/
theorem twoSidedLatticeCellChain_le_of_far :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y e : Z4) (left right : List Z4) (x z : T4),
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTwoSidedNoWrap ε y e left right →
        LatticeTwoSidedPivotFar R y e left right →
        twoSidedCellChain (R * ε) x z
            (left.map (latticeTorusCenter ε))
            (right.map (latticeTorusCenter ε)) ≤
          (C * (R ^ 2 + R ^ 4)) ^ (left.length + right.length) *
            ε ^ (2 * (left.length + right.length)) *
            (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
            latticeTwoSidedPathWeight y e left right := by
  obtain ⟨C, hC, hedge⟩ := invSqKer_latticeCellEdge_le
  refine ⟨C, hC, ?_⟩
  intro ε R hε hR y e left
  induction left generalizing y e with
  | nil =>
      intro right
      induction right generalizing e with
      | nil =>
          intro x z hx hz hnowrap hfar
          rcases hnowrap with ⟨_, _, hpivot⟩
          have hpoint :=
            invSqKer_sub_le_of_mem_balls_of_far
              (mul_pos hR hε)
              (by simpa only [latticeCellNeighborhood] using hx)
              (by simpa only [latticeCellNeighborhood] using hz)
              (by
                simp only [walkEnd_nil] at hpivot hfar
                calc
                  4 * (R * ε) = ε * (4 * R) := by ring
                  _ ≤ ε * znorm (y - e) :=
                    mul_le_mul_of_nonneg_left hfar hε.le
                  _ = dist (latticeTorusCenter ε y)
                      (latticeTorusCenter ε e) := hpivot.symm)
          simp only [walkEnd_nil] at hpivot hfar
          have hlattice :=
            metricTerminalEdgeWeight_lattice_le
              hε hR y e hpivot hfar
          calc
            twoSidedCellChain (R * ε) x z
                ([].map (latticeTorusCenter ε))
                ([].map (latticeTorusCenter ε))
                = invSqKer (x - z) := by
                  simp [twoSidedCellChain.eq_def]
            _ ≤ 4 * (dist (latticeTorusCenter ε y)
                  (latticeTorusCenter ε e) ^ 2)⁻¹ := hpoint
            _ ≤ terminalRadiusFactor R * (ε ^ 2)⁻¹ *
                  latticeEdgeWeight y e := hlattice
            _ = (C * (R ^ 2 + R ^ 4)) ^
                  ([].length + [].length) *
                ε ^ (2 * ([].length + [].length)) *
                (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
                latticeTwoSidedPathWeight y e [] [] := by
                  simp [latticeTwoSidedPathWeight]
      | cons e' es ih =>
          intro x z hx hz hnowrap hfar
          rcases hnowrap with ⟨_, hright, hpivot⟩
          rcases hright with ⟨hEdgeEq, hrightTail⟩
          let K : ℝ :=
            (C * (R ^ 2 + R ^ 4)) ^ es.length *
              ε ^ (2 * es.length) *
              (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
              latticeTwoSidedPathWeight y e' [] es
          have hK : 0 ≤ K := by
            dsimp [K]
            exact mul_nonneg
              (mul_nonneg
                (mul_nonneg (by positivity) (by positivity))
                (mul_nonneg
                  (terminalRadiusFactor_pos hR).le
                  (inv_nonneg.mpr (sq_nonneg ε))))
              (latticeTwoSidedPathWeight_nonneg y e' [] es)
          have htail :
              ∀ u ∈ latticeCellNeighborhood ε R e',
                twoSidedCellChain (R * ε) x u
                    ([].map (latticeTorusCenter ε))
                    (es.map (latticeTorusCenter ε)) ≤ K := by
            intro u hu
            simpa only [K, List.length_nil, zero_add] using
              ih e' x u hx hu
              ⟨trivial, hrightTail, by simpa using hpivot⟩
              (by simpa [LatticeTwoSidedPivotFar] using hfar)
          have hmono :
              twoSidedCellChain (R * ε) x z
                  ([] : List T4)
                  ((e' :: es).map (latticeTorusCenter ε)) ≤
                ∫ u in latticeCellNeighborhood ε R e',
                  invSqKer (z - u) * K ∂paperMeasure := by
            rw [twoSidedCellChain.eq_def]
            exact integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun u =>
                mul_nonneg (invSqKer_nonneg _)
                  (twoSidedCellChain_nonneg
                    (R * ε) x u [] (es.map (latticeTorusCenter ε))))
              ((integrable_invSqKer_sub_left z).mul_const K).integrableOn
              (by
                filter_upwards
                  [ae_restrict_mem
                    (measurableSet_latticeCellNeighborhood ε R e')]
                    with u hu
                exact mul_le_mul_of_nonneg_left
                  (htail u hu) (invSqKer_nonneg _))
          have hedge' :
              (∫ u in latticeCellNeighborhood ε R e',
                  invSqKer (z - u) ∂paperMeasure) ≤
                C * (R ^ 2 + R ^ 4) * ε ^ 2 *
                  latticeEdgeWeight e e' :=
            hedge ε R hε hR e e' z hEdgeEq hz
          calc
            twoSidedCellChain (R * ε) x z
                ([] : List T4)
                ((e' :: es).map (latticeTorusCenter ε))
                ≤ ∫ u in latticeCellNeighborhood ε R e',
                    invSqKer (z - u) * K ∂paperMeasure := hmono
            _ = K * (∫ u in latticeCellNeighborhood ε R e',
                    invSqKer (z - u) ∂paperMeasure) := by
                  rw [integral_mul_const]
                  ring
            _ ≤ K * (C * (R ^ 2 + R ^ 4) * ε ^ 2 *
                  latticeEdgeWeight e e') :=
                mul_le_mul_of_nonneg_left hedge' hK
            _ = (C * (R ^ 2 + R ^ 4)) ^
                  (([] : List Z4).length + (e' :: es).length) *
                ε ^ (2 * (([] : List Z4).length + (e' :: es).length)) *
                (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
                latticeTwoSidedPathWeight y e [] (e' :: es) := by
                  simp only [List.length_nil, zero_add, List.length_cons,
                    latticeTwoSidedPathWeight, K, pow_succ]
                  rw [show 2 * (es.length + 1) =
                    2 * es.length + 2 by omega, pow_add]
                  ring
  | cons y' ys ih =>
      intro right x z hx hz hnowrap hfar
      rcases hnowrap with ⟨hleft, hright, hpivot⟩
      rcases hleft with ⟨hEdgeEq, hleftTail⟩
      let K : ℝ :=
        (C * (R ^ 2 + R ^ 4)) ^ (ys.length + right.length) *
          ε ^ (2 * (ys.length + right.length)) *
          (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
          latticeTwoSidedPathWeight y' e ys right
      have hK : 0 ≤ K := by
        dsimp [K]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity) (by positivity))
            (mul_nonneg
              (terminalRadiusFactor_pos hR).le
              (inv_nonneg.mpr (sq_nonneg ε))))
          (latticeTwoSidedPathWeight_nonneg y' e ys right)
      have htail :
          ∀ u ∈ latticeCellNeighborhood ε R y',
            twoSidedCellChain (R * ε) u z
                (ys.map (latticeTorusCenter ε))
                (right.map (latticeTorusCenter ε)) ≤ K := by
        intro u hu
        exact ih y' e right u z hu hz
          ⟨hleftTail, hright, by simpa using hpivot⟩
          (by simpa [LatticeTwoSidedPivotFar] using hfar)
      have hmono :
          twoSidedCellChain (R * ε) x z
              ((y' :: ys).map (latticeTorusCenter ε))
              (right.map (latticeTorusCenter ε)) ≤
            ∫ u in latticeCellNeighborhood ε R y',
              invSqKer (x - u) * K ∂paperMeasure := by
        rw [twoSidedCellChain.eq_def]
        exact integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun u =>
            mul_nonneg (invSqKer_nonneg _)
              (twoSidedCellChain_nonneg
                (R * ε) u z
                (ys.map (latticeTorusCenter ε))
                (right.map (latticeTorusCenter ε))))
          ((integrable_invSqKer_sub_left x).mul_const K).integrableOn
          (by
            filter_upwards
              [ae_restrict_mem
                (measurableSet_latticeCellNeighborhood ε R y')]
                with u hu
            exact mul_le_mul_of_nonneg_left
              (htail u hu) (invSqKer_nonneg _))
      have hedge' :
          (∫ u in latticeCellNeighborhood ε R y',
              invSqKer (x - u) ∂paperMeasure) ≤
            C * (R ^ 2 + R ^ 4) * ε ^ 2 *
              latticeEdgeWeight y y' :=
        hedge ε R hε hR y y' x hEdgeEq hx
      calc
        twoSidedCellChain (R * ε) x z
            ((y' :: ys).map (latticeTorusCenter ε))
            (right.map (latticeTorusCenter ε))
            ≤ ∫ u in latticeCellNeighborhood ε R y',
                invSqKer (x - u) * K ∂paperMeasure := hmono
        _ = K * (∫ u in latticeCellNeighborhood ε R y',
                invSqKer (x - u) ∂paperMeasure) := by
              rw [integral_mul_const]
              ring
        _ ≤ K * (C * (R ^ 2 + R ^ 4) * ε ^ 2 *
              latticeEdgeWeight y y') :=
            mul_le_mul_of_nonneg_left hedge' hK
        _ = (C * (R ^ 2 + R ^ 4)) ^
              ((y' :: ys).length + right.length) *
            ε ^ (2 * ((y' :: ys).length + right.length)) *
            (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
            latticeTwoSidedPathWeight y e (y' :: ys) right := by
              simp only [List.length_cons, latticeTwoSidedPathWeight, K,
                pow_succ]
              rw [show 2 * (ys.length + 1 + right.length) =
                2 * (ys.length + right.length) + 2 by omega, pow_add]
              ring

/-! ### Tonelli-safe far estimate -/

/-- Recursive real majorant for the far-pivot chain.  Its recursive shape
matches the two-sided Lebesgue integral exactly. -/
def latticeFarChainMajorant (C ε R : ℝ) (y e : Z4) :
    List Z4 → List Z4 → ℝ
  | [], [] =>
      terminalRadiusFactor R * (ε ^ 2)⁻¹ * latticeEdgeWeight y e
  | y' :: ys, right =>
      (C * (R ^ 2 + R ^ 4) * ε ^ 2 * latticeEdgeWeight y y') *
        latticeFarChainMajorant C ε R y' e ys right
  | [], e' :: es =>
      (C * (R ^ 2 + R ^ 4) * ε ^ 2 * latticeEdgeWeight e e') *
        latticeFarChainMajorant C ε R y e' [] es

theorem latticeFarChainMajorant_nonneg
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (ε : ℝ) (y e : Z4) :
    ∀ left right,
      0 ≤ latticeFarChainMajorant C ε R y e left right := by
  intro left
  induction left generalizing y e with
  | nil =>
      intro right
      induction right generalizing e with
      | nil =>
          rw [latticeFarChainMajorant.eq_def]
          exact mul_nonneg
            (mul_nonneg
              (terminalRadiusFactor_pos hR).le
              (inv_nonneg.mpr (sq_nonneg ε)))
            (latticeEdgeWeight_nonneg_complete y e)
      | cons e' es ih =>
          rw [latticeFarChainMajorant.eq_def]
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg hC
                  (add_nonneg (sq_nonneg R) (by positivity)))
                (sq_nonneg ε))
              (latticeEdgeWeight_nonneg_complete e e'))
            (ih e')
  | cons y' ys ih =>
      intro right
      rw [latticeFarChainMajorant.eq_def]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hC
              (add_nonneg (sq_nonneg R) (by positivity)))
            (sq_nonneg ε))
          (latticeEdgeWeight_nonneg_complete y y'))
        (ih y' e right)

theorem latticeFarChainMajorant_eq_closed
    (C ε R : ℝ) (y e : Z4) (left right : List Z4) :
    latticeFarChainMajorant C ε R y e left right =
      (C * (R ^ 2 + R ^ 4)) ^ (left.length + right.length) *
        ε ^ (2 * (left.length + right.length)) *
        (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
        latticeTwoSidedPathWeight y e left right := by
  induction left generalizing y e with
  | nil =>
      induction right generalizing e with
      | nil =>
          rw [latticeFarChainMajorant.eq_def,
            latticeTwoSidedPathWeight.eq_def]
          simp
      | cons e' es ih =>
          rw [latticeFarChainMajorant.eq_def]
          dsimp only
          rw [latticeTwoSidedPathWeight.eq_def]
          dsimp only
          rw [ih e']
          simp only [List.length_nil, zero_add, List.length_cons]
          rw [show 2 * (es.length + 1) =
            2 * es.length + 2 by omega, pow_add, pow_succ]
          ring
  | cons y' ys ih =>
      rw [latticeFarChainMajorant.eq_def]
      dsimp only
      rw [latticeTwoSidedPathWeight.eq_def]
      dsimp only
      rw [ih y' e]
      simp only [List.length_cons]
      rw [show 2 * (ys.length + 1 + right.length) =
        2 * (ys.length + right.length) + 2 by omega]
      rw [show ys.length + 1 + right.length =
        (ys.length + right.length) + 1 by omega, pow_add, pow_succ]
      ring

/-- Far-pivot bound for the Tonelli-safe integral.  Consequently the
selected pivot order is finite, and
`twoSidedCellLIntegral_eq_terminal` transports the same bound to the
original chain order. -/
theorem twoSidedCellLIntegral_le_of_far :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y e : Z4) (left right : List Z4) (x z : T4),
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTwoSidedNoWrap ε y e left right →
        LatticeTwoSidedPivotFar R y e left right →
        twoSidedCellLIntegral (R * ε) x z
            (left.map (latticeTorusCenter ε))
            (right.map (latticeTorusCenter ε)) ≤
          ENNReal.ofReal
            (latticeFarChainMajorant C ε R y e left right) := by
  obtain ⟨C, hC, hedge⟩ := invSqKer_latticeCellEdge_le
  refine ⟨C, hC, ?_⟩
  intro ε R hε hR y e left
  induction left generalizing y e with
  | nil =>
      intro right
      induction right generalizing e with
      | nil =>
          intro x z hx hz hnowrap hfar
          rcases hnowrap with ⟨_, _, hpivot⟩
          simp only [walkEnd_nil] at hpivot hfar
          have hpoint :=
            invSqKer_sub_le_of_mem_balls_of_far
              (mul_pos hR hε)
              (by simpa only [latticeCellNeighborhood] using hx)
              (by simpa only [latticeCellNeighborhood] using hz)
              (by
                calc
                  4 * (R * ε) = ε * (4 * R) := by ring
                  _ ≤ ε * znorm (y - e) :=
                    mul_le_mul_of_nonneg_left hfar hε.le
                  _ = dist (latticeTorusCenter ε y)
                      (latticeTorusCenter ε e) := hpivot.symm)
          have hlattice :=
            metricTerminalEdgeWeight_lattice_le
              hε hR y e hpivot hfar
          rw [twoSidedCellLIntegral.eq_def,
            latticeFarChainMajorant.eq_def]
          exact ENNReal.ofReal_le_ofReal (hpoint.trans hlattice)
      | cons e' es ih =>
          intro x z hx hz hnowrap hfar
          rcases hnowrap with ⟨_, hright, hpivot⟩
          rcases hright with ⟨hEdgeEq, hrightTail⟩
          let K := latticeFarChainMajorant C ε R y e' [] es
          have hK : 0 ≤ K :=
            latticeFarChainMajorant_nonneg hC.le hR ε y e' [] es
          have htail :
              ∀ u ∈ latticeCellNeighborhood ε R e',
                twoSidedCellLIntegral (R * ε) x u
                  ([].map (latticeTorusCenter ε))
                  (es.map (latticeTorusCenter ε)) ≤
                ENNReal.ofReal K := by
            intro u hu
            exact ih e' x u hx hu
              ⟨trivial, hrightTail, by simpa using hpivot⟩
              (by simpa [LatticeTwoSidedPivotFar] using hfar)
          have hedge' :
              (∫ u in latticeCellNeighborhood ε R e',
                  invSqKer (z - u) ∂paperMeasure) ≤
                C * (R ^ 2 + R ^ 4) * ε ^ 2 *
                  latticeEdgeWeight e e' :=
            hedge ε R hε hR e e' z hEdgeEq hz
          have hstep :=
            lintegral_ofReal_mul_le_of_le_const
              ((integrable_invSqKer_sub_left z).integrableOn)
              (Filter.Eventually.of_forall fun u => invSqKer_nonneg _)
              hK hedge'
              (by
                filter_upwards
                  [ae_restrict_mem
                    (measurableSet_latticeCellNeighborhood ε R e')]
                    with u hu
                exact htail u hu)
          rw [twoSidedCellLIntegral.eq_def,
            latticeFarChainMajorant.eq_def]
          change
            (∫⁻ u in latticeCellNeighborhood ε R e',
                ENNReal.ofReal (invSqKer (z - u)) *
                  twoSidedCellLIntegral (R * ε) x u []
                    (es.map (latticeTorusCenter ε)) ∂paperMeasure) ≤
              ENNReal.ofReal
                ((C * (R ^ 2 + R ^ 4) * ε ^ 2 *
                    latticeEdgeWeight e e') * K)
          calc
            _ ≤ ENNReal.ofReal
                (K * (C * (R ^ 2 + R ^ 4) * ε ^ 2 *
                  latticeEdgeWeight e e')) := hstep
            _ = _ := by
              congr 1
              ring
  | cons y' ys ih =>
      intro right x z hx hz hnowrap hfar
      rcases hnowrap with ⟨hleft, hright, hpivot⟩
      rcases hleft with ⟨hEdgeEq, hleftTail⟩
      let K := latticeFarChainMajorant C ε R y' e ys right
      have hK : 0 ≤ K :=
        latticeFarChainMajorant_nonneg hC.le hR ε y' e ys right
      have htail :
          ∀ u ∈ latticeCellNeighborhood ε R y',
            twoSidedCellLIntegral (R * ε) u z
                (ys.map (latticeTorusCenter ε))
                (right.map (latticeTorusCenter ε)) ≤
              ENNReal.ofReal K := by
        intro u hu
        exact ih y' e right u z hu hz
          ⟨hleftTail, hright, by simpa using hpivot⟩
          (by simpa [LatticeTwoSidedPivotFar] using hfar)
      have hedge' :
          (∫ u in latticeCellNeighborhood ε R y',
              invSqKer (x - u) ∂paperMeasure) ≤
            C * (R ^ 2 + R ^ 4) * ε ^ 2 *
              latticeEdgeWeight y y' :=
        hedge ε R hε hR y y' x hEdgeEq hx
      have hstep :=
        lintegral_ofReal_mul_le_of_le_const
          ((integrable_invSqKer_sub_left x).integrableOn)
          (Filter.Eventually.of_forall fun u => invSqKer_nonneg _)
          hK hedge'
          (by
            filter_upwards
              [ae_restrict_mem
                (measurableSet_latticeCellNeighborhood ε R y')]
                with u hu
            exact htail u hu)
      rw [twoSidedCellLIntegral.eq_def,
        latticeFarChainMajorant.eq_def]
      change
        (∫⁻ u in latticeCellNeighborhood ε R y',
            ENNReal.ofReal (invSqKer (x - u)) *
              twoSidedCellLIntegral (R * ε) u z
                (ys.map (latticeTorusCenter ε))
                (right.map (latticeTorusCenter ε)) ∂paperMeasure) ≤
          ENNReal.ofReal
            ((C * (R ^ 2 + R ^ 4) * ε ^ 2 *
                latticeEdgeWeight y y') * K)
      calc
        _ ≤ ENNReal.ofReal
            (K * (C * (R ^ 2 + R ^ 4) * ε ^ 2 *
              latticeEdgeWeight y y')) := hstep
        _ = _ := by
          congr 1
          ring

/-- Closed-form version of the Tonelli-safe far estimate.  This is the
same recursive estimate as `twoSidedCellLIntegral_le_of_far`, with every
ordinary cell edge expanded and the powers collected. -/
theorem twoSidedCellLIntegral_le_of_far_closed :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y e : Z4) (left right : List Z4) (x z : T4),
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTwoSidedNoWrap ε y e left right →
        LatticeTwoSidedPivotFar R y e left right →
        twoSidedCellLIntegral (R * ε) x z
            (left.map (latticeTorusCenter ε))
            (right.map (latticeTorusCenter ε)) ≤
          ENNReal.ofReal
            ((C * (R ^ 2 + R ^ 4)) ^
                (left.length + right.length) *
              ε ^ (2 * (left.length + right.length)) *
              (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
              latticeTwoSidedPathWeight y e left right) := by
  obtain ⟨C, hC, hchain⟩ := twoSidedCellLIntegral_le_of_far
  refine ⟨C, hC, ?_⟩
  intro ε R hε hR y e left right x z hx hz hnowrap hfar
  have h := hchain ε R hε hR y e left right x z
    hx hz hnowrap hfar
  rw [latticeFarChainMajorant_eq_closed] at h
  exact h

/-- The far-pivot estimate in the original fixed-terminal order.  The
only reordering step is the unconditional Tonelli identity
`twoSidedCellLIntegral_eq_terminal`; no Bochner-integrability premise is
silently introduced. -/
theorem terminalCellLIntegral_le_of_far_decomposition :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y e : Z4) (ys left right : List Z4) (x z : T4),
        ys = left ++ right.reverse →
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTwoSidedNoWrap ε y e left right →
        LatticeTwoSidedPivotFar R y e left right →
        terminalCellLIntegral (R * ε) x z
            (ys.map (latticeTorusCenter ε)) ≤
          ENNReal.ofReal
            ((C * (R ^ 2 + R ^ 4)) ^
                (left.length + right.length) *
              ε ^ (2 * (left.length + right.length)) *
              (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
              latticeTwoSidedPathWeight y e left right) := by
  obtain ⟨C, hC, hchain⟩ :=
    twoSidedCellLIntegral_le_of_far_closed
  refine ⟨C, hC, ?_⟩
  intro ε R hε hR y e ys left right x z hdecomp
    hx hz hnowrap hfar
  have h := hchain ε R hε hR y e left right x z
    hx hz hnowrap hfar
  rw [twoSidedCellLIntegral_eq_terminal] at h
  subst ys
  simpa only [List.map_append, List.map_reverse] using h

/-- Paper-order form of the far-pivot estimate.  For the `2n-2`
integrated vertices in (5.3), the exposed scale is exactly
`ε^(4n-6)`. -/
theorem twoSidedLatticeCellChain_order_le_of_far :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (_hn : 2 ≤ n) (ε R : ℝ)
        (_hε : 0 < ε) (_hR : 0 < R)
        (y e : Z4) (left right : List Z4) (x z : T4),
        left.length + right.length = 2 * n - 2 →
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTwoSidedNoWrap ε y e left right →
        LatticeTwoSidedPivotFar R y e left right →
        twoSidedCellChain (R * ε) x z
            (left.map (latticeTorusCenter ε))
            (right.map (latticeTorusCenter ε)) ≤
          (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
            terminalRadiusFactor R * ε ^ (4 * n - 6) *
            latticeTwoSidedPathWeight y e left right := by
  obtain ⟨C, hC, hchain⟩ := twoSidedLatticeCellChain_le_of_far
  refine ⟨C, hC, ?_⟩
  intro n hn ε R hε hR y e left right x z hlen hx hz hnowrap hfar
  have hbase := hchain ε R hε hR y e left right x z
    hx hz hnowrap hfar
  have hk : 1 ≤ 2 * n - 2 := by omega
  have hp := pow_two_mul_mul_inv_sq
    (ne_of_gt hε) (2 * n - 2) hk
  rw [show 2 * (2 * n - 2) - 2 = 4 * n - 6 by omega] at hp
  calc
    twoSidedCellChain (R * ε) x z
        (left.map (latticeTorusCenter ε))
        (right.map (latticeTorusCenter ε))
        ≤ (C * (R ^ 2 + R ^ 4)) ^
            (left.length + right.length) *
          ε ^ (2 * (left.length + right.length)) *
          (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
          latticeTwoSidedPathWeight y e left right := hbase
    _ = (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R *
          (ε ^ (2 * (2 * n - 2)) * (ε ^ 2)⁻¹) *
          latticeTwoSidedPathWeight y e left right := by
          rw [hlen]
          ring
    _ = (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R * ε ^ (4 * n - 6) *
          latticeTwoSidedPathWeight y e left right := by rw [hp]

/-! ## The all-near local-triple branch -/

/-- Nonnegative Lebesgue-integral version of the local three-edge core.
This is the object to which Tonelli/Fubini is applied; in particular it
does not inherit the junk value of a non-integrable Bochner integral. -/
def localTripleCellLIntegral
    (r : ℝ) (c₁ c₂ x y : T4) : ℝ≥0∞ :=
  ∫⁻ z₁ in Metric.ball c₁ r,
    ∫⁻ z₂ in Metric.ball c₂ r,
      ENNReal.ofReal
        (invSqKer (x - z₁) * invSqKer (z₁ - z₂) *
          invSqKer (z₂ - y)) ∂paperMeasure ∂paperMeasure

private def localTripleProduct (x y : T4) (p : T4 × T4) : ℝ :=
  invSqKer (x - p.1) * invSqKer (p.1 - p.2) *
    invSqKer (p.2 - y)

private def localTripleThreeHalfMajorant
    (x y : T4) (p : T4 × T4) : ℝ :=
  invSqKerThreeHalf (x - p.1) *
      invSqKerThreeHalf (p.1 - p.2) +
    invSqKerThreeHalf (p.1 - p.2) *
      invSqKerThreeHalf (p.2 - y) +
    invSqKerThreeHalf (x - p.1) *
      invSqKerThreeHalf (p.2 - y)

private theorem integrable_threeHalf_leftPair (x : T4) :
    Integrable
      (fun p : T4 × T4 =>
        invSqKerThreeHalf (x - p.1) *
          invSqKerThreeHalf (p.1 - p.2))
      (paperMeasure.prod paperMeasure) := by
  have hmeas :
      AEStronglyMeasurable
        (fun p : T4 × T4 =>
          invSqKerThreeHalf (x - p.1) *
            invSqKerThreeHalf (p.1 - p.2))
        (paperMeasure.prod paperMeasure) :=
    ((measurable_invSqKerThreeHalf.comp
        (measurable_const.sub measurable_fst)).mul
      (measurable_invSqKerThreeHalf.comp
        (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · exact Filter.Eventually.of_forall fun z₁ =>
      (integrable_invSqKerThreeHalf_sub_left z₁).const_mul
        (invSqKerThreeHalf (x - z₁))
  · let M : ℝ := ∫ z, invSqKerThreeHalf z ∂paperMeasure
    have heq :
        (fun z₁ : T4 =>
          ∫ z₂,
            ‖invSqKerThreeHalf (x - z₁) *
              invSqKerThreeHalf (z₁ - z₂)‖ ∂paperMeasure) =
          fun z₁ => invSqKerThreeHalf (x - z₁) * M := by
      funext z₁
      rw [show
          (fun z₂ : T4 =>
            ‖invSqKerThreeHalf (x - z₁) *
              invSqKerThreeHalf (z₁ - z₂)‖) =
            fun z₂ =>
              invSqKerThreeHalf (x - z₁) *
                invSqKerThreeHalf (z₁ - z₂) by
          funext z₂
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact mul_nonneg
            (invSqKerThreeHalf_nonneg _)
            (invSqKerThreeHalf_nonneg _)]
      rw [integral_const_mul,
        integral_invSqKerThreeHalf_sub_left]
    rw [heq]
    exact
      (integrable_invSqKerThreeHalf_sub_left x).mul_const M

private theorem integrable_threeHalf_rightPair (y : T4) :
    Integrable
      (fun p : T4 × T4 =>
        invSqKerThreeHalf (p.1 - p.2) *
          invSqKerThreeHalf (p.2 - y))
      (paperMeasure.prod paperMeasure) := by
  have hmeas :
      AEStronglyMeasurable
        (fun p : T4 × T4 =>
          invSqKerThreeHalf (p.1 - p.2) *
            invSqKerThreeHalf (p.2 - y))
        (paperMeasure.prod paperMeasure) :=
    ((measurable_invSqKerThreeHalf.comp
        (measurable_fst.sub measurable_snd)).mul
      (measurable_invSqKerThreeHalf.comp
        (measurable_snd.sub measurable_const))).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  constructor
  · exact Filter.Eventually.of_forall fun z₂ =>
      (integrable_invSqKerThreeHalf_sub_right z₂).mul_const
        (invSqKerThreeHalf (z₂ - y))
  · let M : ℝ := ∫ z, invSqKerThreeHalf z ∂paperMeasure
    have heq :
        (fun z₂ : T4 =>
          ∫ z₁,
            ‖invSqKerThreeHalf (z₁ - z₂) *
              invSqKerThreeHalf (z₂ - y)‖ ∂paperMeasure) =
          fun z₂ => M * invSqKerThreeHalf (z₂ - y) := by
      funext z₂
      rw [show
          (fun z₁ : T4 =>
            ‖invSqKerThreeHalf (z₁ - z₂) *
              invSqKerThreeHalf (z₂ - y)‖) =
            fun z₁ =>
              invSqKerThreeHalf (z₁ - z₂) *
                invSqKerThreeHalf (z₂ - y) by
          funext z₁
          rw [Real.norm_eq_abs, abs_of_nonneg]
          exact mul_nonneg
            (invSqKerThreeHalf_nonneg _)
            (invSqKerThreeHalf_nonneg _)]
      rw [integral_mul_const,
        integral_invSqKerThreeHalf_sub_right]
    rw [heq]
    exact
      (integrable_invSqKerThreeHalf_sub_right y).const_mul M

private theorem integrable_localTripleThreeHalfMajorant
    (x y : T4) :
    Integrable (localTripleThreeHalfMajorant x y)
      (paperMeasure.prod paperMeasure) := by
  have hleft := integrable_threeHalf_leftPair x
  have hright := integrable_threeHalf_rightPair y
  have hseparated :
      Integrable
        (fun p : T4 × T4 =>
          invSqKerThreeHalf (x - p.1) *
            invSqKerThreeHalf (p.2 - y))
        (paperMeasure.prod paperMeasure) :=
    (integrable_invSqKerThreeHalf_sub_left x).mul_prod
      (integrable_invSqKerThreeHalf_sub_right y)
  exact (hleft.add hright).add hseparated

/-- The local triple product is genuinely integrable on the product
torus.  The proof uses the public `3/2`-power AM--GM majorant, so the
subsequent identification of Bochner and Lebesgue integrals is not a
junk-value inference. -/
theorem integrable_localTripleProduct (x y : T4) :
    Integrable (localTripleProduct x y)
      (paperMeasure.prod paperMeasure) := by
  have hmeas :
      AEStronglyMeasurable (localTripleProduct x y)
        (paperMeasure.prod paperMeasure) := by
    apply Measurable.aestronglyMeasurable
    exact
      ((measurable_invSqKer.comp
          (measurable_const.sub measurable_fst)).mul
        (measurable_invSqKer.comp
          (measurable_fst.sub measurable_snd))).mul
        (measurable_invSqKer.comp
          (measurable_snd.sub measurable_const))
  refine Integrable.mono'
    (integrable_localTripleThreeHalfMajorant x y) hmeas ?_
  exact Filter.Eventually.of_forall fun p => by
    dsimp only [localTripleProduct,
      localTripleThreeHalfMajorant]
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg
          (mul_nonneg (invSqKer_nonneg _) (invSqKer_nonneg _))
          (invSqKer_nonneg _))]
    exact invSqKer_triple_le_threeHalf_pairs
      (x - p.1) (p.1 - p.2) (p.2 - y)

/-- The Tonelli-safe local core is the `ofReal` of the paper's ordinary
iterated integral.  Product integrability is proved above before either
application of Fubini. -/
theorem localTripleCellLIntegral_eq_ofReal
    (r : ℝ) (c₁ c₂ x y : T4) :
    localTripleCellLIntegral r c₁ c₂ x y =
      ENNReal.ofReal (localTripleCellIntegral r c₁ c₂ x y) := by
  have hprod :
      Integrable (localTripleProduct x y)
        ((paperMeasure.restrict (Metric.ball c₁ r)).prod
          (paperMeasure.restrict (Metric.ball c₂ r))) :=
    (integrable_localTripleProduct x y).mono_measure
      (Measure.prod_mono Measure.restrict_le_self
        Measure.restrict_le_self)
  have hsections :
      ∀ᵐ z₁ ∂paperMeasure.restrict (Metric.ball c₁ r),
        Integrable
          (fun z₂ => localTripleProduct x y (z₁, z₂))
          (paperMeasure.restrict (Metric.ball c₂ r)) :=
    hprod.prod_right_ae
  have houter :
      Integrable
        (fun z₁ =>
          ∫ z₂ in Metric.ball c₂ r,
            localTripleProduct x y (z₁, z₂) ∂paperMeasure)
        (paperMeasure.restrict (Metric.ball c₁ r)) :=
    hprod.integral_prod_left
  have hinnerNonneg :
      ∀ z₁ : T4, 0 ≤
        ∫ z₂ in Metric.ball c₂ r,
          localTripleProduct x y (z₁, z₂) ∂paperMeasure :=
    fun z₁ => integral_nonneg fun z₂ =>
      mul_nonneg
        (mul_nonneg (invSqKer_nonneg _) (invSqKer_nonneg _))
        (invSqKer_nonneg _)
  unfold localTripleCellLIntegral localTripleCellIntegral
  change
    (∫⁻ z₁ in Metric.ball c₁ r,
      ∫⁻ z₂ in Metric.ball c₂ r,
        ENNReal.ofReal (localTripleProduct x y (z₁, z₂))
          ∂paperMeasure ∂paperMeasure) =
      ENNReal.ofReal
        (∫ z₁ in Metric.ball c₁ r,
          ∫ z₂ in Metric.ball c₂ r,
            localTripleProduct x y (z₁, z₂)
              ∂paperMeasure ∂paperMeasure)
  rw [ofReal_integral_eq_lintegral_ofReal houter
    (Filter.Eventually.of_forall hinnerNonneg)]
  apply lintegral_congr_ae
  filter_upwards [hsections] with z₁ hz₁
  rw [ofReal_integral_eq_lintegral_ofReal hz₁
    (Filter.Eventually.of_forall fun z₂ =>
      mul_nonneg
        (mul_nonneg (invSqKer_nonneg _) (invSqKer_nonneg _))
        (invSqKer_nonneg _))]

/-- Scale estimate for the Tonelli-safe local core. -/
theorem localTripleCellLIntegral_le_scale :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℝ), 0 < r →
      ∀ (c₀ c₁ c₂ c₃ x y : T4),
        x ∈ Metric.ball c₀ r →
        y ∈ Metric.ball c₃ r →
        dist c₀ c₁ ≤ 4 * r →
        dist c₁ c₂ ≤ 4 * r →
        dist c₂ c₃ ≤ 4 * r →
        localTripleCellLIntegral r c₁ c₂ x y ≤
          ENNReal.ofReal (C * r ^ 2) := by
  obtain ⟨C, hC, htriple⟩ := localTripleCellScaleBound
  refine ⟨C, hC, ?_⟩
  intro r hr c₀ c₁ c₂ c₃ x y hx hy h01 h12 h23
  rw [localTripleCellLIntegral_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal
    (htriple r hr c₀ c₁ c₂ c₃ x y hx hy h01 h12 h23)

/-- The two-vertex terminal chain is exactly the Tonelli-safe local
three-edge core. -/
theorem terminalCellLIntegral_pair_eq_localTriple
    (r : ℝ) (c₁ c₂ x y : T4) :
    terminalCellLIntegral r x y [c₁, c₂] =
      localTripleCellLIntegral r c₁ c₂ x y := by
  rw [terminalCellLIntegral.eq_def]
  unfold localTripleCellLIntegral
  apply lintegral_congr
  intro z₁
  rw [terminalCellLIntegral.eq_def]
  dsimp only
  change
    ENNReal.ofReal (invSqKer (x - z₁)) *
        (∫⁻ z₂ in Metric.ball c₂ r,
          ENNReal.ofReal (invSqKer (z₁ - z₂)) *
            ENNReal.ofReal (invSqKer (z₂ - y))
          ∂paperMeasure) =
      ∫⁻ z₂ in Metric.ball c₂ r,
        ENNReal.ofReal
          (invSqKer (x - z₁) * invSqKer (z₁ - z₂) *
            invSqKer (z₂ - y)) ∂paperMeasure
  have hmiddle :
      Measurable fun z₂ : T4 =>
        ENNReal.ofReal (invSqKer (z₁ - z₂)) *
          ENNReal.ofReal (invSqKer (z₂ - y)) :=
    ((measurable_invSqKer.comp
        (measurable_const.sub measurable_id)).ennreal_ofReal).mul
      ((measurable_invSqKer.comp
        (measurable_id.sub measurable_const)).ennreal_ofReal)
  calc
    ENNReal.ofReal (invSqKer (x - z₁)) *
        (∫⁻ z₂ in Metric.ball c₂ r,
          ENNReal.ofReal (invSqKer (z₁ - z₂)) *
            ENNReal.ofReal (invSqKer (z₂ - y))
          ∂paperMeasure)
        = ∫⁻ z₂ in Metric.ball c₂ r,
            ENNReal.ofReal (invSqKer (x - z₁)) *
              (ENNReal.ofReal (invSqKer (z₁ - z₂)) *
                ENNReal.ofReal (invSqKer (z₂ - y)))
            ∂paperMeasure :=
          (lintegral_const_mul''
            (ENNReal.ofReal (invSqKer (x - z₁)))
            hmiddle.aemeasurable).symm
    _ = ∫⁻ z₂ in Metric.ball c₂ r,
          ENNReal.ofReal
            (invSqKer (x - z₁) * invSqKer (z₁ - z₂) *
              invSqKer (z₂ - y)) ∂paperMeasure := by
        apply lintegral_congr
        intro z₂
        rw [ENNReal.ofReal_mul
          (mul_nonneg (invSqKer_nonneg (x - z₁))
            (invSqKer_nonneg (z₁ - z₂)))]
        rw [ENNReal.ofReal_mul (invSqKer_nonneg (x - z₁))]
        ring

/-! ### Lattice geometry for the all-near core -/

/-- Lattice product of all edges in a chain with a three-edge central
core. -/
def latticeTwoSidedTripleWeight (y a b e : Z4) :
    List Z4 → List Z4 → ℝ
  | [], [] =>
      latticeEdgeWeight y a * latticeEdgeWeight a b *
        latticeEdgeWeight b e
  | y' :: ys, right =>
      latticeEdgeWeight y y' *
        latticeTwoSidedTripleWeight y' a b e ys right
  | [], e' :: es =>
      latticeEdgeWeight e e' *
        latticeTwoSidedTripleWeight y a b e' [] es

theorem latticeTwoSidedTripleWeight_nonneg (y a b e : Z4) :
    ∀ (left right : List Z4),
      0 ≤ latticeTwoSidedTripleWeight y a b e left right := by
  intro left
  induction left generalizing y e with
  | nil =>
      intro right
      induction right generalizing e with
      | nil =>
          rw [latticeTwoSidedTripleWeight.eq_def]
          change 0 ≤ latticeEdgeWeight y a * latticeEdgeWeight a b *
            latticeEdgeWeight b e
          exact mul_nonneg
            (mul_nonneg (latticeEdgeWeight_nonneg_complete _ _)
              (latticeEdgeWeight_nonneg_complete _ _))
            (latticeEdgeWeight_nonneg_complete _ _)
      | cons e' es ih =>
          rw [latticeTwoSidedTripleWeight.eq_def]
          change 0 ≤ latticeEdgeWeight e e' *
            latticeTwoSidedTripleWeight y a b e' [] es
          exact mul_nonneg
            (latticeEdgeWeight_nonneg_complete e e') (ih e')
  | cons y' ys ih =>
      intro right
      rw [latticeTwoSidedTripleWeight.eq_def]
      change 0 ≤ latticeEdgeWeight y y' *
        latticeTwoSidedTripleWeight y' a b e ys right
      exact mul_nonneg (latticeEdgeWeight_nonneg_complete y y')
        (ih y' e right)

/-- One no-wrapping, `4R`-near lattice edge. -/
def LatticeNearEdge (ε R : ℝ) (y y' : Z4) : Prop :=
  dist (latticeTorusCenter ε y) (latticeTorusCenter ε y') =
      ε * znorm (y - y') ∧
    znorm (y - y') ≤ 4 * R

/-- Exact geometric data for an all-near central triple after the outer
edges have been stripped. -/
def LatticeTripleNear (ε R : ℝ) (y a b e : Z4) : Prop :=
  LatticeNearEdge ε R y a ∧
    LatticeNearEdge ε R a b ∧
      LatticeNearEdge ε R b e

/-- No-wrapping data on the outer paths and near data on the central
triple. -/
def LatticeTwoSidedTripleGeometry (ε R : ℝ)
    (y a b e : Z4) (left right : List Z4) : Prop :=
  LatticeCellPathNoWrap ε y left ∧
    LatticeCellPathNoWrap ε e right ∧
      LatticeTripleNear ε R
        (walkEnd y left) a b (walkEnd e right)

/-- **All-near core extraction.**  For at least two internal vertices,
the actual `latticePathAllNear` predicate and the actual no-wrap path
produce the exact `(prefix,a,b)` geometry consumed by the local-triple
estimate. -/
theorem latticePathAllNear_exists_tripleGeometry
    {ε R : ℝ} {y e : Z4} {ys : List Z4}
    (hlen : 2 ≤ ys.length)
    (hnear : latticePathAllNear R y e ys)
    (hnowrap : LatticeCellPathNoWrap ε y (ys ++ [e])) :
    ∃ (pre : List Z4) (a b : Z4),
      ys = pre ++ [a, b] ∧
        LatticeTwoSidedTripleGeometry ε R y a b e pre [] := by
  obtain ⟨pre, a, b, hdecomp⟩ :=
    exists_eq_append_pair_of_two_le_length hlen
  subst ys
  have hlast := latticePathAllNear_append_pair hnear
  have hnowrap' :
      LatticeCellPathNoWrap ε y (pre ++ [a, b, e]) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      hnowrap
  have hsplit :=
    (latticeCellPathNoWrap_append_iff ε y pre [a, b, e]).mp
      hnowrap'
  rcases hsplit with ⟨hprefix, htail⟩
  rw [LatticeCellPathNoWrap.eq_def] at htail
  dsimp only at htail
  rw [LatticeCellPathNoWrap.eq_def] at htail
  dsimp only at htail
  rw [LatticeCellPathNoWrap.eq_def] at htail
  dsimp only at htail
  refine ⟨pre, a, b, rfl, hprefix, trivial, ?_⟩
  exact ⟨⟨htail.1, hlast.1⟩,
    ⟨⟨htail.2.1, hlast.2.1⟩,
      ⟨by simpa only [walkEnd_nil] using htail.2.2.1,
        hlast.2.2⟩⟩⟩

/-- Radius factor which absorbs both an ordinary integrated edge and the
three near central lattice denominators. -/
def cellChainRadiusFactor (R : ℝ) : ℝ :=
  (R ^ 2 + R ^ 4) +
    R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 + 1

theorem cellChainRadiusFactor_pos (R : ℝ) :
    0 < cellChainRadiusFactor R := by
  unfold cellChainRadiusFactor
  positivity

private theorem one_le_nearFactor_mul_latticeEdgeWeight
    {R : ℝ} (hR : 0 < R) {y y' : Z4}
    (hnear : znorm (y - y') ≤ 4 * R) :
    1 ≤ (1 + (4 * R) ^ 2) * latticeEdgeWeight y y' := by
  have hD : 0 ≤ znorm (y - y') := znorm_nonneg _
  have h4R : 0 ≤ 4 * R := by positivity
  have hsquare :
      znorm (y - y') ^ 2 ≤ (4 * R) ^ 2 :=
    pow_le_pow_left₀ hD hnear 2
  have hden : 0 < 1 + znorm (y - y') ^ 2 := by positivity
  unfold latticeEdgeWeight
  rw [show (1 + (4 * R) ^ 2) *
      (1 + znorm (y - y') ^ 2)⁻¹ =
      (1 + (4 * R) ^ 2) /
        (1 + znorm (y - y') ^ 2) by rw [div_eq_mul_inv]]
  exact (le_div_iff₀ hden).mpr (by linarith)

private theorem one_le_nearTripleFactor_mul_weight
    {R : ℝ} (hR : 0 < R) {y a b e : Z4}
    (hya : znorm (y - a) ≤ 4 * R)
    (hab : znorm (a - b) ≤ 4 * R)
    (hbe : znorm (b - e) ≤ 4 * R) :
    1 ≤ (1 + (4 * R) ^ 2) ^ 3 *
      (latticeEdgeWeight y a * latticeEdgeWeight a b *
        latticeEdgeWeight b e) := by
  have h₁ := one_le_nearFactor_mul_latticeEdgeWeight hR hya
  have h₂ := one_le_nearFactor_mul_latticeEdgeWeight hR hab
  have h₃ := one_le_nearFactor_mul_latticeEdgeWeight hR hbe
  have hnonneg₁ :
      0 ≤ (1 + (4 * R) ^ 2) * latticeEdgeWeight y a := by
    positivity
  have hnonneg₂ :
      0 ≤ (1 + (4 * R) ^ 2) * latticeEdgeWeight a b := by
    positivity
  calc
    (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ ((1 + (4 * R) ^ 2) * latticeEdgeWeight y a) *
        ((1 + (4 * R) ^ 2) * latticeEdgeWeight a b) *
        ((1 + (4 * R) ^ 2) * latticeEdgeWeight b e) := by
          exact mul_le_mul
            (mul_le_mul h₁ h₂ zero_le_one hnonneg₁)
            h₃ zero_le_one (mul_nonneg hnonneg₁ hnonneg₂)
    _ = (1 + (4 * R) ^ 2) ^ 3 *
        (latticeEdgeWeight y a * latticeEdgeWeight a b *
          latticeEdgeWeight b e) := by ring

/-- Recursive majorant for a one-sided all-near chain.  Its base is the
three-edge local core and every recursive layer is one ordinary cell
edge. -/
def latticeNearChainMajorant
    (C ε R : ℝ) (y a b e : Z4) : List Z4 → ℝ
  | [] =>
      (C * cellChainRadiusFactor R) * ε ^ 2 *
        (latticeEdgeWeight y a * latticeEdgeWeight a b *
          latticeEdgeWeight b e)
  | y' :: ys =>
      (C * cellChainRadiusFactor R * ε ^ 2 *
          latticeEdgeWeight y y') *
        latticeNearChainMajorant C ε R y' a b e ys

theorem latticeNearChainMajorant_nonneg
    {C : ℝ} (hC : 0 ≤ C) (ε R : ℝ)
    (y a b e : Z4) (left : List Z4) :
    0 ≤ latticeNearChainMajorant C ε R y a b e left := by
  induction left generalizing y with
  | nil =>
      rw [latticeNearChainMajorant.eq_def]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hC (cellChainRadiusFactor_pos R).le)
          (sq_nonneg ε))
        (mul_nonneg
          (mul_nonneg
            (latticeEdgeWeight_nonneg_complete y a)
            (latticeEdgeWeight_nonneg_complete a b))
          (latticeEdgeWeight_nonneg_complete b e))
  | cons y' ys ih =>
      rw [latticeNearChainMajorant.eq_def]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hC (cellChainRadiusFactor_pos R).le)
            (sq_nonneg ε))
          (latticeEdgeWeight_nonneg_complete y y'))
        (ih y')

theorem latticeNearChainMajorant_eq_closed
    (C ε R : ℝ) (y a b e : Z4) (left : List Z4) :
    latticeNearChainMajorant C ε R y a b e left =
      (C * cellChainRadiusFactor R) ^ (left.length + 1) *
        ε ^ (2 * left.length + 2) *
        latticeTwoSidedTripleWeight y a b e left [] := by
  induction left generalizing y with
  | nil =>
      rw [latticeNearChainMajorant.eq_def,
        latticeTwoSidedTripleWeight.eq_def]
      simp
  | cons y' ys ih =>
      rw [latticeNearChainMajorant.eq_def]
      dsimp only
      rw [ih y']
      rw [show
        latticeTwoSidedTripleWeight y a b e (y' :: ys) [] =
          latticeEdgeWeight y y' *
            latticeTwoSidedTripleWeight y' a b e ys [] by
        rw [latticeTwoSidedTripleWeight.eq_def]]
      simp only [List.length_cons]
      rw [show ys.length + 1 + 1 =
        (ys.length + 1) + 1 by omega, pow_succ]
      rw [show 2 * (ys.length + 1) + 2 =
        (2 * ys.length + 2) + 2 by omega, pow_add]
      ring

theorem latticeEdgeWeight_comm (y e : Z4) :
    latticeEdgeWeight y e = latticeEdgeWeight e y := by
  unfold latticeEdgeWeight
  rw [znorm_sub_comm]

theorem latticeTerminalPathWeight_append_singleton
    (y e c : Z4) (ys : List Z4) :
    latticeTerminalPathWeight y e (ys ++ [c]) =
      latticeTerminalPathWeight y c ys *
        latticeEdgeWeight c e := by
  induction ys generalizing y with
  | nil =>
      rw [List.nil_append]
      simp only [latticeTerminalPathWeight]
  | cons y' ys ih =>
      rw [List.cons_append]
      simp only [latticeTerminalPathWeight]
      rw [ih y']
      ring

/-- The pivot-ordered lattice product is the product along the original
linear path. -/
theorem latticeTwoSidedPathWeight_eq_terminal
    (y e : Z4) (left right : List Z4) :
    latticeTwoSidedPathWeight y e left right =
      latticeTerminalPathWeight y e
        (left ++ right.reverse) := by
  induction left generalizing y e with
  | nil =>
      induction right generalizing e with
      | nil =>
          rw [latticeTwoSidedPathWeight.eq_def]
          simp only [List.reverse_nil, List.nil_append,
            latticeTerminalPathWeight]
      | cons e' es ih =>
          rw [latticeTwoSidedPathWeight.eq_def]
          dsimp only
          rw [ih e']
          rw [List.reverse_cons]
          simp only [List.nil_append]
          rw [latticeTerminalPathWeight_append_singleton]
          rw [latticeEdgeWeight_comm e e']
          ring
  | cons y' ys ih =>
      rw [latticeTwoSidedPathWeight.eq_def]
      dsimp only
      rw [ih y' e]
      simp only [List.cons_append, latticeTerminalPathWeight]

/-- The three-edge-core lattice product is likewise the product along
the original one-sided path. -/
theorem latticeTwoSidedTripleWeight_eq_terminal
    (y a b e : Z4) (left : List Z4) :
    latticeTwoSidedTripleWeight y a b e left [] =
      latticeTerminalPathWeight y e (left ++ [a, b]) := by
  induction left generalizing y with
  | nil =>
      rw [latticeTwoSidedTripleWeight.eq_def]
      simp only [List.nil_append, latticeTerminalPathWeight]
      ring
  | cons y' ys ih =>
      rw [latticeTwoSidedTripleWeight.eq_def]
      dsimp only
      rw [ih y']
      simp only [List.cons_append, latticeTerminalPathWeight]

/-- Tonelli-safe all-near estimate in the original terminal-chain order.
The actual triple geometry, including the no-wrap prefix, is consumed
recursively. -/
theorem terminalCellLIntegral_le_of_nearCore :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y a b e : Z4) (left : List Z4) (x z : T4),
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTwoSidedTripleGeometry ε R y a b e left [] →
        terminalCellLIntegral (R * ε) x z
            ((left ++ [a, b]).map (latticeTorusCenter ε)) ≤
          ENNReal.ofReal
            (latticeNearChainMajorant C ε R y a b e left) := by
  obtain ⟨Ce, hCe, hedge⟩ := invSqKer_latticeCellEdge_le
  obtain ⟨Ct, hCt, htriple⟩ :=
    localTripleCellLIntegral_le_scale
  let C : ℝ := Ce + Ct + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hCeC : Ce ≤ C := by
    dsimp [C]
    linarith [hCt]
  have hCtC : Ct ≤ C := by
    dsimp [C]
    linarith [hCe]
  refine ⟨C, hC, ?_⟩
  intro ε R hε hR y a b e left
  induction left generalizing y with
  | nil =>
      intro x z hx hz hgeom
      rcases hgeom with ⟨_, _, hya, hab, hbe⟩
      simp only [walkEnd_nil] at hya hbe
      have hr : 0 < R * ε := mul_pos hR hε
      have hlocal := htriple (R * ε) hr
        (latticeTorusCenter ε y)
        (latticeTorusCenter ε a)
        (latticeTorusCenter ε b)
        (latticeTorusCenter ε e) x z
        (by simpa only [latticeCellNeighborhood] using hx)
        (by simpa only [latticeCellNeighborhood] using hz)
        (by
          rw [hya.1]
          nlinarith [mul_le_mul_of_nonneg_left hya.2 hε.le])
        (by
          rw [hab.1]
          nlinarith [mul_le_mul_of_nonneg_left hab.2 hε.le])
        (by
          rw [hbe.1]
          nlinarith [mul_le_mul_of_nonneg_left hbe.2 hε.le])
      have hweight :=
        one_le_nearTripleFactor_mul_weight hR
          hya.2 hab.2 hbe.2
      have hbaseFactor :
          Ct * R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 ≤
            C * cellChainRadiusFactor R := by
        have hRF :
            R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 ≤
              cellChainRadiusFactor R := by
          unfold cellChainRadiusFactor
          have hA : 0 ≤ R ^ 2 + R ^ 4 := by positivity
          linarith
        calc
          Ct * R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 ≤
              C * (R ^ 2 * (1 + (4 * R) ^ 2) ^ 3) := by
            have hfac :
                0 ≤ R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 :=
              mul_nonneg (sq_nonneg R)
                (pow_nonneg (by positivity) 3)
            simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_right hCtC hfac
          _ ≤ C * cellChainRadiusFactor R :=
            mul_le_mul_of_nonneg_left hRF hC.le
      have hscaled :
          Ct * (R * ε) ^ 2 ≤
            latticeNearChainMajorant C ε R y a b e [] := by
        rw [latticeNearChainMajorant.eq_def]
        calc
          Ct * (R * ε) ^ 2 =
              (Ct * R ^ 2) * ε ^ 2 := by ring
          _ = (Ct * R ^ 2) * 1 * ε ^ 2 := by ring
          _ ≤ (Ct * R ^ 2) *
                ((1 + (4 * R) ^ 2) ^ 3 *
                  (latticeEdgeWeight y a *
                    latticeEdgeWeight a b *
                    latticeEdgeWeight b e)) * ε ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hweight
                (mul_nonneg hCt.le (sq_nonneg R)))
              (sq_nonneg ε)
          _ = (Ct * R ^ 2 * (1 + (4 * R) ^ 2) ^ 3) *
                ε ^ 2 *
                (latticeEdgeWeight y a *
                  latticeEdgeWeight a b *
                  latticeEdgeWeight b e) := by ring
          _ ≤ (C * cellChainRadiusFactor R) * ε ^ 2 *
                (latticeEdgeWeight y a *
                  latticeEdgeWeight a b *
                  latticeEdgeWeight b e) := by
            have hW :
                0 ≤ latticeEdgeWeight y a *
                  latticeEdgeWeight a b *
                  latticeEdgeWeight b e :=
              mul_nonneg
                (mul_nonneg
                  (latticeEdgeWeight_nonneg_complete y a)
                  (latticeEdgeWeight_nonneg_complete a b))
                (latticeEdgeWeight_nonneg_complete b e)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hbaseFactor
                (sq_nonneg ε)) hW
      rw [show (([] : List Z4) ++ [a, b]).map
          (latticeTorusCenter ε) =
        [latticeTorusCenter ε a, latticeTorusCenter ε b] by simp]
      rw [terminalCellLIntegral_pair_eq_localTriple]
      exact hlocal.trans (ENNReal.ofReal_le_ofReal hscaled)
  | cons y' ys ih =>
      intro x z hx hz hgeom
      rcases hgeom with ⟨hleft, _, hcore⟩
      rcases hleft with ⟨hEdgeEq, hleftTail⟩
      let K := latticeNearChainMajorant C ε R y' a b e ys
      have hK : 0 ≤ K :=
        latticeNearChainMajorant_nonneg hC.le ε R y' a b e ys
      have htail :
          ∀ u ∈ latticeCellNeighborhood ε R y',
            terminalCellLIntegral (R * ε) u z
                ((ys ++ [a, b]).map
                  (latticeTorusCenter ε)) ≤
              ENNReal.ofReal K := by
        intro u hu
        exact ih y' u z hu hz
          ⟨hleftTail, trivial, by simpa using hcore⟩
      have hedge' :
          (∫ u in latticeCellNeighborhood ε R y',
              invSqKer (x - u) ∂paperMeasure) ≤
            C * cellChainRadiusFactor R * ε ^ 2 *
              latticeEdgeWeight y y' := by
        have hraw := hedge ε R hε hR y y' x hEdgeEq hx
        have hAF :
            R ^ 2 + R ^ 4 ≤ cellChainRadiusFactor R := by
          unfold cellChainRadiusFactor
          have hB :
              0 ≤ R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 := by
            positivity
          linarith
        calc
          (∫ u in latticeCellNeighborhood ε R y',
              invSqKer (x - u) ∂paperMeasure)
              ≤ Ce * (R ^ 2 + R ^ 4) * ε ^ 2 *
                latticeEdgeWeight y y' := hraw
          _ ≤ C * cellChainRadiusFactor R * ε ^ 2 *
                latticeEdgeWeight y y' := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul hCeC hAF (by positivity) hC.le)
                (sq_nonneg ε))
              (latticeEdgeWeight_nonneg_complete y y')
      have hstep :=
        lintegral_ofReal_mul_le_of_le_const
          ((integrable_invSqKer_sub_left x).integrableOn)
          (Filter.Eventually.of_forall fun u => invSqKer_nonneg _)
          hK hedge'
          (by
            filter_upwards
              [ae_restrict_mem
                (measurableSet_latticeCellNeighborhood ε R y')]
                with u hu
            exact htail u hu)
      rw [List.cons_append, List.map_cons,
        terminalCellLIntegral.eq_def,
        latticeNearChainMajorant.eq_def]
      change
        (∫⁻ u in latticeCellNeighborhood ε R y',
          ENNReal.ofReal (invSqKer (x - u)) *
            terminalCellLIntegral (R * ε) u z
              ((ys ++ [a, b]).map
                (latticeTorusCenter ε)) ∂paperMeasure) ≤
          ENNReal.ofReal
            ((C * cellChainRadiusFactor R * ε ^ 2 *
                latticeEdgeWeight y y') * K)
      calc
        _ ≤ ENNReal.ofReal
            (K * (C * cellChainRadiusFactor R * ε ^ 2 *
              latticeEdgeWeight y y')) := hstep
        _ = _ := by
          congr 1
          ring

/-- Closed paper-style form of the Tonelli-safe all-near estimate. -/
theorem terminalCellLIntegral_le_of_nearCore_closed :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y a b e : Z4) (left : List Z4) (x z : T4),
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTwoSidedTripleGeometry ε R y a b e left [] →
        terminalCellLIntegral (R * ε) x z
            ((left ++ [a, b]).map (latticeTorusCenter ε)) ≤
          ENNReal.ofReal
            ((C * cellChainRadiusFactor R) ^ (left.length + 1) *
              ε ^ (2 * left.length + 2) *
              latticeTwoSidedTripleWeight y a b e left []) := by
  obtain ⟨C, hC, hchain⟩ :=
    terminalCellLIntegral_le_of_nearCore
  refine ⟨C, hC, ?_⟩
  intro ε R hε hR y a b e left x z hx hz hgeom
  have h := hchain ε R hε hR y a b e left x z
    hx hz hgeom
  rw [latticeNearChainMajorant_eq_closed] at h
  exact h

/-- A single per-cell majorant containing both exhaustive alternatives.
The first summand is the far-pivot estimate and the second is the
all-near local-triple estimate.  For paths of length at least two both
summands have the paper scale `ε^(2k-2)` after cancellation in the first
summand. -/
def exhaustiveCellChainMajorant
    (C ε R : ℝ) (k : ℕ) (weight : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
      ((C * (R ^ 2 + R ^ 4)) ^ k *
        ε ^ (2 * k) *
        (terminalRadiusFactor R * (ε ^ 2)⁻¹) * weight) +
    ENNReal.ofReal
      ((C * cellChainRadiusFactor R) ^ (k - 1) *
        ε ^ (2 * k - 2) * weight)

/-- **Exhaustive Tonelli-safe per-cell chain estimate.**

For one actual no-wrap cell path with at least two integrated vertices,
this theorem itself performs the `all-near`/`has-far-edge` split.  The
near branch extracts the concrete `(pre,a,b)` core from
`latticePathAllNear`; the far branch extracts a two-sided pivot together
with its no-wrap geometry.  Both branches bound the same original
`terminalCellLIntegral` and the same original linear lattice weight. -/
theorem terminalCellLIntegral_exhaustive_perCell :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y e : Z4) (ys : List Z4) (x z : T4),
        2 ≤ ys.length →
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeCellPathNoWrap ε y (ys ++ [e]) →
        terminalCellLIntegral (R * ε) x z
            (ys.map (latticeTorusCenter ε)) ≤
          exhaustiveCellChainMajorant C ε R ys.length
            (latticeTerminalPathWeight y e ys) := by
  obtain ⟨Cf, hCf, hfarChain⟩ :=
    terminalCellLIntegral_le_of_far_decomposition
  obtain ⟨Cn, hCn, hnearChain⟩ :=
    terminalCellLIntegral_le_of_nearCore_closed
  let C : ℝ := Cf + Cn + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hCfC : Cf ≤ C := by
    dsimp [C]
    linarith [hCn]
  have hCnC : Cn ≤ C := by
    dsimp [C]
    linarith [hCf]
  refine ⟨C, hC, ?_⟩
  intro ε R hε hR y e ys x z hlen hx hz hnowrap
  rcases latticePath_allNear_or_exists_twoSidedGeometry
      ε R y e ys hnowrap with hnear | hfar
  · obtain ⟨pre, a, b, hdecomp, hgeom⟩ :=
      latticePathAllNear_exists_tripleGeometry
        hlen hnear hnowrap
    have hbound :=
      hnearChain ε R hε hR y a b e pre x z hx hz hgeom
    rw [latticeTwoSidedTripleWeight_eq_terminal] at hbound
    have hbase :
        Cn * cellChainRadiusFactor R ≤
          C * cellChainRadiusFactor R :=
      mul_le_mul_of_nonneg_right hCnC
        (cellChainRadiusFactor_pos R).le
    have hbaseNonneg :
        0 ≤ Cn * cellChainRadiusFactor R :=
      mul_nonneg hCn.le (cellChainRadiusFactor_pos R).le
    have hpow :
        (Cn * cellChainRadiusFactor R) ^ (pre.length + 1) ≤
          (C * cellChainRadiusFactor R) ^ (pre.length + 1) :=
      pow_le_pow_left₀ hbaseNonneg hbase _
    have hreal :
        (Cn * cellChainRadiusFactor R) ^ (pre.length + 1) *
            ε ^ (2 * pre.length + 2) *
            latticeTerminalPathWeight y e (pre ++ [a, b]) ≤
          (C * cellChainRadiusFactor R) ^ (pre.length + 1) *
            ε ^ (2 * pre.length + 2) *
            latticeTerminalPathWeight y e (pre ++ [a, b]) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow
          (pow_nonneg hε.le _))
        (latticeTerminalPathWeight_nonneg y e _)
    subst ys
    have hk :
        (pre ++ [a, b]).length - 1 = pre.length + 1 := by
      simp
    have hεexp :
        2 * (pre ++ [a, b]).length - 2 =
          2 * pre.length + 2 := by
      simp
      omega
    unfold exhaustiveCellChainMajorant
    rw [hk, hεexp]
    calc
      terminalCellLIntegral (R * ε) x z
          ((pre ++ [a, b]).map (latticeTorusCenter ε))
          ≤ ENNReal.ofReal
              ((Cn * cellChainRadiusFactor R) ^
                  (pre.length + 1) *
                ε ^ (2 * pre.length + 2) *
                latticeTerminalPathWeight y e
                  (pre ++ [a, b])) := hbound
      _ ≤ ENNReal.ofReal
              ((C * cellChainRadiusFactor R) ^
                  (pre.length + 1) *
                ε ^ (2 * pre.length + 2) *
                latticeTerminalPathWeight y e
                  (pre ++ [a, b])) :=
            ENNReal.ofReal_le_ofReal hreal
      _ ≤
          ENNReal.ofReal
              ((C * (R ^ 2 + R ^ 4)) ^
                  (pre ++ [a, b]).length *
                ε ^ (2 * (pre ++ [a, b]).length) *
                (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
                latticeTerminalPathWeight y e (pre ++ [a, b])) +
            ENNReal.ofReal
              ((C * cellChainRadiusFactor R) ^
                  (pre.length + 1) *
                ε ^ (2 * pre.length + 2) *
                latticeTerminalPathWeight y e
                  (pre ++ [a, b])) :=
            le_add_left le_rfl
  · obtain ⟨left, right, hdecomp, hgeom, hpivot⟩ := hfar
    have hbound :=
      hfarChain ε R hε hR y e ys left right x z
        hdecomp hx hz hgeom hpivot
    rw [latticeTwoSidedPathWeight_eq_terminal] at hbound
    rw [← hdecomp] at hbound
    have hdecompLength :
        left.length + right.length = ys.length := by
      rw [hdecomp, List.length_append, List.length_reverse]
    rw [hdecompLength] at hbound
    have hA : 0 ≤ R ^ 2 + R ^ 4 :=
      add_nonneg (sq_nonneg R) (by positivity)
    have hbase :
        Cf * (R ^ 2 + R ^ 4) ≤
          C * (R ^ 2 + R ^ 4) :=
      mul_le_mul_of_nonneg_right hCfC hA
    have hbaseNonneg :
        0 ≤ Cf * (R ^ 2 + R ^ 4) :=
      mul_nonneg hCf.le hA
    have hpow :
        (Cf * (R ^ 2 + R ^ 4)) ^ ys.length ≤
          (C * (R ^ 2 + R ^ 4)) ^ ys.length :=
      pow_le_pow_left₀ hbaseNonneg hbase _
    have hεpow : 0 ≤ ε ^ (2 * ys.length) :=
      pow_nonneg hε.le _
    have hterminal :
        0 ≤ terminalRadiusFactor R * (ε ^ 2)⁻¹ :=
      mul_nonneg (terminalRadiusFactor_pos hR).le
        (inv_nonneg.mpr (sq_nonneg ε))
    have hweight :
        0 ≤ latticeTerminalPathWeight y e ys :=
      latticeTerminalPathWeight_nonneg y e ys
    have hreal :
        (Cf * (R ^ 2 + R ^ 4)) ^ ys.length *
              ε ^ (2 * ys.length) *
              (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
              latticeTerminalPathWeight y e ys ≤
          (C * (R ^ 2 + R ^ 4)) ^ ys.length *
              ε ^ (2 * ys.length) *
              (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
              latticeTerminalPathWeight y e ys := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpow hεpow)
          hterminal)
        hweight
    unfold exhaustiveCellChainMajorant
    calc
      terminalCellLIntegral (R * ε) x z
          (ys.map (latticeTorusCenter ε))
          ≤ ENNReal.ofReal
              ((Cf * (R ^ 2 + R ^ 4)) ^ ys.length *
                ε ^ (2 * ys.length) *
                (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
                latticeTerminalPathWeight y e ys) := hbound
      _ ≤ ENNReal.ofReal
              ((C * (R ^ 2 + R ^ 4)) ^ ys.length *
                ε ^ (2 * ys.length) *
                (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
                latticeTerminalPathWeight y e ys) :=
            ENNReal.ofReal_le_ofReal hreal
      _ ≤
          ENNReal.ofReal
              ((C * (R ^ 2 + R ^ 4)) ^ ys.length *
                ε ^ (2 * ys.length) *
                (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
                latticeTerminalPathWeight y e ys) +
            ENNReal.ofReal
              ((C * cellChainRadiusFactor R) ^ (ys.length - 1) *
                ε ^ (2 * ys.length - 2) *
                latticeTerminalPathWeight y e ys) :=
            le_add_right le_rfl

/-- Cancellation of the terminal `ε⁻²` factor in the exhaustive
majorant. -/
theorem exhaustiveCellChainMajorant_eq_paperScale
    {ε : ℝ} (hε : ε ≠ 0) (C R weight : ℝ)
    (k : ℕ) (hk : 1 ≤ k) :
    exhaustiveCellChainMajorant C ε R k weight =
      ENNReal.ofReal
          ((C * (R ^ 2 + R ^ 4)) ^ k *
            terminalRadiusFactor R *
            ε ^ (2 * k - 2) * weight) +
        ENNReal.ofReal
          ((C * cellChainRadiusFactor R) ^ (k - 1) *
            ε ^ (2 * k - 2) * weight) := by
  have hp := pow_two_mul_mul_inv_sq hε k hk
  unfold exhaustiveCellChainMajorant
  rw [show
      (C * (R ^ 2 + R ^ 4)) ^ k *
            ε ^ (2 * k) *
            (terminalRadiusFactor R * (ε ^ 2)⁻¹) * weight =
        (C * (R ^ 2 + R ^ 4)) ^ k *
            terminalRadiusFactor R *
            ε ^ (2 * k - 2) * weight by
      calc
        (C * (R ^ 2 + R ^ 4)) ^ k *
              ε ^ (2 * k) *
              (terminalRadiusFactor R * (ε ^ 2)⁻¹) * weight =
            (C * (R ^ 2 + R ^ 4)) ^ k *
              terminalRadiusFactor R *
              (ε ^ (2 * k) * (ε ^ 2)⁻¹) * weight := by
                ring
        _ = (C * (R ^ 2 + R ^ 4)) ^ k *
              terminalRadiusFactor R *
              ε ^ (2 * k - 2) * weight := by rw [hp]]

/-- Paper-order specialization of the exhaustive per-cell estimate.
For `2n-2` integrated vertices, both exhaustive summands expose exactly
`ε^(4n-6)`. -/
theorem terminalCellLIntegral_exhaustive_order :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (_hn : 2 ≤ n) (ε R : ℝ)
        (_hε : 0 < ε) (_hR : 0 < R)
        (y e : Z4) (ys : List Z4) (x z : T4),
        ys.length = 2 * n - 2 →
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeCellPathNoWrap ε y (ys ++ [e]) →
        terminalCellLIntegral (R * ε) x z
            (ys.map (latticeTorusCenter ε)) ≤
          ENNReal.ofReal
              ((C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
                terminalRadiusFactor R *
                ε ^ (4 * n - 6) *
                latticeTerminalPathWeight y e ys) +
            ENNReal.ofReal
              ((C * cellChainRadiusFactor R) ^ (2 * n - 3) *
                ε ^ (4 * n - 6) *
                latticeTerminalPathWeight y e ys) := by
  obtain ⟨C, hC, hchain⟩ :=
    terminalCellLIntegral_exhaustive_perCell
  refine ⟨C, hC, ?_⟩
  intro n hn ε R hε hR y e ys x z hlen hx hz hnowrap
  have hlength : 2 ≤ ys.length := by
    rw [hlen]
    omega
  have h := hchain ε R hε hR y e ys x z
    hlength hx hz hnowrap
  rw [exhaustiveCellChainMajorant_eq_paperScale
    (ne_of_gt hε) C R (latticeTerminalPathWeight y e ys)
    ys.length (by omega)] at h
  have hk :
      (2 * n - 2) - 1 = 2 * n - 3 := by omega
  have hεexp :
      2 * (2 * n - 2) - 2 = 4 * n - 6 := by omega
  rw [hlen, hk, hεexp] at h
  exact h

/-- Chain obtained after selecting the two central integrated vertices
`a,b`; all other integrated vertices are ordered outwards towards the two
fixed endpoints. -/
def twoSidedTripleCellChain (r : ℝ) (a b x z : T4) :
    List T4 → List T4 → ℝ
  | [], [] => localTripleCellIntegral r a b x z
  | c :: cs, right =>
      ∫ u in Metric.ball c r,
        invSqKer (x - u) *
          twoSidedTripleCellChain r a b u z cs right
          ∂paperMeasure
  | [], c :: cs =>
      ∫ u in Metric.ball c r,
        invSqKer (z - u) *
          twoSidedTripleCellChain r a b x u [] cs
          ∂paperMeasure

theorem twoSidedTripleCellChain_nonneg (r : ℝ) (a b : T4) :
    ∀ (x z : T4) (left right : List T4),
      0 ≤ twoSidedTripleCellChain r a b x z left right := by
  intro x z left
  induction left generalizing x z with
  | nil =>
      intro right
      induction right generalizing z with
      | nil =>
          rw [twoSidedTripleCellChain.eq_def]
          unfold localTripleCellIntegral
          exact integral_nonneg fun u =>
            integral_nonneg fun v =>
              mul_nonneg
                (mul_nonneg (invSqKer_nonneg _) (invSqKer_nonneg _))
                (invSqKer_nonneg _)
      | cons c cs ih =>
          rw [twoSidedTripleCellChain.eq_def]
          exact integral_nonneg fun u =>
            mul_nonneg (invSqKer_nonneg _) (ih u)
  | cons c cs ih =>
      intro right
      rw [twoSidedTripleCellChain.eq_def]
      exact integral_nonneg fun u =>
        mul_nonneg (invSqKer_nonneg _) (ih u z right)

/-- In the one-sided orientation the local-triple construction is exactly
the ordinary terminal chain with the two central vertices appended. -/
theorem twoSidedTripleCellChain_right_nil
    (r : ℝ) (a b x z : T4) (left : List T4) :
    twoSidedTripleCellChain r a b x z left [] =
      terminalCellChain r x z (left ++ [a, b]) := by
  induction left generalizing x with
  | nil =>
      simp only [twoSidedTripleCellChain.eq_def, List.nil_append,
        terminalCellChain.eq_def]
      unfold localTripleCellIntegral
      apply integral_congr_ae
      filter_upwards with u
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      ring
  | cons c cs ih =>
      rw [twoSidedTripleCellChain.eq_def, terminalCellChain.eq_def,
        List.cons_append]
      apply integral_congr_ae
      filter_upwards with u
      rw [ih u]

/-- Complete all-near branch of (5.4), with the local triple theorem
consumed at the base and every outer cell integrated explicitly. -/
theorem twoSidedTripleLatticeCellChain_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y a b e : Z4) (left right : List Z4) (x z : T4),
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTwoSidedTripleGeometry ε R y a b e left right →
        twoSidedTripleCellChain (R * ε)
            (latticeTorusCenter ε a) (latticeTorusCenter ε b) x z
            (left.map (latticeTorusCenter ε))
            (right.map (latticeTorusCenter ε)) ≤
          (C * cellChainRadiusFactor R) ^
              (left.length + right.length + 1) *
            ε ^ (2 * (left.length + right.length) + 2) *
            latticeTwoSidedTripleWeight y a b e left right := by
  obtain ⟨Ce, hCe, hedge⟩ := invSqKer_latticeCellEdge_le
  obtain ⟨Ct, hCt, htriple⟩ := localTripleCellScaleBound
  let C : ℝ := Ce + Ct + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hCeC : Ce ≤ C := by
    dsimp [C]
    linarith [hCt]
  have hCtC : Ct ≤ C := by
    dsimp [C]
    linarith [hCe]
  refine ⟨C, hC, ?_⟩
  intro ε R hε hR y a b e left
  induction left generalizing y e with
  | nil =>
      intro right
      induction right generalizing e with
      | nil =>
          intro x z hx hz hgeom
          rcases hgeom with ⟨_, _, hya, hab, hbe⟩
          simp only [walkEnd_nil] at hya hbe
          have hr : 0 < R * ε := mul_pos hR hε
          have hlocal := htriple (R * ε) hr
            (latticeTorusCenter ε y)
            (latticeTorusCenter ε a)
            (latticeTorusCenter ε b)
            (latticeTorusCenter ε e) x z
            (by simpa only [latticeCellNeighborhood] using hx)
            (by simpa only [latticeCellNeighborhood] using hz)
            (by
              rw [hya.1]
              nlinarith [mul_le_mul_of_nonneg_left hya.2 hε.le])
            (by
              rw [hab.1]
              nlinarith [mul_le_mul_of_nonneg_left hab.2 hε.le])
            (by
              rw [hbe.1]
              nlinarith [mul_le_mul_of_nonneg_left hbe.2 hε.le])
          have hweight :=
            one_le_nearTripleFactor_mul_weight hR
              hya.2 hab.2 hbe.2
          have hbaseFactor :
              Ct * R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 ≤
                C * cellChainRadiusFactor R := by
            have hRF :
                R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 ≤
                  cellChainRadiusFactor R := by
              unfold cellChainRadiusFactor
              have hA : 0 ≤ R ^ 2 + R ^ 4 := by positivity
              linarith
            calc
              Ct * R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 ≤
                  C * (R ^ 2 * (1 + (4 * R) ^ 2) ^ 3) := by
                have hfac :
                    0 ≤ R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 :=
                  mul_nonneg (sq_nonneg R) (pow_nonneg (by positivity) 3)
                simpa only [mul_assoc] using
                  mul_le_mul_of_nonneg_right hCtC hfac
              _ ≤ C * cellChainRadiusFactor R := by
                exact mul_le_mul_of_nonneg_left
                  hRF hC.le
          have hscaled :
              Ct * (R * ε) ^ 2 ≤
                (C * cellChainRadiusFactor R) * ε ^ 2 *
                  (latticeEdgeWeight y a *
                    latticeEdgeWeight a b *
                    latticeEdgeWeight b e) := by
            calc
              Ct * (R * ε) ^ 2 =
                  (Ct * R ^ 2) * ε ^ 2 := by ring
              _ = (Ct * R ^ 2) * 1 * ε ^ 2 := by ring
              _ ≤ (Ct * R ^ 2) *
                    ((1 + (4 * R) ^ 2) ^ 3 *
                      (latticeEdgeWeight y a *
                        latticeEdgeWeight a b *
                        latticeEdgeWeight b e)) * ε ^ 2 := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hweight
                    (mul_nonneg hCt.le (sq_nonneg R)))
                  (sq_nonneg ε)
              _ = (Ct * R ^ 2 * (1 + (4 * R) ^ 2) ^ 3) *
                    ε ^ 2 *
                    (latticeEdgeWeight y a *
                      latticeEdgeWeight a b *
                      latticeEdgeWeight b e) := by ring
              _ ≤ (C * cellChainRadiusFactor R) * ε ^ 2 *
                    (latticeEdgeWeight y a *
                      latticeEdgeWeight a b *
                      latticeEdgeWeight b e) := by
                have hW :
                    0 ≤ latticeEdgeWeight y a *
                      latticeEdgeWeight a b *
                      latticeEdgeWeight b e :=
                  mul_nonneg
                    (mul_nonneg
                      (latticeEdgeWeight_nonneg_complete y a)
                      (latticeEdgeWeight_nonneg_complete a b))
                    (latticeEdgeWeight_nonneg_complete b e)
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hbaseFactor (sq_nonneg ε))
                  hW
              _ = (C * cellChainRadiusFactor R) * ε ^ 2 *
                    (latticeEdgeWeight y a *
                      latticeEdgeWeight a b *
                      latticeEdgeWeight b e) := by ring
          calc
            twoSidedTripleCellChain (R * ε)
                (latticeTorusCenter ε a) (latticeTorusCenter ε b) x z
                ([] : List T4) ([] : List T4)
                = localTripleCellIntegral (R * ε)
                    (latticeTorusCenter ε a)
                    (latticeTorusCenter ε b) x z := by
                      simp [twoSidedTripleCellChain.eq_def]
            _ ≤ Ct * (R * ε) ^ 2 := hlocal
            _ ≤ (C * cellChainRadiusFactor R) * ε ^ 2 *
                  (latticeEdgeWeight y a *
                    latticeEdgeWeight a b *
                    latticeEdgeWeight b e) := hscaled
            _ = (C * cellChainRadiusFactor R) ^
                  (([] : List Z4).length + [].length + 1) *
                ε ^ (2 * (([] : List Z4).length + [].length) + 2) *
                latticeTwoSidedTripleWeight y a b e [] [] := by
                  simp [latticeTwoSidedTripleWeight]
      | cons e' es ih =>
          intro x z hx hz hgeom
          rcases hgeom with ⟨_, hright, hcore⟩
          rcases hright with ⟨hEdgeEq, hrightTail⟩
          let K : ℝ :=
            (C * cellChainRadiusFactor R) ^ (es.length + 1) *
              ε ^ (2 * es.length + 2) *
              latticeTwoSidedTripleWeight y a b e' [] es
          have hK : 0 ≤ K := by
            dsimp [K]
            exact mul_nonneg
              (mul_nonneg
                (pow_nonneg
                  (mul_nonneg hC.le (cellChainRadiusFactor_pos R).le) _)
                (pow_nonneg hε.le _))
              (latticeTwoSidedTripleWeight_nonneg y a b e' [] es)
          have htail :
              ∀ u ∈ latticeCellNeighborhood ε R e',
                twoSidedTripleCellChain (R * ε)
                    (latticeTorusCenter ε a)
                    (latticeTorusCenter ε b) x u
                    ([].map (latticeTorusCenter ε))
                    (es.map (latticeTorusCenter ε)) ≤ K := by
            intro u hu
            simpa only [K, List.length_nil, zero_add] using
              ih e' x u hx hu
              ⟨trivial, hrightTail, by simpa using hcore⟩
          have hmono :
              twoSidedTripleCellChain (R * ε)
                  (latticeTorusCenter ε a)
                  (latticeTorusCenter ε b) x z
                  ([] : List T4)
                  ((e' :: es).map (latticeTorusCenter ε)) ≤
                ∫ u in latticeCellNeighborhood ε R e',
                  invSqKer (z - u) * K ∂paperMeasure := by
            rw [twoSidedTripleCellChain.eq_def]
            exact integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun u =>
                mul_nonneg (invSqKer_nonneg _)
                  (twoSidedTripleCellChain_nonneg
                    (R * ε) (latticeTorusCenter ε a)
                    (latticeTorusCenter ε b) x u []
                    (es.map (latticeTorusCenter ε))))
              ((integrable_invSqKer_sub_left z).mul_const K).integrableOn
              (by
                filter_upwards
                  [ae_restrict_mem
                    (measurableSet_latticeCellNeighborhood ε R e')]
                    with u hu
                exact mul_le_mul_of_nonneg_left
                  (htail u hu) (invSqKer_nonneg _))
          have hedge' :
              (∫ u in latticeCellNeighborhood ε R e',
                  invSqKer (z - u) ∂paperMeasure) ≤
                C * cellChainRadiusFactor R * ε ^ 2 *
                  latticeEdgeWeight e e' := by
            have hraw := hedge ε R hε hR e e' z hEdgeEq hz
            have hAF :
                R ^ 2 + R ^ 4 ≤ cellChainRadiusFactor R := by
              unfold cellChainRadiusFactor
              have hB :
                  0 ≤ R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 := by positivity
              linarith
            calc
              (∫ u in latticeCellNeighborhood ε R e',
                  invSqKer (z - u) ∂paperMeasure)
                  ≤ Ce * (R ^ 2 + R ^ 4) * ε ^ 2 *
                    latticeEdgeWeight e e' := hraw
              _ ≤ C * cellChainRadiusFactor R * ε ^ 2 *
                    latticeEdgeWeight e e' := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right
                    (mul_le_mul hCeC hAF (by positivity) hC.le)
                    (sq_nonneg ε))
                  (latticeEdgeWeight_nonneg_complete e e')
          calc
            twoSidedTripleCellChain (R * ε)
                (latticeTorusCenter ε a)
                (latticeTorusCenter ε b) x z
                ([] : List T4)
                ((e' :: es).map (latticeTorusCenter ε))
                ≤ ∫ u in latticeCellNeighborhood ε R e',
                    invSqKer (z - u) * K ∂paperMeasure := hmono
            _ = K * (∫ u in latticeCellNeighborhood ε R e',
                    invSqKer (z - u) ∂paperMeasure) := by
                  rw [integral_mul_const]
                  ring
            _ ≤ K * (C * cellChainRadiusFactor R * ε ^ 2 *
                  latticeEdgeWeight e e') :=
                mul_le_mul_of_nonneg_left hedge' hK
            _ = (C * cellChainRadiusFactor R) ^
                  (([] : List Z4).length + (e' :: es).length + 1) *
                ε ^ (2 * (([] : List Z4).length +
                  (e' :: es).length) + 2) *
                latticeTwoSidedTripleWeight y a b e [] (e' :: es) := by
                  simp only [List.length_nil, zero_add, List.length_cons,
                    latticeTwoSidedTripleWeight, K]
                  rw [show es.length + 1 + 1 =
                    (es.length + 1) + 1 by omega, pow_succ]
                  rw [show 2 * (es.length + 1) + 2 =
                    (2 * es.length + 2) + 2 by omega, pow_add]
                  ring
  | cons y' ys ih =>
      intro right x z hx hz hgeom
      rcases hgeom with ⟨hleft, hright, hcore⟩
      rcases hleft with ⟨hEdgeEq, hleftTail⟩
      let K : ℝ :=
        (C * cellChainRadiusFactor R) ^
            (ys.length + right.length + 1) *
          ε ^ (2 * (ys.length + right.length) + 2) *
          latticeTwoSidedTripleWeight y' a b e ys right
      have hK : 0 ≤ K := by
        dsimp [K]
        exact mul_nonneg
          (mul_nonneg
            (pow_nonneg
              (mul_nonneg hC.le (cellChainRadiusFactor_pos R).le) _)
            (pow_nonneg hε.le _))
          (latticeTwoSidedTripleWeight_nonneg y' a b e ys right)
      have htail :
          ∀ u ∈ latticeCellNeighborhood ε R y',
            twoSidedTripleCellChain (R * ε)
                (latticeTorusCenter ε a) (latticeTorusCenter ε b) u z
                (ys.map (latticeTorusCenter ε))
                (right.map (latticeTorusCenter ε)) ≤ K := by
        intro u hu
        exact ih y' e right u z hu hz
          ⟨hleftTail, hright, by simpa using hcore⟩
      have hmono :
          twoSidedTripleCellChain (R * ε)
              (latticeTorusCenter ε a) (latticeTorusCenter ε b) x z
              ((y' :: ys).map (latticeTorusCenter ε))
              (right.map (latticeTorusCenter ε)) ≤
            ∫ u in latticeCellNeighborhood ε R y',
              invSqKer (x - u) * K ∂paperMeasure := by
        rw [twoSidedTripleCellChain.eq_def]
        exact integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun u =>
            mul_nonneg (invSqKer_nonneg _)
              (twoSidedTripleCellChain_nonneg
                (R * ε) (latticeTorusCenter ε a)
                (latticeTorusCenter ε b) u z
                (ys.map (latticeTorusCenter ε))
                (right.map (latticeTorusCenter ε))))
          ((integrable_invSqKer_sub_left x).mul_const K).integrableOn
          (by
            filter_upwards
              [ae_restrict_mem
                (measurableSet_latticeCellNeighborhood ε R y')]
                with u hu
            exact mul_le_mul_of_nonneg_left
              (htail u hu) (invSqKer_nonneg _))
      have hedge' :
          (∫ u in latticeCellNeighborhood ε R y',
              invSqKer (x - u) ∂paperMeasure) ≤
            C * cellChainRadiusFactor R * ε ^ 2 *
              latticeEdgeWeight y y' := by
        have hraw := hedge ε R hε hR y y' x hEdgeEq hx
        have hAF :
            R ^ 2 + R ^ 4 ≤ cellChainRadiusFactor R := by
          unfold cellChainRadiusFactor
          have hB :
              0 ≤ R ^ 2 * (1 + (4 * R) ^ 2) ^ 3 := by positivity
          linarith
        calc
          (∫ u in latticeCellNeighborhood ε R y',
              invSqKer (x - u) ∂paperMeasure)
              ≤ Ce * (R ^ 2 + R ^ 4) * ε ^ 2 *
                latticeEdgeWeight y y' := hraw
          _ ≤ C * cellChainRadiusFactor R * ε ^ 2 *
                latticeEdgeWeight y y' := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul hCeC hAF (by positivity) hC.le)
                (sq_nonneg ε))
              (latticeEdgeWeight_nonneg_complete y y')
      calc
        twoSidedTripleCellChain (R * ε)
            (latticeTorusCenter ε a) (latticeTorusCenter ε b) x z
            ((y' :: ys).map (latticeTorusCenter ε))
            (right.map (latticeTorusCenter ε))
            ≤ ∫ u in latticeCellNeighborhood ε R y',
                invSqKer (x - u) * K ∂paperMeasure := hmono
        _ = K * (∫ u in latticeCellNeighborhood ε R y',
                invSqKer (x - u) ∂paperMeasure) := by
              rw [integral_mul_const]
              ring
        _ ≤ K * (C * cellChainRadiusFactor R * ε ^ 2 *
              latticeEdgeWeight y y') :=
            mul_le_mul_of_nonneg_left hedge' hK
        _ = (C * cellChainRadiusFactor R) ^
              ((y' :: ys).length + right.length + 1) *
            ε ^ (2 * ((y' :: ys).length + right.length) + 2) *
            latticeTwoSidedTripleWeight y a b e (y' :: ys) right := by
              simp only [List.length_cons, latticeTwoSidedTripleWeight, K]
              rw [show ys.length + 1 + right.length + 1 =
                (ys.length + right.length + 1) + 1 by omega, pow_succ]
              rw [show 2 * (ys.length + 1 + right.length) + 2 =
                (2 * (ys.length + right.length) + 2) + 2 by omega,
                pow_add]
              ring

/-- Paper-order form of the all-near branch.  The two central variables
and all outer variables total `2n-2`, hence the local-triple scale and the
outer `ε²` factors again give exactly `ε^(4n-6)`. -/
theorem twoSidedTripleLatticeCellChain_order_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (_hn : 2 ≤ n) (ε R : ℝ)
        (_hε : 0 < ε) (_hR : 0 < R)
        (y a b e : Z4) (left right : List Z4) (x z : T4),
        left.length + right.length + 2 = 2 * n - 2 →
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTwoSidedTripleGeometry ε R y a b e left right →
        twoSidedTripleCellChain (R * ε)
            (latticeTorusCenter ε a) (latticeTorusCenter ε b) x z
            (left.map (latticeTorusCenter ε))
            (right.map (latticeTorusCenter ε)) ≤
          (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
            ε ^ (4 * n - 6) *
            latticeTwoSidedTripleWeight y a b e left right := by
  obtain ⟨C, hC, hchain⟩ := twoSidedTripleLatticeCellChain_le
  refine ⟨C, hC, ?_⟩
  intro n hn ε R hε hR y a b e left right x z hlen hx hz hgeom
  have hbase := hchain ε R hε hR y a b e left right x z hx hz hgeom
  have hpow :
      left.length + right.length + 1 = 2 * n - 3 := by omega
  have hexp :
      2 * (left.length + right.length) + 2 = 4 * n - 6 := by omega
  rw [hpow, hexp] at hbase
  exact hbase

end

end Anderson4D
