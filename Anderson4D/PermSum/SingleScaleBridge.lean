import Anderson4D.PermSum.SingleScaleSetup
import Anderson4D.PermSum.SingleScaleMixed

/-!
# Assembly bridge for the single-scale estimate

This file connects the finite `(N,X,Y,P)` classification in
`SingleScaleSetup` to the analytic skipped-edge estimates in
`SingleScaleMixed`.  Each analytic cluster remains the image of one
`(N,X)` fiber.  In particular, an `(N,Y)` class is represented by its
canonical maximal-`X` fiber, never by the union of all its fibers.
-/

namespace Anderson4D

open PlaneTree

noncomputable section

namespace XYCluster

/-! ## Root-budget certificates -/

/-- The raw root-budget estimate for an active `(N,X)` fiber, packaged in
the exact interface consumed by the constant-one mixed estimate. -/
theorem nxClassCluster_RNDominance_one {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℕ) (hR : accumulatedScale Nm mu (rootV t) ≤ R)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    RNDominance 1 (R : ℝ)
      (nxClassCluster ht hroot Nm mu z hz a ha) := by
  simpa [RNDominance] using
    nxClassCluster_R_dominance_one
      ht hroot Nm mu z hz R hR ha

/-- Safe constant-two weakening for the coarse `(N,Y)` representative.
The exact-cardinality root budget already gives constant-one dominance for
its chosen maximal-`X` fiber; `2` is exposed only as an assembly-safe
weakening, not as a necessary dyadic-cardinality loss. -/
theorem nyClassCluster_RNDominance_two {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℕ) (hR : accumulatedScale Nm mu (rootV t) ≤ R)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    RNDominance 2 (R : ℝ)
      (nyClassCluster ht hroot Nm mu z hz q hq) := by
  simpa [RNDominance] using
    nyClassCluster_R_dominance_two
      ht hroot Nm mu z hz R hR q hq

/-- Every active `(N,X)` cluster has a point. -/
theorem nxClassCluster_points_nonempty {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    (nxClassCluster ht hroot Nm mu z hz a ha).points.Nonempty := by
  simpa using nxClassPoints_nonempty Nm mu z ha

/-- The dyadic multiplicity weight of every active `(N,X)` cluster is at
least one. -/
theorem nxClassCluster_one_le_X {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    1 ≤ (nxClassCluster ht hroot Nm mu z hz a ha).X := by
  rw [nxClassCluster_X]
  exact_mod_cast one_le_nxClass_X Nm mu ha

/-! ## From labeled copies to the point carrier

The paper's permutation word contains `mu.m l` distinct copies of a leaf
`l`, whereas Lemma 5.14 sums once over its lattice point.  On an active
`(N,X)` fiber these quantities are comparable but not equal:
`X ≤ mu.m l < 2X`.  The definitions and bounds below preserve the actual
multiplicity and expose one factor `2` for every independently chosen copy.
-/

/-- A weighted sum over the distinct copies in one `(N,X)` fiber, written
without inventing labels: the weight at `z l` is repeated `mu.m l` times. -/
def nxCopyWeightedSum {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (a : NXClass)
    (f : (Fin 4 → ℤ) → ℝ) : ℝ :=
  ∑ l ∈ leavesAtNX Nm mu a, (leafMultiplicity mu l : ℝ) * f (z l)

/-- The corresponding point-level sum, with each embedded leaf counted
once. -/
def nxPointWeightedSum {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (a : NXClass)
    (f : (Fin 4 → ℤ) → ℝ) : ℝ :=
  ∑ x ∈ nxClassPoints Nm mu z a, f x

/-- Exact paper fact behind the copies-to-points conversion: an actual leaf
multiplicity is strictly smaller than twice its dyadic bucket value. -/
theorem leafMultiplicity_lt_two_mul_nxClass_X {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (_ha : a ∈ nxCarrier Nm mu)
    {l : HeppLeaf t} (hl : l ∈ leavesAtNX Nm mu a) :
    leafMultiplicity mu l < 2 * a.2 := by
  have hclass : singleScaleSigma1 Nm mu l = a :=
    (Finset.mem_filter.mp hl).2
  simpa [hclass] using (sigma1_bucket Nm mu l).2

/-- One copy variable costs at most `2` after the analytic `X` factor is
pulled out.  The weight is allowed to depend on the embedded lattice point. -/
theorem nxCopyWeightedSum_le_two_mul_pointWeightedSum {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu)
    (f : (Fin 4 → ℤ) → ℝ)
    (hf : ∀ x ∈ nxClassPoints Nm mu z a, 0 ≤ f x) :
    nxCopyWeightedSum Nm mu z a f ≤
      2 * ((a.2 : ℝ) * nxPointWeightedSum Nm mu z a f) := by
  unfold nxCopyWeightedSum nxPointWeightedSum
  calc
    (∑ l ∈ leavesAtNX Nm mu a,
        (leafMultiplicity mu l : ℝ) * f (z l)) ≤
        ∑ l ∈ leavesAtNX Nm mu a, (2 * (a.2 : ℝ)) * f (z l) := by
      apply Finset.sum_le_sum
      intro l hl
      have hmNat :
          leafMultiplicity mu l ≤ 2 * a.2 :=
        Nat.le_of_lt (leafMultiplicity_lt_two_mul_nxClass_X Nm mu ha hl)
      have hm :
          (leafMultiplicity mu l : ℝ) ≤ 2 * (a.2 : ℝ) := by
        exact_mod_cast hmNat
      have hpoint :
          z l ∈ nxClassPoints Nm mu z a :=
        Finset.mem_image.mpr ⟨l, hl, rfl⟩
      exact mul_le_mul_of_nonneg_right hm (hf (z l) hpoint)
    _ = (2 * (a.2 : ℝ)) *
        ∑ l ∈ leavesAtNX Nm mu a, f (z l) := by
      rw [Finset.mul_sum]
    _ = 2 * ((a.2 : ℝ) *
        ∑ l ∈ leavesAtNX Nm mu a, f (z l)) := by ring
    _ = 2 * ((a.2 : ℝ) *
        ∑ x ∈ nxClassPoints Nm mu z a, f x) := by
      rw [nxClassPoints, Finset.sum_image hz.1.injOn]

/-- Number of actual labeled-copy choices in one active fiber. -/
def nxCopyChoiceCount {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (a : NXClass) : ℕ :=
  ∑ l ∈ leavesAtNX Nm mu a, leafMultiplicity mu l

/-- Number of point choices after pulling out the dyadic multiplicity `X`. -/
def nxPointChoiceCount {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (a : NXClass) : ℕ :=
  a.2 * (nxClassPoints Nm mu z a).card

/-- Counting specialization of the one-variable copies-to-points bound.
It uses the actual `mu.m l`; no multiplicity is identified with `X`. -/
theorem nxCopyChoiceCount_le_two_mul_pointChoiceCount {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : Function.Injective z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    nxCopyChoiceCount Nm mu a ≤
      2 * nxPointChoiceCount Nm mu z a := by
  unfold nxCopyChoiceCount nxPointChoiceCount
  calc
    (∑ l ∈ leavesAtNX Nm mu a, leafMultiplicity mu l) ≤
        ∑ _l ∈ leavesAtNX Nm mu a, 2 * a.2 := by
      apply Finset.sum_le_sum
      intro l hl
      exact Nat.le_of_lt
        (leafMultiplicity_lt_two_mul_nxClass_X Nm mu ha hl)
    _ = 2 * (a.2 * (nxClassPoints Nm mu z a).card) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_nxClassPoints Nm mu z hz a]
      ac_rfl

/-- `k` independent copy choices incur the explicit loss `2^k`. -/
theorem nxCopyChoiceCount_pow_le_two_pow_mul_pointChoiceCount_pow
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : Function.Injective z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) (k : ℕ) :
    (nxCopyChoiceCount Nm mu a) ^ k ≤
      2 ^ k * (nxPointChoiceCount Nm mu z a) ^ k := by
  calc
    (nxCopyChoiceCount Nm mu a) ^ k ≤
        (2 * nxPointChoiceCount Nm mu z a) ^ k :=
      Nat.pow_le_pow_left
        (nxCopyChoiceCount_le_two_mul_pointChoiceCount
          Nm mu z hz ha) k
    _ = 2 ^ k * (nxPointChoiceCount Nm mu z a) ^ k := by
      rw [mul_pow]

/-- Weighted `k`-variable version.  This is the reusable interface for
replacing independent labeled-copy sums by Lemma 5.14 point sums. -/
theorem nxCopyWeightedChoice_le_two_pow_mul_pointWeightedChoice
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu)
    (k : ℕ) (f : Fin k → (Fin 4 → ℤ) → ℝ)
    (hf : ∀ i x, x ∈ nxClassPoints Nm mu z a → 0 ≤ f i x) :
    (∏ i : Fin k, nxCopyWeightedSum Nm mu z a (f i)) ≤
      2 ^ k *
        ∏ i : Fin k,
          ((a.2 : ℝ) * nxPointWeightedSum Nm mu z a (f i)) := by
  calc
    (∏ i : Fin k, nxCopyWeightedSum Nm mu z a (f i)) ≤
        ∏ i : Fin k,
          (2 * ((a.2 : ℝ) * nxPointWeightedSum Nm mu z a (f i))) := by
      apply Finset.prod_le_prod
      · intro i _hi
        unfold nxCopyWeightedSum
        apply Finset.sum_nonneg
        intro l hl
        exact mul_nonneg (by positivity)
          (hf i (z l) (Finset.mem_image.mpr ⟨l, hl, rfl⟩))
      · intro i _hi
        exact nxCopyWeightedSum_le_two_mul_pointWeightedSum
          Nm mu z hz ha (f i) (hf i)
    _ = 2 ^ k *
        ∏ i : Fin k,
          ((a.2 : ℝ) * nxPointWeightedSum Nm mu z a (f i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]

/-! ### The coupled two-copy sum used in (5.91) -/

/-- The unrestricted nested sum over the actual labeled copies in two
possibly different `(N,X)` fibers.  This is the copy-level left-hand side
that dominates the corresponding conditional permutation sum: forgetting
which labeled copies have already been used only enlarges a nonnegative
sum. -/
noncomputable def nxCoupledCopyPairSum {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) {a b : NXClass}
    (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu)
    (skipA skipB : Bool) (u : Fin 4 → ℤ) : ℝ :=
  let ca := nxClassCluster ht hroot Nm mu z hz a ha
  let cb := nxClassCluster ht hroot Nm mu z hz b hb
  nxCopyWeightedSum Nm mu z a fun x =>
    ca.lambda R skipA u x *
      nxCopyWeightedSum Nm mu z b fun y =>
        strongLambda ca cb R skipB x y

private theorem lambda_nonneg_bridge (c : XYCluster) (R : ℝ)
    (skipped : Bool) (u x : Fin 4 → ℤ) :
    0 ≤ c.lambda R skipped u x := by
  unfold lambda
  split_ifs <;> positivity

private theorem strongLambda_nonneg_bridge (a b : XYCluster) (R : ℝ)
    (skipped : Bool) (x y : Fin 4 → ℤ) :
    0 ≤ strongLambda a b R skipped x y := by
  unfold strongLambda
  split_ifs <;> positivity

/-- Replacing the two actual copy variables by their point carriers costs
at most `2² = 4`.  The proof is nested, so the second edge may genuinely
depend on the first point; no false product-separability assumption is used. -/
theorem nxCoupledCopyPairSum_le_four_mul_mixedPairInner {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) {a b : NXClass}
    (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu)
    (skipA skipB : Bool) (u : Fin 4 → ℤ) :
    nxCoupledCopyPairSum ht hroot Nm mu z hz R ha hb skipA skipB u ≤
      4 * mixedPairInner
        (nxClassCluster ht hroot Nm mu z hz a ha)
        (nxClassCluster ht hroot Nm mu z hz b hb)
        R skipA skipB u := by
  let ca := nxClassCluster ht hroot Nm mu z hz a ha
  let cb := nxClassCluster ht hroot Nm mu z hz b hb
  let innerCopy := fun x =>
    nxCopyWeightedSum Nm mu z b fun y =>
      strongLambda ca cb R skipB x y
  let innerPoint := fun x =>
    nxPointWeightedSum Nm mu z b fun y =>
      strongLambda ca cb R skipB x y
  have hinner (x : Fin 4 → ℤ) :
      innerCopy x ≤ 2 * ((b.2 : ℝ) * innerPoint x) := by
    exact nxCopyWeightedSum_le_two_mul_pointWeightedSum
      Nm mu z hz hb
      (fun y => strongLambda ca cb R skipB x y)
      (fun y _hy => strongLambda_nonneg_bridge ca cb R skipB x y)
  have hinner_nonneg (x : Fin 4 → ℤ) : 0 ≤ innerCopy x := by
    unfold innerCopy nxCopyWeightedSum
    apply Finset.sum_nonneg
    intro l _hl
    exact mul_nonneg (by positivity)
      (strongLambda_nonneg_bridge ca cb R skipB x (z l))
  have houter :
      nxCoupledCopyPairSum ht hroot Nm mu z hz R ha hb skipA skipB u ≤
        2 * ((a.2 : ℝ) *
          nxPointWeightedSum Nm mu z a
            (fun x => ca.lambda R skipA u x * innerCopy x)) := by
    simpa [nxCoupledCopyPairSum, ca, cb, innerCopy] using
      nxCopyWeightedSum_le_two_mul_pointWeightedSum
        Nm mu z hz ha
        (fun x => ca.lambda R skipA u x * innerCopy x)
        (fun x _hx =>
          mul_nonneg (lambda_nonneg_bridge ca R skipA u x)
            (hinner_nonneg x))
  calc
    nxCoupledCopyPairSum ht hroot Nm mu z hz R ha hb skipA skipB u ≤
        2 * ((a.2 : ℝ) *
          nxPointWeightedSum Nm mu z a
            (fun x => ca.lambda R skipA u x * innerCopy x)) := houter
    _ ≤ 2 * ((a.2 : ℝ) *
          nxPointWeightedSum Nm mu z a
            (fun x => ca.lambda R skipA u x *
              (2 * ((b.2 : ℝ) * innerPoint x)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold nxPointWeightedSum
      apply Finset.sum_le_sum
      intro x _hx
      exact mul_le_mul_of_nonneg_left (hinner x)
        (lambda_nonneg_bridge ca R skipA u x)
    _ = 4 * mixedPairInner ca cb R skipA skipB u := by
      have hsum :
          (∑ x ∈ nxClassPoints Nm mu z a,
              ca.lambda R skipA u x *
                (2 * ((b.2 : ℝ) *
                  ∑ y ∈ nxClassPoints Nm mu z b,
                    strongLambda ca cb R skipB x y))) =
            (2 * (b.2 : ℝ)) *
              ∑ x ∈ nxClassPoints Nm mu z a,
                ca.lambda R skipA u x *
                  ∑ y ∈ nxClassPoints Nm mu z b,
                    strongLambda ca cb R skipB x y := by
        calc
          _ = ∑ x ∈ nxClassPoints Nm mu z a,
                (2 * (b.2 : ℝ)) *
                  (ca.lambda R skipA u x *
                    ∑ y ∈ nxClassPoints Nm mu z b,
                      strongLambda ca cb R skipB x y) := by
                apply Finset.sum_congr rfl
                intro x _hx
                ring
          _ = _ := by rw [Finset.mul_sum]
      change
        2 * ((a.2 : ℝ) *
          ∑ x ∈ nxClassPoints Nm mu z a,
            ca.lambda R skipA u x *
              (2 * ((b.2 : ℝ) *
                ∑ y ∈ nxClassPoints Nm mu z b,
                  strongLambda ca cb R skipB x y))) =
          4 * ((a.2 : ℝ) * (b.2 : ℝ) *
            ∑ x ∈ nxClassPoints Nm mu z a,
              ca.lambda R skipA u x *
                ∑ y ∈ nxClassPoints Nm mu z b,
                  strongLambda ca cb R skipB x y)
      rw [hsum]
      ring

/-! ## Uniform local assembly -/

/-- Uniform form of (5.91) for arbitrary active `(N,X)` fibers.  The
existential constant is outside every tree, class, embedding, and skip
choice, so later finite sums may use it without choosing a new constant
for each fiber. -/
theorem nxClassClusters_mixedPairInner_le_5_91 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {t : PlaneTree}
        (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ {a b : NXClass}
          (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu)
          (skipA skipB : Bool) (u : Fin 4 → ℤ),
          mixedPairInner
              (nxClassCluster ht hroot Nm mu z hz a ha)
              (nxClassCluster ht hroot Nm mu z hz b hb)
              (R : ℝ) skipA skipB u ≤
            C * mixedTarget
              (nxClassCluster ht hroot Nm mu z hz a ha)
              (nxClassCluster ht hroot Nm mu z hz b hb)
              skipA skipB := by
  obtain ⟨C, hC, hlocal⟩ :=
    mixedPairInner_le_5_91_of_dominance_one
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu z hz R hR a b ha hb skipA skipB u
  exact hlocal (R : ℝ)
    (nxClassCluster ht hroot Nm mu z hz a ha)
    (nxClassCluster ht hroot Nm mu z hz b hb)
    skipA skipB u
    (nxClassCluster_one_le_X ht hroot Nm mu z hz ha)
    (nxClassCluster_one_le_X ht hroot Nm mu z hz hb)
    (nxClassCluster_points_nonempty ht hroot Nm mu z hz ha)
    (nxClassCluster_points_nonempty ht hroot Nm mu z hz hb)
    (nxClassCluster_RNDominance_one ht hroot Nm mu z hz R hR ha)
    (nxClassCluster_RNDominance_one ht hroot Nm mu z hz R hR hb)

/-- Representative-only convenience bound for active `(N,Y)` classes.
It estimates the canonical maximal-`X` fiber used in the coarse (5.75)
ledger.  It must not replace the arbitrary `(N,X)` fibers occurring in
the fixed-`X` inner sum (5.87). -/
theorem nyClassClusters_mixedPairInner_le_5_91 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {t : PlaneTree}
        (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ {q r : NYClass}
          (hq : q ∈ nyCarrier Nm mu) (hr : r ∈ nyCarrier Nm mu)
          (skipQ skipR : Bool) (u : Fin 4 → ℤ),
          mixedPairInner
              (nyClassCluster ht hroot Nm mu z hz q hq)
              (nyClassCluster ht hroot Nm mu z hz r hr)
              (R : ℝ) skipQ skipR u ≤
            C * mixedTarget
              (nyClassCluster ht hroot Nm mu z hz q hq)
              (nyClassCluster ht hroot Nm mu z hz r hr)
              skipQ skipR := by
  obtain ⟨C, hC, hlocal⟩ :=
    mixedPairInner_le_5_91_of_dominance_two
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu z hz R hR q r hq hr skipQ skipR u
  exact hlocal (R : ℝ)
    (nyClassCluster ht hroot Nm mu z hz q hq)
    (nyClassCluster ht hroot Nm mu z hz r hr)
    skipQ skipR u
    (nyClassCluster_one_le_X ht hroot Nm mu z hz q hq)
    (nyClassCluster_one_le_X ht hroot Nm mu z hz r hr)
    (nyClassCluster_points_nonempty ht hroot Nm mu z hz q hq)
    (nyClassCluster_points_nonempty ht hroot Nm mu z hz r hr)
    (nyClassCluster_RNDominance_two ht hroot Nm mu z hz R hR hq)
    (nyClassCluster_RNDominance_two ht hroot Nm mu z hz R hR hr)

/-! ## Actual-volume versus dyadic-volume gain -/

/-- The paper's dyadic volume `P = Y N⁴`, cast to the analytic value type. -/
def dyadicP (q : NYClass) : ℝ :=
  singleScaleSigma3 q

/-- The dyadic gain in (5.87)/(5.91), with exponent `1/8`.
The separate outer estimate (5.76) uses `θ = 1/20`. -/
noncomputable def dyadicForwardGain (q r : NYClass) : ℝ :=
  min 1 ((dyadicP r / dyadicP q) ^ (1 / 8 : ℝ))

/-- An active dyadic class has strictly positive paper volume. -/
theorem dyadicP_pos {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    0 < dyadicP q := by
  let c := nyClassCluster ht hroot Nm mu z hz q hq
  have hcP : 0 < c.P :=
    P_pos_of_nonempty
      (nyClassCluster_points_nonempty ht hroot Nm mu z hz q hq)
  have hcompare :
      8 * c.P ≤ dyadicP q := by
    simpa [dyadicP] using
      (nyClassCluster_P_comparable
        ht hroot Nm mu z hz q hq).1
  nlinarith

theorem dyadicForwardGain_nonneg (q r : NYClass) :
    0 ≤ dyadicForwardGain q r := by
  have hq : 0 ≤ dyadicP q := by
    unfold dyadicP singleScaleSigma3
    positivity
  have hr : 0 ≤ dyadicP r := by
    unfold dyadicP singleScaleSigma3
    positivity
  unfold dyadicForwardGain
  exact le_min zero_le_one
    (Real.rpow_nonneg (div_nonneg hr hq) _)

/-! ### The exact dyadic target printed in (5.91) -/

/-- The dyadic point-count parameter `Y` belonging to an `(N,X)` fiber. -/
def paperDyadicY {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (a : NXClass) : ℝ :=
  (singleScaleSigma2 Nm mu a).2

/-- The unskipped local factor `X Y^(1/2) N⁻²` in (5.91), using the
paper's original scale `N`, not the analytic separation scale `N/2`. -/
noncomputable def paperDyadicBase {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (a : NXClass) : ℝ :=
  (a.2 : ℝ) * Real.sqrt (paperDyadicY Nm mu a) *
    (a.1 : ℝ)⁻¹ ^ 2

/-- The paper's factor `Ξ = (XY)⁻¹/²` when the incoming edge is skipped. -/
noncomputable def paperDyadicSkipXi {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (a : NXClass) (skipped : Bool) : ℝ :=
  if skipped then
    (Real.sqrt ((a.2 : ℝ) * paperDyadicY Nm mu a))⁻¹
  else 1

/-- One exact local factor on the right-hand side of (5.91). -/
noncomputable def paperDyadicLocalTarget {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (a : NXClass) (skipped : Bool) : ℝ :=
  paperDyadicBase Nm mu a * paperDyadicSkipXi Nm mu a skipped

/-- The exact two-cluster dyadic target on the right-hand side of (5.91). -/
noncomputable def paperDyadicPairTarget {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (a b : NXClass) (skipA skipB : Bool) : ℝ :=
  paperDyadicLocalTarget Nm mu a skipA *
    paperDyadicLocalTarget Nm mu b skipB *
      dyadicForwardGain
        (singleScaleSigma2 Nm mu a)
        (singleScaleSigma2 Nm mu b)

theorem paperDyadicLocalTarget_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (a : NXClass) (skipped : Bool) :
    0 ≤ paperDyadicLocalTarget Nm mu a skipped := by
  unfold paperDyadicLocalTarget paperDyadicBase paperDyadicSkipXi
  split_ifs <;> positivity

theorem paperDyadicPairTarget_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (a b : NXClass) (skipA skipB : Bool) :
    0 ≤ paperDyadicPairTarget Nm mu a b skipA skipB := by
  unfold paperDyadicPairTarget
  exact mul_nonneg
    (mul_nonneg
      (paperDyadicLocalTarget_nonneg Nm mu a skipA)
      (paperDyadicLocalTarget_nonneg Nm mu b skipB))
    (dyadicForwardGain_nonneg _ _)

private theorem nxClass_actualP_ratio_le_two_mul_dyadicP_ratio
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a b : NXClass}
    (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu) :
    (nxClassCluster ht hroot Nm mu z hz b hb).P /
        (nxClassCluster ht hroot Nm mu z hz a ha).P ≤
      2 * (dyadicP (singleScaleSigma2 Nm mu b) /
        dyadicP (singleScaleSigma2 Nm mu a)) := by
  let ca := nxClassCluster ht hroot Nm mu z hz a ha
  let cb := nxClassCluster ht hroot Nm mu z hz b hb
  have hqa :
      singleScaleSigma2 Nm mu a ∈ nyCarrier Nm mu :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hqb :
      singleScaleSigma2 Nm mu b ∈ nyCarrier Nm mu :=
    Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hcaP : 0 < ca.P :=
    P_pos_of_nonempty
      (nxClassCluster_points_nonempty ht hroot Nm mu z hz ha)
  have hcbP : 0 < cb.P :=
    P_pos_of_nonempty
      (nxClassCluster_points_nonempty ht hroot Nm mu z hz hb)
  have hqaP : 0 < dyadicP (singleScaleSigma2 Nm mu a) :=
    dyadicP_pos ht hroot Nm mu z hz hqa
  have hqbP : 0 < dyadicP (singleScaleSigma2 Nm mu b) :=
    dyadicP_pos ht hroot Nm mu z hz hqb
  have haUpper :
      dyadicP (singleScaleSigma2 Nm mu a) ≤ 16 * ca.P := by
    simpa [dyadicP, ca] using
      nxClassCluster_P_lower ht hroot Nm mu z hz ha
  have hbLower :
      8 * cb.P ≤ dyadicP (singleScaleSigma2 Nm mu b) := by
    simpa [dyadicP, cb] using
      nxClassCluster_P_upper ht hroot Nm mu z hz hb
  have hcbUpper :
      cb.P ≤ dyadicP (singleScaleSigma2 Nm mu b) / 8 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith
  have hcaLower :
      dyadicP (singleScaleSigma2 Nm mu a) / 16 ≤ ca.P := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
    nlinarith
  have hratio :
      cb.P / ca.P ≤
        (dyadicP (singleScaleSigma2 Nm mu b) / 8) /
          (dyadicP (singleScaleSigma2 Nm mu a) / 16) :=
    div_le_div₀
      (div_nonneg hqbP.le (by norm_num))
      hcbUpper
      (div_pos hqaP (by norm_num))
      hcaLower
  calc
    cb.P / ca.P ≤
        (dyadicP (singleScaleSigma2 Nm mu b) / 8) /
          (dyadicP (singleScaleSigma2 Nm mu a) / 16) := hratio
    _ = 2 * (dyadicP (singleScaleSigma2 Nm mu b) /
          dyadicP (singleScaleSigma2 Nm mu a)) := by
      field_simp [hqaP.ne']
      ring

/-- The actual Lemma 5.14 gain for arbitrary active `(N,X)` fibers is
controlled by the dyadic `P = YN⁴` gain attached to their own `σ₂`
classes.  No maximal-`X` representative is substituted. -/
theorem nxClassCluster_forwardGain_le_dyadicForwardGain
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a b : NXClass}
    (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu) :
    forwardGain
        (nxClassCluster ht hroot Nm mu z hz a ha)
        (nxClassCluster ht hroot Nm mu z hz b hb) ≤
      (2 : ℝ) ^ (1 / 8 : ℝ) *
        dyadicForwardGain
          (singleScaleSigma2 Nm mu a)
          (singleScaleSigma2 Nm mu b) := by
  let ca := nxClassCluster ht hroot Nm mu z hz a ha
  let cb := nxClassCluster ht hroot Nm mu z hz b hb
  have hqa :
      singleScaleSigma2 Nm mu a ∈ nyCarrier Nm mu :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hqb :
      singleScaleSigma2 Nm mu b ∈ nyCarrier Nm mu :=
    Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hcaP : 0 < ca.P :=
    P_pos_of_nonempty
      (nxClassCluster_points_nonempty ht hroot Nm mu z hz ha)
  have hcbP : 0 < cb.P :=
    P_pos_of_nonempty
      (nxClassCluster_points_nonempty ht hroot Nm mu z hz hb)
  have hqaP : 0 < dyadicP (singleScaleSigma2 Nm mu a) :=
    dyadicP_pos ht hroot Nm mu z hz hqa
  have hqbP : 0 < dyadicP (singleScaleSigma2 Nm mu b) :=
    dyadicP_pos ht hroot Nm mu z hz hqb
  have hratio :
      cb.P / ca.P ≤
        2 * (dyadicP (singleScaleSigma2 Nm mu b) /
          dyadicP (singleScaleSigma2 Nm mu a)) :=
    nxClass_actualP_ratio_le_two_mul_dyadicP_ratio
      ht hroot Nm mu z hz ha hb
  have hratioActual : 0 ≤ cb.P / ca.P :=
    div_nonneg hcbP.le hcaP.le
  have hratioDyadic :
      0 ≤ dyadicP (singleScaleSigma2 Nm mu b) /
        dyadicP (singleScaleSigma2 Nm mu a) :=
    div_nonneg hqbP.le hqaP.le
  have hpow :
      (cb.P / ca.P) ^ (1 / 8 : ℝ) ≤
        (2 : ℝ) ^ (1 / 8 : ℝ) *
          (dyadicP (singleScaleSigma2 Nm mu b) /
            dyadicP (singleScaleSigma2 Nm mu a)) ^ (1 / 8 : ℝ) := by
    calc
      (cb.P / ca.P) ^ (1 / 8 : ℝ) ≤
          (2 * (dyadicP (singleScaleSigma2 Nm mu b) /
            dyadicP (singleScaleSigma2 Nm mu a))) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow hratioActual hratio (by norm_num)
      _ = (2 : ℝ) ^ (1 / 8 : ℝ) *
          (dyadicP (singleScaleSigma2 Nm mu b) /
            dyadicP (singleScaleSigma2 Nm mu a)) ^ (1 / 8 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hratioDyadic]
  have hconstant :
      1 ≤ (2 : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by norm_num) (by norm_num)
  unfold forwardGain dyadicForwardGain
  by_cases hdyadic :
      (dyadicP (singleScaleSigma2 Nm mu b) /
        dyadicP (singleScaleSigma2 Nm mu a)) ^ (1 / 8 : ℝ) ≤ 1
  · rw [min_eq_right hdyadic]
    exact (min_le_right _ _).trans hpow
  · have hone :
        1 ≤ (dyadicP (singleScaleSigma2 Nm mu b) /
          dyadicP (singleScaleSigma2 Nm mu a)) ^ (1 / 8 : ℝ) :=
      le_of_not_ge hdyadic
    rw [min_eq_left hone]
    calc
      min 1 ((cb.P / ca.P) ^ (1 / 8 : ℝ)) ≤ 1 :=
        min_le_left _ _
      _ ≤ (2 : ℝ) ^ (1 / 8 : ℝ) := hconstant
      _ = (2 : ℝ) ^ (1 / 8 : ℝ) * 1 := by ring

private theorem paperDyadicY_pos {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (_ha : a ∈ nxCarrier Nm mu) :
    0 < paperDyadicY Nm mu a := by
  unfold paperDyadicY singleScaleSigma2 dyadicFloor
  positivity

private theorem nxClassCluster_sqrtY_le_two_mul_paperSqrtY
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    Real.sqrt (nxClassCluster ht hroot Nm mu z hz a ha).Y ≤
      2 * Real.sqrt (paperDyadicY Nm mu a) := by
  let c := nxClassCluster ht hroot Nm mu z hz a ha
  have hcardNat :
      c.points.card ≤ 2 * (singleScaleSigma2 Nm mu a).2 :=
    Nat.le_of_lt (nxClassCluster_card_bounds
      ht hroot Nm mu z hz ha).2
  have hcard :
      c.Y ≤ 2 * paperDyadicY Nm mu a := by
    unfold Y paperDyadicY
    exact_mod_cast hcardNat
  have hY : 0 ≤ paperDyadicY Nm mu a :=
    (paperDyadicY_pos Nm mu ha).le
  have hcard4 :
      c.Y ≤ 4 * paperDyadicY Nm mu a := by
    nlinarith
  calc
    Real.sqrt c.Y ≤
        Real.sqrt (4 * paperDyadicY Nm mu a) :=
      Real.sqrt_le_sqrt hcard4
    _ = Real.sqrt 4 * Real.sqrt (paperDyadicY Nm mu a) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    _ = 2 * Real.sqrt (paperDyadicY Nm mu a) := by norm_num

private theorem nxClassCluster_invSq_eq_four_mul_paperInvSq
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    (nxClassCluster ht hroot Nm mu z hz a ha).N⁻¹ ^ 2 =
      4 * (a.1 : ℝ)⁻¹ ^ 2 := by
  rw [nxClassCluster_N ht hroot Nm mu z hz a ha]
  have hN : (a.1 : ℝ) ≠ 0 := by
    have htwo := two_le_nxClass_scale ht hroot Nm mu ha
    exact_mod_cast (by omega : a.1 ≠ 0)
  field_simp [hN]
  ring

private theorem nxClassCluster_base_le_eight_mul_paperDyadicBase
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    (nxClassCluster ht hroot Nm mu z hz a ha).X *
        Real.sqrt (nxClassCluster ht hroot Nm mu z hz a ha).Y *
        (nxClassCluster ht hroot Nm mu z hz a ha).N⁻¹ ^ 2 ≤
      8 * paperDyadicBase Nm mu a := by
  let c := nxClassCluster ht hroot Nm mu z hz a ha
  have hsqrt :
      Real.sqrt c.Y ≤
        2 * Real.sqrt (paperDyadicY Nm mu a) :=
    nxClassCluster_sqrtY_le_two_mul_paperSqrtY
      ht hroot Nm mu z hz ha
  have hinv :
      c.N⁻¹ ^ 2 = 4 * (a.1 : ℝ)⁻¹ ^ 2 :=
    nxClassCluster_invSq_eq_four_mul_paperInvSq
      ht hroot Nm mu z hz ha
  have hscaledSqrt :
      (a.2 : ℝ) * Real.sqrt c.Y ≤
        (a.2 : ℝ) * (2 * Real.sqrt (paperDyadicY Nm mu a)) :=
    mul_le_mul_of_nonneg_left hsqrt (by positivity)
  rw [show c.X = (a.2 : ℝ) by rfl, hinv]
  unfold paperDyadicBase
  calc
    (a.2 : ℝ) * Real.sqrt c.Y *
        (4 * (a.1 : ℝ)⁻¹ ^ 2) ≤
      ((a.2 : ℝ) * (2 * Real.sqrt (paperDyadicY Nm mu a))) *
        (4 * (a.1 : ℝ)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_right hscaledSqrt (by positivity)
    _ = 8 * ((a.2 : ℝ) * Real.sqrt (paperDyadicY Nm mu a) *
        (a.1 : ℝ)⁻¹ ^ 2) := by ring

private theorem nxClassCluster_skipXi_le_paperDyadicSkipXi
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) (skipped : Bool) :
    skipXi (nxClassCluster ht hroot Nm mu z hz a ha) skipped ≤
      paperDyadicSkipXi Nm mu a skipped := by
  let c := nxClassCluster ht hroot Nm mu z hz a ha
  cases skipped with
  | false => simp [skipXi, paperDyadicSkipXi]
  | true =>
      have hcardNat :
          (singleScaleSigma2 Nm mu a).2 ≤ c.points.card :=
        (nxClassCluster_card_bounds ht hroot Nm mu z hz ha).1
      have hcard :
          paperDyadicY Nm mu a ≤ c.Y := by
        unfold paperDyadicY Y
        exact_mod_cast hcardNat
      have hXpos : 0 < (a.2 : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
          (one_le_nxClass_X Nm mu ha))
      have hmass :
          (a.2 : ℝ) * paperDyadicY Nm mu a ≤ c.X * c.Y := by
        rw [show c.X = (a.2 : ℝ) by rfl]
        exact mul_le_mul_of_nonneg_left hcard hXpos.le
      have hsqrt :
          Real.sqrt ((a.2 : ℝ) * paperDyadicY Nm mu a) ≤
            Real.sqrt (c.X * c.Y) :=
        Real.sqrt_le_sqrt hmass
      have hden :
          0 < Real.sqrt ((a.2 : ℝ) * paperDyadicY Nm mu a) :=
        Real.sqrt_pos.2
          (mul_pos hXpos (paperDyadicY_pos Nm mu ha))
      simp only [skipXi, paperDyadicSkipXi, if_true]
      exact inv_anti₀ hden hsqrt

private theorem nxClassCluster_localTarget_le_eight_mul_paperTarget
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) (skipped : Bool) :
    ((nxClassCluster ht hroot Nm mu z hz a ha).X *
        Real.sqrt (nxClassCluster ht hroot Nm mu z hz a ha).Y *
        (nxClassCluster ht hroot Nm mu z hz a ha).N⁻¹ ^ 2) *
        skipXi (nxClassCluster ht hroot Nm mu z hz a ha) skipped ≤
      8 * paperDyadicLocalTarget Nm mu a skipped := by
  let c := nxClassCluster ht hroot Nm mu z hz a ha
  have hbase :
      c.X * Real.sqrt c.Y * c.N⁻¹ ^ 2 ≤
        8 * paperDyadicBase Nm mu a :=
    nxClassCluster_base_le_eight_mul_paperDyadicBase
      ht hroot Nm mu z hz ha
  have hxi :
      skipXi c skipped ≤ paperDyadicSkipXi Nm mu a skipped :=
    nxClassCluster_skipXi_le_paperDyadicSkipXi
      ht hroot Nm mu z hz ha skipped
  have hactualXi : 0 ≤ skipXi c skipped := by
    cases skipped <;> simp [skipXi]
  have hpaperBase : 0 ≤ paperDyadicBase Nm mu a := by
    unfold paperDyadicBase
    positivity
  calc
    (c.X * Real.sqrt c.Y * c.N⁻¹ ^ 2) * skipXi c skipped ≤
        (8 * paperDyadicBase Nm mu a) * skipXi c skipped :=
      mul_le_mul_of_nonneg_right hbase hactualXi
    _ ≤ (8 * paperDyadicBase Nm mu a) *
        paperDyadicSkipXi Nm mu a skipped :=
      mul_le_mul_of_nonneg_left hxi (mul_nonneg (by norm_num) hpaperBase)
    _ = 8 * paperDyadicLocalTarget Nm mu a skipped := by
      unfold paperDyadicLocalTarget
      ring

/-- The analytic target built from actual point-cardinalities and the
separation scale `N/2` is bounded by a universal multiple of the exact
dyadic target printed in (5.91).  The constant audit is:

* at most `8` per local factor (`4` from `(N/2)⁻²`, at most `2` from
  replacing `sqrt |L_{N,X}|` by `sqrt Y`; skipped `Ξ` only improves);
* at most `2` for the `1/8`-power volume gain.

Thus `8 · 8 · 2 = 128`. -/
theorem nxClassCluster_mixedTarget_le_paperDyadicPairTarget
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a b : NXClass}
    (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu)
    (skipA skipB : Bool) :
    mixedTarget
        (nxClassCluster ht hroot Nm mu z hz a ha)
        (nxClassCluster ht hroot Nm mu z hz b hb)
        skipA skipB ≤
      128 * paperDyadicPairTarget Nm mu a b skipA skipB := by
  let ca := nxClassCluster ht hroot Nm mu z hz a ha
  let cb := nxClassCluster ht hroot Nm mu z hz b hb
  let localA :=
    (ca.X * Real.sqrt ca.Y * ca.N⁻¹ ^ 2) * skipXi ca skipA
  let localB :=
    (cb.X * Real.sqrt cb.Y * cb.N⁻¹ ^ 2) * skipXi cb skipB
  have hlocalA :
      localA ≤ 8 * paperDyadicLocalTarget Nm mu a skipA :=
    nxClassCluster_localTarget_le_eight_mul_paperTarget
      ht hroot Nm mu z hz ha skipA
  have hlocalB :
      localB ≤ 8 * paperDyadicLocalTarget Nm mu b skipB :=
    nxClassCluster_localTarget_le_eight_mul_paperTarget
      ht hroot Nm mu z hz hb skipB
  have hlocalB0 : 0 ≤ localB := by
    unfold localB
    have hxi : 0 ≤ skipXi cb skipB := by
      cases skipB <;> simp [skipXi]
    have hbase :
        0 ≤ cb.X * Real.sqrt cb.Y * cb.N⁻¹ ^ 2 :=
      mul_nonneg
        (mul_nonneg cb.X_nonneg (Real.sqrt_nonneg _))
        (sq_nonneg _)
    exact mul_nonneg hbase hxi
  have hupperA0 :
      0 ≤ 8 * paperDyadicLocalTarget Nm mu a skipA :=
    mul_nonneg (by norm_num)
      (paperDyadicLocalTarget_nonneg Nm mu a skipA)
  have hlocalPair :
      localA * localB ≤
        64 * (paperDyadicLocalTarget Nm mu a skipA *
          paperDyadicLocalTarget Nm mu b skipB) := by
    calc
      localA * localB ≤
          (8 * paperDyadicLocalTarget Nm mu a skipA) *
            (8 * paperDyadicLocalTarget Nm mu b skipB) :=
        mul_le_mul hlocalA hlocalB hlocalB0 hupperA0
      _ = 64 * (paperDyadicLocalTarget Nm mu a skipA *
          paperDyadicLocalTarget Nm mu b skipB) := by ring
  have hgain :=
    nxClassCluster_forwardGain_le_dyadicForwardGain
      ht hroot Nm mu z hz ha hb
  have hrootTwo :
      (2 : ℝ) ^ (1 / 8 : ℝ) ≤ 2 := by
    calc
      (2 : ℝ) ^ (1 / 8 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := by norm_num
  have hgainTwo :
      forwardGain ca cb ≤
        2 * dyadicForwardGain
          (singleScaleSigma2 Nm mu a)
          (singleScaleSigma2 Nm mu b) := by
    exact hgain.trans
      (mul_le_mul_of_nonneg_right hrootTwo
        (dyadicForwardGain_nonneg _ _))
  have hgain0 : 0 ≤ forwardGain ca cb :=
    forwardGain_nonneg ca cb
  have hupperPair0 :
      0 ≤ 64 * (paperDyadicLocalTarget Nm mu a skipA *
        paperDyadicLocalTarget Nm mu b skipB) :=
    mul_nonneg (by norm_num)
      (mul_nonneg
        (paperDyadicLocalTarget_nonneg Nm mu a skipA)
        (paperDyadicLocalTarget_nonneg Nm mu b skipB))
  have hcombined :
      (localA * localB) * forwardGain ca cb ≤
        (64 * (paperDyadicLocalTarget Nm mu a skipA *
          paperDyadicLocalTarget Nm mu b skipB)) *
          (2 * dyadicForwardGain
            (singleScaleSigma2 Nm mu a)
            (singleScaleSigma2 Nm mu b)) :=
    mul_le_mul hlocalPair hgainTwo hgain0 hupperPair0
  have hmixed :
      mixedTarget ca cb skipA skipB =
        (localA * localB) * forwardGain ca cb := by
    unfold mixedTarget localA localB
    ring
  change mixedTarget ca cb skipA skipB ≤
    128 * paperDyadicPairTarget Nm mu a b skipA skipB
  rw [hmixed]
  unfold paperDyadicPairTarget
  calc
    (localA * localB) * forwardGain ca cb ≤
        (64 * (paperDyadicLocalTarget Nm mu a skipA *
          paperDyadicLocalTarget Nm mu b skipB)) *
          (2 * dyadicForwardGain
            (singleScaleSigma2 Nm mu a)
            (singleScaleSigma2 Nm mu b)) := hcombined
    _ = _ := by ring

/-- Uniform copy-level form of the local estimate (5.91), with the
existential constant outside every tree, class, embedding, scale, skip
choice, and fixed preceding point.  Its left-hand side uses the actual
leaf multiplicities; its right-hand side is the paper's exact dyadic
`X,Y,N,Ξ,P` target. -/
theorem nxCoupledCopyPairSum_le_paperDyadicPairTarget :
    ∃ C : ℝ, 0 < C ∧
      ∀ {t : PlaneTree}
        (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ {a b : NXClass}
          (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu)
          (skipA skipB : Bool) (u : Fin 4 → ℤ),
          nxCoupledCopyPairSum
              ht hroot Nm mu z hz (R : ℝ) ha hb skipA skipB u ≤
            C * paperDyadicPairTarget Nm mu a b skipA skipB := by
  obtain ⟨C, hC, hlocal⟩ :=
    nxClassClusters_mixedPairInner_le_5_91
  refine ⟨512 * C, by positivity, ?_⟩
  intro t ht hroot Nm mu z hz R hR a b ha hb skipA skipB u
  have hcopy :=
    nxCoupledCopyPairSum_le_four_mul_mixedPairInner
      ht hroot Nm mu z hz (R : ℝ) ha hb skipA skipB u
  have hmixed :=
    hlocal ht hroot Nm mu z hz R hR ha hb skipA skipB u
  have htarget :=
    nxClassCluster_mixedTarget_le_paperDyadicPairTarget
      ht hroot Nm mu z hz ha hb skipA skipB
  calc
    nxCoupledCopyPairSum
        ht hroot Nm mu z hz (R : ℝ) ha hb skipA skipB u ≤
      4 * mixedPairInner
        (nxClassCluster ht hroot Nm mu z hz a ha)
        (nxClassCluster ht hroot Nm mu z hz b hb)
        (R : ℝ) skipA skipB u := hcopy
    _ ≤ 4 * (C * mixedTarget
        (nxClassCluster ht hroot Nm mu z hz a ha)
        (nxClassCluster ht hroot Nm mu z hz b hb)
        skipA skipB) :=
      mul_le_mul_of_nonneg_left hmixed (by norm_num)
    _ ≤ 4 * (C * (128 *
        paperDyadicPairTarget Nm mu a b skipA skipB)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htarget hC.le)
        (by norm_num)
    _ = (512 * C) *
        paperDyadicPairTarget Nm mu a b skipA skipB := by ring

private theorem actualP_ratio_le_two_mul_dyadicP_ratio
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {q r : NYClass}
    (hq : q ∈ nyCarrier Nm mu) (hr : r ∈ nyCarrier Nm mu) :
    (nyClassCluster ht hroot Nm mu z hz r hr).P /
        (nyClassCluster ht hroot Nm mu z hz q hq).P ≤
      2 * (dyadicP r / dyadicP q) := by
  let cq := nyClassCluster ht hroot Nm mu z hz q hq
  let cr := nyClassCluster ht hroot Nm mu z hz r hr
  let aq := maxNXAtNY Nm mu q hq
  let ar := maxNXAtNY Nm mu r hr
  have haq : aq ∈ nxCarrier Nm mu :=
    maxNXAtNY_active Nm mu q hq
  have har : ar ∈ nxCarrier Nm mu :=
    maxNXAtNY_active Nm mu r hr
  have hqClass : singleScaleSigma2 Nm mu aq = q :=
    (Finset.mem_filter.mp (maxNXAtNY_mem Nm mu q hq)).2
  have hrClass : singleScaleSigma2 Nm mu ar = r :=
    (Finset.mem_filter.mp (maxNXAtNY_mem Nm mu r hr)).2
  have hcqP : 0 < cq.P :=
    P_pos_of_nonempty
      (nyClassCluster_points_nonempty ht hroot Nm mu z hz q hq)
  have hcrP : 0 < cr.P :=
    P_pos_of_nonempty
      (nyClassCluster_points_nonempty ht hroot Nm mu z hz r hr)
  have hqP : 0 < dyadicP q :=
    dyadicP_pos ht hroot Nm mu z hz hq
  have hrP : 0 < dyadicP r :=
    dyadicP_pos ht hroot Nm mu z hz hr
  have hqUpper :
      dyadicP q ≤ 16 * cq.P := by
    simpa [dyadicP, cq, nyClassCluster, aq, hqClass] using
      nxClassCluster_P_lower ht hroot Nm mu z hz haq
  have hrLower :
      8 * cr.P ≤ dyadicP r := by
    simpa [dyadicP, cr, nyClassCluster, ar, hrClass] using
      nxClassCluster_P_upper ht hroot Nm mu z hz har
  have hcrUpper : cr.P ≤ dyadicP r / 8 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith
  have hcqLower : dyadicP q / 16 ≤ cq.P := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
    nlinarith
  have hratio :
      cr.P / cq.P ≤ (dyadicP r / 8) / (dyadicP q / 16) :=
    div_le_div₀
      (div_nonneg hrP.le (by norm_num))
      hcrUpper
      (div_pos hqP (by norm_num))
      hcqLower
  calc
    cr.P / cq.P ≤
        (dyadicP r / 8) / (dyadicP q / 16) := hratio
    _ = 2 * (dyadicP r / dyadicP q) := by
      field_simp [hqP.ne']
      ring

/-- Representative-only corollary for the maximal-`X` fiber of each
`(N,Y)` class.  The `1/8` gain is the one in (5.87)/(5.91), not the
outer exponent `θ = 1/20` in (5.76).  The constant is exactly the eighth
root of the comparison factor `2`. -/
theorem nyClassCluster_forwardGain_le_dyadicForwardGain
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {q r : NYClass}
    (hq : q ∈ nyCarrier Nm mu) (hr : r ∈ nyCarrier Nm mu) :
    forwardGain
        (nyClassCluster ht hroot Nm mu z hz q hq)
        (nyClassCluster ht hroot Nm mu z hz r hr) ≤
      (2 : ℝ) ^ (1 / 8 : ℝ) * dyadicForwardGain q r := by
  let cq := nyClassCluster ht hroot Nm mu z hz q hq
  let cr := nyClassCluster ht hroot Nm mu z hz r hr
  have hcqP : 0 < cq.P :=
    P_pos_of_nonempty
      (nyClassCluster_points_nonempty ht hroot Nm mu z hz q hq)
  have hcrP : 0 < cr.P :=
    P_pos_of_nonempty
      (nyClassCluster_points_nonempty ht hroot Nm mu z hz r hr)
  have hqP : 0 < dyadicP q :=
    dyadicP_pos ht hroot Nm mu z hz hq
  have hrP : 0 < dyadicP r :=
    dyadicP_pos ht hroot Nm mu z hz hr
  have hratio :
      cr.P / cq.P ≤ 2 * (dyadicP r / dyadicP q) :=
    actualP_ratio_le_two_mul_dyadicP_ratio
      ht hroot Nm mu z hz hq hr
  have hratioActual : 0 ≤ cr.P / cq.P :=
    div_nonneg hcrP.le hcqP.le
  have hratioDyadic : 0 ≤ dyadicP r / dyadicP q :=
    div_nonneg hrP.le hqP.le
  have hpow :
      (cr.P / cq.P) ^ (1 / 8 : ℝ) ≤
        (2 : ℝ) ^ (1 / 8 : ℝ) *
          (dyadicP r / dyadicP q) ^ (1 / 8 : ℝ) := by
    calc
      (cr.P / cq.P) ^ (1 / 8 : ℝ) ≤
          (2 * (dyadicP r / dyadicP q)) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow hratioActual hratio (by norm_num)
      _ = (2 : ℝ) ^ (1 / 8 : ℝ) *
          (dyadicP r / dyadicP q) ^ (1 / 8 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hratioDyadic]
  have hconstant :
      1 ≤ (2 : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by norm_num) (by norm_num)
  unfold forwardGain dyadicForwardGain
  by_cases hdyadic :
      (dyadicP r / dyadicP q) ^ (1 / 8 : ℝ) ≤ 1
  · rw [min_eq_right hdyadic]
    exact (min_le_right _ _).trans hpow
  · have hone :
        1 ≤ (dyadicP r / dyadicP q) ^ (1 / 8 : ℝ) :=
      le_of_not_ge hdyadic
    rw [min_eq_left hone]
    calc
      min 1 ((cr.P / cq.P) ^ (1 / 8 : ℝ)) ≤ 1 :=
        min_le_left _ _
      _ ≤ (2 : ℝ) ^ (1 / 8 : ℝ) := hconstant
      _ = (2 : ℝ) ^ (1 / 8 : ℝ) * 1 := by ring

end XYCluster

end

end Anderson4D
