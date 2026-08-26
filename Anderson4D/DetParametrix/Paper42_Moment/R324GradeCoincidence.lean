import Anderson4D.DetParametrix.Paper42_Moment.R324GradeLedger

/-!
# The σ-grading count from a coincidence count

`R324GradeLedger` reduces clause A to the permutation layer count
`#{τ : grade τ = j} ≤ A^m·(m-j)!`.  This file reduces *that* to the
elementary gluing count

`#{τ : τ realises all coincidences in S} ≤ B^m·(m-|S|)!`,

for a prescribed set `S` of coincidences — which is the shape one
actually proves, by gluing the `|S|` coincident pairs into blocks and
permuting the `m-|S|` blocks.

## The mechanism

Power counting on the collapsed lattice sum
`∑_q ∏ᵢ‖ρ̂(εqᵢ)‖²·∏ⱼ⟨Sⱼ⟩⁻²⟨Sⱼ^τ⟩⁻²` produces one factor `L` per member
of a maximal refinement chain of partitions of `{1,…,m}` whose blocks
are intervals for the identity order *and* for the `τ` order.  Every
proper step of such a chain merges two blocks that are adjacent in both
orders, so the chain length is controlled by the *coincidences* of `τ`:
the positions `i` at which `i` and `i+1` are also neighbours in the
`τ` order.  The trivial chain (the all-singletons partition alone) is
always present, which is the reason for the `+ 1` in `hdom`: the
generic bijection has no coincidence at all and still has grade `1`
(the `m = 4` example `τ = (2,4,1,3)` of `R324CappedCrossGrading`).

That `+1` is affordable: one unit of grade costs one factor `m`, and
`m ≤ 2^m`.  The subset-count constant `B` is likewise affordable: a
prescribed set of `|S|` coincidences may be realised with either
orientation of each glued block, which is a `2^m` overhead at worst.
Both are absorbed into the final constant `4B`.

## Alignment with the proved §5 machine

The factorial layer criterion is not an ad hoc device: the proved
`permSumRHS` of Proposition 5.7 (`PermSum/Statements.lean`) already has
the shape

`C^n·∑_{W ⊆ branches} (n - |W|)!·∏ₗ √(mult l)!·(scale ratios)`,

i.e. a sum over subsets `W` weighted by exactly `(n-|W|)!`, each
element of `W` paying for its factorial with a scale-ratio gain.  So
`(m-j)!` per grade level is the same bookkeeping the paper's §5 uses,
and the downstream of clause A is built to absorb it.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## Factorial bookkeeping for the `+1` offset -/

/-- One extra unit of grade costs one factor `m`. -/
theorem r324Grade_factorial_pred_le {m j : ℕ} (hm : 1 ≤ m) (hj : j ≤ m - 1) :
    (m - (j - 1)).factorial ≤ m * (m - j).factorial := by
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    simpa using Nat.le_mul_of_pos_left _ hm
  · have hsub : m - (j - 1) = (m - j) + 1 := by omega
    rw [hsub, Nat.factorial_succ]
    exact Nat.mul_le_mul_right _ (by omega)

/-! ## The reduction -/

/-- **The σ-grading layer count from a prescribed-coincidence count.**

`coin τ` is the finite set of coincidences of `τ`.  If

* the grade never exceeds `#coincidences + 1`, and
* for every prescribed set `S` of coincidences at most `B^m·(m-|S|)!`
  bijections realise all of them,

then the permutation layer count holds with constant `4B`, hence — via
`r324Grade_layeredAt_of_collapse` — clause A.

The proof is the union bound over the `≤ 2^m` candidate coincidence
sets of the right size, followed by `r324Grade_factorial_pred_le`. -/
theorem r324Grade_permLayerCount_of_subsetCount
    {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {gradeP : Equiv.Perm (Fin m) → ℕ} {B : ℝ}
    (coin : Equiv.Perm (Fin m) → Finset ι)
    (hB : 1 ≤ B) (hm : 1 ≤ m) (hι : Fintype.card ι ≤ m)
    (hgle : ∀ τ : Equiv.Perm (Fin m), gradeP τ ≤ m - 1)
    (hdom : ∀ τ : Equiv.Perm (Fin m), gradeP τ ≤ (coin τ).card + 1)
    (hsub : ∀ S : Finset ι,
      ((((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
          fun τ => S ⊆ coin τ).card : ℕ) : ℝ) ≤
        B ^ m * (((m - S.card).factorial : ℕ) : ℝ)) :
    R324GradePermLayerCount (4 * B) m gradeP := by
  refine ⟨hgle, ?_⟩
  intro j hj
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB
  have hBm : (0 : ℝ) ≤ B ^ m := pow_nonneg hB0 m
  set k : ℕ := j - 1 with hk
  set P : Finset (Finset ι) :=
    Finset.powersetCard k (Finset.univ : Finset ι) with hP
  -- union bound over the candidate coincidence sets
  have hcover :
      ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
          fun τ => gradeP τ = j) ⊆
        P.biUnion fun S =>
          (Finset.univ : Finset (Equiv.Perm (Fin m))).filter
            fun τ => S ⊆ coin τ := by
    intro τ hτ
    have hgj : gradeP τ = j := (Finset.mem_filter.mp hτ).2
    have hkle : k ≤ (coin τ).card := by
      have := hdom τ
      omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hkle
    refine Finset.mem_biUnion.mpr ⟨S, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSsub⟩
  have hcardNat :
      ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
          fun τ => gradeP τ = j).card ≤
        ∑ S ∈ P, ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
          fun τ => S ⊆ coin τ).card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_biUnion_le)
  -- the number of candidate sets is at most `2^m`
  have hPcard : (P.card : ℝ) ≤ (2 : ℝ) ^ m := by
    have hsubset : P ⊆ (Finset.univ : Finset ι).powerset := by
      intro S hS
      exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1
    have h1 : P.card ≤ 2 ^ Fintype.card ι := by
      have := Finset.card_le_card hsubset
      rwa [Finset.card_powerset, Finset.card_univ] at this
    have h2 : (2 : ℕ) ^ Fintype.card ι ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by norm_num) hι
    exact_mod_cast le_trans h1 h2
  -- each candidate set contributes at most `B^m·(m-k)!`
  have hterm : ∀ S ∈ P,
      ((((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
          fun τ => S ⊆ coin τ).card : ℕ) : ℝ) ≤
        B ^ m * (((m - k).factorial : ℕ) : ℝ) := by
    intro S hS
    have hScard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have := hsub S
    rwa [hScard] at this
  have hfac : (((m - k).factorial : ℕ) : ℝ) ≤
      (m : ℝ) * (((m - j).factorial : ℕ) : ℝ) := by
    have := r324Grade_factorial_pred_le (m := m) (j := j) hm hj
    exact_mod_cast this
  have hm2 : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    exact_mod_cast Nat.lt_two_pow_self.le
  have hfacNonneg : (0 : ℝ) ≤ (((m - j).factorial : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  calc
    ((((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
        fun τ => gradeP τ = j).card : ℕ) : ℝ)
        ≤ ∑ S ∈ P, ((((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
            fun τ => S ⊆ coin τ).card : ℕ) : ℝ) := by
          exact_mod_cast hcardNat
    _ ≤ ∑ _S ∈ P, B ^ m * (((m - k).factorial : ℕ) : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (P.card : ℝ) * (B ^ m * (((m - k).factorial : ℕ) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ m * (B ^ m * (((m - k).factorial : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_right hPcard ?_
        exact mul_nonneg hBm (Nat.cast_nonneg _)
    _ ≤ (2 : ℝ) ^ m * (B ^ m * ((m : ℝ) * (((m - j).factorial : ℕ) : ℝ))) := by
        gcongr
    _ ≤ (2 : ℝ) ^ m * (B ^ m * ((2 : ℝ) ^ m * (((m - j).factorial : ℕ) : ℝ))) := by
        gcongr
    _ = (4 * B) ^ m * (((m - j).factorial : ℕ) : ℝ) := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, mul_pow]
        ring

/-! ## The concrete coincidence family -/

/-- The position of `i` in the `τ`-order (junk outside the range). -/
def r324GradePos {m : ℕ} (τ : Equiv.Perm (Fin m)) (i : ℕ) : ℕ :=
  if h : i < m then ((τ.symm ⟨i, h⟩ : Fin m) : ℕ) else 0

/-- **The coincidences of a bijection**: the positions `i < m-1` at
which the neighbouring pair `{i, i+1}` of the identity order is also a
neighbouring pair of the `τ` order.  These are exactly the two-block
merges available at the finest level of the common-interval chain, so
they control the grade. -/
def r324GradeCoincidence {m : ℕ} (τ : Equiv.Perm (Fin m)) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter fun i : Fin m =>
    (i : ℕ) + 1 < m ∧
      (r324GradePos τ ((i : ℕ) + 1) + 1 = r324GradePos τ (i : ℕ) ∨
        r324GradePos τ (i : ℕ) + 1 = r324GradePos τ ((i : ℕ) + 1))

/-- **The remaining combinatorial obligation.**  A prescribed set `S`
of coincidences is realised by at most `2^m·(m-|S|)!` bijections: glue
the `|S|` coincident pairs into blocks (at most `2^m` orientations) and
permute the `≤ m-|S|` blocks.  `S = ∅` is the equality case `m!`. -/
def R324GradeCoincidenceCount (m : ℕ) : Prop :=
  ∀ S : Finset (Fin m),
    ((((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
        fun τ => S ⊆ r324GradeCoincidence τ).card : ℕ) : ℝ) ≤
      (2 : ℝ) ^ m * (((m - S.card).factorial : ℕ) : ℝ)

/-- **The σ-grading count, packaged.**  A grade dominated by the
coincidence count, together with the gluing count, gives the
permutation layer count at constant `8`, hence clause A through
`r324Grade_layeredAt_of_collapse`. -/
theorem r324Grade_permLayerCount_of_coincidence
    {m : ℕ} {gradeP : Equiv.Perm (Fin m) → ℕ} (hm : 1 ≤ m)
    (hgle : ∀ τ : Equiv.Perm (Fin m), gradeP τ ≤ m - 1)
    (hdom : ∀ τ : Equiv.Perm (Fin m),
      gradeP τ ≤ (r324GradeCoincidence τ).card + 1)
    (hcnt : R324GradeCoincidenceCount m) :
    R324GradePermLayerCount 8 m gradeP := by
  have h :=
    r324Grade_permLayerCount_of_subsetCount (m := m) (ι := Fin m)
      (gradeP := gradeP) (B := 2) r324GradeCoincidence
      (by norm_num) hm (by simp) hgle hdom hcnt
  have h8 : (4 : ℝ) * 2 = 8 := by norm_num
  rwa [h8] at h

end

end Anderson4D
