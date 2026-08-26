import Anderson4D.PermSum.SingleScaleSetup
import Anderson4D.Combinatorics.SequenceCount

/-!
# The outer `P`-word gain in the single-scale estimate

This file isolates the `P`-word gain estimate (5.77), which is the sequence
input used in (5.76), including the paper's indexing convention.  A word of
length `k + 2` has `k + 1` adjacent edges.  The first edge is omitted because
the product in (5.76) starts at the one-based index `j = 2`;
`E : Finset (Fin k)` records at most 99 further omitted edges and is shifted
one place to the right.  Thus the bounded-skip form of Lemma 5.13 is used
with the honest total budget `100`.

The active `P` values are first replaced by the finite subtype of
`pCarrier`.  Only that subtype is enumerated by `Fin ν`.  Its dyadic
exponents are injective because the *values* in the carrier are distinct;
repeated occurrences of a `P` value in a word remain arbitrary repetitions
of the corresponding `Fin ν` index.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## The active `P` carrier and its dyadic enumeration -/

/-- Number `ν` of distinct active dyadic `P` values. -/
abbrev activePCount {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) : ℕ :=
  Fintype.card (ActivePClass Nm mu)

/-- A fixed enumeration of the distinct active `P` values. -/
noncomputable def activePEnumeration {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) :
    Fin (activePCount Nm mu) ≃ ActivePClass Nm mu :=
  (Fintype.equivFin (ActivePClass Nm mu)).symm

/-- On the active carrier, taking `Nat.log 2` recovers the dyadic value. -/
theorem activeP_eq_pow_log {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (P : ActivePClass Nm mu) :
    P.1 = 2 ^ Nat.log 2 P.1 := by
  obtain ⟨e, he⟩ := pClass_dyadic Nm mu P.2
  rw [he, Nat.log_pow Nat.one_lt_two]

/-- Integer exponent attached to the enumerated dyadic value. -/
noncomputable def activePExponent {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (i : Fin (activePCount Nm mu)) : ℤ :=
  Nat.log 2 (activePEnumeration Nm mu i).1

/--
The exponent family, rather than a word containing repeated exponent
indices, is injective.
-/
theorem activePExponent_injective {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) :
    Function.Injective (activePExponent Nm mu) := by
  intro i j hij
  apply (activePEnumeration Nm mu).injective
  apply Subtype.ext
  have hlog :
      Nat.log 2 (activePEnumeration Nm mu i).1 =
        Nat.log 2 (activePEnumeration Nm mu j).1 := by
    simpa [activePExponent] using hij
  calc
    (activePEnumeration Nm mu i).1 =
        2 ^ Nat.log 2 (activePEnumeration Nm mu i).1 :=
      activeP_eq_pow_log Nm mu _
    _ = 2 ^ Nat.log 2 (activePEnumeration Nm mu j).1 := by rw [hlog]
    _ = (activePEnumeration Nm mu j).1 :=
      (activeP_eq_pow_log Nm mu _).symm

/-- The enumerated natural `P` is exactly the corresponding real `zpow`. -/
theorem activePEnumeration_cast_eq_zpow {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (i : Fin (activePCount Nm mu)) :
    ((activePEnumeration Nm mu i).1 : ℝ) =
      (2 : ℝ) ^ activePExponent Nm mu i := by
  rw [activeP_eq_pow_log Nm mu (activePEnumeration Nm mu i)]
  simp [activePExponent, Nat.cast_pow]

/--
There are no more distinct active `P` values than word positions.  The three
classification maps can only decrease cardinality, and every leaf
multiplicity is at least two (in particular at least one).
-/
theorem activePCount_le_totalMultiplicity {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    activePCount Nm mu ≤ totalMultiplicity mu := by
  have h : (pCarrier Nm mu).card ≤ totalMultiplicity mu := by
    calc
      (pCarrier Nm mu).card ≤ (nyCarrier Nm mu).card :=
        Finset.card_image_le
      _ ≤ (nxCarrier Nm mu).card :=
        Finset.card_image_le
      _ ≤ (Finset.univ : Finset (HeppLeaf t)).card :=
        Finset.card_image_le
      _ = ∑ _l : HeppLeaf t, 1 := by simp
      _ ≤ ∑ l : HeppLeaf t, leafMultiplicity mu l := by
        exact Finset.sum_le_sum fun l _ =>
          (show 1 ≤ leafMultiplicity mu l by
            unfold leafMultiplicity
            exact le_trans (by omega) (mu.two_le l.1 l.2))
      _ = totalMultiplicity mu := rfl
  simpa using h

/-- Every paper word has length at least two. -/
theorem two_le_totalMultiplicity {t : PlaneTree} (mu : Multiplicities t) :
    2 ≤ totalMultiplicity mu := by
  have hcard : 1 ≤ Fintype.card (HeppLeaf t) := by
    rw [Fintype.card_coe, card_Leaves_eq_leafCount]
    obtain ⟨cs⟩ := t
    exact le_max_left 1 (leafCountList cs)
  calc
    2 ≤ 2 * Fintype.card (HeppLeaf t) := by omega
    _ = ∑ _l : HeppLeaf t, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ l : HeppLeaf t, leafMultiplicity mu l := by
      exact Finset.sum_le_sum fun l _ => mu.two_le l.1 l.2
    _ = totalMultiplicity mu := rfl

/-! ## The edge shift in (5.76) -/

/-- Shift a tail edge one position to the right in the full edge list. -/
def outerTailEdgeEmbedding (k : ℕ) : Fin k ↪ Fin (k + 1) where
  toFun := Fin.succ
  inj' := Fin.succ_injective k

@[simp] theorem outerTailEdgeEmbedding_ne_zero {k : ℕ} (i : Fin k) :
    outerTailEdgeEmbedding k i ≠ (0 : Fin (k + 1)) := by
  intro h
  have hv := congrArg Fin.val h
  simp [outerTailEdgeEmbedding] at hv

/--
The full exception set: the first edge, omitted because the product in
(5.76) starts at `j = 2`, together with the shifted additional exceptions.
-/
def outerGainExceptions {k : ℕ} (E : Finset (Fin k)) :
    Finset (Fin (k + 1)) :=
  insert 0 (E.map (outerTailEdgeEmbedding k))

@[simp] theorem mem_outerGainExceptions_zero {k : ℕ}
    (E : Finset (Fin k)) :
    (0 : Fin (k + 1)) ∈ outerGainExceptions E := by
  simp [outerGainExceptions]

@[simp] theorem mem_outerGainExceptions_succ {k : ℕ}
    (E : Finset (Fin k)) (j : Fin k) :
    j.succ ∈ outerGainExceptions E ↔ j ∈ E := by
  simp [outerGainExceptions, outerTailEdgeEmbedding]

theorem card_outerGainExceptions {k : ℕ} (E : Finset (Fin k)) :
    (outerGainExceptions E).card = E.card + 1 := by
  simp [outerGainExceptions, outerTailEdgeEmbedding]

theorem card_outerGainExceptions_le_hundred {k : ℕ}
    {E : Finset (Fin k)} (hE : E.card ≤ 99) :
    (outerGainExceptions E).card ≤ 100 := by
  rw [card_outerGainExceptions]
  omega

/--
After removing the first edge, the remaining full edge indices are exactly
the successors of the tail indices not in `E`.
-/
theorem fullEdges_diff_outerGainExceptions {k : ℕ}
    (E : Finset (Fin k)) :
    (Finset.univ : Finset (Fin (k + 1))) \ outerGainExceptions E =
      ((Finset.univ : Finset (Fin k)) \ E).map
        (outerTailEdgeEmbedding k) := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [outerGainExceptions]
  · simp [outerGainExceptions, outerTailEdgeEmbedding]

/-- Product-level form of the one-place edge-index shift. -/
theorem prod_diff_outerGainExceptions_eq_tail {k : ℕ}
    (E : Finset (Fin k)) (f : Fin (k + 1) → ℝ) :
    (∏ j ∈ Finset.univ \ outerGainExceptions E, f j) =
      ∏ i ∈ Finset.univ \ E, f i.succ := by
  rw [fullEdges_diff_outerGainExceptions]
  simp [outerTailEdgeEmbedding]

/-! ## The rectangular sequence estimate at `θ = 1/20` -/

/--
Paper (5.77), in its exact rectangular form.

The word has length `k + 2`, while `ν` is only the number of distinct
dyadic values.  Entries of a word may repeat.  The first edge and at most
99 additional tail edges are omitted, so Lemma 5.13 is invoked with budget
100.  The constant is outside all data quantifiers.
-/
theorem outerGain_code_sum_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (k ν : ℕ) (e : Fin ν → ℤ),
        ν ≤ k + 2 → Function.Injective e →
        ∀ E : Finset (Fin k), E.card ≤ 99 →
          ∑ x : Fin (k + 2) → Fin ν,
            ∏ j ∈ Finset.univ \ outerGainExceptions E,
              min 1 (((2 : ℝ) ^ e (x j.succ) /
                (2 : ℝ) ^ e (x j.castSucc)) ^ (1 / 20 : ℝ))
            ≤ C ^ (k + 2) := by
  obtain ⟨C, hC, hbound⟩ :=
    sum_min_ratio_pow_skip_le_rect (1 / 20 : ℝ) (by norm_num) 100
  refine ⟨C, hC, ?_⟩
  intro k ν e hν he E hE
  have hν' : ν ≤ (k + 1) + 1 := by omega
  have hskip : (outerGainExceptions E).card ≤ 100 :=
    card_outerGainExceptions_le_hundred hE
  simpa only [Nat.add_assoc] using
    hbound (k + 1) ν e hν' he (outerGainExceptions E) hskip

/-! ## Reindexing the actual paper carrier -/

/-- Pointwise enumeration equivalence, used to reindex whole `P` words. -/
noncomputable def activePWordEquiv {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (M : ℕ) :
    (Fin M → Fin (activePCount Nm mu)) ≃
      (Fin M → ActivePClass Nm mu) where
  toFun x := fun j => activePEnumeration Nm mu (x j)
  invFun w := fun j => (activePEnumeration Nm mu).symm (w j)
  left_inv x := by
    funext j
    simp
  right_inv w := by
    funext j
    simp

/-- The actual `min(1,(P_{j+1}/P_j)^{1/20})` factor in (5.76). -/
noncomputable def outerPWordGain {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t} {k : ℕ}
    (w : Fin (k + 2) → ActivePClass Nm mu)
    (j : Fin (k + 1)) : ℝ :=
  min 1 (((((w j.succ).1 : ℕ) : ℝ) /
    (((w j.castSucc).1 : ℕ) : ℝ)) ^ (1 / 20 : ℝ))

/--
The same gain indexed directly by the paper's tail positions:
`i = 0` represents the one-based edge `j = 2`.
-/
noncomputable def outerPWordTailGain {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t} {k : ℕ}
    (w : Fin (k + 2) → ActivePClass Nm mu)
    (i : Fin k) : ℝ :=
  outerPWordGain w i.succ

/--
Actual-carrier form of (5.77).

This is the assembly-facing theorem: the sum is over words in the subtype
of active natural `P` values, and the factors are literal ratios of those
values.  The only cardinality assumption is the necessary rectangular one
`ν ≤ k + 2`; it is discharged for the paper word by
`activePCount_le_totalMultiplicity`.
-/
theorem outerGain_activeP_sum_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (k : ℕ), activePCount Nm mu ≤ k + 2 →
        ∀ E : Finset (Fin k), E.card ≤ 99 →
          ∑ w : Fin (k + 2) → ActivePClass Nm mu,
            ∏ j ∈ Finset.univ \ outerGainExceptions E,
              outerPWordGain w j
            ≤ C ^ (k + 2) := by
  obtain ⟨C, hC, hcode⟩ := outerGain_code_sum_le
  refine ⟨C, hC, ?_⟩
  intro t Nm mu k hν E hE
  have hbound :=
    hcode k (activePCount Nm mu) (activePExponent Nm mu)
      hν (activePExponent_injective Nm mu) E hE
  let wordEquiv := activePWordEquiv Nm mu (k + 2)
  have hreindex :
      (∑ x : Fin (k + 2) → Fin (activePCount Nm mu),
        ∏ j ∈ Finset.univ \ outerGainExceptions E,
          min 1 (((2 : ℝ) ^ activePExponent Nm mu (x j.succ) /
            (2 : ℝ) ^ activePExponent Nm mu (x j.castSucc)) ^
              (1 / 20 : ℝ))) =
        ∑ w : Fin (k + 2) → ActivePClass Nm mu,
          ∏ j ∈ Finset.univ \ outerGainExceptions E,
            outerPWordGain w j := by
    apply Fintype.sum_equiv wordEquiv
    intro x
    apply Finset.prod_congr rfl
    intro j hj
    rw [← activePEnumeration_cast_eq_zpow Nm mu (x j.succ),
      ← activePEnumeration_cast_eq_zpow Nm mu (x j.castSucc)]
    simp only [wordEquiv, activePWordEquiv, outerPWordGain,
      Equiv.coe_fn_mk]
  rw [← hreindex]
  exact hbound

/--
Literal tail-indexed form of the (5.77) gain used in (5.76): a length-`k+2`
word, product over its one-based edges `j = 2, ..., k+1`, with at most 99 of
those factors removed.
-/
theorem outerGain_activeP_tail_sum_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (k : ℕ), activePCount Nm mu ≤ k + 2 →
        ∀ E : Finset (Fin k), E.card ≤ 99 →
          ∑ w : Fin (k + 2) → ActivePClass Nm mu,
            ∏ i ∈ Finset.univ \ E, outerPWordTailGain w i
            ≤ C ^ (k + 2) := by
  obtain ⟨C, hC, hbound⟩ := outerGain_activeP_sum_le
  refine ⟨C, hC, ?_⟩
  intro t Nm mu k hν E hE
  calc
    (∑ w : Fin (k + 2) → ActivePClass Nm mu,
        ∏ i ∈ Finset.univ \ E, outerPWordTailGain w i) =
        ∑ w : Fin (k + 2) → ActivePClass Nm mu,
          ∏ j ∈ Finset.univ \ outerGainExceptions E,
            outerPWordGain w j := by
      apply Fintype.sum_congr
      intro w
      rw [prod_diff_outerGainExceptions_eq_tail]
      rfl
    _ ≤ C ^ (k + 2) := hbound Nm mu k hν E hE

/--
Paper specialization: choose the word length to be the total multiplicity.

Writing the length as `(m - 2) + 2` keeps the first-edge shift definitionally
transparent.  `two_le_totalMultiplicity` proves that this is exactly `m`,
and no extra hypothesis beyond the project data is needed.
-/
theorem outerGain_totalMultiplicity_sum_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let k := totalMultiplicity mu - 2
        ∀ E : Finset (Fin k), E.card ≤ 99 →
          ∑ w : Fin (k + 2) → ActivePClass Nm mu,
            ∏ j ∈ Finset.univ \ outerGainExceptions E,
              outerPWordGain w j
            ≤ C ^ totalMultiplicity mu := by
  obtain ⟨C, hC, hbound⟩ := outerGain_activeP_sum_le
  refine ⟨C, hC, ?_⟩
  intro t Nm mu
  dsimp only
  intro E hE
  have htwo : 2 ≤ totalMultiplicity mu := two_le_totalMultiplicity mu
  have hν :
      activePCount Nm mu ≤ (totalMultiplicity mu - 2) + 2 := by
    calc
      activePCount Nm mu ≤ totalMultiplicity mu :=
        activePCount_le_totalMultiplicity Nm mu
      _ = (totalMultiplicity mu - 2) + 2 :=
        (Nat.sub_add_cancel htwo).symm
  have h :=
    hbound Nm mu (totalMultiplicity mu - 2) hν E hE
  simpa only [Nat.sub_add_cancel htwo] using h

/-- Total-multiplicity specialization of the literal tail-indexed theorem. -/
theorem outerGain_totalMultiplicity_tail_sum_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let k := totalMultiplicity mu - 2
        ∀ E : Finset (Fin k), E.card ≤ 99 →
          ∑ w : Fin (k + 2) → ActivePClass Nm mu,
            ∏ i ∈ Finset.univ \ E, outerPWordTailGain w i
            ≤ C ^ totalMultiplicity mu := by
  obtain ⟨C, hC, hbound⟩ := outerGain_activeP_tail_sum_le
  refine ⟨C, hC, ?_⟩
  intro t Nm mu
  dsimp only
  intro E hE
  have htwo : 2 ≤ totalMultiplicity mu := two_le_totalMultiplicity mu
  have hν :
      activePCount Nm mu ≤ (totalMultiplicity mu - 2) + 2 := by
    calc
      activePCount Nm mu ≤ totalMultiplicity mu :=
        activePCount_le_totalMultiplicity Nm mu
      _ = (totalMultiplicity mu - 2) + 2 :=
        (Nat.sub_add_cancel htwo).symm
  have h :=
    hbound Nm mu (totalMultiplicity mu - 2) hν E hE
  simpa only [Nat.sub_add_cancel htwo] using h

end

end Anderson4D
