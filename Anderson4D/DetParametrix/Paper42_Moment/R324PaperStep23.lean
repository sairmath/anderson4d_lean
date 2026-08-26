import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep1
import Anderson4D.DetParametrix.Paper42_Moment.R324BlockCollapse
import Anderson4D.Continuum.SingularConv
import Anderson4D.Continuum.SingularChain

/-!
# Paper §4.2, Steps 2 and 3: the second moment

Paper: R-324 — §4.2 Steps 2–3 — interval structure, positional count, nested chain

This file transcribes **Steps 2 and 3 of Section 4.2** of
arXiv:2607.10105v1 (pages 19–20) literally, in the paper's own order,
continuing `R324PaperStep1` (Step 1).

**Step 2.**
* `r324Step2_wick_regroup` — (a) by Wick, summing over `(κ₊, κ₋, π)` is
  summing over full pairings `κ′` of `[1, 2m]`.
* `isRelFullyPaired_univ_iff` — (b) Definition 3.1 / Proposition 3.2 at the
  start of the extraction.
* `card_intervalConfigs_le`, `card_intervalConfigs_two_mul_le` — (c)
  "we may fix the positions of these subintervals at `O(C^m)` cost", with
  `C = 16`.  This is the *entire* combinatorial cost of §4.2, and it is a
  purely positional count.
* (d)–(f) — (4.18), the successive removal of each `I_i` gaining `Cλ` and
  introducing `H` with `|H| ≲ |z|⁻²`, and only then taking absolute values
  to reach (4.19) — are the §4.1 iteration, recorded as the single named
  hypothesis `R324Step23Reduction` (exactly as `R324Step1Reduction`
  records it for Step 1).

**Step 3.**
* `r324Step3_external_legs` — (a) integrating in `(x, y, z, w)` yields
  constants, giving (4.20).
* `r324Step3_fullyPaired_straddles`, `r324Step3_strict_nested` — (b) the
  key structural lemma: since the pairing `κ₀` induces on `[1, p]` and on
  `[p+1, p+q]` is primitive **and not full**, every fully paired
  subinterval contains `{p, p+1}`, and any two of them are equal or
  strictly nested.  This is the paper's
  `1 ≤ a_t < ⋯ < a₁ ≤ p < p+1 ≤ b₁ < ⋯ < b_t ≤ p+q`, and it is what
  replaces every form of grading or per-contraction budget.
* `exists_r324Step3_elementaryEightDim_le` — (c) the elementary
  eight-dimensional integral that removes `[a₁, b₁]` and reassembles the
  structure of (4.20).
* `r324Step3_chain_induction` — (d) the induction along the nested chain.
* `r324Step23_output_identity`, `exists_r324Step23_bound` — the last line,
`(Cλ)^{2m}|log ε|⁻¹ ≤ λ_ε² · C (Cλ)^{2m-2}`, i.e. (3.24) with `1` on the
right, in the form used by the downstream estimates.

Every analytic input is a proved theorem:
`momentContractionEquivFullPairing` (the Wick regrouping),
`exists_r324ProperInsertedConvolution_le` (the elementary eight-dimensional
integral), `integral_invSqKer_sub_left` (the external legs) and
`exists_integral_primitiveInsertedMajorant_le` (the last application
of (4.4)).
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Step 2(a): Wick — the `(κ₊, κ₋, π)` sum is a full-pairing sum -/

/-- **Step 2(a).**  "Summing over `(κ₊, κ₋, π)` is equivalent to summing over
full pairings `κ′` of `[1, 2m]`, where `κ′ = κ₊ ∪ κ₋ ∪ (∪_i {i, π(i)})`."
The gluing map is `momentCombinedPairing` and the equivalence is
`momentContractionEquivFullPairing`. -/
theorem r324Step2_wick_regroup {m : ℕ} {A : Type*} [AddCommMonoid A]
    (F : PartialPairing (Fin (2 * m)) → A) :
    (∑ κp : PartialPairing (Fin m), ∑ κm : PartialPairing (Fin m),
        ∑ π : κp.singles ≃ κm.singles,
          F (momentCombinedPairing κp κm π)) =
      ∑ κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull}, F κ.1 := by
  rw [← sum_momentContractions_eq_nested m
    (fun e => F (momentCombinedPairing e.1 e.2.1 e.2.2))]
  exact Fintype.sum_equiv (momentContractionEquivFullPairing m) _ _ fun _ => rfl

/-! ## Step 2(c): fixing the positions of the subintervals costs `O(C^m)`

The paper: "we may fix the positions of these subintervals at `O(C^m)`
cost".  This is a purely *positional* count.  The blocks `Ĩ_i` that (4.18)
positions are pairwise disjoint subintervals of `[1, 2m]` — that is exactly
what the variable product `∏_{j ∈ Ĩ_0} dx_j · ∏_i ∏_{j ∈ Ĩ_i} dx_j` of
(4.18) asserts — and the number of such configurations is at most
`4^{2m} = 16^m`.  Nothing about pairings or permutations enters: the count
below is a statement about *positions only*. -/

/-- A *positional configuration*: a finite family of pairwise disjoint
nonempty subintervals of `[1, N]`, each recorded by its endpoint pair
`(ℓ_i, r_i)`. -/
def IsIntervalConfig {N : ℕ} (F : Finset (Fin N × Fin N)) : Prop :=
  (∀ p ∈ F, p.1 ≤ p.2) ∧
    ∀ p ∈ F, ∀ q ∈ F, p ≠ q →
      Disjoint (Finset.Icc p.1 p.2) (Finset.Icc q.1 q.2)

instance {N : ℕ} (F : Finset (Fin N × Fin N)) : Decidable (IsIntervalConfig F) :=
  decidable_of_iff
    ((∀ p ∈ F, p.1 ≤ p.2) ∧
      ∀ p ∈ F, ∀ q ∈ F, p ≠ q →
        Disjoint (Finset.Icc p.1 p.2) (Finset.Icc q.1 q.2)) Iff.rfl

/-- All positional configurations inside `[1, N]`. -/
def intervalConfigs (N : ℕ) : Finset (Finset (Fin N × Fin N)) :=
  {F | IsIntervalConfig F}

@[simp]
theorem mem_intervalConfigs {N : ℕ} {F : Finset (Fin N × Fin N)} :
    F ∈ intervalConfigs N ↔ IsIntervalConfig F := by
  simp [intervalConfigs]

/-- In a configuration, an interval is determined by its left endpoint
together with the set of right endpoints: the right endpoint of the
interval starting at `a` is the least right endpoint `≥ a`.  This is the
only content of the positional count. -/
private theorem intervalConfig_subset {N : ℕ} {F F' : Finset (Fin N × Fin N)}
    (hF : IsIntervalConfig F) (hF' : IsIntervalConfig F')
    (hl : F.image Prod.fst = F'.image Prod.fst)
    (hr : F.image Prod.snd = F'.image Prod.snd) : F ⊆ F' := by
  intro p hp
  obtain ⟨q, hq, hq1⟩ :
      ∃ q ∈ F', q.1 = p.1 := by
    have : p.1 ∈ F'.image Prod.fst := by
      rw [← hl]; exact Finset.mem_image_of_mem _ hp
    obtain ⟨q, hq, hq1⟩ := Finset.mem_image.mp this
    exact ⟨q, hq, hq1⟩
  have hp12 : p.1 ≤ p.2 := hF.1 p hp
  have hq12 : q.1 ≤ q.2 := hF'.1 q hq
  have hsnd : p.2 = q.2 := by
    rcases lt_trichotomy p.2 q.2 with hlt | heq | hgt
    · -- a shorter interval of `F'` would have to end inside `[q.1, q.2]`
      obtain ⟨r, hrmem, hr2⟩ : ∃ r ∈ F', r.2 = p.2 := by
        have : p.2 ∈ F'.image Prod.snd := by
          rw [← hr]; exact Finset.mem_image_of_mem _ hp
        obtain ⟨r, hrmem, hr2⟩ := Finset.mem_image.mp this
        exact ⟨r, hrmem, hr2⟩
      have hrq : r ≠ q := by
        intro h; rw [h] at hr2; exact absurd hr2 (ne_of_gt hlt)
      have hr12 : r.1 ≤ r.2 := hF'.1 r hrmem
      set x : Fin N := max r.1 q.1 with hx
      have hxr : x ∈ Finset.Icc r.1 r.2 := by
        refine Finset.mem_Icc.mpr ⟨le_max_left _ _, ?_⟩
        exact max_le hr12 (by rw [hq1, hr2]; exact hp12)
      have hxq : x ∈ Finset.Icc q.1 q.2 := by
        refine Finset.mem_Icc.mpr ⟨le_max_right _ _, ?_⟩
        exact max_le (le_trans hr12 (by rw [hr2]; exact hlt.le)) hq12
      exact absurd (Finset.disjoint_left.mp (hF'.2 r hrmem q hq hrq) hxr) (not_not.mpr hxq)
    · exact heq
    · obtain ⟨s, hsmem, hs2⟩ : ∃ s ∈ F, s.2 = q.2 := by
        have : q.2 ∈ F.image Prod.snd := by
          rw [hr]; exact Finset.mem_image_of_mem _ hq
        obtain ⟨s, hsmem, hs2⟩ := Finset.mem_image.mp this
        exact ⟨s, hsmem, hs2⟩
      have hsp : s ≠ p := by
        intro h; rw [h] at hs2; exact absurd hs2 (ne_of_gt hgt)
      have hs12 : s.1 ≤ s.2 := hF.1 s hsmem
      set x : Fin N := max s.1 p.1 with hx
      have hxs : x ∈ Finset.Icc s.1 s.2 := by
        refine Finset.mem_Icc.mpr ⟨le_max_left _ _, ?_⟩
        exact max_le hs12 (by rw [hs2, ← hq1]; exact hq12)
      have hxp : x ∈ Finset.Icc p.1 p.2 := by
        refine Finset.mem_Icc.mpr ⟨le_max_right _ _, ?_⟩
        exact max_le (le_trans hs12 (by rw [hs2]; exact hgt.le)) hp12
      exact absurd (Finset.disjoint_left.mp (hF.2 s hsmem p hp hsp) hxs) (not_not.mpr hxp)
  have : p = q := Prod.ext hq1.symm hsnd
  rw [this]; exact hq

/-- A positional configuration is determined by its set of left endpoints
together with its set of right endpoints. -/
theorem intervalConfig_eq_of_images {N : ℕ} {F F' : Finset (Fin N × Fin N)}
    (hF : IsIntervalConfig F) (hF' : IsIntervalConfig F')
    (hl : F.image Prod.fst = F'.image Prod.fst)
    (hr : F.image Prod.snd = F'.image Prod.snd) : F = F' :=
  Finset.Subset.antisymm (intervalConfig_subset hF hF' hl hr)
    (intervalConfig_subset hF' hF hl.symm hr.symm)

/-- **Step 2(c), the positional count.**  There are at most `4^N`
configurations of pairwise disjoint subintervals of `[1, N]`. -/
theorem card_intervalConfigs_le (N : ℕ) :
    (intervalConfigs N).card ≤ 4 ^ N := by
  have hinj :
      Set.InjOn (fun F : Finset (Fin N × Fin N) =>
        (F.image Prod.fst, F.image Prod.snd)) (intervalConfigs N) := by
    intro F hF F' hF' h
    exact intervalConfig_eq_of_images (mem_intervalConfigs.mp hF)
      (mem_intervalConfigs.mp hF') (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hcard :=
    Finset.card_le_card_of_injOn
      (fun F : Finset (Fin N × Fin N) => (F.image Prod.fst, F.image Prod.snd))
      (fun F _ => Finset.mem_univ _) hinj
  refine hcard.trans ?_
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_finset,
    Fintype.card_fin, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]

/-- **Step 2(c) at the doubled carrier.**  Inside `[1, 2m]` the positional
cost is `C^m` with `C = 16`; this is the paper's `O(C^m)`, and it is the
*entire* combinatorial cost of §4.2. -/
theorem card_intervalConfigs_two_mul_le (m : ℕ) :
    (intervalConfigs (2 * m)).card ≤ 16 ^ m := by
  refine (card_intervalConfigs_le (2 * m)).trans ?_
  rw [pow_mul]
  norm_num

/-! ## Step 2(b): Definition 3.1 at the start of the extraction

Before any removal the Def 3.1 relative notion `IsRelFullyPaired κ univ a b`
of "fully paired subinterval" (Combinatorics/PairingExtract) is the absolute
notion `IsFullyPairedOn κ (Finset.Icc a b)` used throughout Step 3. -/

/-- **Step 2(b).**  Definition 3.1's fully paired subintervals of the full
index range are exactly the fully paired `Finset.Icc a b`. -/
theorem isRelFullyPaired_univ_iff {m : ℕ} {κ : PartialPairing (Fin m)}
    (a b : Fin m) :
    IsRelFullyPaired κ Finset.univ a b ↔
      a ≤ b ∧ IsFullyPairedOn κ (Finset.Icc a b) := by
  constructor
  · rintro ⟨-, -, hab, hfp⟩
    exact ⟨hab, by rwa [relIcc_univ] at hfp⟩
  · rintro ⟨hab, hfp⟩
    exact ⟨Finset.mem_univ _, Finset.mem_univ _, hab, by rwa [relIcc_univ]⟩

/-! ## Step 3(b): the key structural lemma — the surviving intervals are nested

After Step 2 the remaining variables are `{x_1, …, x_p}` (from the left
copy) and `{x_{p+1}, …, x_{p+q}}` (from the right copy), carrying the
pairing `κ₀`.  "By our construction, the partial pairing that `κ₀` induces
on `[1, p]` and on `[p+1, p+q]` must both be primitive **and not full**."

`r324SplitBlockLeft` / `r324SplitBlockRight` are the two blocks and
`R324SidePrimitiveNotFull` is the paper's hypothesis on each of them. -/

/-- The left block `[1, p]` of the split index set `[1, p+q]`. -/
def r324SplitBlockLeft (n p : ℕ) : Finset (Fin n) :=
  {i | (i : ℕ) < p}

/-- The right block `[p+1, p+q]` of the split index set `[1, p+q]`. -/
def r324SplitBlockRight (n p : ℕ) : Finset (Fin n) :=
  {i | p ≤ (i : ℕ)}

@[simp]
theorem mem_r324SplitBlockLeft {n p : ℕ} {i : Fin n} :
    i ∈ r324SplitBlockLeft n p ↔ (i : ℕ) < p := by
  simp [r324SplitBlockLeft]

@[simp]
theorem mem_r324SplitBlockRight {n p : ℕ} {i : Fin n} :
    i ∈ r324SplitBlockRight n p ↔ p ≤ (i : ℕ) := by
  simp [r324SplitBlockRight]

/-- **The paper's hypothesis on each half.**  The pairing induced by `κ` on
the block `B` is *primitive* (every fully paired subinterval of `B` is all
of `B`) and *not full* (`B` itself is not fully paired). -/
def R324SidePrimitiveNotFull {n : ℕ} (κ : PartialPairing (Fin n))
    (B : Finset (Fin n)) : Prop :=
  (∀ a b : Fin n, a ≤ b → Finset.Icc a b ⊆ B →
      IsFullyPairedOn κ (Finset.Icc a b) → Finset.Icc a b = B) ∧
    ¬ IsFullyPairedOn κ B

/-- Primitive *and not full* means: **no** nonempty subinterval of the block
is fully paired. -/
theorem R324SidePrimitiveNotFull.not_isFullyPairedOn {n : ℕ}
    {κ : PartialPairing (Fin n)} {B : Finset (Fin n)}
    (h : R324SidePrimitiveNotFull κ B) {a b : Fin n} (hab : a ≤ b)
    (hsub : Finset.Icc a b ⊆ B) : ¬ IsFullyPairedOn κ (Finset.Icc a b) := by
  intro hfp
  exact h.2 (h.1 a b hab hsub hfp ▸ hfp)

/-- **Step 3(b), first half.**  Every fully paired subinterval of `κ₀`
contains the split pair `{p, p+1}`: it starts in the left block and ends in
the right block. -/
theorem r324Step3_fullyPaired_straddles {n p : ℕ} {κ : PartialPairing (Fin n)}
    (hL : R324SidePrimitiveNotFull κ (r324SplitBlockLeft n p))
    (hR : R324SidePrimitiveNotFull κ (r324SplitBlockRight n p))
    {a b : Fin n} (hab : a ≤ b)
    (hfp : IsFullyPairedOn κ (Finset.Icc a b)) :
    (a : ℕ) < p ∧ p ≤ (b : ℕ) := by
  constructor
  · by_contra hpa
    refine hR.not_isFullyPairedOn hab (fun i hi => ?_) hfp
    have := (Finset.mem_Icc.mp hi).1
    exact mem_r324SplitBlockRight.mpr (le_trans (not_lt.mp hpa) this)
  · by_contra hpb
    refine hL.not_isFullyPairedOn hab (fun i hi => ?_) hfp
    have := (Finset.mem_Icc.mp hi).2
    exact mem_r324SplitBlockLeft.mpr (lt_of_le_of_lt this (not_le.mp hpb))

/-- **No left overhang.**  If one fully paired subinterval starts strictly
before another and does not end after it, the part sticking out on the left
is again a fully paired subinterval, and it lies entirely inside the left
block — which Step 3(b) forbids. -/
private theorem r324Step3_no_left_part {n p : ℕ} {κ : PartialPairing (Fin n)}
    (hL : R324SidePrimitiveNotFull κ (r324SplitBlockLeft n p))
    (hR : R324SidePrimitiveNotFull κ (r324SplitBlockRight n p))
    {a₁ b₁ a₂ b₂ : Fin n} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hf₁ : IsFullyPairedOn κ (Finset.Icc a₁ b₁))
    (hf₂ : IsFullyPairedOn κ (Finset.Icc a₂ b₂))
    (ha : a₁ < a₂) (hb : b₁ ≤ b₂) : False := by
  set A : Finset (Fin n) := Finset.Icc a₁ b₁ with hA
  set B : Finset (Fin n) := Finset.Icc a₂ b₂ with hB
  have ha₁ : a₁ ∈ A \ B := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl _, h₁⟩, ?_⟩
    intro hmem
    exact absurd (Finset.mem_Icc.mp hmem).1 (not_le.mpr ha)
  have hne : (A \ B).Nonempty := ⟨a₁, ha₁⟩
  set c : Fin n := (A \ B).max' hne with hc
  have hcmem : c ∈ A \ B := (A \ B).max'_mem hne
  obtain ⟨hcA, hcB⟩ := Finset.mem_sdiff.mp hcmem
  have hcb₁ : c ≤ b₁ := (Finset.mem_Icc.mp hcA).2
  have hca₂ : c < a₂ := by
    by_contra hcon
    exact hcB (Finset.mem_Icc.mpr ⟨not_lt.mp hcon, le_trans hcb₁ hb⟩)
  have ha₁c : a₁ ≤ c := (A \ B).le_max' a₁ ha₁
  -- the sticking-out part is exactly the interval `[a₁, c]`
  have hIcc : Finset.Icc a₁ c = A \ B := by
    apply Finset.Subset.antisymm
    · intro i hi
      obtain ⟨hia, hic⟩ := Finset.mem_Icc.mp hi
      refine Finset.mem_sdiff.mpr
        ⟨Finset.mem_Icc.mpr ⟨hia, le_trans hic hcb₁⟩, fun hmem => ?_⟩
      exact absurd (Finset.mem_Icc.mp hmem).1
        (not_le.mpr (lt_of_le_of_lt hic hca₂))
    · intro i hi
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp (Finset.mem_sdiff.mp hi).1).1,
          (A \ B).le_max' i hi⟩
  have hfp : IsFullyPairedOn κ (Finset.Icc a₁ c) := by
    rw [hIcc]; exact hf₁.sdiff hf₂
  -- and it lies strictly to the left of `a₂ ≤ p`, hence inside the left block
  have ha₂p : (a₂ : ℕ) < p :=
    (r324Step3_fullyPaired_straddles hL hR h₂ hf₂).1
  refine hL.not_isFullyPairedOn ha₁c (fun i hi => ?_) hfp
  exact mem_r324SplitBlockLeft.mpr
    (lt_of_lt_of_le (lt_of_le_of_lt (Finset.mem_Icc.mp hi).2 hca₂) ha₂p.le)

/-- **No right overhang**, the mirror image of `r324Step3_no_left_part`:
the part sticking out on the right lies inside the right block. -/
private theorem r324Step3_no_right_part {n p : ℕ} {κ : PartialPairing (Fin n)}
    (hL : R324SidePrimitiveNotFull κ (r324SplitBlockLeft n p))
    (hR : R324SidePrimitiveNotFull κ (r324SplitBlockRight n p))
    {a₁ b₁ a₂ b₂ : Fin n} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hf₁ : IsFullyPairedOn κ (Finset.Icc a₁ b₁))
    (hf₂ : IsFullyPairedOn κ (Finset.Icc a₂ b₂))
    (ha : a₂ ≤ a₁) (hb : b₂ < b₁) : False := by
  set A : Finset (Fin n) := Finset.Icc a₁ b₁ with hA
  set B : Finset (Fin n) := Finset.Icc a₂ b₂ with hB
  have hb₁ : b₁ ∈ A \ B := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨h₁, le_refl _⟩, ?_⟩
    intro hmem
    exact absurd (Finset.mem_Icc.mp hmem).2 (not_le.mpr hb)
  have hne : (A \ B).Nonempty := ⟨b₁, hb₁⟩
  set c : Fin n := (A \ B).min' hne with hc
  have hcmem : c ∈ A \ B := (A \ B).min'_mem hne
  obtain ⟨hcA, hcB⟩ := Finset.mem_sdiff.mp hcmem
  have hca₁ : a₁ ≤ c := (Finset.mem_Icc.mp hcA).1
  have hcb₂ : b₂ < c := by
    by_contra hcon
    exact hcB (Finset.mem_Icc.mpr ⟨le_trans ha hca₁, not_lt.mp hcon⟩)
  have hcb₁ : c ≤ b₁ := (A \ B).min'_le b₁ hb₁
  have hIcc : Finset.Icc c b₁ = A \ B := by
    apply Finset.Subset.antisymm
    · intro i hi
      obtain ⟨hic, hib⟩ := Finset.mem_Icc.mp hi
      refine Finset.mem_sdiff.mpr
        ⟨Finset.mem_Icc.mpr ⟨le_trans hca₁ hic, hib⟩, fun hmem => ?_⟩
      exact absurd (Finset.mem_Icc.mp hmem).2
        (not_le.mpr (lt_of_lt_of_le hcb₂ hic))
    · intro i hi
      exact Finset.mem_Icc.mpr
        ⟨(A \ B).min'_le i hi,
          (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hi).1).2⟩
  have hfp : IsFullyPairedOn κ (Finset.Icc c b₁) := by
    rw [hIcc]; exact hf₁.sdiff hf₂
  have hb₂p : p ≤ (b₂ : ℕ) :=
    (r324Step3_fullyPaired_straddles hL hR h₂ hf₂).2
  refine hR.not_isFullyPairedOn hcb₁ (fun i hi => ?_) hfp
  exact mem_r324SplitBlockRight.mpr
    (le_trans hb₂p (le_of_lt (lt_of_lt_of_le hcb₂ (Finset.mem_Icc.mp hi).1)))

/-- **Step 3(b), the paper's display.**  Two fully paired subintervals of
`κ₀` are either equal or *strictly nested*.  Together with
`r324Step3_fullyPaired_straddles` (each of them straddles the split point)
this is exactly

`1 ≤ a_t < ⋯ < a₁ ≤ p < p+1 ≤ b₁ < ⋯ < b_t ≤ p+q`,

the nested chain that Step 3 reduces one interval at a time.  It replaces
every form of grading or per-contraction budget: there is a *linear order*
on the surviving intervals. -/
theorem r324Step3_strict_nested {n p : ℕ} {κ : PartialPairing (Fin n)}
    (hL : R324SidePrimitiveNotFull κ (r324SplitBlockLeft n p))
    (hR : R324SidePrimitiveNotFull κ (r324SplitBlockRight n p))
    {a₁ b₁ a₂ b₂ : Fin n} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hf₁ : IsFullyPairedOn κ (Finset.Icc a₁ b₁))
    (hf₂ : IsFullyPairedOn κ (Finset.Icc a₂ b₂)) :
    (a₁ < a₂ ∧ b₂ < b₁) ∨ (a₁ = a₂ ∧ b₁ = b₂) ∨ (a₂ < a₁ ∧ b₁ < b₂) := by
  rcases lt_trichotomy a₁ a₂ with ha | ha | ha
  · refine Or.inl ⟨ha, ?_⟩
    by_contra hcon
    exact r324Step3_no_left_part hL hR h₁ h₂ hf₁ hf₂ ha (not_lt.mp hcon)
  · refine Or.inr (Or.inl ⟨ha, ?_⟩)
    rcases lt_trichotomy b₁ b₂ with hb | hb | hb
    · exact absurd (r324Step3_no_right_part hL hR h₂ h₁ hf₂ hf₁ ha.le hb)
        not_false
    · exact hb
    · exact absurd (r324Step3_no_right_part hL hR h₁ h₂ hf₁ hf₂ ha.ge hb)
        not_false
  · refine Or.inr (Or.inr ⟨ha, ?_⟩)
    by_contra hcon
    exact r324Step3_no_left_part hL hR h₂ h₁ hf₂ hf₁ ha (not_lt.mp hcon)

/-! ## Step 3(a): the four external legs integrate to constants -/

/-- **Step 3(a).**  "In (4.19) we first integrate in `(x, y, z, w)` yielding
constants, leading to (4.20)."  Each of the four external legs
`|x - x₁|⁻²`, `|x_p - y|⁻²`, `|z - x_{p+1}|⁻²`, `|x_{p+q} - w|⁻²`
integrates to the same finite constant `∫|z|⁻²`; the passage from (4.19) to
(4.20) costs exactly its fourth power. -/
theorem r324Step3_external_legs (x₁ xp xq xr : T4) :
    (∫ x, invSqKer (x - x₁) ∂paperMeasure) *
        (∫ y, invSqKer (xp - y) ∂paperMeasure) *
        (∫ z, invSqKer (z - xq) ∂paperMeasure) *
        (∫ w, invSqKer (xr - w) ∂paperMeasure) =
      invSqKerMass ^ 4 := by
  have hflip : ∀ v : T4,
      (∫ x, invSqKer (x - v) ∂paperMeasure) = invSqKerMass := by
    intro v
    have : (fun x : T4 => invSqKer (x - v)) = fun x : T4 => invSqKer (v - x) := by
      funext x; exact invSqKer_sub_comm x v
    rw [this, integral_invSqKer_sub_left]
  rw [hflip x₁, hflip xq, integral_invSqKer_sub_left xp,
    integral_invSqKer_sub_left xr]
  ring

/-! ## Step 3(c): the elementary eight-dimensional integral

"It is then elementary to show that

`∫_{T⁸} |x_{a₁-1} - x_{a₁}|⁻² · [(4.4) bound](z) · |x_{b₁} - x_{b₁+1}|⁻²
  dx_{a₁} dx_{b₁} ≤ C`,  `z := x_{a₁} - x_{b₁}`,

so we can bound (4.20) by ... ", i.e. the innermost interval `[a₁, b₁]` of
the nested chain is removed at the price of a single constant, and the
structure of (4.20) is reassembled with `κ₀′ := κ₀ \ κ₁`. -/

/-- The integrand of the paper's elementary eight-dimensional integral: the
chain leg entering `a₁`, the (4.4) majorant `J̃_{k,prim}(x_{a₁} - x_{b₁})`
of the primitive pairing induced on `[a₁, b₁]`, and the chain leg leaving
`b₁`. -/
def r324Step3EightDimIntegrand (C lam ε supportConstant : ℝ) (k : ℕ)
    (u v a b : T4) : ℝ :=
  invSqKer (u - a) *
    primitiveInsertedMajorant C lam ε supportConstant k (a - b) *
    invSqKer (b - v)

/-- **Step 3(c), the elementary eight-dimensional integral.**  Uniformly in
the two flanking chain variables `u = x_{a₁-1}`, `v = x_{b₁+1}`, in the
scale `ε` and in the length `k = k₁` of the removed interval,

`∫∫ |u - a|⁻² · J̃_{k,prim}(a - b) · |b - v|⁻² da db ≤ (Cλ)^{2k} · K`.

Stripping the `(Cλ)^{2k}` that (4.4) puts in front of `J̃_{k,prim}`, the
integral is bounded by the single constant `K` — the paper's "`≤ C`". -/
theorem exists_r324Step3_elementaryEightDim_le
    {supportConstant : ℝ} (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C lam ε : ℝ) (k : ℕ) (u v : T4),
        0 ≤ C → 0 ≤ lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
          (∫ a, ∫ b,
            r324Step3EightDimIntegrand C lam ε supportConstant k u v a b
            ∂paperMeasure ∂paperMeasure) ≤ (C * lam) ^ (2 * k) * K := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_r324ProperInsertedConvolution_le hsupport
  refine ⟨K, hK, ?_⟩
  intro C lam ε k u v hC hlam hε hε1 hlog
  exact (hbound C lam ε k u v hC hlam hε hε1 hlog).2

/-! ## Step 3(d): the induction over the nested chain -/

/-- **Step 3(d).**  "Now we perform successive reductions for these
subintervals ... Iterate over `[a₂, b₂]`, ...".  Because the surviving
fully paired subintervals form a *strictly nested chain*
(`r324Step3_strict_nested`), the reductions can be performed one at a time,
each gaining `(Cλ)^{2 k_i}` from (4.4) and costing the single constant `K`
of the elementary eight-dimensional integral.  After `t` steps: -/
theorem r324Step3_chain_induction {t : ℕ} {Cl K : ℝ} (hCl : 0 ≤ Cl)
    (hK : 0 ≤ K) (E : ℕ → ℝ) (k : ℕ → ℕ)
    (hstep : ∀ i, i < t → E i ≤ Cl ^ (2 * k i) * K * E (i + 1)) :
    E 0 ≤ Cl ^ (2 * ∑ i ∈ Finset.range t, k i) * K ^ t * E t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hIH := ih fun i hi => hstep i (Nat.lt_succ_of_lt hi)
    have hlast := hstep t (Nat.lt_succ_self t)
    have hpos : (0 : ℝ) ≤ Cl ^ (2 * ∑ i ∈ Finset.range t, k i) * K ^ t :=
      mul_nonneg (pow_nonneg hCl _) (pow_nonneg hK _)
    calc
      E 0 ≤ Cl ^ (2 * ∑ i ∈ Finset.range t, k i) * K ^ t * E t := hIH
      _ ≤ Cl ^ (2 * ∑ i ∈ Finset.range t, k i) * K ^ t *
            (Cl ^ (2 * k t) * K * E (t + 1)) :=
        mul_le_mul_of_nonneg_left hlast hpos
      _ = Cl ^ (2 * ∑ i ∈ Finset.range (t + 1), k i) * K ^ (t + 1) *
            E (t + 1) := by
        rw [Finset.sum_range_succ, Nat.mul_add, pow_add, pow_succ]
        ring

/-! ## Step 3, last line: `(Cλ)^{2m}|log ε|⁻¹ ≤ λ_ε² · C (Cλ)^{2m-2}` -/

theorem r324Step23_lamEps_sq (lam ε : ℝ) :
    lamEps lam ε ^ 2 = lam ^ 2 / |Real.log ε| := by
  unfold lamEps
  rw [div_pow, Real.sq_sqrt (abs_nonneg _)]

/-- **The paper's last line of Step 3**, verbatim:
`(Cλ)^{2m}|log ε|⁻¹ ≤ λ_ε² · C (Cλ)^{2m-2}`, here as an identity with
`C = C²`.  This is (3.24) with `1` on the right-hand side, written in the
shape the proved consumers use. -/
theorem r324Step23_output_identity (C lam ε : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (C * lam) ^ (2 * m) / |Real.log ε| =
      lamEps lam ε ^ 2 * C ^ 2 * (C * lam) ^ (2 * m - 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, Nat.add_sub_cancel, pow_add,
    r324Step23_lamEps_sq]
  ring

/-! ## Steps 2–3, assembled

The single input the two steps take from the §4.1 iteration is recorded as
one named hypothesis, exactly as `R324Step1Reduction` records it for
Step 1. -/

/-- **The one input Steps 2–3 take from the §4.1 iteration.**

Everything the paper does between (4.16) and the last line of Step 3 is:

* **2(a)** replace the sum over `(κ₊, κ₋, π)` by a sum over full pairings
  `κ′` of `[1, 2m]` — proved, and restated here as
  `r324Step2_wick_regroup`;
* **2(b), 2(c)** identify the fully paired subintervals of `κ′` inside
  `[1, m]` and inside `[m+1, 2m]` and *fix their positions* — the purely
  positional count `card_intervalConfigs_two_mul_le`, whose cost is
  `16^m`;
* **2(d), 2(e)** write (4.18) and successively sum over the primitive
  pairings `κ_i` (`i ≥ 1`), removing each `I_i`, gaining a factor `Cλ` per
  removal and introducing new inputs `H` with `|H(z)| ≲ |z|⁻²` (the §4.1
  iteration, verbatim);
* **2(f)** only then take absolute values, giving (4.19);
* **3(a)** integrate the four external legs, giving (4.20) —
  `r324Step3_external_legs`;
* **3(b)** the surviving intervals form a strictly nested chain —
  `r324Step3_fullyPaired_straddles`, `r324Step3_strict_nested`;
* **3(c), 3(d)** reduce the chain one interval at a time by the elementary
  eight-dimensional integral — `exists_r324Step3_elementaryEightDim_le`,
  `r324Step3_chain_induction`.

What survives is the *last* application of (4.4): one primitive block of
size `k`, whose inserted majorant `J̃_{k,prim}` is integrated once.  This
hypothesis says exactly that, with the positional cost `16^m` and the
`(Cλ)` gained by each removal displayed. -/
def R324Step23Reduction (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (Cred supportConstant : ℝ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      (16 : ℝ) ^ m * (Cred * lam) ^ (2 * m - 2 * k) *
        ∫ z, primitiveInsertedMajorant Cred lam ε supportConstant k z
          ∂paperMeasure

/-- **Steps 2 and 3 of §4.2, complete.**

Given the §4.1 successive removal and the nested-chain reduction (the one
named hypothesis `R324Step23Reduction`), the second moment obeys

`|E|P̂_m(α,β)|²| ≤ (Cλ)^{2m}|log ε|⁻¹ = λ_ε² · C (Cλ)^{2m-2}`,

which is (3.24) with `1` on the right-hand side, in the form consumed by
the deterministic closure. -/
theorem exists_r324Step23_bound (ρ : SmoothCutoff) {Cred supportConstant : ℝ}
    (hCred : 0 < Cred) (hsupport : 0 < supportConstant) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 ≤ lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
        R324Step23Reduction ρ lam ε m α β Cred supportConstant →
          ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
            lamEps lam ε ^ 2 * outerC * (powerC * lam) ^ (2 * m - 2) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hmaj⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  set D : ℝ := Cball * supportConstant ^ 2 + 2 * Creg with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  refine ⟨(4 * Cred * (D + 1)) ^ 2, 4 * Cred * (D + 1), by positivity,
    by positivity, ?_⟩
  intro lam ε m α β hlam hε hε1 hlog hm hred
  obtain ⟨k, hk1, hkm, hbound⟩ := hred
  have hlog0 : (0 : ℝ) < |Real.log ε| := lt_of_lt_of_le one_pos hlog
  have hbase : (0 : ℝ) ≤ Cred * lam := mul_nonneg hCred.le hlam
  have hpre : (0 : ℝ) ≤ (16 : ℝ) ^ m * (Cred * lam) ^ (2 * m - 2 * k) :=
    mul_nonneg (by positivity) (pow_nonneg hbase _)
  have hsplit : (2 * m - 2 * k) + 2 * k = 2 * m := by omega
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        (16 : ℝ) ^ m * (Cred * lam) ^ (2 * m - 2 * k) *
          ∫ z, primitiveInsertedMajorant Cred lam ε supportConstant k z
            ∂paperMeasure := hbound
    _ ≤ (16 : ℝ) ^ m * (Cred * lam) ^ (2 * m - 2 * k) *
          ((Cred * lam) ^ (2 * k) * (D / |Real.log ε|)) :=
      mul_le_mul_of_nonneg_left
        (hmaj Cred lam ε supportConstant k hε hε1 hsupport hlog) hpre
    _ = (16 : ℝ) ^ m * (Cred * lam) ^ (2 * m) * (D / |Real.log ε|) := by
      rw [mul_assoc, ← mul_assoc ((Cred * lam) ^ (2 * m - 2 * k)),
        ← pow_add, hsplit, mul_assoc]
    _ = ((4 * Cred) * lam) ^ (2 * m) * D / |Real.log ε| := by
      have h16 : ((4 : ℝ) * Cred * lam) ^ (2 * m) =
          16 ^ m * (Cred * lam) ^ (2 * m) := by
        rw [show (4 : ℝ) * Cred * lam = 4 * (Cred * lam) by ring, mul_pow,
          show ((4 : ℝ) ^ (2 * m)) = 16 ^ m by rw [pow_mul]; norm_num]
      rw [h16]; ring
    _ ≤ ((4 * Cred * (D + 1)) * lam) ^ (2 * m) / |Real.log ε| := by
      rw [div_le_div_iff_of_pos_right hlog0]
      have := mul_constant_le_absorbed_even_pow
        (base := (4 * Cred) * lam) (K := D) (q := m)
        (by positivity) hD0.le hm
      calc ((4 * Cred) * lam) ^ (2 * m) * D ≤
            (((4 * Cred) * lam) * (D + 1)) ^ (2 * m) := this
        _ = ((4 * Cred * (D + 1)) * lam) ^ (2 * m) := by ring_nf
    _ = lamEps lam ε ^ 2 * (4 * Cred * (D + 1)) ^ 2 *
          ((4 * Cred * (D + 1)) * lam) ^ (2 * m - 2) :=
      r324Step23_output_identity _ lam ε hm

end

end Anderson4D
