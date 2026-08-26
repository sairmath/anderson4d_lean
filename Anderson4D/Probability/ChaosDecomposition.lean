import Anderson4D.Probability.PartialPairingWick
import Anderson4D.Probability.CovariancePoisson

/-!
# Raw Gaussian products as partial-pairing chaos sums

This file proves the algebraic decomposition used in paper equation (2.4).
For every partial pairing, its two-cycles contribute positive covariance
factors and its fixed points contribute the homogeneous Wick polynomial of
the remaining variables.  The fixed points are listed in the order inherited
from the original finite carrier.

The proof is pointwise.  Probability enters only in the final specialization
to the mollified noise, where the covariance kernel is identified with
`etaEpsT4`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Labels at the fixed points of a partial pairing, in the order inherited
from the ambient finite ordinal. -/
def partialPairingSingleLabels {n : ℕ} {ι : Type*}
    (v : Fin n → ι) (κ : PartialPairing (Fin n)) : List ι :=
  κ.singles.sort.map v

@[simp]
theorem partialPairingSingleLabels_length {n : ℕ} {ι : Type*}
    (v : Fin n → ι) (κ : PartialPairing (Fin n)) :
    (partialPairingSingleLabels v κ).length = κ.singles.card := by
  simp [partialPairingSingleLabels]

/-- Product of the covariance factors carried by the two-cycles of a
partial pairing. -/
def partialPairingCovarianceProduct {n : ℕ} {ι : Type*}
    (C : ι → ι → ℝ) (v : Fin n → ι)
    (κ : PartialPairing (Fin n)) : ℝ :=
  ∏ i ∈ κ.representatives, C (v i) (v (κ i))

/-- One summand in equation (2.4): positive covariance on every pair and
the chaos projection of the product at the ordered singles. -/
def partialPairingChaosWeight {n : ℕ} {ι Ω : Type*}
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : Fin n → ι) (κ : PartialPairing (Fin n)) (ω : Ω) : ℝ :=
  partialPairingCovarianceProduct C v κ *
    chaosProjProduct κ.singles.card C X
      (partialPairingSingleLabels v κ) ω

theorem partialPairingChaosWeight_eq_pairProduct_mul_wickPolynomial
    {n : ℕ} {ι Ω : Type*}
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : Fin n → ι) (κ : PartialPairing (Fin n)) (ω : Ω) :
    partialPairingChaosWeight C X v κ ω =
      partialPairingCovarianceProduct C v κ *
        wickPolynomial C X (partialPairingSingleLabels v κ) ω := by
  unfold partialPairingChaosWeight
  rw [chaosProjProduct_eq_wickPolynomial C X
    (partialPairingSingleLabels_length v κ)]

namespace ChaosDecomposition

namespace PartialPairing

/-! ## A marked-single equivalence local to the probability layer -/

/-- Remove a specified fixed point from a partial pairing. -/
def eraseSingle {α : Type*} [DecidableEq α]
    (κ : PartialPairing α) (j : α) (hj : κ j = j) :
    PartialPairing {i : α // i ≠ j} where
  toFun i :=
    ⟨κ i.1, by
      intro h
      apply i.2
      rw [← κ.apply_apply i.1, h, hj]⟩
  involutive i := Subtype.ext (κ.apply_apply i.1)

@[simp]
theorem eraseSingle_apply_val
    {α : Type*} [DecidableEq α]
    (κ : PartialPairing α) (j : α) (hj : κ j = j)
    (i : {i : α // i ≠ j}) :
    (eraseSingle κ j hj i).1 = κ i.1 :=
  rfl

/-- Restore a distinguished fixed point to a pairing of its complement. -/
def insertSingle {α : Type*} [DecidableEq α]
    (j : α) (κ : PartialPairing {i : α // i ≠ j}) :
    PartialPairing α where
  toFun i :=
    if h : i = j then j else (κ ⟨i, h⟩).1
  involutive i := by
    by_cases hi : i = j
    · subst i
      simp
    · have hout : (κ ⟨i, hi⟩).1 ≠ j := (κ ⟨i, hi⟩).2
      simp [hi, hout]

@[simp]
theorem insertSingle_apply_eq
    {α : Type*} [DecidableEq α]
    (j : α) (κ : PartialPairing {i : α // i ≠ j}) :
    insertSingle j κ j = j := by
  simp [insertSingle]

@[simp]
theorem insertSingle_apply_ne
    {α : Type*} [DecidableEq α]
    (j : α) (κ : PartialPairing {i : α // i ≠ j})
    (i : α) (hi : i ≠ j) :
    insertSingle j κ i = (κ ⟨i, hi⟩).1 := by
  simp [insertSingle, hi]

@[simp]
theorem eraseSingle_insertSingle
    {α : Type*} [DecidableEq α]
    (j : α) (κ : PartialPairing {i : α // i ≠ j}) :
    eraseSingle (insertSingle j κ) j
      (insertSingle_apply_eq j κ) = κ := by
  apply Anderson4D.PartialPairing.ext
  intro i
  apply Subtype.ext
  rw [eraseSingle_apply_val, insertSingle_apply_ne j κ i.1 i.2]

@[simp]
theorem insertSingle_eraseSingle
    {α : Type*} [DecidableEq α]
    (κ : PartialPairing α) (j : α) (hj : κ j = j) :
    insertSingle j (eraseSingle κ j hj) = κ := by
  apply Anderson4D.PartialPairing.ext
  intro i
  by_cases hi : i = j
  · subst i
    rw [insertSingle_apply_eq, hj]
  · rw [insertSingle_apply_ne _ _ _ hi, eraseSingle_apply_val]

/-- A partial pairing together with one marked fixed point. -/
structure MarkedSingle (α : Type*) [Fintype α] [DecidableEq α] where
  pairing : Anderson4D.PartialPairing α
  index : α
  isSingle : index ∈ pairing.singles

@[ext]
theorem MarkedSingle.ext
    {α : Type*} [Fintype α] [DecidableEq α]
    {d e : MarkedSingle α}
    (hpairing : d.pairing = e.pairing)
    (hindex : d.index = e.index) :
    d = e := by
  cases d
  cases e
  simp only [MarkedSingle.mk.injEq] at hpairing hindex ⊢
  exact ⟨hpairing, hindex⟩

/-- Marking a single is equivalent to choosing its index and a pairing on
the complementary carrier. -/
def markedSingleEquiv (α : Type*) [Fintype α] [DecidableEq α] :
    MarkedSingle α ≃
      ((j : α) × Anderson4D.PartialPairing {i : α // i ≠ j}) where
  toFun d :=
    ⟨d.index, eraseSingle d.pairing d.index
      (Anderson4D.PartialPairing.mem_singles.mp d.isSingle)⟩
  invFun d :=
    ⟨insertSingle d.1 d.2, d.1,
      Anderson4D.PartialPairing.mem_singles.mpr
        (insertSingle_apply_eq d.1 d.2)⟩
  left_inv d := by
    apply MarkedSingle.ext
    · exact insertSingle_eraseSingle d.pairing d.index
        (Anderson4D.PartialPairing.mem_singles.mp d.isSingle)
    · rfl
  right_inv d := by
    rcases d with ⟨j, κ⟩
    exact Sigma.ext rfl
      (heq_of_eq (eraseSingle_insertSingle j κ))

noncomputable instance markedSingleFintype
    (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype (MarkedSingle α) :=
  Fintype.ofEquiv
    ((j : α) × Anderson4D.PartialPairing {i : α // i ≠ j})
    (markedSingleEquiv α).symm

/-- A pairing together with the increasing rank of one of its singles. -/
abbrev RankedSingle (α : Type*) [Fintype α] [LinearOrder α] :=
  (κ : Anderson4D.PartialPairing α) × Fin κ.singles.card

/-- Increasing enumeration turns a ranked single into a marked single. -/
def rankedSingleEquiv
    (α : Type*) [Fintype α] [LinearOrder α] :
    RankedSingle α ≃ MarkedSingle α :=
  (Equiv.sigmaCongrRight fun κ : Anderson4D.PartialPairing α =>
      (κ.singles.orderIsoOfFin rfl).toEquiv).trans
    { toFun := fun d => ⟨d.1, d.2.1, d.2.2⟩
      invFun := fun d => ⟨d.pairing, ⟨d.index, d.isSingle⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp]
theorem rankedSingleEquiv_pairing
    {n : ℕ} (κ : Anderson4D.PartialPairing (Fin n))
    (j : Fin κ.singles.card) :
    (rankedSingleEquiv (Fin n) ⟨κ, j⟩).pairing = κ :=
  rfl

@[simp]
theorem rankedSingleEquiv_index
    {n : ℕ} (κ : Anderson4D.PartialPairing (Fin n))
    (j : Fin κ.singles.card) :
    (rankedSingleEquiv (Fin n) ⟨κ, j⟩).index =
      κ.singles.orderEmbOfFin rfl j :=
  rfl

theorem rankedSingleEquiv_idxOf
    {n : ℕ} (κ : Anderson4D.PartialPairing (Fin n))
    (j : Fin κ.singles.card) :
    κ.singles.sort.idxOf
        (rankedSingleEquiv (Fin n) ⟨κ, j⟩).index =
      j.val := by
  let e := κ.singles.orderIsoOfFin rfl
  have h :=
    Finset.orderIsoOfFin_symm_apply
      κ.singles rfl (e j)
  have he : e.symm (e j) = j := e.symm_apply_apply j
  rw [he] at h
  exact h.symm

theorem sum_rankedSingle
    {α R : Type*} [Fintype α] [LinearOrder α]
    [AddCommMonoid R] (f : MarkedSingle α → R) :
    (∑ κ : Anderson4D.PartialPairing α,
      ∑ j : Fin κ.singles.card,
        f (rankedSingleEquiv α ⟨κ, j⟩)) =
      ∑ d : MarkedSingle α, f d := by
  calc
    _ = ∑ d : RankedSingle α,
        f (rankedSingleEquiv α d) := by
      rw [Fintype.sum_sigma]
    _ = _ := (rankedSingleEquiv α).sum_comp f

/-- The two head branches, with contractions indexed by a pairing and one
of its old singles. -/
def headEquiv (n : ℕ) :
    Anderson4D.PartialPairing (Fin n) ⊕ MarkedSingle (Fin n) ≃
      Anderson4D.PartialPairing (Fin (n + 1)) :=
  (Equiv.sumCongr (Equiv.refl _) (markedSingleEquiv (Fin n))).trans
    (Anderson4D.PartialPairing.finHeadEquiv n).symm

@[simp]
theorem headEquiv_apply_creation
    (n : ℕ) (κ : Anderson4D.PartialPairing (Fin n)) :
    headEquiv n (Sum.inl κ) =
      (Anderson4D.PartialPairing.finHeadEquiv n).symm (Sum.inl κ) :=
  rfl

@[simp]
theorem headEquiv_apply_contraction
    (n : ℕ) (d : MarkedSingle (Fin n)) :
    headEquiv n (Sum.inr d) =
      (Anderson4D.PartialPairing.finHeadEquiv n).symm
        (Sum.inr (markedSingleEquiv (Fin n) d)) :=
  rfl

/-- Creation and marked contraction enumerate every pairing after adjoining
a new zero exactly once. -/
theorem sum_creation_contraction
    {R : Type*} [AddCommMonoid R] (n : ℕ)
    (f : Anderson4D.PartialPairing (Fin (n + 1)) → R) :
    (∑ κ : Anderson4D.PartialPairing (Fin n),
        f (headEquiv n (Sum.inl κ))) +
      (∑ d : MarkedSingle (Fin n),
        f (headEquiv n (Sum.inr d))) =
      ∑ κ : Anderson4D.PartialPairing (Fin (n + 1)), f κ := by
  calc
    _ = ∑ s :
        Anderson4D.PartialPairing (Fin n) ⊕ MarkedSingle (Fin n),
        f (headEquiv n s) := by
      rw [Fintype.sum_sum_type]
    _ = _ := (headEquiv n).sum_comp f

@[simp]
theorem headEquiv_creation_zero
    (n : ℕ) (κ : Anderson4D.PartialPairing (Fin n)) :
    headEquiv n (Sum.inl κ) 0 = 0 := by
  unfold headEquiv Anderson4D.PartialPairing.finHeadEquiv
  simp [Anderson4D.PartialPairing.optionHeadEquiv,
    Anderson4D.PartialPairing.optionHeadAssemble]
  change
    Anderson4D.PartialPairing.congr (finSuccEquiv n).symm
        (Anderson4D.PartialPairing.optionFixed κ) 0 = 0
  rw [Anderson4D.PartialPairing.congr_apply_apply]
  rfl

@[simp]
theorem headEquiv_creation_succ
    (n : ℕ) (κ : Anderson4D.PartialPairing (Fin n)) (i : Fin n) :
    headEquiv n (Sum.inl κ) i.succ = (κ i).succ := by
  unfold headEquiv Anderson4D.PartialPairing.finHeadEquiv
  simp [Anderson4D.PartialPairing.optionHeadEquiv,
    Anderson4D.PartialPairing.optionHeadAssemble]
  change
    Anderson4D.PartialPairing.congr (finSuccEquiv n).symm
        (Anderson4D.PartialPairing.optionFixed κ) i.succ =
      (κ i).succ
  rw [Anderson4D.PartialPairing.congr_apply_apply]
  rfl

@[simp]
theorem headEquiv_contraction_zero
    {n : ℕ} (d : MarkedSingle (Fin n)) :
    headEquiv n (Sum.inr d) 0 = d.index.succ := by
  unfold headEquiv Anderson4D.PartialPairing.finHeadEquiv
  simp [Anderson4D.PartialPairing.optionHeadEquiv,
    Anderson4D.PartialPairing.optionHeadAssemble, markedSingleEquiv]
  change
    Anderson4D.PartialPairing.congr (finSuccEquiv n).symm
      (Anderson4D.PartialPairing.optionPaired d.index
        (eraseSingle d.pairing d.index
          (Anderson4D.PartialPairing.mem_singles.mp d.isSingle))) 0 =
        d.index.succ
  rw [Anderson4D.PartialPairing.congr_apply_apply]
  simp

@[simp]
theorem headEquiv_contraction_partner
    {n : ℕ} (d : MarkedSingle (Fin n)) :
    headEquiv n (Sum.inr d) d.index.succ = 0 := by
  unfold headEquiv Anderson4D.PartialPairing.finHeadEquiv
  simp [Anderson4D.PartialPairing.optionHeadEquiv,
    Anderson4D.PartialPairing.optionHeadAssemble, markedSingleEquiv]
  change
    Anderson4D.PartialPairing.congr (finSuccEquiv n).symm
      (Anderson4D.PartialPairing.optionPaired d.index
        (eraseSingle d.pairing d.index
          (Anderson4D.PartialPairing.mem_singles.mp d.isSingle)))
          d.index.succ = 0
  rw [Anderson4D.PartialPairing.congr_apply_apply]
  simp

@[simp]
theorem headEquiv_contraction_succ_ne
    {n : ℕ} (d : MarkedSingle (Fin n))
    (i : Fin n) (hi : i ≠ d.index) :
    headEquiv n (Sum.inr d) i.succ = (d.pairing i).succ := by
  unfold headEquiv Anderson4D.PartialPairing.finHeadEquiv
  simp [Anderson4D.PartialPairing.optionHeadEquiv,
    Anderson4D.PartialPairing.optionHeadAssemble, markedSingleEquiv]
  change
    Anderson4D.PartialPairing.congr (finSuccEquiv n).symm
      (Anderson4D.PartialPairing.optionPaired d.index
        (eraseSingle d.pairing d.index
          (Anderson4D.PartialPairing.mem_singles.mp d.isSingle)))
        i.succ = (d.pairing i).succ
  rw [Anderson4D.PartialPairing.congr_apply_apply]
  simp only [Equiv.symm_symm, finSuccEquiv_succ]
  rw [Anderson4D.PartialPairing.optionPaired_some_ne d.index
    (eraseSingle d.pairing d.index
      (Anderson4D.PartialPairing.mem_singles.mp d.isSingle)) i hi]
  rw [eraseSingle_apply_val, finSuccEquiv_symm_some]

theorem singles_headEquiv_creation
    (n : ℕ) (κ : Anderson4D.PartialPairing (Fin n)) :
    (headEquiv n (Sum.inl κ)).singles =
      insert 0 (κ.singles.map (Fin.succEmb n)) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Anderson4D.PartialPairing.mem_singles,
      headEquiv_creation_zero]
    simp
  · rw [Anderson4D.PartialPairing.mem_singles,
      headEquiv_creation_succ]
    simp [Anderson4D.PartialPairing.mem_singles]

theorem singles_headEquiv_contraction
    {n : ℕ} (d : MarkedSingle (Fin n)) :
    (headEquiv n (Sum.inr d)).singles =
      (d.pairing.singles.erase d.index).map (Fin.succEmb n) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Anderson4D.PartialPairing.mem_singles,
      headEquiv_contraction_zero]
    constructor
    · intro heq
      exact False.elim (Fin.succ_ne_zero d.index heq)
    · intro h
      rw [Finset.mem_map] at h
      obtain ⟨j, _hj, hj0⟩ := h
      exact False.elim (Fin.succ_ne_zero j hj0)
  · by_cases hj : j = d.index
    · subst j
      rw [Anderson4D.PartialPairing.mem_singles,
        headEquiv_contraction_partner]
      constructor
      · intro heq
        exact False.elim (Fin.succ_ne_zero d.index heq.symm)
      · intro h
        rw [Finset.mem_map] at h
        obtain ⟨k, hk, hkeq⟩ := h
        have hkEq : k = d.index := Fin.succ_injective n hkeq
        subst k
        exact False.elim (Finset.notMem_erase
          d.index d.pairing.singles hk)
    · rw [Anderson4D.PartialPairing.mem_singles,
        headEquiv_contraction_succ_ne d j hj]
      simp only [Fin.succ_inj]
      simp [Anderson4D.PartialPairing.mem_singles, hj]

theorem representatives_headEquiv_creation
    (n : ℕ) (κ : Anderson4D.PartialPairing (Fin n)) :
    (headEquiv n (Sum.inl κ)).representatives =
      κ.representatives.map (Fin.succEmb n) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Anderson4D.PartialPairing.mem_representatives,
      headEquiv_creation_zero]
    simp
  · rw [Anderson4D.PartialPairing.mem_representatives,
      headEquiv_creation_succ]
    simp

theorem representatives_headEquiv_contraction
    {n : ℕ} (d : MarkedSingle (Fin n)) :
    (headEquiv n (Sum.inr d)).representatives =
      insert 0 (d.pairing.representatives.map (Fin.succEmb n)) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Anderson4D.PartialPairing.mem_representatives,
      headEquiv_contraction_zero]
    simp
  · by_cases hj : j = d.index
    · subst j
      have hsingle :
          d.pairing d.index = d.index :=
        Anderson4D.PartialPairing.mem_singles.mp d.isSingle
      rw [Anderson4D.PartialPairing.mem_representatives,
        headEquiv_contraction_partner]
      simp [Anderson4D.PartialPairing.mem_representatives,
        hsingle]
    · rw [Anderson4D.PartialPairing.mem_representatives,
        headEquiv_contraction_succ_ne d j hj]
      simp [Anderson4D.PartialPairing.mem_representatives]

theorem singleLabels_headEquiv_creation
    {n : ℕ} {ι : Type*} (v : Fin (n + 1) → ι)
    (κ : Anderson4D.PartialPairing (Fin n)) :
    partialPairingSingleLabels v (headEquiv n (Sum.inl κ)) =
      v 0 :: partialPairingSingleLabels (fun i => v i.succ) κ := by
  rw [partialPairingSingleLabels, singles_headEquiv_creation]
  have hzero :
      (0 : Fin (n + 1)) ∉ κ.singles.map (Fin.succEmb n) := by
    simp
  rw [Finset.sort_insert (r := (· ≤ ·)) (by simp) hzero,
    List.map_cons]
  have hsort :
      κ.singles.sort.map Fin.succ =
        (κ.singles.map (Fin.succEmb n)).sort := by
    exact StrictMonoOn.map_finsetSort
      (Fin.succEmb n) κ.singles
      (Fin.strictMono_succ.strictMonoOn
        (↑κ.singles : Set (Fin n)))
  rw [← hsort, List.map_map]
  rfl

theorem sort_erase_eq_sort_erase
    {α : Type*} [LinearOrder α]
    (s : Finset α) (a : α) :
    (s.erase a).sort = s.sort.erase a := by
  have hnodup : (s.sort.erase a).Nodup :=
    (s.sort_nodup (· ≤ ·)).erase a
  have hpairwise :
      (s.sort.erase a).Pairwise (· ≤ ·) :=
    (Finset.pairwise_sort s (· ≤ ·)).erase a
  have hsorted :=
    (List.toFinset_sort (· ≤ ·) hnodup).2 hpairwise
  have hfin :
      (s.sort.erase a).toFinset = s.erase a := by
    ext x
    rw [List.mem_toFinset,
      (s.sort_nodup (· ≤ ·)).mem_erase_iff,
      Finset.mem_erase, Finset.mem_sort (· ≤ ·)]
  simpa only [hfin] using hsorted

theorem sort_erase_eq_eraseIdx_idxOf
    {α : Type*} [LinearOrder α]
    (s : Finset α) (a : α) (ha : a ∈ s) :
    s.sort.erase a =
      s.sort.eraseIdx (s.sort.idxOf a) := by
  let j : Fin s.sort.length :=
    ⟨s.sort.idxOf a,
      List.idxOf_lt_length_iff.mpr
        (by
          rw [Finset.mem_sort (fun x y : α => x ≤ y)]
          exact ha)⟩
  have h := (s.sort_nodup (· ≤ ·)).erase_get j
  have hget : s.sort.get j = a :=
    List.getElem_idxOf j.isLt
  simpa only [hget, j] using h

theorem singleLabels_headEquiv_contraction
    {n : ℕ} {ι : Type*} (v : Fin (n + 1) → ι)
    (d : MarkedSingle (Fin n)) :
    partialPairingSingleLabels v (headEquiv n (Sum.inr d)) =
      (partialPairingSingleLabels (fun i => v i.succ) d.pairing).eraseIdx
        (d.pairing.singles.sort.idxOf d.index) := by
  rw [partialPairingSingleLabels, singles_headEquiv_contraction]
  have hsort :
      (d.pairing.singles.erase d.index).sort.map Fin.succ =
        ((d.pairing.singles.erase d.index).map
          (Fin.succEmb n)).sort := by
    exact StrictMonoOn.map_finsetSort
      (Fin.succEmb n)
      (d.pairing.singles.erase d.index)
      (Fin.strictMono_succ.strictMonoOn
        (↑(d.pairing.singles.erase d.index) : Set (Fin n)))
  rw [← hsort, List.map_map, partialPairingSingleLabels,
    List.eraseIdx_map, sort_erase_eq_sort_erase,
    sort_erase_eq_eraseIdx_idxOf
      d.pairing.singles d.index d.isSingle]
  rfl

theorem covarianceProduct_headEquiv_creation
    {n : ℕ} {ι : Type*} (C : ι → ι → ℝ)
    (v : Fin (n + 1) → ι)
    (κ : Anderson4D.PartialPairing (Fin n)) :
    partialPairingCovarianceProduct C v
        (headEquiv n (Sum.inl κ)) =
      partialPairingCovarianceProduct C (fun i => v i.succ) κ := by
  unfold partialPairingCovarianceProduct
  rw [representatives_headEquiv_creation]
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i _hi
  simp only [Fin.coe_succEmb]
  rw [headEquiv_creation_succ]

theorem covarianceProduct_headEquiv_contraction
    {n : ℕ} {ι : Type*} (C : ι → ι → ℝ)
    (v : Fin (n + 1) → ι)
    (d : MarkedSingle (Fin n)) :
    partialPairingCovarianceProduct C v
        (headEquiv n (Sum.inr d)) =
      C (v 0) (v d.index.succ) *
        partialPairingCovarianceProduct C (fun i => v i.succ)
          d.pairing := by
  unfold partialPairingCovarianceProduct
  rw [representatives_headEquiv_contraction]
  have hzero :
      (0 : Fin (n + 1)) ∉
        d.pairing.representatives.map (Fin.succEmb n) := by
    simp
  rw [Finset.prod_insert hzero, headEquiv_contraction_zero,
    Finset.prod_map]
  apply congrArg (C (v 0) (v d.index.succ) * ·)
  apply Finset.prod_congr rfl
  intro i hi
  have hine : i ≠ d.index := by
    intro h
    subst i
    have hpair :=
      (Anderson4D.PartialPairing.mem_representatives.mp hi).1
    exact hpair
      (Anderson4D.PartialPairing.mem_singles.mp d.isSingle)
  simp only [Fin.coe_succEmb]
  rw [headEquiv_contraction_succ_ne d i hine]

end PartialPairing

open PartialPairing

/-- Cast an increasing single rank to the definitionally equal length of
the ordered single-label list. -/
def singleLabelRankEquiv
    {n : ℕ} {ι : Type*} (v : Fin n → ι)
    (κ : Anderson4D.PartialPairing (Fin n)) :
    Fin κ.singles.card ≃
      Fin (partialPairingSingleLabels v κ).length :=
  finCongr (partialPairingSingleLabels_length v κ).symm

@[simp]
theorem singleLabelRankEquiv_val
    {n : ℕ} {ι : Type*} (v : Fin n → ι)
    (κ : Anderson4D.PartialPairing (Fin n))
    (j : Fin κ.singles.card) :
    (singleLabelRankEquiv v κ j).val = j.val :=
  rfl

theorem singleLabels_get_rank
    {n : ℕ} {ι : Type*} (v : Fin n → ι)
    (κ : Anderson4D.PartialPairing (Fin n))
    (j : Fin κ.singles.card) :
    (partialPairingSingleLabels v κ).get
        (singleLabelRankEquiv v κ j) =
      v (κ.singles.orderEmbOfFin rfl j) := by
  simp [partialPairingSingleLabels, singleLabelRankEquiv,
    Finset.orderEmbOfFin_apply]
  apply congrArg v
  exact getElem_congr_idx
    (singleLabelRankEquiv_val v κ j)

theorem singleLabels_headEquiv_rankedContraction
    {n : ℕ} {ι : Type*} (v : Fin (n + 1) → ι)
    (κ : Anderson4D.PartialPairing (Fin n))
    (j : Fin κ.singles.card) :
    partialPairingSingleLabels v
        (PartialPairing.headEquiv n
          (Sum.inr (PartialPairing.rankedSingleEquiv
            (Fin n) ⟨κ, j⟩))) =
      (partialPairingSingleLabels (fun i => v i.succ) κ).eraseIdx
        j := by
  rw [PartialPairing.singleLabels_headEquiv_contraction,
    PartialPairing.rankedSingleEquiv_pairing,
    PartialPairing.rankedSingleEquiv_idxOf]

theorem covarianceProduct_headEquiv_rankedContraction
    {n : ℕ} {ι : Type*} (C : ι → ι → ℝ)
    (v : Fin (n + 1) → ι)
    (κ : Anderson4D.PartialPairing (Fin n))
    (j : Fin κ.singles.card) :
    partialPairingCovarianceProduct C v
        (PartialPairing.headEquiv n
          (Sum.inr (PartialPairing.rankedSingleEquiv
            (Fin n) ⟨κ, j⟩))) =
      C (v 0) (v (κ.singles.orderEmbOfFin rfl j).succ) *
        partialPairingCovarianceProduct C (fun i => v i.succ) κ := by
  rw [PartialPairing.covarianceProduct_headEquiv_contraction,
    PartialPairing.rankedSingleEquiv_index,
    PartialPairing.rankedSingleEquiv_pairing]

theorem partialPairingChaosWeight_headEquiv_creation
    {n : ℕ} {ι Ω : Type*}
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : Fin (n + 1) → ι)
    (κ : Anderson4D.PartialPairing (Fin n)) (ω : Ω) :
    partialPairingChaosWeight C X v
        (PartialPairing.headEquiv n (Sum.inl κ)) ω =
      partialPairingCovarianceProduct C (fun i => v i.succ) κ *
        wickPolynomial C X
          (v 0 ::
            partialPairingSingleLabels (fun i => v i.succ) κ) ω := by
  rw [
    partialPairingChaosWeight_eq_pairProduct_mul_wickPolynomial,
    PartialPairing.covarianceProduct_headEquiv_creation,
    PartialPairing.singleLabels_headEquiv_creation]

theorem partialPairingChaosWeight_headEquiv_rankedContraction
    {n : ℕ} {ι Ω : Type*}
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : Fin (n + 1) → ι)
    (κ : Anderson4D.PartialPairing (Fin n))
    (j : Fin κ.singles.card) (ω : Ω) :
    partialPairingChaosWeight C X v
        (PartialPairing.headEquiv n
          (Sum.inr (PartialPairing.rankedSingleEquiv
            (Fin n) ⟨κ, j⟩))) ω =
      C (v 0) (v (κ.singles.orderEmbOfFin rfl j).succ) *
        partialPairingCovarianceProduct C (fun i => v i.succ) κ *
          wickPolynomial C X
            ((partialPairingSingleLabels
              (fun i => v i.succ) κ).eraseIdx j) ω := by
  rw [
    partialPairingChaosWeight_eq_pairProduct_mul_wickPolynomial,
    covarianceProduct_headEquiv_rankedContraction,
    singleLabels_headEquiv_rankedContraction]

theorem sum_ranked_contractions_eq_wick_contractions
    {n : ℕ} {ι Ω : Type*}
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : Fin (n + 1) → ι)
    (κ : Anderson4D.PartialPairing (Fin n)) (ω : Ω) :
    (∑ j : Fin κ.singles.card,
        C (v 0) (v (κ.singles.orderEmbOfFin rfl j).succ) *
          wickPolynomial C X
            ((partialPairingSingleLabels
              (fun i => v i.succ) κ).eraseIdx j) ω) =
      ∑ j : Fin
          (partialPairingSingleLabels
            (fun i => v i.succ) κ).length,
        C (v 0)
            ((partialPairingSingleLabels
              (fun i => v i.succ) κ).get j) *
          wickPolynomial C X
            ((partialPairingSingleLabels
              (fun i => v i.succ) κ).eraseIdx j) ω := by
  let labels :=
    partialPairingSingleLabels (fun i => v i.succ) κ
  let e := singleLabelRankEquiv (fun i => v i.succ) κ
  let f : Fin labels.length → ℝ :=
    fun j =>
      C (v 0) (labels.get j) *
        wickPolynomial C X (labels.eraseIdx j) ω
  calc
    _ = ∑ j : Fin κ.singles.card, f (e j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      dsimp only [f, labels, e]
      rw [singleLabels_get_rank]
      rfl
    _ = ∑ j : Fin labels.length, f j :=
      e.sum_comp f
    _ = _ := rfl

/-- One tail pairing obeys the creation--contraction split after adjoining
the new first variable. -/
theorem mul_partialPairingChaosWeight_eq_head_sum
    {n : ℕ} {ι Ω : Type*}
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : Fin (n + 1) → ι)
    (κ : Anderson4D.PartialPairing (Fin n)) (ω : Ω) :
    X (v 0) ω *
        partialPairingChaosWeight C X (fun i => v i.succ) κ ω =
      partialPairingChaosWeight C X v
          (PartialPairing.headEquiv n (Sum.inl κ)) ω +
        ∑ j : Fin κ.singles.card,
          partialPairingChaosWeight C X v
            (PartialPairing.headEquiv n
              (Sum.inr (PartialPairing.rankedSingleEquiv
                (Fin n) ⟨κ, j⟩))) ω := by
  rw [
    partialPairingChaosWeight_eq_pairProduct_mul_wickPolynomial,
    partialPairingChaosWeight_headEquiv_creation]
  simp_rw [
    partialPairingChaosWeight_headEquiv_rankedContraction]
  let labels :=
    partialPairingSingleLabels (fun i => v i.succ) κ
  let pairWeight :=
    partialPairingCovarianceProduct C (fun i => v i.succ) κ
  change
    X (v 0) ω *
        (pairWeight * wickPolynomial C X labels ω) =
      pairWeight *
          wickPolynomial C X (v 0 :: labels) ω +
        ∑ j : Fin κ.singles.card,
          C (v 0) (v (κ.singles.orderEmbOfFin rfl j).succ) *
            pairWeight *
              wickPolynomial C X (labels.eraseIdx j) ω
  calc
    _ = pairWeight *
        (X (v 0) ω * wickPolynomial C X labels ω) := by
      ring
    _ = pairWeight *
        (wickPolynomial C X (v 0 :: labels) ω +
          ∑ j : Fin labels.length,
            C (v 0) (labels.get j) *
              wickPolynomial C X (labels.eraseIdx j) ω) := by
      rw [mul_wickPolynomial_eq_create_add_contract]
    _ = pairWeight *
        (wickPolynomial C X (v 0 :: labels) ω +
          ∑ j : Fin κ.singles.card,
            C (v 0) (v (κ.singles.orderEmbOfFin rfl j).succ) *
              wickPolynomial C X (labels.eraseIdx j) ω) := by
      rw [sum_ranked_contractions_eq_wick_contractions]
    _ = _ := by
      rw [mul_add, Finset.mul_sum]
      apply congrArg
        (pairWeight * wickPolynomial C X (v 0 :: labels) ω + ·)
      apply Finset.sum_congr rfl
      intro j _hj
      ring

end ChaosDecomposition

/-- **Raw-product partial-pairing decomposition (paper (2.4)).**

Every two-cycle contributes one positive covariance factor.  The fixed
points, in their original carrier order, contribute the chaos projection of
degree equal to their number. -/
theorem rawProduct_eq_sum_partialPairingChaos
    {ι Ω : Type*} (C : ι → ι → ℝ) (X : ι → Ω → ℝ) :
    ∀ {n : ℕ} (v : Fin n → ι) (ω : Ω),
      (∏ i, X (v i) ω) =
        ∑ κ : PartialPairing (Fin n),
          partialPairingChaosWeight C X v κ ω := by
  intro n
  induction n with
  | zero =>
      intro v ω
      letI : Unique (PartialPairing (Fin 0)) :=
        { default := PartialPairing.id
          uniq := fun κ => by
            apply PartialPairing.ext
            exact fun i => Fin.elim0 i }
      simp [partialPairingChaosWeight,
        partialPairingCovarianceProduct,
        partialPairingSingleLabels, chaosProjProduct,
        PartialPairing.representatives,
        PartialPairing.representativesBy,
        PartialPairing.pairSupport, PartialPairing.singles]
  | succ n ih =>
      intro v ω
      rw [Fin.prod_univ_succ, ih (fun i => v i.succ) ω,
        Finset.mul_sum]
      calc
        (∑ κ : PartialPairing (Fin n),
            X (v 0) ω *
              partialPairingChaosWeight C X
                (fun i => v i.succ) κ ω) =
            ∑ κ : PartialPairing (Fin n),
              (partialPairingChaosWeight C X v
                  (ChaosDecomposition.PartialPairing.headEquiv n
                    (Sum.inl κ)) ω +
                ∑ j : Fin κ.singles.card,
                  partialPairingChaosWeight C X v
                    (ChaosDecomposition.PartialPairing.headEquiv n
                      (Sum.inr
                        (ChaosDecomposition.PartialPairing.rankedSingleEquiv
                          (Fin n) ⟨κ, j⟩))) ω) := by
          apply Finset.sum_congr rfl
          intro κ _hκ
          exact
            ChaosDecomposition.mul_partialPairingChaosWeight_eq_head_sum
              C X v κ ω
        _ =
            (∑ κ : PartialPairing (Fin n),
              partialPairingChaosWeight C X v
                (ChaosDecomposition.PartialPairing.headEquiv n
                  (Sum.inl κ)) ω) +
              ∑ κ : PartialPairing (Fin n),
                ∑ j : Fin κ.singles.card,
                  partialPairingChaosWeight C X v
                    (ChaosDecomposition.PartialPairing.headEquiv n
                      (Sum.inr
                        (ChaosDecomposition.PartialPairing.rankedSingleEquiv
                          (Fin n) ⟨κ, j⟩))) ω := by
          rw [Finset.sum_add_distrib]
        _ =
            (∑ κ : PartialPairing (Fin n),
              partialPairingChaosWeight C X v
                (ChaosDecomposition.PartialPairing.headEquiv n
                  (Sum.inl κ)) ω) +
              ∑ d :
                  ChaosDecomposition.PartialPairing.MarkedSingle (Fin n),
                partialPairingChaosWeight C X v
                  (ChaosDecomposition.PartialPairing.headEquiv n
                    (Sum.inr d)) ω := by
          apply congrArg
            ((∑ κ : PartialPairing (Fin n),
              partialPairingChaosWeight C X v
                (ChaosDecomposition.PartialPairing.headEquiv n
                  (Sum.inl κ)) ω) + ·)
          exact
            ChaosDecomposition.PartialPairing.sum_rankedSingle
              (fun d =>
                partialPairingChaosWeight C X v
                  (ChaosDecomposition.PartialPairing.headEquiv n
                    (Sum.inr d)) ω)
        _ = ∑ κ : PartialPairing (Fin (n + 1)),
              partialPairingChaosWeight C X v κ ω := by
          exact
            ChaosDecomposition.PartialPairing.sum_creation_contraction
              n (fun κ => partialPairingChaosWeight C X v κ ω)

/-- List form of the raw-product decomposition. -/
theorem listProduct_eq_sum_partialPairingChaos
    {ι Ω : Type*} (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (xs : List ι) (ω : Ω) :
    (xs.map fun x => X x ω).prod =
      ∑ κ : PartialPairing (Fin xs.length),
        partialPairingChaosWeight C X xs.get κ ω := by
  calc
    (xs.map fun x => X x ω).prod =
        ∏ i : Fin xs.length, X (xs.get i) ω := by
      rw [← List.prod_ofFn]
      rw [List.ofFn_comp' xs.get (fun x => X x ω),
        List.ofFn_get]
    _ = _ := rawProduct_eq_sum_partialPairingChaos C X xs.get ω

namespace NoiseModel

/-- Equation (2.4) specialized to the mollified noise.  The covariance
factors have the positive sign, and the singles retain their ambient order.
For positive `ε`, `integral_xiEps_mul_eq_etaEpsT4` identifies the displayed
kernel with the actual two-point covariance. -/
theorem xiEpsProduct_eq_sum_partialPairingChaos
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ} (_hε : 0 < ε)
    {n : ℕ} (z : Fin n → T4) (ω : M.Ω) :
    (∏ i, M.xiEps ρ ε ω (z i)) =
      ∑ κ : PartialPairing (Fin n),
        (∏ i ∈ κ.representatives,
            ρ.etaEpsT4 ε (z i - z (κ i))) *
          chaosProjProduct κ.singles.card
            (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
            (fun x ω' => M.xiEps ρ ε ω' x)
            (partialPairingSingleLabels z κ) ω := by
  simpa [partialPairingChaosWeight,
    partialPairingCovarianceProduct] using
    rawProduct_eq_sum_partialPairingChaos
      (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
      (fun x ω' => M.xiEps ρ ε ω' x) z ω

end NoiseModel

end

end Anderson4D
