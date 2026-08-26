import Anderson4D.DetParametrix.Core.FinalBound
import Anderson4D.Combinatorics.PairingHeadCases

/-!
# The doubled pairing behind the deterministic moment expansion

Paper §4.2 combines the two within-copy partial pairings and the bijection
between their single sets into one full pairing of the doubled carrier.
This file constructs that pairing explicitly.  It is the combinatorial
input required before the R-322 interval reducer can be reused for R-324.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- The involution on the disjoint union of the two copies.  Paired
indices stay in their own copy; single indices are joined across the two
copies using `π`. -/
def momentCombinedSumMap
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    Fin m ⊕ Fin m → Fin m ⊕ Fin m
  | Sum.inl i =>
      if hi : i ∈ κp.singles then
        Sum.inr (π ⟨i, hi⟩).1
      else
        Sum.inl (κp i)
  | Sum.inr j =>
      if hj : j ∈ κm.singles then
        Sum.inl (π.symm ⟨j, hj⟩).1
      else
        Sum.inr (κm j)

theorem momentCombinedSumMap_involutive
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    Function.Involutive (momentCombinedSumMap κp κm π) := by
  intro x
  rcases x with i | j
  · by_cases hi : i ∈ κp.singles
    · have hj : (π ⟨i, hi⟩).1 ∈ κm.singles :=
        (π ⟨i, hi⟩).2
      simp only [momentCombinedSumMap, dif_pos hi, dif_pos hj]
      exact congrArg Sum.inl
        (congrArg Subtype.val (π.symm_apply_apply ⟨i, hi⟩))
    · have hiNe : κp i ≠ i := by
        simpa only [PartialPairing.mem_singles, not_false_eq_true]
          using hi
      have hki : κp i ∉ κp.singles := by
        rw [PartialPairing.mem_singles]
        intro hfix
        exact hiNe (κp.injective hfix)
      simp only [momentCombinedSumMap, dif_neg hi, dif_neg hki,
        κp.apply_apply]
  · by_cases hj : j ∈ κm.singles
    · have hi : (π.symm ⟨j, hj⟩).1 ∈ κp.singles :=
        (π.symm ⟨j, hj⟩).2
      simp only [momentCombinedSumMap, dif_pos hj, dif_pos hi]
      exact congrArg Sum.inr
        (congrArg Subtype.val (π.apply_symm_apply ⟨j, hj⟩))
    · have hjNe : κm j ≠ j := by
        simpa only [PartialPairing.mem_singles, not_false_eq_true]
          using hj
      have hkj : κm j ∉ κm.singles := by
        rw [PartialPairing.mem_singles]
        intro hfix
        exact hjNe (κm.injective hfix)
      simp only [momentCombinedSumMap, dif_neg hj, dif_neg hkj,
        κm.apply_apply]

/-- The combined pairing before identifying the disjoint union with
`Fin (2m)`. -/
def momentCombinedSumPairing
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    PartialPairing (Fin m ⊕ Fin m) where
  toFun := momentCombinedSumMap κp κm π
  involutive := momentCombinedSumMap_involutive κp κm π

/-- Order-preserving identification of the left and right copies with
the two consecutive halves of `Fin (2m)`. -/
def momentDoubleFinEquiv (m : ℕ) :
    (Fin m ⊕ Fin m) ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (two_mul m).symm)

@[simp]
theorem momentDoubleFinEquiv_apply_inl
    {m : ℕ} (i : Fin m) :
    momentDoubleFinEquiv m (Sum.inl i) =
      leftMomentIndex i := by
  apply Fin.ext
  rfl

@[simp]
theorem momentDoubleFinEquiv_apply_inr
    {m : ℕ} (j : Fin m) :
    momentDoubleFinEquiv m (Sum.inr j) =
      rightMomentIndex j := by
  apply Fin.ext
  rfl

@[simp]
theorem momentDoubleFinEquiv_symm_leftMomentIndex
    {m : ℕ} (i : Fin m) :
    (momentDoubleFinEquiv m).symm (leftMomentIndex i) =
      Sum.inl i := by
  rw [← momentDoubleFinEquiv_apply_inl i]
  exact Equiv.symm_apply_apply _ _

@[simp]
theorem momentDoubleFinEquiv_symm_rightMomentIndex
    {m : ℕ} (j : Fin m) :
    (momentDoubleFinEquiv m).symm (rightMomentIndex j) =
      Sum.inr j := by
  rw [← momentDoubleFinEquiv_apply_inr j]
  exact Equiv.symm_apply_apply _ _

/-- The full pairing of the doubled carrier described between paper
(4.16) and (4.18). -/
def momentCombinedPairing
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    PartialPairing (Fin (2 * m)) :=
  PartialPairing.congr (momentDoubleFinEquiv m)
    (momentCombinedSumPairing κp κm π)

theorem momentCombinedSumPairing_isFull
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentCombinedSumPairing κp κm π).IsFull := by
  intro x
  rcases x with i | j
  · by_cases hi : i ∈ κp.singles
    · change momentCombinedSumMap κp κm π (Sum.inl i) ≠
          Sum.inl i
      simp [momentCombinedSumMap, hi]
    · change momentCombinedSumMap κp κm π (Sum.inl i) ≠
          Sum.inl i
      simp only [momentCombinedSumMap, dif_neg hi]
      intro h
      apply hi
      rw [PartialPairing.mem_singles]
      exact Sum.inl.inj h
  · by_cases hj : j ∈ κm.singles
    · change momentCombinedSumMap κp κm π (Sum.inr j) ≠
          Sum.inr j
      simp [momentCombinedSumMap, hj]
    · change momentCombinedSumMap κp κm π (Sum.inr j) ≠
          Sum.inr j
      simp only [momentCombinedSumMap, dif_neg hj]
      intro h
      apply hj
      rw [PartialPairing.mem_singles]
      exact Sum.inr.inj h

/-- Every contraction triple produces a full pairing, even though the
two within-copy pairings may have singles. -/
theorem momentCombinedPairing_isFull
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentCombinedPairing κp κm π).IsFull :=
  (momentCombinedSumPairing_isFull κp κm π).congr
    (momentDoubleFinEquiv m)

/-! ## Evaluation on the two copies -/

@[simp]
theorem momentCombinedPairing_left_single
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (i : Fin m) (hi : i ∈ κp.singles) :
    momentCombinedPairing κp κm π (leftMomentIndex i) =
      rightMomentIndex (π ⟨i, hi⟩).1 := by
  have hiEq : κp i = i :=
    PartialPairing.mem_singles.mp hi
  simp [momentCombinedPairing, momentCombinedSumPairing,
    momentCombinedSumMap, hiEq]

@[simp]
theorem momentCombinedPairing_left_pair
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (i : Fin m) (hi : i ∉ κp.singles) :
    momentCombinedPairing κp κm π (leftMomentIndex i) =
      leftMomentIndex (κp i) := by
  have hiNe : κp i ≠ i := by
    simpa only [PartialPairing.mem_singles,
      not_false_eq_true] using hi
  simp [momentCombinedPairing, momentCombinedSumPairing,
    momentCombinedSumMap, hiNe]

@[simp]
theorem momentCombinedPairing_right_single
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (j : Fin m) (hj : j ∈ κm.singles) :
    momentCombinedPairing κp κm π (rightMomentIndex j) =
      leftMomentIndex (π.symm ⟨j, hj⟩).1 := by
  have hjEq : κm j = j :=
    PartialPairing.mem_singles.mp hj
  simp [momentCombinedPairing, momentCombinedSumPairing,
    momentCombinedSumMap, hjEq]

@[simp]
theorem momentCombinedPairing_right_pair
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (j : Fin m) (hj : j ∉ κm.singles) :
    momentCombinedPairing κp κm π (rightMomentIndex j) =
      rightMomentIndex (κm j) := by
  have hjNe : κm j ≠ j := by
    simpa only [PartialPairing.mem_singles,
      not_false_eq_true] using hj
  simp [momentCombinedPairing, momentCombinedSumPairing,
    momentCombinedSumMap, hjNe]

/-! ## Lower-endpoint classification -/

@[simp]
theorem leftMomentIndex_lt_leftMomentIndex_iff
    {m : ℕ} (i j : Fin m) :
    leftMomentIndex i < leftMomentIndex j ↔ i < j := by
  rfl

@[simp]
theorem rightMomentIndex_lt_rightMomentIndex_iff
    {m : ℕ} (i j : Fin m) :
    rightMomentIndex i < rightMomentIndex j ↔ i < j := by
  simp only [rightMomentIndex, Fin.mk_lt_mk]
  omega

@[simp]
theorem leftMomentIndex_lt_rightMomentIndex
    {m : ℕ} (i j : Fin m) :
    leftMomentIndex i < rightMomentIndex j := by
  simp only [leftMomentIndex, rightMomentIndex, Fin.mk_lt_mk]
  omega

@[simp]
theorem not_rightMomentIndex_lt_leftMomentIndex
    {m : ℕ} (i j : Fin m) :
    ¬rightMomentIndex i < leftMomentIndex j := by
  simp only [leftMomentIndex, rightMomentIndex, Fin.mk_lt_mk,
    not_lt]
  omega

/-- A left-copy index is the lower endpoint either of its within-copy
pair or, when it is single in `κp`, of its cross-copy pair. -/
theorem leftMomentIndex_lt_combined_iff
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) (i : Fin m) :
    leftMomentIndex i <
        momentCombinedPairing κp κm π (leftMomentIndex i) ↔
      i ∈ κp.singles ∨
        (i ∉ κp.singles ∧ i < κp i) := by
  by_cases hi : i ∈ κp.singles
  · rw [momentCombinedPairing_left_single κp κm π i hi]
    simp only [leftMomentIndex_lt_rightMomentIndex, true_iff]
    exact Or.inl hi
  · rw [momentCombinedPairing_left_pair κp κm π i hi]
    simp only [leftMomentIndex_lt_leftMomentIndex_iff]
    simp only [hi, false_or, not_false_eq_true, true_and]

/-- A right-copy index is a lower endpoint precisely when it is the
lower endpoint of a within-right-copy pair.  Cross pairs are already
counted from their left-copy endpoints. -/
theorem rightMomentIndex_lt_combined_iff
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) (j : Fin m) :
    rightMomentIndex j <
        momentCombinedPairing κp κm π (rightMomentIndex j) ↔
      j ∉ κm.singles ∧ j < κm j := by
  by_cases hj : j ∈ κm.singles
  · rw [momentCombinedPairing_right_single κp κm π j hj]
    simp only [not_rightMomentIndex_lt_leftMomentIndex,
      hj, not_true_eq_false, false_and]
  · rw [momentCombinedPairing_right_pair κp κm π j hj]
    simp only [rightMomentIndex_lt_rightMomentIndex_iff,
      hj, not_false_eq_true, true_and]

/-! ## Lower-endpoint finset decomposition -/

def momentCombinedLowerEndpoints
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    Finset (Fin (2 * m)) :=
  (momentCombinedPairing κp κm π).pairSupport.filter
    fun i => i < momentCombinedPairing κp κm π i

def leftMomentPairLowerEndpoints
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    Finset (Fin (2 * m)) :=
  (κp.pairSupport.filter fun i => i < κp i).image
    leftMomentIndex

def rightMomentPairLowerEndpoints
    {m : ℕ} (κm : PartialPairing (Fin m)) :
    Finset (Fin (2 * m)) :=
  (κm.pairSupport.filter fun j => j < κm j).image
    rightMomentIndex

def momentCrossLowerEndpoints
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    Finset (Fin (2 * m)) :=
  κp.singles.image leftMomentIndex

theorem leftMomentIndex_injective {m : ℕ} :
    Function.Injective
      (leftMomentIndex : Fin m → Fin (2 * m)) := by
  intro i j hij
  exact Fin.ext
    (congrArg (fun x : Fin (2 * m) => x.val) hij)

theorem rightMomentIndex_injective {m : ℕ} :
    Function.Injective
      (rightMomentIndex : Fin m → Fin (2 * m)) := by
  intro i j hij
  apply Fin.ext
  have hval :=
    congrArg (fun x : Fin (2 * m) => x.val) hij
  simp only [rightMomentIndex] at hval
  omega

/-! ## Fully paired sets embedded in either half -/

/-- A fully paired set in the left copy remains fully paired for the
combined doubled pairing.  In particular, every interval extracted from
`κp` in paper §4.2 Step 2 is a legitimate primitive block of the
combined contraction pairing. -/
theorem IsFullyPairedOn.image_leftMomentIndex
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin m)}
    (hB : IsFullyPairedOn κp B) :
    IsFullyPairedOn (momentCombinedPairing κp κm π)
      (B.image leftMomentIndex) := by
  constructor
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hiNot : i ∉ κp.singles := by
      rw [PartialPairing.mem_singles]
      exact hB.ne_of_mem hi
    rw [momentCombinedPairing_left_pair κp κm π i hiNot]
    exact fun h =>
      hB.ne_of_mem hi (leftMomentIndex_injective h)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hiNot : i ∉ κp.singles := by
      rw [PartialPairing.mem_singles]
      exact hB.ne_of_mem hi
    rw [momentCombinedPairing_left_pair κp κm π i hiNot]
    exact Finset.mem_image.mpr
      ⟨κp i, hB.apply_mem hi, rfl⟩

/-- Right-copy counterpart of `IsFullyPairedOn.image_leftMomentIndex`. -/
theorem IsFullyPairedOn.image_rightMomentIndex
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin m)}
    (hB : IsFullyPairedOn κm B) :
    IsFullyPairedOn (momentCombinedPairing κp κm π)
      (B.image rightMomentIndex) := by
  constructor
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjNot : j ∉ κm.singles := by
      rw [PartialPairing.mem_singles]
      exact hB.ne_of_mem hj
    rw [momentCombinedPairing_right_pair κp κm π j hjNot]
    exact fun h =>
      hB.ne_of_mem hj (rightMomentIndex_injective h)
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjNot : j ∉ κm.singles := by
      rw [PartialPairing.mem_singles]
      exact hB.ne_of_mem hj
    rw [momentCombinedPairing_right_pair κp κm π j hjNot]
    exact Finset.mem_image.mpr
      ⟨κm j, hB.apply_mem hj, rfl⟩

/-- Relative intervals commute with the order-preserving left-copy
embedding into the doubled carrier. -/
theorem image_leftMomentIndex_relIcc
    {m : ℕ} (active : Finset (Fin m)) (a b : Fin m) :
    (relIcc active a b).image leftMomentIndex =
      relIcc (active.image leftMomentIndex)
        (leftMomentIndex a) (leftMomentIndex b) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hiActive, hai, hib⟩ := mem_relIcc.mp hi
    have hai' :
        leftMomentIndex a ≤ leftMomentIndex i := by
      change a.val ≤ i.val
      exact hai
    have hib' :
        leftMomentIndex i ≤ leftMomentIndex b := by
      change i.val ≤ b.val
      exact hib
    exact mem_relIcc.mpr
      ⟨Finset.mem_image.mpr ⟨i, hiActive, rfl⟩,
        hai', hib'⟩
  · intro hx
    obtain ⟨hxActive, hax, hxb⟩ := mem_relIcc.mp hx
    obtain ⟨i, hiActive, rfl⟩ := Finset.mem_image.mp hxActive
    have hai : a ≤ i := by
      change a.val ≤ i.val
      change a.val ≤ i.val at hax
      exact hax
    have hib : i ≤ b := by
      change i.val ≤ b.val
      change i.val ≤ b.val at hxb
      exact hxb
    exact Finset.mem_image.mpr
      ⟨i, mem_relIcc.mpr
        ⟨hiActive, hai, hib⟩,
        rfl⟩

/-- Relative intervals commute with the order-preserving right-copy
embedding into the doubled carrier. -/
theorem image_rightMomentIndex_relIcc
    {m : ℕ} (active : Finset (Fin m)) (a b : Fin m) :
    (relIcc active a b).image rightMomentIndex =
      relIcc (active.image rightMomentIndex)
        (rightMomentIndex a) (rightMomentIndex b) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hiActive, hai, hib⟩ := mem_relIcc.mp hi
    have hai' :
        rightMomentIndex a ≤ rightMomentIndex i := by
      change m + a.val ≤ m + i.val
      have haiVal : a.val ≤ i.val := hai
      omega
    have hib' :
        rightMomentIndex i ≤ rightMomentIndex b := by
      change m + i.val ≤ m + b.val
      have hibVal : i.val ≤ b.val := hib
      omega
    exact mem_relIcc.mpr
      ⟨Finset.mem_image.mpr ⟨i, hiActive, rfl⟩,
        hai', hib'⟩
  · intro hx
    obtain ⟨hxActive, hax, hxb⟩ := mem_relIcc.mp hx
    obtain ⟨i, hiActive, rfl⟩ := Finset.mem_image.mp hxActive
    have hai : a ≤ i := by
      change a.val ≤ i.val
      change m + a.val ≤ m + i.val at hax
      omega
    have hib : i ≤ b := by
      change i.val ≤ b.val
      change m + i.val ≤ m + b.val at hxb
      omega
    exact Finset.mem_image.mpr
      ⟨i, mem_relIcc.mpr
        ⟨hiActive, hai, hib⟩,
        rfl⟩

/-- A relative fully paired interval selected in the left copy is still
a relative fully paired interval of the combined pairing on the embedded
active carrier. -/
theorem IsRelFullyPaired.image_leftMomentIndex
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {active : Finset (Fin m)} {a b : Fin m}
    (h : IsRelFullyPaired κp active a b) :
    IsRelFullyPaired (momentCombinedPairing κp κm π)
      (active.image leftMomentIndex)
      (leftMomentIndex a) (leftMomentIndex b) := by
  refine ⟨Finset.mem_image.mpr ⟨a, h.left_mem, rfl⟩,
    Finset.mem_image.mpr ⟨b, h.right_mem, rfl⟩,
    ?_, ?_⟩
  · change a.val ≤ b.val
    exact h.le
  · rw [← image_leftMomentIndex_relIcc]
    exact h.isFullyPairedOn.image_leftMomentIndex

/-- Right-copy counterpart of
`IsRelFullyPaired.image_leftMomentIndex`. -/
theorem IsRelFullyPaired.image_rightMomentIndex
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {active : Finset (Fin m)} {a b : Fin m}
    (h : IsRelFullyPaired κm active a b) :
    IsRelFullyPaired (momentCombinedPairing κp κm π)
      (active.image rightMomentIndex)
      (rightMomentIndex a) (rightMomentIndex b) := by
  refine ⟨Finset.mem_image.mpr ⟨a, h.left_mem, rfl⟩,
    Finset.mem_image.mpr ⟨b, h.right_mem, rfl⟩,
    ?_, ?_⟩
  · change m + a.val ≤ m + b.val
    have hab : a.val ≤ b.val := h.le
    omega
  · rw [← image_rightMomentIndex_relIcc]
    exact h.isFullyPairedOn.image_rightMomentIndex

/-- If the combined image of a left-copy index stays in a left-image
set, then that index was not a single. -/
theorem not_mem_singles_of_combined_mem_image_left
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin m)} {i : Fin m}
    (hi :
      momentCombinedPairing κp κm π (leftMomentIndex i) ∈
        B.image leftMomentIndex) :
    i ∉ κp.singles := by
  intro hiSingle
  rw [momentCombinedPairing_left_single
    κp κm π i hiSingle] at hi
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  have hval := congrArg Fin.val hj
  simp only [leftMomentIndex, rightMomentIndex] at hval
  have hjLt := j.isLt
  omega

/-- Right-copy counterpart of
`not_mem_singles_of_combined_mem_image_left`. -/
theorem not_mem_singles_of_combined_mem_image_right
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin m)} {j : Fin m}
    (hj :
      momentCombinedPairing κp κm π (rightMomentIndex j) ∈
        B.image rightMomentIndex) :
    j ∉ κm.singles := by
  intro hjSingle
  rw [momentCombinedPairing_right_single
    κp κm π j hjSingle] at hj
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
  have hval := congrArg Fin.val hi
  simp only [leftMomentIndex, rightMomentIndex] at hval
  have hiLt := i.isLt
  omega

/-- Full pairing on an embedded left-copy set reflects back to the
original partial pairing. -/
theorem IsFullyPairedOn.of_image_leftMomentIndex
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin m)}
    (hB :
      IsFullyPairedOn (momentCombinedPairing κp κm π)
        (B.image leftMomentIndex)) :
    IsFullyPairedOn κp B := by
  constructor
  · intro i hi
    have himage :
        leftMomentIndex i ∈ B.image leftMomentIndex :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hmap := hB.apply_mem himage
    have hiNot :=
      not_mem_singles_of_combined_mem_image_left hmap
    simpa only [PartialPairing.mem_singles,
      not_false_eq_true] using hiNot
  · intro i hi
    have himage :
        leftMomentIndex i ∈ B.image leftMomentIndex :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hmap := hB.apply_mem himage
    have hiNot :=
      not_mem_singles_of_combined_mem_image_left hmap
    rw [momentCombinedPairing_left_pair
      κp κm π i hiNot] at hmap
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hmap
    have hji' : j = κp i :=
      leftMomentIndex_injective hji
    simpa only [hji'] using hj

/-- Full pairing on an embedded right-copy set reflects back to the
original partial pairing. -/
theorem IsFullyPairedOn.of_image_rightMomentIndex
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {B : Finset (Fin m)}
    (hB :
      IsFullyPairedOn (momentCombinedPairing κp κm π)
        (B.image rightMomentIndex)) :
    IsFullyPairedOn κm B := by
  constructor
  · intro j hj
    have hjimage :
        rightMomentIndex j ∈ B.image rightMomentIndex :=
      Finset.mem_image.mpr ⟨j, hj, rfl⟩
    have hmap := hB.apply_mem hjimage
    have hjNot :=
      not_mem_singles_of_combined_mem_image_right hmap
    simpa only [PartialPairing.mem_singles,
      not_false_eq_true] using hjNot
  · intro j hj
    have hjimage :
        rightMomentIndex j ∈ B.image rightMomentIndex :=
      Finset.mem_image.mpr ⟨j, hj, rfl⟩
    have hmap := hB.apply_mem hjimage
    have hjNot :=
      not_mem_singles_of_combined_mem_image_right hmap
    rw [momentCombinedPairing_right_pair
      κp κm π j hjNot] at hmap
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hmap
    have hij' : i = κm j :=
      rightMomentIndex_injective hij
    simpa only [hij'] using hi

/-- Exact left-copy reflection principle for relative fully paired
intervals. -/
theorem isRelFullyPaired_image_leftMomentIndex_iff
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {active : Finset (Fin m)} {a b : Fin m} :
    IsRelFullyPaired (momentCombinedPairing κp κm π)
        (active.image leftMomentIndex)
        (leftMomentIndex a) (leftMomentIndex b) ↔
      IsRelFullyPaired κp active a b := by
  constructor
  · intro h
    have ha : a ∈ active := by
      obtain ⟨i, hi, hia⟩ :=
        Finset.mem_image.mp h.left_mem
      have hia' : i = a :=
        leftMomentIndex_injective hia
      simpa only [hia'] using hi
    have hb : b ∈ active := by
      obtain ⟨i, hi, hib⟩ :=
        Finset.mem_image.mp h.right_mem
      have hib' : i = b :=
        leftMomentIndex_injective hib
      simpa only [hib'] using hi
    refine ⟨ha, hb, ?_, ?_⟩
    · change a.val ≤ b.val
      exact h.le
    · have hfull := h.isFullyPairedOn
      rw [← image_leftMomentIndex_relIcc] at hfull
      exact hfull.of_image_leftMomentIndex
  · exact fun h => h.image_leftMomentIndex

/-- Exact right-copy reflection principle for relative fully paired
intervals. -/
theorem isRelFullyPaired_image_rightMomentIndex_iff
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {active : Finset (Fin m)} {a b : Fin m} :
    IsRelFullyPaired (momentCombinedPairing κp κm π)
        (active.image rightMomentIndex)
        (rightMomentIndex a) (rightMomentIndex b) ↔
      IsRelFullyPaired κm active a b := by
  constructor
  · intro h
    have ha : a ∈ active := by
      obtain ⟨j, hj, hja⟩ :=
        Finset.mem_image.mp h.left_mem
      have hja' : j = a :=
        rightMomentIndex_injective hja
      simpa only [hja'] using hj
    have hb : b ∈ active := by
      obtain ⟨j, hj, hjb⟩ :=
        Finset.mem_image.mp h.right_mem
      have hjb' : j = b :=
        rightMomentIndex_injective hjb
      simpa only [hjb'] using hj
    refine ⟨ha, hb, ?_, ?_⟩
    · have hab : m + a.val ≤ m + b.val := h.le
      change a.val ≤ b.val
      omega
    · have hfull := h.isFullyPairedOn
      rw [← image_rightMomentIndex_relIcc] at hfull
      exact hfull.of_image_rightMomentIndex
  · exact fun h => h.image_rightMomentIndex

/-! ## The doubled residual carrier after within-half reduction -/

/-- The active carrier left after running Definition 3.1 separately in
the two copies, embedded into the doubled order. -/
def momentResidualActive
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    Finset (Fin (2 * m)) :=
  (finalActive κp).image leftMomentIndex ∪
    (finalActive κm).image rightMomentIndex

/-- The within-half extraction removes only closed paired blocks.
Consequently the remaining within-copy pairs stay inside the residual
carrier, while every surviving single is joined by `π` to a surviving
single in the other half.  Thus the combined pairing is full on the
residual doubled carrier. -/
theorem momentResidualActive_isFullyPairedOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    IsFullyPairedOn (momentCombinedPairing κp κm π)
      (momentResidualActive κp κm) := by
  constructor
  · intro x _
    exact momentCombinedPairing_isFull κp κm π x
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      by_cases hiSingle : i ∈ κp.singles
      · rw [momentCombinedPairing_left_single
          κp κm π i hiSingle]
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr
            ⟨(π ⟨i, hiSingle⟩).1,
              singles_subset_finalActive κm
                (π ⟨i, hiSingle⟩).2,
              rfl⟩)
      · rw [momentCombinedPairing_left_pair
          κp κm π i hiSingle]
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr
            ⟨κp i, finalActive_apply_mem κp hi, rfl⟩)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      by_cases hjSingle : j ∈ κm.singles
      · rw [momentCombinedPairing_right_single
          κp κm π j hjSingle]
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr
            ⟨(π.symm ⟨j, hjSingle⟩).1,
              singles_subset_finalActive κp
                (π.symm ⟨j, hjSingle⟩).2,
              rfl⟩)
      · rw [momentCombinedPairing_right_pair
          κp κm π j hjSingle]
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr
            ⟨κm j, finalActive_apply_mem κm hj, rfl⟩)

theorem disjoint_leftMomentPair_rightMomentPair
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    Disjoint (leftMomentPairLowerEndpoints κp)
      (rightMomentPairLowerEndpoints κm) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [leftMomentPairLowerEndpoints] at ha
  rw [rightMomentPairLowerEndpoints] at hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hb
  have hval := congrArg Fin.val hji
  simp only [leftMomentIndex, rightMomentIndex] at hval
  have hiLt := i.isLt
  omega

theorem disjoint_leftMomentPair_cross
    {m : ℕ} (κp : PartialPairing (Fin m)) :
    Disjoint (leftMomentPairLowerEndpoints κp)
      (momentCrossLowerEndpoints κp) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [leftMomentPairLowerEndpoints] at ha
  rw [momentCrossLowerEndpoints] at hb
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hb
  have hji' : j = i :=
    leftMomentIndex_injective hji
  subst j
  exact
    (PartialPairing.mem_pairSupport.mp
      (Finset.mem_filter.mp hi).1)
      (PartialPairing.mem_singles.mp hj)

theorem disjoint_rightMomentPair_cross
    {m : ℕ} (κm κp : PartialPairing (Fin m)) :
    Disjoint (rightMomentPairLowerEndpoints κm)
      (momentCrossLowerEndpoints κp) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [rightMomentPairLowerEndpoints] at ha
  rw [momentCrossLowerEndpoints] at hb
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hb
  have hval := congrArg Fin.val hij
  simp only [leftMomentIndex, rightMomentIndex] at hval
  have hiLt := i.isLt
  omega

/-- The lower endpoints of the doubled full pairing split into the
within-left, within-right, and cross-copy classes. -/
theorem momentCombinedLowerEndpoints_eq
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    momentCombinedLowerEndpoints κp κm π =
      leftMomentPairLowerEndpoints κp ∪
        rightMomentPairLowerEndpoints κm ∪
          momentCrossLowerEndpoints κp := by
  have hsupport :
      (momentCombinedPairing κp κm π).pairSupport =
        Finset.univ :=
    PartialPairing.isFull_iff_pairSupport_eq_univ.mp
      (momentCombinedPairing_isFull κp κm π)
  ext a
  obtain ⟨s, rfl⟩ :=
    (momentDoubleFinEquiv m).surjective a
  rcases s with i | j
  · simp only [momentDoubleFinEquiv_apply_inl]
    simp only [momentCombinedLowerEndpoints, hsupport,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [leftMomentIndex_lt_combined_iff]
    simp [leftMomentPairLowerEndpoints,
      rightMomentPairLowerEndpoints,
      momentCrossLowerEndpoints,
      PartialPairing.mem_pairSupport,
      leftMomentIndex, rightMomentIndex]
    constructor
    · rintro (hfix | ⟨hne, hlt⟩)
      · exact Or.inr (Or.inr ⟨i, hfix, rfl⟩)
      · exact Or.inl ⟨i, ⟨hne, hlt⟩, rfl⟩
    · rintro (⟨a, ha, haval⟩ |
        ⟨a, ha, haval⟩ | ⟨a, ha, haval⟩)
      · have hai : a = i := Fin.ext haval
        subst a
        exact Or.inr ha
      · have haLt := a.isLt
        have hiLt := i.isLt
        omega
      · have hai : a = i := Fin.ext haval
        subst a
        exact Or.inl ha
  · simp only [momentDoubleFinEquiv_apply_inr]
    simp only [momentCombinedLowerEndpoints, hsupport,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rightMomentIndex_lt_combined_iff]
    simp [leftMomentPairLowerEndpoints,
      rightMomentPairLowerEndpoints,
      momentCrossLowerEndpoints,
      PartialPairing.mem_pairSupport,
      leftMomentIndex, rightMomentIndex]
    constructor
    · rintro ⟨hne, hlt⟩
      exact Or.inr (Or.inl ⟨j, ⟨hne, hlt⟩, rfl⟩)
    · rintro (⟨a, ha, haval⟩ |
        ⟨a, ha, haval⟩ | ⟨a, ha, haval⟩)
      · have haLt := a.isLt
        have hjLt := j.isLt
        omega
      · have haj : a = j := Fin.ext haval
        subst a
        exact ha
      · have haLt := a.isLt
        have hjLt := j.isLt
        omega

/-- Product form of the three-way lower-endpoint partition. -/
theorem prod_momentCombinedLowerEndpoints
    {M : Type*} [CommMonoid M]
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (f : Fin (2 * m) → M) :
    (∏ a ∈ momentCombinedLowerEndpoints κp κm π, f a) =
      (∏ a ∈ leftMomentPairLowerEndpoints κp, f a) *
        (∏ a ∈ rightMomentPairLowerEndpoints κm, f a) *
          ∏ a ∈ momentCrossLowerEndpoints κp, f a := by
  have hLR :=
    disjoint_leftMomentPair_rightMomentPair κp κm
  have hLC :=
    disjoint_leftMomentPair_cross κp
  have hRC :=
    disjoint_rightMomentPair_cross κm κp
  have hUnion :
      Disjoint
        (leftMomentPairLowerEndpoints κp ∪
          rightMomentPairLowerEndpoints κm)
        (momentCrossLowerEndpoints κp) :=
    Finset.disjoint_union_left.mpr ⟨hLC, hRC⟩
  rw [momentCombinedLowerEndpoints_eq,
    Finset.prod_union hUnion,
    Finset.prod_union hLR]

theorem prod_leftMomentPairLowerEndpoints
    {M : Type*} [CommMonoid M]
    {m : ℕ} (κp : PartialPairing (Fin m))
    (f : Fin (2 * m) → M) :
    (∏ a ∈ leftMomentPairLowerEndpoints κp, f a) =
      ∏ i ∈ κp.pairSupport.filter (fun i => i < κp i),
        f (leftMomentIndex i) := by
  unfold leftMomentPairLowerEndpoints
  exact Finset.prod_image leftMomentIndex_injective.injOn

theorem prod_rightMomentPairLowerEndpoints
    {M : Type*} [CommMonoid M]
    {m : ℕ} (κm : PartialPairing (Fin m))
    (f : Fin (2 * m) → M) :
    (∏ a ∈ rightMomentPairLowerEndpoints κm, f a) =
      ∏ j ∈ κm.pairSupport.filter (fun j => j < κm j),
        f (rightMomentIndex j) := by
  unfold rightMomentPairLowerEndpoints
  exact Finset.prod_image rightMomentIndex_injective.injOn

theorem prod_momentCrossLowerEndpoints
    {M : Type*} [CommMonoid M]
    {m : ℕ} (κp : PartialPairing (Fin m))
    (f : Fin (2 * m) → M) :
    (∏ a ∈ momentCrossLowerEndpoints κp, f a) =
      ∏ i ∈ κp.singles, f (leftMomentIndex i) := by
  unfold momentCrossLowerEndpoints
  exact Finset.prod_image leftMomentIndex_injective.injOn

/-! ## Covariance-product identification -/

/-- The three covariance products in (4.18) are exactly the covariance
product of the combined full pairing on the doubled carrier. -/
theorem primitiveCovarianceProduct_momentCombinedPairing
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    primitiveCovarianceProduct ρ ε m
        (momentCombinedPairing κp κm π) v =
      (∏ i ∈ κp.pairSupport.filter (fun i => i < κp i),
          ρ.etaEpsT4 ε
            (v (leftMomentIndex i) -
              v (leftMomentIndex (κp i)))) *
        (∏ j ∈ κm.pairSupport.filter (fun j => j < κm j),
          ρ.etaEpsT4 ε
            (v (rightMomentIndex j) -
              v (rightMomentIndex (κm j)))) *
        momentCrossCovarianceProduct ρ ε m κp κm π v := by
  let combined :=
    momentCombinedPairing κp κm π
  let f : Fin (2 * m) → ℝ := fun a =>
    ρ.etaEpsT4 ε (v a - v (combined a))
  have hleft :
      (∏ i ∈ κp.pairSupport.filter (fun i => i < κp i),
          f (leftMomentIndex i)) =
        ∏ i ∈ κp.pairSupport.filter (fun i => i < κp i),
          ρ.etaEpsT4 ε
            (v (leftMomentIndex i) -
              v (leftMomentIndex (κp i))) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hiNot : i ∉ κp.singles := by
      intro hiSingle
      exact
        (PartialPairing.mem_pairSupport.mp
          (Finset.mem_filter.mp hi).1)
          (PartialPairing.mem_singles.mp hiSingle)
    dsimp only [f, combined]
    rw [momentCombinedPairing_left_pair κp κm π i hiNot]
  have hright :
      (∏ j ∈ κm.pairSupport.filter (fun j => j < κm j),
          f (rightMomentIndex j)) =
        ∏ j ∈ κm.pairSupport.filter (fun j => j < κm j),
          ρ.etaEpsT4 ε
            (v (rightMomentIndex j) -
              v (rightMomentIndex (κm j))) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjNot : j ∉ κm.singles := by
      intro hjSingle
      exact
        (PartialPairing.mem_pairSupport.mp
          (Finset.mem_filter.mp hj).1)
          (PartialPairing.mem_singles.mp hjSingle)
    dsimp only [f, combined]
    rw [momentCombinedPairing_right_pair κp κm π j hjNot]
  have hcross :
      (∏ i ∈ κp.singles, f (leftMomentIndex i)) =
        momentCrossCovarianceProduct ρ ε m κp κm π v := by
    rw [Finset.prod_subtype κp.singles
      (fun _ => Iff.rfl)
      (fun i => f (leftMomentIndex i))]
    unfold momentCrossCovarianceProduct
    apply Finset.prod_congr rfl
    intro i hi
    dsimp only [f, combined]
    rw [momentCombinedPairing_left_single
      κp κm π i.1 i.2]
  unfold primitiveCovarianceProduct
  change
    (∏ a ∈ momentCombinedLowerEndpoints κp κm π, f a) = _
  rw [prod_momentCombinedLowerEndpoints,
    prod_leftMomentPairLowerEndpoints,
    prod_rightMomentPairLowerEndpoints,
    prod_momentCrossLowerEndpoints,
    hleft, hright, hcross]

/-! ## Finite contraction entities and extraction signatures -/

/-- One complete contraction choice in (4.18): a partial pairing in
each copy and a bijection between their single sets. -/
abbrev MomentContraction (m : ℕ) :=
  Σ κp : PartialPairing (Fin m),
    Σ κm : PartialPairing (Fin m),
      κp.singles ≃ κm.singles

/-- Endpoint roles of the Def. 3.1 intervals extracted separately in
the left and right copies, embedded into the doubled carrier.  This is
the structure fixed in paper §4.2 Step 2 before (4.18); cross-copy
intervals of the residual pairing are reduced only later, after (4.20). -/
def momentWithinHalfEndpointSignature
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    Finset (Fin (2 * m)) × Finset (Fin (2 * m)) :=
  ((leftEndpoints κp).image leftMomentIndex ∪
      (leftEndpoints κm).image rightMomentIndex,
    (rightEndpoints κp).image leftMomentIndex ∪
      (rightEndpoints κm).image rightMomentIndex)

/-- The within-half extraction signature associated with a complete
contraction entity.  The cross-single bijection does not change these
initial intervals. -/
def momentContractionSignature
    {m : ℕ} (e : MomentContraction m) :
    Finset (Fin (2 * m)) × Finset (Fin (2 * m)) :=
  momentWithinHalfEndpointSignature e.1 e.2.1

/-- The finite set of doubled extraction signatures realized at order
`m`. -/
def momentContractionSignatures (m : ℕ) :
    Finset
      (Finset (Fin (2 * m)) ×
        Finset (Fin (2 * m))) :=
  (Finset.univ : Finset (MomentContraction m)).image
    momentContractionSignature

/-- The two within-half R-324 extraction structures have the same
coarse `4^(2m)` endpoint-role count as a role assignment on the doubled
carrier. -/
theorem card_momentContractionSignatures_le
    (m : ℕ) :
    (momentContractionSignatures m).card ≤
      4 ^ (2 * m) := by
  calc
    (momentContractionSignatures m).card ≤
        Fintype.card
          (Finset (Fin (2 * m)) ×
            Finset (Fin (2 * m))) :=
      Finset.card_le_univ _
    _ = 4 ^ (2 * m) := by
      simp only [Fintype.card_prod,
        Fintype.card_finset, Fintype.card_fin]
      rw [show (4 : ℕ) = 2 * 2 by norm_num,
        mul_pow]

/-- Nested sums over `(κ⁺, κ⁻, π)` are ordinary finite sums over the
single contraction-entity type. -/
theorem sum_momentContractions_eq_nested
    {M : Type*} [AddCommMonoid M]
    (m : ℕ) (F : MomentContraction m → M) :
    (∑ e : MomentContraction m, F e) =
      ∑ κp : PartialPairing (Fin m),
        ∑ κm : PartialPairing (Fin m),
          ∑ π : κp.singles ≃ κm.singles,
            F ⟨κp, ⟨κm, π⟩⟩ := by
  simp only [Fintype.sum_sigma]

/-- Exact regrouping of the complete contraction sum by the extraction
signature of its doubled full pairing. -/
theorem sum_momentContractions_by_signature
    {M : Type*} [AddCommMonoid M]
    (m : ℕ) (F : MomentContraction m → M) :
    (∑ s ∈ momentContractionSignatures m,
        ∑ e ∈ (Finset.univ :
            Finset (MomentContraction m)) with
          momentContractionSignature e = s,
          F e) =
      ∑ e : MomentContraction m, F e := by
  apply Finset.sum_fiberwise_of_maps_to
  intro e he
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

end

end Anderson4D
