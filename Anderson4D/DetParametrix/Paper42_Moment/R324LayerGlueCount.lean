import Anderson4D.DetParametrix.Paper42_Moment.R324GradeCoincidence

/-!
# The coincidence gluing count

This file proves `R324GradeCoincidenceCount`, the second combinatorial
input of the σ-grading: for every prescribed set `S` of coincidences,

`#{τ : S ⊆ r324GradeCoincidence τ} ≤ 2^m·(m - |S|)!`.

## The mechanism

A coincidence `i ∈ S` says that the labels `i` and `i+1` occupy
*adjacent slots* of the `τ`-order.  Prescribing `|S|` coincidences glues
the labels into `m - |S|` blocks of consecutive labels, each of which
must occupy a block of consecutive slots; the arrangement is determined
by the order of the blocks (`(m-|S|)!` choices) and the orientation of
each block (`≤ 2^m` choices).

The proof implements the gluing *one coincidence at a time*: the
contraction `r324LayerContract` merges the two glued labels into one and
the two occupied slots into one, producing a permutation of `Fin (m-1)`
that realises the shifted coincidence set, and the original permutation
is recovered from the contracted one together with a single orientation
bit.  This gives `N(m,S) ≤ 2·N(m-1,S')` with `|S'| = |S|-1`, hence
`N(m,S) ≤ 2^{|S|}·(m-|S|)!` by induction on `m` — no loss at all, the
`2^m` of the interface is slack.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## Positions -/

/-- The slot occupied by label `i` under the arrangement `π` (junk
outside the range).  `r324GradePos τ = r324LayerPos τ.symm`. -/
def r324LayerPos {m : ℕ} (π : Equiv.Perm (Fin m)) (i : ℕ) : ℕ :=
  if h : i < m then ((π ⟨i, h⟩ : Fin m) : ℕ) else 0

theorem r324LayerPos_eq_gradePos {m : ℕ} (τ : Equiv.Perm (Fin m)) (i : ℕ) :
    r324LayerPos τ.symm i = r324GradePos τ i := rfl

theorem r324LayerPos_lt {m : ℕ} (π : Equiv.Perm (Fin m)) {i : ℕ}
    (h : i < m) : r324LayerPos π i < m := by
  rw [r324LayerPos, dif_pos h]
  exact (π ⟨i, h⟩).isLt

theorem r324LayerPos_inj {m : ℕ} (π : Equiv.Perm (Fin m)) {i j : ℕ}
    (hi : i < m) (hj : j < m) (h : r324LayerPos π i = r324LayerPos π j) :
    i = j := by
  rw [r324LayerPos, dif_pos hi, r324LayerPos, dif_pos hj] at h
  have : (⟨i, hi⟩ : Fin m) = ⟨j, hj⟩ := π.injective (Fin.val_injective h)
  exact congrArg Fin.val this

/-- Two arrangements with the same slot function agree. -/
theorem r324LayerPos_ext {m : ℕ} {π σ : Equiv.Perm (Fin m)}
    (h : ∀ i < m, r324LayerPos π i = r324LayerPos σ i) : π = σ := by
  refine Equiv.ext fun a => Fin.ext ?_
  have := h a a.isLt
  rwa [r324LayerPos, dif_pos a.isLt, r324LayerPos, dif_pos a.isLt] at this

/-! ## The glued sets -/

/-- The arrangements realising all the prescribed coincidences in `S`:
for each `i ∈ S` the labels `i` and `i+1` occupy adjacent slots. -/
def r324LayerGlued (m : ℕ) (S : Finset ℕ) : Finset (Equiv.Perm (Fin m)) :=
  Finset.univ.filter fun π => ∀ i ∈ S, i + 1 < m ∧
    (r324LayerPos π (i + 1) + 1 = r324LayerPos π i ∨
      r324LayerPos π i + 1 = r324LayerPos π (i + 1))

theorem r324LayerGlued_mem {m : ℕ} {S : Finset ℕ} {π : Equiv.Perm (Fin m)} :
    π ∈ r324LayerGlued m S ↔ ∀ i ∈ S, i + 1 < m ∧
      (r324LayerPos π (i + 1) + 1 = r324LayerPos π i ∨
        r324LayerPos π i + 1 = r324LayerPos π (i + 1)) := by
  simp [r324LayerGlued]

theorem r324LayerGlued_empty (m : ℕ) :
    (r324LayerGlued m ∅).card = m.factorial := by
  have : r324LayerGlued m ∅ = (Finset.univ : Finset (Equiv.Perm (Fin m))) := by
    ext π; simp [r324LayerGlued]
  rw [this, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-! ## Label and slot merging -/

/-- Label map: `Fin (m-1) → ℕ` skipping the merged label `i₀+1`. -/
def r324LayerHat (i₀ j : ℕ) : ℕ := if j ≤ i₀ then j else j + 1

/-- Slot map: merge the slots `p` and `p+1`. -/
def r324LayerKap (p v : ℕ) : ℕ := if v ≤ p then v else v - 1

/-- The lower of the two slots occupied by the glued labels. -/
def r324LayerBase {m : ℕ} (π : Equiv.Perm (Fin m)) (i₀ : ℕ) : ℕ :=
  min (r324LayerPos π i₀) (r324LayerPos π (i₀ + 1))

theorem r324LayerHat_ne {i₀ j : ℕ} : r324LayerHat i₀ j ≠ i₀ + 1 := by
  unfold r324LayerHat; split_ifs <;> omega

theorem r324LayerHat_inj {i₀ j₁ j₂ : ℕ}
    (h : r324LayerHat i₀ j₁ = r324LayerHat i₀ j₂) : j₁ = j₂ := by
  unfold r324LayerHat at h; split_ifs at h <;> omega

theorem r324LayerHat_lt {m i₀ j : ℕ} (hi₀ : i₀ + 1 < m) (hj : j < m - 1) :
    r324LayerHat i₀ j < m := by
  unfold r324LayerHat; split_ifs <;> omega

theorem r324LayerHat_le {i₀ j : ℕ} (h : j ≤ i₀) : r324LayerHat i₀ j = j := by
  unfold r324LayerHat; simp [h]

theorem r324LayerHat_gt {i₀ j : ℕ} (h : i₀ < j) :
    r324LayerHat i₀ j = j + 1 := by
  unfold r324LayerHat; simp [Nat.not_le.mpr h]

/-- The two glued labels occupy the slots `base` and `base+1`. -/
theorem r324LayerBase_spec {m : ℕ} {π : Equiv.Perm (Fin m)} {i₀ : ℕ}
    (hadj : r324LayerPos π (i₀ + 1) + 1 = r324LayerPos π i₀ ∨
      r324LayerPos π i₀ + 1 = r324LayerPos π (i₀ + 1)) :
    (r324LayerPos π i₀ = r324LayerBase π i₀ ∧
        r324LayerPos π (i₀ + 1) = r324LayerBase π i₀ + 1) ∨
      (r324LayerPos π i₀ = r324LayerBase π i₀ + 1 ∧
        r324LayerPos π (i₀ + 1) = r324LayerBase π i₀) := by
  unfold r324LayerBase; omega

theorem r324LayerBase_lt {m : ℕ} {π : Equiv.Perm (Fin m)} {i₀ : ℕ}
    (hi₀ : i₀ + 1 < m)
    (hadj : r324LayerPos π (i₀ + 1) + 1 = r324LayerPos π i₀ ∨
      r324LayerPos π i₀ + 1 = r324LayerPos π (i₀ + 1)) :
    r324LayerBase π i₀ + 1 < m := by
  have h1 := r324LayerPos_lt π (i := i₀) (by omega)
  have h2 := r324LayerPos_lt π (i := i₀ + 1) hi₀
  unfold r324LayerBase; omega

/-- Only the two glued labels sit in the merged slots. -/
theorem r324LayerPos_ne_base {m : ℕ} {π : Equiv.Perm (Fin m)} {i₀ j : ℕ}
    (hi₀ : i₀ + 1 < m) (hj : j < m) (hj1 : j ≠ i₀) (hj2 : j ≠ i₀ + 1)
    (hadj : r324LayerPos π (i₀ + 1) + 1 = r324LayerPos π i₀ ∨
      r324LayerPos π i₀ + 1 = r324LayerPos π (i₀ + 1)) :
    r324LayerPos π j ≠ r324LayerBase π i₀ ∧
      r324LayerPos π j ≠ r324LayerBase π i₀ + 1 := by
  have hspec := r324LayerBase_spec (π := π) (i₀ := i₀) hadj
  constructor <;> intro hcon
  · rcases hspec with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hj1 (r324LayerPos_inj π hj (by omega) (by omega))
    · exact hj2 (r324LayerPos_inj π hj hi₀ (by omega))
  · rcases hspec with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hj2 (r324LayerPos_inj π hj hi₀ (by omega))
    · exact hj1 (r324LayerPos_inj π hj (by omega) (by omega))

theorem r324LayerKap_le {m p v : ℕ} (hp : p + 1 < m) (hv : v < m) :
    r324LayerKap p v ≤ m - 2 := by
  unfold r324LayerKap; split_ifs <;> omega

theorem r324LayerKap_eq_of_mem {p v : ℕ} (h : v = p ∨ v = p + 1) :
    r324LayerKap p v = p := by
  unfold r324LayerKap; split_ifs <;> omega

/-- Slot merging preserves adjacency of two slots not both merged. -/
theorem r324LayerKap_adj {p a b : ℕ}
    (hmem : ¬ ((a = p ∨ a = p + 1) ∧ (b = p ∨ b = p + 1)))
    (hab : a + 1 = b ∨ b + 1 = a) :
    r324LayerKap p a + 1 = r324LayerKap p b ∨
      r324LayerKap p b + 1 = r324LayerKap p a := by
  unfold r324LayerKap; split_ifs <;> omega

/-- Slot merging is injective away from the merged slots. -/
theorem r324LayerKap_inj {p a b : ℕ}
    (_ha : a ≠ p ∧ a ≠ p + 1) (_hb : b ≠ p ∧ b ≠ p + 1)
    (h : r324LayerKap p a = r324LayerKap p b) : a = b := by
  unfold r324LayerKap at h; split_ifs at h <;> omega

/-! ## The contracted arrangement -/

/-- The contracted arrangement as a function: drop the label `i₀+1` and
merge its slot with the slot of `i₀`. -/
def r324LayerContractFun {m : ℕ} (π : Equiv.Perm (Fin m)) (i₀ : ℕ)
    (j : Fin (m - 1)) : Fin (m - 1) :=
  ⟨min (r324LayerKap (r324LayerBase π i₀)
      (r324LayerPos π (r324LayerHat i₀ (j : ℕ)))) (m - 2),
    by have := j.isLt; omega⟩

theorem r324LayerContractFun_val {m : ℕ} {π : Equiv.Perm (Fin m)} {i₀ : ℕ}
    (hi₀ : i₀ + 1 < m)
    (hadj : r324LayerPos π (i₀ + 1) + 1 = r324LayerPos π i₀ ∨
      r324LayerPos π i₀ + 1 = r324LayerPos π (i₀ + 1))
    (j : Fin (m - 1)) :
    ((r324LayerContractFun π i₀ j : Fin (m - 1)) : ℕ) =
      r324LayerKap (r324LayerBase π i₀)
        (r324LayerPos π (r324LayerHat i₀ (j : ℕ))) := by
  have hb := r324LayerBase_lt hi₀ hadj
  have hlt : r324LayerPos π (r324LayerHat i₀ (j : ℕ)) < m :=
    r324LayerPos_lt π (r324LayerHat_lt hi₀ j.isLt)
  have hle := r324LayerKap_le (p := r324LayerBase π i₀) hb hlt
  simp [r324LayerContractFun, Nat.min_eq_left hle]

/-- Every label other than the two glued ones avoids the merged slots. -/
theorem r324LayerContract_dichotomy {m : ℕ} {π : Equiv.Perm (Fin m)} {i₀ : ℕ}
    (hi₀ : i₀ + 1 < m)
    (hadj : r324LayerPos π (i₀ + 1) + 1 = r324LayerPos π i₀ ∨
      r324LayerPos π i₀ + 1 = r324LayerPos π (i₀ + 1))
    {j : ℕ} (hj : j < m - 1) :
    r324LayerHat i₀ j = i₀ ∨
      (r324LayerPos π (r324LayerHat i₀ j) ≠ r324LayerBase π i₀ ∧
        r324LayerPos π (r324LayerHat i₀ j) ≠ r324LayerBase π i₀ + 1) := by
  by_cases h : r324LayerHat i₀ j = i₀
  · exact Or.inl h
  · exact Or.inr (r324LayerPos_ne_base hi₀ (r324LayerHat_lt hi₀ hj) h
      r324LayerHat_ne hadj)

theorem r324LayerContractFun_injective {m : ℕ} {π : Equiv.Perm (Fin m)}
    {i₀ : ℕ} (hi₀ : i₀ + 1 < m)
    (hadj : r324LayerPos π (i₀ + 1) + 1 = r324LayerPos π i₀ ∨
      r324LayerPos π i₀ + 1 = r324LayerPos π (i₀ + 1)) :
    Function.Injective (r324LayerContractFun π i₀) := by
  have hbm : r324LayerPos π i₀ = r324LayerBase π i₀ ∨
      r324LayerPos π i₀ = r324LayerBase π i₀ + 1 := by
    rcases r324LayerBase_spec (π := π) (i₀ := i₀) hadj with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  intro j₁ j₂ hj
  have hval := congrArg Fin.val hj
  rw [r324LayerContractFun_val hi₀ hadj, r324LayerContractFun_val hi₀ hadj]
    at hval
  refine Fin.ext (r324LayerHat_inj (i₀ := i₀) ?_)
  rcases r324LayerContract_dichotomy hi₀ hadj j₁.isLt with h1 | h1 <;>
    rcases r324LayerContract_dichotomy hi₀ hadj j₂.isLt with h2 | h2
  · rw [h1, h2]
  · exfalso
    rw [h1, r324LayerKap_eq_of_mem hbm] at hval
    unfold r324LayerKap at hval
    split_ifs at hval <;> omega
  · exfalso
    rw [h2, r324LayerKap_eq_of_mem hbm] at hval
    unfold r324LayerKap at hval
    split_ifs at hval <;> omega
  · exact r324LayerPos_inj π (r324LayerHat_lt hi₀ j₁.isLt)
      (r324LayerHat_lt hi₀ j₂.isLt) (r324LayerKap_inj h1 h2 hval)

open Classical in
/-- The contracted arrangement. -/
def r324LayerContract {m : ℕ} (π : Equiv.Perm (Fin m)) (i₀ : ℕ) :
    Equiv.Perm (Fin (m - 1)) :=
  if h : Function.Injective (r324LayerContractFun π i₀) then
    Equiv.ofBijective _ (Finite.injective_iff_bijective.mp h)
  else 1

/-- The slot function of the contracted arrangement. -/
theorem r324LayerContract_pos {m : ℕ} {π : Equiv.Perm (Fin m)} {i₀ : ℕ}
    (hi₀ : i₀ + 1 < m)
    (hadj : r324LayerPos π (i₀ + 1) + 1 = r324LayerPos π i₀ ∨
      r324LayerPos π i₀ + 1 = r324LayerPos π (i₀ + 1))
    {j : ℕ} (hj : j < m - 1) :
    r324LayerPos (r324LayerContract π i₀) j =
      r324LayerKap (r324LayerBase π i₀)
        (r324LayerPos π (r324LayerHat i₀ j)) := by
  have hinj := r324LayerContractFun_injective hi₀ hadj
  rw [r324LayerPos, dif_pos hj, r324LayerContract, dif_pos hinj]
  simpa using r324LayerContractFun_val hi₀ hadj ⟨j, hj⟩

/-! ## Coincidences survive the contraction -/

/-- Relabelling after the merge. -/
def r324LayerShift (i₀ i : ℕ) : ℕ := if i < i₀ then i else i - 1

theorem r324LayerShift_injOn {i₀ : ℕ} {i j : ℕ} (hi : i ≠ i₀) (hj : j ≠ i₀)
    (h : r324LayerShift i₀ i = r324LayerShift i₀ j) : i = j := by
  unfold r324LayerShift at h; split_ifs at h <;> omega

/-- **The contraction realises the shifted coincidences.** -/
theorem r324LayerContract_mem {m : ℕ} {π : Equiv.Perm (Fin m)} {S : Finset ℕ}
    (hπ : π ∈ r324LayerGlued m S) {i₀ : ℕ} (hi₀S : i₀ ∈ S) :
    r324LayerContract π i₀ ∈
      r324LayerGlued (m - 1) ((S.erase i₀).image (r324LayerShift i₀)) := by
  have hmem := r324LayerGlued_mem.mp hπ
  obtain ⟨hi₀m, hadj₀⟩ := hmem i₀ hi₀S
  have hspec := r324LayerBase_spec (π := π) (i₀ := i₀) hadj₀
  have hbase : r324LayerPos π i₀ = r324LayerBase π i₀ ∨
      r324LayerPos π i₀ = r324LayerBase π i₀ + 1 := by
    rcases hspec with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  rw [r324LayerGlued_mem]
  intro i' hi'
  obtain ⟨i, hiE, rfl⟩ := Finset.mem_image.mp hi'
  have hine : i ≠ i₀ := Finset.ne_of_mem_erase hiE
  obtain ⟨him, hadji⟩ := hmem i (Finset.mem_of_mem_erase hiE)
  rcases Nat.lt_or_ge i i₀ with hlt | hge
  · -- the coincidence lies strictly below the merged pair
    have hsh : r324LayerShift i₀ i = i := by unfold r324LayerShift; simp [hlt]
    have h1 : i < m - 1 := by omega
    have h2 : i + 1 < m - 1 := by omega
    rw [hsh]
    refine ⟨h2, ?_⟩
    rw [r324LayerContract_pos hi₀m hadj₀ h1,
      r324LayerContract_pos hi₀m hadj₀ h2,
      r324LayerHat_le (le_of_lt hlt), r324LayerHat_le (by omega)]
    refine r324LayerKap_adj ?_ hadji
    have := r324LayerPos_ne_base (π := π) hi₀m (j := i) (by omega)
      (by omega) (by omega) hadj₀
    tauto
  · have hgt : i₀ < i := lt_of_le_of_ne hge (Ne.symm hine)
    rcases Nat.lt_or_ge (i₀ + 1) i with hfar | hnear
    · -- the coincidence lies strictly above the merged pair
      have hsh : r324LayerShift i₀ i = i - 1 := by
        unfold r324LayerShift; simp [Nat.not_lt.mpr hge]
      have h1 : i - 1 < m - 1 := by omega
      have h2 : i - 1 + 1 < m - 1 := by omega
      rw [hsh]
      refine ⟨h2, ?_⟩
      rw [r324LayerContract_pos hi₀m hadj₀ h1,
        r324LayerContract_pos hi₀m hadj₀ h2,
        r324LayerHat_gt (by omega), r324LayerHat_gt (by omega)]
      have he1 : i - 1 + 1 = i := by omega
      rw [he1]
      refine r324LayerKap_adj ?_ hadji
      have ha := r324LayerPos_ne_base (π := π) hi₀m (j := i) (by omega)
        (by omega) (by omega) hadj₀
      tauto
    · -- the coincidence straddles the merged pair from above
      have hi1 : i = i₀ + 1 := by omega
      subst hi1
      have hsh : r324LayerShift i₀ (i₀ + 1) = i₀ := by
        unfold r324LayerShift; simp
      have h1 : i₀ < m - 1 := by omega
      have h2 : i₀ + 1 < m - 1 := by omega
      rw [hsh]
      refine ⟨h2, ?_⟩
      rw [r324LayerContract_pos hi₀m hadj₀ h1,
        r324LayerContract_pos hi₀m hadj₀ h2,
        r324LayerHat_le (le_refl _), r324LayerHat_gt (by omega),
        r324LayerKap_eq_of_mem hbase]
      have hne := r324LayerPos_ne_base (π := π) hi₀m (j := i₀ + 1 + 1)
        (by omega) (by omega) (by omega) hadj₀
      unfold r324LayerKap
      split_ifs <;> omega

/-! ## The contraction is two-to-one -/

theorem r324LayerHat_shift {i₀ j : ℕ} (h1 : j ≠ i₀) (h2 : j ≠ i₀ + 1) :
    r324LayerHat i₀ (r324LayerShift i₀ j) = j := by
  unfold r324LayerHat r324LayerShift; split_ifs <;> omega

theorem r324LayerShift_lt {m i₀ j : ℕ} (hi₀ : i₀ + 1 < m) (hj : j < m) :
    r324LayerShift i₀ j < m - 1 := by
  unfold r324LayerShift; split_ifs <;> omega

/-- **The arrangement is recovered from its contraction and one
orientation bit.** -/
theorem r324LayerGlue_ext {m : ℕ} {S : Finset ℕ} {i₀ : ℕ} (hi₀S : i₀ ∈ S)
    {π σ : Equiv.Perm (Fin m)}
    (hπ : π ∈ r324LayerGlued m S) (hσ : σ ∈ r324LayerGlued m S)
    (hbit : (r324LayerPos π (i₀ + 1) < r324LayerPos π i₀) ↔
      (r324LayerPos σ (i₀ + 1) < r324LayerPos σ i₀))
    (hcon : r324LayerContract π i₀ = r324LayerContract σ i₀) : π = σ := by
  obtain ⟨hi₀m, hadjπ⟩ := (r324LayerGlued_mem.mp hπ) i₀ hi₀S
  obtain ⟨-, hadjσ⟩ := (r324LayerGlued_mem.mp hσ) i₀ hi₀S
  have hspecπ := r324LayerBase_spec (π := π) (i₀ := i₀) hadjπ
  have hspecσ := r324LayerBase_spec (π := σ) (i₀ := i₀) hadjσ
  have hbaseπ : r324LayerPos π i₀ = r324LayerBase π i₀ ∨
      r324LayerPos π i₀ = r324LayerBase π i₀ + 1 := by tauto
  have hbaseσ : r324LayerPos σ i₀ = r324LayerBase σ i₀ ∨
      r324LayerPos σ i₀ = r324LayerBase σ i₀ + 1 := by tauto
  have hb : r324LayerBase π i₀ = r324LayerBase σ i₀ := by
    have e1 : r324LayerPos (r324LayerContract π i₀) i₀ = r324LayerBase π i₀ := by
      rw [r324LayerContract_pos hi₀m hadjπ (by omega),
        r324LayerHat_le (le_refl _), r324LayerKap_eq_of_mem hbaseπ]
    have e2 : r324LayerPos (r324LayerContract σ i₀) i₀ = r324LayerBase σ i₀ := by
      rw [r324LayerContract_pos hi₀m hadjσ (by omega),
        r324LayerHat_le (le_refl _), r324LayerKap_eq_of_mem hbaseσ]
    rw [← e1, ← e2, hcon]
  refine r324LayerPos_ext fun j hj => ?_
  by_cases hj0 : j = i₀
  · subst hj0; omega
  by_cases hj1 : j = i₀ + 1
  · subst hj1; omega
  · have hshlt : r324LayerShift i₀ j < m - 1 := r324LayerShift_lt hi₀m hj
    have e1 := r324LayerContract_pos hi₀m hadjπ hshlt
    have e2 := r324LayerContract_pos hi₀m hadjσ hshlt
    rw [r324LayerHat_shift hj0 hj1] at e1 e2
    rw [hcon] at e1
    rw [e2, hb] at e1
    exact r324LayerKap_inj (p := r324LayerBase σ i₀)
      (by rw [← hb]; exact r324LayerPos_ne_base hi₀m hj hj0 hj1 hadjπ)
      (r324LayerPos_ne_base hi₀m hj hj0 hj1 hadjσ) e1.symm

/-! ## The gluing count -/

/-- **The gluing count.**  At most `2^{|S|}·(m-|S|)!` arrangements
realise all the prescribed coincidences in `S`. -/
theorem r324LayerGlued_card_le : ∀ (m : ℕ) (S : Finset ℕ),
    (r324LayerGlued m S).card ≤ 2 ^ S.card * (m - S.card).factorial := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S
    rcases S.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀S⟩
    · simp [r324LayerGlued_empty]
    by_cases hi₀m : i₀ + 1 < m
    · set S' : Finset ℕ := (S.erase i₀).image (r324LayerShift i₀) with hS'def
      have hk : 1 ≤ S.card := Finset.card_pos.mpr ⟨i₀, hi₀S⟩
      have hS' : S'.card = S.card - 1 := by
        rw [hS'def, Finset.card_image_of_injOn
          (fun a ha b hb h => r324LayerShift_injOn
            (Finset.ne_of_mem_erase ha) (Finset.ne_of_mem_erase hb) h),
          Finset.card_erase_of_mem hi₀S]
      have hstep : (r324LayerGlued m S).card ≤
          2 * (r324LayerGlued (m - 1) S').card := by
        have hcard : (r324LayerGlued m S).card ≤
            ((Finset.univ : Finset Bool) ×ˢ r324LayerGlued (m - 1) S').card := by
          refine Finset.card_le_card_of_injOn
            (fun π => (decide (r324LayerPos π (i₀ + 1) < r324LayerPos π i₀),
              r324LayerContract π i₀)) (fun π hπ => ?_) (fun π hπ σ hσ h => ?_)
          · exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
              r324LayerContract_mem hπ hi₀S⟩
          · exact r324LayerGlue_ext hi₀S (Finset.mem_coe.mp hπ)
              (Finset.mem_coe.mp hσ)
              (decide_eq_decide.mp (congrArg Prod.fst h))
              (congrArg Prod.snd h)
        simpa [Finset.card_product] using hcard
      have hih := ih (m - 1) (by omega) S'
      have e1 : (m - 1) - S'.card = m - S.card := by rw [hS']; omega
      have e2 : 2 * 2 ^ S'.card = 2 ^ S.card := by
        rw [hS']
        calc 2 * 2 ^ (S.card - 1) = 2 ^ (S.card - 1 + 1) := by ring
          _ = 2 ^ S.card := by congr 1; omega
      calc (r324LayerGlued m S).card
          ≤ 2 * (r324LayerGlued (m - 1) S').card := hstep
        _ ≤ 2 * (2 ^ S'.card * ((m - 1) - S'.card).factorial) := by
            exact Nat.mul_le_mul_left 2 hih
        _ = 2 ^ S.card * (m - S.card).factorial := by
            rw [e1, ← mul_assoc, e2]
    · have hempty : r324LayerGlued m S = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun π hπ => ?_
        exact hi₀m ((r324LayerGlued_mem.mp hπ) i₀ hi₀S).1
      simp [hempty]

/-! ## The proved coincidence interface -/

theorem r324Layer_mem_glued_of_subset {m : ℕ} {τ : Equiv.Perm (Fin m)}
    {S : Finset (Fin m)} (h : S ⊆ r324GradeCoincidence τ) :
    τ.symm ∈ r324LayerGlued m (S.image Fin.val) := by
  rw [r324LayerGlued_mem]
  intro n hn
  obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp hn
  have hi := h hiS
  rw [r324GradeCoincidence, Finset.mem_filter] at hi
  simpa [r324LayerPos_eq_gradePos] using hi.2

/-- **The coincidence gluing count.**  This is the remaining
combinatorial obligation of `R324GradeCoincidence`: a prescribed set `S`
of coincidences is realised by at most `2^m·(m-|S|)!` bijections. -/
theorem r324Layer_gradeCoincidenceCount (m : ℕ) : R324GradeCoincidenceCount m := by
  intro S
  have hcard :
      ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
          fun τ => S ⊆ r324GradeCoincidence τ).card ≤
        (r324LayerGlued m (S.image Fin.val)).card := by
    refine Finset.card_le_card_of_injOn (fun τ => τ.symm)
      (fun τ hτ => ?_) (fun a _ b _ h => ?_)
    · exact r324Layer_mem_glued_of_subset
        (Finset.mem_filter.mp (Finset.mem_coe.mp hτ)).2
    · simpa using congrArg Equiv.symm h
  have hSc : (S.image Fin.val).card = S.card :=
    Finset.card_image_of_injective S Fin.val_injective
  have hle := r324LayerGlued_card_le m (S.image Fin.val)
  rw [hSc] at hle
  have hSm : S.card ≤ m := by simpa using Finset.card_le_univ S
  have hnat :
      ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
          fun τ => S ⊆ r324GradeCoincidence τ).card ≤
        2 ^ m * (m - S.card).factorial :=
    le_trans (le_trans hcard hle)
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hSm))
  exact_mod_cast hnat

/-- **The σ-grading layer count, with only the grade domination left.**
Combining the gluing count with `r324Grade_permLayerCount_of_coincidence`:
any grade dominated by the coincidence count obeys the permutation layer
count at constant `8`, hence — through `r324Grade_layeredAt_of_collapse`
— clause A. -/
theorem r324Layer_permLayerCount_of_dominated {m : ℕ}
    {gradeP : Equiv.Perm (Fin m) → ℕ} (hm : 1 ≤ m)
    (hgle : ∀ τ : Equiv.Perm (Fin m), gradeP τ ≤ m - 1)
    (hdom : ∀ τ : Equiv.Perm (Fin m),
      gradeP τ ≤ (r324GradeCoincidence τ).card + 1) :
    R324GradePermLayerCount 8 m gradeP :=
  r324Grade_permLayerCount_of_coincidence hm hgle hdom
    (r324Layer_gradeCoincidenceCount m)

/-! ## The grade statistic the lattice rewards

The collapsed lattice sum of `R324CollapseEntity` is
`∑_q ∏ᵢ‖ρ̂(εqᵢ)‖²·∏ⱼ⟨Sⱼ⟩⁻²⟨Sⱼ^τ⟩⁻²` over the zero-sum sector, where
`Sⱼ = q₁+…+qⱼ` and `Sⱼ^τ = q_{τ(1)}+…+q_{τ(j)}`.  **Both propagator
families are prefix sums.**  A free `ε⁻¹`-window summation is produced
exactly when a proper prefix of the identity order and a prefix of the
`τ` order agree *as sets*: then `Sⱼ^τ = Sⱼ`, the two brackets collide
into `⟨Sⱼ⟩⁻⁴`, and the single `Z4` variable `Sⱼ` may be summed freely
against a log-critical kernel (`r324SW_translated_window_le_log`,
`r324SW_shifted_window_le_log`, both `≤ C·|log ε|`).  A key that is
*not* freed this way is pinned by the zero-sum constraint and is not a
summation variable at all: that is the only reason it costs `O(1)`.
Summing a pinned key freely is never affordable — the bare symbol mass
costs `ε⁻⁴` (`r324SW_symbol_mass_le`) and a marked key costs `ε⁻⁸`
(`r324RoutedWindow_marked_window_le`), which is exactly the endpoint
sacrifice the routed budget `C^m·L^{m-1}·ε⁻⁸` pays once.

So the statistic is the number of **prefix coincidences**
`#{j : 1 ≤ j < m, τ({0,…,j-1}) = {0,…,j-1}}` — the classical count of
decomposition points of `τ` — plus one for the trivial (whole-set)
member of the chain, capped at `m-1`.  The two proved data points
are matched exactly: the identity has all `m-1` decomposition points,
hence grade `m-1` (`r324LayerSplitGrade_one`), and the simple
permutation `(2,4,1,3)` of `R324CappedCrossGrading` has none, hence
grade `1` (`r324LayerSplitGrade_simple_four`).

Note that this is *not* dominated by the adjacency coincidences of
`r324GradeCoincidence`: the direct sum of two copies of `(2,4,1,3)` at
`m = 8` has one decomposition point and no adjacency coincidence at all
(`r324Layer_split_not_dominated_by_coincidence`), so the split grade
needs — and here gets — its own layer count. -/

/-- The **decomposition points** of `τ`: the proper prefixes of the
identity order that `τ` preserves setwise. -/
def r324LayerSplit {m : ℕ} (τ : Equiv.Perm (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun j : Fin m =>
    1 ≤ (j : ℕ) ∧ ∀ i < (j : ℕ), r324LayerPos τ i < (j : ℕ)

/-- **The σ-grade of a bijection**: one free window per decomposition
point, plus the trivial member of the chain, capped by the identity's
full power `m-1`. -/
def r324LayerSplitGrade {m : ℕ} (τ : Equiv.Perm (Fin m)) : ℕ :=
  min ((r324LayerSplit τ).card + 1) (m - 1)

theorem r324LayerSplitGrade_le {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    r324LayerSplitGrade τ ≤ m - 1 := min_le_right _ _

theorem r324LayerSplitGrade_le_card {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    r324LayerSplitGrade τ ≤ (r324LayerSplit τ).card + 1 := min_le_left _ _

/-- The identity has every decomposition point. -/
theorem r324LayerSplit_one (m : ℕ) :
    r324LayerSplit (1 : Equiv.Perm (Fin m)) =
      Finset.univ.filter fun j : Fin m => 1 ≤ (j : ℕ) := by
  ext j
  simp only [r324LayerSplit, Finset.mem_filter, Finset.mem_univ, true_and,
    and_iff_left_iff_imp]
  intro _ i hi
  have him : i < m := lt_of_lt_of_le hi (Nat.le_of_lt_succ (Nat.lt_succ_of_lt j.isLt))
  rw [r324LayerPos, dif_pos him]
  simpa using hi

/-- **The identity carries the full window power `m-1`.** -/
theorem r324LayerSplitGrade_one {m : ℕ} (hm : 2 ≤ m) :
    r324LayerSplitGrade (1 : Equiv.Perm (Fin m)) = m - 1 := by
  haveI : NeZero m := ⟨by omega⟩
  have hcard : (r324LayerSplit (1 : Equiv.Perm (Fin m))).card = m - 1 := by
    rw [r324LayerSplit_one]
    have hset : (Finset.univ.filter fun j : Fin m => 1 ≤ (j : ℕ)) =
        (Finset.univ : Finset (Fin m)).erase 0 := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        and_true]
      rw [Ne, Fin.ext_iff, Fin.val_zero]
      omega
    rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  rw [r324LayerSplitGrade, hcard]
  omega

/-- A bijection with no decomposition point has grade `1`. -/
theorem r324LayerSplitGrade_of_split_empty {m : ℕ} {τ : Equiv.Perm (Fin m)}
    (hm : 2 ≤ m) (h : r324LayerSplit τ = ∅) : r324LayerSplitGrade τ = 1 := by
  rw [r324LayerSplitGrade, h]
  simp only [Finset.card_empty, Nat.zero_add]
  omega

/-- The simple permutation `(2,4,1,3)` of `R324CappedCrossGrading` has
no decomposition point. -/
theorem r324LayerSplit_simple_four :
    r324LayerSplit (c[(0 : Fin 4), 1, 3, 2] : Equiv.Perm (Fin 4)) = ∅ := by
  decide

/-- **The deranged `m = 4` bijection has grade `1`**, matching the
proved table of `R324CappedCrossGrading`. -/
theorem r324LayerSplitGrade_simple_four :
    r324LayerSplitGrade (c[(0 : Fin 4), 1, 3, 2] : Equiv.Perm (Fin 4)) = 1 :=
  r324LayerSplitGrade_of_split_empty (by norm_num) r324LayerSplit_simple_four

/-- **The split grade is not dominated by the adjacency coincidences.**
The direct sum of two copies of the simple permutation `(2,4,1,3)` has a
decomposition point at `4` and no adjacency coincidence at all, so the
hypothesis `gradeP τ ≤ #coincidences + 1` of
`r324Grade_permLayerCount_of_coincidence` *fails* for the split grade.
That is why `r324Layer_permLayerCount_split` below proves the layer
count for the split grade directly, from its own subset count. -/
theorem r324Layer_split_not_dominated_by_coincidence :
    (r324GradeCoincidence
        (c[(0 : Fin 8), 1, 3, 2] * c[(4 : Fin 8), 5, 7, 6])).card + 1 <
      r324LayerSplitGrade
        (c[(0 : Fin 8), 1, 3, 2] * c[(4 : Fin 8), 5, 7, 6]) := by
  decide

/-! ## The layer count of the split grade -/

theorem r324LayerFactorial_mul_le {a : ℕ} (ha : 1 ≤ a) (n : ℕ) :
    a.factorial * (n + 1).factorial ≤ (a + n).factorial := by
  induction n with
  | zero => simp
  | succ p ih =>
    rw [Nat.factorial_succ (p + 1), show a + (p + 1) = a + p + 1 by omega,
      Nat.factorial_succ]
    calc a.factorial * ((p + 1 + 1) * (p + 1).factorial)
        = (p + 2) * (a.factorial * (p + 1).factorial) := by ring
      _ ≤ (p + 2) * (a + p).factorial := Nat.mul_le_mul_left _ ih
      _ ≤ (a + p + 1) * (a + p).factorial := Nat.mul_le_mul_right _ (by omega)

/-- Bijections with prescribed decomposition points (indexed by `ℕ`). -/
def r324LayerSplitAt (m : ℕ) (T : Finset ℕ) : Finset (Equiv.Perm (Fin m)) :=
  Finset.univ.filter fun τ =>
    ∀ j ∈ T, 1 ≤ j ∧ j < m ∧ ∀ i < j, r324LayerPos τ i < j

theorem r324LayerSplitAt_mem {m : ℕ} {T : Finset ℕ} {τ : Equiv.Perm (Fin m)} :
    τ ∈ r324LayerSplitAt m T ↔
      ∀ j ∈ T, 1 ≤ j ∧ j < m ∧ ∀ i < j, r324LayerPos τ i < j := by
  simp [r324LayerSplitAt]

/-- The head block of a decomposed bijection. -/
def r324LayerHead {m : ℕ} (τ : Equiv.Perm (Fin m)) (j : ℕ) (a : Fin j) :
    Fin j :=
  ⟨min (r324LayerPos τ (a : ℕ)) (j - 1), by have := a.isLt; omega⟩

/-- The tail block of a decomposed bijection. -/
def r324LayerTail {m : ℕ} (τ : Equiv.Perm (Fin m)) (j : ℕ) (a : Fin (m - j)) :
    Fin (m - j) :=
  ⟨min (r324LayerPos τ (j + (a : ℕ)) - j) (m - j - 1), by have := a.isLt; omega⟩

theorem r324LayerHead_val {m : ℕ} {τ : Equiv.Perm (Fin m)} {j : ℕ}
    (hsplit : ∀ i < j, r324LayerPos τ i < j) (a : Fin j) :
    ((r324LayerHead τ j a : Fin j) : ℕ) = r324LayerPos τ (a : ℕ) := by
  have := hsplit (a : ℕ) a.isLt
  simp [r324LayerHead, Nat.min_eq_left (by omega : r324LayerPos τ (a : ℕ) ≤ j - 1)]

theorem r324LayerHead_injective {m : ℕ} {τ : Equiv.Perm (Fin m)} {j : ℕ}
    (hjm : j < m) (hsplit : ∀ i < j, r324LayerPos τ i < j) :
    Function.Injective (r324LayerHead τ j) := by
  intro a b h
  have hval := congrArg Fin.val h
  rw [r324LayerHead_val hsplit, r324LayerHead_val hsplit] at hval
  exact Fin.ext (r324LayerPos_inj τ (by omega) (by omega) hval)

/-- Labels above a decomposition point occupy slots above it. -/
theorem r324LayerPos_ge_of_split {m : ℕ} {τ : Equiv.Perm (Fin m)} {j : ℕ}
    (hjm : j < m) (hsplit : ∀ i < j, r324LayerPos τ i < j) {a : ℕ}
    (haj : j ≤ a) (ham : a < m) : j ≤ r324LayerPos τ a := by
  by_contra hcon
  have hcon' : r324LayerPos τ a < j := by omega
  have hbij := Finite.injective_iff_bijective.mp (r324LayerHead_injective hjm hsplit)
  obtain ⟨b, hb⟩ := hbij.2 ⟨r324LayerPos τ a, hcon'⟩
  have hbval := congrArg Fin.val hb
  rw [r324LayerHead_val hsplit] at hbval
  have : (b : ℕ) = a := r324LayerPos_inj τ (by omega) ham hbval
  omega

theorem r324LayerTail_val {m : ℕ} {τ : Equiv.Perm (Fin m)} {j : ℕ}
    (hjm : j < m) (_hsplit : ∀ i < j, r324LayerPos τ i < j) (a : Fin (m - j)) :
    ((r324LayerTail τ j a : Fin (m - j)) : ℕ) =
      r324LayerPos τ (j + (a : ℕ)) - j := by
  have hlt : r324LayerPos τ (j + (a : ℕ)) < m := by
    have := a.isLt; exact r324LayerPos_lt τ (by omega)
  simp [r324LayerTail, Nat.min_eq_left (by omega :
    r324LayerPos τ (j + (a : ℕ)) - j ≤ m - j - 1)]

theorem r324LayerTail_injective {m : ℕ} {τ : Equiv.Perm (Fin m)} {j : ℕ}
    (hjm : j < m) (hsplit : ∀ i < j, r324LayerPos τ i < j) :
    Function.Injective (r324LayerTail τ j) := by
  intro a b h
  have hval := congrArg Fin.val h
  rw [r324LayerTail_val hjm hsplit, r324LayerTail_val hjm hsplit] at hval
  have ha := r324LayerPos_ge_of_split hjm hsplit (a := j + (a : ℕ)) (by omega)
    (by have := a.isLt; omega)
  have hb := r324LayerPos_ge_of_split hjm hsplit (a := j + (b : ℕ)) (by omega)
    (by have := b.isLt; omega)
  have := r324LayerPos_inj τ (by have := a.isLt; omega) (by have := b.isLt; omega)
    (show r324LayerPos τ (j + (a : ℕ)) = r324LayerPos τ (j + (b : ℕ)) by omega)
  exact Fin.ext (by omega)

open Classical in
/-- The head block as a bijection of `Fin j`. -/
def r324LayerHeadPerm {m : ℕ} (τ : Equiv.Perm (Fin m)) (j : ℕ) :
    Equiv.Perm (Fin j) :=
  if h : Function.Injective (r324LayerHead τ j) then
    Equiv.ofBijective _ (Finite.injective_iff_bijective.mp h)
  else 1

open Classical in
/-- The tail block as a bijection of `Fin (m-j)`. -/
def r324LayerTailPerm {m : ℕ} (τ : Equiv.Perm (Fin m)) (j : ℕ) :
    Equiv.Perm (Fin (m - j)) :=
  if h : Function.Injective (r324LayerTail τ j) then
    Equiv.ofBijective _ (Finite.injective_iff_bijective.mp h)
  else 1

theorem r324LayerHeadPerm_pos {m : ℕ} {τ : Equiv.Perm (Fin m)} {j : ℕ}
    (hjm : j < m) (hsplit : ∀ i < j, r324LayerPos τ i < j) {i : ℕ} (hi : i < j) :
    r324LayerPos (r324LayerHeadPerm τ j) i = r324LayerPos τ i := by
  rw [r324LayerPos, dif_pos hi, r324LayerHeadPerm,
    dif_pos (r324LayerHead_injective hjm hsplit)]
  simpa using r324LayerHead_val hsplit ⟨i, hi⟩

theorem r324LayerTailPerm_pos {m : ℕ} {τ : Equiv.Perm (Fin m)} {j : ℕ}
    (hjm : j < m) (hsplit : ∀ i < j, r324LayerPos τ i < j) {i : ℕ}
    (hi : i < m - j) :
    r324LayerPos (r324LayerTailPerm τ j) i = r324LayerPos τ (j + i) - j := by
  rw [r324LayerPos, dif_pos hi, r324LayerTailPerm,
    dif_pos (r324LayerTail_injective hjm hsplit)]
  simpa using r324LayerTail_val hjm hsplit ⟨i, hi⟩

/-- **The split count.**  At most `(m-|T|)!` bijections have all the
prescribed decomposition points in `T`: the blocks between consecutive
points are permuted independently, and `∏ bₜ! ≤ (m-|T|)!`. -/
theorem r324LayerSplitAt_card_le : ∀ (m : ℕ) (T : Finset ℕ),
    (r324LayerSplitAt m T).card ≤ (m - T.card).factorial := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro T
    rcases Finset.eq_empty_or_nonempty (r324LayerSplitAt m T) with hE | ⟨τ₀, hτ₀⟩
    · simp [hE]
    rcases T.eq_empty_or_nonempty with rfl | hTne
    · have huniv : r324LayerSplitAt m ∅ = (Finset.univ : Finset (Equiv.Perm (Fin m))) := by
        ext τ; simp [r324LayerSplitAt]
      rw [huniv, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      simp
    · set j := T.max' hTne with hjdef
      have hjT : j ∈ T := T.max'_mem hTne
      obtain ⟨hj1, hjm, -⟩ := (r324LayerSplitAt_mem.mp hτ₀) j hjT
      have hk : 1 ≤ T.card := Finset.card_pos.mpr hTne
      have hTcard : T.card ≤ j := by
        have hsub : T ⊆ Finset.Icc 1 j := fun x hx =>
          Finset.mem_Icc.mpr ⟨((r324LayerSplitAt_mem.mp hτ₀) x hx).1,
            T.le_max' x hx⟩
        have := Finset.card_le_card hsub
        simpa [Nat.card_Icc] using this
      have hstep : (r324LayerSplitAt m T).card ≤
          (r324LayerSplitAt j (T.erase j)).card * (m - j).factorial := by
        have hcard : (r324LayerSplitAt m T).card ≤
            ((r324LayerSplitAt j (T.erase j)) ×ˢ
              (Finset.univ : Finset (Equiv.Perm (Fin (m - j))))).card := by
          refine Finset.card_le_card_of_injOn
            (fun τ => (r324LayerHeadPerm τ j, r324LayerTailPerm τ j))
            (fun τ hτ => ?_) (fun σ hσ σ' hσ' h => ?_)
          · obtain ⟨-, -, hsplit⟩ := (r324LayerSplitAt_mem.mp hτ) j hjT
            refine Finset.mem_product.mpr ⟨r324LayerSplitAt_mem.mpr ?_,
              Finset.mem_univ _⟩
            intro j' hj'
            obtain ⟨h1, -, hs'⟩ := (r324LayerSplitAt_mem.mp hτ) j'
              (Finset.mem_of_mem_erase hj')
            have hlt : j' < j := lt_of_le_of_ne (T.le_max' j'
              (Finset.mem_of_mem_erase hj')) (Finset.ne_of_mem_erase hj')
            refine ⟨h1, hlt, fun i hi => ?_⟩
            rw [r324LayerHeadPerm_pos hjm hsplit (by omega)]
            exact hs' i hi
          · obtain ⟨-, -, hsplitσ⟩ :=
              (r324LayerSplitAt_mem.mp (Finset.mem_coe.mp hσ)) j hjT
            obtain ⟨-, -, hsplitσ'⟩ :=
              (r324LayerSplitAt_mem.mp (Finset.mem_coe.mp hσ')) j hjT
            have hhead : r324LayerHeadPerm σ j = r324LayerHeadPerm σ' j :=
              congrArg Prod.fst h
            have htail : r324LayerTailPerm σ j = r324LayerTailPerm σ' j :=
              congrArg Prod.snd h
            refine r324LayerPos_ext fun i hi => ?_
            rcases Nat.lt_or_ge i j with hij | hij
            · rw [← r324LayerHeadPerm_pos hjm hsplitσ hij,
                ← r324LayerHeadPerm_pos hjm hsplitσ' hij, hhead]
            · have e1 := r324LayerTailPerm_pos hjm hsplitσ (i := i - j) (by omega)
              have e2 := r324LayerTailPerm_pos hjm hsplitσ' (i := i - j) (by omega)
              have hji : j + (i - j) = i := by omega
              rw [hji] at e1 e2
              rw [htail] at e1
              have gσ := r324LayerPos_ge_of_split hjm hsplitσ hij hi
              have gσ' := r324LayerPos_ge_of_split hjm hsplitσ' hij hi
              omega
        simpa [Finset.card_product, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin] using hcard
      have hih := ih j hjm (T.erase j)
      have hcarderase : (T.erase j).card = T.card - 1 :=
        Finset.card_erase_of_mem hjT
      have hfac : (j - (T.card - 1)).factorial * (m - j).factorial ≤
          (m - T.card).factorial := by
        have h1 : 1 ≤ j - (T.card - 1) := by omega
        have hmain := r324LayerFactorial_mul_le h1 (m - j - 1)
        have e1 : m - j - 1 + 1 = m - j := by omega
        have e2 : j - (T.card - 1) + (m - j - 1) = m - T.card := by omega
        rwa [e1, e2] at hmain
      calc (r324LayerSplitAt m T).card
          ≤ (r324LayerSplitAt j (T.erase j)).card * (m - j).factorial := hstep
        _ ≤ (j - (T.erase j).card).factorial * (m - j).factorial :=
            Nat.mul_le_mul_right _ hih
        _ = (j - (T.card - 1)).factorial * (m - j).factorial := by
            rw [hcarderase]
        _ ≤ (m - T.card).factorial := hfac

/-! ## The σ-grading layer count for the split grade -/

theorem r324LayerSplit_subsetCount {m : ℕ} (S : Finset (Fin m)) :
    ((((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
        fun τ => S ⊆ r324LayerSplit τ).card : ℕ) : ℝ) ≤
      (1 : ℝ) ^ m * (((m - S.card).factorial : ℕ) : ℝ) := by
  have hsub : ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
      fun τ => S ⊆ r324LayerSplit τ) ⊆ r324LayerSplitAt m (S.image Fin.val) := by
    intro τ hτ
    have hτ' := (Finset.mem_filter.mp hτ).2
    refine r324LayerSplitAt_mem.mpr fun j hj => ?_
    obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp hj
    have hi := hτ' hiS
    rw [r324LayerSplit, Finset.mem_filter] at hi
    exact ⟨hi.2.1, i.isLt, hi.2.2⟩
  have h2 := r324LayerSplitAt_card_le m (S.image Fin.val)
  rw [Finset.card_image_of_injective S Fin.val_injective] at h2
  have hnat : (((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
      fun τ => S ⊆ r324LayerSplit τ).card) ≤ (m - S.card).factorial :=
    le_trans (Finset.card_le_card hsub) h2
  simpa using (Nat.cast_le (α := ℝ)).mpr hnat

/-- **The σ-grading layer count for the split grade, unconditionally.**
Grade `j` is carried by at most `4^m·(m-j)!` bijections.  Combined with
`r324Grade_layeredAt_of_collapse` this is the entire counting half of
clause A for the grade the lattice actually produces; only the per-`τ`
graded lattice budget `R324ColGradedBudgetAt` remains. -/
theorem r324Layer_permLayerCount_split {m : ℕ} (hm : 1 ≤ m) :
    R324GradePermLayerCount 4 m r324LayerSplitGrade := by
  have h := r324Grade_permLayerCount_of_subsetCount (m := m) (ι := Fin m)
    (gradeP := r324LayerSplitGrade) (B := 1) r324LayerSplit
    (le_refl 1) hm (by simp) r324LayerSplitGrade_le
    r324LayerSplitGrade_le_card r324LayerSplit_subsetCount
  simpa using h

/-- **The order-three slice.**  At `m = 3` the split grade obeys the
layer count, and the identity still carries the full power `m-1 = 2`
(`r324LayerSplitGrade_one`) — the proved flat calibration
`r324Grade_permLayerCount_flat_three` is the same slice with the grade
rounded up to `2` for all six bijections. -/
theorem r324Layer_permLayerCount_split_three :
    R324GradePermLayerCount 4 3 r324LayerSplitGrade :=
  r324Layer_permLayerCount_split (by norm_num)

theorem r324LayerSplitGrade_one_three :
    r324LayerSplitGrade (1 : Equiv.Perm (Fin 3)) = 2 :=
  r324LayerSplitGrade_one (by norm_num)

/-! ## Analytic input for clause A

Together with the adjacency statistic `r324Layer_gradeCoincidenceCount`,
`r324Layer_permLayerCount_split` supplies the counting half of the
σ-grading.  The analytic input of
`r324Grade_cappedCrossLedger_of_gradedLattice` is

`R324ColGradedBudgetAt ρ D m r324LayerSplitGrade`,

i.e. `∑_q ∏ᵢ‖ρ̂(εqᵢ)‖²·∏ⱼ⟨Sⱼ⟩⁻²⟨Sⱼ^τ⟩⁻² ≤ D^m·|log ε|^{grade τ}` over
the zero-sum sector.  Its inductive step is: *if `j` is the least
decomposition point of `τ`, the zero-sum
lattice sum factorises over the head block `{0,…,j-1}` and the tail
block `{j,…,m-1}`* (the head keys sum to `Sⱼ`, which is the only
variable shared with the tail), *the head factor is the `j`-key sum at
the reduced grade of `τ|head` and the tail factor is the `(m-j)`-key
sum at the reduced grade of `τ|tail`, and the shared variable `Sⱼ` is
summed once against `⟨Sⱼ⟩⁻⁴`, contributing one factor `|log ε|*
(`r324SW_translated_window_le_log`)*, giving
`grade τ = grade(head) + grade(tail) + 1`, which is exactly the
recursion satisfied by `r324LayerSplitGrade`* (the two extremes being
`τ = id`, where the recursion iterates `m-1` times, and a `τ` with no
decomposition point, where it stops immediately at `grade = 1`, the
single free window of the whole zero-sum cube).  The base case with no
decomposition point is the proved `R324ColDoubledBudgetAt` route:
`r324Col_tsum_latWeight_le` already bounds *every* `τ` by the identity
pattern, which is `|log ε|^{m-1}`; the content of the general step is
that a `τ` without decomposition points is bounded by a *single* log,
for which the pinned keys must be eliminated by the zero-sum constraint
rather than summed (a freely summed key costs `ε⁻⁴`,
`r324SW_symbol_mass_le`, and a marked one `ε⁻⁸`,
`r324RoutedWindow_marked_window_le`). -/

end

end Anderson4D
