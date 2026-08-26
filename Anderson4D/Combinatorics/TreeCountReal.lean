import Anderson4D.HeppTree.Basic

/-!
# Quantitative counting for the Hepp-tree carrier

Paper: L-5.2 — tree counting via the Dyck-word injection

This is paper Lemma 5.2 for `Anderson4D.PlaneTree`, the carrier used by the
formalization.

A valid tree with at most `r` leaves is injected into
`Fin (4 * r + 1) × (Fin (4 * r) → Bool)` through the balanced-parentheses
key.  This gives the explicit bound `4 ^ (4 * r)`.  The final declarations
package the sets of trees with at most, and exactly, `r` leaves as actual
`Finset PlaneTree`s.
-/

namespace Anderson4D

namespace PlaneTree

/-! ## Size and key bounds on the real carrier -/

private theorem tcReal_size_lt_of_mem {c : PlaneTree} {cs : List PlaneTree}
    (hc : c ∈ cs) : c.size < (node cs).size := by
  have hmem : c.size ∈ cs.map size := List.mem_map.mpr ⟨c, hc, rfl⟩
  have hle : c.size ≤ (cs.map size).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  rw [size, sizeList_eq_map]
  omega

private theorem tcReal_induction {motive : PlaneTree → Prop}
    (step : ∀ cs : List PlaneTree, (∀ c ∈ cs, motive c) → motive (node cs)) :
    ∀ t, motive t
  | node cs => step cs fun c _hc => tcReal_induction step c
termination_by t => t.size
decreasing_by exact tcReal_size_lt_of_mem _hc

private theorem tcReal_isValidList_iff (cs : List PlaneTree) :
    isValidList cs = true ↔ ∀ c ∈ cs, c.isValid = true := by
  induction cs with
  | nil => simp [isValidList]
  | cons c cs ih =>
    rw [isValidList, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hc, hcs⟩ d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hc
      · exact hcs d hd
    · intro h
      exact ⟨h c (List.mem_cons_self ..),
        fun d hd => h d (List.mem_cons_of_mem c hd)⟩

private theorem tcReal_isValid_node_iff {cs : List PlaneTree} :
    (node cs).isValid = true ↔
      cs.length ≠ 1 ∧ ∀ c ∈ cs, c.isValid = true := by
  rw [isValid, Bool.and_eq_true, tcReal_isValidList_iff]
  simp [bne_iff_ne]

private theorem tcReal_sum_size_add_length_le (cs : List PlaneTree)
    (h : ∀ c ∈ cs, c.size + 1 ≤ 2 * c.leafCount) :
    (cs.map size).sum + cs.length ≤ 2 * (cs.map leafCount).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := h c (List.mem_cons_self ..)
    have hcs := ih fun d hd => h d (List.mem_cons_of_mem c hd)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- A real-carrier valid Hepp tree has at most twice as many vertices as
leaves, in subtraction-free form. -/
theorem size_add_one_le_of_isValid :
    ∀ t : PlaneTree, t.isValid = true → t.size + 1 ≤ 2 * t.leafCount := by
  intro t
  induction t using tcReal_induction with
  | step cs ih =>
    intro ht
    rw [tcReal_isValid_node_iff] at ht
    obtain ⟨hlen, hall⟩ := ht
    have hsum :=
      tcReal_sum_size_add_length_le cs fun c hc => ih c hc (hall c hc)
    have hsize : (node cs).size = 1 + (cs.map size).sum := by
      rw [size, sizeList_eq_map]
    have hleaf : (node cs).leafCount = max 1 (cs.map leafCount).sum := by
      rw [leafCount, leafCountList_eq_map]
    cases cs with
    | nil =>
      rw [hsize, hleaf]
      simp
    | cons c cs' =>
      have hone : 1 ≤ c.leafCount := by
        obtain ⟨ds⟩ := c
        exact le_max_left 1 _
      rw [hsize, hleaf]
      simp only [List.map_cons, List.sum_cons] at hsum ⊢
      simp only [List.length_cons] at hsum hlen
      omega

/-- Paper Lemma 5.2, size part, on `Anderson4D.PlaneTree`. -/
theorem size_le_of_isValid (t : PlaneTree) (ht : t.isValid = true) :
    t.size ≤ 2 * t.leafCount - 1 := by
  have h := size_add_one_le_of_isValid t ht
  omega

private theorem tcReal_keyList_length (cs : List PlaneTree)
    (h : ∀ c ∈ cs, (key c).length = 2 * c.size) :
    (keyList cs).length = 2 * (cs.map size).sum := by
  induction cs with
  | nil => simp [keyList]
  | cons c cs ih =>
    have hc := h c (List.mem_cons_self ..)
    have hcs := ih fun d hd => h d (List.mem_cons_of_mem c hd)
    rw [keyList]
    simp only [List.length_append, List.map_cons, List.sum_cons]
    omega

/-- Each vertex of a real-carrier tree contributes one opening and one
closing symbol to its key. -/
theorem key_length : ∀ t : PlaneTree, (key t).length = 2 * t.size := by
  intro t
  induction t using tcReal_induction with
  | step cs ih =>
    have hforest := tcReal_keyList_length cs ih
    rw [key, size, sizeList_eq_map]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega

/-- Every symbol in a real-carrier tree key is either `0` or `1`. -/
theorem key_mem : ∀ t : PlaneTree, ∀ x ∈ key t, x = 0 ∨ x = 1 := by
  intro t
  induction t using tcReal_induction with
  | step cs ih =>
    intro x hx
    rw [key] at hx
    rcases List.mem_cons.mp hx with hzero | hx
    · exact Or.inl hzero
    rcases List.mem_append.mp hx with hx | hone
    · rw [keyList_eq_map] at hx
      obtain ⟨ks, hks, hxks⟩ := List.mem_flatten.mp hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hks
      exact ih c hc x hxks
    · exact Or.inr (List.mem_singleton.mp hone)

private theorem tcReal_key_length_le {r : ℕ} {t : PlaneTree}
    (hv : t.isValid = true) (hl : t.leafCount ≤ r) :
    (key t).length ≤ 4 * r := by
  have hsize := size_add_one_le_of_isValid t hv
  have hkey := key_length t
  omega

/-! ## Explicit encoding and cardinality -/

/-- The type of valid real-carrier trees having at most `r` leaves. -/
abbrev ValidTreesAtMost (r : ℕ) :=
  {t : PlaneTree // t.isValid = true ∧ t.leafCount ≤ r}

/-- Bounded binary-word code used to count `ValidTreesAtMost r`. -/
def validTreeCode (r : ℕ) :
    ValidTreesAtMost r → Fin (4 * r + 1) × (Fin (4 * r) → Bool) :=
  fun t =>
    ⟨⟨(key t.1).length,
      Nat.lt_succ_of_le (tcReal_key_length_le t.2.1 t.2.2)⟩,
      fun i => (key t.1).getD i 0 == 1⟩

/-- The bounded binary-word code is injective. -/
theorem validTreeCode_injective (r : ℕ) :
    Function.Injective (validTreeCode r) := by
  intro t t' h
  rw [Prod.ext_iff] at h
  obtain ⟨hlenCode, hbits⟩ := h
  have hlen : (key t.1).length = (key t'.1).length :=
    congrArg Fin.val hlenCode
  have hkey : key t.1 = key t'.1 := by
    apply List.ext_getElem hlen
    intro i hi hi'
    have hiCode : i < 4 * r :=
      lt_of_lt_of_le hi (tcReal_key_length_le t.2.1 t.2.2)
    have hbit :
        ((key t.1).getD i 0 == 1) = ((key t'.1).getD i 0 == 1) :=
      congrFun hbits ⟨i, hiCode⟩
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at hbit
    have hleft := key_mem t.1 _ (List.getElem_mem hi)
    have hright := key_mem t'.1 _ (List.getElem_mem hi')
    rcases hleft with hleft | hleft <;>
      rcases hright with hright | hright <;>
      rw [hleft, hright] at hbit ⊢ <;> simp_all
  exact Subtype.ext (key_injective hkey)

instance validTreesAtMostFinite (r : ℕ) : Finite (ValidTreesAtMost r) :=
  Finite.of_injective (validTreeCode r) (validTreeCode_injective r)

noncomputable instance validTreesAtMostFintype (r : ℕ) :
    Fintype (ValidTreesAtMost r) :=
  Fintype.ofFinite _

private theorem tcReal_succ_le_two_pow (m : ℕ) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    omega

/-- Quantitative real-carrier version of paper Lemma 5.2. -/
theorem card_validTreesAtMost_type_le (r : ℕ) :
    Fintype.card (ValidTreesAtMost r) ≤ 4 ^ (4 * r) := by
  have hcode :
      Fintype.card (ValidTreesAtMost r)
        ≤ Fintype.card (Fin (4 * r + 1) × (Fin (4 * r) → Bool)) :=
    Fintype.card_le_of_injective (validTreeCode r) (validTreeCode_injective r)
  have htarget :
      Fintype.card (Fin (4 * r + 1) × (Fin (4 * r) → Bool))
        = (4 * r + 1) * 2 ^ (4 * r) := by
    simp
  have hpow : (4 * r + 1) * 2 ^ (4 * r) ≤ 4 ^ (4 * r) := by
    calc
      (4 * r + 1) * 2 ^ (4 * r)
          ≤ 2 ^ (4 * r) * 2 ^ (4 * r) :=
        Nat.mul_le_mul (tcReal_succ_le_two_pow (4 * r)) le_rfl
      _ = 4 ^ (4 * r) := by
        rw [← mul_pow]
        norm_num
  rw [htarget] at hcode
  exact hcode.trans hpow

/-- The actual finite set of valid real-carrier trees with at most `r`
leaves. -/
noncomputable def validTreesAtMost (r : ℕ) : Finset PlaneTree :=
  Finset.univ.image fun t : ValidTreesAtMost r => t.1

@[simp] theorem mem_validTreesAtMost {r : ℕ} {t : PlaneTree} :
    t ∈ validTreesAtMost r ↔ t.isValid = true ∧ t.leafCount ≤ r := by
  simp [validTreesAtMost]

/-- Cardinality bound for the concrete `Finset` of valid trees with at most
`r` leaves. -/
theorem card_validTreesAtMost_le (r : ℕ) :
    (validTreesAtMost r).card ≤ 4 ^ (4 * r) := by
  rw [validTreesAtMost,
    Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.card_univ]
  exact card_validTreesAtMost_type_le r

/-- The corresponding finite-set statement, for clients formulated with
`Set.Finite` or `Nat.card`. -/
theorem finite_validTreesAtMost (r : ℕ) :
    Set.Finite {t : PlaneTree | t.isValid = true ∧ t.leafCount ≤ r} := by
  have heq :
      {t : PlaneTree | t.isValid = true ∧ t.leafCount ≤ r}
        = (validTreesAtMost r : Set PlaneTree) := by
    ext t
    simp
  rw [heq]
  exact (validTreesAtMost r).finite_toSet

/-- The actual finite set of valid real-carrier trees with exactly `r`
leaves. -/
noncomputable def validTreesExactly (r : ℕ) : Finset PlaneTree :=
  (validTreesAtMost r).filter fun t => t.leafCount = r

@[simp] theorem mem_validTreesExactly {r : ℕ} {t : PlaneTree} :
    t ∈ validTreesExactly r ↔ t.isValid = true ∧ t.leafCount = r := by
  rw [validTreesExactly, Finset.mem_filter, mem_validTreesAtMost]
  constructor
  · rintro ⟨⟨hv, _⟩, hleaf⟩
    exact ⟨hv, hleaf⟩
  · rintro ⟨hv, hleaf⟩
    exact ⟨⟨hv, by omega⟩, hleaf⟩

/-- Cardinality bound for valid real-carrier trees with exactly `r` leaves. -/
theorem card_validTreesExactly_le (r : ℕ) :
    (validTreesExactly r).card ≤ 4 ^ (4 * r) := by
  exact (Finset.card_filter_le _ _).trans (card_validTreesAtMost_le r)

end PlaneTree

end Anderson4D
