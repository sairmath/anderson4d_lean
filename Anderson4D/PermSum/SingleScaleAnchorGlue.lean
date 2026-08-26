import Anderson4D.PermSum.SingleScalePosition

/-!
# Assembly glue for anchored bidirectional sequence gains

This file supplies the two interfaces needed by the final finite-Fubini
assembly:

* a product-level identification between the gain on the original edge
  order (reverse to the left of the anchor and forward to its right) and
  the two padded outward products;
* the active-`P` sequence estimate when the exceptional set is allowed to
  depend on the anchor.

No comparison between forward and reverse gains is used.  The left product
is reindexed by reflection, the right product by translation, and every
extra padded factor is proved to be exactly one.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## The original-edge oriented product -/

/--
The gain attached to an edge in the original word order.  Edges strictly
left of the anchor are traversed outwards and hence use the reverse ratio;
edges at or to the right of the anchor use the ordinary forward ratio.
-/
noncomputable def anchoredOrientedCodeEdgeGain (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) (j : Fin n) : ℝ :=
  if j.1 < a.1 then
    min 1 (((2 : ℝ) ^ e (w j.castSucc) /
      (2 : ℝ) ^ e (w j.succ)) ^ θ)
  else
    anchoredCodeEdgeGain θ e w j

theorem anchoredOrientedCodeEdgeGain_of_lt (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) (j : Fin n) (hj : j.1 < a.1) :
    anchoredOrientedCodeEdgeGain θ e a w j =
      min 1 (((2 : ℝ) ^ e (w j.castSucc) /
        (2 : ℝ) ^ e (w j.succ)) ^ θ) := by
  simp [anchoredOrientedCodeEdgeGain, hj]

theorem anchoredOrientedCodeEdgeGain_of_le (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) (j : Fin n) (hj : a.1 ≤ j.1) :
    anchoredOrientedCodeEdgeGain θ e a w j =
      anchoredCodeEdgeGain θ e w j := by
  rw [anchoredOrientedCodeEdgeGain, if_neg (by omega)]

/--
The original-edge form consumed by finite-Fubini: use one exception set on
the original adjacency indices and orient every retained edge away from the
anchor.
-/
noncomputable def anchoredOrientedCodeWeight (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) : ℝ :=
  ∏ j ∈ Finset.univ \ E, anchoredOrientedCodeEdgeGain θ e a w j

private theorem anchoredLeftExceptionIndex_lt {n : ℕ}
    (a : Fin (n + 1)) (j : Fin n) (hj : j.1 < a.1) :
    (anchoredLeftExceptionIndex a j).1 < a.1 := by
  simp only [anchoredLeftExceptionIndex]
  omega

private theorem anchoredLeftExceptionIndex_involutive {n : ℕ}
    (a : Fin (n + 1)) (j : Fin n) (hj : j.1 < a.1) :
    anchoredLeftExceptionIndex a (anchoredLeftExceptionIndex a j) = j := by
  apply Fin.ext
  simp only [anchoredLeftExceptionIndex]
  omega

private theorem anchoredLeftExceptionIndex_injective_of_lt {n : ℕ}
    (a : Fin (n + 1)) (i j : Fin n)
    (hi : i.1 < a.1) (hj : j.1 < a.1)
    (h : anchoredLeftExceptionIndex a i =
      anchoredLeftExceptionIndex a j) :
    i = j := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [anchoredLeftExceptionIndex] at hv
  omega

/--
Reflect the retained original left edges into the genuine part of the
padded outward-left word.
-/
private theorem prod_original_left_eq_outward_left (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) :
    (∏ j ∈ ((Finset.univ \ E).filter fun j : Fin n => j.1 < a.1),
        min 1 (((2 : ℝ) ^ e (w j.castSucc) /
          (2 : ℝ) ^ e (w j.succ)) ^ θ)) =
      anchoredLeftCodeWeight θ e E a w := by
  let source :=
    (Finset.univ \ E).filter fun j : Fin n => j.1 < a.1
  let target :=
    (Finset.univ \ anchoredLeftExceptions a E).filter
      fun k : Fin n => k.1 < a.1
  let gain : Fin n → ℝ :=
    fun k => anchoredCodeEdgeGain θ e (anchoredLeftWord a w) k
  have hreindex :
      (∏ j ∈ source,
          min 1 (((2 : ℝ) ^ e (w j.castSucc) /
            (2 : ℝ) ^ e (w j.succ)) ^ θ)) =
        ∏ k ∈ target, gain k := by
    refine Finset.prod_bij
      (fun j _ => anchoredLeftExceptionIndex a j) ?_ ?_ ?_ ?_
    · intro j hj
      have hj' := Finset.mem_filter.mp hj
      have hjkeep := (Finset.mem_sdiff.mp hj'.1).2
      have hjlt := hj'.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩,
        anchoredLeftExceptionIndex_lt a j hjlt⟩
      intro hmem
      rw [anchoredLeftExceptions, Finset.mem_image] at hmem
      obtain ⟨i, hi, himage⟩ := hmem
      have hi' := Finset.mem_filter.mp hi
      have hij := anchoredLeftExceptionIndex_injective_of_lt
        a i j hi'.2 hjlt himage
      exact hjkeep (hij ▸ hi'.1)
    · intro i hi j hj hij
      exact anchoredLeftExceptionIndex_injective_of_lt
        a i j (Finset.mem_filter.mp hi).2
          (Finset.mem_filter.mp hj).2 hij
    · intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hkkeep := (Finset.mem_sdiff.mp hk'.1).2
      have hklt := hk'.2
      let j := anchoredLeftExceptionIndex a k
      have hjlt : j.1 < a.1 :=
        anchoredLeftExceptionIndex_lt a k hklt
      have hmap : anchoredLeftExceptionIndex a j = k := by
        exact anchoredLeftExceptionIndex_involutive a k hklt
      have hjnot : j ∉ E := by
        intro hjE
        have himage : anchoredLeftExceptionIndex a j ∈
            anchoredLeftExceptions a E := by
          rw [anchoredLeftExceptions, Finset.mem_image]
          exact ⟨j, Finset.mem_filter.mpr ⟨hjE, hjlt⟩, rfl⟩
        exact hkkeep (hmap ▸ himage)
      refine ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjnot⟩, hjlt⟩,
        hmap⟩
    · intro j hj
      have hjlt := (Finset.mem_filter.mp hj).2
      exact (anchoredLeftCodeEdgeGain_at_original
        θ e w a j hjlt).symm
  have hpad :
      (∏ k ∈
          (Finset.univ \ anchoredLeftExceptions a E).filter
            (fun k : Fin n => ¬k.1 < a.1),
          gain k) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    have hknot := (Finset.mem_filter.mp hk).2
    exact anchoredLeftCodeEdgeGain_eq_one_of_anchor_le
      θ e w a k (by omega)
  calc
    (∏ j ∈ ((Finset.univ \ E).filter fun j : Fin n => j.1 < a.1),
        min 1 (((2 : ℝ) ^ e (w j.castSucc) /
          (2 : ℝ) ^ e (w j.succ)) ^ θ)) =
        ∏ k ∈ target, gain k := by
          simpa only [source, target] using hreindex
    _ = (∏ k ∈ target, gain k) *
        ∏ k ∈
          (Finset.univ \ anchoredLeftExceptions a E).filter
            (fun k : Fin n => ¬k.1 < a.1),
          gain k := by rw [hpad, mul_one]
    _ = ∏ k ∈ Finset.univ \ anchoredLeftExceptions a E, gain k := by
      simpa only [target] using
        Finset.prod_filter_mul_prod_filter_not
          (Finset.univ \ anchoredLeftExceptions a E)
          (fun k : Fin n => k.1 < a.1) gain
    _ = anchoredLeftCodeWeight θ e E a w := by
      rfl

private theorem anchoredRightExceptionIndex_injective_of_le {n : ℕ}
    (a : Fin (n + 1)) (i j : Fin n)
    (hi : a.1 ≤ i.1) (hj : a.1 ≤ j.1)
    (h : anchoredRightExceptionIndex a i =
      anchoredRightExceptionIndex a j) :
    i = j := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [anchoredRightExceptionIndex] at hv
  omega

/--
Translate the retained original right edges into the genuine part of the
padded outward-right word.
-/
private theorem prod_original_right_eq_outward_right (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) :
    (∏ j ∈ ((Finset.univ \ E).filter fun j : Fin n => a.1 ≤ j.1),
        anchoredCodeEdgeGain θ e w j) =
      anchoredRightCodeWeight θ e E a w := by
  let source :=
    (Finset.univ \ E).filter fun j : Fin n => a.1 ≤ j.1
  let target :=
    (Finset.univ \ anchoredRightExceptions a E).filter
      fun k : Fin n => a.1 + k.1 < n
  let gain : Fin n → ℝ :=
    fun k => anchoredCodeEdgeGain θ e (anchoredRightWord a w) k
  have hreindex :
      (∏ j ∈ source, anchoredCodeEdgeGain θ e w j) =
        ∏ k ∈ target, gain k := by
    refine Finset.prod_bij
      (fun j _ => anchoredRightExceptionIndex a j) ?_ ?_ ?_ ?_
    · intro j hj
      have hj' := Finset.mem_filter.mp hj
      have hjkeep := (Finset.mem_sdiff.mp hj'.1).2
      have hjle := hj'.2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · intro hmem
        rw [anchoredRightExceptions, Finset.mem_image] at hmem
        obtain ⟨i, hi, himage⟩ := hmem
        have hi' := Finset.mem_filter.mp hi
        have hij := anchoredRightExceptionIndex_injective_of_le
          a i j hi'.2 hjle himage
        exact hjkeep (hij ▸ hi'.1)
      · simp only [anchoredRightExceptionIndex]
        omega
    · intro i hi j hj hij
      exact anchoredRightExceptionIndex_injective_of_le
        a i j (Finset.mem_filter.mp hi).2
          (Finset.mem_filter.mp hj).2 hij
    · intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hkkeep := (Finset.mem_sdiff.mp hk'.1).2
      have hklt := hk'.2
      let j : Fin n := ⟨a.1 + k.1, hklt⟩
      have hjle : a.1 ≤ j.1 := by
        dsimp only [j]
        omega
      have hmap : anchoredRightExceptionIndex a j = k := by
        apply Fin.ext
        simp only [anchoredRightExceptionIndex]
        dsimp only [j]
        omega
      have hjnot : j ∉ E := by
        intro hjE
        have himage : anchoredRightExceptionIndex a j ∈
            anchoredRightExceptions a E := by
          rw [anchoredRightExceptions, Finset.mem_image]
          exact ⟨j, Finset.mem_filter.mpr ⟨hjE, hjle⟩, rfl⟩
        exact hkkeep (hmap ▸ himage)
      refine ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjnot⟩, hjle⟩,
        hmap⟩
    · intro j hj
      have hjle := (Finset.mem_filter.mp hj).2
      exact (anchoredRightCodeEdgeGain_at_original
        θ e w a j hjle).symm
  have hpad :
      (∏ k ∈
          (Finset.univ \ anchoredRightExceptions a E).filter
            (fun k : Fin n => ¬a.1 + k.1 < n),
          gain k) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    have hknot := (Finset.mem_filter.mp hk).2
    exact anchoredRightCodeEdgeGain_eq_one_of_le_anchor_add
      θ e w a k (by omega)
  calc
    (∏ j ∈ ((Finset.univ \ E).filter fun j : Fin n => a.1 ≤ j.1),
        anchoredCodeEdgeGain θ e w j) =
        ∏ k ∈ target, gain k := by
          simpa only [source, target] using hreindex
    _ = (∏ k ∈ target, gain k) *
        ∏ k ∈
          (Finset.univ \ anchoredRightExceptions a E).filter
            (fun k : Fin n => ¬a.1 + k.1 < n),
          gain k := by rw [hpad, mul_one]
    _ = ∏ k ∈ Finset.univ \ anchoredRightExceptions a E, gain k := by
      simpa only [target] using
        Finset.prod_filter_mul_prod_filter_not
          (Finset.univ \ anchoredRightExceptions a E)
          (fun k : Fin n => a.1 + k.1 < n) gain
    _ = anchoredRightCodeWeight θ e E a w := by
      rfl

/--
Exact assembly rewrite: the single product on retained original edges,
oriented away from the anchor, is the product of the two padded outward
weights.  This is an equality, not an inequality or a comparison of
oppositely oriented gains.
-/
theorem anchoredOrientedCodeWeight_eq_bidirectional (θ : ℝ) {n ν : ℕ}
    (e : Fin ν → ℤ) (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → Fin ν) :
    anchoredOrientedCodeWeight θ e E a w =
      anchoredBidirectionalCodeWeight θ e E a w := by
  let kept := Finset.univ \ E
  have hsplit :
      (∏ j ∈ kept, anchoredOrientedCodeEdgeGain θ e a w j) =
        (∏ j ∈ kept.filter (fun j : Fin n => j.1 < a.1),
          anchoredOrientedCodeEdgeGain θ e a w j) *
        ∏ j ∈ kept.filter (fun j : Fin n => ¬j.1 < a.1),
          anchoredOrientedCodeEdgeGain θ e a w j := by
    exact (Finset.prod_filter_mul_prod_filter_not kept
      (fun j : Fin n => j.1 < a.1)
      (anchoredOrientedCodeEdgeGain θ e a w)).symm
  have hleft :
      (∏ j ∈ kept.filter (fun j : Fin n => j.1 < a.1),
          anchoredOrientedCodeEdgeGain θ e a w j) =
        anchoredLeftCodeWeight θ e E a w := by
    calc
      (∏ j ∈ kept.filter (fun j : Fin n => j.1 < a.1),
          anchoredOrientedCodeEdgeGain θ e a w j) =
          ∏ j ∈ kept.filter (fun j : Fin n => j.1 < a.1),
            min 1 (((2 : ℝ) ^ e (w j.castSucc) /
              (2 : ℝ) ^ e (w j.succ)) ^ θ) := by
            apply Finset.prod_congr rfl
            intro j hj
            exact anchoredOrientedCodeEdgeGain_of_lt
              θ e a w j (Finset.mem_filter.mp hj).2
      _ = anchoredLeftCodeWeight θ e E a w := by
        simpa only [kept] using
          prod_original_left_eq_outward_left θ e E a w
  have hright :
      (∏ j ∈ kept.filter (fun j : Fin n => ¬j.1 < a.1),
          anchoredOrientedCodeEdgeGain θ e a w j) =
        anchoredRightCodeWeight θ e E a w := by
    calc
      (∏ j ∈ kept.filter (fun j : Fin n => ¬j.1 < a.1),
          anchoredOrientedCodeEdgeGain θ e a w j) =
          ∏ j ∈ kept.filter (fun j : Fin n => ¬j.1 < a.1),
            anchoredCodeEdgeGain θ e w j := by
            apply Finset.prod_congr rfl
            intro j hj
            exact anchoredOrientedCodeEdgeGain_of_le
              θ e a w j (by
                have := (Finset.mem_filter.mp hj).2
                omega)
      _ = ∏ j ∈ kept.filter (fun j : Fin n => a.1 ≤ j.1),
            anchoredCodeEdgeGain θ e w j := by
          congr 1
          ext j
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hj, hjnot⟩
            exact ⟨hj, by omega⟩
          · rintro ⟨hj, hjle⟩
            exact ⟨hj, by omega⟩
      _ = anchoredRightCodeWeight θ e E a w := by
        simpa only [kept] using
          prod_original_right_eq_outward_right θ e E a w
  calc
    anchoredOrientedCodeWeight θ e E a w =
        ∏ j ∈ kept, anchoredOrientedCodeEdgeGain θ e a w j := by
      rfl
    _ = (∏ j ∈ kept.filter (fun j : Fin n => j.1 < a.1),
          anchoredOrientedCodeEdgeGain θ e a w j) *
        ∏ j ∈ kept.filter (fun j : Fin n => ¬j.1 < a.1),
          anchoredOrientedCodeEdgeGain θ e a w j := hsplit
    _ = anchoredLeftCodeWeight θ e E a w *
        anchoredRightCodeWeight θ e E a w := by rw [hleft, hright]
    _ = anchoredBidirectionalCodeWeight θ e E a w := rfl

/-! ## The original-edge oriented product on the active carrier -/

/-- Active-`P` version of the original-edge gain oriented away from the
anchor. -/
noncomputable def anchoredOrientedActivePEdgeGain (θ : ℝ)
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    {n : ℕ} (a : Fin (n + 1))
    (w : Fin (n + 1) → ActivePClass Nm mu) (j : Fin n) : ℝ :=
  if j.1 < a.1 then
    min 1 (((((w j.castSucc).1 : ℕ) : ℝ) /
      (((w j.succ).1 : ℕ) : ℝ)) ^ θ)
  else
    anchoredActivePEdgeGain θ w j

/-- Active-`P` product in the original edge order, with one original
exception set and the two directions oriented away from the anchor. -/
noncomputable def anchoredOrientedActivePWeight (θ : ℝ)
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    {n : ℕ} (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → ActivePClass Nm mu) : ℝ :=
  ∏ j ∈ Finset.univ \ E,
    anchoredOrientedActivePEdgeGain θ a w j

theorem anchoredOrientedActivePEdgeGain_enumeration (θ : ℝ)
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    {n : ℕ} (a : Fin (n + 1))
    (x : Fin (n + 1) → Fin (activePCount Nm mu)) (j : Fin n) :
    anchoredOrientedActivePEdgeGain θ a
        (fun i => activePEnumeration Nm mu (x i)) j =
      anchoredOrientedCodeEdgeGain θ (activePExponent Nm mu) a x j := by
  unfold anchoredOrientedActivePEdgeGain
    anchoredOrientedCodeEdgeGain
  split_ifs
  · rw [activePEnumeration_cast_eq_zpow Nm mu (x j.castSucc),
      activePEnumeration_cast_eq_zpow Nm mu (x j.succ)]
  · exact anchoredActivePEdgeGain_enumeration θ Nm mu x j

theorem anchoredOrientedActivePWeight_enumeration (θ : ℝ)
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    {n : ℕ} (E : Finset (Fin n)) (a : Fin (n + 1))
    (x : Fin (n + 1) → Fin (activePCount Nm mu)) :
    anchoredOrientedActivePWeight θ E a
        (fun i => activePEnumeration Nm mu (x i)) =
      anchoredOrientedCodeWeight θ
        (activePExponent Nm mu) E a x := by
  unfold anchoredOrientedActivePWeight anchoredOrientedCodeWeight
  apply Finset.prod_congr rfl
  intro j _hj
  exact anchoredOrientedActivePEdgeGain_enumeration
    θ Nm mu a x j

/--
Active-carrier form of the exact assembly rewrite.  This is the bridge from
the original finite-Fubini product directly to the padded bidirectional
sequence weight.
-/
theorem anchoredOrientedActivePWeight_eq_bidirectional (θ : ℝ)
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    {n : ℕ} (E : Finset (Fin n)) (a : Fin (n + 1))
    (w : Fin (n + 1) → ActivePClass Nm mu) :
    anchoredOrientedActivePWeight θ E a w =
      anchoredBidirectionalActivePWeight θ E a w := by
  let x : Fin (n + 1) → Fin (activePCount Nm mu) :=
    fun i => (activePEnumeration Nm mu).symm (w i)
  have hw :
      (fun i => activePEnumeration Nm mu (x i)) = w := by
    funext i
    simp [x]
  rw [← hw,
    anchoredOrientedActivePWeight_enumeration,
    anchoredBidirectionalActivePWeight_enumeration,
    anchoredOrientedCodeWeight_eq_bidirectional]

/-! ## Anchor-dependent exception sets on the active carrier -/

/--
The active-`P` anchored estimate with an exception set chosen separately at
each anchor.  The same fixed budget applies uniformly to every choice.
-/
theorem anchoredBidirectional_activeP_sum_le_varyingExceptions
    (θ : ℝ) (hθ : 0 < θ) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (n : ℕ), activePCount Nm mu ≤ n + 1 →
        ∀ E : Fin (n + 1) → Finset (Fin n),
          (∀ a, (E a).card ≤ B) →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight θ (E a) a w
            ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hfixed⟩ :=
    anchoredBidirectional_code_fixedAnchor_sum_le θ hθ B
  refine ⟨2 * C, by nlinarith, ?_⟩
  intro t Nm mu n hν E hE
  let wordEquiv := activePWordEquiv Nm mu (n + 1)
  have hanchor :
      ∀ a : Fin (n + 1),
        (∑ w : Fin (n + 1) → ActivePClass Nm mu,
            anchoredBidirectionalActivePWeight θ (E a) a w) ≤
          C ^ (n + 1) := by
    intro a
    have hcode :=
      hfixed n (activePCount Nm mu) (activePExponent Nm mu)
        hν (activePExponent_injective Nm mu) (E a) (hE a) a
    have hreindex :
        (∑ x : Fin (n + 1) → Fin (activePCount Nm mu),
            anchoredBidirectionalCodeWeight θ
              (activePExponent Nm mu) (E a) a x) =
          ∑ w : Fin (n + 1) → ActivePClass Nm mu,
            anchoredBidirectionalActivePWeight θ (E a) a w := by
      apply Fintype.sum_equiv wordEquiv
      intro x
      exact
        (anchoredBidirectionalActivePWeight_enumeration
          θ Nm mu (E a) a x).symm
    rw [← hreindex]
    exact hcode
  have hcount :
      ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
    exact_mod_cast Nat.le_of_lt (n + 1).lt_two_pow_self
  calc
    (∑ a : Fin (n + 1),
        ∑ w : Fin (n + 1) → ActivePClass Nm mu,
          anchoredBidirectionalActivePWeight θ (E a) a w) ≤
        ∑ _a : Fin (n + 1), C ^ (n + 1) :=
      Finset.sum_le_sum fun a _ => hanchor a
    _ = ((n + 1 : ℕ) : ℝ) * C ^ (n + 1) := by simp
    _ ≤ (2 : ℝ) ^ (n + 1) * C ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hcount
        (pow_nonneg (le_trans zero_le_one hC) _)
    _ = (2 * C) ^ (n + 1) := by rw [mul_pow]

/--
Paper-length form of the anchor-dependent active-`P` estimate.  With
`m = totalMultiplicity mu`, the word has `m` positions and `m-1` edges.
-/
theorem anchoredBidirectional_totalMultiplicity_varyingExceptions
    (θ : ℝ) (hθ : 0 < θ) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let n := totalMultiplicity mu - 1
        ∀ E : Fin (n + 1) → Finset (Fin n),
          (∀ a, (E a).card ≤ B) →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight θ (E a) a w
            ≤ C ^ totalMultiplicity mu := by
  obtain ⟨C, hC, hbound⟩ :=
    anchoredBidirectional_activeP_sum_le_varyingExceptions θ hθ B
  refine ⟨C, hC, ?_⟩
  intro t Nm mu
  dsimp only
  intro E hE
  have hm1 : 1 ≤ totalMultiplicity mu :=
    le_trans (by omega) (two_le_totalMultiplicity mu)
  have hlen :
      totalMultiplicity mu - 1 + 1 = totalMultiplicity mu :=
    Nat.sub_add_cancel hm1
  have hν :
      activePCount Nm mu ≤ totalMultiplicity mu - 1 + 1 := by
    rw [hlen]
    exact activePCount_le_totalMultiplicity Nm mu
  have h :=
    hbound Nm mu (totalMultiplicity mu - 1) hν E hE
  simpa only [hlen] using h

/--
Final assembly-facing form: sum the original-edge active-`P` weights when
the exception set varies with the anchor.  The proof rewrites each summand
by the exact orientation theorem above and then invokes the bidirectional
bound; no exponent comparison is involved.
-/
theorem anchoredOriented_activeP_sum_le_varyingExceptions
    (θ : ℝ) (hθ : 0 < θ) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (n : ℕ), activePCount Nm mu ≤ n + 1 →
        ∀ E : Fin (n + 1) → Finset (Fin n),
          (∀ a, (E a).card ≤ B) →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredOrientedActivePWeight θ (E a) a w
            ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hbound⟩ :=
    anchoredBidirectional_activeP_sum_le_varyingExceptions θ hθ B
  refine ⟨C, hC, ?_⟩
  intro t Nm mu n hν E hE
  simpa only [anchoredOrientedActivePWeight_eq_bidirectional] using
    hbound Nm mu n hν E hE

/-- Literal paper-length version of the original-edge, anchor-varying
active-`P` estimate. -/
theorem anchoredOriented_totalMultiplicity_varyingExceptions
    (θ : ℝ) (hθ : 0 < θ) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let n := totalMultiplicity mu - 1
        ∀ E : Fin (n + 1) → Finset (Fin n),
          (∀ a, (E a).card ≤ B) →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredOrientedActivePWeight θ (E a) a w
            ≤ C ^ totalMultiplicity mu := by
  obtain ⟨C, hC, hbound⟩ :=
    anchoredBidirectional_totalMultiplicity_varyingExceptions θ hθ B
  refine ⟨C, hC, ?_⟩
  intro t Nm mu
  dsimp only
  intro E hE
  simpa only [anchoredOrientedActivePWeight_eq_bidirectional] using
    hbound Nm mu E hE

/--
Convenience specialization at exponent `1/16` when each anchor has at most
twenty skipped edges.  The final even/odd union uses the forty-exception
interface below.
-/
theorem anchoredBidirectional_activeP_varyingExceptions_oneSixteenth_twenty :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (n : ℕ), activePCount Nm mu ≤ n + 1 →
        ∀ E : Fin (n + 1) → Finset (Fin n),
          (∀ a, (E a).card ≤ 20) →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight (1 / 16 : ℝ) (E a) a w
            ≤ C ^ (n + 1) :=
  anchoredBidirectional_activeP_sum_le_varyingExceptions
    (1 / 16 : ℝ) (by norm_num) 20

/-- Literal `m = totalMultiplicity mu` form of the twenty-exception
convenience specialization. -/
theorem
    anchoredBidirectional_totalMultiplicity_varyingExceptions_oneSixteenth_twenty :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let n := totalMultiplicity mu - 1
        ∀ E : Fin (n + 1) → Finset (Fin n),
          (∀ a, (E a).card ≤ 20) →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight (1 / 16 : ℝ) (E a) a w
            ≤ C ^ totalMultiplicity mu :=
  anchoredBidirectional_totalMultiplicity_varyingExceptions
    (1 / 16 : ℝ) (by norm_num) 20

/--
Paper-facing varying-exception interface after the Step 4 even/odd
geometric-mean assembly: each parity contributes at most twenty skipped
edges, so their union has budget forty at exponent `1/16`.
-/
theorem anchoredBidirectional_activeP_varyingExceptions_oneSixteenth_forty :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (n : ℕ), activePCount Nm mu ≤ n + 1 →
        ∀ E : Fin (n + 1) → Finset (Fin n),
          (∀ a, (E a).card ≤ 40) →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight (1 / 16 : ℝ) (E a) a w
            ≤ C ^ (n + 1) :=
  anchoredBidirectional_activeP_sum_le_varyingExceptions
    (1 / 16 : ℝ) (by norm_num) 40

/-- Literal `m = totalMultiplicity mu` specialization of the paper-facing
`1/16`, forty-exception interface. -/
theorem
    anchoredBidirectional_totalMultiplicity_varyingExceptions_oneSixteenth_forty :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let n := totalMultiplicity mu - 1
        ∀ E : Fin (n + 1) → Finset (Fin n),
          (∀ a, (E a).card ≤ 40) →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredBidirectionalActivePWeight (1 / 16 : ℝ) (E a) a w
            ≤ C ^ totalMultiplicity mu :=
  anchoredBidirectional_totalMultiplicity_varyingExceptions
    (1 / 16 : ℝ) (by norm_num) 40

/--
Final paper-facing original-edge interface: exponent `1/16`, the forty-edge
even/odd exception budget, and literal `m = totalMultiplicity mu` length.
-/
theorem
    anchoredOriented_totalMultiplicity_varyingExceptions_oneSixteenth_forty :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let n := totalMultiplicity mu - 1
        ∀ E : Fin (n + 1) → Finset (Fin n),
          (∀ a, (E a).card ≤ 40) →
          ∑ a : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredOrientedActivePWeight (1 / 16 : ℝ) (E a) a w
            ≤ C ^ totalMultiplicity mu :=
  anchoredOriented_totalMultiplicity_varyingExceptions
    (1 / 16 : ℝ) (by norm_num) 40

/-! ## Class-independent positional exception schedule -/

namespace XYCluster

/--
The control data of a located parity block, with every analytic class
payload erased.  This is the information that can influence rough marking
and the exceptional original-edge set.
-/
inductive PositionControlBlock (m : ℕ)
  | single (position : Fin m) (skipped : Bool)
  | pair
      (leftPosition rightPosition : Fin m)
      (skipLeft skipRight : Bool)
  | roughPair
      (leftPosition rightPosition : Fin m)
      (skipLeft skipRight : Bool)
deriving DecidableEq

/-- Attach only the incoming-edge flags to a positional block. -/
def positionBlockToControl {m : ℕ}
    (incomingSkipped : Fin m → Bool) :
    PositionBlock (Fin m) → PositionControlBlock m
  | .single i => .single i (incomingSkipped i)
  | .pair i j =>
      .pair i j (incomingSkipped i) (incomingSkipped j)

/-- Erase the analytic payload of a located block. -/
def LocatedNXParityBlock.positionControl
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    LocatedNXParityBlock (m := m) Nm mu → PositionControlBlock m
  | .single i _ skipped => .single i skipped
  | .pair i j p => .pair i j p.skipLeft p.skipRight
  | .roughPair i j p => .roughPair i j p.skipLeft p.skipRight

@[simp] theorem positionControl_locatePositionBlock
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : Fin m → ActiveNXClass Nm mu)
    (incomingSkipped : Fin m → Bool)
    (b : PositionBlock (Fin m)) :
    (locatePositionBlock Nm mu cls incomingSkipped b).positionControl =
      positionBlockToControl incomingSkipped b := by
  cases b <;> rfl

/-- Purely positional version of “choose the first three eligible pairs”. -/
def markFirstSkippedPositionPairsRough {m : ℕ} :
    ℕ → List (PositionControlBlock m) →
      List (PositionControlBlock m)
  | _, [] => []
  | 0, bs => bs
  | fuel + 1, b :: bs =>
      match b with
      | .single i skipped =>
          .single i skipped ::
            markFirstSkippedPositionPairsRough (fuel + 1) bs
      | .pair i j skipLeft skipRight =>
          if skipLeft || skipRight then
            .roughPair i j skipLeft skipRight ::
              markFirstSkippedPositionPairsRough fuel bs
          else
            .pair i j skipLeft skipRight ::
              markFirstSkippedPositionPairsRough (fuel + 1) bs
      | .roughPair i j skipLeft skipRight =>
          .roughPair i j skipLeft skipRight ::
            markFirstSkippedPositionPairsRough (fuel + 1) bs

/-- Erasing analytic payload commutes with rough marking. -/
@[simp] theorem map_positionControl_markFirstSkippedLocatedPairsRough
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (fuel : ℕ) (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    (markFirstSkippedLocatedPairsRough fuel bs).map
        LocatedNXParityBlock.positionControl =
      markFirstSkippedPositionPairsRough fuel
        (bs.map LocatedNXParityBlock.positionControl) := by
  induction bs generalizing fuel with
  | nil =>
      simp [markFirstSkippedLocatedPairsRough,
        markFirstSkippedPositionPairsRough]
  | cons b bs ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases b with
          | single i a skipped =>
              simp [markFirstSkippedLocatedPairsRough,
                markFirstSkippedPositionPairsRough,
                LocatedNXParityBlock.positionControl, ih]
          | pair i j p =>
              cases hleft : p.skipLeft <;>
                cases hright : p.skipRight <;>
                simp [markFirstSkippedLocatedPairsRough,
                  markFirstSkippedPositionPairsRough,
                  LocatedNXParityBlock.positionControl,
                  nxPairBlockTouchesSkip, hleft, hright, ih]
          | roughPair i j p =>
              simp [markFirstSkippedLocatedPairsRough,
                markFirstSkippedPositionPairsRough,
                LocatedNXParityBlock.positionControl, ih]

/-- Exceptional original edges computed only from positional control data. -/
def positionControlExceptionalEdges {m : ℕ} :
    List (PositionControlBlock m) → Finset (AdjacentIndex m)
  | [] => ∅
  | .single i _ :: bs =>
      (PositionBlock.single i).affectedEdges ∪
        positionControlExceptionalEdges bs
  | .pair _ _ _ _ :: bs =>
      positionControlExceptionalEdges bs
  | .roughPair i j _ _ :: bs =>
      (PositionBlock.pair i j).affectedEdges ∪
        positionControlExceptionalEdges bs

/-- Erasing analytic payload does not alter the exceptional-edge union. -/
theorem positionControlExceptionalEdges_map_positionControl
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    positionControlExceptionalEdges
        (bs.map LocatedNXParityBlock.positionControl) =
      locatedExceptionalEdges bs := by
  induction bs with
  | nil =>
      rfl
  | cons b bs ih =>
      cases b <;>
        simp [LocatedNXParityBlock.positionControl,
          positionControlExceptionalEdges, locatedExceptionalEdges, ih]

/-- The raw anchored schedule with no analytic class payload. -/
def finAnchorPositionControlLedgerWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (O : Finset (AdjacentIndex m)) :
    List (PositionControlBlock m) :=
  (pairPositionRun leftPhase (leftAnchorPositions anchor)).map
      (positionBlockToControl
        (positionIncomingSkipped O .reverse)) ++
    (pairPositionRun rightPhase (rightAnchorPositions anchor)).map
      (positionBlockToControl
        (positionIncomingSkipped O .forward))

theorem map_positionControl_finAnchorNXLocatedParityLedgerWithPhases
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedParityLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O).map
        LocatedNXParityBlock.positionControl =
      finAnchorPositionControlLedgerWithPhases
        leftPhase rightPhase anchor O := by
  simp [finAnchorNXLocatedParityLedgerWithPhases,
    finAnchorPositionControlLedgerWithPhases,
    List.map_map, Function.comp_def]

/-- Pure positional coarse ledger after selecting at most three rough pairs. -/
def finAnchorPositionControlCoarseLedgerWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (O : Finset (AdjacentIndex m)) :
    List (PositionControlBlock m) :=
  markFirstSkippedPositionPairsRough 3
    (finAnchorPositionControlLedgerWithPhases
      leftPhase rightPhase anchor O)

theorem map_positionControl_finAnchorNXLocatedCoarseLedgerWithPhases
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O).map
        LocatedNXParityBlock.positionControl =
      finAnchorPositionControlCoarseLedgerWithPhases
        leftPhase rightPhase anchor O := by
  rw [finAnchorNXLocatedCoarseLedgerWithPhases,
    map_positionControl_markFirstSkippedLocatedPairsRough,
    map_positionControl_finAnchorNXLocatedParityLedgerWithPhases]
  rfl

/--
The concrete original-edge exception set with all analytically irrelevant
class data removed.
-/
def finAnchorPositionalExceptionalEdgesWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (O : Finset (AdjacentIndex m)) :
    Finset (AdjacentIndex m) :=
  finAnchorPureExceptionalEdgesWithPhases
    leftPhase rightPhase anchor O

/--
The scheduled exception set is definitionally controlled only by positions,
phases, and `O`; its apparent `cls` argument carries no information.
-/
theorem finAnchorNXExceptionalEdgesWithPhases_eq_positional
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    finAnchorNXExceptionalEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls O =
      finAnchorPositionalExceptionalEdgesWithPhases
        leftPhase rightPhase anchor O := by
  rfl

/-- Explicit class-independence theorem for downstream finite-Fubini
reindexing. -/
theorem finAnchorNXExceptionalEdgesWithPhases_independent_cls
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls₁ cls₂ : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    finAnchorNXExceptionalEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls₁ O =
      finAnchorNXExceptionalEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls₂ O := by
  rw [finAnchorNXExceptionalEdgesWithPhases_eq_positional,
    finAnchorNXExceptionalEdgesWithPhases_eq_positional]

/-- Positional exception set in the `Fin n` indexing used by the sequence
theorems. -/
def finAnchorPositionalExceptionalFinEdgesWithPhases {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (O : Finset (AdjacentIndex (n + 1))) :
    Finset (Fin n) :=
  reindexAdjacentExceptions
    (finAnchorPositionalExceptionalEdgesWithPhases
      leftPhase rightPhase anchor O)

theorem finAnchorNXExceptionalFinEdgesWithPhases_eq_positional
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    finAnchorNXExceptionalFinEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls O =
      finAnchorPositionalExceptionalFinEdgesWithPhases
        leftPhase rightPhase anchor O := by
  rfl

theorem finAnchorNXExceptionalFinEdgesWithPhases_independent_cls
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls₁ cls₂ : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    finAnchorNXExceptionalFinEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls₁ O =
      finAnchorNXExceptionalFinEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls₂ O := by
  rw [finAnchorNXExceptionalFinEdgesWithPhases_eq_positional,
    finAnchorNXExceptionalFinEdgesWithPhases_eq_positional]

/-- The even/odd union is likewise independent of the analytic class word. -/
theorem finAnchorNXInterpolatedExceptionalFinEdges_independent_cls
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (n + 1))
    (cls₁ cls₂ : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    finAnchorNXInterpolatedExceptionalFinEdges Nm mu
        leftPhase rightPhase anchor cls₁ O =
      finAnchorNXInterpolatedExceptionalFinEdges Nm mu
        leftPhase rightPhase anchor cls₂ O :=
  positionPhase_interpolatedExceptionalFinEdges_independent_cls
    Nm mu leftPhase rightPhase anchor cls₁ cls₂ O

/-- Pure positional even/odd exception union in sequence indexing. -/
def finAnchorPositionalInterpolatedExceptionalFinEdges {n : ℕ}
    (leftPhase rightPhase : Bool)
    (anchor : Fin (n + 1))
    (O : Finset (AdjacentIndex (n + 1))) :
    Finset (Fin n) :=
  finAnchorPositionalExceptionalFinEdgesWithPhases
      leftPhase rightPhase anchor O ∪
    finAnchorPositionalExceptionalFinEdgesWithPhases
      (!leftPhase) (!rightPhase) anchor O

theorem finAnchorNXInterpolatedExceptionalFinEdges_eq_positional
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    finAnchorNXInterpolatedExceptionalFinEdges Nm mu
        leftPhase rightPhase anchor cls O =
      finAnchorPositionalInterpolatedExceptionalFinEdges
        leftPhase rightPhase anchor O := by
  rfl

theorem card_finAnchorPositionalInterpolatedExceptionalFinEdges_le_forty
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (n + 1))
    (_cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    (finAnchorPositionalInterpolatedExceptionalFinEdges
      leftPhase rightPhase anchor O).card ≤ 40 := by
  rw [← finAnchorNXInterpolatedExceptionalFinEdges_eq_positional
    Nm mu leftPhase rightPhase anchor _cls O]
  exact card_finAnchorNXInterpolatedExceptionalFinEdges_le_forty
    Nm mu leftPhase rightPhase anchor _cls O

/--
Concrete final counting interface with the class-independent positional
even/odd exception set, original-edge orientation, exponent `1/16`, and
literal paper length.
-/
theorem
    finAnchorPositional_orientedActiveP_totalMultiplicity_oneSixteenth_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t),
        let n := totalMultiplicity mu - 1
        ∀ (leftPhase rightPhase : Fin (n + 1) → Bool)
          (_cls : Fin (n + 1) → ActiveNXClass Nm mu)
          (O : Finset (AdjacentIndex (n + 1))),
          ∑ anchor : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredOrientedActivePWeight (1 / 16 : ℝ)
                (finAnchorPositionalInterpolatedExceptionalFinEdges
                  (leftPhase anchor) (rightPhase anchor)
                  anchor O)
                anchor w
            ≤ C ^ totalMultiplicity mu := by
  obtain ⟨C, hC, hbound⟩ :=
    anchoredOriented_totalMultiplicity_varyingExceptions_oneSixteenth_forty
  refine ⟨C, hC, ?_⟩
  intro t Nm mu
  dsimp only
  intro leftPhase rightPhase _cls O
  apply hbound Nm mu
    (fun anchor =>
      finAnchorPositionalInterpolatedExceptionalFinEdges
        (leftPhase anchor) (rightPhase anchor)
        anchor O)
  intro anchor
  exact card_finAnchorPositionalInterpolatedExceptionalFinEdges_le_forty
    Nm mu
    (leftPhase anchor) (rightPhase anchor)
    anchor _cls O

end XYCluster

end

end Anderson4D
