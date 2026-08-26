import Anderson4D.HeppTree.Decomposition

/-!
# Uniform scale bounds for realizing Hepp trees

Paper Lemma 5.5 requires the marks of a realizing tree to satisfy
`1 < N_v ≲ M`.  The lower bound is part of `HeppMarking`; this file proves
the uniform upper bound `N_v ≤ 4 M` directly from admissibility in the box
`[-M, M]⁴`, and packages it with the general realizing-tree construction.
-/

namespace Anderson4D

open PlaneTree

private theorem eb_isPos_append_singleton {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) {i : ℕ} (hi : i < childCount t p) :
    IsPos t (p ++ [i]) := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      rw [childCount] at hi
      simpa using (isPos_cons_iff.mpr ⟨hi, isPos_nil _⟩)
  | cons a p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨ha, hp'⟩ := isPos_cons_iff.mp hp
      rw [childCount, dif_pos ha] at hi
      rw [List.cons_append, isPos_cons_iff]
      exact ⟨ha, ih hp' hi⟩

private def eb_childAt {t : PlaneTree} (v : VPos t)
    (i : Fin (childCount t v.1)) : VPos t :=
  ⟨v.1 ++ [i.1], eb_isPos_append_singleton v.2 i.2⟩

private theorem eb_childAt_mem_childrenOf {t : PlaneTree} (v : VPos t)
    (i : Fin (childCount t v.1)) :
    eb_childAt v i ∈ childrenOf v := by
  rw [mem_childrenOf]
  exact ⟨by simp [eb_childAt], List.prefix_append _ _⟩

private theorem eb_childAt_injective {t : PlaneTree} (v : VPos t) :
    Function.Injective (eb_childAt v) := by
  intro i j h
  have hp : v.1 ++ [i.1] = v.1 ++ [j.1] := congrArg Subtype.val h
  have hs : [i.1] = [j.1] := List.append_inj_right hp rfl
  exact Fin.ext (List.singleton_inj.mp hs)

private theorem eb_exists_ne_edge_of_reflTransGen {α : Type*}
    {r : α → α → Prop} {a b : α} (hab : a ≠ b)
    (h : Relation.ReflTransGen r a b) :
    ∃ x y, r x y ∧ x ≠ y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact (hab rfl).elim
  | @head x y hxy hyb ih =>
      by_cases hne : x = y
      · subst y
        exact ih hab
      · exact ⟨x, y, hxy, hne⟩

private theorem eb_child_path {t : PlaneTree} {v c : VPos t}
    (hc : c ∈ childrenOf v) :
    ∃ i : ℕ, c.1 = v.1 ++ [i] := by
  rw [mem_childrenOf] at hc
  let q := c.1.drop v.1.length
  have hq : v.1 ++ q = c.1 := List.prefix_iff_eq_append.mp hc.2
  have hq_len : q.length = 1 := by
    dsimp [q]
    rw [List.length_drop]
    omega
  obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp hq_len
  refine ⟨i, ?_⟩
  rw [← hq, hi]

private theorem eb_leaf_path_below {t : PlaneTree} {v c : VPos t}
    (hc : c ∈ childrenOf v) {l : {w // w ∈ Leaves t}}
    (hl : l ∈ leavesUnder c) :
    ∃ i : ℕ, ∃ q : List ℕ,
      c.1 = v.1 ++ [i] ∧ l.1.1 = v.1 ++ i :: q := by
  obtain ⟨i, hcpath⟩ := eb_child_path hc
  rw [mem_leavesUnder] at hl
  have happ : c.1 ++ l.1.1.drop c.1.length = l.1.1 := by
    simpa using List.prefix_iff_eq_append.mp hl
  refine ⟨i, l.1.1.drop c.1.length, hcpath, ?_⟩
  calc
    l.1.1 = c.1 ++ l.1.1.drop c.1.length := happ.symm
    _ = (v.1 ++ [i]) ++ l.1.1.drop c.1.length := by rw [hcpath]
    _ = v.1 ++ i :: l.1.1.drop c.1.length := by
      simp only [List.append_assoc, List.singleton_append]

private theorem eb_lcaPath_append_cons_ne (p q r : List ℕ) {i j : ℕ}
    (hij : i ≠ j) :
    lcaPath (p ++ i :: q) (p ++ j :: r) = p := by
  induction p with
  | nil => simp [lcaPath, hij]
  | cons a p ih =>
      simp [lcaPath, ih]

private theorem eb_lcaV_eq_of_under_distinct_children {t : PlaneTree}
    {v c c' : VPos t} (hc : c ∈ childrenOf v)
    (hc' : c' ∈ childrenOf v) (hne : c ≠ c')
    {l l' : {w // w ∈ Leaves t}} (hl : l ∈ leavesUnder c)
    (hl' : l' ∈ leavesUnder c') :
    lcaV l.1 l'.1 = v := by
  obtain ⟨i, q, hcpath, hpath⟩ := eb_leaf_path_below hc hl
  obtain ⟨j, r, hcpath', hpath'⟩ := eb_leaf_path_below hc' hl'
  have hij : i ≠ j := by
    intro h
    subst j
    have : c.1 = c'.1 := hcpath.trans hcpath'.symm
    exact hne (Subtype.ext this)
  apply Subtype.ext
  change lcaPath l.1.1 l'.1.1 = v.1
  rw [hpath, hpath', eb_lcaPath_append_cons_ne _ _ _ hij]

private theorem eb_znorm_sub_le_two_mul {M : ℕ} {x y : Fin 4 → ℤ}
    (hx : ∀ i, |x i| ≤ (M : ℤ)) (hy : ∀ i, |y i| ≤ (M : ℤ)) :
    znorm (x - y) ≤ 2 * (M : ℝ) := by
  have hpos : (0 : ℝ) ≤ 2 * (M : ℝ) := by positivity
  rw [znorm, pi_norm_le_iff_of_nonneg hpos]
  intro i
  have hZ : |x i - y i| ≤ (2 * M : ℤ) := by
    have h1 : |x i - y i| ≤ |x i| + |y i| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (x i) (-(y i))
    have h2 := hx i
    have h3 := hy i
    omega
  have hcast : |(x i : ℝ) - (y i : ℝ)| ≤ ((2 * M : ℕ) : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this ⊢
    simpa using this
  calc
    ‖((x - y) i : ℝ)‖ = |(x i : ℝ) - (y i : ℝ)| := by
      rw [Real.norm_eq_abs]
      norm_num [Pi.sub_apply]
    _ ≤ ((2 * M : ℕ) : ℝ) := hcast
    _ = 2 * (M : ℝ) := by norm_num

/-- Every branch scale of an admissible embedding in `[-M,M]⁴` is at most
`4M`.  This is the explicit `N_v ≲ M` part of paper Lemma 5.5.

Choose two children of `v`.  Connectedness supplies a nontrivial link between
two (possibly intermediate) distinct children, hence leaves below those two
children.  Their LCA is `v`; admissible separation gives `N_v / 2` as a lower
bound for their distance, while the box gives the upper bound `2M`. -/
theorem scaleN_le_four_mul_of_isAdmissible {t : PlaneTree}
    {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ}
    (hadm : IsAdmissible Nm M z) {v : VPos t}
    (hv : v ∈ BranchNodes t) :
    (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ) := by
  have hcount : 2 ≤ childCount t v.1 := mem_BranchNodes_iff.mp hv
  let i₀ : Fin (childCount t v.1) := ⟨0, by omega⟩
  let i₁ : Fin (childCount t v.1) := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    dsimp [i₀, i₁] at this
    omega
  let c₀ : VPos t := eb_childAt v i₀
  let c₁ : VPos t := eb_childAt v i₁
  have hc₀ : c₀ ∈ childrenOf v := eb_childAt_mem_childrenOf v i₀
  have hc₁ : c₁ ∈ childrenOf v := eb_childAt_mem_childrenOf v i₁
  have hcne : c₀ ≠ c₁ := (eb_childAt_injective v).ne hi
  have hconn := hadm.linked v hv c₀ hc₀ c₁ hc₁
  obtain ⟨c, c', hcc', hne⟩ :=
    eb_exists_ne_edge_of_reflTransGen hcne hconn
  obtain ⟨hc, hc', l, hl, l', hl', -⟩ := hcc'
  have hlca : lcaV l.1 l'.1 = v :=
    eb_lcaV_eq_of_under_distinct_children hc hc' hne hl hl'
  have hll : l ≠ l' := by
    intro h
    subst l'
    have heq : l.1 = v := by simpa using hlca
    have hbranch := mem_BranchNodes_iff.mp hv
    have hleaf := mem_Leaves_iff.mp l.2
    rw [← heq] at hbranch
    omega
  have hsep := hadm.sep l l' hll
  rw [hlca] at hsep
  have hbox := eb_znorm_sub_le_two_mul (hadm.bounded l) (hadm.bounded l')
  linarith

/-- Paper-facing wrapper around the greedy realizing-tree construction:
besides validity, realization, and the exact leaf count, every branch mark is
bounded by `4M`. -/
theorem rdec_exists_realizing_marked_tree_with_scale
    (M : ℕ) (Z : Finset (Fin 4 → ℤ)) (hZ : Z.Nonempty)
    (hbound : ∀ x ∈ Z, ∀ i, |x i| ≤ (M : ℤ)) :
    ∃ t : PlaneTree, t.isValid = true ∧ ∃ Nm : HeppMarking t,
      Realizes Nm M Z ∧ t.leafCount = Z.card ∧
        ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ) := by
  obtain ⟨t, ht, Nm, hreal, hcard⟩ :=
    rdec_exists_realizing_marked_tree M Z hZ hbound
  obtain ⟨z, hadm, himage⟩ := hreal
  refine ⟨t, ht, Nm, ⟨z, hadm, himage⟩, hcard, ?_⟩
  intro v hv
  exact scaleN_le_four_mul_of_isAdmissible hadm hv

end Anderson4D
