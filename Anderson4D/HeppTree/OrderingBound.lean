import Anderson4D.HeppTree.Basic
import Anderson4D.Combinatorics.TreeCountReal

/-!
# Ordering bound for Hepp trees

This file formalizes paper §5.3, Step 3, equation (5.21), on the real
`Anderson4D.PlaneTree` carrier.  Local permutations of the children at every
vertex are encoded by a target plane tree together with an isomorphism from
the original unordered tree.  For each fixed target the isomorphism set is a
torsor for `Aut(t)`, while the possible valid targets are bounded by
`TreeCountReal.card_validTreesExactly_le`.
-/

namespace Anderson4D

namespace PlaneTree

/-! ## Local ordering choices

The tree/list mutual definitions are structural.  This is important here:
using a nested `Fin cs.length → ...` recursive definition would elaborate by
well-founded recursion and would not reduce while building the finite
instances.
-/

mutual
/-- A permutation at a root together with local choices in its child forest. -/
def LocalOrdering : PlaneTree → Type
  | node cs => Equiv.Perm (Fin cs.length) × LocalOrderingList cs

/-- Local ordering choices for a forest, as a structural dependent product. -/
def LocalOrderingList : List PlaneTree → Type
  | [] => PUnit
  | c :: cs => LocalOrdering c × LocalOrderingList cs
end

mutual
@[reducible] noncomputable def localOrderingFintypeDef :
    ∀ t : PlaneTree, Fintype (LocalOrdering t)
  | node cs => by
      letI : Fintype (LocalOrderingList cs) := localOrderingListFintypeDef cs
      change Fintype (Equiv.Perm (Fin cs.length) × LocalOrderingList cs)
      exact inferInstance

@[reducible] noncomputable def localOrderingListFintypeDef :
    ∀ cs : List PlaneTree, Fintype (LocalOrderingList cs)
  | [] => by
      change Fintype PUnit
      exact inferInstance
  | c :: cs => by
      letI : Fintype (LocalOrdering c) := localOrderingFintypeDef c
      letI : Fintype (LocalOrderingList cs) := localOrderingListFintypeDef cs
      change Fintype (LocalOrdering c × LocalOrderingList cs)
      exact inferInstance
end

noncomputable instance localOrderingFintype (t : PlaneTree) :
    Fintype (LocalOrdering t) :=
  localOrderingFintypeDef t

noncomputable instance localOrderingListFintype (cs : List PlaneTree) :
    Fintype (LocalOrderingList cs) :=
  localOrderingListFintypeDef cs

/-- View structural forest choices as a dependent function over child
indices. -/
def localOrderingListToPi :
    ∀ {cs : List PlaneTree}, LocalOrderingList cs →
      ((i : Fin cs.length) → LocalOrdering (cs.get i))
  | [], _ => fun i => Fin.elim0 i
  | _ :: _, ⟨o, os⟩ => Fin.cases o fun i => localOrderingListToPi os i

/-- Build structural forest choices from a dependent function over indices. -/
def localOrderingListOfPi :
    ∀ {cs : List PlaneTree},
      ((i : Fin cs.length) → LocalOrdering (cs.get i)) →
        LocalOrderingList cs
  | [], _ => PUnit.unit
  | _ :: _, f =>
      ⟨f 0, localOrderingListOfPi fun i => f i.succ⟩

theorem localOrderingListOfPi_toPi :
    ∀ {cs : List PlaneTree} (os : LocalOrderingList cs),
      localOrderingListOfPi (localOrderingListToPi os) = os
  | [], os => by cases os; rfl
  | _ :: _, ⟨o, os⟩ => by
      simp only [localOrderingListToPi, localOrderingListOfPi]
      apply Prod.ext
      · rfl
      · exact localOrderingListOfPi_toPi os

mutual
/-- The recursive product of all child-count factorials. -/
def orderingFactor : PlaneTree → ℕ
  | node cs => cs.length.factorial * orderingFactorList cs

/-- Forest companion of `orderingFactor`. -/
def orderingFactorList : List PlaneTree → ℕ
  | [] => 1
  | c :: cs => orderingFactor c * orderingFactorList cs
end

mutual
/-- The local-ordering type has the expected product-factorial cardinality. -/
theorem card_localOrdering : ∀ t : PlaneTree,
    Fintype.card (LocalOrdering t) = orderingFactor t
  | node cs => by
      change Fintype.card
        (Equiv.Perm (Fin cs.length) × LocalOrderingList cs) =
          cs.length.factorial * orderingFactorList cs
      rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
        card_localOrderingList cs]

theorem card_localOrderingList : ∀ cs : List PlaneTree,
    Fintype.card (LocalOrderingList cs) = orderingFactorList cs
  | [] => by simp [LocalOrderingList, orderingFactorList]
  | c :: cs => by
      change Fintype.card (LocalOrdering c × LocalOrderingList cs) =
        orderingFactor c * orderingFactorList cs
      rw [Fintype.card_prod, card_localOrdering c, card_localOrderingList cs]
end

/-! ## Realizing an ordering as a target plane tree plus an isomorphism -/

/-- Realize all local ordering choices as a plane presentation of the same
unordered rooted tree, retaining the induced isomorphism. -/
noncomputable def realizeLocalOrdering :
    ∀ (t : PlaneTree), LocalOrdering t → Σ s : PlaneTree, Iso t s
  | node cs, ⟨π, Os⟩ => by
      let O : (i : Fin cs.length) → LocalOrdering (cs.get i) :=
        localOrderingListToPi Os
      let child : ∀ i : Fin cs.length, Σ s : PlaneTree, Iso (cs.get i) s :=
        fun i => realizeLocalOrdering (cs.get i) (O i)
      let target : Fin cs.length → PlaneTree := fun i => (child i).1
      let ds : List PlaneTree :=
        List.ofFn fun j : Fin cs.length => target (π.symm j)
      have hlen : ds.length = cs.length := by simp [ds]
      let πd : Fin cs.length ≃ Fin ds.length :=
        π.trans (finCongr hlen.symm)
      have htarget (i : Fin cs.length) :
          (child i).1 = ds.get (πd i) := by
        change target i = ds.get (finCongr hlen.symm (π i))
        have hget :
            ds.get (finCongr hlen.symm (π i)) =
              target (π.symm (π i)) := by
          simp [ds]
        rw [hget, π.symm_apply_apply]
      let F : ∀ i : Fin cs.length, Iso (cs.get i) (ds.get (πd i)) :=
        fun i => Iso.congr rfl (htarget i) (child i).2
      exact ⟨node ds, graft πd F⟩
termination_by t _ => sizeOf t
decreasing_by
  have hmem := List.sizeOf_lt_of_mem (List.get_mem cs i)
  simp only [node.sizeOf_spec]
  omega

/-- Split a target isomorphism back into local ordering choices. -/
noncomputable def decodeLocalOrdering :
    ∀ (t : PlaneTree), (Σ s : PlaneTree, Iso t s) → LocalOrdering t
  | node cs, ⟨node ds, e⟩ => by
      have hlen : cs.length = ds.length :=
        by simpa using Fintype.card_congr (childEquiv e)
      let π : Equiv.Perm (Fin cs.length) :=
        (childEquiv e).trans (finCongr hlen.symm)
      exact ⟨π, localOrderingListOfPi fun i =>
        decodeLocalOrdering (cs.get i)
          ⟨ds.get (childEquiv e i), childIso e i⟩⟩
termination_by t _ => sizeOf t
decreasing_by
  have hmem := List.sizeOf_lt_of_mem (List.get_mem cs i)
  simp only [node.sizeOf_spec]
  omega

private theorem split_graft {cs ds : List PlaneTree}
    (π : Fin cs.length ≃ Fin ds.length)
    (F : ∀ i, Iso (cs.get i) (ds.get (π i))) :
    (⟨childEquiv (graft π F), childIso (graft π F)⟩ :
        Σ σ : Fin cs.length ≃ Fin ds.length,
          ∀ i, Iso (cs.get i) (ds.get (σ i))) =
      ⟨π, F⟩ := by
  apply graft_injective
  exact graft_childEquiv_childIso (graft π F)

private theorem sigmaIso_congr_right {s t u : PlaneTree}
    (e : Iso s t) (h : t = u) :
    (⟨u, Iso.congr rfl h e⟩ : Σ x : PlaneTree, Iso s x) = ⟨t, e⟩ := by
  subst u
  apply Sigma.ext rfl
  rfl

/-- Decoding the target and isomorphism produced by an ordering recovers the
ordering.  Consequently `realizeLocalOrdering` is injective. -/
theorem decode_realizeLocalOrdering :
    ∀ (t : PlaneTree) (o : LocalOrdering t),
      decodeLocalOrdering t (realizeLocalOrdering t o) = o
  | node cs, ⟨π, Os⟩ => by
      let O : (i : Fin cs.length) → LocalOrdering (cs.get i) :=
        localOrderingListToPi Os
      let child : ∀ i : Fin cs.length, Σ s : PlaneTree, Iso (cs.get i) s :=
        fun i => realizeLocalOrdering (cs.get i) (O i)
      let target : Fin cs.length → PlaneTree := fun i => (child i).1
      let ds : List PlaneTree :=
        List.ofFn fun j : Fin cs.length => target (π.symm j)
      have hlen : ds.length = cs.length := by simp [ds]
      let πd : Fin cs.length ≃ Fin ds.length :=
        π.trans (finCongr hlen.symm)
      have htarget (i : Fin cs.length) :
          (child i).1 = ds.get (πd i) := by
        change target i = ds.get (finCongr hlen.symm (π i))
        have hget :
            ds.get (finCongr hlen.symm (π i)) =
              target (π.symm (π i)) := by
          simp [ds]
        rw [hget, π.symm_apply_apply]
      let F : ∀ i : Fin cs.length, Iso (cs.get i) (ds.get (πd i)) :=
        fun i => Iso.congr rfl (htarget i) (child i).2
      let e : Iso (node cs) (node ds) := graft πd F
      have hreal :
          realizeLocalOrdering (node cs) (π, Os) = ⟨node ds, e⟩ := by
        unfold realizeLocalOrdering
        apply Sigma.ext rfl
        rfl
      rw [hreal]
      simp only [decodeLocalOrdering]
      have hs :
          (⟨childEquiv e, childIso e⟩ :
              Σ σ : Fin cs.length ≃ Fin ds.length,
                ∀ i, Iso (cs.get i) (ds.get (σ i))) =
            ⟨πd, F⟩ := by
        simpa [e] using split_graft πd F
      have hπe : childEquiv e = πd := congrArg Sigma.fst hs
      have hpack (i : Fin cs.length) :
          (⟨ds.get (childEquiv e i), childIso e i⟩ :
              Σ s : PlaneTree, Iso (cs.get i) s) =
            child i := by
        have h :=
          congrArg
            (fun x :
                Σ σ : Fin cs.length ≃ Fin ds.length,
                  ∀ j, Iso (cs.get j) (ds.get (σ j)) =>
              (⟨ds.get (x.1 i), x.2 i⟩ :
                Σ s : PlaneTree, Iso (cs.get i) s))
            hs
        exact h.trans (sigmaIso_congr_right (child i).2 (htarget i))
      have hdecodeLen : cs.length = ds.length := by
        simpa using Fintype.card_congr (childEquiv e)
      apply Prod.ext
      · apply Equiv.ext
        intro i
        change
          finCongr hdecodeLen.symm (childEquiv e i) =
            π i
        rw [hπe]
        simp [πd]
      · apply Eq.trans _ (localOrderingListOfPi_toPi Os)
        apply congrArg localOrderingListOfPi
        funext i
        rw [hpack i]
        exact decode_realizeLocalOrdering (cs.get i) (O i)
termination_by t _ => sizeOf t
decreasing_by
  have hmem := List.sizeOf_lt_of_mem (List.get_mem cs i)
  simp only [node.sizeOf_spec]
  omega

theorem realizeLocalOrdering_injective (t : PlaneTree) :
    Function.Injective (realizeLocalOrdering t) :=
  Function.LeftInverse.injective (decode_realizeLocalOrdering t)

/-! ## Isomorphism invariants needed to restrict the target -/

private theorem ordering_isValidList_iff (cs : List PlaneTree) :
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

private theorem ordering_isValid_node_iff {cs : List PlaneTree} :
    (node cs).isValid = true ↔
      cs.length ≠ 1 ∧ ∀ c ∈ cs, c.isValid = true := by
  rw [isValid, Bool.and_eq_true, ordering_isValidList_iff]
  simp [bne_iff_ne]

/-- An unordered-tree isomorphism preserves the number of leaves. -/
theorem leafCount_eq_of_iso :
    ∀ (s t : PlaneTree), Iso s t → s.leafCount = t.leafCount
  | node cs, node ds, e => by
      have hsum : leafCountList cs = leafCountList ds := by
        rw [leafCountList_eq_map, leafCountList_eq_map, map_eq_ofFn,
          map_eq_ofFn, List.sum_ofFn, List.sum_ofFn]
        exact Fintype.sum_equiv (childEquiv e)
          (fun i => leafCount (cs.get i))
          (fun j => leafCount (ds.get j))
          (fun i => leafCount_eq_of_iso _ _ (childIso e i))
      rw [leafCount, leafCount, hsum]
termination_by s _ _ => sizeOf s
decreasing_by
  have hmem := List.sizeOf_lt_of_mem (List.get_mem cs i)
  simp only [node.sizeOf_spec]
  omega

/-- An unordered-tree isomorphism sends a valid Hepp tree to a valid Hepp
tree. -/
theorem isValid_of_iso :
    ∀ (s t : PlaneTree), Iso s t → s.isValid = true → t.isValid = true
  | node cs, node ds, e, hs => by
      rw [ordering_isValid_node_iff] at hs ⊢
      obtain ⟨hlen, hchildren⟩ := hs
      have hcard : cs.length = ds.length := by
        simpa using Fintype.card_congr (childEquiv e)
      constructor
      · omega
      · intro d hd
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp hd
        let i : Fin cs.length := (childEquiv e).symm j
        have hi : cs.get i ∈ cs := List.get_mem cs i
        have hchild :
            (ds.get ((childEquiv e) i)).isValid = true :=
          isValid_of_iso (cs.get i) (ds.get ((childEquiv e) i))
            (childIso e i) (hchildren _ hi)
        rw [← hj]
        simpa [i] using hchild
termination_by s _ _ _ => sizeOf s
decreasing_by
  have hmem := List.sizeOf_lt_of_mem
    (List.get_mem cs ((childEquiv e).symm j))
  simp only [node.sizeOf_spec] at hmem ⊢
  omega

/-! ## Counting the ordering choices by their valid targets -/

/-- A valid plane presentation with the same leaf count as `t`, together
with an unordered-tree isomorphism from `t`. -/
abbrev OrderedIsoTarget (t : PlaneTree) :=
  Σ s : ↥(validTreesExactly t.leafCount), Iso t s.1

noncomputable instance orderedIsoTargetFintype (t : PlaneTree) :
    Fintype (OrderedIsoTarget t) :=
  Fintype.ofFinite _

/-- Restrict the realized ordering to the finite set of valid targets. -/
noncomputable def realizeValidLocalOrdering (t : PlaneTree)
    (ht : t.isValid = true) :
    LocalOrdering t → OrderedIsoTarget t := fun o => by
  let r := realizeLocalOrdering t o
  exact ⟨⟨r.1, mem_validTreesExactly.mpr
    ⟨isValid_of_iso t r.1 r.2 ht, (leafCount_eq_of_iso t r.1 r.2).symm⟩⟩,
    r.2⟩

private def forgetOrderedIsoTarget (t : PlaneTree) :
    OrderedIsoTarget t → Σ s : PlaneTree, Iso t s :=
  fun x => ⟨x.1.1, x.2⟩

theorem realizeValidLocalOrdering_injective (t : PlaneTree)
    (ht : t.isValid = true) :
    Function.Injective (realizeValidLocalOrdering t ht) := by
  intro o₁ o₂ h
  apply realizeLocalOrdering_injective t
  have h' := congrArg (forgetOrderedIsoTarget t) h
  simpa [realizeValidLocalOrdering, forgetOrderedIsoTarget] using h'

private theorem nat_card_iso_le_autCard (t s : PlaneTree) :
    Nat.card (Iso t s) ≤ t.autCard := by
  by_cases h : Nonempty (Iso t s)
  · rw [nat_card_iso_of_nonempty h, Nat.card_congr (isoAutEquiv t),
      Nat.card_eq_fintype_card, card_aut_eq_autCard]
  · haveI : IsEmpty (Iso t s) := not_nonempty_iff.mp h
    rw [Nat.card_eq_zero.mpr (Or.inl inferInstance)]
    exact Nat.zero_le _

/-- Every valid target contributes at most `|Aut(t)|` isomorphisms. -/
theorem card_orderedIsoTarget_le (t : PlaneTree) :
    Fintype.card (OrderedIsoTarget t)
      ≤ (validTreesExactly t.leafCount).card * t.autCard := by
  rw [← Nat.card_eq_fintype_card, Nat.card_sigma]
  calc
    (∑ s : ↥(validTreesExactly t.leafCount), Nat.card (Iso t s.1))
        ≤ ∑ _s : ↥(validTreesExactly t.leafCount), t.autCard :=
      Finset.sum_le_sum fun s _ => nat_card_iso_le_autCard t s.1
    _ = (validTreesExactly t.leafCount).card * t.autCard := by
      simp

/-- Paper (5.21), first in its recursive product-factorial form. -/
theorem orderingFactor_le (t : PlaneTree) (ht : t.isValid = true) :
    orderingFactor t ≤ 4 ^ (4 * t.leafCount) * t.autCard := by
  calc
    orderingFactor t = Fintype.card (LocalOrdering t) :=
      (card_localOrdering t).symm
    _ ≤ Fintype.card (OrderedIsoTarget t) :=
      Fintype.card_le_of_injective (realizeValidLocalOrdering t ht)
        (realizeValidLocalOrdering_injective t ht)
    _ ≤ (validTreesExactly t.leafCount).card * t.autCard :=
      card_orderedIsoTarget_le t
    _ ≤ 4 ^ (4 * t.leafCount) * t.autCard :=
      Nat.mul_le_mul_right t.autCard
        (card_validTreesExactly_le t.leafCount)

/-! ## Identification with the branching-vertex product -/

theorem orderingFactorList_eq_map (cs : List PlaneTree) :
    orderingFactorList cs = (cs.map orderingFactor).prod := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [orderingFactorList, ih, List.map_cons, List.prod_cons]

private theorem prod_orderingFactor_get (cs : List PlaneTree) :
    (∏ i : Fin cs.length, orderingFactor (cs.get i)) =
      orderingFactorList cs := by
  rw [orderingFactorList_eq_map, map_eq_ofFn, List.prod_ofFn]

private theorem ordering_childCount_childV {cs : List PlaneTree}
    (i : Fin cs.length) (v : VPos (cs.get i)) :
    childCount (node cs) (childV i v).1 =
      childCount (cs.get i) v.1 := by
  rw [childV_val]
  simp [childCount, i.2, List.get_eq_getElem]

/-- The recursive ordering factor is the product of the factorial of the
child count over all vertices. -/
theorem prod_childCount_factorial_eq_orderingFactor :
    ∀ t : PlaneTree,
      (∏ v : VPos t, (childCount t v.1).factorial) = orderingFactor t
  | node cs => by
      let f : VPos (node cs) → ℕ :=
        fun v => (childCount (node cs) v.1).factorial
      let g : Option ((i : Fin cs.length) × VPos (cs.get i)) → ℕ
        | none => cs.length.factorial
        | some ⟨i, v⟩ => (childCount (cs.get i) v.1).factorial
      have hfg (v : VPos (node cs)) :
          f v = g (vposNodeEquiv cs v) := by
        rcases vpos_node_cases_or v with rfl | ⟨i, w, rfl⟩
        · rfl
        · simpa [f, g] using
            congrArg Nat.factorial (ordering_childCount_childV i w)
      change (∏ v : VPos (node cs), f v) =
        cs.length.factorial * orderingFactorList cs
      rw [Fintype.prod_equiv (vposNodeEquiv cs) f g hfg,
        Fintype.prod_option]
      change cs.length.factorial *
          (∏ x : (i : Fin cs.length) × VPos (cs.get i),
            (childCount (cs.get x.1) x.2.1).factorial) =
        cs.length.factorial * orderingFactorList cs
      rw [Fintype.prod_sigma]
      congr 1
      calc
        (∏ i : Fin cs.length, ∏ v : VPos (cs.get i),
            (childCount (cs.get i) v.1).factorial) =
            ∏ i : Fin cs.length, orderingFactor (cs.get i) := by
              apply Finset.prod_congr rfl
              intro i _
              exact prod_childCount_factorial_eq_orderingFactor (cs.get i)
        _ = orderingFactorList cs := prod_orderingFactor_get cs
termination_by t => sizeOf t
decreasing_by
  have hmem := List.sizeOf_lt_of_mem (List.get_mem cs i)
  simp only [node.sizeOf_spec]
  omega

/-- Vertices outside `BranchNodes` have zero or one child, hence contribute
factorial one. -/
theorem prod_branchNodes_factorial_eq_orderingFactor (t : PlaneTree) :
    (∏ v ∈ BranchNodes t, (childCount t v.1).factorial) =
      orderingFactor t := by
  rw [← prod_childCount_factorial_eq_orderingFactor t]
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro v _ hv
  have hlt : childCount t v.1 < 2 := by
    simpa [BranchNodes] using hv
  have hc : childCount t v.1 = 0 ∨ childCount t v.1 = 1 := by
    omega
  rcases hc with hc | hc <;> simp [hc]

/-- Paper §5.3 Step 3, equation (5.21), on the real `PlaneTree` carrier. -/
theorem prod_branchNodes_factorial_le (t : PlaneTree)
    (ht : t.isValid = true) :
    (∏ v ∈ BranchNodes t, (childCount t v.1).factorial)
      ≤ 4 ^ (4 * t.leafCount) * t.autCard := by
  rw [prod_branchNodes_factorial_eq_orderingFactor]
  exact orderingFactor_le t ht

end PlaneTree

end Anderson4D
