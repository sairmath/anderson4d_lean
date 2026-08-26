import Anderson4D.Continuum.PrimitiveEndpointAssembly

/-!
# Extremal endpoint assembly for the primitive lattice estimate

When the non-root branch count is `n - 2`, validity and total multiplicity
force exactly `n` leaves, each of multiplicity two.  A primitive compatible
word then has distinct first and last leaves.  This makes the endpoint
constraint in `primitiveEndpointMarkingRatioSum` available and closes the
extremal logarithmic marking sum, including the finite sum over endpoint
leaf pairs.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

private theorem endpointSizeLtOfMem
    {c : PlaneTree} {cs : List PlaneTree}
    (hc : c ∈ cs) : c.size < (PlaneTree.node cs).size := by
  have h₁ : c.size ∈ cs.map PlaneTree.size :=
    List.mem_map.mpr ⟨c, hc, rfl⟩
  have h₂ : c.size ≤ (cs.map PlaneTree.size).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ h₁
  have h₃ :
      (PlaneTree.node cs).size =
        1 + PlaneTree.sizeList cs := rfl
  rw [h₃, PlaneTree.sizeList_eq_map]
  omega

private theorem endpointPlaneTreeInduction
    {motive : PlaneTree → Prop}
    (ind : ∀ cs : List PlaneTree,
      (∀ c ∈ cs, motive c) → motive (PlaneTree.node cs)) :
    ∀ t, motive t
  | PlaneTree.node cs =>
      ind cs fun c _hc =>
        endpointPlaneTreeInduction ind c
termination_by t => t.size
decreasing_by exact endpointSizeLtOfMem _hc

theorem endpointLcaV_mem_branchNodes_of_ne :
    ∀ {t : PlaneTree} (l l' : HeppLeaf t),
      l ≠ l' → lcaV l.1 l'.1 ∈ BranchNodes t := by
  intro t
  induction t using endpointPlaneTreeInduction with
  | ind cs ih =>
      intro l l' hne
      by_cases hlen : 1 ≤ cs.length
      · obtain ⟨i, li, rfl⟩ :=
          rdec_leafUp_surj hlen l
        obtain ⟨j, lj, rfl⟩ :=
          rdec_leafUp_surj hlen l'
        by_cases hij : i = j
        · subst j
          have hli : li ≠ lj := by
            intro h
            apply hne
            subst lj
            rfl
          change
            lcaV (childV i li.1) (childV i lj.1) ∈
              BranchNodes (PlaneTree.node cs)
          rw [rdec_lcaV_childV]
          exact (rdec_childV_mem_branchNodes i _).mpr
            (ih (cs.get i) (List.get_mem cs i)
              li lj hli)
        · change
            lcaV (childV i li.1) (childV j lj.1) ∈
              BranchNodes (PlaneTree.node cs)
          rw [rdec_lcaV_childV_ne hij]
          apply rdec_root_mem_branchNodes
          omega
      · have hzero : cs.length = 0 := by omega
        have hcs : cs = [] :=
          List.eq_nil_of_length_eq_zero hzero
        subst cs
        exact absurd
          (Subtype.ext
            ((vpos_leaf_eq l.1).trans
              (vpos_leaf_eq l'.1).symm))
          hne

theorem endpointExtremal_leafCount_eq
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (n : ℕ)
    (htotal : totalMultiplicity mu = 2 * n)
    (hbranchCard : (nonrootBranches t).card = n - 2) :
    t.leafCount = n := by
  have hnonroot :
      (nonrootBranches t).card + 1 =
        (BranchNodes t).card := by
    simpa [nonrootBranches] using
      Finset.card_erase_add_one hroot
  have hbranch :
      (BranchNodes t).card ≤ t.leafCount - 1 := by
    calc
      (BranchNodes t).card ≤ branchExcess t := by
        rw [← sum_branchNodes_childCount_sub_one_eq_branchExcess,
          Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum fun v hv => by
          have htwo : 2 ≤ childCount t v.1 := by
            simpa [BranchNodes] using hv
          omega
      _ = t.leafCount - 1 :=
        branchExcess_eq_leafCount_sub_one t ht
  have hleaf :
      2 * t.leafCount ≤ totalMultiplicity mu := by
    rw [totalMultiplicity]
    calc
      2 * t.leafCount =
          ∑ _l : HeppLeaf t, 2 := by
        simp [card_Leaves_eq_leafCount, Nat.mul_comm]
      _ ≤ ∑ l : HeppLeaf t, leafMultiplicity mu l :=
        Finset.sum_le_sum fun l _ => mu.two_le l.1 l.2
  omega

theorem endpointExtremal_leafMultiplicity_eq_two
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (n : ℕ)
    (htotal : totalMultiplicity mu = 2 * n)
    (hbranchCard : (nonrootBranches t).card = n - 2)
    (l : HeppLeaf t) :
    leafMultiplicity mu l = 2 := by
  have hleafCount :
      t.leafCount = n :=
    endpointExtremal_leafCount_eq ht hroot mu n htotal hbranchCard
  have hn : 2 ≤ n := by
    rw [← hleafCount]
    exact two_le_leafCount_of_root_mem_BranchNodes t hroot
  have hcardErase :
      ((Finset.univ : Finset (HeppLeaf t)).erase l).card =
        n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ l),
      Finset.card_univ, Fintype.card_coe,
      card_Leaves_eq_leafCount, hleafCount]
  have hdecomp :
      leafMultiplicity mu l +
          ∑ x ∈ (Finset.univ : Finset (HeppLeaf t)).erase l,
            leafMultiplicity mu x =
        2 * n := by
    rw [← htotal, totalMultiplicity,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
  have hother :
      2 * (n - 1) ≤
        ∑ x ∈ (Finset.univ : Finset (HeppLeaf t)).erase l,
          leafMultiplicity mu x := by
    calc
      2 * (n - 1) =
          ∑ _x ∈
            (Finset.univ : Finset (HeppLeaf t)).erase l,
            2 := by
        simp [card_Leaves_eq_leafCount,
          hleafCount, Nat.mul_comm]
      _ ≤
          ∑ x ∈
              (Finset.univ : Finset (HeppLeaf t)).erase l,
            leafMultiplicity mu x := by
        exact Finset.sum_le_sum fun x _ => mu.two_le x.1 x.2
  have hcombined :
      leafMultiplicity mu l + 2 * (n - 1) ≤ 2 * n := by
    calc
      leafMultiplicity mu l + 2 * (n - 1) ≤
          leafMultiplicity mu l +
            ∑ x ∈
                (Finset.univ : Finset (HeppLeaf t)).erase l,
              leafMultiplicity mu x :=
        Nat.add_le_add_left hother _
      _ = 2 * n := hdecomp
  have htwo := mu.two_le l.1 l.2
  change mu.m l.1 + 2 * (n - 1) ≤ 2 * n at hcombined
  change 2 ≤ mu.m l.1 at htwo
  change mu.m l.1 = 2
  omega

theorem noProperLeafBlock_endpoint_ne
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin (2 * n) → α)
    (hfiber :
      ∀ a,
        (Finset.univ.filter fun j => w j = a).card = 2)
    (hprimitive : NoProperLeafBlock w) :
    w (primitiveEndpointLeft n (by omega)) ≠
      w (primitiveEndpointRight n (by omega)) := by
  classical
  let i₀ : Fin (2 * n) :=
    primitiveEndpointLeft n (by omega)
  let i₁ : Fin (2 * n) :=
    primitiveEndpointRight n (by omega)
  let a : Fin (2 * n) := ⟨1, by omega⟩
  let b : Fin (2 * n) := ⟨2 * n - 2, by omega⟩
  intro heq
  let l : α := w i₀
  let fiber : Finset (Fin (2 * n)) :=
    Finset.univ.filter fun j => w j = l
  have hi₀ : i₀ ∈ fiber := by
    simp [fiber, l]
  have hi₁ : i₁ ∈ fiber := by
    simp only [fiber, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa [l, i₀, i₁] using heq.symm
  have hi_ne : i₀ ≠ i₁ := by
    intro h
    have hv := congrArg Fin.val h
    simp [i₀, i₁, primitiveEndpointLeft,
      primitiveEndpointRight] at hv
    omega
  have hpairSubset :
      ({i₀, i₁} : Finset (Fin (2 * n))) ⊆ fiber := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact hi₀
    · exact hi₁
  have hfiberCard : fiber.card = 2 := by
    simpa [fiber] using hfiber l
  have hpairCard :
      ({i₀, i₁} : Finset (Fin (2 * n))).card = 2 := by
    simp [hi_ne]
  have hfiberEq :
      fiber = ({i₀, i₁} : Finset (Fin (2 * n))) := by
    symm
    exact Finset.eq_of_subset_of_card_le hpairSubset
      (by omega)
  have hw_eq_iff (j : Fin (2 * n)) :
      w j = l ↔ j = i₀ ∨ j = i₁ := by
    have hj := Finset.ext_iff.mp hfiberEq j
    simpa [fiber] using hj
  let S : Finset α := Finset.univ.erase l
  have hS_nonempty : S.Nonempty := by
    refine ⟨w a, ?_⟩
    simp only [S, Finset.mem_erase, Finset.mem_univ,
      and_true]
    intro hwa
    have ha_cases := (hw_eq_iff a).mp hwa
    rcases ha_cases with ha | ha
    · have hv := congrArg Fin.val ha
      simp [a, i₀, primitiveEndpointLeft] at hv
    · have hv := congrArg Fin.val ha
      simp [a, i₁, primitiveEndpointRight] at hv
      omega
  have hS_proper : S ⊂ (Finset.univ : Finset α) := by
    exact Finset.erase_ssubset (Finset.mem_univ l)
  have hpositions :
      letterPositions w S = Finset.Icc a b := by
    ext j
    simp only [mem_letterPositions, S, Finset.mem_erase,
      Finset.mem_univ, and_true, Finset.mem_Icc]
    constructor
    · intro hj
      have hnot :
          ¬(j = i₀ ∨ j = i₁) := by
        intro hcases
        exact hj ((hw_eq_iff j).mpr hcases)
      push Not at hnot
      have hj0 : j.val ≠ 0 := by
        intro hjv
        apply hnot.1
        apply Fin.ext
        simpa [i₀, primitiveEndpointLeft] using hjv
      have hjlast : j.val ≠ 2 * n - 1 := by
        intro hjv
        apply hnot.2
        apply Fin.ext
        simpa [i₁, primitiveEndpointRight] using hjv
      change 1 ≤ j.val ∧ j.val ≤ 2 * n - 2
      omega
    · intro hj
      change 1 ≤ j.val ∧ j.val ≤ 2 * n - 2 at hj
      intro hwjl
      have hcases := (hw_eq_iff j).mp hwjl
      rcases hcases with hj0 | hj1
      · have hv := congrArg Fin.val hj0
        simp [i₀, primitiveEndpointLeft] at hv
        omega
      · have hv := congrArg Fin.val hj1
        simp [i₁, primitiveEndpointRight] at hv
        omega
  have hwhole :
      Finset.Icc a b =
        (Finset.univ : Finset (Fin (2 * n))) := by
    apply hprimitive S hS_nonempty hS_proper a b
    · change 1 ≤ 2 * n - 2
      omega
    · exact hpositions
  have hi₀mem : i₀ ∈ Finset.Icc a b := by
    rw [hwhole]
    exact Finset.mem_univ i₀
  simp [Finset.mem_Icc, i₀, a, primitiveEndpointLeft] at hi₀mem

theorem activeExtremalEndpointLeaves
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (hbranchCard : (nonrootBranches t).card = n - 2)
    (d : PrimitiveActiveEndpointData
      t M n hn Y A x₀ x₁) :
    ∃ (f₀ f₁ : HeppLeaf t) (z : HeppLeaf t → Z4),
      IsAdmissible (pairedMarking d.1) M z ∧
        z f₀ = x₀ ∧ z f₁ = x₁ ∧ f₀ ≠ f₁ := by
  classical
  have hn2 : 2 ≤ n := by
    have hleafCount :
        t.leafCount = n :=
      endpointExtremal_leafCount_eq ht hroot
        (pairedMultiplicities d.1) n
        (RealizationData.toMultiplicities_total
          d.1.1 d.1.2.1)
        hbranchCard
    rw [← hleafCount]
    exact two_le_leafCount_of_root_mem_BranchNodes t hroot
  obtain ⟨z, w, hadm, hw, hy⟩ :=
    primitiveActiveEndpointWitness_realizes d
  obtain ⟨κ, hκmem⟩ :=
    primitiveActiveEndpointWitness_pairing_nonempty d
  have hκdata :=
    mem_primitiveCompatibleAcrossPairings.mp hκmem
  have hwrespects : RespectsWord A w κ := by
    intro j
    apply hadm.inj
    rw [← hy j.1, ← hy (κ j).1]
    exact hκdata.1 j
  have hnoblock : NoProperLeafBlock w :=
    noProperLeafBlock_of_primitive_across
      hκdata.2 hwrespects
  have hwfiber :
      ∀ l : HeppLeaf t,
        (Finset.univ.filter fun j => w j = l).card = 2 := by
    intro l
    have hcount :=
      (Finset.mem_filter.mp hw).2 l
    change
      (Finset.univ.filter fun j => w j = l).card =
        leafMultiplicity (pairedMultiplicities d.1) l
      at hcount
    rw [endpointExtremal_leafMultiplicity_eq_two
      ht hroot (pairedMultiplicities d.1) n
      (RealizationData.toMultiplicities_total
        d.1.1 d.1.2.1)
      hbranchCard l] at hcount
    exact hcount
  have hendpointNe :
      w (primitiveEndpointLeft n (by omega)) ≠
        w (primitiveEndpointRight n (by omega)) :=
    noProperLeafBlock_endpoint_ne
      hn2 w hwfiber hnoblock
  have hymem :=
    mem_primitiveTuplesAtEndpoints.mp
      (primitiveActiveEndpointWitness_mem d)
  refine
    ⟨w (primitiveEndpointLeft n (by omega)),
      w (primitiveEndpointRight n (by omega)), z,
      hadm, ?_, ?_, hendpointNe⟩
  · calc
      z (w (primitiveEndpointLeft n (by omega))) =
          primitiveActiveEndpointWitness d
            (primitiveEndpointLeft n (by omega)) :=
        (hy _).symm
      _ = x₀ := hymem.2.1
  · calc
      z (w (primitiveEndpointRight n (by omega))) =
          primitiveActiveEndpointWitness d
            (primitiveEndpointRight n (by omega)) :=
        (hy _).symm
      _ = x₁ := hymem.2.2

theorem activeExtremalLogMarking_eq
    {t : PlaneTree} (ht : t.isValid = true)
    {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (d : PrimitiveActiveEndpointData
      t M n hn Y A x₀ x₁) :
    ((primitiveActiveEndpointBranchData ht d).1.toHeppMarking
        (primitiveActiveEndpointBranchData ht d).2) =
      pairedMarking d.1 := by
  have hNexp :
      ((primitiveActiveEndpointBranchData ht d).1.toHeppMarking
          (primitiveActiveEndpointBranchData ht d).2).Nexp =
        (pairedMarking d.1).Nexp := by
    funext v
    by_cases hv : v ∈ BranchNodes t
    · simp [primitiveActiveEndpointBranchData,
        logBranchDataOfScaleBound,
        BranchExponentData.toHeppMarking,
        BranchExponentData.ofHeppMarking,
        BranchExponentData.raw, hv]
    · simp [primitiveActiveEndpointBranchData,
        logBranchDataOfScaleBound,
        BranchExponentData.toHeppMarking,
        BranchExponentData.raw, pairedMarking,
        RealizationData.toHeppMarking, hv]
  have heq_of_Nexp_eq :
      ∀ {Nm Nm' : HeppMarking t},
        Nm.Nexp = Nm'.Nexp → Nm = Nm' := by
    intro Nm Nm' h
    cases Nm with
    | mk Nexp pos parent_gt =>
        cases Nm' with
        | mk Nexp' pos' parent_gt' =>
            simpa only [HeppMarking.mk.injEq] using h
  exact heq_of_Nexp_eq hNexp

noncomputable def activeExtremalEndpointChoice
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (hbranchCard : (nonrootBranches t).card = n - 2)
    (d : PrimitiveActiveEndpointData
      t M n hn Y A x₀ x₁) :
    Σ f₀ : HeppLeaf t, Σ f₁ : HeppLeaf t,
      {z : HeppLeaf t → Z4 //
        IsAdmissible (pairedMarking d.1) M z ∧
          z f₀ = x₀ ∧ z f₁ = x₁ ∧ f₀ ≠ f₁} := by
  let hex :=
    activeExtremalEndpointLeaves
      ht hroot hbranchCard d
  let f₀ := Classical.choose hex
  let hex₁ := Classical.choose_spec hex
  let f₁ := Classical.choose hex₁
  let hex₂ := Classical.choose_spec hex₁
  let z := Classical.choose hex₂
  exact ⟨f₀, f₁, z, Classical.choose_spec hex₂⟩

abbrev ActiveExtremalEndpointCodeTarget
    (t : PlaneTree) (M : ℕ) (x₀ x₁ : Z4) :=
  Σ p : {p : HeppLeaf t × HeppLeaf t // p.1 ≠ p.2},
    EndpointValidBranchExponentData t
      (Nat.log 2 (4 * M)) M p.1.1 p.1.2 x₀ x₁

noncomputable def activeExtremalEndpointCode
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (hbranchCard : (nonrootBranches t).card = n - 2)
    (d : PrimitiveActiveEndpointData
      t M n hn Y A x₀ x₁) :
    ActiveExtremalEndpointCodeTarget t M x₀ x₁ := by
  let c :=
    activeExtremalEndpointChoice
      ht hroot hbranchCard d
  let f₀ : HeppLeaf t := c.1
  let f₁ : HeppLeaf t := c.2.1
  let z : HeppLeaf t → Z4 := c.2.2.1
  have hadm :
      IsAdmissible
        ((primitiveActiveEndpointBranchData ht d).1.toHeppMarking
          (primitiveActiveEndpointBranchData ht d).2)
        M z := by
    rw [activeExtremalLogMarking_eq ht d]
    exact c.2.2.2.1
  exact
    ⟨⟨(f₀, f₁), c.2.2.2.2.2.2⟩,
      ⟨primitiveActiveEndpointBranchData ht d,
        z, hadm, c.2.2.2.2.1, c.2.2.2.2.2.1⟩⟩

theorem activeExtremalEndpointCode_injective
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (hbranchCard : (nonrootBranches t).card = n - 2) :
    Function.Injective
      (activeExtremalEndpointCode
        ht hroot (M := M) (n := n) (hn := hn)
        (Y := Y) (A := A) (x₀ := x₀) (x₁ := x₁)
        hbranchCard) := by
  intro d d' hcode
  have hbranch :
      primitiveActiveEndpointBranchData ht d =
        primitiveActiveEndpointBranchData ht d' := by
    exact congrArg
      (fun q : ActiveExtremalEndpointCodeTarget
          t M x₀ x₁ => q.2.1)
      hcode
  have hhalf :
      pairedLeafHalfAssignment d.1 =
        pairedLeafHalfAssignment d'.1 := by
    apply Subtype.ext
    funext l
    apply Fin.ext
    have hd :=
      endpointExtremal_leafMultiplicity_eq_two
        ht hroot (pairedMultiplicities d.1) n
        (RealizationData.toMultiplicities_total
          d.1.1 d.1.2.1)
        hbranchCard l
    have hd' :=
      endpointExtremal_leafMultiplicity_eq_two
        ht hroot (pairedMultiplicities d'.1) n
        (RealizationData.toMultiplicities_total
          d'.1.1 d'.1.2.1)
        hbranchCard l
    change d.1.1.2.raw l.1 = 2 at hd
    change d'.1.1.2.raw l.1 = 2 at hd'
    rw [LeafMultiplicityData.raw_apply_of_mem
      d.1.1.2 l.2] at hd
    rw [LeafMultiplicityData.raw_apply_of_mem
      d'.1.1.2 l.2] at hd'
    change (d.1.1.2 l).1 / 2 =
      (d'.1.1.2 l).1 / 2
    rw [hd, hd']
  apply primitiveActiveEndpointCode_injective ht
  exact Prod.ext hbranch hhalf

theorem sum_activeExtremal_le_endpointMarkingSums
    {C : ℝ} (hC : 0 ≤ C)
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (hbranchCard : (nonrootBranches t).card = n - 2) :
    (∑ d : PrimitiveActiveEndpointData
        t M n hn Y A x₀ x₁,
        primitiveRatioRHS C n t (pairedMarking d.1)) ≤
      ∑ p : {p : HeppLeaf t × HeppLeaf t // p.1 ≠ p.2},
        primitiveEndpointMarkingRatioSum
          C n M t p.1.1 p.1.2 x₀ x₁ := by
  classical
  let code :
      PrimitiveActiveEndpointData t M n hn Y A x₀ x₁ →
        ActiveExtremalEndpointCodeTarget t M x₀ x₁ :=
    activeExtremalEndpointCode
      ht hroot hbranchCard
  let F :
      ActiveExtremalEndpointCodeTarget t M x₀ x₁ → ℝ :=
    fun q =>
      primitiveRatioRHS C n t
        (q.2.1.1.toHeppMarking q.2.1.2)
  have hcode : Function.Injective code :=
    activeExtremalEndpointCode_injective
      ht hroot hbranchCard
  have hF : ∀ q, 0 ≤ F q := by
    intro q
    exact primitiveRatioRHS_nonneg hC n t
      (q.2.1.1.toHeppMarking q.2.1.2)
  calc
    (∑ d : PrimitiveActiveEndpointData
        t M n hn Y A x₀ x₁,
        primitiveRatioRHS C n t (pairedMarking d.1)) =
      ∑ d : PrimitiveActiveEndpointData
          t M n hn Y A x₀ x₁, F (code d) := by
        apply Fintype.sum_congr
        intro d
        simpa [F, code, activeExtremalEndpointCode] using
          primitiveRatioRHS_activeBranchData ht d C
    _ =
      ∑ q ∈
          (Finset.univ :
            Finset (PrimitiveActiveEndpointData
              t M n hn Y A x₀ x₁)).image code,
        F q := by
      symm
      exact Finset.sum_image hcode.injOn
    _ ≤
      ∑ q : ActiveExtremalEndpointCodeTarget
          t M x₀ x₁, F q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _)
      intro q hq hnot
      exact hF q
    _ =
      ∑ p : {p : HeppLeaf t × HeppLeaf t // p.1 ≠ p.2},
        primitiveEndpointMarkingRatioSum
          C n M t p.1.1 p.1.2 x₀ x₁ := by
      rw [Fintype.sum_sigma]
      rfl

theorem sum_endpointMarkingSums_le_final
    {C : ℝ} (hC : 0 ≤ C)
    {n M K : ℕ} {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (hn : 2 ≤ n)
    (htotal : totalMultiplicity mu = 2 * n)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (hbranchCard : (nonrootBranches t).card = n - 2)
    (x₀ x₁ : Z4) :
    (∑ p : {p : HeppLeaf t × HeppLeaf t // p.1 ≠ p.2},
        primitiveEndpointMarkingRatioSum
          C n M t p.1.1 p.1.2 x₀ x₁) ≤
      ((n * n : ℕ) : ℝ) *
        ((256 * C * (K + 1)) ^ n *
          (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
            (n - 2))) := by
  classical
  let B : ℝ :=
    (256 * C * (K + 1)) ^ n *
      (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
        (n - 2))
  have hterm :
      ∀ p : {p : HeppLeaf t × HeppLeaf t //
          p.1 ≠ p.2},
        primitiveEndpointMarkingRatioSum
            C n M t p.1.1 p.1.2 x₀ x₁ ≤ B := by
    intro p
    let anchor :
        {v // v ∈ BranchNodes t} :=
      ⟨lcaV p.1.1.1 p.1.2.1,
        endpointLcaV_mem_branchNodes_of_ne
          p.1.1 p.1.2 p.2⟩
    exact
      primitiveEndpointMarkingRatioSum_le_final_of_card_eq
        hC ht hroot mu hn htotal hnL hbranchCard
        anchor p.1.1 p.1.2 p.2 rfl x₀ x₁
  have hleaf :
      t.leafCount ≤ n := by
    have htwo :
        2 * t.leafCount ≤ totalMultiplicity mu := by
      rw [totalMultiplicity]
      calc
        2 * t.leafCount =
            ∑ _l : HeppLeaf t, 2 := by
          simp [card_Leaves_eq_leafCount, Nat.mul_comm]
        _ ≤ ∑ l : HeppLeaf t,
              leafMultiplicity mu l :=
          Finset.sum_le_sum fun l _ =>
            mu.two_le l.1 l.2
    omega
  have hcard :
      Fintype.card
          {p : HeppLeaf t × HeppLeaf t // p.1 ≠ p.2} ≤
        n * n := by
    calc
      Fintype.card
          {p : HeppLeaf t × HeppLeaf t // p.1 ≠ p.2} ≤
          Fintype.card (HeppLeaf t × HeppLeaf t) :=
        Fintype.card_le_of_injective
          Subtype.val Subtype.val_injective
      _ = t.leafCount * t.leafCount := by
        simp [Fintype.card_coe, card_Leaves_eq_leafCount]
      _ ≤ n * n := Nat.mul_le_mul hleaf hleaf
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  calc
    (∑ p : {p : HeppLeaf t × HeppLeaf t //
        p.1 ≠ p.2},
        primitiveEndpointMarkingRatioSum
          C n M t p.1.1 p.1.2 x₀ x₁) ≤
      ∑ _p : {p : HeppLeaf t × HeppLeaf t //
          p.1 ≠ p.2}, B := by
        apply Finset.sum_le_sum
        intro p hp
        exact hterm p
    _ =
      (Fintype.card
        {p : HeppLeaf t × HeppLeaf t //
          p.1 ≠ p.2} : ℝ) * B := by
        simp
    _ ≤ ((n * n : ℕ) : ℝ) * B := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcard) hB
    _ =
      ((n * n : ℕ) : ℝ) *
        ((256 * C * (K + 1)) ^ n *
          (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
            (n - 2))) := rfl

theorem sum_activeExtremal_le_final
    {C : ℝ} (hC : 0 ≤ C)
    {n M K : ℕ} {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (hn : 2 ≤ n)
    (htotal : totalMultiplicity mu = 2 * n)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (hbranchCard : (nonrootBranches t).card = n - 2)
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4} :
    (∑ d : PrimitiveActiveEndpointData
        t M n (by omega) Y A x₀ x₁,
        primitiveRatioRHS C n t (pairedMarking d.1)) ≤
      ((n * n : ℕ) : ℝ) *
        ((256 * C * (K + 1)) ^ n *
          (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
            (n - 2))) := by
  exact
    (sum_activeExtremal_le_endpointMarkingSums
      hC ht hroot hbranchCard).trans
      (sum_endpointMarkingSums_le_final
        hC ht hroot mu hn htotal hnL hbranchCard x₀ x₁)

end

end Anderson4D
