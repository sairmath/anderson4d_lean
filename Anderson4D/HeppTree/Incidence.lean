import Anderson4D.HeppTree.RealizationData
import Anderson4D.HeppTree.PairedExistence
import Anderson4D.HeppTree.Decomposition

/-!
# Concrete incidence data for the fixed-tree form of (5.6)

The denominator in paper (5.6) counts only the finite pair consisting of
branch exponents and leaf multiplicities.  In particular, neither an
admissible embedding nor a word witnessing a realization is part of the
finite carrier below.  Its multiplicities are arbitrary values at least two;
the evenness supplied later by an across-pairing is not part of this count.
-/

namespace Anderson4D

open PlaneTree

/-- Valid restricted realization data for a fixed tree and tuple length.
Embedding and word witnesses deliberately remain in the incidence relation,
not in this finite type. -/
abbrev ValidRealizationData (t : PlaneTree) (M m : ℕ) :=
  {d : RealizationData t M m // d.IsValid}

/-- The finite carrier of all valid restricted realization data. -/
def validRealizationDataFinset (t : PlaneTree) (M m : ℕ) :
    Finset (ValidRealizationData t M m) :=
  Finset.univ

/-- Incidence of restricted data with a tuple, via the canonical marking and
multiplicity bundles determined by the validity proof. -/
def ValidRealizationData.Realizes {t : PlaneTree} {M m : ℕ}
    (d : ValidRealizationData t M m) (y : Fin m → Fin 4 → ℤ) : Prop :=
  RealizesTuple t (d.1.toHeppMarking d.2) (d.1.toMultiplicities d.2) M y

noncomputable instance validRealizationDataDecidableRel
    (t : PlaneTree) (M m : ℕ) :
    DecidableRel
      (fun (d : ValidRealizationData t M m) (y : Fin m → Fin 4 → ℤ) =>
        d.Realizes y) :=
  fun _ _ => Classical.propDecidable _

/-- The restricted data incident to `y` for a fixed tree. -/
noncomputable def treeRealizationFiber (t : PlaneTree) (M m : ℕ)
    (y : Fin m → Fin 4 → ℤ) : Finset (ValidRealizationData t M m) :=
  (validRealizationDataFinset t M m).filter fun d => d.Realizes y

/-- The concrete fixed-tree symmetry denominator in (5.6). -/
noncomputable def treeSymDenom (t : PlaneTree) (M m : ℕ)
    (y : Fin m → Fin 4 → ℤ) : ℕ :=
  (treeRealizationFiber t M m y).card

theorem treeRealizationFiber_eq_realizationFiber
    (t : PlaneTree) (M m : ℕ) (y : Fin m → Fin 4 → ℤ) :
    treeRealizationFiber t M m y =
      realizationFiber (validRealizationDataFinset t M m)
        (fun d y => d.Realizes y) y :=
  rfl

theorem treeSymDenom_eq_symDenom
    (t : PlaneTree) (M m : ℕ) (y : Fin m → Fin 4 → ℤ) :
    treeSymDenom t M m y =
      symDenom (validRealizationDataFinset t M m)
        (fun d y => d.Realizes y) y :=
  rfl

private theorem card_fiber_precomp_perm {m : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (w : Fin m → α) (σ : Equiv.Perm (Fin m))
    (a : α) :
    (Finset.univ.filter fun j => w (σ j) = a).card =
      (Finset.univ.filter fun j => w j = a).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    (Equiv.subtypeEquiv σ (fun j => Iff.rfl))

private theorem precomp_perm_mem_validWords {m : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] {mult : α → ℕ} {w : Fin m → α}
    (hw : w ∈ validWords mult) (σ : Equiv.Perm (Fin m)) :
    (fun j => w (σ j)) ∈ validWords mult := by
  rw [validWords, Finset.mem_filter] at hw ⊢
  exact ⟨Finset.mem_univ _, fun a => (card_fiber_precomp_perm w σ a).trans (hw.2 a)⟩

/-- Realization incidence is invariant under permuting tuple indices. -/
theorem ValidRealizationData.realizes_precomp_perm_iff
    {t : PlaneTree} {M m : ℕ} (d : ValidRealizationData t M m)
    (σ : Equiv.Perm (Fin m)) (y : Fin m → Fin 4 → ℤ) :
    d.Realizes (fun j => y (σ j)) ↔ d.Realizes y := by
  constructor
  · rintro ⟨z, w, hadm, hw, hy⟩
    refine ⟨z, fun j => w (σ.symm j), hadm,
      precomp_perm_mem_validWords hw σ.symm, ?_⟩
    intro j
    simpa using hy (σ.symm j)
  · rintro ⟨z, w, hadm, hw, hy⟩
    refine ⟨z, fun j => w (σ j), hadm,
      precomp_perm_mem_validWords hw σ, ?_⟩
    intro j
    exact hy (σ j)

/-- Consequently the concrete symmetry denominator is invariant under
permuting the indices of the tuple. -/
theorem treeSymDenom_precomp_perm
    (t : PlaneTree) (M m : ℕ) (σ : Equiv.Perm (Fin m))
    (y : Fin m → Fin 4 → ℤ) :
    treeSymDenom t M m (fun j => y (σ j)) = treeSymDenom t M m y := by
  exact symDenom_eq_of_iff _ _ fun d _ => d.realizes_precomp_perm_iff σ y

private theorem incidence_size_lt_of_mem {c : PlaneTree} {cs : List PlaneTree}
    (hc : c ∈ cs) : c.size < (PlaneTree.node cs).size := by
  have h₁ : c.size ∈ cs.map PlaneTree.size :=
    List.mem_map.mpr ⟨c, hc, rfl⟩
  have h₂ : c.size ≤ (cs.map PlaneTree.size).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ h₁
  have h₃ : (PlaneTree.node cs).size = 1 + PlaneTree.sizeList cs := rfl
  rw [h₃, PlaneTree.sizeList_eq_map]
  omega

private theorem incidence_planeTreeInduction {motive : PlaneTree → Prop}
    (ind : ∀ cs : List PlaneTree,
      (∀ c ∈ cs, motive c) → motive (PlaneTree.node cs)) :
    ∀ t, motive t
  | PlaneTree.node cs =>
      ind cs fun c _hc => incidence_planeTreeInduction ind c
termination_by t => t.size
decreasing_by exact incidence_size_lt_of_mem _hc

/-- The least common ancestor of two distinct leaves is necessarily a
branching vertex. -/
private theorem lcaV_mem_branchNodes_of_ne :
    ∀ {t : PlaneTree} (l l' : {v // v ∈ Leaves t}),
      l ≠ l' → lcaV l.1 l'.1 ∈ BranchNodes t := by
  intro t
  induction t using incidence_planeTreeInduction with
  | ind cs ih =>
      intro l l' hne
      by_cases hlen : 1 ≤ cs.length
      · obtain ⟨i, li, rfl⟩ := rdec_leafUp_surj hlen l
        obtain ⟨j, lj, rfl⟩ := rdec_leafUp_surj hlen l'
        by_cases hij : i = j
        · subst j
          have hli : li ≠ lj := by
            intro h
            apply hne
            subst lj
            rfl
          change lcaV (childV i li.1) (childV i lj.1) ∈
            BranchNodes (PlaneTree.node cs)
          rw [rdec_lcaV_childV]
          exact (rdec_childV_mem_branchNodes i _).mpr
            (ih (cs.get i) (List.get_mem cs i) li lj hli)
        · change lcaV (childV i li.1) (childV j lj.1) ∈
            BranchNodes (PlaneTree.node cs)
          rw [rdec_lcaV_childV_ne hij]
          apply rdec_root_mem_branchNodes
          omega
      · have hzero : cs.length = 0 := by omega
        have hcs : cs = [] := List.eq_nil_of_length_eq_zero hzero
        subst cs
        exact absurd
          (Subtype.ext ((vpos_leaf_eq l.1).trans (vpos_leaf_eq l'.1).symm)) hne

/-- Admissibility depends on a marking only through its values on branch
vertices. -/
private theorem isAdmissible_congr_marking
    {t : PlaneTree} {Nm Nm' : HeppMarking t} {M : ℕ}
    {z : {v // v ∈ Leaves t} → Fin 4 → ℤ}
    (hNm : HeppMarking.EqOnBranch Nm Nm')
    (h : IsAdmissible Nm M z) :
    IsAdmissible Nm' M z := by
  refine ⟨h.inj, ?_, h.bounded, ?_⟩
  · intro l l' hne
    have hv : lcaV l.1 l'.1 ∈ BranchNodes t :=
      lcaV_mem_branchNodes_of_ne l l' hne
    have hs : scaleN Nm (lcaV l.1 l'.1) =
        scaleN Nm' (lcaV l.1 l'.1) := by
      simp [scaleN, hNm _ hv]
    rw [← hs]
    exact h.sep l l' hne
  · intro v hv c hc c' hc'
    refine Relation.ReflTransGen.lift id ?_ _ _
      (h.linked v hv c hc c' hc')
    intro a b hab
    rcases hab with ⟨ha, hb, l, hl, l', hl', hd⟩
    refine ⟨ha, hb, l, hl, l', hl', ?_⟩
    have hs : scaleN Nm v = scaleN Nm' v := by
      simp [scaleN, hNm v hv]
    rw [← hs]
    exact hd

/-- `RealizesTuple` is insensitive to junk marking values off branch nodes
and junk multiplicity values off leaves. -/
theorem realizesTuple_congr_restricted
    {t : PlaneTree} {Nm Nm' : HeppMarking t}
    {mu mu' : Multiplicities t} {M m : ℕ}
    {y : Fin m → Fin 4 → ℤ}
    (hNm : HeppMarking.EqOnBranch Nm Nm')
    (hmu : Multiplicities.EqOnLeaves mu mu') :
    RealizesTuple t Nm mu M y ↔ RealizesTuple t Nm' mu' M y := by
  have hmult :
      (fun l : {v // v ∈ Leaves t} => mu.m l.1) =
        (fun l : {v // v ∈ Leaves t} => mu'.m l.1) := by
    funext l
    exact hmu l.1 l.2
  constructor
  · rintro ⟨z, w, hadm, hw, hy⟩
    exact ⟨z, w, isAdmissible_congr_marking hNm hadm,
      by simpa [hmult] using hw, hy⟩
  · rintro ⟨z, w, hadm, hw, hy⟩
    exact ⟨z, w,
      isAdmissible_congr_marking
        (HeppMarking.eqOnBranch_symm hNm) hadm,
      by simpa [hmult] using hw, hy⟩

private theorem total_of_mem_validWords {m : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] {mult : α → ℕ} {w : Fin m → α}
    (hw : w ∈ validWords mult) :
    ∑ a, mult a = m := by
  rw [validWords, Finset.mem_filter] at hw
  calc
    ∑ a, mult a =
        ∑ a : α, (Finset.univ.filter fun j => w j = a).card := by
          apply Finset.sum_congr rfl
          intro a _
          exact (hw.2 a).symm
    _ = (Finset.univ : Finset (Fin m)).card := by
          symm
          exact Finset.card_eq_sum_card_fiberwise
            (f := w) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    _ = m := by simp

/-- Every concrete realization witness forces the total leaf multiplicity to
equal the tuple length. -/
theorem multiplicities_total_of_realizesTuple
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (h : RealizesTuple t Nm mu M y) :
    ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m := by
  obtain ⟨_, w, _, hw, _⟩ := h
  exact total_of_mem_validWords hw

/-- An actual valid-tree realization by bounded bundle data contributes
an element to the concrete incidence fiber, so its denominator is positive. -/
theorem treeSymDenom_pos_of_realizesTuple
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (ht : t.isValid = true) (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (hreal : RealizesTuple t Nm mu M y) :
    0 < treeSymDenom t M m y := by
  let d₀ : RealizationData t M m :=
    realizationDataOfBundles Nm mu hscale htotal
  have hd₀ : d₀.IsValid := by
    exact realizationDataOfBundles_isValid_of_treeValid
      ht Nm mu hscale htotal
  let d : ValidRealizationData t M m := ⟨d₀, hd₀⟩
  rw [treeSymDenom_eq_symDenom, symDenom_pos_iff]
  refine ⟨d, Finset.mem_univ _, ?_⟩
  have hNm :
      HeppMarking.EqOnBranch (d₀.toHeppMarking hd₀) Nm := by
    intro v hv
    change (branchDataOfScaleBound Nm hscale).raw v = Nm.Nexp v
    rw [BranchExponentData.raw_apply_of_mem _ hv]
    exact branchDataOfScaleBound_apply Nm hscale ⟨v, hv⟩
  have hmu :
      Multiplicities.EqOnLeaves (d₀.toMultiplicities hd₀) mu := by
    intro v hv
    change (leafDataOfTotal mu htotal).raw v = mu.m v
    rw [LeafMultiplicityData.raw_apply_of_mem _ hv]
    exact LeafMultiplicityData.ofMultiplicities_apply mu _ ⟨v, hv⟩
  exact (realizesTuple_congr_restricted hNm hmu).mpr hreal

/-- Convenience form in which the total-multiplicity equation is recovered
from the realization word itself; no parity hypothesis is needed. -/
theorem treeSymDenom_pos_of_realizesTuple_autoTotal
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (ht : t.isValid = true) (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (hreal : RealizesTuple t Nm mu M y) :
    0 < treeSymDenom t M m y :=
  treeSymDenom_pos_of_realizesTuple ht Nm mu hscale
    (multiplicities_total_of_realizesTuple hreal) hreal

/-- Paired-vector compatibility wrapper.  Evenness remains available as an
extra property, but does not alter the general denominator. -/
theorem treeSymDenom_pos_of_realizesTuple_even
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (ht : t.isValid = true) (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (_heven : ∀ l : {v // v ∈ Leaves t}, Even (mu.m l.1))
    (hreal : RealizesTuple t Nm mu M y) :
    0 < treeSymDenom t M m y :=
  treeSymDenom_pos_of_realizesTuple_autoTotal
    ht Nm mu hscale hreal

/-- The paired-vector existence theorem supplies a valid tree whose concrete
fixed-tree denominator is positive. -/
theorem exists_treeSymDenom_pos_of_across_pairing
    (M m : ℕ) (hm : 1 ≤ m) (A : Finset (Fin m))
    (y : Fin m → Fin 4 → ℤ) (hy : y ∈ rdec_boundedTuples M m)
    (κ : AcrossPairing A) (hκ : RespectsWord A y κ) :
    ∃ t : PlaneTree, t.isValid = true ∧ 0 < treeSymDenom t M m y := by
  obtain ⟨t, ht, Nm, mu, hyreal, _, hscale, heven⟩ :=
    exists_realizing_tree_of_across_pairing M m hm A y hy κ hκ
  have hreal : RealizesTuple t Nm mu M y :=
    (mem_realizedTuples.mp hyreal).2
  exact ⟨t, ht, treeSymDenom_pos_of_realizesTuple_even
    ht Nm mu hscale (fun l => heven l.1 l.2) hreal⟩

/-- Fixed-tree finite-incidence resummation, the abstract content of paper
(5.6), specialized to the restricted realization data above. -/
theorem sum_eq_sum_tree_incidence_div
    (t : PlaneTree) (M m : ℕ)
    (Y : Finset (Fin m → Fin 4 → ℤ))
    (F : (Fin m → Fin 4 → ℤ) → ℝ)
    (hcover : ∀ y ∈ Y, ∃ d : ValidRealizationData t M m, d.Realizes y) :
    ∑ y ∈ Y, F y =
      ∑ d ∈ validRealizationDataFinset t M m,
        ∑ y ∈ Y.filter (fun y => d.Realizes y),
          F y / treeSymDenom t M m y := by
  classical
  simpa [treeSymDenom_eq_symDenom] using
    (sum_eq_sum_incidence_div
      (validRealizationDataFinset t M m) Y
      (fun d y => d.Realizes y) F
      (fun y hy => ⟨(hcover y hy).choose, Finset.mem_univ _,
        (hcover y hy).choose_spec⟩))

end Anderson4D
