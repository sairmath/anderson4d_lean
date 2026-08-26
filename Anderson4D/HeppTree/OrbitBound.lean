import Anderson4D.HeppTree.AutomorphismGeometry
import Anderson4D.HeppTree.Incidence

/-!
# Orbit lower bound for the fixed-tree incidence denominator

This file implements Proposition 5.6, Step 1.  Simultaneously transporting a
Hepp marking, the leaf multiplicities, an admissible embedding, and its word
witness along a tree automorphism preserves realization.  Consequently every
marking in the orbit of a realizing marked tree supplies distinct restricted
branch data in the concrete denominator fiber.  Orbit--stabilizer then gives
the division-free natural-number form of paper (5.12).
-/

namespace Anderson4D

open PlaneTree

/-! ## Transport of word and realization witnesses -/

/-- Postcomposing a word by an equivalence merely reindexes its prescribed
fiber sizes. -/
theorem postcomp_equiv_mem_validWords
    {m : ℕ} {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β) {mult : α → ℕ} {w : Fin m → α}
    (hw : w ∈ validWords mult) :
    (fun j => e (w j)) ∈ validWords (fun b => mult (e.symm b)) := by
  rw [validWords, Finset.mem_filter] at hw ⊢
  refine ⟨Finset.mem_univ _, fun b => ?_⟩
  have hfilter :
      (Finset.univ.filter fun j => e (w j) = b) =
        Finset.univ.filter fun j => w j = e.symm b := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact e.apply_eq_iff_eq_symm_apply
  rw [hfilter]
  exact hw.2 (e.symm b)

/-- A concrete tuple realization is preserved by simultaneous transport of
all tree-indexed data along an automorphism. -/
theorem RealizesTuple.map_aut
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t}
    {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (h : RealizesTuple t Nm mu M y) (g : Aut t) :
    RealizesTuple t (smulHeppMarking g Nm) (smulMultiplicities g mu) M y := by
  obtain ⟨z, w, hadm, hw, hy⟩ := h
  refine ⟨smulLeafEmbedding g z, fun j => autLeavesEquiv g (w j),
    hadm.map_aut g, ?_, ?_⟩
  · simpa [smulMultiplicities, autLeavesEquiv] using
      postcomp_equiv_mem_validWords (autLeavesEquiv g) hw
  · intro j
    simpa using hy j

/-! ## Restricted data attached to transported bundles -/

/-- The analytic scale bound is invariant under transport. -/
theorem scale_bound_smulHeppMarking
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    (hscale : ∀ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (g : Aut t) :
    ∀ v ∈ BranchNodes t,
      (scaleN (smulHeppMarking g Nm) v : ℝ) ≤ 4 * (M : ℝ) := by
  intro v hv
  rw [scaleN_smulHeppMarking]
  exact hscale ((g⁻¹ : Aut t).1 v)
    ((aut_mem_BranchNodes_iff (g⁻¹ : Aut t) v).mpr hv)

/-- The finite branch carrier obtained from a scale-bounded marking has raw
view equal to the marking's canonical branch-supported view. -/
theorem branchDataOfScaleBound_raw
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    (hscale : ∀ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ)) :
    (branchDataOfScaleBound Nm hscale).raw = Nm.canonicalRaw := by
  funext v
  by_cases hv : v ∈ BranchNodes t
  · rw [BranchExponentData.raw_apply_of_mem _ hv,
      HeppMarking.canonicalRaw_apply_of_mem _ hv]
    exact branchDataOfScaleBound_apply Nm hscale ⟨v, hv⟩
  · rw [BranchExponentData.raw_apply_of_not_mem _ hv,
      HeppMarking.canonicalRaw_apply_of_not_mem _ hv]

/-- The valid restricted datum obtained by simultaneously transporting a
fixed marking and fixed multiplicities along `g`. -/
def validRealizationDataOfAut
    {t : PlaneTree} {M m : ℕ}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (g : Aut t) :
    ValidRealizationData t M m := by
  let hscaleg := scale_bound_smulHeppMarking hscale g
  have htotalg :
      ∑ l : {v // v ∈ Leaves t}, (smulMultiplicities g mu).m l.1 = m :=
    (sum_smulMultiplicities g mu).trans htotal
  exact
    ⟨realizationDataOfBundles
        (smulHeppMarking g Nm) (smulMultiplicities g mu)
        hscaleg htotalg,
      realizationDataOfBundles_isValid_of_treeValid
        ht (smulHeppMarking g Nm) (smulMultiplicities g mu)
        hscaleg htotalg⟩

/-- The branch component of the transported restricted datum records exactly
the transported canonical raw marking. -/
theorem validRealizationDataOfAut_branch_raw
    {t : PlaneTree} {M m : ℕ}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (g : Aut t) :
    (validRealizationDataOfAut ht Nm mu hscale htotal g).1.1.raw =
      g • Nm.canonicalRaw := by
  rw [← smulHeppMarking_canonicalRaw]
  exact branchDataOfScaleBound_raw
    (scale_bound_smulHeppMarking hscale g)

/-- The transported restricted datum remains incident to the original tuple. -/
theorem validRealizationDataOfAut_realizes
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (hreal : RealizesTuple t Nm mu M y)
    (g : Aut t) :
    (validRealizationDataOfAut ht Nm mu hscale htotal g).Realizes y := by
  let d :=
    validRealizationDataOfAut ht Nm mu hscale htotal g
  have hNm :
      HeppMarking.EqOnBranch
        (d.1.toHeppMarking d.2) (smulHeppMarking g Nm) := by
    intro v hv
    change
      (branchDataOfScaleBound
          (smulHeppMarking g Nm)
          (scale_bound_smulHeppMarking hscale g)).raw v =
        (smulHeppMarking g Nm).Nexp v
    rw [BranchExponentData.raw_apply_of_mem _ hv]
    exact branchDataOfScaleBound_apply
      (smulHeppMarking g Nm)
      (scale_bound_smulHeppMarking hscale g) ⟨v, hv⟩
  have hmu :
      Multiplicities.EqOnLeaves
        (d.1.toMultiplicities d.2) (smulMultiplicities g mu) := by
    intro v hv
    change
      (leafDataOfTotal
          (smulMultiplicities g mu)
          ((sum_smulMultiplicities g mu).trans htotal)).raw v =
        (smulMultiplicities g mu).m v
    rw [LeafMultiplicityData.raw_apply_of_mem _ hv]
    exact LeafMultiplicityData.ofMultiplicities_apply
      (smulMultiplicities g mu) _ ⟨v, hv⟩
  exact (realizesTuple_congr_restricted hNm hmu).mpr (hreal.map_aut g)

/-! ## Injection of the marking orbit into the incidence fiber -/

/-- Choose one tree automorphism representing an element of the marking
orbit.  The final injection is independent of this noncanonical choice
because its branch component recovers the orbit element itself. -/
noncomputable def orbitRepresentative
    {t : PlaneTree} {Nm : HeppMarking t}
    (N : MulAction.orbit (Aut t) Nm.canonicalRaw) :
    Aut t :=
  Classical.choose (MulAction.mem_orbit_iff.mp N.2)

theorem orbitRepresentative_spec
    {t : PlaneTree} {Nm : HeppMarking t}
    (N : MulAction.orbit (Aut t) Nm.canonicalRaw) :
    orbitRepresentative N • Nm.canonicalRaw = N.1 :=
  Classical.choose_spec (MulAction.mem_orbit_iff.mp N.2)

/-- An orbit marking, together with any representative automorphism, gives a
member of the concrete fixed-tree incidence fiber. -/
noncomputable def orbitToTreeRealizationFiber
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (hreal : RealizesTuple t Nm mu M y)
    (N : MulAction.orbit (Aut t) Nm.canonicalRaw) :
    {d : ValidRealizationData t M m //
      d ∈ treeRealizationFiber t M m y} := by
  let g := orbitRepresentative N
  let d := validRealizationDataOfAut ht Nm mu hscale htotal g
  refine ⟨d, ?_⟩
  rw [treeRealizationFiber, Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    validRealizationDataOfAut_realizes
      ht Nm mu hscale htotal hreal g⟩

theorem orbitToTreeRealizationFiber_injective
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (hreal : RealizesTuple t Nm mu M y) :
    Function.Injective
      (orbitToTreeRealizationFiber
        ht Nm mu hscale htotal hreal) := by
  intro N N' hNN'
  apply Subtype.ext
  have hraw := congrArg
    (fun d : {d : ValidRealizationData t M m //
        d ∈ treeRealizationFiber t M m y} =>
      d.1.1.1.raw) hNN'
  change
    (validRealizationDataOfAut ht Nm mu hscale htotal
        (orbitRepresentative N)).1.1.raw =
      (validRealizationDataOfAut ht Nm mu hscale htotal
        (orbitRepresentative N')).1.1.raw at hraw
  rw [validRealizationDataOfAut_branch_raw,
    validRealizationDataOfAut_branch_raw,
    orbitRepresentative_spec, orbitRepresentative_spec] at hraw
  exact hraw

/-! ## The denominator lower bound (paper (5.12)) -/

/-- Distinct canonical raw markings in the automorphism orbit yield distinct
elements of the concrete incidence fiber. -/
theorem markingOrbit_card_le_treeSymDenom
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (hreal : RealizesTuple t Nm mu M y) :
    (MulAction.orbit (Aut t) Nm.canonicalRaw).toFinset.card ≤
      treeSymDenom t M m y := by
  classical
  have hcard :=
    Fintype.card_le_of_injective
      (orbitToTreeRealizationFiber
        ht Nm mu hscale htotal hreal)
      (orbitToTreeRealizationFiber_injective
        ht Nm mu hscale htotal hreal)
  simpa [treeSymDenom] using hcard

/-- Paper (5.12), stated without natural-number division:

`|Aut(t)| ≤ treeSymDenom(t,M,m,y) * |Aut(t,Nm)|`.

The scale and total-multiplicity bounds needed to enter the finite denominator
carrier are recovered from the realization witness itself. -/
theorem card_aut_le_treeSymDenom_mul_card_autHeppMarked
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hreal : RealizesTuple t Nm mu M y) :
    Fintype.card (Aut t) ≤
      treeSymDenom t M m y *
        Fintype.card (AutHeppMarked t Nm) := by
  obtain ⟨z, w, hadm, hw, hy⟩ := hreal
  have hreal' : RealizesTuple t Nm mu M y :=
    ⟨z, w, hadm, hw, hy⟩
  have hscale :
      ∀ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ) :=
    fun v hv => scaleN_le_four_mul_of_isAdmissible hadm hv
  have htotal :
      ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m :=
    multiplicities_total_of_realizesTuple hreal'
  have horbit :=
    markingOrbit_card_le_treeSymDenom
      ht Nm mu hscale htotal hreal'
  calc
    Fintype.card (Aut t) =
        (MulAction.orbit (Aut t) Nm.canonicalRaw).toFinset.card *
          Fintype.card (AutHeppMarked t Nm) :=
      (card_orbit_mul_card_autHeppMarked t Nm).symm
    _ ≤ treeSymDenom t M m y *
          Fintype.card (AutHeppMarked t Nm) :=
      Nat.mul_le_mul_right _ horbit

end Anderson4D
