import Anderson4D.HeppTree.ExistenceBounds

/-!
# Paired-vector form of paper Lemma 5.5

The general realizing-tree construction only needs every value to occur at
least twice.  Paper Lemma 5.5 starts from a fixed bijection `κ : A ≃ Aᶜ`;
this stronger input forces the leaf multiplicities to be even.  This module
packages that paper-facing corollary, including the uniform branch-scale
bound from `ExistenceBounds`.
-/

namespace Anderson4D

open PlaneTree

private theorem pe_two_le_valueFiber {m : ℕ} (A : Finset (Fin m))
    (y : Fin m → Fin 4 → ℤ) (κ : AcrossPairing A)
    (hκ : RespectsWord A y κ) (j : Fin m) :
    2 ≤ (Finset.univ.filter fun k => y k = y j).card := by
  classical
  by_cases hj : j ∈ A
  · let jA : ↥A := ⟨j, hj⟩
    let k : Fin m := (κ jA).1
    have hkAc : k ∈ Aᶜ := (κ jA).2
    have hk : k ∉ A := Finset.mem_compl.mp hkAc
    have hjk : j ≠ k := fun h => hk (h ▸ hj)
    have hyk : y k = y j := (hκ jA).symm
    apply Finset.one_lt_card.mpr
    exact ⟨j, by simp, k, by simp [hyk], hjk⟩
  · have hjAc : j ∈ Aᶜ := Finset.mem_compl.mpr hj
    let jAc : ↥(Aᶜ) := ⟨j, hjAc⟩
    let kA : ↥A := κ.symm jAc
    let k : Fin m := kA.1
    have hk : k ∈ A := kA.2
    have hjk : j ≠ k := fun h => hj (h ▸ hk)
    have hyk : y k = y j := by
      simpa [k, kA, jAc] using hκ kA
    apply Finset.one_lt_card.mpr
    exact ⟨j, by simp, k, by simp [hyk], hjk⟩

/-- **Paper Lemma 5.5, paired-vector form.**  A bounded word admitting a
pairing across `A/Aᶜ` is realized by a valid marked Hepp tree.  Every branch
scale is at most `4M`, and every leaf multiplicity is even. -/
theorem exists_realizing_tree_of_across_pairing
    (M m : ℕ) (hm : 1 ≤ m) (A : Finset (Fin m))
    (y : Fin m → Fin 4 → ℤ) (hy : y ∈ rdec_boundedTuples M m)
    (κ : AcrossPairing A) (hκ : RespectsWord A y κ) :
    ∃ (t : PlaneTree) (_ : t.isValid = true) (Nm : HeppMarking t)
      (mu : Multiplicities t),
      y ∈ realizedTuples t Nm mu M m ∧ t.leafCount ≤ m ∧
        (∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ)) ∧
        (∀ l ∈ Leaves t, Even (mu.m l)) := by
  obtain ⟨t, hv, Nm, mu, hreal, hleaf⟩ :=
    exists_realizing_tree M m hm y hy
      (fun j => pe_two_le_valueFiber A y κ hκ j)
  obtain ⟨_, z, w, hadm, hw, hyz⟩ := mem_realizedTuples.mp hreal
  have hwκ : RespectsWord A w κ := by
    intro j
    apply hadm.inj
    rw [← hyz j.1, ← hyz (κ j).1, hκ j]
  have heven :
      ∀ l : {l // l ∈ Leaves t}, Even (mu.m l.1) :=
    even_mult_of_compatibleAcrossPairing A
      (fun l : {l // l ∈ Leaves t} => mu.m l.1) hw κ hwκ
  refine ⟨t, hv, Nm, mu, hreal, hleaf, ?_, ?_⟩
  · intro v hv'
    exact scaleN_le_four_mul_of_isAdmissible hadm hv'
  · intro l hl
    exact heven ⟨l, hl⟩

end Anderson4D
