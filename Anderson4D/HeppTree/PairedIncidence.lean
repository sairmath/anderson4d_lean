import Anderson4D.HeppTree.Incidence
import Anderson4D.HeppTree.OrbitBound
import Anderson4D.Combinatorics.PrimitiveWord

/-!
# Even-multiplicity incidence for the paper's paired decomposition

The denominator in paper (5.6) ranges over branch-scale and leaf-multiplicity
data whose leaf multiplicities are even.  The general incidence carrier in
`Incidence` is useful for Proposition 5.6, where arbitrary multiplicities at
least two occur.  This file supplies the paired specialization and proves
that, for a tuple equipped with an across-half pairing, its general and
paired incidence fibers have the same cardinality.
-/

namespace Anderson4D

open PlaneTree

/-- The finite carrier of restricted realization data with even leaf
multiplicities, exactly as in the denominator of paper (5.6). -/
def pairedValidRealizationDataFinset (t : PlaneTree) (M m : ℕ) :
    Finset (PairedValidRealizationData t M m) :=
  Finset.univ

/-- Incidence of paired restricted data with a tuple. -/
def PairedDataRealizes
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (y : Fin m → Fin 4 → ℤ) : Prop :=
  RealizesTuple t
    (d.1.toHeppMarking d.2.1)
    (d.1.toMultiplicities d.2.1) M y

noncomputable instance pairedValidRealizationDataDecidableRel
    (t : PlaneTree) (M m : ℕ) :
    DecidableRel
      (fun (d : PairedValidRealizationData t M m)
        (y : Fin m → Fin 4 → ℤ) => PairedDataRealizes d y) :=
  fun _ _ => Classical.propDecidable _

/-- The even restricted data incident to `y` for a fixed tree. -/
noncomputable def pairedTreeRealizationFiber
    (t : PlaneTree) (M m : ℕ) (y : Fin m → Fin 4 → ℤ) :
    Finset (PairedValidRealizationData t M m) :=
  (pairedValidRealizationDataFinset t M m).filter fun d =>
    PairedDataRealizes d y

/-- The exact even-multiplicity symmetry denominator in paper (5.6). -/
noncomputable def pairedTreeSymDenom
    (t : PlaneTree) (M m : ℕ) (y : Fin m → Fin 4 → ℤ) : ℕ :=
  (pairedTreeRealizationFiber t M m y).card

/-- Forget parity while retaining general validity. -/
def pairedDataToValid
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m) :
    ValidRealizationData t M m :=
  ⟨d.1, d.2.1⟩

@[simp]
theorem pairedDataToValid_val
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m) :
    (pairedDataToValid d).1 = d.1 :=
  rfl

/-- Forgetting parity does not change the realization predicate. -/
theorem pairedDataRealizes_toValid_iff
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (y : Fin m → Fin 4 → ℤ) :
    (pairedDataToValid d).Realizes y ↔ PairedDataRealizes d y := by
  rfl

/-- A realization of a tuple carrying an across-half pairing necessarily has
even leaf multiplicities.  This is the converse parity bridge needed to
identify the two incidence fibers. -/
theorem ValidRealizationData.isEven_of_realizes_of_acrossPairing
    {t : PlaneTree} {M m : ℕ}
    (d : ValidRealizationData t M m)
    {y : Fin m → Fin 4 → ℤ}
    (hreal : d.Realizes y)
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (hκ : RespectsWord A y κ) :
    d.1.IsEven := by
  obtain ⟨z, w, hadm, hw, hy⟩ := hreal
  have hwκ : RespectsWord A w κ := by
    intro j
    apply hadm.inj
    rw [← hy j.1, ← hy (κ j).1, hκ j]
  have heven :
      ∀ l : {l // l ∈ Leaves t},
        Even ((d.1.toMultiplicities d.2).m l.1) :=
    even_mult_of_compatibleAcrossPairing A
      (fun l : {l // l ∈ Leaves t} =>
        (d.1.toMultiplicities d.2).m l.1) hw κ hwκ
  intro l
  have hl := heven l
  change Even (d.1.2.raw l.1) at hl
  rw [LeafMultiplicityData.raw_apply_of_mem d.1.2 l.2] at hl
  exact hl

/-- Promote incident general data to paired-valid data using an across-half
pairing on the realized tuple. -/
def validDataToPairedOfAcrossPairing
    {t : PlaneTree} {M m : ℕ}
    (d : ValidRealizationData t M m)
    {y : Fin m → Fin 4 → ℤ}
    (hreal : d.Realizes y)
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (hκ : RespectsWord A y κ) :
    PairedValidRealizationData t M m :=
  ⟨d.1, d.2,
    ValidRealizationData.isEven_of_realizes_of_acrossPairing
      d hreal A κ hκ⟩

@[simp]
theorem validDataToPairedOfAcrossPairing_val
    {t : PlaneTree} {M m : ℕ}
    (d : ValidRealizationData t M m)
    {y : Fin m → Fin 4 → ℤ}
    (hreal : d.Realizes y)
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (hκ : RespectsWord A y κ) :
    (validDataToPairedOfAcrossPairing d hreal A κ hκ).1 = d.1 :=
  rfl

/-- On a paired tuple, forgetting and reconstructing parity gives an
equivalence between the general and even incidence fibers. -/
noncomputable def treeRealizationFiberEquivPaired
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (hκ : RespectsWord A y κ) :
    {d : ValidRealizationData t M m //
      d ∈ treeRealizationFiber t M m y} ≃
    {d : PairedValidRealizationData t M m //
      d ∈ pairedTreeRealizationFiber t M m y} where
  toFun d := by
    have hreal : d.1.Realizes y := by
      exact (Finset.mem_filter.mp d.2).2
    let dp :=
      validDataToPairedOfAcrossPairing d.1 hreal A κ hκ
    refine ⟨dp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact hreal
  invFun d := by
    have hreal : PairedDataRealizes d.1 y := by
      exact (Finset.mem_filter.mp d.2).2
    refine ⟨pairedDataToValid d.1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact (pairedDataRealizes_toValid_iff d.1 y).mpr hreal
  left_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- For a tuple with an across-half pairing, allowing arbitrary
multiplicities in the auxiliary denominator adds no incident data: every
realizing multiplicity is automatically even. -/
theorem treeSymDenom_eq_pairedTreeSymDenom
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (hκ : RespectsWord A y κ) :
    treeSymDenom t M m y = pairedTreeSymDenom t M m y := by
  unfold treeSymDenom pairedTreeSymDenom
  simpa only [Fintype.card_coe] using
    Fintype.card_congr
      (treeRealizationFiberEquivPaired A κ hκ)

/-- The paired denominator has the same orbit-stabilizer lower bound as the
general denominator, by the preceding exact identification. -/
theorem pairedTreeSymDenom_pos_of_general
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (hκ : RespectsWord A y κ)
    (hpos : 0 < treeSymDenom t M m y) :
    0 < pairedTreeSymDenom t M m y := by
  rwa [treeSymDenom_eq_pairedTreeSymDenom A κ hκ] at hpos

/-- Paper (5.12) with the exact even-multiplicity denominator from (5.6),
in division-free form. -/
theorem card_aut_le_pairedTreeSymDenom_mul_card_autHeppMarked
    {t : PlaneTree} {M m : ℕ} {y : Fin m → Fin 4 → ℤ}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hreal : RealizesTuple t Nm mu M y)
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (hκ : RespectsWord A y κ) :
    Fintype.card (Aut t) ≤
      pairedTreeSymDenom t M m y *
        Fintype.card (AutHeppMarked t Nm) := by
  rw [← treeSymDenom_eq_pairedTreeSymDenom A κ hκ]
  exact card_aut_le_treeSymDenom_mul_card_autHeppMarked
    ht Nm mu hreal

/-- Fixed-tree finite-incidence resummation with the exact even denominator
printed in paper (5.6). -/
theorem sum_eq_sum_paired_tree_incidence_div
    (t : PlaneTree) (M m : ℕ)
    (Y : Finset (Fin m → Fin 4 → ℤ))
    (F : (Fin m → Fin 4 → ℤ) → ℝ)
    (hcover : ∀ y ∈ Y,
      ∃ d : PairedValidRealizationData t M m,
        PairedDataRealizes d y) :
    ∑ y ∈ Y, F y =
      ∑ d ∈ pairedValidRealizationDataFinset t M m,
        ∑ y ∈ Y.filter (fun y => PairedDataRealizes d y),
          F y / pairedTreeSymDenom t M m y := by
  classical
  simpa [pairedTreeSymDenom, pairedTreeRealizationFiber,
    pairedValidRealizationDataFinset, realizationFiber, symDenom] using
    (sum_eq_sum_incidence_div
      (pairedValidRealizationDataFinset t M m) Y
      (fun d y => PairedDataRealizes d y) F
      (fun y hy =>
        ⟨(hcover y hy).choose, Finset.mem_univ _,
          (hcover y hy).choose_spec⟩))

end Anderson4D
