import Anderson4D.Combinatorics.MultiplicityCount
import Anderson4D.Continuum.PrimitiveAssembly

/-!
# Fixed-incidence reindexing by realized sets and induced words

This file supplies the finite carrier change used in paper (5.8)--(5.11).
For one fixed paired realization datum, a realized lattice tuple is sent to

* its unlabelled support `Z`, which is an element of `realizedSets`, and
* the word of its values, now regarded as a word in the finite alphabet `Z`.

The tuple is recovered by forgetting the subtype proofs in that word.
Consequently the map is injective, its finite image gives an exact
reindexing of arbitrary real-valued sums, and the result admits a second
exact Fubini decomposition by the induced multiplicity profile on `Z`.

No estimate or target-shaped hypothesis occurs in this construction.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## Supports and finite-support words -/

/-- The unlabelled set of values occurring in a finite lattice tuple. -/
def tupleSupport {m : ℕ} (y : Fin m → Z4) : Finset Z4 :=
  Finset.univ.image y

@[simp]
theorem mem_tupleSupport {m : ℕ} {y : Fin m → Z4} {x : Z4} :
    x ∈ tupleSupport y ↔ ∃ j, y j = x := by
  simp [tupleSupport]

/-- A word with values in a prescribed finite support. -/
abbrev SupportWord (m : ℕ) (Z : Finset Z4) :=
  Fin m → {x // x ∈ Z}

/-- Forget the support proofs and recover a lattice tuple. -/
def SupportWord.toTuple {m : ℕ} {Z : Finset Z4}
    (w : SupportWord m Z) : Fin m → Z4 :=
  fun j => (w j).1

/-- Regard a tuple as a word over its own support. -/
def tupleWord {m : ℕ} (y : Fin m → Z4) :
    SupportWord m (tupleSupport y) :=
  fun j => ⟨y j, Finset.mem_image.mpr
    ⟨j, Finset.mem_univ _, rfl⟩⟩

@[simp]
theorem tupleWord_toTuple {m : ℕ} (y : Fin m → Z4) :
    (tupleWord y).toTuple = y :=
  rfl

/-- Transport a tuple word along an equality of its support with `Z`. -/
def tupleWordAt {m : ℕ} {y : Fin m → Z4} {Z : Finset Z4}
    (hZ : tupleSupport y = Z) : SupportWord m Z :=
  fun j => ⟨y j, by
    rw [← hZ]
    exact Finset.mem_image.mpr
      ⟨j, Finset.mem_univ _, rfl⟩⟩

@[simp]
theorem tupleWordAt_toTuple
    {m : ℕ} {y : Fin m → Z4} {Z : Finset Z4}
    (hZ : tupleSupport y = Z) :
    (tupleWordAt hZ).toTuple = y :=
  rfl

theorem tupleWordAt_injective
    {m : ℕ} {Z : Finset Z4}
    {y y' : Fin m → Z4}
    (hy : tupleSupport y = Z) (hy' : tupleSupport y' = Z)
    (h : tupleWordAt hy = tupleWordAt hy') :
    y = y' := by
  exact (tupleWordAt_toTuple hy).symm.trans
    ((congrArg SupportWord.toTuple h).trans
      (tupleWordAt_toTuple hy'))

/-! ## A realized tuple has a realized unlabelled support -/

private theorem word_surjective_of_mem_validWords_of_two_le
    {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (mult : α → ℕ) (hmult : ∀ a, 2 ≤ mult a)
    {w : Fin m → α} (hw : w ∈ validWords mult) :
    Function.Surjective w := by
  intro a
  have hcard :
      (Finset.univ.filter fun j => w j = a).card = mult a :=
    (Finset.mem_filter.mp hw).2 a
  have hpos :
      0 < (Finset.univ.filter fun j => w j = a).card := by
    rw [hcard]
    exact lt_of_lt_of_le (by omega) (hmult a)
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  exact ⟨j, (Finset.mem_filter.mp hj).2⟩

/-- The support of a realized tuple is exactly the image of its admissible
leaf embedding. -/
theorem tupleSupport_eq_leafEmbeddingImage_of_realizes
    {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {M m : ℕ}
    {y : Fin m → Z4}
    (hreal : RealizesTuple t Nm mu M y) :
    ∃ (z : HeppLeaf t → Z4) (w : Fin m → HeppLeaf t),
      IsAdmissible Nm M z ∧
      w ∈ validWords (leafMultiplicity mu) ∧
      (∀ j, y j = z (w j)) ∧
      tupleSupport y = leafEmbeddingImage z := by
  obtain ⟨z, w, hadm, hw, hy⟩ := hreal
  have hsurj : Function.Surjective w :=
    word_surjective_of_mem_validWords_of_two_le
      (leafMultiplicity mu) (fun l => mu.two_le l.1 l.2) hw
  refine ⟨z, w, hadm, hw, hy, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨j, _hj, hjx⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨w j, Finset.mem_univ _, (hy j).symm.trans hjx⟩
  · intro hx
    obtain ⟨l, _hl, hlx⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj⟩ := hsurj l
    exact Finset.mem_image.mpr
      ⟨j, Finset.mem_univ _, by
        rw [hy j, hj]
        exact hlx⟩

/-- Projection of paired realization data to its branch datum. -/
def pairedBranchData
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m) :
    BranchExponentData t (4 * M) :=
  d.1.1

/-- Projection of paired realization data to its canonical marking. -/
def pairedMarking
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m) :
    HeppMarking t :=
  d.1.toHeppMarking d.2.1

/-- Projection of paired realization data to its canonical multiplicities. -/
def pairedMultiplicities
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m) :
    Multiplicities t :=
  d.1.toMultiplicities d.2.1

/-- A support/word coordinate whose support is an unlabelled realized set for
the branch datum of `d`. -/
abbrev RealizedSupportWord
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m) :=
  Σ Z : {Z : Finset Z4 //
      Z ∈ realizedSets d.1.1 d.2.1.1},
    SupportWord m Z.1

instance instFintypeRealizedSupportWord
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m) :
    Fintype (RealizedSupportWord d) :=
  inferInstance

/-- Forget a realized support/word coordinate back to its lattice tuple. -/
def RealizedSupportWord.toTuple
    {t : PlaneTree} {M m : ℕ}
    {d : PairedValidRealizationData t M m}
    (p : RealizedSupportWord d) : Fin m → Z4 :=
  p.2.toTuple

/-- A tuple realized by `d` has an unlabelled support in the public
`realizedSets` carrier. -/
theorem tupleSupport_mem_realizedSets_of_pairedDataRealizes
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    {y : Fin m → Z4} (hy : PairedDataRealizes d y) :
    tupleSupport y ∈ realizedSets d.1.1 d.2.1.1 := by
  obtain ⟨z, w, hadm, hw, hyz, hsupport⟩ :=
    tupleSupport_eq_leafEmbeddingImage_of_realizes hy
  rw [mem_realizedSets_iff]
  refine ⟨z, ?_, hsupport.symm⟩
  exact hadm

/-- The canonical support/word coordinate of a tuple realized by `d`. -/
def pairedTupleCoordinate
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (y : Fin m → Z4) (hy : PairedDataRealizes d y) :
    RealizedSupportWord d :=
  ⟨⟨tupleSupport y,
      tupleSupport_mem_realizedSets_of_pairedDataRealizes d hy⟩,
    tupleWord y⟩

@[simp]
theorem pairedTupleCoordinate_toTuple
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (y : Fin m → Z4) (hy : PairedDataRealizes d y) :
    (pairedTupleCoordinate d y hy).toTuple = y :=
  rfl

/-- The support/word coordinate loses no information about the tuple. -/
theorem pairedTupleCoordinate_injective
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    {y y' : Fin m → Z4}
    (hy : PairedDataRealizes d y)
    (hy' : PairedDataRealizes d y')
    (h :
      pairedTupleCoordinate d y hy =
        pairedTupleCoordinate d y' hy') :
    y = y' := by
  exact (pairedTupleCoordinate_toTuple d y hy).symm.trans
    ((congrArg RealizedSupportWord.toTuple h).trans
      (pairedTupleCoordinate_toTuple d y' hy'))

/-! ## Exact finite image of an arbitrary fixed incidence fiber -/

/-- Image of a finite tuple family in unlabelled-support/word coordinates.
The hypothesis is local: every tuple in `Y` is incident to the one fixed
datum `d`. -/
def pairedFiberCoordinates
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (Y : Finset (Fin m → Z4))
    (hY : ∀ y ∈ Y, PairedDataRealizes d y) :
    Finset (RealizedSupportWord d) :=
  Y.attach.image fun y =>
    pairedTupleCoordinate d y.1 (hY y.1 y.2)

theorem pairedFiberCoordinateMap_injective
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (Y : Finset (Fin m → Z4))
    (hY : ∀ y ∈ Y, PairedDataRealizes d y) :
    Function.Injective
      (fun y : ↥Y =>
        pairedTupleCoordinate d y.1 (hY y.1 y.2)) := by
  intro y y' h
  apply Subtype.ext
  exact pairedTupleCoordinate_injective d
    (hY y.1 y.2) (hY y'.1 y'.2) h

/-- **Exact fixed-fiber reindexing.**  Any statistic on tuples can be summed
over the finite image of the support/word coordinate with no multiplicity
loss. -/
theorem sum_pairedFiberCoordinates
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (Y : Finset (Fin m → Z4))
    (hY : ∀ y ∈ Y, PairedDataRealizes d y)
    (F : (Fin m → Z4) → ℝ) :
    ∑ p ∈ pairedFiberCoordinates d Y hY, F p.toTuple =
      ∑ y ∈ Y, F y := by
  unfold pairedFiberCoordinates
  rw [Finset.sum_image
    (pairedFiberCoordinateMap_injective d Y hY).injOn]
  calc
    (∑ y ∈ Y.attach,
        F (pairedTupleCoordinate d y.1 (hY y.1 y.2)).toTuple) =
        ∑ y ∈ Y.attach, F y.1 := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [pairedTupleCoordinate_toTuple]
    _ = ∑ y ∈ Y, F y := Finset.sum_attach Y F

/-! ## Fixed-support words and a second exact Fubini decomposition -/

/-- Tuples in `Y` whose unlabelled support is exactly `Z`. -/
def tuplesAtSupport
    {m : ℕ} (Y : Finset (Fin m → Z4)) (Z : Finset Z4) :
    Finset (Fin m → Z4) :=
  Y.filter fun y => tupleSupport y = Z

@[simp]
theorem mem_tuplesAtSupport
    {m : ℕ} {Y : Finset (Fin m → Z4)} {Z : Finset Z4}
    {y : Fin m → Z4} :
    y ∈ tuplesAtSupport Y Z ↔
      y ∈ Y ∧ tupleSupport y = Z := by
  simp [tuplesAtSupport]

/-- Words over `Z` induced by the tuples in the corresponding support fiber. -/
def inducedWordsAtSupport
    {m : ℕ} (Y : Finset (Fin m → Z4)) (Z : Finset Z4) :
    Finset (SupportWord m Z) :=
  (tuplesAtSupport Y Z).attach.image fun y =>
    tupleWordAt (mem_tuplesAtSupport.mp y.2).2

theorem inducedWordMap_injective
    {m : ℕ} (Y : Finset (Fin m → Z4)) (Z : Finset Z4) :
    Function.Injective
      (fun y : ↥(tuplesAtSupport Y Z) =>
        tupleWordAt (mem_tuplesAtSupport.mp y.2).2) := by
  intro y y' h
  apply Subtype.ext
  exact tupleWordAt_injective
    (mem_tuplesAtSupport.mp y.2).2
    (mem_tuplesAtSupport.mp y'.2).2 h

/-- Reindex one fixed-support fiber by its actual finite word image. -/
theorem sum_inducedWordsAtSupport
    {m : ℕ} (Y : Finset (Fin m → Z4)) (Z : Finset Z4)
    (F : (Fin m → Z4) → ℝ) :
    ∑ w ∈ inducedWordsAtSupport Y Z, F w.toTuple =
      ∑ y ∈ tuplesAtSupport Y Z, F y := by
  unfold inducedWordsAtSupport
  rw [Finset.sum_image (inducedWordMap_injective Y Z).injOn]
  calc
    (∑ y ∈ (tuplesAtSupport Y Z).attach,
        F (tupleWordAt
          (mem_tuplesAtSupport.mp y.2).2).toTuple) =
        ∑ y ∈ (tuplesAtSupport Y Z).attach, F y.1 := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [tupleWordAt_toTuple]
    _ = ∑ y ∈ tuplesAtSupport Y Z, F y :=
      Finset.sum_attach (tuplesAtSupport Y Z) F

/-! ## The induced multiplicity profile on one support -/

/-- Multiplicity of one support value in a support word. -/
def supportWordMultiplicity
    {m : ℕ} {Z : Finset Z4} (w : SupportWord m Z)
    (x : {x // x ∈ Z}) : ℕ :=
  (Finset.univ.filter fun j => w j = x).card

/-- Words induced from the exact support fiber hit every element of `Z`. -/
theorem tupleSupport_toTuple_eq_of_mem_inducedWordsAtSupport
    {m : ℕ} {Y : Finset (Fin m → Z4)} {Z : Finset Z4}
    {w : SupportWord m Z}
    (hw : w ∈ inducedWordsAtSupport Y Z) :
    tupleSupport w.toTuple = Z := by
  obtain ⟨y, hy, hwy⟩ := Finset.mem_image.mp hw
  have hsupport :=
    (mem_tuplesAtSupport.mp y.2).2
  rw [← hwy, tupleWordAt_toTuple]
  exact hsupport

/-- The positive assignment induced by a support word which hits all of its
support. -/
def supportWordProfile
    {m : ℕ} {Z : Finset Z4} (w : SupportWord m Z)
    (hrange : tupleSupport w.toTuple = Z) :
    PositiveAssignment {x // x ∈ Z} m where
  val := fun x =>
    ⟨supportWordMultiplicity w x, by
      unfold supportWordMultiplicity
      apply Nat.lt_succ_of_le
      calc
        (Finset.univ.filter fun j => w j = x).card ≤
            (Finset.univ : Finset (Fin m)).card :=
          Finset.card_filter_le _ _
        _ = m := by simp⟩
  property := by
    constructor
    · intro x
      have hxZ : x.1 ∈ tupleSupport w.toTuple := by
        rw [hrange]
        exact x.2
      obtain ⟨j, hj⟩ := mem_tupleSupport.mp hxZ
      have hj' : w j = x := by
        apply Subtype.ext
        exact hj
      unfold supportWordMultiplicity
      rw [Finset.card_pos]
      exact ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hj'⟩⟩
    · change
        ∑ x : {x // x ∈ Z},
            (Finset.univ.filter fun j => w j = x).card = m
      calc
        ∑ x : {x // x ∈ Z},
            (Finset.univ.filter fun j => w j = x).card =
            (Finset.univ : Finset (Fin m)).card := by
          symm
          exact Finset.card_eq_sum_card_fiberwise
            (f := w) (t := Finset.univ)
            (fun _ _ => Finset.mem_univ _)
        _ = m := by simp

/-- Profile predicate independent of the proof that a word hits `Z`. -/
def SupportWord.HasProfile
    {m : ℕ} {Z : Finset Z4} (w : SupportWord m Z)
    (p : PositiveAssignment {x // x ∈ Z} m) : Prop :=
  ∀ x, supportWordMultiplicity w x = (p.1 x).1

noncomputable instance instDecidableSupportWordHasProfile
    {m : ℕ} {Z : Finset Z4} (w : SupportWord m Z)
    (p : PositiveAssignment {x // x ∈ Z} m) :
    Decidable (w.HasProfile p) :=
  Classical.propDecidable _

theorem supportWordProfile_hasProfile
    {m : ℕ} {Z : Finset Z4} (w : SupportWord m Z)
    (hrange : tupleSupport w.toTuple = Z) :
    w.HasProfile (supportWordProfile w hrange) := by
  intro x
  rfl

/-- Words in one realized-support fiber having the prescribed induced
multiplicity assignment `p`. -/
def inducedWordsAtProfile
    {m : ℕ} (Y : Finset (Fin m → Z4)) (Z : Finset Z4)
    (p : PositiveAssignment {x // x ∈ Z} m) :
    Finset (SupportWord m Z) :=
  (inducedWordsAtSupport Y Z).filter fun w => w.HasProfile p

/-- Exact second Fubini decomposition by the induced multiplicity assignment
`χ` from paper (5.8)--(5.9). -/
theorem sum_inducedWords_eq_sum_profiles
    {m : ℕ} (Y : Finset (Fin m → Z4)) (Z : Finset Z4)
    (F : SupportWord m Z → ℝ) :
    ∑ w ∈ inducedWordsAtSupport Y Z, F w =
      ∑ p : PositiveAssignment {x // x ∈ Z} m,
        ∑ w ∈ inducedWordsAtProfile Y Z p, F w := by
  classical
  symm
  unfold inducedWordsAtProfile
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  let p : PositiveAssignment {x // x ∈ Z} m :=
    supportWordProfile w
      (tupleSupport_toTuple_eq_of_mem_inducedWordsAtSupport hw)
  rw [Finset.sum_eq_single p]
  · simp [p, supportWordProfile_hasProfile]
  · intro p' hp' hne
    have hnot : ¬w.HasProfile p' := by
      intro hprofile
      apply hne
      apply Subtype.ext
      funext x
      apply Fin.ext
      exact (hprofile x).symm.trans
        (supportWordProfile_hasProfile w
          (tupleSupport_toTuple_eq_of_mem_inducedWordsAtSupport hw) x)
    simp [hnot]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ p))

/-- There are at most `2^m` possible induced profiles, uniformly in the
size and labelling of the support. -/
theorem card_positiveAssignments_support_le_two_pow
    (m : ℕ) (Z : Finset Z4) :
    Fintype.card (PositiveAssignment {x // x ∈ Z} m) ≤
      2 ^ m :=
  PositiveAssignment.card_le_two_pow m

/-! ## Every induced word carries a genuine leaf realization -/

/-- A support word is induced by the fixed paired datum `d` when it is the
value word of one admissible leaf embedding with the prescribed leaf
multiplicities. -/
def SupportWord.IsInducedBy
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    {Z : Finset Z4} (w : SupportWord m Z) : Prop :=
  ∃ (z : HeppLeaf t → Z4)
      (u : Fin m → HeppLeaf t),
    IsAdmissible (pairedMarking d) M z ∧
      u ∈ validWords
        (leafMultiplicity (pairedMultiplicities d)) ∧
      leafEmbeddingImage z = Z ∧
      ∀ j, (w j).1 = z (u j)

/-- Every word in the exact fixed-incidence image has a genuine admissible
leaf realization; this is the local witness needed to invoke Proposition
5.7 after grouping by profile. -/
theorem SupportWord.isInducedBy_of_mem_inducedWordsAtSupport
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (Y : Finset (Fin m → Z4))
    (hY : ∀ y ∈ Y, PairedDataRealizes d y)
    {Z : Finset Z4} {w : SupportWord m Z}
    (hw : w ∈ inducedWordsAtSupport Y Z) :
    w.IsInducedBy d := by
  obtain ⟨y, hy, hwy⟩ := Finset.mem_image.mp hw
  have hyY : y.1 ∈ Y :=
    (mem_tuplesAtSupport.mp y.2).1
  have hsupport : tupleSupport y.1 = Z :=
    (mem_tuplesAtSupport.mp y.2).2
  obtain ⟨z, u, hadm, hu, hyu, himage⟩ :=
    tupleSupport_eq_leafEmbeddingImage_of_realizes
      (hY y.1 hyY)
  refine ⟨z, u, hadm, hu, ?_, ?_⟩
  · exact himage.symm.trans hsupport
  · intro j
    have hval :=
      congrArg (fun v : SupportWord m Z => (v j).1) hwy
    simpa only [tupleWordAt] using hval.symm.trans (hyu j)

/-- An injective leaf embedding whose image is `Z` gives an equivalence from
the labelled leaves to the unlabelled support. -/
noncomputable def leafEquivSupport
    {t : PlaneTree} {Z : Finset Z4}
    (z : HeppLeaf t → Z4) (hz : Function.Injective z)
    (himage : leafEmbeddingImage z = Z) :
    HeppLeaf t ≃ {x // x ∈ Z} :=
  Equiv.ofBijective
    (fun l => ⟨z l, by
      rw [← himage]
      exact Finset.mem_image.mpr
        ⟨l, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun _ _ h => hz (congrArg Subtype.val h), by
      intro x
      have hx : x.1 ∈ leafEmbeddingImage z := by
        rw [himage]
        exact x.2
      obtain ⟨l, _hl, hl⟩ := Finset.mem_image.mp hx
      refine ⟨l, Subtype.ext ?_⟩
      exact hl⟩

@[simp]
theorem leafEquivSupport_apply_val
    {t : PlaneTree} {Z : Finset Z4}
    (z : HeppLeaf t → Z4) (hz : Function.Injective z)
    (himage : leafEmbeddingImage z = Z)
    (l : HeppLeaf t) :
    ((leafEquivSupport z hz himage) l).1 = z l :=
  rfl

/-- Under a genuine leaf realization, the support multiplicity profile is
the leaf multiplicity function transported along the leaf/support
equivalence. -/
theorem supportWordMultiplicity_eq_leafMultiplicity
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    {Z : Finset Z4} (w : SupportWord m Z)
    {z : HeppLeaf t → Z4} {u : Fin m → HeppLeaf t}
    (hadm : IsAdmissible (pairedMarking d) M z)
    (hu : u ∈ validWords
      (leafMultiplicity (pairedMultiplicities d)))
    (himage : leafEmbeddingImage z = Z)
    (hwu : ∀ j, (w j).1 = z (u j))
    (x : {x // x ∈ Z}) :
    supportWordMultiplicity w x =
      leafMultiplicity (pairedMultiplicities d)
        ((leafEquivSupport z hadm.inj himage).symm x) := by
  let e := leafEquivSupport z hadm.inj himage
  have hex :
      x.1 = z (e.symm x) := by
    calc
      x.1 = (e (e.symm x)).1 :=
        congrArg Subtype.val (e.apply_symm_apply x).symm
      _ = z (e.symm x) := by
        exact leafEquivSupport_apply_val
          z hadm.inj himage (e.symm x)
  have hfiber :
      (Finset.univ.filter fun j => w j = x) =
        Finset.univ.filter fun j => u j = e.symm x := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      apply hadm.inj
      rw [← hwu j, congrArg Subtype.val hj, hex]
    · intro hj
      apply Subtype.ext
      rw [hwu j, hj, ← hex]
  unfold supportWordMultiplicity
  rw [hfiber]
  exact (Finset.mem_filter.mp hu).2 (e.symm x)

/-- Reindex a support word by a leaf/support equivalence. -/
def reindexSupportWord
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    (w : SupportWord m Z) : Fin m → HeppLeaf t :=
  fun j => e.symm (w j)

theorem reindexSupportWord_injective
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z}) :
    Function.Injective (reindexSupportWord (m := m) e) := by
  intro w w' h
  funext j
  apply e.symm.injective
  exact congrFun h j

/-- Fiber cardinality after reindexing a support word to the leaf alphabet. -/
theorem reindexSupportWord_fiber_card
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    (w : SupportWord m Z) (l : HeppLeaf t) :
    (Finset.univ.filter fun j =>
      reindexSupportWord e w j = l).card =
        supportWordMultiplicity w (e l) := by
  unfold supportWordMultiplicity
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    simpa [reindexSupportWord] using congrArg e h
  · intro h
    simpa [reindexSupportWord] using congrArg e.symm h

/-- Fixing one realized word in a profile identifies that profile with the
fixed datum's labelled leaf multiplicities.  Every other word with the same
profile therefore reindexes to a `validWords` word on the leaves. -/
theorem reindexSupportWord_mem_validWords_of_sameProfile
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    {Z : Finset Z4}
    (p : PositiveAssignment {x // x ∈ Z} m)
    (w₀ w : SupportWord m Z)
    (hw₀profile : w₀.HasProfile p)
    (hwprofile : w.HasProfile p)
    {z : HeppLeaf t → Z4} {u₀ : Fin m → HeppLeaf t}
    (hadm : IsAdmissible (pairedMarking d) M z)
    (hu₀ : u₀ ∈ validWords
      (leafMultiplicity (pairedMultiplicities d)))
    (himage : leafEmbeddingImage z = Z)
    (hw₀u : ∀ j, (w₀ j).1 = z (u₀ j)) :
    reindexSupportWord
        (leafEquivSupport z hadm.inj himage) w ∈
      validWords (leafMultiplicity (pairedMultiplicities d)) := by
  rw [validWords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro l
  let e := leafEquivSupport z hadm.inj himage
  rw [reindexSupportWord_fiber_card e w l]
  calc
    supportWordMultiplicity w (e l) =
        (p.1 (e l)).1 := hwprofile (e l)
    _ = supportWordMultiplicity w₀ (e l) :=
      (hw₀profile (e l)).symm
    _ = leafMultiplicity (pairedMultiplicities d)
          (e.symm (e l)) := by
      exact supportWordMultiplicity_eq_leafMultiplicity
        d w₀ hadm hu₀ himage hw₀u (e l)
    _ = leafMultiplicity (pairedMultiplicities d) l := by
      rw [e.symm_apply_apply]

/-! ## Pairing primitivity and the chain weight survive the reindexing -/

/-- The adjacent-chain product read directly on a support word. -/
def supportChainWeight
    {m : ℕ} {Z : Finset Z4} (w : SupportWord m Z) : ℝ :=
  ∏ j : AdjacentIndex m,
    latticeEdgeWeight (w j.1).1 (w (adjacentSucc j)).1

theorem supportChainWeight_nonneg
    {m : ℕ} {Z : Finset Z4} (w : SupportWord m Z) :
    0 ≤ supportChainWeight w := by
  unfold supportChainWeight
  exact Finset.prod_nonneg fun j _ =>
    latticeEdgeWeight_nonneg _ _

/-- Reading pairing compatibility before or after forgetting support proofs
is equivalent. -/
theorem supportWord_respectsWord_iff_toTuple
    {m : ℕ} {Z : Finset Z4}
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (w : SupportWord m Z) :
    RespectsWord A w κ ↔ RespectsWord A w.toTuple κ := by
  constructor
  · intro h j
    exact congrArg Subtype.val (h j)
  · intro h j
    apply Subtype.ext
    exact h j

/-- If the original tuple family respects one across pairing, every induced
support word respects it as well. -/
theorem SupportWord.respectsWord_of_mem_inducedWordsAtSupport
    {m : ℕ} {Y : Finset (Fin m → Z4)}
    {Z : Finset Z4} {w : SupportWord m Z}
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (hY : ∀ y ∈ Y, RespectsWord A y κ)
    (hw : w ∈ inducedWordsAtSupport Y Z) :
    RespectsWord A w κ := by
  obtain ⟨y, hy, hwy⟩ := Finset.mem_image.mp hw
  have hyY : y.1 ∈ Y :=
    (mem_tuplesAtSupport.mp y.2).1
  rw [supportWord_respectsWord_iff_toTuple]
  have htuple : w.toTuple = y.1 := by
    rw [← hwy, tupleWordAt_toTuple]
  rw [htuple]
  exact hY y.1 hyY

/-- A leaf realization reads the same adjacent-chain product as its support
word. -/
theorem supportChainWeight_eq_heppChainWeight
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (w : SupportWord m Z) (z : HeppLeaf t → Z4)
    (u : Fin m → HeppLeaf t)
    (hwu : ∀ j, (w j).1 = z (u j)) :
    supportChainWeight w = heppChainWeight z u := by
  unfold supportChainWeight heppChainWeight
  apply Finset.prod_congr rfl
  intro j hj
  rw [hwu j.1, hwu (adjacentSucc j)]

/-- Renaming the support alphabet along an equivalence preserves
compatibility with a fixed across pairing. -/
theorem reindexSupportWord_respectsWord
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (w : SupportWord m Z)
    (hw : RespectsWord A w κ) :
    RespectsWord A (reindexSupportWord e w) κ := by
  intro j
  exact congrArg e.symm (hw j)

/-- If an alphabet equivalence is induced by an embedding `z`, reindexing
does not change the adjacent-chain product. -/
theorem supportChainWeight_eq_heppChainWeight_reindex
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    (w : SupportWord m Z) (z : HeppLeaf t → Z4)
    (he : ∀ l, (e l).1 = z l) :
    supportChainWeight w =
      heppChainWeight z (reindexSupportWord e w) := by
  apply supportChainWeight_eq_heppChainWeight
  intro j
  calc
    (w j).1 = (e (e.symm (w j))).1 :=
      congrArg Subtype.val (e.apply_symm_apply (w j)).symm
    _ = z (e.symm (w j)) := he (e.symm (w j))

/-- A primitive across pairing on the support word transports through an
injective admissible embedding to the paper's primitive leaf-word condition
(5.11)(c). -/
theorem SupportWord.exists_primitiveLeafRealization
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    {Z : Finset Z4} (w : SupportWord m Z)
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (hinduced : w.IsInducedBy d)
    (hrespects : RespectsWord A w κ)
    (hprimitive : IsPrimitiveAcross A κ) :
    ∃ (z : HeppLeaf t → Z4)
        (u : Fin m → HeppLeaf t),
      IsAdmissible (pairedMarking d) M z ∧
        u ∈ validWords
          (leafMultiplicity (pairedMultiplicities d)) ∧
        leafEmbeddingImage z = Z ∧
        (∀ j, (w j).1 = z (u j)) ∧
        NoProperLeafBlock u ∧
        supportChainWeight w = heppChainWeight z u := by
  obtain ⟨z, u, hadm, hu, himage, hwu⟩ := hinduced
  have hurespects : RespectsWord A u κ := by
    intro j
    apply hadm.inj
    rw [← hwu j.1, ← hwu (κ j).1]
    exact congrArg Subtype.val (hrespects j)
  refine ⟨z, u, hadm, hu, himage, hwu,
    noProperLeafBlock_of_primitive_across
      hprimitive hurespects, ?_⟩
  exact supportChainWeight_eq_heppChainWeight w z u hwu

/-- A raw restricted word sum is no larger than its factorial-ledger
counterpart when the summand is nonnegative. -/
theorem wordSumFiltered_le_paperSumFiltered_of_nonneg
    {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (mult : α → ℕ)
    (P : (Fin m → α) → Prop) [DecidablePred P]
    (F : (Fin m → α) → ℝ)
    (hF : ∀ w, 0 ≤ F w) :
    wordSumFiltered mult P F ≤ paperSumFiltered mult P F := by
  have hsum : 0 ≤ wordSumFiltered mult P F := by
    unfold wordSumFiltered
    exact Finset.sum_nonneg fun w _ => hF w
  have hfactor :
      (1 : ℝ) ≤ ∏ a : α, ((mult a).factorial : ℝ) := by
    apply Finset.one_le_prod
    intro a ha
    exact_mod_cast
      (Nat.succ_le_iff.mpr (Nat.factorial_pos (mult a)))
  unfold paperSumFiltered
  calc
    wordSumFiltered mult P F =
        1 * wordSumFiltered mult P F := by ring
    _ ≤ (∏ a : α, ((mult a).factorial : ℝ)) *
          wordSumFiltered mult P F :=
      mul_le_mul_of_nonneg_right hfactor hsum

/-- The explicit right-hand side of Proposition 5.7 is nonnegative for a
nonnegative constant. -/
theorem permSumRHS_nonneg
    {C : ℝ} (hC : 0 ≤ C) (n : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    0 ≤ permSumRHS C n t Nm mu := by
  unfold permSumRHS
  refine mul_nonneg (pow_nonneg hC n) ?_
  apply Finset.sum_nonneg
  intro W hW
  have hsqrt :
      0 ≤ ∏ l : HeppLeaf t,
        sqrtFactorial (leafMultiplicity mu l) := by
    apply Finset.prod_nonneg
    intro l hl
    exact Real.sqrt_nonneg _
  have hbranch :
      0 ≤ ∏ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ^
          ((-4 : ℤ) * (((childrenOf v).card : ℤ) - 1)) := by
    apply Finset.prod_nonneg
    intro v hv
    exact zpow_nonneg (Nat.cast_nonneg _) _
  have hroot :
      0 ≤ (scaleN Nm (rootV t) : ℝ) ^ (-2 : ℤ) :=
    zpow_nonneg (Nat.cast_nonneg _) _
  have hratio :
      0 ≤ ∏ v ∈ (nonrootBranches t) \ W,
        parentScaleRatio Nm v := by
    apply Finset.prod_nonneg
    intro v hv
    unfold parentScaleRatio
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  positivity

/-- The exponential profile count is absorbed by multiplying the absolute
constant in Proposition 5.7 by four. -/
theorem two_pow_two_mul_permSumRHS
    (C : ℝ) (n : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    ((2 ^ (2 * n) : ℕ) : ℝ) *
        permSumRHS C n t Nm mu =
      permSumRHS (4 * C) n t Nm mu := by
  have hpow :
      ((2 ^ (2 * n) : ℕ) : ℝ) = (4 : ℝ) ^ n := by
    norm_num [pow_mul]
  unfold permSumRHS
  rw [hpow, mul_pow]
  ring

/-- **Fixed-profile bridge to the primitive word sum.**

Choose any realized word in a nonempty profile fiber.  Its admissible leaf
embedding identifies the unlabelled support with the labelled leaves.
Every other word in the profile then reindexes injectively into the paper's
`validWords` carrier, and primitivity supplies condition (5.11)(c).  Hence
the whole fixed-profile chain sum is bounded by the restricted word sum
appearing immediately before Proposition 5.7. -/
theorem sum_inducedWordsAtProfile_chainWeight_le_wordSumFiltered
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (Y : Finset (Fin m → Z4))
    {Z : Finset Z4}
    (p : PositiveAssignment {x // x ∈ Z} m)
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y)
    (hYrespect : ∀ y ∈ Y, RespectsWord A y κ)
    (hprimitive : IsPrimitiveAcross A κ)
    (hne : (inducedWordsAtProfile Y Z p).Nonempty) :
    ∃ z : HeppLeaf t → Z4,
      IsAdmissible (pairedMarking d) M z ∧
      leafEmbeddingImage z = Z ∧
      (∑ w ∈ inducedWordsAtProfile Y Z p,
          supportChainWeight w) ≤
        wordSumFiltered (M := m)
          (leafMultiplicity (pairedMultiplicities d))
          NoProperLeafBlock (heppChainWeight z) := by
  classical
  obtain ⟨w₀, hw₀⟩ := hne
  have hw₀support :
      w₀ ∈ inducedWordsAtSupport Y Z :=
    (Finset.mem_filter.mp hw₀).1
  have hw₀profile : w₀.HasProfile p :=
    (Finset.mem_filter.mp hw₀).2
  obtain ⟨z, u₀, hadm, hu₀, himage, hw₀u⟩ :=
    SupportWord.isInducedBy_of_mem_inducedWordsAtSupport
      d Y hYreal hw₀support
  let e : HeppLeaf t ≃ {x // x ∈ Z} :=
    leafEquivSupport z hadm.inj himage
  have hsubset :
      (inducedWordsAtProfile Y Z p).image
          (reindexSupportWord e) ⊆
        (validWords
          (leafMultiplicity (pairedMultiplicities d))).filter
            NoProperLeafBlock := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    have hwsupport :
        w ∈ inducedWordsAtSupport Y Z :=
      (Finset.mem_filter.mp hw).1
    have hwprofile : w.HasProfile p :=
      (Finset.mem_filter.mp hw).2
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · exact reindexSupportWord_mem_validWords_of_sameProfile
        d p w₀ w hw₀profile hwprofile hadm hu₀ himage hw₀u
    · apply noProperLeafBlock_of_primitive_across hprimitive
      apply reindexSupportWord_respectsWord e A κ w
      exact SupportWord.respectsWord_of_mem_inducedWordsAtSupport
        A κ hYrespect hwsupport
  refine ⟨z, hadm, himage, ?_⟩
  calc
    (∑ w ∈ inducedWordsAtProfile Y Z p,
        supportChainWeight w) =
        ∑ w ∈ inducedWordsAtProfile Y Z p,
          heppChainWeight z (reindexSupportWord e w) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact supportChainWeight_eq_heppChainWeight_reindex
        e w z (fun l =>
          leafEquivSupport_apply_val z hadm.inj himage l)
    _ = ∑ u ∈
          (inducedWordsAtProfile Y Z p).image
            (reindexSupportWord e),
          heppChainWeight z u := by
      rw [Finset.sum_image
        (reindexSupportWord_injective e).injOn]
    _ ≤ ∑ u ∈
          (validWords
            (leafMultiplicity (pairedMultiplicities d))).filter
              NoProperLeafBlock,
          heppChainWeight z u := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun u _ _ => heppChainWeight_nonneg z u)
    _ = wordSumFiltered (M := m)
          (leafMultiplicity (pairedMultiplicities d))
          NoProperLeafBlock (heppChainWeight z) := rfl

/-- **Paper (5.8)--(5.11), fixed-profile analytic bound.**

For total length `2n`, the preceding exact reindexing feeds directly into
Proposition 5.7.  Validity and parity are read from the paired realization
datum itself, so the only remaining assumptions are precisely P-5.7's tree
hypotheses and the nonempty primitive profile fiber. -/
theorem sum_inducedWordsAtProfile_chainWeight_le_permSumRHS
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    {Z : Finset Z4}
    (p : PositiveAssignment {x // x ∈ Z} (2 * n))
    (A : Finset (Fin (2 * n))) (κ : AcrossPairing A)
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y)
    (hYrespect : ∀ y ∈ Y, RespectsWord A y κ)
    (hprimitive : IsPrimitiveAcross A κ)
    (hne : (inducedWordsAtProfile Y Z p).Nonempty) :
    ∃ z : HeppLeaf t → Z4,
      IsAdmissible (pairedMarking d) M z ∧
      leafEmbeddingImage z = Z ∧
      (∑ w ∈ inducedWordsAtProfile Y Z p,
          supportChainWeight w) ≤
        permSumRHS C n t (pairedMarking d)
          (pairedMultiplicities d) := by
  obtain ⟨z, hadm, himage, hprofile⟩ :=
    sum_inducedWordsAtProfile_chainWeight_le_wordSumFiltered
      d Y p A κ hYreal hYrespect hprimitive hne
  refine ⟨z, hadm, himage, hprofile.trans ?_⟩
  have htotal :
      totalMultiplicity (pairedMultiplicities d) = 2 * n := by
    exact RealizationData.toMultiplicities_total d.1 d.2.1
  have heven :
      ∀ l : HeppLeaf t,
        Even (leafMultiplicity (pairedMultiplicities d) l) := by
    intro l
    exact RealizationData.toMultiplicities_even
      d.1 d.2.1 d.2.2 l
  calc
    wordSumFiltered
          (leafMultiplicity (pairedMultiplicities d))
          NoProperLeafBlock (heppChainWeight z) ≤
        paperSumFiltered
          (leafMultiplicity (pairedMultiplicities d))
          NoProperLeafBlock (heppChainWeight z) :=
      wordSumFiltered_le_paperSumFiltered_of_nonneg
        (leafMultiplicity (pairedMultiplicities d))
        NoProperLeafBlock (heppChainWeight z)
        (heppChainWeight_nonneg z)
    _ = paperSum (M := 2 * n)
          (leafMultiplicity (pairedMultiplicities d))
          (primitiveChainWeight (m := 2 * n) z) :=
      (paperSum_primitiveChainWeight
        (pairedMultiplicities d) z).symm
    _ ≤ permSumRHS C n t (pairedMarking d)
          (pairedMultiplicities d) :=
      hC.2 n M t (pairedMarking d)
        (pairedMultiplicities d) z hn ht hroot
        htotal heven hadm

/-- Empty profile fibers satisfy the same bound trivially; nonempty fibers
use the genuine embedding extracted above. -/
theorem sum_inducedWordsAtProfile_chainWeight_le_permSumRHS_unconditional
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    {Z : Finset Z4}
    (p : PositiveAssignment {x // x ∈ Z} (2 * n))
    (A : Finset (Fin (2 * n))) (κ : AcrossPairing A)
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y)
    (hYrespect : ∀ y ∈ Y, RespectsWord A y κ)
    (hprimitive : IsPrimitiveAcross A κ) :
    (∑ w ∈ inducedWordsAtProfile Y Z p,
        supportChainWeight w) ≤
      permSumRHS C n t (pairedMarking d)
        (pairedMultiplicities d) := by
  classical
  by_cases hne : (inducedWordsAtProfile Y Z p).Nonempty
  · obtain ⟨z, hadm, himage, hbound⟩ :=
      sum_inducedWordsAtProfile_chainWeight_le_permSumRHS
        hC d Y p A κ hn ht hroot hYreal hYrespect
        hprimitive hne
    exact hbound
  · have hempty :
        inducedWordsAtProfile Y Z p = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.sum_empty]
    exact permSumRHS_nonneg (le_of_lt hC.1) n t
      (pairedMarking d) (pairedMultiplicities d)

/-- Summing over all induced profiles costs at most `2^(2n)`, the exact
profile-count loss from (5.9). -/
theorem sum_profiles_chainWeight_le_two_pow_mul_permSumRHS
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    (Z : Finset Z4)
    (A : Finset (Fin (2 * n))) (κ : AcrossPairing A)
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y)
    (hYrespect : ∀ y ∈ Y, RespectsWord A y κ)
    (hprimitive : IsPrimitiveAcross A κ) :
    (∑ p : PositiveAssignment {x // x ∈ Z} (2 * n),
        ∑ w ∈ inducedWordsAtProfile Y Z p,
          supportChainWeight w) ≤
      ((2 ^ (2 * n) : ℕ) : ℝ) *
        permSumRHS C n t (pairedMarking d)
          (pairedMultiplicities d) := by
  classical
  have hRHS :
      0 ≤ permSumRHS C n t (pairedMarking d)
        (pairedMultiplicities d) :=
    permSumRHS_nonneg (le_of_lt hC.1) n t
      (pairedMarking d) (pairedMultiplicities d)
  have hcard :
      ((Fintype.card
        (PositiveAssignment {x // x ∈ Z} (2 * n)) : ℕ) : ℝ) ≤
        ((2 ^ (2 * n) : ℕ) : ℝ) := by
    exact_mod_cast
      card_positiveAssignments_support_le_two_pow (2 * n) Z
  calc
    (∑ p : PositiveAssignment {x // x ∈ Z} (2 * n),
        ∑ w ∈ inducedWordsAtProfile Y Z p,
          supportChainWeight w) ≤
        ∑ p : PositiveAssignment {x // x ∈ Z} (2 * n),
          permSumRHS C n t (pairedMarking d)
            (pairedMultiplicities d) := by
      apply Finset.sum_le_sum
      intro p hp
      exact
        sum_inducedWordsAtProfile_chainWeight_le_permSumRHS_unconditional
          hC d Y p A κ hn ht hroot hYreal hYrespect hprimitive
    _ = ((Fintype.card
          (PositiveAssignment {x // x ∈ Z} (2 * n)) : ℕ) : ℝ) *
          permSumRHS C n t (pairedMarking d)
            (pairedMultiplicities d) := by
      simp
    _ ≤ ((2 ^ (2 * n) : ℕ) : ℝ) *
          permSumRHS C n t (pairedMarking d)
            (pairedMultiplicities d) :=
      mul_le_mul_of_nonneg_right hcard hRHS

/-- The complete fixed-support word fiber, after summing away the profile
coordinate, is controlled by the same `2^(2n)` loss. -/
theorem sum_inducedWordsAtSupport_chainWeight_le_two_pow_mul_permSumRHS
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    (Z : Finset Z4)
    (A : Finset (Fin (2 * n))) (κ : AcrossPairing A)
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y)
    (hYrespect : ∀ y ∈ Y, RespectsWord A y κ)
    (hprimitive : IsPrimitiveAcross A κ) :
    (∑ w ∈ inducedWordsAtSupport Y Z,
        supportChainWeight w) ≤
      ((2 ^ (2 * n) : ℕ) : ℝ) *
        permSumRHS C n t (pairedMarking d)
          (pairedMultiplicities d) := by
  rw [sum_inducedWords_eq_sum_profiles Y Z
    (fun w => supportChainWeight w)]
  exact sum_profiles_chainWeight_le_two_pow_mul_permSumRHS
    hC d Y Z A κ hn ht hroot hYreal hYrespect hprimitive

/-- Constant-absorbed form of the complete fixed-support estimate.  This is
the statement consumed by the outer realized-set summation: all profile
bookkeeping has disappeared into the replacement `C ↦ 4C`. -/
theorem sum_inducedWordsAtSupport_chainWeight_le_permSumRHS_four_mul
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    (Z : Finset Z4)
    (A : Finset (Fin (2 * n))) (κ : AcrossPairing A)
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y)
    (hYrespect : ∀ y ∈ Y, RespectsWord A y κ)
    (hprimitive : IsPrimitiveAcross A κ) :
    (∑ w ∈ inducedWordsAtSupport Y Z,
        supportChainWeight w) ≤
      permSumRHS (4 * C) n t (pairedMarking d)
        (pairedMultiplicities d) := by
  calc
    (∑ w ∈ inducedWordsAtSupport Y Z,
        supportChainWeight w) ≤
      ((2 ^ (2 * n) : ℕ) : ℝ) *
        permSumRHS C n t (pairedMarking d)
          (pairedMultiplicities d) :=
      sum_inducedWordsAtSupport_chainWeight_le_two_pow_mul_permSumRHS
        hC d Y Z A κ hn ht hroot hYreal hYrespect hprimitive
    _ = permSumRHS (4 * C) n t (pairedMarking d)
          (pairedMultiplicities d) :=
      two_pow_two_mul_permSumRHS C n t
        (pairedMarking d) (pairedMultiplicities d)

/-- Exact grouping of a finite tuple family by unlabelled support, provided
every occurring support belongs to the chosen finite support carrier. -/
theorem sum_eq_sum_tuplesAtSupport
    {m : ℕ} (Y : Finset (Fin m → Z4))
    (S : Finset (Finset Z4))
    (hS : ∀ y ∈ Y, tupleSupport y ∈ S)
    (F : (Fin m → Z4) → ℝ) :
    ∑ y ∈ Y, F y =
      ∑ Z ∈ S, ∑ y ∈ tuplesAtSupport Y Z, F y := by
  classical
  symm
  unfold tuplesAtSupport
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_eq_single (tupleSupport y)]
  · simp
  · intro Z hZ hne
    simp [hne.symm]
  · intro hnot
    exact False.elim (hnot (hS y hy))

/-- **Paper (5.8)--(5.11), carrier-level finite Fubini.**

A fixed paired incidence fiber is first grouped by its unlabelled realized
set and then reindexed by the actual words occurring over that set.  The
equality is exact for every statistic `F`; neither automorphism factors nor
factorial bounds have entered yet. -/
theorem sum_pairedFiber_eq_realizedSets_words
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (Y : Finset (Fin m → Z4))
    (hY : ∀ y ∈ Y, PairedDataRealizes d y)
    (F : (Fin m → Z4) → ℝ) :
    ∑ y ∈ Y, F y =
      ∑ Z ∈ realizedSets d.1.1 d.2.1.1,
        ∑ w ∈ inducedWordsAtSupport Y Z, F w.toTuple := by
  calc
    ∑ y ∈ Y, F y =
        ∑ Z ∈ realizedSets d.1.1 d.2.1.1,
          ∑ y ∈ tuplesAtSupport Y Z, F y :=
      sum_eq_sum_tuplesAtSupport Y
        (realizedSets d.1.1 d.2.1.1)
        (fun y hy =>
          tupleSupport_mem_realizedSets_of_pairedDataRealizes
            d (hY y hy))
        F
    _ = ∑ Z ∈ realizedSets d.1.1 d.2.1.1,
          ∑ w ∈ inducedWordsAtSupport Y Z, F w.toTuple := by
      apply Finset.sum_congr rfl
      intro Z hZ
      rw [sum_inducedWordsAtSupport]

/-- **Full carrier decomposition through the paper's `χ` parameter.**

This is the exact three-level finite sum over an unlabelled realized set,
a positive multiplicity assignment on that set, and the words with that
assignment.  The preceding exponential cardinality theorem bounds the
middle carrier by `2^m`. -/
theorem sum_pairedFiber_eq_realizedSets_profiles_words
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (Y : Finset (Fin m → Z4))
    (hY : ∀ y ∈ Y, PairedDataRealizes d y)
    (F : (Fin m → Z4) → ℝ) :
    ∑ y ∈ Y, F y =
      ∑ Z ∈ realizedSets d.1.1 d.2.1.1,
        ∑ p : PositiveAssignment {x // x ∈ Z} m,
          ∑ w ∈ inducedWordsAtProfile Y Z p,
            F w.toTuple := by
  rw [sum_pairedFiber_eq_realizedSets_words d Y hY F]
  apply Finset.sum_congr rfl
  intro Z hZ
  exact sum_inducedWords_eq_sum_profiles Y Z
    (fun w => F w.toTuple)

end

end Anderson4D
