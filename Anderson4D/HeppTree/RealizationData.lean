import Anderson4D.HeppTree.RestrictedData
import Anderson4D.HeppTree.ExistenceBounds
import Anderson4D.HeppTree.ValidParent

/-!
# Finite restricted realization data

The denominator in paper (5.6) counts only the discrete pair consisting of
branch scales and leaf multiplicities.  It must not count an admissible
embedding or a word witness, and it must not distinguish junk values away
from branching vertices or leaves.

For a fixed tree `t`, box radius `M`, and total word length `m`, this file
uses the finite carriers

* `BranchExponentData t (4 * M) =
    BranchNodes t → Fin (4 * M + 1)`, and
* `LeafMultiplicityData t m = Leaves t → Fin (m + 1)`.

Both have canonical zero extensions to all vertices.  The predicates
`BranchExponentData.IsValid`, `LeafMultiplicityData.AtLeastTwo`, and
`LeafMultiplicityData.HasTotal` express the general denominator constraints,
while `realizationDataFinset` enumerates the pairs satisfying all of them.
Evenness belongs only to the paired-vector specialization and is recorded
separately by `RealizationData.IsEven` and
`RealizationData.IsPairedValid`.
-/

namespace Anderson4D

namespace PlaneTree

/-! ## Branch-only exponent data -/

/-- Branch exponents bounded by `bound`, stored only where they have meaning. -/
abbrev BranchExponentData (t : PlaneTree) (bound : ℕ) :=
  {v // v ∈ BranchNodes t} → Fin (bound + 1)

namespace BranchExponentData

/-- Canonical zero extension of bounded branch exponent data to all vertices. -/
def raw {t : PlaneTree} {bound : ℕ} (N : BranchExponentData t bound) :
    Marking t :=
  fun v => if h : v ∈ BranchNodes t then (N ⟨v, h⟩).1 else 0

@[simp] theorem raw_apply_of_mem {t : PlaneTree} {bound : ℕ}
    (N : BranchExponentData t bound) {v : VPos t}
    (hv : v ∈ BranchNodes t) :
    N.raw v = (N ⟨v, hv⟩).1 := by
  simp [raw, hv]

@[simp] theorem raw_apply_of_not_mem {t : PlaneTree} {bound : ℕ}
    (N : BranchExponentData t bound) {v : VPos t}
    (hv : v ∉ BranchNodes t) :
    N.raw v = 0 := by
  simp [raw, hv]

theorem raw_le {t : PlaneTree} {bound : ℕ}
    (N : BranchExponentData t bound) (v : VPos t) :
    N.raw v ≤ bound := by
  by_cases hv : v ∈ BranchNodes t
  · rw [raw_apply_of_mem N hv]
    exact (N ⟨v, hv⟩).is_le
  · rw [raw_apply_of_not_mem N hv]
    exact Nat.zero_le _

/-- Extensionality on the restricted branch carrier. -/
theorem ext {t : PlaneTree} {bound : ℕ}
    {N N' : BranchExponentData t bound}
    (h : ∀ v, (N v).1 = (N' v).1) : N = N' := by
  funext v
  exact Fin.ext (h v)

/-- The canonical raw view is injective; off-branch zeros carry no data. -/
theorem raw_injective {t : PlaneTree} {bound : ℕ} :
    Function.Injective (@raw t bound) := by
  intro N N' h
  apply ext
  intro v
  have hv := congrFun h v.1
  simpa using hv

theorem raw_eq_iff {t : PlaneTree} {bound : ℕ}
    {N N' : BranchExponentData t bound} :
    N.raw = N'.raw ↔ N = N' := by
  constructor
  · intro h
    exact raw_injective h
  · intro h
    subst N'
    rfl

/-- The paper's marking constraints, expressed entirely through restricted
data.  At a non-root branch the parent value is read from the canonical raw
extension, so invalid unary-parent configurations cannot be hidden in junk. -/
def IsValid {t : PlaneTree} {bound : ℕ}
    (N : BranchExponentData t bound) : Prop :=
  (∀ v, 1 ≤ (N v).1) ∧
    ∀ v, v.1 ≠ rootV t → N.raw (parentV v.1) > (N v).1

instance {t : PlaneTree} {bound : ℕ} (N : BranchExponentData t bound) :
    Decidable N.IsValid := by
  unfold IsValid
  infer_instance

/-- Valid restricted branch data defines a canonical `HeppMarking`. -/
def toHeppMarking {t : PlaneTree} {bound : ℕ}
    (N : BranchExponentData t bound) (hN : N.IsValid) :
    HeppMarking t where
  Nexp := N.raw
  pos := by
    intro v hv
    rw [raw_apply_of_mem N hv]
    exact hN.1 ⟨v, hv⟩
  parent_gt := by
    intro v hv hroot
    rw [raw_apply_of_mem N hv]
    exact hN.2 ⟨v, hv⟩ hroot

/-- Converting valid restricted data to a marking preserves its canonical
raw view literally. -/
theorem toHeppMarking_canonicalRaw {t : PlaneTree} {bound : ℕ}
    (N : BranchExponentData t bound) (hN : N.IsValid) :
    (N.toHeppMarking hN).canonicalRaw = N.raw := by
  funext v
  by_cases hv : v ∈ BranchNodes t <;>
    simp [HeppMarking.canonicalRaw, toHeppMarking, raw, hv]

/-- Restrict a `HeppMarking` whose branch exponents have an explicit natural
upper bound. -/
def ofHeppMarking {t : PlaneTree} {bound : ℕ} (Nm : HeppMarking t)
    (hbound : ∀ v ∈ BranchNodes t, Nm.Nexp v ≤ bound) :
    BranchExponentData t bound :=
  fun v => ⟨Nm.Nexp v.1, Nat.lt_succ_of_le (hbound v.1 v.2)⟩

@[simp] theorem ofHeppMarking_apply {t : PlaneTree} {bound : ℕ}
    (Nm : HeppMarking t)
    (hbound : ∀ v ∈ BranchNodes t, Nm.Nexp v ≤ bound)
    (v : {v // v ∈ BranchNodes t}) :
    ((ofHeppMarking Nm hbound) v).1 = Nm.Nexp v.1 := rfl

/-- On a tree whose non-root branch vertices have branching parents, a
genuine `HeppMarking` restricts to valid finite branch data. -/
theorem isValid_ofHeppMarking {t : PlaneTree} {bound : ℕ}
    (Nm : HeppMarking t)
    (hbound : ∀ v ∈ BranchNodes t, Nm.Nexp v ≤ bound)
    (hparent : ∀ v ∈ BranchNodes t, v ≠ rootV t →
      parentV v ∈ BranchNodes t) :
    (ofHeppMarking Nm hbound).IsValid := by
  constructor
  · intro v
    exact Nm.pos v.1 v.2
  · intro v hroot
    have hp : parentV v.1 ∈ BranchNodes t :=
      hparent v.1 v.2 hroot
    simpa [raw, hp] using Nm.parent_gt v.1 v.2 hroot

end BranchExponentData

/-! ## Leaf-only multiplicity data -/

/-- Leaf multiplicities bounded by the total word length `bound`, stored only
at leaves. -/
abbrev LeafMultiplicityData (t : PlaneTree) (bound : ℕ) :=
  {v // v ∈ Leaves t} → Fin (bound + 1)

namespace LeafMultiplicityData

/-- Canonical zero extension of bounded leaf multiplicities to all vertices. -/
def raw {t : PlaneTree} {bound : ℕ} (mu : LeafMultiplicityData t bound) :
    VPos t → ℕ :=
  fun v => if h : v ∈ Leaves t then (mu ⟨v, h⟩).1 else 0

@[simp] theorem raw_apply_of_mem {t : PlaneTree} {bound : ℕ}
    (mu : LeafMultiplicityData t bound) {v : VPos t}
    (hv : v ∈ Leaves t) :
    mu.raw v = (mu ⟨v, hv⟩).1 := by
  simp [raw, hv]

@[simp] theorem raw_apply_of_not_mem {t : PlaneTree} {bound : ℕ}
    (mu : LeafMultiplicityData t bound) {v : VPos t}
    (hv : v ∉ Leaves t) :
    mu.raw v = 0 := by
  simp [raw, hv]

theorem raw_le {t : PlaneTree} {bound : ℕ}
    (mu : LeafMultiplicityData t bound) (v : VPos t) :
    mu.raw v ≤ bound := by
  by_cases hv : v ∈ Leaves t
  · rw [raw_apply_of_mem mu hv]
    exact (mu ⟨v, hv⟩).is_le
  · rw [raw_apply_of_not_mem mu hv]
    exact Nat.zero_le _

/-- Extensionality on the restricted leaf carrier. -/
theorem ext {t : PlaneTree} {bound : ℕ}
    {mu mu' : LeafMultiplicityData t bound}
    (h : ∀ l, (mu l).1 = (mu' l).1) : mu = mu' := by
  funext l
  exact Fin.ext (h l)

/-- The canonical raw multiplicity view is injective. -/
theorem raw_injective {t : PlaneTree} {bound : ℕ} :
    Function.Injective (@raw t bound) := by
  intro mu mu' h
  apply ext
  intro l
  have hl := congrFun h l.1
  simpa using hl

theorem raw_eq_iff {t : PlaneTree} {bound : ℕ}
    {mu mu' : LeafMultiplicityData t bound} :
    mu.raw = mu'.raw ↔ mu = mu' := by
  constructor
  · intro h
    exact raw_injective h
  · intro h
    subst mu'
    rfl

/-- Every leaf multiplicity is at least two. -/
def AtLeastTwo {t : PlaneTree} {bound : ℕ}
    (mu : LeafMultiplicityData t bound) : Prop :=
  ∀ l, 2 ≤ (mu l).1

/-- Every leaf multiplicity is even (the paired-vector specialization used
after the Gaussian expectation). -/
def IsEven {t : PlaneTree} {bound : ℕ}
    (mu : LeafMultiplicityData t bound) : Prop :=
  ∀ l, Even (mu l).1

/-- The sum of all leaf multiplicities is the prescribed total length. -/
def HasTotal {t : PlaneTree} {bound : ℕ}
    (mu : LeafMultiplicityData t bound) (total : ℕ) : Prop :=
  ∑ l, (mu l).1 = total

instance {t : PlaneTree} {bound : ℕ} (mu : LeafMultiplicityData t bound) :
    Decidable mu.AtLeastTwo := by
  unfold AtLeastTwo
  infer_instance

instance {t : PlaneTree} {bound : ℕ} (mu : LeafMultiplicityData t bound) :
    Decidable mu.IsEven := by
  unfold IsEven
  infer_instance

instance {t : PlaneTree} {bound total : ℕ}
    (mu : LeafMultiplicityData t bound) :
    Decidable (mu.HasTotal total) := by
  unfold HasTotal
  infer_instance

/-- Restricted multiplicity data satisfying the lower bound defines a
canonical `Multiplicities` bundle. -/
def toMultiplicities {t : PlaneTree} {bound : ℕ}
    (mu : LeafMultiplicityData t bound) (htwo : mu.AtLeastTwo) :
    Multiplicities t where
  m := mu.raw
  two_le := by
    intro v hv
    rw [raw_apply_of_mem mu hv]
    exact htwo ⟨v, hv⟩

theorem toMultiplicities_canonicalRaw {t : PlaneTree} {bound : ℕ}
    (mu : LeafMultiplicityData t bound) (htwo : mu.AtLeastTwo) :
    (mu.toMultiplicities htwo).canonicalRaw = mu.raw := by
  funext v
  by_cases hv : v ∈ Leaves t <;>
    simp [Multiplicities.canonicalRaw, toMultiplicities, raw, hv]

/-- Restrict a `Multiplicities` bundle with an explicit leafwise bound. -/
def ofMultiplicities {t : PlaneTree} {bound : ℕ} (mu : Multiplicities t)
    (hbound : ∀ v ∈ Leaves t, mu.m v ≤ bound) :
    LeafMultiplicityData t bound :=
  fun l => ⟨mu.m l.1, Nat.lt_succ_of_le (hbound l.1 l.2)⟩

@[simp] theorem ofMultiplicities_apply {t : PlaneTree} {bound : ℕ}
    (mu : Multiplicities t) (hbound : ∀ v ∈ Leaves t, mu.m v ≤ bound)
    (l : {v // v ∈ Leaves t}) :
    ((ofMultiplicities mu hbound) l).1 = mu.m l.1 := rfl

theorem atLeastTwo_ofMultiplicities {t : PlaneTree} {bound : ℕ}
    (mu : Multiplicities t) (hbound : ∀ v ∈ Leaves t, mu.m v ≤ bound) :
    (ofMultiplicities mu hbound).AtLeastTwo := by
  intro l
  exact mu.two_le l.1 l.2

/-- A summand is bounded by the total sum of all leaf multiplicities. -/
theorem value_le_of_hasTotal {t : PlaneTree} {bound total : ℕ}
    (mu : LeafMultiplicityData t bound) (htotal : mu.HasTotal total)
    (l : {v // v ∈ Leaves t}) :
    (mu l).1 ≤ total := by
  calc
    (mu l).1 ≤ ∑ x, (mu x).1 :=
      Finset.single_le_sum (fun x _ => Nat.zero_le (mu x).1)
        (Finset.mem_univ l)
    _ = total := htotal

end LeafMultiplicityData

/-! ## The finite denominator carrier -/

/-- Discrete realization data for paper (5.6).  There are no embedding or
word witnesses in this type. -/
abbrev RealizationData (t : PlaneTree) (M m : ℕ) :=
  BranchExponentData t (4 * M) × LeafMultiplicityData t m

namespace RealizationData

/-- General validity for the denominator in (5.6): valid branch scales,
leaf multiplicities at least two, and the prescribed total.  Evenness is
deliberately not part of this predicate. -/
def IsValid {t : PlaneTree} {M m : ℕ}
    (d : RealizationData t M m) : Prop :=
  d.1.IsValid ∧ d.2.AtLeastTwo ∧ d.2.HasTotal m

instance {t : PlaneTree} {M m : ℕ} (d : RealizationData t M m) :
    Decidable d.IsValid := by
  unfold IsValid
  infer_instance

/-- Extra leafwise parity condition for data supplied by a pairing. -/
def IsEven {t : PlaneTree} {M m : ℕ}
    (d : RealizationData t M m) : Prop :=
  d.2.IsEven

instance {t : PlaneTree} {M m : ℕ} (d : RealizationData t M m) :
    Decidable d.IsEven := by
  unfold IsEven
  infer_instance

/-- Paired-vector validity is general denominator validity together with
the separate parity property. -/
def IsPairedValid {t : PlaneTree} {M m : ℕ}
    (d : RealizationData t M m) : Prop :=
  d.IsValid ∧ d.IsEven

instance {t : PlaneTree} {M m : ℕ} (d : RealizationData t M m) :
    Decidable d.IsPairedValid := by
  unfold IsPairedValid
  infer_instance

/-- Convert valid denominator data to the marking bundle. -/
def toHeppMarking {t : PlaneTree} {M m : ℕ}
    (d : RealizationData t M m) (hd : d.IsValid) :
    HeppMarking t :=
  d.1.toHeppMarking hd.1

/-- Convert valid denominator data to the multiplicity bundle. -/
def toMultiplicities {t : PlaneTree} {M m : ℕ}
    (d : RealizationData t M m) (hd : d.IsValid) :
    Multiplicities t :=
  d.2.toMultiplicities hd.2.1

theorem toMultiplicities_even {t : PlaneTree} {M m : ℕ}
    (d : RealizationData t M m) (hd : d.IsValid)
    (heven : d.IsEven)
    (l : {v // v ∈ Leaves t}) :
    Even ((d.toMultiplicities hd).m l.1) := by
  change Even (d.2.raw l.1)
  rw [LeafMultiplicityData.raw_apply_of_mem d.2 l.2]
  exact heven l

theorem toMultiplicities_total {t : PlaneTree} {M m : ℕ}
    (d : RealizationData t M m) (hd : d.IsValid) :
    ∑ l : {v // v ∈ Leaves t}, (d.toMultiplicities hd).m l.1 = m := by
  change ∑ l : {v // v ∈ Leaves t}, d.2.raw l.1 = m
  have hfun :
      (fun l : {v // v ∈ Leaves t} => d.2.raw l.1) =
        fun l => (d.2 l).1 := by
    funext l
    exact LeafMultiplicityData.raw_apply_of_mem d.2 l.2
  rw [hfun]
  exact hd.2.2

end RealizationData

/-- Valid denominator data carrying the additional parity property supplied
by a pairing.  It is intentionally distinct from the general denominator
subtype. -/
abbrev PairedValidRealizationData (t : PlaneTree) (M m : ℕ) :=
  {d : RealizationData t M m // d.IsPairedValid}

/-- The finite enumeration of valid restricted realization data for fixed
`t`, `M`, and total length `m`. -/
def realizationDataFinset (t : PlaneTree) (M m : ℕ) :
    Finset (RealizationData t M m) :=
  Finset.univ.filter RealizationData.IsValid

@[simp] theorem mem_realizationDataFinset {t : PlaneTree} {M m : ℕ}
    {d : RealizationData t M m} :
    d ∈ realizationDataFinset t M m ↔ d.IsValid := by
  simp [realizationDataFinset]

/-- The explicit ambient cardinality of the restricted data carrier. -/
theorem card_realizationData_type (t : PlaneTree) (M m : ℕ) :
    Fintype.card (RealizationData t M m) =
      (4 * M + 1) ^ (BranchNodes t).card *
        (m + 1) ^ (Leaves t).card := by
  change
    Fintype.card
      (({v // v ∈ BranchNodes t} → Fin (4 * M + 1)) ×
        ({v // v ∈ Leaves t} → Fin (m + 1))) =
      (4 * M + 1) ^ (BranchNodes t).card *
        (m + 1) ^ (Leaves t).card
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe]

/-- Explicit finiteness bound for the actual denominator enumeration. -/
theorem card_realizationDataFinset_le (t : PlaneTree) (M m : ℕ) :
    (realizationDataFinset t M m).card ≤
      (4 * M + 1) ^ (BranchNodes t).card *
        (m + 1) ^ (Leaves t).card := by
  calc
    (realizationDataFinset t M m).card
        ≤ Fintype.card (RealizationData t M m) := by
      simpa [realizationDataFinset] using
        (Finset.card_filter_le (Finset.univ : Finset (RealizationData t M m))
          RealizationData.IsValid)
    _ = _ := card_realizationData_type t M m

/-- The valid restricted data form a finite set, independently of any
realization witnesses. -/
theorem finite_validRealizationData (t : PlaneTree) (M m : ℕ) :
    Set.Finite {d : RealizationData t M m | d.IsValid} := by
  have heq :
      {d : RealizationData t M m | d.IsValid}
        = (realizationDataFinset t M m : Set (RealizationData t M m)) := by
    ext d
    simp
  rw [heq]
  exact (realizationDataFinset t M m).finite_toSet

/-! ## From the analytic scale bound to the finite natural bound -/

/-- The analytic bound `2^Nexp ≤ 4M` implies the deliberately coarse natural
bound `Nexp ≤ 4M` used by the finite carrier. -/
theorem nexp_le_four_mul_of_scaleN_le {t : PlaneTree}
    {Nm : HeppMarking t} {M : ℕ} {v : VPos t}
    (hscale : (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ)) :
    Nm.Nexp v ≤ 4 * M := by
  have hn : Nm.Nexp v ≤ 2 ^ Nm.Nexp v :=
    (Nat.lt_two_pow_self : Nm.Nexp v < 2 ^ Nm.Nexp v).le
  have hreal : (Nm.Nexp v : ℝ) ≤ ((4 * M : ℕ) : ℝ) := by
    calc
      (Nm.Nexp v : ℝ) ≤ ((2 ^ Nm.Nexp v : ℕ) : ℝ) := by
        exact_mod_cast hn
      _ = (scaleN Nm v : ℝ) := by rfl
      _ ≤ 4 * (M : ℝ) := hscale
      _ = ((4 * M : ℕ) : ℝ) := by norm_num
  exact_mod_cast hreal

/-- Restrict a marking satisfying the paper's scale bound to the finite
branch carrier used in `RealizationData`. -/
def branchDataOfScaleBound {t : PlaneTree} {M : ℕ}
    (Nm : HeppMarking t)
    (hscale : ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ)) :
    BranchExponentData t (4 * M) :=
  BranchExponentData.ofHeppMarking Nm fun v hv =>
    nexp_le_four_mul_of_scaleN_le (hscale v hv)

@[simp] theorem branchDataOfScaleBound_apply {t : PlaneTree} {M : ℕ}
    (Nm : HeppMarking t)
    (hscale : ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (v : {v // v ∈ BranchNodes t}) :
    ((branchDataOfScaleBound Nm hscale) v).1 = Nm.Nexp v.1 := rfl

theorem branchDataOfScaleBound_isValid {t : PlaneTree} {M : ℕ}
    (Nm : HeppMarking t)
    (hscale : ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (hparent : ∀ v ∈ BranchNodes t, v ≠ rootV t →
      parentV v ∈ BranchNodes t) :
    (branchDataOfScaleBound Nm hscale).IsValid := by
  exact BranchExponentData.isValid_ofHeppMarking Nm
    (fun v hv => nexp_le_four_mul_of_scaleN_le (hscale v hv)) hparent

/-! ## Bundle-to-carrier bridge without realization witnesses -/

/-- If the leaf multiplicities sum to `m`, each individual multiplicity is
at most `m`. -/
theorem multiplicity_le_total {t : PlaneTree} {mu : Multiplicities t} {m : ℕ}
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (l : {v // v ∈ Leaves t}) :
    mu.m l.1 ≤ m := by
  calc
    mu.m l.1 ≤ ∑ x : {v // v ∈ Leaves t}, mu.m x.1 :=
      Finset.single_le_sum (fun x _ => Nat.zero_le (mu.m x.1))
        (Finset.mem_univ l)
    _ = m := htotal

/-- Restrict a multiplicity bundle using its prescribed total as the finite
leafwise bound. -/
def leafDataOfTotal {t : PlaneTree} {m : ℕ} (mu : Multiplicities t)
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m) :
    LeafMultiplicityData t m :=
  LeafMultiplicityData.ofMultiplicities mu fun v hv =>
    multiplicity_le_total htotal ⟨v, hv⟩

theorem leafDataOfTotal_atLeastTwo {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t)
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m) :
    (leafDataOfTotal mu htotal).AtLeastTwo :=
  LeafMultiplicityData.atLeastTwo_ofMultiplicities mu _

theorem leafDataOfTotal_isEven {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t)
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (heven : ∀ l : {v // v ∈ Leaves t}, Even (mu.m l.1)) :
    (leafDataOfTotal mu htotal).IsEven := by
  intro l
  exact heven l

theorem leafDataOfTotal_hasTotal {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t)
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m) :
    (leafDataOfTotal mu htotal).HasTotal m := by
  simpa [LeafMultiplicityData.HasTotal, leafDataOfTotal] using htotal

/-- Form the finite denominator datum from the marking and multiplicity bundles.  The construction
contains no embedding and no word witness. -/
def realizationDataOfBundles {t : PlaneTree} {M m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m) :
    RealizationData t M m :=
  ⟨branchDataOfScaleBound Nm hscale, leafDataOfTotal mu htotal⟩

theorem realizationDataOfBundles_isValid {t : PlaneTree} {M m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (hparent : ∀ v ∈ BranchNodes t, v ≠ rootV t →
      parentV v ∈ BranchNodes t) :
    (realizationDataOfBundles Nm mu hscale htotal).IsValid := by
  refine ⟨branchDataOfScaleBound_isValid Nm hscale hparent,
    leafDataOfTotal_atLeastTwo mu htotal,
    leafDataOfTotal_hasTotal mu htotal⟩

/-- Bundle data from a paired vector satisfies the separately recorded
parity predicate. -/
theorem realizationDataOfBundles_isEven {t : PlaneTree} {M m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (heven : ∀ l : {v // v ∈ Leaves t}, Even (mu.m l.1)) :
    (realizationDataOfBundles Nm mu hscale htotal).IsEven :=
  leafDataOfTotal_isEven mu htotal heven

/-- Bundle data satisfying both the general and paired-vector conditions. -/
theorem realizationDataOfBundles_isPairedValid
    {t : PlaneTree} {M m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (heven : ∀ l : {v // v ∈ Leaves t}, Even (mu.m l.1))
    (hparent : ∀ v ∈ BranchNodes t, v ≠ rootV t →
      parentV v ∈ BranchNodes t) :
    (realizationDataOfBundles Nm mu hscale htotal).IsPairedValid :=
  ⟨realizationDataOfBundles_isValid
      Nm mu hscale htotal hparent,
    realizationDataOfBundles_isEven
      Nm mu hscale htotal heven⟩

theorem realizationDataOfBundles_mem {t : PlaneTree} {M m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (hparent : ∀ v ∈ BranchNodes t, v ≠ rootV t →
      parentV v ∈ BranchNodes t) :
    realizationDataOfBundles Nm mu hscale htotal ∈
      realizationDataFinset t M m :=
  mem_realizationDataFinset.mpr
    (realizationDataOfBundles_isValid Nm mu hscale htotal hparent)

/-- On a valid Hepp tree the structural parent hypothesis is automatic. -/
theorem realizationDataOfBundles_isValid_of_treeValid
    {t : PlaneTree} {M m : ℕ} (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m) :
    (realizationDataOfBundles Nm mu hscale htotal).IsValid :=
  realizationDataOfBundles_isValid Nm mu hscale htotal
    (fun _ hv hroot =>
      parentV_mem_BranchNodes_of_branch ht hv hroot)

/-- On a valid tree, paired-vector bundle data is paired-valid. -/
theorem realizationDataOfBundles_isPairedValid_of_treeValid
    {t : PlaneTree} {M m : ℕ} (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m)
    (heven : ∀ l : {v // v ∈ Leaves t}, Even (mu.m l.1)) :
    (realizationDataOfBundles Nm mu hscale htotal).IsPairedValid :=
  ⟨realizationDataOfBundles_isValid_of_treeValid
      ht Nm mu hscale htotal,
    realizationDataOfBundles_isEven Nm mu hscale htotal heven⟩

theorem realizationDataOfBundles_mem_of_treeValid
    {t : PlaneTree} {M m : ℕ} (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : ∀ v ∈ BranchNodes t, (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (htotal : ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = m) :
    realizationDataOfBundles Nm mu hscale htotal ∈
      realizationDataFinset t M m :=
  mem_realizationDataFinset.mpr
    (realizationDataOfBundles_isValid_of_treeValid
      ht Nm mu hscale htotal)

end PlaneTree

end Anderson4D
