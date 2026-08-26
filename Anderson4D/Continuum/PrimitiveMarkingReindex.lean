import Anderson4D.Continuum.PrimitiveAssembly

/-!
# Reindexing the increasing Hepp markings in (5.17)

For a fixed valid tree, an increasing branch marking is encoded by

* its root exponent;
* at a branch in the chosen free set, its own exponent;
* at every other non-root branch, the positive exponent gap to its parent.

The encoding is injective: starting at the root, the exponent at each branch
is recovered either directly (free case) or by subtracting the recorded gap
from the already recovered parent exponent.  Moreover, on a non-free branch
the parent-scale ratio is exactly `2⁻gap`.  Thus the constrained marking sum
injects into the independent product domain used by
`sum_dyadicAssignmentWeight_le`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- Valid bounded branch data, with no multiplicity or realization witness. -/
abbrev ValidBranchExponentData (t : PlaneTree) (bound : ℕ) :=
  {N : BranchExponentData t bound // N.IsValid}

/-- Independent coordinates used to dominate an increasing marking: one root
coordinate and one coordinate for every non-root branch. -/
abbrev PrimitiveMarkingCode (t : PlaneTree) (bound : ℕ) :=
  Fin (bound + 1) × (NonrootBranch t → Fin (bound + 1))

private theorem pmr_branch_of_nonroot
    {t : PlaneTree} (v : NonrootBranch t) :
    v.1 ∈ BranchNodes t :=
  (Finset.mem_erase.mp v.2).2

private theorem pmr_ne_root_of_nonroot
    {t : PlaneTree} (v : NonrootBranch t) :
    v.1 ≠ rootV t :=
  (Finset.mem_erase.mp v.2).1

/-- The root/free/gap code of a valid bounded marking.  The gap coordinate is
stored in the same `Fin (bound+1)` box because it is at most the parent
exponent, hence at most `bound`. -/
def primitiveMarkingCode
    {t : PlaneTree} {bound : ℕ}
    (hroot : rootV t ∈ BranchNodes t)
    (free : Finset (NonrootBranch t))
    (N : ValidBranchExponentData t bound) :
    PrimitiveMarkingCode t bound :=
  (N.1 ⟨rootV t, hroot⟩,
    fun v =>
      if v ∈ free then
        N.1 ⟨v.1, pmr_branch_of_nonroot v⟩
      else
        ⟨N.1.raw (parentV v.1) -
            (N.1 ⟨v.1, pmr_branch_of_nonroot v⟩).1,
          Nat.lt_succ_of_le
            ((Nat.sub_le _ _).trans (N.1.raw_le (parentV v.1)))⟩)

@[simp]
theorem primitiveMarkingCode_fst
    {t : PlaneTree} {bound : ℕ}
    (hroot : rootV t ∈ BranchNodes t)
    (free : Finset (NonrootBranch t))
    (N : ValidBranchExponentData t bound) :
    (primitiveMarkingCode hroot free N).1 =
      N.1 ⟨rootV t, hroot⟩ :=
  rfl

@[simp]
theorem primitiveMarkingCode_snd_of_mem
    {t : PlaneTree} {bound : ℕ}
    (hroot : rootV t ∈ BranchNodes t)
    (free : Finset (NonrootBranch t))
    (N : ValidBranchExponentData t bound)
    (v : NonrootBranch t) (hv : v ∈ free) :
    (primitiveMarkingCode hroot free N).2 v =
      N.1 ⟨v.1, pmr_branch_of_nonroot v⟩ := by
  simp [primitiveMarkingCode, hv]

@[simp]
theorem primitiveMarkingCode_snd_of_not_mem
    {t : PlaneTree} {bound : ℕ}
    (hroot : rootV t ∈ BranchNodes t)
    (free : Finset (NonrootBranch t))
    (N : ValidBranchExponentData t bound)
    (v : NonrootBranch t) (hv : v ∉ free) :
    ((primitiveMarkingCode hroot free N).2 v).1 =
      N.1.raw (parentV v.1) -
        (N.1 ⟨v.1, pmr_branch_of_nonroot v⟩).1 := by
  simp [primitiveMarkingCode, hv]

/-- The root/free/gap encoding is injective on valid increasing markings. -/
theorem primitiveMarkingCode_injective
    {t : PlaneTree} {bound : ℕ}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (free : Finset (NonrootBranch t)) :
    Function.Injective
      (primitiveMarkingCode (bound := bound) hroot free) := by
  intro N N' hcode
  apply Subtype.ext
  apply BranchExponentData.ext
  intro v
  have hpoint :
      ∀ k : ℕ, ∀ u : {u // u ∈ BranchNodes t},
        u.1.1.length = k → (N.1 u).1 = (N'.1 u).1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro u hdepth
        by_cases hur : u.1 = rootV t
        · have hu : u = ⟨rootV t, hroot⟩ := Subtype.ext hur
          rw [hu]
          exact Fin.ext_iff.mp (congrArg Prod.fst hcode)
        · have hunonroot : u.1 ∈ nonrootBranches t := by
            exact Finset.mem_erase.mpr ⟨hur, u.2⟩
          let nu : NonrootBranch t := ⟨u.1, hunonroot⟩
          by_cases hfree : nu ∈ free
          · have hcoord :=
              congrArg (fun c => (c.2 nu).1) hcode
            simpa [primitiveMarkingCode, hfree, nu] using hcoord
          · have hpbranch :
                parentV u.1 ∈ BranchNodes t :=
              parentV_mem_BranchNodes_of_branch ht u.2 hur
            let p : {p // p ∈ BranchNodes t} :=
              ⟨parentV u.1, hpbranch⟩
            have hune : u.1.1 ≠ [] := ne_root_iff.mp hur
            have hpdepth : p.1.1.length < k := by
              change u.1.1.dropLast.length < k
              rw [List.length_dropLast, hdepth]
              have : 0 < k := by
                have hlenne : u.1.1.length ≠ 0 := by
                  simpa using hune
                omega
              omega
            have hpval : (N.1 p).1 = (N'.1 p).1 :=
              ih p.1.1.length hpdepth p rfl
            have hcoord :=
              congrArg (fun c => (c.2 nu).1) hcode
            have hgap :
                N.1.raw (parentV u.1) - (N.1 u).1 =
                  N'.1.raw (parentV u.1) - (N'.1 u).1 := by
              simpa [primitiveMarkingCode, hfree, nu] using hcoord
            have hpraw :
                N.1.raw (parentV u.1) =
                  N'.1.raw (parentV u.1) := by
              simpa [BranchExponentData.raw_apply_of_mem _ hpbranch]
                using hpval
            have hgt : (N.1 u).1 < N.1.raw (parentV u.1) :=
              N.2.2 u hur
            have hgt' : (N'.1 u).1 < N'.1.raw (parentV u.1) :=
              N'.2.2 u hur
            omega
  exact hpoint v.1.1.length v rfl

/-- On a non-free branch, the recorded coordinate is the exact exponent
gap, so its geometric weight is the exact parent-scale ratio. -/
theorem parentScaleRatio_eq_half_pow_markingCode
    {t : PlaneTree} {bound : ℕ}
    (hroot : rootV t ∈ BranchNodes t)
    (free : Finset (NonrootBranch t))
    (N : ValidBranchExponentData t bound)
    (v : NonrootBranch t) (hv : v ∉ free) :
    parentScaleRatio (N.1.toHeppMarking N.2) v.1 =
      (1 / 2 : ℝ) ^
        ((primitiveMarkingCode hroot free N).2 v).1 := by
  let ev : ℕ :=
    (N.1 ⟨v.1, pmr_branch_of_nonroot v⟩).1
  let ep : ℕ := N.1.raw (parentV v.1)
  have hgt : ev < ep :=
    N.2.2 ⟨v.1, pmr_branch_of_nonroot v⟩
      (pmr_ne_root_of_nonroot v)
  have hsplit : ev + (ep - ev) = ep :=
    Nat.add_sub_of_le hgt.le
  rw [primitiveMarkingCode_snd_of_not_mem hroot free N v hv]
  unfold parentScaleRatio scaleN
  simp only [BranchExponentData.toHeppMarking]
  rw [BranchExponentData.raw_apply_of_mem N.1
    (pmr_branch_of_nonroot v)]
  change ((2 ^ ev : ℕ) : ℝ) / ((2 ^ ep : ℕ) : ℝ) =
    (1 / 2 : ℝ) ^ (ep - ev)
  calc
    ((2 ^ ev : ℕ) : ℝ) / ((2 ^ ep : ℕ) : ℝ) =
        1 / (2 : ℝ) ^ (ep - ev) := by
      rw [← hsplit, pow_add, Nat.cast_mul]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      field_simp
      congr 1
      omega
    _ = (1 / 2 : ℝ) ^ (ep - ev) := by
      simp [one_div, inv_pow]

/-- The ratio factor in (5.16), indexed on the genuine non-root branch
carrier.  Branches in `free` have no ratio factor. -/
def primitiveMarkingRatioWeight
    {t : PlaneTree} {bound : ℕ}
    (free : Finset (NonrootBranch t))
    (N : ValidBranchExponentData t bound) : ℝ :=
  ∏ v : NonrootBranch t,
    if v ∈ free then 1
    else parentScaleRatio (N.1.toHeppMarking N.2) v.1

theorem primitiveMarkingRatioWeight_nonneg
    {t : PlaneTree} {bound : ℕ}
    (free : Finset (NonrootBranch t))
    (N : ValidBranchExponentData t bound) :
    0 ≤ primitiveMarkingRatioWeight free N := by
  unfold primitiveMarkingRatioWeight
  apply Finset.prod_nonneg
  intro v hv
  split_ifs
  · exact zero_le_one
  · unfold parentScaleRatio
    positivity

/-- Pointwise identification of the actual marking-ratio product with the
independent dyadic assignment weight of its code. -/
theorem primitiveMarkingRatioWeight_eq_codeWeight
    {t : PlaneTree} {bound : ℕ}
    (hroot : rootV t ∈ BranchNodes t)
    (free : Finset (NonrootBranch t))
    (N : ValidBranchExponentData t bound) :
    primitiveMarkingRatioWeight free N =
      dyadicAssignmentWeight (bound + 1) free
        (primitiveMarkingCode hroot free N).2 := by
  unfold primitiveMarkingRatioWeight dyadicAssignmentWeight
  apply Finset.prod_congr rfl
  intro v hv
  by_cases hvfree : v ∈ free
  · simp [hvfree]
  · simp only [hvfree, ↓reduceIte]
    exact parentScaleRatio_eq_half_pow_markingCode
      hroot free N v hvfree

/-! ## Bridge to the paper's ordinary vertex-subset indexing -/

/-- Regard a vertex finset known to lie in `nonrootBranches` as a finset of
the genuine non-root branch subtype. -/
def nonrootBranchFinsetOfSubset
    {t : PlaneTree} (W : Finset (VPos t))
    (hW : W ⊆ nonrootBranches t) :
    Finset (NonrootBranch t) :=
  W.attach.map
    ⟨fun v => ⟨v.1, hW v.2⟩,
      fun a b hab => by
        have huv : a.1 = b.1 :=
          congrArg (fun v : NonrootBranch t => v.1) hab
        exact Subtype.ext huv⟩

@[simp]
theorem mem_nonrootBranchFinsetOfSubset
    {t : PlaneTree} {W : Finset (VPos t)}
    (hW : W ⊆ nonrootBranches t)
    (v : NonrootBranch t) :
    v ∈ nonrootBranchFinsetOfSubset W hW ↔ v.1 ∈ W := by
  constructor
  · intro hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hv
    have hwW : w.1 ∈ W := w.2
    simpa [Subtype.ext_iff] using heq ▸ hwW
  · intro hv
    apply Finset.mem_map.mpr
    refine ⟨⟨v.1, hv⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

@[simp]
theorem card_nonrootBranchFinsetOfSubset
    {t : PlaneTree} (W : Finset (VPos t))
    (hW : W ⊆ nonrootBranches t) :
    (nonrootBranchFinsetOfSubset W hW).card = W.card := by
  simp [nonrootBranchFinsetOfSubset]

/-- The subtype-indexed ratio weight is literally the product over the
paper's complement `(B \\ {root}) \\ W`. -/
theorem primitiveMarkingRatioWeight_ofSubset
    {t : PlaneTree} {bound : ℕ}
    (W : Finset (VPos t)) (hW : W ⊆ nonrootBranches t)
    (N : ValidBranchExponentData t bound) :
    primitiveMarkingRatioWeight
        (nonrootBranchFinsetOfSubset W hW) N =
      ∏ v ∈ nonrootBranches t \ W,
        parentScaleRatio (N.1.toHeppMarking N.2) v := by
  calc
    primitiveMarkingRatioWeight
          (nonrootBranchFinsetOfSubset W hW) N =
        ∏ v : NonrootBranch t,
          if v.1 ∈ W then 1
          else parentScaleRatio (N.1.toHeppMarking N.2) v.1 := by
      unfold primitiveMarkingRatioWeight
      apply Finset.prod_congr rfl
      intro v hv
      by_cases hvW : v.1 ∈ W
      · have hvfree :
            v ∈ nonrootBranchFinsetOfSubset W hW :=
          (mem_nonrootBranchFinsetOfSubset hW v).2 hvW
        simp [hvfree, hvW]
      · have hvfree :
            v ∉ nonrootBranchFinsetOfSubset W hW :=
          fun h => hvW
            ((mem_nonrootBranchFinsetOfSubset hW v).1 h)
        simp [hvfree, hvW]
    _ = ∏ v ∈ nonrootBranches t,
          if v ∈ W then 1
          else parentScaleRatio (N.1.toHeppMarking N.2) v := by
      symm
      exact Finset.prod_subtype
        (nonrootBranches t) (fun _ => Iff.rfl)
        (fun v =>
          if v ∈ W then 1
          else parentScaleRatio (N.1.toHeppMarking N.2) v)
    _ = ∏ v ∈ nonrootBranches t \ W,
          parentScaleRatio (N.1.toHeppMarking N.2) v := by
      rw [Finset.sdiff_eq_filter, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro v hv
      by_cases hvW : v ∈ W <;> simp [hvW]

/-- **Increasing-marking reindexing for paper (5.17).**

The sum is over the actual valid bounded branch markings.  The root exponent
costs one unrestricted coordinate, every branch in `free` costs one more,
and every remaining branch is summed by a geometric series.  The proof uses
the injective root/free/gap code above; no independence of the original
marking coordinates is assumed. -/
theorem sum_validBranchExponentData_ratioWeight_le
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (bound : ℕ) (free : Finset (NonrootBranch t)) :
    (∑ N : ValidBranchExponentData t bound,
        primitiveMarkingRatioWeight free N) ≤
      ((bound + 1 : ℕ) : ℝ) ^ (free.card + 1) *
        2 ^ ((nonrootBranches t).card - free.card) := by
  let code :
      ValidBranchExponentData t bound →
        PrimitiveMarkingCode t bound :=
    primitiveMarkingCode hroot free
  let weight : PrimitiveMarkingCode t bound → ℝ :=
    fun c => dyadicAssignmentWeight (bound + 1) free c.2
  have hcode : Function.Injective code :=
    primitiveMarkingCode_injective ht hroot free
  have hweight_nonneg :
      ∀ c : PrimitiveMarkingCode t bound, 0 ≤ weight c := by
    intro c
    dsimp only [weight]
    unfold dyadicAssignmentWeight
    apply Finset.prod_nonneg
    intro v hv
    split_ifs
    · exact zero_le_one
    · positivity
  calc
    (∑ N : ValidBranchExponentData t bound,
        primitiveMarkingRatioWeight free N) =
        ∑ N : ValidBranchExponentData t bound, weight (code N) := by
      apply Fintype.sum_congr
      intro N
      exact primitiveMarkingRatioWeight_eq_codeWeight
        hroot free N
    _ = ∑ c ∈
          (Finset.univ.image code), weight c := by
      symm
      exact Finset.sum_image
        (fun x _hx y _hy hxy => hcode hxy)
    _ ≤ ∑ c : PrimitiveMarkingCode t bound, weight c :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _)
        (fun c _hc _himage => hweight_nonneg c)
    _ = ((bound + 1 : ℕ) : ℝ) *
          ∑ a : NonrootBranch t → Fin (bound + 1),
            dyadicAssignmentWeight (bound + 1) free a := by
      rw [Fintype.sum_prod_type]
      simp only [weight]
      simp
    _ ≤ ((bound + 1 : ℕ) : ℝ) *
          (((bound + 1 : ℕ) : ℝ) ^ free.card *
            2 ^ ((nonrootBranches t).card - free.card)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_nonrootBranch_dyadicAssignmentWeight_le
          t (bound + 1) free)
        (by positivity)
    _ = ((bound + 1 : ℕ) : ℝ) ^ (free.card + 1) *
          2 ^ ((nonrootBranches t).card - free.card) := by
      rw [pow_succ]
      ring

/-! ## The logarithmic scale window used in the primitive estimate -/

/-- The analytic scale cap `2^Nexp ≤ 4M` places the exponent in the exact
base-two logarithmic window.  This is the sharp replacement for the coarse
`Nexp ≤ 4M` bound used only to make the incidence denominator finite. -/
theorem nexp_le_log_four_mul_of_scaleN_le
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {v : VPos t}
    (hscale : (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ)) :
    Nm.Nexp v ≤ Nat.log 2 (4 * M) := by
  apply Nat.le_log_of_pow_le (by norm_num)
  have hnat : scaleN Nm v ≤ 4 * M := by
    exact_mod_cast hscale
  exact hnat

/-- Canonical restriction of an analytically scale-capped marking to the
logarithmic exponent carrier needed in (5.17). -/
def logBranchDataOfScaleBound
    {t : PlaneTree} {M : ℕ}
    (Nm : HeppMarking t)
    (hscale :
      ∀ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ)) :
    BranchExponentData t (Nat.log 2 (4 * M)) :=
  BranchExponentData.ofHeppMarking Nm fun v hv =>
    nexp_le_log_four_mul_of_scaleN_le (hscale v hv)

@[simp]
theorem logBranchDataOfScaleBound_apply
    {t : PlaneTree} {M : ℕ}
    (Nm : HeppMarking t)
    (hscale :
      ∀ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (v : {v // v ∈ BranchNodes t}) :
    ((logBranchDataOfScaleBound Nm hscale) v).1 =
      Nm.Nexp v.1 :=
  rfl

theorem logBranchDataOfScaleBound_isValid
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ}
    (Nm : HeppMarking t)
    (hscale :
      ∀ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ)) :
    (logBranchDataOfScaleBound Nm hscale).IsValid := by
  exact BranchExponentData.isValid_ofHeppMarking Nm
    (fun v hv =>
      nexp_le_log_four_mul_of_scaleN_le (hscale v hv))
    (fun v hv hne =>
      parentV_mem_BranchNodes_of_branch ht hv hne)

/-- The logarithmic restriction preserves every parent-scale ratio on the
actual non-root branch carrier. -/
theorem parentScaleRatio_logBranchDataOfScaleBound
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ}
    (Nm : HeppMarking t)
    (hscale :
      ∀ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (v : NonrootBranch t) :
    parentScaleRatio
        ((logBranchDataOfScaleBound Nm hscale).toHeppMarking
          (logBranchDataOfScaleBound_isValid ht Nm hscale))
        v.1 =
      parentScaleRatio Nm v.1 := by
  have hvbranch : v.1 ∈ BranchNodes t :=
    pmr_branch_of_nonroot v
  have hpbranch : parentV v.1 ∈ BranchNodes t :=
    parentV_mem_BranchNodes_of_branch ht hvbranch
      (pmr_ne_root_of_nonroot v)
  unfold parentScaleRatio scaleN
  simp only [BranchExponentData.toHeppMarking]
  rw [BranchExponentData.raw_apply_of_mem _ hvbranch,
    BranchExponentData.raw_apply_of_mem _ hpbranch]
  rfl

/-- Applying the logarithmic restriction changes neither the free branches
nor the ratio weight appearing in (5.16). -/
theorem primitiveMarkingRatioWeight_logBranchDataOfScaleBound
    {t : PlaneTree} (ht : t.isValid = true)
    {M : ℕ}
    (Nm : HeppMarking t)
    (hscale :
      ∀ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ))
    (free : Finset (NonrootBranch t)) :
    primitiveMarkingRatioWeight free
        ⟨logBranchDataOfScaleBound Nm hscale,
          logBranchDataOfScaleBound_isValid ht Nm hscale⟩ =
      ∏ v : NonrootBranch t,
        if v ∈ free then 1 else parentScaleRatio Nm v.1 := by
  unfold primitiveMarkingRatioWeight
  apply Finset.prod_congr rfl
  intro v hv
  by_cases hvfree : v ∈ free
  · simp [hvfree]
  · simp only [hvfree, ↓reduceIte]
    exact parentScaleRatio_logBranchDataOfScaleBound
      ht Nm hscale v

/-- Paper-facing logarithmic form of the increasing-marking sum (5.17).
All scale-capped realizing markings canonically lie in this finite domain by
`logBranchDataOfScaleBound`. -/
theorem sum_logBranchExponentData_ratioWeight_le
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (M : ℕ) (free : Finset (NonrootBranch t)) :
    (∑ N :
        ValidBranchExponentData t (Nat.log 2 (4 * M)),
        primitiveMarkingRatioWeight free N) ≤
      ((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          (free.card + 1) *
        2 ^ ((nonrootBranches t).card - free.card) :=
  sum_validBranchExponentData_ratioWeight_le
    ht hroot (Nat.log 2 (4 * M)) free

/-- Direct ordinary-finset form of (5.17), matching the `W` indexing in
`permSumRHS`.  This is the form consumed by the primitive lattice assembly. -/
theorem sum_logBranchExponentData_parentScaleRatio_le
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (M : ℕ) (W : Finset (VPos t))
    (hW : W ⊆ nonrootBranches t) :
    (∑ N :
        ValidBranchExponentData t (Nat.log 2 (4 * M)),
        ∏ v ∈ nonrootBranches t \ W,
          parentScaleRatio (N.1.toHeppMarking N.2) v) ≤
      ((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          (W.card + 1) *
        2 ^ ((nonrootBranches t).card - W.card) := by
  let free : Finset (NonrootBranch t) :=
    nonrootBranchFinsetOfSubset W hW
  calc
    (∑ N :
        ValidBranchExponentData t (Nat.log 2 (4 * M)),
        ∏ v ∈ nonrootBranches t \ W,
          parentScaleRatio (N.1.toHeppMarking N.2) v) =
        ∑ N :
          ValidBranchExponentData t (Nat.log 2 (4 * M)),
          primitiveMarkingRatioWeight free N := by
      apply Fintype.sum_congr
      intro N
      exact (primitiveMarkingRatioWeight_ofSubset W hW N).symm
    _ ≤ ((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          (free.card + 1) *
        2 ^ ((nonrootBranches t).card - free.card) :=
      sum_logBranchExponentData_ratioWeight_le
        ht hroot M free
    _ = ((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          (W.card + 1) *
        2 ^ ((nonrootBranches t).card - W.card) := by
      rw [card_nonrootBranchFinsetOfSubset]

end

end Anderson4D
