import Anderson4D.Combinatorics.PairingHeadCases
import Anderson4D.Parametrix.WickAtBridge

/-!
# Dependency-closed pairing collapse for Proposition 3.4

This file connects the three head cases to the current random-parametrix and
Wick APIs.  It contains the finite reindexing and creation--contraction
identities which require no analytic interchange of integrals.  The remaining
step in the full kernel identity (3.16) is an analytic identification of each
case-(3) integral with `detJ` times the external `randRI`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-- The minimal prefix order of a case-(3) pairing. -/
def caseThreeQ {m : ℕ}
    (κ : {κ : PartialPairing (Fin (m + 1)) //
      HeadPairedWithPrefix κ}) : ℕ :=
  firstFullyPairedHeadQ κ.1 κ.2.2

theorem caseThreeQ_spec {m : ℕ}
    (κ : {κ : PartialPairing (Fin (m + 1)) //
      HeadPairedWithPrefix κ}) :
    IsFullyPairedHeadPrefix κ.1 (caseThreeQ κ) :=
  firstFullyPairedHeadQ_spec κ.1 κ.2.2

theorem caseThreeQ_mem_range {m : ℕ}
    (κ : {κ : PartialPairing (Fin (m + 1)) //
      HeadPairedWithPrefix κ}) :
    caseThreeQ κ ∈ Finset.Icc 1 ((m + 1) / 2) := by
  have hs := caseThreeQ_spec κ
  simp only [Finset.mem_Icc]
  constructor
  · exact hs.1
  · apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    simpa [Nat.mul_comm] using hs.2.1

/-- Regroup the case-(3) contribution by the uniquely determined minimal
prefix length `2q`. -/
theorem sum_caseThree_by_q
    {m : ℕ} {R : Type*} [AddCommMonoid R]
    (f : {κ : PartialPairing (Fin (m + 1)) //
      HeadPairedWithPrefix κ} → R) :
    (∑ κ, f κ) =
      ∑ q ∈ Finset.Icc 1 ((m + 1) / 2),
        ∑ κ ∈ Finset.univ.filter (fun κ => caseThreeQ κ = q),
          f κ := by
  exact (Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ :
      Finset {κ : PartialPairing (Fin (m + 1)) //
        HeadPairedWithPrefix κ}))
    (t := Finset.Icc 1 ((m + 1) / 2))
    (g := caseThreeQ)
    (fun κ _ => caseThreeQ_mem_range κ) f).symm

/-- A generic collapse theorem: once the contribution is identified on
each of the three disjoint classes, the full pairing sum is their sum. -/
theorem sum_headCases_collapse
    {m : ℕ} {R : Type*} [AddCommMonoid R]
    (f : PartialPairing (Fin (m + 1)) → R)
    (fSingle :
      {κ : PartialPairing (Fin (m + 1)) // HeadIsSingle κ} → R)
    (fRegular :
      {κ : PartialPairing (Fin (m + 1)) //
        HeadPairedNoPrefix κ} → R)
    (fCounter :
      {κ : PartialPairing (Fin (m + 1)) //
        HeadPairedWithPrefix κ} → R)
    (hSingle : ∀ κ, f κ.1 = fSingle κ)
    (hRegular : ∀ κ, f κ.1 = fRegular κ)
    (hCounter : ∀ κ, f κ.1 = fCounter κ) :
    (∑ κ, f κ) =
      (∑ κ, fSingle κ) + (∑ κ, fRegular κ) +
        ∑ κ, fCounter κ := by
  rw [sum_headCases]
  simp_rw [hSingle, hRegular, hCounter]

/-! ### The minimal prefix is a non-split full pairing -/

/-- The concrete cast-based order isomorphism from `Fin (2q)` to the
ambient first `2q` positions.  Unlike an abstract sorted enumeration, this
has definitionally transparent index values. -/
def HeadPrefixDecomposition.collapsePrefixOrderIso
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    Fin (2 * d.q) ≃o
      {i : Fin (m + 1) // i ∈ headEvenPrefix m d.q} where
  toFun i :=
    ⟨Fin.castLE d.two_mul_le i,
      mem_headEvenPrefix.mpr i.isLt⟩
  invFun i :=
    ⟨i.1.val, mem_headEvenPrefix.mp i.2⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Subtype.ext (Fin.ext rfl)
  map_rel_iff' := Iff.rfl

/-- The first block `σ₁`, using the transparent cast reindexing. -/
def HeadPrefixDecomposition.collapsePrefixPairing
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    PartialPairing (Fin (2 * d.q)) :=
  PartialPairing.congr d.collapsePrefixOrderIso.symm.toEquiv
    (restrictTo κ d.fullyPaired.2)

theorem HeadPrefixDecomposition.collapsePrefixPairing_isFull
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    d.collapsePrefixPairing.IsFull := by
  have hrestrict : (restrictTo κ d.fullyPaired.2).IsFull := by
    intro i hi
    exact d.fullyPaired.ne_of_mem i.2
      (congrArg Subtype.val hi)
  exact hrestrict.congr d.collapsePrefixOrderIso.symm.toEquiv

@[simp]
theorem HeadPrefixDecomposition.collapsePrefixPairing_apply_val
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) (i : Fin (2 * d.q)) :
    (d.collapsePrefixPairing i).val =
      (κ (Fin.castLE d.two_mul_le i)).val :=
  rfl

/-- A fully paired prefix of the collapsed first block pulls back to the
same zero-based prefix of the ambient pairing. -/
theorem HeadPrefixDecomposition.ambientFullyPaired_of_collapsePrefix
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) {r : ℕ}
    (hr : 2 * r ≤ 2 * d.q)
    (h :
      IsFullyPairedOn d.collapsePrefixPairing
        (Finset.univ.filter fun i : Fin (2 * d.q) =>
          i.val < 2 * r)) :
    IsFullyPairedOn κ (headEvenPrefix m r) := by
  constructor
  · intro i hi
    have hir : i.val < 2 * r := mem_headEvenPrefix.mp hi
    have hiq : i.val < 2 * d.q := lt_of_lt_of_le hir hr
    let j : Fin (2 * d.q) := ⟨i.val, hiq⟩
    have hj :
        j ∈ Finset.univ.filter
          (fun a : Fin (2 * d.q) => a.val < 2 * r) := by
      simp [j, hir]
    intro hfix
    apply h.ne_of_mem hj
    apply Fin.ext
    rw [d.collapsePrefixPairing_apply_val]
    have hcast : Fin.castLE d.two_mul_le j = i := by
      apply Fin.ext
      rfl
    rw [hcast, hfix]
  · intro i hi
    have hir : i.val < 2 * r := mem_headEvenPrefix.mp hi
    have hiq : i.val < 2 * d.q := lt_of_lt_of_le hir hr
    let j : Fin (2 * d.q) := ⟨i.val, hiq⟩
    have hj :
        j ∈ Finset.univ.filter
          (fun a : Fin (2 * d.q) => a.val < 2 * r) := by
      simp [j, hir]
    have hout := h.apply_mem hj
    rw [mem_headEvenPrefix]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hout
    have hcast : Fin.castLE d.two_mul_le j = i := by
      apply Fin.ext
      rfl
    simpa only [d.collapsePrefixPairing_apply_val, hcast] using hout

/-- Minimality of the first fully paired head prefix says exactly that its
restriction belongs to the paper's non-concatenation class.  This is the
combinatorial bridge from case (3) of Proposition 3.4 to the indexing set in
`renormC2q`. -/
theorem HeadPrefixDecomposition.collapsePrefixPairing_isNonSplit
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (d : HeadPrefixDecomposition κ) :
    IsNonSplit d.collapsePrefixPairing := by
  refine ⟨d.collapsePrefixPairing_isFull, ?_⟩
  rintro ⟨p, hpRange, hpProper, hprefix⟩
  let B : Finset (Fin (2 * d.q)) :=
    Finset.univ.filter fun i => i.val ≤ p
  have hBclosed : ∀ i ∈ B, d.collapsePrefixPairing i ∈ B := by
    intro i hi
    exact hprefix.apply_mem hi
  have hrestricted :
      (restrictTo d.collapsePrefixPairing hBclosed).IsFull := by
    intro i hfix
    exact hprefix.ne_of_mem i.2 (congrArg Subtype.val hfix)
  have heven : Even (Fintype.card B) := hrestricted.even_card
  have hpLt : p < 2 * d.q := Finset.mem_range.mp hpRange
  have hcard : Fintype.card B = p + 1 := by
    rw [Fintype.card_coe]
    change
      (Finset.univ.filter (fun i : Fin (2 * d.q) => i.val ≤ p)).card =
        p + 1
    have hfilter :
        Finset.univ.filter (fun i : Fin (2 * d.q) => i.val ≤ p) =
          Finset.univ.filter (fun i : Fin (2 * d.q) => i.val < p + 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hfilter, Fin.card_filter_val_lt, Nat.min_eq_right]
    omega
  rw [hcard] at heven
  obtain ⟨r, hr⟩ := heven
  have hrPos : 1 ≤ r := by omega
  have hrLt : r < d.q := by omega
  have hrBound : 2 * r ≤ m + 1 :=
    le_trans (by omega) d.two_mul_le
  have hset :
      Finset.univ.filter (fun i : Fin (2 * d.q) => i.val ≤ p) =
        Finset.univ.filter (fun i : Fin (2 * d.q) => i.val < 2 * r) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hambient : IsFullyPairedOn κ (headEvenPrefix m r) :=
    d.ambientFullyPaired_of_collapsePrefix
      (r := r) (by omega) (by simpa only [hset] using hprefix)
  exact d.no_smaller hrLt ⟨hrPos, hrBound, hambient⟩

/-- The canonical minimal-prefix decomposition attached to a case-(3)
pairing. -/
def caseThreeDecomposition {m : ℕ}
    (κ : {κ : PartialPairing (Fin (m + 1)) //
      HeadPairedWithPrefix κ}) :
    HeadPrefixDecomposition κ.1 :=
  headPrefixDecomposition κ.1 κ.2.2

@[simp]
theorem caseThreeDecomposition_q {m : ℕ}
    (κ : {κ : PartialPairing (Fin (m + 1)) //
      HeadPairedWithPrefix κ}) :
    (caseThreeDecomposition κ).q = caseThreeQ κ :=
  rfl

/-- In canonical case-(3) data, the internal pairing `σ₁` is an admissible
summand of `renormC2q`. -/
theorem caseThree_prefix_isNonSplit {m : ℕ}
    (κ : {κ : PartialPairing (Fin (m + 1)) //
      HeadPairedWithPrefix κ}) :
    IsNonSplit (caseThreeDecomposition κ).collapsePrefixPairing :=
  (caseThreeDecomposition κ).collapsePrefixPairing_isNonSplit

theorem caseThree_prefix_mem_nonSplit_filter {m : ℕ}
    (κ : {κ : PartialPairing (Fin (m + 1)) //
      HeadPairedWithPrefix κ}) :
    (caseThreeDecomposition κ).collapsePrefixPairing ∈
      Finset.univ.filter IsNonSplit := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact caseThree_prefix_isNonSplit κ

end PartialPairing

/-! ## Wick creation--contraction at the head -/

/-- The exact Wick-theorem step used before the three pairing cases in
the proof of (3.16), specialized to the mollified field and its covariance.
No symmetry or probabilistic hypothesis is needed. -/
theorem xi_mul_wickAt_eq_create_add_contract
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) (xt : Fin (m + 2) → T4)
    (z : T4) (ω : M.Ω) :
    M.xiEps ρ ε ω z * wickAt M ρ ε κ xt ω =
      wickPolynomial
        (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
        (fun x ω' => M.xiEps ρ ε ω' x)
        (z :: wickAtSingleLabels κ xt) ω +
      ∑ j : Fin (wickAtSingleLabels κ xt).length,
        ρ.etaEpsT4 ε
          (z - (wickAtSingleLabels κ xt).get j) *
        wickPolynomial
          (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
          (fun x ω' => M.xiEps ρ ε ω' x)
          ((wickAtSingleLabels κ xt).eraseIdx j) ω := by
  rw [wickAt_eq_wickPolynomial]
  exact mul_wickPolynomial_eq_create_add_contract
    (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
    (fun x ω' => M.xiEps ρ ε ω' x)
    z (wickAtSingleLabels κ xt) ω

/-! ## Parametrix finite-sum collapse -/

/-- `P_{m+1}` split into exactly the three classes in paper Prop. 3.4. -/
theorem parametrixP_succ_eq_headCases
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (x y : T4) (ω : M.Ω) :
    parametrixP M ρ lam ε (m + 1) x y ω =
      (∑ κ : {κ : PartialPairing (Fin (m + 1)) //
          PartialPairing.HeadIsSingle κ},
        randRI M ρ lam ε (m + 1) κ.1 x y ω) +
      (∑ κ : {κ : PartialPairing (Fin (m + 1)) //
          PartialPairing.HeadPairedNoPrefix κ},
        randRI M ρ lam ε (m + 1) κ.1 x y ω) +
      ∑ κ : {κ : PartialPairing (Fin (m + 1)) //
          PartialPairing.HeadPairedWithPrefix κ},
        randRI M ρ lam ε (m + 1) κ.1 x y ω := by
  unfold parametrixP
  exact PartialPairing.sum_headCases
    (fun κ => randRI M ρ lam ε (m + 1) κ x y ω)

/-- The same split with case (3) already regrouped by its unique `q`.
This is the finite-sum shape of the counterterm sum in (3.16). -/
theorem parametrixP_succ_eq_headCases_by_q
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (x y : T4) (ω : M.Ω) :
    parametrixP M ρ lam ε (m + 1) x y ω =
      (∑ κ : {κ : PartialPairing (Fin (m + 1)) //
          PartialPairing.HeadIsSingle κ},
        randRI M ρ lam ε (m + 1) κ.1 x y ω) +
      (∑ κ : {κ : PartialPairing (Fin (m + 1)) //
          PartialPairing.HeadPairedNoPrefix κ},
        randRI M ρ lam ε (m + 1) κ.1 x y ω) +
      ∑ q ∈ Finset.Icc 1 ((m + 1) / 2),
        ∑ κ ∈ Finset.univ.filter
            (fun κ : {κ : PartialPairing (Fin (m + 1)) //
              PartialPairing.HeadPairedWithPrefix κ} =>
              PartialPairing.caseThreeQ κ = q),
          randRI M ρ lam ε (m + 1) κ.1 x y ω := by
  rw [parametrixP_succ_eq_headCases]
  rw [PartialPairing.sum_caseThree_by_q]

end

end Anderson4D
