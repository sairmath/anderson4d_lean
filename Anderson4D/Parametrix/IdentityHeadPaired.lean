import Anderson4D.Parametrix.IdentityHeadSingle

/-!
# The paired-head branch of the parametrix identity

This module isolates the exact deterministic and Wick ledgers for a
Wick contraction.  The only combinatorial datum used by the closed-form
factorization is that deleting the paired head shifts every extracted
interval down by one.  For paper case (2), this datum is forced by the
absence of a fully paired head prefix; case (3) is handled separately by
the non-split prefix decomposition.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace PartialPairing

/-- Exact extraction compatibility expected in paper case (2): after
deleting the paired head, every extracted interval is shifted by one
and no terminal head interval is created. -/
def ContractionExtractCompatible {n : ℕ}
    (d : MarkedSingle (Fin n)) : Prop :=
  extract (wickHeadEquiv n (Sum.inr d)) =
    (extract d.pairing).map hdSuccPair

/-- The singles of a contracted pairing are the shifted old singles
with the marked partner removed. -/
theorem singles_wickHeadEquiv_contraction
    {n : ℕ} (d : MarkedSingle (Fin n)) :
    (wickHeadEquiv n (Sum.inr d)).singles =
      (d.pairing.singles.erase d.index).map
        (Fin.succEmb n) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [mem_singles,
      hd_wickHeadEquiv_contraction_zero]
    constructor
    · intro heq
      exact False.elim (Fin.succ_ne_zero d.index heq)
    · intro h
      rw [Finset.mem_map] at h
      obtain ⟨j, _hj, hj0⟩ := h
      exact False.elim (Fin.succ_ne_zero j hj0)
  · by_cases hj : j = d.index
    · subst j
      rw [mem_singles,
        hd_wickHeadEquiv_contraction_partner]
      constructor
      · intro heq
        exact False.elim
          (Fin.succ_ne_zero d.index heq.symm)
      · intro h
        rw [Finset.mem_map] at h
        obtain ⟨k, hk, hkeq⟩ := h
        have hkEq : k = d.index := by
          exact Fin.succ_injective n hkeq
        subst k
        exact False.elim
          (Finset.notMem_erase
            d.index d.pairing.singles hk)
    · rw [mem_singles,
        hd_wickHeadEquiv_contraction_succ_ne d j hj]
      simp only [Fin.succ_inj]
      simp [mem_singles, hj]

/-- Sorting after erasing a member is the same as erasing it from the
sorted list. -/
theorem sort_erase_eq_sort_erase
    {α : Type*} [LinearOrder α]
    (s : Finset α) (a : α) :
    (s.erase a).sort = s.sort.erase a := by
  have hnodup : (s.sort.erase a).Nodup :=
    (s.sort_nodup (· ≤ ·)).erase a
  have hpairwise :
      (s.sort.erase a).Pairwise (· ≤ ·) :=
    (Finset.pairwise_sort s (· ≤ ·)).erase a
  have hsorted :=
    (List.toFinset_sort (· ≤ ·) hnodup).2 hpairwise
  have hfin :
      (s.sort.erase a).toFinset = s.erase a := by
    ext x
    rw [List.mem_toFinset,
      (s.sort_nodup (· ≤ ·)).mem_erase_iff,
      Finset.mem_erase, Finset.mem_sort (· ≤ ·)]
  simpa only [hfin] using hsorted

/-- On a nodup sorted finset list, erasing a member agrees with erasing
the entry at its `idxOf`. -/
theorem sort_erase_eq_eraseIdx_idxOf
    {α : Type*} [LinearOrder α]
    (s : Finset α) (a : α) (ha : a ∈ s) :
    s.sort.erase a =
      s.sort.eraseIdx (s.sort.idxOf a) := by
  let j : Fin s.sort.length :=
    ⟨s.sort.idxOf a,
      List.idxOf_lt_length_iff.mpr
        (by
          rw [Finset.mem_sort
            (fun x y : α => x ≤ y)]
          exact ha)⟩
  have h :=
    (s.sort_nodup (· ≤ ·)).erase_get j
  have hget : s.sort.get j = a := by
    exact List.getElem_idxOf j.isLt
  simpa only [hget, j] using h

/-- The Wick labels of a contracted pairing are the old Wick labels
with the marked partner removed at its ordered rank. -/
theorem wickAtSingleLabels_wickHeadEquiv_contraction
    {n : ℕ} (d : MarkedSingle (Fin n))
    (xt : Fin (n + 3) → T4) :
    wickAtSingleLabels
        (wickHeadEquiv n (Sum.inr d)) xt =
      (wickAtSingleLabels d.pairing
        (ambientTailTuple
          (by omega : 1 ≤ n + 1) xt)).eraseIdx
        (d.pairing.singles.sort.idxOf d.index) := by
  rw [wickAtSingleLabels_eq_sort_map,
    singles_wickHeadEquiv_contraction]
  have hsort :
      (d.pairing.singles.erase d.index).sort.map
          Fin.succ =
        ((d.pairing.singles.erase d.index).map
          (Fin.succEmb n)).sort := by
    exact StrictMonoOn.map_finsetSort
      (Fin.succEmb n)
      (d.pairing.singles.erase d.index)
      (Fin.strictMono_succ.strictMonoOn
        (↑(d.pairing.singles.erase d.index) :
          Set (Fin n)))
  rw [← hsort, List.map_map]
  rw [wickAtSingleLabels_eq_sort_map,
    List.eraseIdx_map]
  rw [sort_erase_eq_sort_erase,
    sort_erase_eq_eraseIdx_idxOf
      d.pairing.singles d.index d.isSingle]
  apply List.map_congr_left
  intro i hi
  apply congrArg xt
  apply Fin.ext
  simp only [varIdx_val, Fin.val_succ]
  omega

/-- Reindexing a ranked single preserves the underlying pairing. -/
@[simp]
theorem rankedSingleEquiv_pairing
    {n : ℕ} (κ : PartialPairing (Fin n))
    (j : Fin κ.singles.card) :
    (rankedSingleEquiv (Fin n) ⟨κ, j⟩).pairing = κ := by
  rfl

/-- The marked index obtained from a rank is the increasing single
enumeration at that rank. -/
@[simp]
theorem rankedSingleEquiv_index
    {n : ℕ} (κ : PartialPairing (Fin n))
    (j : Fin κ.singles.card) :
    (rankedSingleEquiv (Fin n) ⟨κ, j⟩).index =
      κ.singles.orderEmbOfFin rfl j := by
  rfl

/-- Converting a ranked single to a marked single and then locating it
in the sorted single list returns the original rank. -/
theorem rankedSingleEquiv_idxOf
    {n : ℕ} (κ : PartialPairing (Fin n))
    (j : Fin κ.singles.card) :
    κ.singles.sort.idxOf
        (rankedSingleEquiv (Fin n) ⟨κ, j⟩).index =
      j.val := by
  let e := κ.singles.orderIsoOfFin rfl
  have h :=
    Finset.orderIsoOfFin_symm_apply
      κ.singles rfl (e j)
  have he : e.symm (e j) = j :=
    e.symm_apply_apply j
  rw [he] at h
  exact h.symm

/-- The rank `j` transported to the definitionally equal length of the
Wick label list. -/
def wickRankIndex
    {n : ℕ} (κ : PartialPairing (Fin n))
    (xt : Fin (n + 2) → T4)
    (j : Fin κ.singles.card) :
    Fin (wickAtSingleLabels κ xt).length :=
  Fin.cast (wickAtSingleLabels_length κ xt).symm j

@[simp]
theorem wickRankIndex_val
    {n : ℕ} (κ : PartialPairing (Fin n))
    (xt : Fin (n + 2) → T4)
    (j : Fin κ.singles.card) :
    (wickRankIndex κ xt j).val = j.val := by
  rfl

/-- Looking up the Wick label at an increasing single rank returns the
ambient variable at the corresponding ordered single index. -/
theorem wickAtSingleLabels_get_wickRankIndex
    {n : ℕ} (κ : PartialPairing (Fin n))
    (xt : Fin (n + 2) → T4)
    (j : Fin κ.singles.card) :
    (wickAtSingleLabels κ xt).get
        (wickRankIndex κ xt j) =
      xt (varIdx
        (κ.singles.orderEmbOfFin rfl j)) := by
  rw [wickAtSingleLabels_get_eq]
  rfl

/-- A shifted extracted pair has exactly the old difference factor on
the tuple with its first coordinate removed. -/
theorem diffFactor_hdSuccPair
    {n : ℕ} (xt : Fin (n + 3) → T4)
    (p : Fin n × Fin n) :
    diffFactor xt (hdSuccPair p) =
      diffFactor
        (ambientTailTuple
          (by omega : 1 ≤ n + 1) xt) p := by
  unfold diffFactor hdSuccPair ambientTailTuple
  apply congrArg₂ (· - ·)
  · apply congrArg greenFn
    apply congrArg₂ (· - ·)
    · apply congrArg xt
      apply Fin.ext
      simp only [varIdx_val, Fin.val_succ]
      omega
    · apply congrArg xt
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
  · apply congrArg greenFn
    apply congrArg₂ (· - ·)
    · apply congrArg xt
      apply Fin.ext
      simp only [varIdx_val, Fin.val_succ]
      omega
    · apply congrArg xt
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

/-- Under extraction compatibility, adjoining the paired head adds only
the new first Green edge to the chain product. -/
theorem chainProduct_wickHeadEquiv_contraction
    {n : ℕ} (d : MarkedSingle (Fin n))
    (hExtract : ContractionExtractCompatible d)
    (xt : Fin (n + 3) → T4) :
    (∏ e : Fin (n + 2),
        if e.val ∈
            (extract (wickHeadEquiv n (Sum.inr d))).map
              (fun p => p.2.val + 1) then 1
        else greenFn (xt e.castSucc - xt e.succ)) =
      greenFn (xt 0 - xt 1) *
        ∏ e : Fin (n + 1),
          if e.val ∈
              (extract d.pairing).map
                (fun p => p.2.val + 1) then 1
          else greenFn
            (ambientTailTuple
                (by omega : 1 ≤ n + 1) xt e.castSucc -
              ambientTailTuple
                (by omega : 1 ≤ n + 1) xt e.succ) := by
  let rvNew :=
    (extract (wickHeadEquiv n (Sum.inr d))).map
      (fun p => p.2.val + 1)
  let rvOld :=
    (extract d.pairing).map
      (fun p => p.2.val + 1)
  have hrv :
      rvNew =
        (extract d.pairing).map
          (fun p => p.2.val + 2) := by
    dsimp only [rvNew]
    rw [hExtract, List.map_map]
    apply List.map_congr_left
    intro p hp
    unfold hdSuccPair
    simp only [Function.comp_apply, Fin.val_succ]
  have hzero : 0 ∉ rvNew := by
    rw [hrv]
    intro h
    obtain ⟨p, _hp, heq⟩ := List.mem_map.mp h
    omega
  have hsucc (e : Fin (n + 1)) :
      e.succ.val ∈ rvNew ↔ e.val ∈ rvOld := by
    rw [hrv]
    constructor
    · intro h
      obtain ⟨p, hp, heq⟩ := List.mem_map.mp h
      exact List.mem_map.mpr ⟨p, hp, by
        simp only [Fin.val_succ] at heq
        omega⟩
    · intro h
      obtain ⟨p, hp, heq⟩ := List.mem_map.mp h
      exact List.mem_map.mpr ⟨p, hp, by
        simp only [Fin.val_succ]
        omega⟩
  change
    (∏ e : Fin (n + 2),
        if e.val ∈ rvNew then 1
        else greenFn (xt e.castSucc - xt e.succ)) = _
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, if_neg hzero]
  apply congrArg (greenFn (xt 0 - xt 1) * ·)
  apply Finset.prod_congr rfl
  intro e _he
  by_cases h : e.val ∈ rvOld
  · rw [if_pos h, if_pos ((hsucc e).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((hsucc e).mp h'))]
    apply congrArg greenFn
    apply congrArg₂ (· - ·)
    · apply congrArg xt
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    · apply congrArg xt
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

/-- Under extraction compatibility, the difference-factor product is
the old product on the tail tuple. -/
theorem differenceProduct_wickHeadEquiv_contraction
    {n : ℕ} (d : MarkedSingle (Fin n))
    (hExtract : ContractionExtractCompatible d)
    (xt : Fin (n + 3) → T4) :
    ((extract (wickHeadEquiv n (Sum.inr d))).map
        (diffFactor xt)).prod =
      ((extract d.pairing).map
        (diffFactor
          (ambientTailTuple
            (by omega : 1 ≤ n + 1) xt))).prod := by
  rw [hExtract, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro p hp
  exact diffFactor_hdSuccPair xt p

/-- The covariance ledger of a contraction consists of the new
head--partner covariance and the old covariance product. -/
theorem covarianceProduct_wickHeadEquiv_contraction
    (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (d : MarkedSingle (Fin n))
    (xt : Fin (n + 3) → T4) :
    (∏ k ∈
        (wickHeadEquiv n (Sum.inr d)).pairSupport.filter
          (fun k => k < wickHeadEquiv n (Sum.inr d) k),
        ρ.etaEpsT4 ε
          (xt (varIdx k) -
            xt (varIdx
              (wickHeadEquiv n (Sum.inr d) k)))) =
      ρ.etaEpsT4 ε
          (xt 1 -
            ambientTailTuple
              (by omega : 1 ≤ n + 1) xt
              (varIdx d.index)) *
        ∏ i ∈ d.pairing.pairSupport.filter
            (fun i => i < d.pairing i),
          ρ.etaEpsT4 ε
            (ambientTailTuple
                (by omega : 1 ≤ n + 1) xt
                (varIdx i) -
              ambientTailTuple
                (by omega : 1 ≤ n + 1) xt
                (varIdx (d.pairing i))) := by
  let K := wickHeadEquiv n (Sum.inr d)
  rw [← Finset.prod_ite_mem_eq]
  rw [Fin.prod_univ_succ]
  have hheadMem :
      (0 : Fin (n + 1)) ∈
        K.pairSupport.filter (fun k => k < K k) := by
    simp only [Finset.mem_filter, mem_pairSupport]
    dsimp only [K]
    rw [hd_wickHeadEquiv_contraction_zero]
    exact ⟨Fin.succ_ne_zero d.index,
      Fin.pos_iff_ne_zero.mpr (Fin.succ_ne_zero d.index)⟩
  rw [if_pos hheadMem]
  have hheadFactor :
      ρ.etaEpsT4 ε
          (xt (varIdx (0 : Fin (n + 1))) -
            xt (varIdx (K 0))) =
        ρ.etaEpsT4 ε
          (xt 1 -
            ambientTailTuple
              (by omega : 1 ≤ n + 1) xt
              (varIdx d.index)) := by
    apply congrArg (ρ.etaEpsT4 ε)
    apply congrArg₂ (· - ·)
    · apply congrArg xt
      apply Fin.ext
      rfl
    · apply congrArg xt
      apply Fin.ext
      dsimp only [K]
      rw [hd_wickHeadEquiv_contraction_zero]
      simp only [varIdx_val, Fin.val_succ]
      omega
  rw [hheadFactor]
  apply congrArg
    (ρ.etaEpsT4 ε
      (xt 1 -
        ambientTailTuple
          (by omega : 1 ≤ n + 1) xt
          (varIdx d.index)) * ·)
  calc
    (∏ i : Fin n,
        if i.succ ∈
            K.pairSupport.filter (fun k => k < K k)
        then
          ρ.etaEpsT4 ε
            (xt (varIdx i.succ) -
              xt (varIdx (K i.succ)))
        else 1) =
        ∏ i : Fin n,
          if i ∈ d.pairing.pairSupport.filter
              (fun j => j < d.pairing j)
          then
            ρ.etaEpsT4 ε
              (ambientTailTuple
                  (by omega : 1 ≤ n + 1) xt
                  (varIdx i) -
                ambientTailTuple
                  (by omega : 1 ≤ n + 1) xt
                  (varIdx (d.pairing i)))
          else 1 := by
      apply Finset.prod_congr rfl
      intro i _hi
      have hrep :
          i.succ ∈ K.pairSupport.filter
              (fun k => k < K k) ↔
            i ∈ d.pairing.pairSupport.filter
              (fun j => j < d.pairing j) := by
        simp only [Finset.mem_filter, mem_pairSupport]
        by_cases hid : i = d.index
        · subst i
          dsimp only [K]
          rw [hd_wickHeadEquiv_contraction_partner]
          have hsingle :
              d.pairing d.index = d.index :=
            mem_singles.mp d.isSingle
          simp only [hsingle, ne_eq, not_true_eq_false,
            false_and]
          constructor
          · rintro ⟨_hne, hlt⟩
            exact Fin.not_lt_zero _ hlt
          · intro h
            contradiction
        · dsimp only [K]
          rw [hd_wickHeadEquiv_contraction_succ_ne d i hid]
          simp only [Fin.succ_lt_succ_iff]
          constructor
          · rintro ⟨hne, hlt⟩
            exact ⟨fun heq => hne (congrArg Fin.succ heq), hlt⟩
          · rintro ⟨hne, hlt⟩
            refine ⟨?_, hlt⟩
            intro heq
            apply hne
            apply Fin.ext
            have hv := congrArg Fin.val heq
            simp only [Fin.val_succ] at hv
            omega
      by_cases h :
          i ∈ d.pairing.pairSupport.filter
            (fun j => j < d.pairing j)
      · rw [if_pos h, if_pos (hrep.mpr h)]
        have hid : i ≠ d.index := by
          intro hi
          subst i
          have hsingle :
              d.pairing d.index = d.index :=
            mem_singles.mp d.isSingle
          simp [mem_pairSupport, hsingle] at h
        dsimp only [K]
        rw [hd_wickHeadEquiv_contraction_succ_ne d i hid]
        apply congrArg (ρ.etaEpsT4 ε)
        apply congrArg₂ (· - ·)
        · apply congrArg xt
          apply Fin.ext
          simp only [varIdx_val, Fin.val_succ]
          omega
        · apply congrArg xt
          apply Fin.ext
          simp only [varIdx_val, Fin.val_succ]
          omega
      · rw [if_neg h,
          if_neg (fun h' => h (hrep.mp h'))]
    _ = _ := Finset.prod_ite_mem_eq
      (d.pairing.pairSupport.filter
        (fun j => j < d.pairing j))
      (fun i =>
        ρ.etaEpsT4 ε
          (ambientTailTuple
              (by omega : 1 ≤ n + 1) xt
              (varIdx i) -
            ambientTailTuple
              (by omega : 1 ≤ n + 1) xt
              (varIdx (d.pairing i))))

/-- Deterministic closed-form factorization for a paired head whose
extraction list only shifts under head deletion. -/
theorem detIntegrand_wickHeadEquiv_contraction
    (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (d : MarkedSingle (Fin n))
    (hExtract : ContractionExtractCompatible d)
    (xt : Fin (n + 3) → T4) :
    detIntegrand ρ ε (n + 1)
        (wickHeadEquiv n (Sum.inr d)) xt =
      greenFn (xt 0 - xt 1) *
        (ρ.etaEpsT4 ε
            (xt 1 -
              ambientTailTuple
                (by omega : 1 ≤ n + 1) xt
                (varIdx d.index)) *
          detIntegrand ρ ε n d.pairing
            (ambientTailTuple
              (by omega : 1 ≤ n + 1) xt)) := by
  unfold detIntegrand
  rw [chainProduct_wickHeadEquiv_contraction
    d hExtract xt]
  rw [differenceProduct_wickHeadEquiv_contraction
    d hExtract xt]
  rw [covarianceProduct_wickHeadEquiv_contraction
    ρ ε d xt]
  ac_rfl

/-- The Wick factor of a contraction is the Wick polynomial with the
marked old single removed. -/
theorem wickAt_wickHeadEquiv_contraction
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (d : MarkedSingle (Fin n))
    (xt : Fin (n + 3) → T4) (ω : M.Ω) :
    wickAt M ρ ε
        (wickHeadEquiv n (Sum.inr d)) xt ω =
      wickPolynomial
        (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
        (fun x ω' => M.xiEps ρ ε ω' x)
        ((wickAtSingleLabels d.pairing
          (ambientTailTuple
            (by omega : 1 ≤ n + 1) xt)).eraseIdx
          (d.pairing.singles.sort.idxOf d.index)) ω := by
  rw [wickAt_eq_wickPolynomial,
    wickAtSingleLabels_wickHeadEquiv_contraction]

/-- Pointwise Wick-contraction compatibility, conditional only on the
explicit extraction shift that distinguishes paper case (2) from case
(3). -/
theorem headPairedContractionTerm_eq_randIntegrand
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (d : MarkedSingle (Fin n))
    (hExtract : ContractionExtractCompatible d)
    (xt : Fin (n + 3) → T4) (ω : M.Ω) :
    greenFn (xt 0 - xt 1) *
        (detIntegrand ρ ε n d.pairing
            (ambientTailTuple
              (by omega : 1 ≤ n + 1) xt) *
          (ρ.etaEpsT4 ε
              (xt 1 -
                ambientTailTuple
                  (by omega : 1 ≤ n + 1) xt
                  (varIdx d.index)) *
            wickPolynomial
              (fun x y : T4 =>
                ρ.etaEpsT4 ε (x - y))
              (fun x ω' =>
                M.xiEps ρ ε ω' x)
              ((wickAtSingleLabels d.pairing
                (ambientTailTuple
                  (by omega : 1 ≤ n + 1) xt)).eraseIdx
                (d.pairing.singles.sort.idxOf
                  d.index)) ω)) =
      randIntegrand M ρ ε
        (wickHeadEquiv n (Sum.inr d)) xt ω := by
  unfold randIntegrand
  rw [detIntegrand_wickHeadEquiv_contraction
    ρ ε d hExtract xt]
  rw [wickAt_wickHeadEquiv_contraction
    M ρ ε d xt ω]
  ac_rfl

/-- The integrated contraction source attached to one marked old
single.  Its indexing is deliberately by `MarkedSingle`: the separate
rank ledger below identifies this with the `j`-th term in the Wick
recursion. -/
def headPairedContractionContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (d : MarkedSingle (Fin n))
    (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε ^ (n + 1) *
    (∫ z : T4, ∫ v : Fin n → T4,
      greenFn (x - z) *
        (detIntegrand ρ ε n d.pairing
            (assemble z y v) *
          (ρ.etaEpsT4 ε
              (z -
                assemble z y v
                  (varIdx d.index)) *
            wickPolynomial
              (fun a b : T4 =>
                ρ.etaEpsT4 ε (a - b))
              (fun a ω' =>
                M.xiEps ρ ε ω' a)
              ((wickAtSingleLabels d.pairing
                (assemble z y v)).eraseIdx
                  (d.pairing.singles.sort.idxOf
                    d.index)) ω))
      ∂(Measure.pi fun _ => paperMeasure)
      ∂paperMeasure)

/-- The same contraction source in the rank indexing produced directly
by the Wick creation--contraction formula. -/
def rankedContractionContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (j : Fin κ.singles.card)
    (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε ^ (n + 1) *
    (∫ z : T4, ∫ v : Fin n → T4,
      greenFn (x - z) *
        (detIntegrand ρ ε n κ
            (assemble z y v) *
          (ρ.etaEpsT4 ε
              (z -
                (wickAtSingleLabels κ
                  (assemble z y v)).get
                    (wickRankIndex κ
                      (assemble z y v) j)) *
            wickPolynomial
              (fun a b : T4 =>
                ρ.etaEpsT4 ε (a - b))
              (fun a ω' =>
                M.xiEps ρ ε ω' a)
              ((wickAtSingleLabels κ
                (assemble z y v)).eraseIdx
                  (wickRankIndex κ
                    (assemble z y v) j).val) ω))
      ∂(Measure.pi fun _ => paperMeasure)
      ∂paperMeasure)

/-- Rank indexing and marked-single indexing define literally the same
integrated contraction source. -/
theorem rankedContractionContribution_eq_headPaired
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (j : Fin κ.singles.card)
    (x y : T4) (ω : M.Ω) :
    rankedContractionContribution
        M ρ lam ε n κ j x y ω =
      headPairedContractionContribution
        M ρ lam ε n
          (rankedSingleEquiv (Fin n) ⟨κ, j⟩)
          x y ω := by
  unfold rankedContractionContribution
  unfold headPairedContractionContribution
  simp only [rankedSingleEquiv_pairing]
  rw [rankedSingleEquiv_idxOf]
  simp only [rankedSingleEquiv_index,
    wickRankIndex_val]
  apply congrArg (lamEps lam ε ^ (n + 1) * ·)
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with v
  rw [wickAtSingleLabels_get_wickRankIndex]

/-- Integrated paired-head contraction.  Under the exact extraction
shift for paper case (2) and the Fubini integrability hypothesis, the
contraction source is the random kernel indexed by the new pairing. -/
theorem headPairedContractionContribution_eq_randRI
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (d : MarkedSingle (Fin n))
    (hExtract : ContractionExtractCompatible d)
    (x y : T4) (ω : M.Ω)
    (hint :
      Integrable
        (fun u : Fin (n + 1) → T4 =>
          randIntegrand M ρ ε
            (wickHeadEquiv n (Sum.inr d))
            (assemble x y u) ω)
        (Measure.pi fun _ => paperMeasure)) :
    headPairedContractionContribution
        M ρ lam ε n d x y ω =
      randRI M ρ lam ε (n + 1)
        (wickHeadEquiv n (Sum.inr d))
        x y ω := by
  unfold headPairedContractionContribution
  unfold randRI
  rw [integral_headTailVariables n _ hint]
  apply congrArg (lamEps lam ε ^ (n + 1) * ·)
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with v
  have hpoint :=
    headPairedContractionTerm_eq_randIntegrand
      M ρ ε d hExtract
      (assemble x y (Fin.cons z v)) ω
  rw [ambientTailTuple_assemble_cons,
    assemble_cons_first_internal, assemble_zero] at hpoint
  exact hpoint

/-- The integrated contraction theorem in the rank indexing occurring in
the Wick recursion. -/
theorem rankedContractionContribution_eq_randRI
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (j : Fin κ.singles.card)
    (hExtract :
      ContractionExtractCompatible
        (rankedSingleEquiv (Fin n) ⟨κ, j⟩))
    (x y : T4) (ω : M.Ω)
    (hint :
      Integrable
        (fun u : Fin (n + 1) → T4 =>
          randIntegrand M ρ ε
            (wickHeadEquiv n
              (Sum.inr
                (rankedSingleEquiv
                  (Fin n) ⟨κ, j⟩)))
            (assemble x y u) ω)
        (Measure.pi fun _ => paperMeasure)) :
    rankedContractionContribution
        M ρ lam ε n κ j x y ω =
      randRI M ρ lam ε (n + 1)
        (wickHeadEquiv n
          (Sum.inr
            (rankedSingleEquiv
              (Fin n) ⟨κ, j⟩)))
        x y ω := by
  rw [rankedContractionContribution_eq_headPaired]
  exact headPairedContractionContribution_eq_randRI
    M ρ lam ε n
      (rankedSingleEquiv (Fin n) ⟨κ, j⟩)
      hExtract x y ω hint

end PartialPairing

end

end Anderson4D
