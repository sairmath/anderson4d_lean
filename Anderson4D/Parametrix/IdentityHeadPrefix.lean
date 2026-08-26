import Anderson4D.Parametrix.IdentityCaseThreeSum
import Anderson4D.Parametrix.IdentityHeadPaired

/-!
# The paired-head branch with a closed non-split prefix

This file connects the actual Wick-contraction summand obtained by
deleting the paired head of an assembled case-(3) pairing with the
`J × R` source used in the paper's prefix-collapse argument.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-- The head of a non-split prefix remains paired after an arbitrary
pairing is appended to it. -/
theorem appendPairing_nonSplit_head_ne
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ) :
    appendPairing σ τ 0 ≠ 0 := by
  have hzero :
      (0 : Fin (2 * (q + 1) + r)) =
        Fin.castAdd r (0 : Fin (2 * (q + 1))) := by
    apply Fin.ext
    rfl
  rw [hzero, appendPairing_apply_castAdd]
  intro h
  apply hσ.1 0
  apply Fin.ext
  simpa using congrArg Fin.val h

/-- The assembled pairing transported to the successor presentation of
its cardinality used by head deletion. -/
def caseThreeHeadPairing
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r)) :
    PartialPairing (Fin ((2 * q + 1 + r) + 1)) :=
  arithmeticCastPairing
    (by omega :
      2 * (q + 1) + r = (2 * q + 1 + r) + 1)
    (appendPairing σ τ)

theorem caseThreeHeadPairing_zero_ne
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ) :
    caseThreeHeadPairing q r σ τ 0 ≠ 0 := by
  unfold caseThreeHeadPairing arithmeticCastPairing
  rw [PartialPairing.congr_apply_apply]
  intro h
  apply appendPairing_nonSplit_head_ne q r σ τ hσ
  apply Fin.ext
  simpa using congrArg Fin.val h

@[simp]
theorem caseThreeHeadPairing_apply_val
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (i : Fin ((2 * q + 1 + r) + 1)) :
    (caseThreeHeadPairing q r σ τ i).val =
      (appendPairing σ τ
        ⟨i.val, by omega⟩).val := by
  rfl

/-- Head deletion inside the non-split prefix alone. -/
def caseThreePrefixHeadDeletionData
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (hσ : IsNonSplit σ) :
    MarkedSingle (Fin (2 * q + 1)) :=
  headDeletionData
    (n := 2 * q + 1) σ (hσ.1 0)

/-- Append a tail pairing to marked-single data in a consecutive
prefix. -/
def appendMarkedSingle
    {a b : ℕ}
    (d : MarkedSingle (Fin a))
    (τ : PartialPairing (Fin b)) :
    MarkedSingle (Fin (a + b)) where
  pairing := appendPairing d.pairing τ
  index := Fin.castAdd b d.index
  isSingle :=
    (appendPairing_castAdd_mem_singles
      d.pairing τ d.index).mpr d.isSingle

/-- The marked old single obtained by deleting the head of an assembled
case-(3) pairing. -/
def caseThreeHeadDeletionData
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ) :
    MarkedSingle (Fin (2 * q + 1 + r)) :=
  headDeletionData
    (n := 2 * q + 1 + r)
    (caseThreeHeadPairing q r σ τ)
    (caseThreeHeadPairing_zero_ne q r σ τ hσ)

/-- Deleting the assembled head acts only on the non-split prefix; the
tail pairing is unchanged. -/
theorem caseThreeHeadDeletionData_eq_append
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ) :
    caseThreeHeadDeletionData q r σ τ hσ =
      appendMarkedSingle
        (caseThreePrefixHeadDeletionData q σ hσ) τ := by
  let K := caseThreeHeadPairing q r σ τ
  let hK := caseThreeHeadPairing_zero_ne q r σ τ hσ
  let d := caseThreeHeadDeletionData q r σ τ hσ
  let dσ := caseThreePrefixHeadDeletionData q σ hσ
  change d = appendMarkedSingle dσ τ
  have hindexVal : d.index.val = dσ.index.val := by
    have hKzero :=
      congrArg Fin.val (headDeletionData_zero K hK)
    have hσzero :=
      congrArg Fin.val
        (headDeletionData_zero σ (hσ.1 0))
    rw [caseThreeHeadPairing_apply_val] at hKzero
    have hzero :
        (⟨(0 : Fin ((2 * q + 1 + r) + 1)).val,
          by omega⟩ :
            Fin (2 * (q + 1) + r)) =
          Fin.castAdd r
            (0 : Fin (2 * (q + 1))) := by
      apply Fin.ext
      rfl
    rw [hzero, appendPairing_apply_castAdd] at hKzero
    change (σ 0).val = d.index.val + 1 at hKzero
    change (σ 0).val = dσ.index.val + 1 at hσzero
    omega
  have hindex :
      d.index = Fin.castAdd r dσ.index := by
    apply Fin.ext
    exact hindexVal
  apply MarkedSingle.ext
  · apply PartialPairing.ext
    intro i
    apply Fin.ext
    by_cases hiIndex : i = d.index
    · subst i
      have hdSingle :
          d.pairing d.index = d.index :=
        mem_singles.mp d.isSingle
      rw [hdSingle]
      rw [hindex]
      change (Fin.castAdd r dσ.index).val =
        (appendPairing dσ.pairing τ
          (Fin.castAdd r dσ.index)).val
      rw [appendPairing_apply_castAdd]
      have hdσSingle :
          dσ.pairing dσ.index = dσ.index :=
        mem_singles.mp dσ.isSingle
      rw [hdσSingle]
    · have hrec :=
        congrArg Fin.val
          (headDeletionData_succ_ne K hK i hiIndex)
      change (K i.succ).val =
        (d.pairing i).val + 1 at hrec
      rw [caseThreeHeadPairing_apply_val] at hrec
      by_cases hiprefix : i.val < 2 * q + 1
      · let j : Fin (2 * q + 1) :=
          ⟨i.val, hiprefix⟩
        have hjIndex : j ≠ dσ.index := by
          intro hj
          apply hiIndex
          apply Fin.ext
          have hij : i.val = j.val := rfl
          rw [hij, hj, hindexVal]
        have hσrec :=
          congrArg Fin.val
            (headDeletionData_succ_ne
              σ (hσ.1 0) j hjIndex)
        have hnewPrefix :
            (⟨i.succ.val, by omega⟩ :
                Fin (2 * (q + 1) + r)) =
              Fin.castAdd r j.succ := by
          apply Fin.ext
          rfl
        rw [hnewPrefix,
          appendPairing_apply_castAdd] at hrec
        change (σ j.succ).val =
          (d.pairing i).val + 1 at hrec
        change (σ j.succ).val =
          (dσ.pairing j).val + 1 at hσrec
        change
          (d.pairing i).val =
            (appendPairing dσ.pairing τ
              (Fin.castAdd r j)).val
        rw [appendPairing_apply_castAdd]
        change
          (d.pairing i).val =
            (dσ.pairing j).val
        omega
      · have hisuffix : 2 * q + 1 ≤ i.val :=
          Nat.le_of_not_gt hiprefix
        let j : Fin r :=
          ⟨i.val - (2 * q + 1), by
            have := i.isLt
            omega⟩
        have hnewSuffix :
            (⟨i.succ.val, by omega⟩ :
                Fin (2 * (q + 1) + r)) =
              Fin.natAdd (2 * (q + 1)) j := by
          apply Fin.ext
          change i.val + 1 =
            2 * (q + 1) + j.val
          dsimp only [j]
          omega
        rw [hnewSuffix,
          appendPairing_apply_natAdd] at hrec
        change (Fin.natAdd (2 * (q + 1)) (τ j)).val =
          (d.pairing i).val + 1 at hrec
        have holdSuffix :
            i =
              Fin.natAdd (2 * q + 1) j := by
          apply Fin.ext
          change i.val = 2 * q + 1 + j.val
          dsimp only [j]
          omega
        rw [holdSuffix]
        change
          (d.pairing
              (Fin.natAdd (2 * q + 1) j)).val =
            (appendPairing dσ.pairing τ
              (Fin.natAdd (2 * q + 1) j)).val
        rw [appendPairing_apply_natAdd]
        change
          2 * (q + 1) + (τ j).val =
            (d.pairing i).val + 1 at hrec
        change
          (d.pairing
              (Fin.natAdd (2 * q + 1) j)).val =
            2 * q + 1 + (τ j).val
        rw [← holdSuffix]
        omega
  · apply Fin.ext
    exact hindexVal

/-- Removing the head pair from a full non-split prefix leaves exactly
its former partner as a single. -/
theorem caseThreePrefixHeadDeletion_singles
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (hσ : IsNonSplit σ) :
    (caseThreePrefixHeadDeletionData q σ hσ).pairing.singles =
      {(caseThreePrefixHeadDeletionData q σ hσ).index} := by
  let d := caseThreePrefixHeadDeletionData q σ hσ
  have hpair :
      wickHeadEquiv (2 * q + 1) (Sum.inr d) = σ := by
    exact contractionHeadEquiv_headDeletionData
      σ (hσ.1 0)
  have hfullSingles :
      (wickHeadEquiv (2 * q + 1) (Sum.inr d)).singles =
        ∅ := by
    rw [hpair]
    exact isFull_iff_singles_eq_empty.mp hσ.1
  rw [singles_wickHeadEquiv_contraction] at hfullSingles
  have herase :
      d.pairing.singles.erase d.index = ∅ := by
    exact Finset.map_eq_empty.mp hfullSingles
  rcases (Finset.erase_eq_empty_iff
      d.pairing.singles d.index).mp herase with hempty | hsingle
  · exfalso
    have : d.index ∉ d.pairing.singles := by
      rw [hempty]
      simp
    exact this d.isSingle
  · exact hsingle

/-- In assembled case-(3) data, the marked prefix single is the first
single in increasing order; all other singles come from the tail. -/
theorem caseThreeHeadDeletion_singles
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ) :
    (caseThreeHeadDeletionData q r σ τ hσ).pairing.singles =
      insert
        (caseThreeHeadDeletionData q r σ τ hσ).index
        (τ.singles.map (Fin.natAddEmb (2 * q + 1))) := by
  let d := caseThreeHeadDeletionData q r σ τ hσ
  let dσ := caseThreePrefixHeadDeletionData q σ hσ
  have hd :
      d = appendMarkedSingle dσ τ :=
    caseThreeHeadDeletionData_eq_append q r σ τ hσ
  have hdσSingles :
      dσ.pairing.singles = {dσ.index} :=
    caseThreePrefixHeadDeletion_singles q σ hσ
  change d.pairing.singles =
    insert d.index
      (τ.singles.map (Fin.natAddEmb (2 * q + 1)))
  rw [hd]
  ext i
  obtain ⟨i, rfl⟩ :=
    (finSumFinEquiv :
      Fin (2 * q + 1) ⊕ Fin r ≃
        Fin (2 * q + 1 + r)).surjective i
  cases i with
  | inl j =>
      rw [finSumFinEquiv_apply_left]
      change
        Fin.castAdd r j ∈
            (appendPairing dσ.pairing τ).singles ↔
          Fin.castAdd r j ∈
            insert (Fin.castAdd r dσ.index)
              (τ.singles.map
                (Fin.natAddEmb (2 * q + 1)))
      rw [appendPairing_castAdd_mem_singles]
      rw [hdσSingles]
      simp only [Finset.mem_singleton,
        Finset.mem_insert, Finset.mem_map]
      constructor
      · intro hj
        exact Or.inl (congrArg (Fin.castAdd r) hj)
      · rintro (heq | ⟨k, _hk, heq⟩)
        · exact Fin.castAdd_inj.mp heq
        · have hv := congrArg Fin.val heq
          change
            2 * q + 1 + k.val = j.val at hv
          have hjlt := j.isLt
          omega
  | inr j =>
      rw [finSumFinEquiv_apply_right]
      change
        Fin.natAdd (2 * q + 1) j ∈
            (appendPairing dσ.pairing τ).singles ↔
          Fin.natAdd (2 * q + 1) j ∈
            insert (Fin.castAdd r dσ.index)
              (τ.singles.map
                (Fin.natAddEmb (2 * q + 1)))
      rw [appendPairing_natAdd_mem_singles]
      simp only [Finset.mem_insert, Finset.mem_map]
      constructor
      · intro hj
        exact Or.inr
          ⟨j, hj, by
            apply Fin.ext
            rfl⟩
      · rintro (heq | ⟨k, hk, heq⟩)
        · have hv := congrArg Fin.val heq
          change
            2 * q + 1 + j.val =
              dσ.index.val at hv
          omega
        · have hjk : j = k := by
            apply Fin.ext
            have hv := congrArg Fin.val heq
            change
              2 * q + 1 + k.val =
                2 * q + 1 + j.val at hv
            omega
          simpa only [hjk] using hk

/-- The marked contraction has rank zero in the ordered singles list. -/
theorem caseThreeHeadDeletion_rank
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ) :
    (caseThreeHeadDeletionData q r σ τ hσ).pairing.singles.sort.idxOf
        (caseThreeHeadDeletionData q r σ τ hσ).index = 0 := by
  let d := caseThreeHeadDeletionData q r σ τ hσ
  let dσ := caseThreePrefixHeadDeletionData q σ hσ
  have hd :
      d = appendMarkedSingle dσ τ :=
    caseThreeHeadDeletionData_eq_append q r σ τ hσ
  have hindexVal : d.index.val = dσ.index.val := by
    have h :=
      congrArg (fun e : MarkedSingle
        (Fin (2 * q + 1 + r)) => e.index.val) hd
    exact h
  change d.pairing.singles.sort.idxOf d.index = 0
  rw [caseThreeHeadDeletion_singles q r σ τ hσ]
  have hnot :
      d.index ∉
        τ.singles.map (Fin.natAddEmb (2 * q + 1)) := by
    intro h
    rw [Finset.mem_map] at h
    obtain ⟨j, _hj, heq⟩ := h
    have hv := congrArg Fin.val heq
    change
      2 * q + 1 + j.val = d.index.val at hv
    have hdlt : d.index.val < 2 * q + 1 := by
      rw [hindexVal]
      exact dσ.index.isLt
    omega
  rw [Finset.sort_insert
    (r := (· ≤ ·))
    (by
      intro b hb
      rw [Finset.mem_map] at hb
      obtain ⟨j, _hj, rfl⟩ := hb
      apply Fin.le_def.mpr
      change d.index.val ≤ 2 * q + 1 + j.val
      have hdlt : d.index.val < 2 * q + 1 := by
        rw [hindexVal]
        exact dσ.index.isLt
      omega)
    hnot]
  exact List.idxOf_cons_self

/-- After removing the marked prefix single, the ordered Wick labels are
exactly the labels of the appended tail pairing. -/
theorem caseThreeHeadDeletion_wickLabels_erase
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (xt : Fin (2 * q + 1 + r + 2) → T4) :
    (wickAtSingleLabels
        (caseThreeHeadDeletionData q r σ τ hσ).pairing
        xt).eraseIdx
        ((caseThreeHeadDeletionData q r σ τ hσ).pairing.singles.sort.idxOf
          (caseThreeHeadDeletionData q r σ τ hσ).index) =
      wickAtSingleLabels τ
        (arithmeticCastTuple
          (by omega :
            (2 * q + 1 + r) - (2 * q + 1) = r)
          (ambientTailTuple
            (by omega :
              2 * q + 1 ≤ 2 * q + 1 + r) xt)) := by
  let d := caseThreeHeadDeletionData q r σ τ hσ
  let a := 2 * q + 1
  let ha : a ≤ a + r := by omega
  change
    (wickAtSingleLabels d.pairing xt).eraseIdx
        (d.pairing.singles.sort.idxOf d.index) =
      wickAtSingleLabels τ
        (arithmeticCastTuple
          (by omega : a + r - a = r)
          (ambientTailTuple ha xt))
  rw [caseThreeHeadDeletion_rank q r σ τ hσ]
  rw [wickAtSingleLabels_eq_sort_map,
    caseThreeHeadDeletion_singles q r σ τ hσ]
  have hnot :
      d.index ∉
        τ.singles.map (Fin.natAddEmb a) := by
    intro h
    rw [Finset.mem_map] at h
    obtain ⟨j, _hj, heq⟩ := h
    have hd :
        d =
          appendMarkedSingle
            (caseThreePrefixHeadDeletionData q σ hσ) τ :=
      caseThreeHeadDeletionData_eq_append q r σ τ hσ
    have hindexVal :
        d.index.val =
          (caseThreePrefixHeadDeletionData q σ hσ).index.val := by
      have hv :=
        congrArg
          (fun e : MarkedSingle (Fin (a + r)) =>
            e.index.val) hd
      exact hv
    have hv := congrArg Fin.val heq
    change a + j.val = d.index.val at hv
    have hdlt : d.index.val < a := by
      rw [hindexVal]
      exact
        (caseThreePrefixHeadDeletionData
          q σ hσ).index.isLt
    omega
  have hle :
      ∀ b ∈ τ.singles.map (Fin.natAddEmb a),
        d.index ≤ b := by
    intro b hb
    rw [Finset.mem_map] at hb
    obtain ⟨j, _hj, rfl⟩ := hb
    apply Fin.le_def.mpr
    have hd :
        d =
          appendMarkedSingle
            (caseThreePrefixHeadDeletionData q σ hσ) τ :=
      caseThreeHeadDeletionData_eq_append q r σ τ hσ
    have hindexVal :
        d.index.val =
          (caseThreePrefixHeadDeletionData q σ hσ).index.val := by
      have hv :=
        congrArg
          (fun e : MarkedSingle (Fin (a + r)) =>
            e.index.val) hd
      exact hv
    have hdlt : d.index.val < a := by
      rw [hindexVal]
      exact
        (caseThreePrefixHeadDeletionData
          q σ hσ).index.isLt
    change d.index.val ≤ a + j.val
    omega
  rw [Finset.sort_insert (r := (· ≤ ·)) hle hnot]
  simp only [List.map_cons, List.eraseIdx_zero]
  have hsort :
      τ.singles.sort.map (Fin.natAdd a) =
        (τ.singles.map (Fin.natAddEmb a)).sort := by
    exact StrictMonoOn.map_finsetSort
      (Fin.natAddEmb a) τ.singles
      (by
        intro i _hi j _hj hij
        exact Fin.strictMono_natAdd a hij)
  rw [← hsort, List.map_map,
    wickAtSingleLabels_eq_sort_map]
  apply List.map_congr_left
  intro j hj
  apply congrArg xt
  apply Fin.ext
  rfl

/-! ## Deterministic ledger for the deleted prefix -/

/-- The first `a+1` spatial slots of an old contraction tuple.  These
are exactly the variables of the closed `J` block: its left endpoint,
the `a-1` remaining internal variables, and its right endpoint. -/
def prefixWithLeftTuple
    {N a : ℕ} (ha : a ≤ N)
    (xt : Fin (N + 2) → T4) :
    Fin (a + 1) → T4 :=
  fun i => xt (Fin.castLE (by omega : a + 1 ≤ N + 2) i)

/-- Deterministic factors carried by a head-deleted prefix, before the
head--partner covariance is restored. -/
def headDeletedPrefixCore
    (ρ : SmoothCutoff) (ε : ℝ)
    (a : ℕ) (κ : PartialPairing (Fin a))
    (xt : Fin (a + 1) → T4) : ℝ :=
  (∏ e : Fin a,
      if e.val ∈
          (extract κ).map (fun p => p.2.val + 1)
      then 1
      else greenFn (xt e.castSucc - xt e.succ)) *
    ((extract κ).map
      (fun p => diffFactorJ xt (hdSuccPair p))).prod *
    ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
      ρ.etaEpsT4 ε
        (xt i.succ - xt (κ i).succ)

/-- Every extraction left after deleting the head of a non-split block
ends strictly before the block's right endpoint. -/
theorem caseThreePrefixHeadDeletion_extract_proper
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (hσ : IsNonSplit σ)
    (p : Fin (2 * q + 1) × Fin (2 * q + 1))
    (hp :
      p ∈ extract
        (caseThreePrefixHeadDeletionData q σ hσ).pairing) :
    p.2.val + 1 < 2 * q + 1 := by
  have hpmap :
      hdSuccPair p ∈
        (extract
          (headDeletionData (n := 2 * q + 1)
            σ (hσ.1 0)).pairing).map hdSuccPair := by
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hproper :=
    nonSplit_proper_right_before_whole
      q σ hσ (hdSuccPair p) hpmap
  simp only [hdSuccPair, Fin.val_succ] at hproper
  omega

/-- A prefix extraction in an old contraction tuple is the corresponding
shifted `J` difference factor. -/
theorem diffFactor_prefix_eq_headDeletedJ
    {N a : ℕ} (ha : a ≤ N)
    (xt : Fin (N + 2) → T4)
    (p : Fin a × Fin a)
    (hp : p.2.val + 1 < a) :
    diffFactor xt (eaPrefixPair ha p) =
      diffFactorJ (prefixWithLeftTuple ha xt)
        (hdSuccPair p) := by
  unfold diffFactor diffFactorJ
  rw [dif_pos (by
    simp only [hdSuccPair, Fin.val_succ]
    omega)]
  unfold eaPrefixPair prefixWithLeftTuple hdSuccPair
  apply congrArg₂ (· - ·)
  · apply congrArg greenFn
    apply congrArg₂ (· - ·)
    · apply congrArg xt
      apply Fin.ext
      rfl
    · apply congrArg xt
      apply Fin.ext
      rfl
  · apply congrArg greenFn
    apply congrArg₂ (· - ·)
    · apply congrArg xt
      apply Fin.ext
      rfl
    · apply congrArg xt
      apply Fin.ext
      rfl

/-- Chain factors split at a consecutive prefix provided no prefix
extraction removes the boundary edge. -/
theorem chainProduct_appendPairingTo_properPrefix
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (xt : Fin (N + 2) → T4)
    (hproper :
      ∀ p ∈ extract σ, p.2.val + 1 < a) :
    (∏ e : Fin (N + 1),
        if e.val ∈
            (extract (appendPairingTo ha σ τ)).map
              (fun p => p.2.val + 1)
        then 1
        else greenFn (xt e.castSucc - xt e.succ)) =
      (∏ e : Fin a,
        if e.val ∈
            (extract σ).map (fun p => p.2.val + 1)
        then 1
        else greenFn
          (prefixWithLeftTuple ha xt e.castSucc -
            prefixWithLeftTuple ha xt e.succ)) *
      ∏ e : Fin (N - a + 1),
        if e.val ∈
            (extract τ).map (fun p => p.2.val + 1)
        then 1
        else greenFn
          (ambientTailTuple ha xt e.castSucc -
            ambientTailTuple ha xt e.succ) := by
  let K := appendPairingTo ha σ τ
  let rvK :=
    (extract K).map (fun p => p.2.val + 1)
  let rvσ :=
    (extract σ).map (fun p => p.2.val + 1)
  let rvτ :=
    (extract τ).map (fun p => a + p.2.val + 1)
  have hperm : rvK.Perm (rvσ ++ rvτ) := by
    exact extractedRightValues_appendPairingTo_perm
      ha σ τ
  have hmem (k : ℕ) :
      k ∈ rvK ↔ k ∈ rvσ ++ rvτ :=
    hperm.mem_iff
  change
    (∏ e : Fin (N + 1),
      if e.val ∈ rvK then 1
      else greenFn (xt e.castSucc - xt e.succ)) = _
  rw [prod_prefix_suffix
    (N := N + 1) (a := a) (by omega)]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro e _he
    have hprefixMem :
        e.val ∈ rvK ↔ e.val ∈ rvσ := by
      rw [hmem]
      constructor
      · intro h
        rcases List.mem_append.mp h with hpre | hsuf
        · exact hpre
        · dsimp only [rvτ] at hsuf
          obtain ⟨p, hp, heq⟩ :=
            List.mem_map.mp hsuf
          have helt := e.isLt
          omega
      · intro h
        exact List.mem_append_left rvτ h
    change
      (if e.val ∈ rvK then 1
        else greenFn
          (xt (Fin.castLE (by omega) e).castSucc -
            xt (Fin.castLE (by omega) e).succ)) =
        (if e.val ∈ rvσ then 1
        else greenFn
          (prefixWithLeftTuple ha xt e.castSucc -
            prefixWithLeftTuple ha xt e.succ))
    by_cases he : e.val ∈ rvσ
    · rw [if_pos he, if_pos (hprefixMem.mpr he)]
    · rw [if_neg he,
        if_neg (fun h => he (hprefixMem.mp h))]
      apply congrArg greenFn
      apply congrArg₂ (· - ·)
      · apply congrArg xt
        apply Fin.ext
        rfl
      · apply congrArg xt
        apply Fin.ext
        rfl
  · let hsize :
        (N + 1 - a) = (N - a + 1) := by omega
    rw [← Fin.prod_congr'
      (fun e : Fin (N - a + 1) =>
        if e.val ∈
            (extract τ).map
              (fun p => p.2.val + 1)
        then 1
        else greenFn
          (ambientTailTuple ha xt e.castSucc -
            ambientTailTuple ha xt e.succ))
      hsize]
    apply Finset.prod_congr rfl
    intro e _he
    let e' : Fin (N - a + 1) :=
      e.cast hsize
    have heval : e'.val = e.val := rfl
    have hsuffixMem :
        (suffixFin
            (N := N + 1) (a := a)
            (by omega) e).val ∈ rvK ↔
          e'.val ∈
            (extract τ).map
              (fun p => p.2.val + 1) := by
      rw [hmem]
      constructor
      · intro h
        rcases List.mem_append.mp h with hpre | hsuf
        · dsimp only [rvσ] at hpre
          obtain ⟨p, hp, heq⟩ :=
            List.mem_map.mp hpre
          have hlt := hproper p hp
          have heqVal :
              a + e.val = p.2.val + 1 := by
            simpa only [suffixFin_val] using heq.symm
          omega
        · dsimp only [rvτ] at hsuf
          obtain ⟨p, hp, heq⟩ :=
            List.mem_map.mp hsuf
          exact List.mem_map.mpr
            ⟨p, hp, by
              have heqVal :
                  a + p.2.val + 1 = a + e.val := by
                simpa only [suffixFin_val] using heq
              omega⟩
      · intro h
        obtain ⟨p, hp, heq⟩ :=
          List.mem_map.mp h
        apply List.mem_append_right
        dsimp only [rvτ]
        exact List.mem_map.mpr
          ⟨p, hp, by
            simp only [suffixFin_val]
            omega⟩
    by_cases he :
        e'.val ∈
          (extract τ).map
            (fun p => p.2.val + 1)
    · rw [if_pos he,
        if_pos (hsuffixMem.mpr he)]
    · rw [if_neg he,
        if_neg (fun h => he (hsuffixMem.mp h))]
      apply congrArg greenFn
      apply congrArg₂ (· - ·)
      · apply congrArg xt
        apply Fin.ext
        change a + e.val = a + e'.val
        omega
      · apply congrArg xt
        apply Fin.ext
        change a + e.val + 1 = a + e'.val + 1
        omega

/-- Closed-form factorization of an old contraction pairing into its
proper head-deleted prefix and the full tail integrand. -/
theorem detIntegrand_appendPairingTo_properPrefix
    (ρ : SmoothCutoff) (ε : ℝ)
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (xt : Fin (N + 2) → T4)
    (hproper :
      ∀ p ∈ extract σ, p.2.val + 1 < a) :
    detIntegrand ρ ε N
        (appendPairingTo ha σ τ) xt =
      headDeletedPrefixCore ρ ε a σ
          (prefixWithLeftTuple ha xt) *
        detIntegrand ρ ε (N - a) τ
          (ambientTailTuple ha xt) := by
  have hdiff :
      ((extract σ).map
          (fun p =>
            diffFactor xt (eaPrefixPair ha p))).prod =
        ((extract σ).map
          (fun p =>
            diffFactorJ
              (prefixWithLeftTuple ha xt)
              (hdSuccPair p))).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    exact diffFactor_prefix_eq_headDeletedJ
      ha xt p (hproper p hp)
  have hcov :
      (∏ i ∈ σ.pairSupport.filter
          (fun i => i < σ i),
        ρ.etaEpsT4 ε
          (ambientPrefixTuple ha xt i -
            ambientPrefixTuple ha xt (σ i))) =
        ∏ i ∈ σ.pairSupport.filter
          (fun i => i < σ i),
        ρ.etaEpsT4 ε
          (prefixWithLeftTuple ha xt i.succ -
            prefixWithLeftTuple ha xt (σ i).succ) := by
    apply Finset.prod_congr rfl
    intro i _hi
    apply congrArg (ρ.etaEpsT4 ε)
    apply congrArg₂ (· - ·)
    · apply congrArg xt
      apply Fin.ext
      rfl
    · apply congrArg xt
      apply Fin.ext
      rfl
  unfold detIntegrand headDeletedPrefixCore
  rw [chainProduct_appendPairingTo_properPrefix
    ha σ τ xt hproper]
  rw [differenceProduct_appendPairingTo
    ha σ τ xt]
  rw [covarianceProduct_appendPairingTo
    ρ ε ha σ τ xt]
  rw [hdiff, hcov]
  ring

/-- Restoring the head--partner covariance turns the proper
head-deleted prefix ledger into the paper's full non-split `J`
integrand. -/
theorem headDeletedPrefixCore_mul_eta_eq_detJintegrand
    (ρ : SmoothCutoff) (ε : ℝ)
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (hσ : IsNonSplit σ)
    (xt : Fin (2 * (q + 1)) → T4) :
    headDeletedPrefixCore ρ ε (2 * q + 1)
        (caseThreePrefixHeadDeletionData q σ hσ).pairing
        xt *
      ρ.etaEpsT4 ε
        (xt 0 -
          xt
            (caseThreePrefixHeadDeletionData
              q σ hσ).index.succ) =
      detJintegrand ρ ε (q + 1) σ xt := by
  let d := caseThreePrefixHeadDeletionData q σ hσ
  change
    headDeletedPrefixCore ρ ε (2 * q + 1)
        d.pairing xt *
      ρ.etaEpsT4 ε
        (xt 0 - xt d.index.succ) =
      detJintegrand ρ ε (q + 1) σ xt
  have hpair :
      wickHeadEquiv (2 * q + 1) (Sum.inr d) = σ :=
    contractionHeadEquiv_headDeletionData
      σ (hσ.1 0)
  have hextract :
      extract σ =
        (extract d.pairing).map hdSuccPair ++
          [wholePrefixPair
            (by omega : 0 < 2 * (q + 1))] := by
    exact extract_nonSplit_eq_proper_append_whole
      q σ hσ
  have hmem (e : Fin (2 * q + 1)) :
      e.val ∈
          (extract σ).map (fun p => p.2.val) ↔
        e.val ∈
          (extract d.pairing).map
            (fun p => p.2.val + 1) := by
    rw [hextract]
    simp only [List.map_append, List.mem_append,
      List.map_map,
      List.map_singleton, List.mem_singleton]
    constructor
    · rintro (h | h)
      · obtain ⟨p, hp, heq⟩ :=
          List.mem_map.mp h
        exact List.mem_map.mpr
          ⟨p, hp, by
            change (hdSuccPair p).2.val = e.val at heq
            simpa only [hdSuccPair,
              Fin.val_succ] using heq⟩
      · unfold wholePrefixPair at h
        have helt := e.isLt
        change e.val =
          2 * (q + 1) - 1 at h
        omega
    · intro h
      apply Or.inl
      obtain ⟨p, hp, heq⟩ :=
        List.mem_map.mp h
      exact List.mem_map.mpr
        ⟨p, hp, by
          change (hdSuccPair p).2.val = e.val
          simpa only [hdSuccPair,
            Fin.val_succ] using heq⟩
  have hchain :
      (∏ e : Fin (2 * q + 1),
        if e.val ∈
            (extract σ).map (fun p => p.2.val)
        then 1
        else if h :
            e.val + 1 < 2 * (q + 1)
        then
          greenFn
            (xt ⟨e.val, by omega⟩ -
              xt ⟨e.val + 1, h⟩)
        else 1) =
      ∏ e : Fin (2 * q + 1),
        if e.val ∈
            (extract d.pairing).map
              (fun p => p.2.val + 1)
        then 1
        else greenFn
          (xt e.castSucc - xt e.succ) := by
    apply Finset.prod_congr rfl
    intro e _he
    have heNext :
        e.val + 1 < 2 * (q + 1) := by
      have := e.isLt
      omega
    by_cases he :
        e.val ∈
          (extract d.pairing).map
            (fun p => p.2.val + 1)
    · rw [if_pos he, if_pos ((hmem e).mpr he)]
    · rw [if_neg he,
        if_neg (fun h => he ((hmem e).mp h)),
        dif_pos heNext]
      congr 2
  have hdiff :
      ((extract σ).map (diffFactorJ xt)).prod =
        ((extract d.pairing).map
          (fun p => diffFactorJ xt
            (hdSuccPair p))).prod := by
    rw [hextract]
    simp only [List.map_append, List.prod_append,
      List.map_map,
      List.map_singleton, List.prod_singleton]
    rw [diffFactorJ_wholePrefixPair]
    simp only [mul_one]
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    rfl
  have hchainActual :
      (∏ e : Fin (2 * (q + 1) - 1),
        if e.val ∈
            (extract σ).map (fun p => p.2.val)
        then 1
        else if h :
            e.val + 1 < 2 * (q + 1)
        then
          greenFn
            (xt ⟨e.val, by omega⟩ -
              xt ⟨e.val + 1, h⟩)
        else 1) =
      ∏ e : Fin (2 * q + 1),
        if e.val ∈
            (extract d.pairing).map
              (fun p => p.2.val + 1)
        then 1
        else greenFn
          (xt e.castSucc - xt e.succ) := by
    let hsize :
        2 * (q + 1) - 1 = 2 * q + 1 := by
      omega
    calc
      _ =
          ∏ e : Fin (2 * q + 1),
            if e.val ∈
                (extract σ).map
                  (fun p => p.2.val)
            then 1
            else if h :
                e.val + 1 < 2 * (q + 1)
            then
              greenFn
                (xt ⟨e.val, by omega⟩ -
                  xt ⟨e.val + 1, h⟩)
            else 1 := by
        rw [← Fin.prod_congr'
          (fun e : Fin (2 * q + 1) =>
            if e.val ∈
                (extract σ).map
                  (fun p => p.2.val)
            then 1
            else if h :
                e.val + 1 < 2 * (q + 1)
            then
              greenFn
                (xt ⟨e.val, by omega⟩ -
                  xt ⟨e.val + 1, h⟩)
            else 1)
          hsize]
        apply Finset.prod_congr rfl
        intro e _he
        rfl
      _ = _ := hchain
  have hcov :
      (∏ i ∈ σ.pairSupport.filter
          (fun i => i < σ i),
        ρ.etaEpsT4 ε (xt i - xt (σ i))) =
        ρ.etaEpsT4 ε
            (xt 0 - xt d.index.succ) *
          ∏ i ∈ d.pairing.pairSupport.filter
              (fun i => i < d.pairing i),
            ρ.etaEpsT4 ε
              (xt i.succ -
                xt (d.pairing i).succ) := by
    let xtFull : Fin (2 * (q + 1) + 2) → T4 :=
      assemble 0 0 xt
    have hbase :=
      covarianceProduct_wickHeadEquiv_contraction
        ρ ε d xtFull
    rw [hpair] at hbase
    have hfirst :
        xtFull 1 = xt 0 := by
      change
        assemble 0 0 xt
            (varIdx (0 :
              Fin (2 * (q + 1)))) =
          xt 0
      rw [assemble_varIdx]
    have htail (i : Fin (2 * q + 1)) :
        ambientTailTuple
            (by omega :
              1 ≤ 2 * q + 2) xtFull
            (varIdx i) =
          xt i.succ := by
      rw [ambientTailTuple_varIdx]
      have hsuffix :
          suffixFin
              (N := 2 * q + 2) (a := 1)
              (by omega) i =
            i.succ := by
        apply Fin.ext
        change 1 + i.val = i.val + 1
        omega
      rw [hsuffix]
      change
        xtFull
            (varIdx i.succ) =
          xt i.succ
      change
        assemble 0 0 xt
            (varIdx i.succ) =
          xt i.succ
      rw [assemble_varIdx]
    simp only [xtFull, assemble_varIdx,
      hfirst, htail] at hbase
    exact hbase
  unfold detJintegrand headDeletedPrefixCore
  rw [hchainActual, hdiff, hcov]
  ac_rfl

/-! ## The actual case-(3) contraction tuple -/

/-- Delete the first (new-head) internal coordinate from the ambient
case-(3) tuple.  The result is the old tuple integrated by the Wick
contraction summand. -/
def caseThreeContractionTuple
    (q r : ℕ) (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    Fin (2 * q + 1 + r + 2) → T4 :=
  arithmeticCastTuple
    (by omega :
      (2 * (q + 1) + r) - 1 =
        2 * q + 1 + r)
    (ambientTailTuple
      (N := 2 * (q + 1) + r) (a := 1)
      (by omega)
      (assemble x y
        (caseThreeAmbientInternal
          q r z w t)))

@[simp]
theorem caseThreeContractionTuple_zero
    (q r : ℕ) (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    caseThreeContractionTuple
        q r x z w y t 0 = z := by
  unfold caseThreeContractionTuple
  unfold arithmeticCastTuple ambientTailTuple
  have hslot :
      (⟨1 + (Fin.cast
          (by omega :
            2 * q + 1 + r + 2 =
              (2 * (q + 1) + r - 1) + 2)
          (0 : Fin (2 * q + 1 + r + 2))).val,
        by omega⟩ :
          Fin (2 * (q + 1) + r + 2)) =
        varIdx
          (Fin.castAdd r
            (0 : Fin (2 * (q + 1)))) := by
    apply Fin.ext
    rfl
  rw [hslot, assemble_varIdx,
    caseThreeAmbientInternal_prefix,
    detJTupleSucc_zero]

/-- The closed prefix of the contraction tuple is the tuple used in
`detJintegrand`. -/
theorem prefixWithLeftTuple_caseThreeContraction
    (q r : ℕ) (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    prefixWithLeftTuple
        (N := 2 * q + 1 + r)
        (a := 2 * q + 1) (by omega)
        (caseThreeContractionTuple
          q r x z w y t) =
      detJTupleSucc q z w
        (fun i => t (Fin.castAdd r i)) := by
  funext i
  unfold prefixWithLeftTuple
  unfold caseThreeContractionTuple
  unfold arithmeticCastTuple ambientTailTuple
  have hslot :
      (⟨1 +
          (Fin.cast
            (by omega :
              2 * q + 1 + r + 2 =
                (2 * (q + 1) + r - 1) + 2)
            (Fin.castLE (by omega :
              2 * q + 2 ≤
                2 * q + 1 + r + 2) i)).val,
        by omega⟩ :
          Fin (2 * (q + 1) + r + 2)) =
        varIdx (Fin.castAdd r i) := by
    apply Fin.ext
    change 1 + i.val = i.val + 1
    omega
  rw [hslot, assemble_varIdx,
    caseThreeAmbientInternal_prefix]

/-- The tail beginning at the right endpoint `w` is the usual
case-(3) tail tuple, up to the unavoidable arithmetic cast. -/
theorem ambientTailTuple_caseThreeContraction
    (q r : ℕ) (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    ambientTailTuple
        (N := 2 * q + 1 + r)
        (a := 2 * q + 1) (by omega)
        (caseThreeContractionTuple
          q r x z w y t) =
      arithmeticCastTuple
        (by omega :
          r =
            (2 * q + 1 + r -
              (2 * q + 1)))
        (caseThreeTailTuple q r w y t) := by
  funext i
  let fullxt :
      Fin (2 * (q + 1) + r + 2) → T4 :=
    assemble x y
      (caseThreeAmbientInternal q r z w t)
  let j :
      Fin
        (2 * (q + 1) + r -
          2 * (q + 1) + 2) :=
    Fin.cast (by omega) i
  have hfullTail :=
    congrFun
      (ambientTailTuple_caseThree
        q r x z w y t) j
  calc
    ambientTailTuple
        (N := 2 * q + 1 + r)
        (a := 2 * q + 1) (by omega)
        (caseThreeContractionTuple
          q r x z w y t) i =
      ambientTailTuple
        (N := 2 * (q + 1) + r)
        (a := 2 * (q + 1)) (by omega)
        fullxt j := by
          unfold caseThreeContractionTuple
          unfold arithmeticCastTuple ambientTailTuple
          apply congrArg fullxt
          apply Fin.ext
          dsimp only [j]
          have hleft :
              (Fin.cast
                (by omega :
                  2 * q + 1 + r + 2 =
                    (2 * (q + 1) + r - 1) + 2)
                (⟨2 * q + 1 + i.val, by omega⟩ :
                  Fin (2 * q + 1 + r + 2))).val =
                2 * q + 1 + i.val := rfl
          have hright :
              (Fin.cast
                (by omega :
                  2 * q + 1 + r -
                      (2 * q + 1) + 2 =
                    2 * (q + 1) + r -
                      2 * (q + 1) + 2)
                i).val = i.val := rfl
          rw [hleft, hright]
          omega
    _ =
      arithmeticCastTuple
        (by omega :
          r =
            (2 * q + 1 + r -
              (2 * q + 1)))
        (caseThreeTailTuple q r w y t) i := by
          rw [hfullTail]
          unfold arithmeticCastTuple
          apply congrArg
            (caseThreeTailTuple q r w y t)
          apply Fin.ext
          dsimp only [j]
          rfl

/-- The marked old variable is the same prefix coordinate as the
partner restored in the closed `J` block. -/
theorem caseThreeContractionTuple_marked
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    caseThreeContractionTuple q r x z w y t
        (varIdx
          (caseThreeHeadDeletionData
            q r σ τ hσ).index) =
      detJTupleSucc q z w
          (fun i => t (Fin.castAdd r i))
        (caseThreePrefixHeadDeletionData
          q σ hσ).index.succ := by
  let d := caseThreeHeadDeletionData q r σ τ hσ
  let dσ := caseThreePrefixHeadDeletionData q σ hσ
  have hd :
      d = appendMarkedSingle dσ τ :=
    caseThreeHeadDeletionData_eq_append
      q r σ τ hσ
  have hindex :
      d.index =
        Fin.castAdd r dσ.index := by
    have hv :=
      congrArg
        (fun e : MarkedSingle
          (Fin (2 * q + 1 + r)) => e.index) hd
    exact hv
  have hpref :=
    congrFun
      (prefixWithLeftTuple_caseThreeContraction
        q r x z w y t) dσ.index.succ
  rw [← hpref]
  unfold prefixWithLeftTuple
  apply congrArg
    (caseThreeContractionTuple
      q r x z w y t)
  apply Fin.ext
  rw [hindex]
  rfl

/-- The deterministic part of the actual Wick contraction is exactly
the closed non-split `J` integrand times the deterministic tail
integrand. -/
theorem caseThreeHeadContraction_det_eq
    (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    detIntegrand ρ ε (2 * q + 1 + r)
        (caseThreeHeadDeletionData
          q r σ τ hσ).pairing
        (caseThreeContractionTuple
          q r x z w y t) *
      ρ.etaEpsT4 ε
        (z -
          caseThreeContractionTuple
            q r x z w y t
            (varIdx
              (caseThreeHeadDeletionData
                q r σ τ hσ).index)) =
      detJintegrand ρ ε (q + 1) σ
          (detJTupleSucc q z w
            (fun i => t (Fin.castAdd r i))) *
        detIntegrand ρ ε r τ
          (caseThreeTailTuple q r w y t) := by
  let a := 2 * q + 1
  let N := a + r
  let ha : a ≤ N := by omega
  let d := caseThreeHeadDeletionData q r σ τ hσ
  let dσ := caseThreePrefixHeadDeletionData q σ hσ
  let τ' : PartialPairing (Fin (N - a)) :=
    arithmeticTailPairing (a := a) τ
  have hd :
      d = appendMarkedSingle dσ τ :=
    caseThreeHeadDeletionData_eq_append
      q r σ τ hσ
  have hpair :
      d.pairing =
        appendPairing dσ.pairing τ := by
    exact congrArg MarkedSingle.pairing hd
  have happend :
      appendPairingTo ha dσ.pairing τ' =
        appendPairing dσ.pairing τ := by
    exact appendPairingTo_arithmeticTailPairing
      dσ.pairing τ
  have hproper :
      ∀ p ∈ extract dσ.pairing,
        p.2.val + 1 < a := by
    intro p hp
    exact caseThreePrefixHeadDeletion_extract_proper
      q σ hσ p hp
  have hbase :=
    detIntegrand_appendPairingTo_properPrefix
      ρ ε ha dσ.pairing τ'
      (caseThreeContractionTuple
        q r x z w y t) hproper
  rw [happend] at hbase
  rw [← hpair] at hbase
  have hprefix :
      prefixWithLeftTuple ha
          (caseThreeContractionTuple
            q r x z w y t) =
        detJTupleSucc q z w
          (fun i => t (Fin.castAdd r i)) := by
    exact prefixWithLeftTuple_caseThreeContraction
      q r x z w y t
  have htail :
      ambientTailTuple ha
          (caseThreeContractionTuple
            q r x z w y t) =
        arithmeticCastTuple
          (by omega : r = N - a)
          (caseThreeTailTuple q r w y t) := by
    exact ambientTailTuple_caseThreeContraction
      q r x z w y t
  have hτ :
      τ' =
        arithmeticCastPairing
          (by omega : r = N - a) τ := by
    exact arithmeticTailPairing_eq_cast τ
  have htailDet :
      detIntegrand ρ ε (N - a) τ'
          (ambientTailTuple ha
            (caseThreeContractionTuple
              q r x z w y t)) =
        detIntegrand ρ ε r τ
          (caseThreeTailTuple q r w y t) := by
    rw [htail, hτ]
    exact detIntegrand_arithmeticCast
      ρ ε (by omega : r = N - a) τ
        (caseThreeTailTuple q r w y t)
  have hmarked :
      caseThreeContractionTuple q r x z w y t
          (varIdx d.index) =
        detJTupleSucc q z w
            (fun i => t (Fin.castAdd r i))
          dσ.index.succ := by
    exact caseThreeContractionTuple_marked
      q r σ τ hσ x z w y t
  change
    detIntegrand ρ ε N d.pairing
        (caseThreeContractionTuple
          q r x z w y t) *
      ρ.etaEpsT4 ε
        (z -
          caseThreeContractionTuple
            q r x z w y t
            (varIdx d.index)) = _
  rw [hbase, hprefix, htailDet, hmarked]
  have hJ :=
    headDeletedPrefixCore_mul_eta_eq_detJintegrand
      ρ ε q σ hσ
        (detJTupleSucc q z w
          (fun i => t (Fin.castAdd r i)))
  rw [detJTupleSucc_zero] at hJ
  calc
    (headDeletedPrefixCore ρ ε a dσ.pairing
          (detJTupleSucc q z w
            (fun i => t (Fin.castAdd r i))) *
        detIntegrand ρ ε r τ
          (caseThreeTailTuple q r w y t)) *
        ρ.etaEpsT4 ε
          (z -
            detJTupleSucc q z w
                (fun i => t (Fin.castAdd r i))
              dσ.index.succ) =
      (headDeletedPrefixCore ρ ε a dσ.pairing
          (detJTupleSucc q z w
            (fun i => t (Fin.castAdd r i))) *
        ρ.etaEpsT4 ε
          (z -
            detJTupleSucc q z w
                (fun i => t (Fin.castAdd r i))
              dσ.index.succ)) *
        detIntegrand ρ ε r τ
          (caseThreeTailTuple q r w y t) := by
            ring
    _ = _ := by
      rw [hJ]

/-- On the actual case-(3) tuple, erasing the marked Wick label leaves
literally the ordered tail labels. -/
theorem caseThreeHeadContraction_wickLabels
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    (wickAtSingleLabels
        (caseThreeHeadDeletionData
          q r σ τ hσ).pairing
        (caseThreeContractionTuple
          q r x z w y t)).eraseIdx
        ((caseThreeHeadDeletionData
          q r σ τ hσ).pairing.singles.sort.idxOf
            (caseThreeHeadDeletionData
              q r σ τ hσ).index) =
      wickAtSingleLabels τ
        (caseThreeTailTuple q r w y t) := by
  rw [caseThreeHeadDeletion_wickLabels_erase
    q r σ τ hσ
      (caseThreeContractionTuple
        q r x z w y t)]
  rw [ambientTailTuple_caseThreeContraction
    q r x z w y t]
  apply congrArg (wickAtSingleLabels τ)
  funext i
  unfold arithmeticCastTuple
  apply congrArg
    (caseThreeTailTuple q r w y t)
  apply Fin.ext
  rfl

/-- Pointwise fixed-data case-(3) bridge: the actual Wick contraction
integrand is the paper's joint `J × R` source. -/
theorem caseThreeHeadContractionTerm_eq_jointCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x z w y : T4)
    (t : Fin (2 * q + r) → T4)
    (ω : M.Ω) :
    detIntegrand ρ ε (2 * q + 1 + r)
        (caseThreeHeadDeletionData
          q r σ τ hσ).pairing
        (caseThreeContractionTuple
          q r x z w y t) *
      (ρ.etaEpsT4 ε
          (z -
            caseThreeContractionTuple
              q r x z w y t
              (varIdx
                (caseThreeHeadDeletionData
                  q r σ τ hσ).index)) *
        wickPolynomial
          (fun a b : T4 =>
            ρ.etaEpsT4 ε (a - b))
          (fun a ω' =>
            M.xiEps ρ ε ω' a)
          ((wickAtSingleLabels
            (caseThreeHeadDeletionData
              q r σ τ hσ).pairing
            (caseThreeContractionTuple
              q r x z w y t)).eraseIdx
                ((caseThreeHeadDeletionData
                  q r σ τ hσ).pairing.singles.sort.idxOf
                    (caseThreeHeadDeletionData
                      q r σ τ hσ).index)) ω) =
      caseThreeJointCore
        M ρ ε q r σ τ z w y ω t := by
  rw [caseThreeHeadContraction_wickLabels
    q r σ τ hσ x z w y t]
  rw [← wickAt_eq_wickPolynomial]
  rw [← mul_assoc]
  rw [caseThreeHeadContraction_det_eq
    ρ ε q r σ τ hσ x z w y t]
  unfold caseThreeJointCore randIntegrand
  unfold caseThreeTailTuple
  ac_rfl

/-! ## Fubini for the old contraction variables -/

/-- Paper order `(u,w,v)` for the old variables after the new head has
been deleted. -/
def caseThreeContractionInternal
    (q r : ℕ) (w : T4)
    (t : Fin (2 * q + r) → T4) :
    Fin (2 * q + 1 + r) → T4 :=
  fun j =>
    Fin.insertNth (α := fun _ => T4)
      (⟨2 * q, by omega⟩ :
        Fin ((2 * q + r) + 1))
      w t
      (Fin.cast (by omega) j)

@[simp]
theorem caseThreeContractionInternal_prefix
    (q r : ℕ) (w : T4)
    (t : Fin (2 * q + r) → T4)
    (i : Fin (2 * q)) :
    caseThreeContractionInternal q r w t
        (⟨i.val, by omega⟩ :
          Fin (2 * q + 1 + r)) =
      t (Fin.castAdd r i) := by
  unfold caseThreeContractionInternal
  let k :
      Fin ((2 * q + r) + 1) :=
    ⟨2 * q, by omega⟩
  let u : Fin (2 * q + r) :=
    Fin.castAdd r i
  have hrep :
      k.succAbove u =
        Fin.cast (by omega)
          (⟨i.val, by omega⟩ :
            Fin (2 * q + 1 + r)) := by
    rw [Fin.succAbove_of_castSucc_lt]
    · apply Fin.ext
      rfl
    · exact Fin.mk_lt_mk.mpr i.isLt
  rw [← hrep, Fin.insertNth_apply_succAbove]

@[simp]
theorem caseThreeContractionInternal_middle
    (q r : ℕ) (w : T4)
    (t : Fin (2 * q + r) → T4) :
    caseThreeContractionInternal q r w t
        (⟨2 * q, by omega⟩ :
          Fin (2 * q + 1 + r)) =
      w := by
  unfold caseThreeContractionInternal
  have heq :
      Fin.cast (by omega)
          (⟨2 * q, by omega⟩ :
            Fin (2 * q + 1 + r)) =
        (⟨2 * q, by omega⟩ :
          Fin ((2 * q + r) + 1)) := by
    apply Fin.ext
    rfl
  rw [heq, Fin.insertNth_apply_same]

@[simp]
theorem caseThreeContractionInternal_suffix
    (q r : ℕ) (w : T4)
    (t : Fin (2 * q + r) → T4)
    (j : Fin r) :
    caseThreeContractionInternal q r w t
        (Fin.natAdd (2 * q + 1) j) =
      t (Fin.natAdd (2 * q) j) := by
  unfold caseThreeContractionInternal
  let k :
      Fin ((2 * q + r) + 1) :=
    ⟨2 * q, by omega⟩
  let u : Fin (2 * q + r) :=
    Fin.natAdd (2 * q) j
  have hrep :
      k.succAbove u =
        Fin.cast (by omega)
          (Fin.natAdd (2 * q + 1) j) := by
    rw [Fin.succAbove_of_le_castSucc]
    · apply Fin.ext
      change u.val + 1 =
        (Fin.cast (by omega)
          (Fin.natAdd (2 * q + 1) j)).val
      dsimp only [u]
      change
        2 * q + j.val + 1 =
          2 * q + 1 + j.val
      omega
    · exact Fin.mk_le_mk.mpr (by
        change 2 * q ≤
          (Fin.natAdd (2 * q) j).val
        change 2 * q ≤ 2 * q + j.val
        omega)
  rw [← hrep, Fin.insertNth_apply_succAbove]

private def caseThreeContractionIndexCast
    (q r : ℕ) :
    Fin ((2 * q + r) + 1) ≃
      Fin (2 * q + 1 + r) :=
  Equiv.cast (congrArg Fin (by omega))

private theorem finCastEquiv_symm_val
    {m n : ℕ} (h : m = n) (j : Fin n) :
    ((Equiv.cast (congrArg Fin h)).symm j).val =
      j.val := by
  subst n
  rfl

private def caseThreeContractionFullCastEquiv
    (q r : ℕ) :
    (Fin (2 * q + 1 + r) → T4) ≃ᵐ
      (Fin ((2 * q + r) + 1) → T4) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : Fin (2 * q + 1 + r) => T4)
    (caseThreeContractionIndexCast q r)).symm

/-- Measurable coordinate separation `(u,w,v) ↔ (w,(u,v))`. -/
def caseThreeContractionVariablesEquiv
    (q r : ℕ) :
    (Fin (2 * q + 1 + r) → T4) ≃ᵐ
      T4 × (Fin (2 * q + r) → T4) :=
  (caseThreeContractionFullCastEquiv q r).trans <|
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin ((2 * q + r) + 1) => T4)
      (⟨2 * q, by omega⟩ :
        Fin ((2 * q + r) + 1))

@[simp]
theorem caseThreeContractionVariablesEquiv_symm_apply
    (q r : ℕ) (w : T4)
    (t : Fin (2 * q + r) → T4) :
    (caseThreeContractionVariablesEquiv q r).symm
        (w, t) =
      caseThreeContractionInternal q r w t := by
  funext j
  simp only [caseThreeContractionVariablesEquiv,
    MeasurableEquiv.trans_symm,
    MeasurableEquiv.trans_apply,
    MeasurableEquiv.piFinSuccAbove_symm_apply,
    caseThreeContractionFullCastEquiv,
    MeasurableEquiv.symm_symm]
  rw [MeasurableEquiv.coe_piCongrLeft]
  simp only [Equiv.piCongrLeft_apply_eq_cast]
  unfold caseThreeContractionInternal
  apply congrArg
    (Fin.insertNth (α := fun _ => T4)
      (⟨2 * q, by omega⟩ :
        Fin ((2 * q + r) + 1)) w t)
  apply Fin.ext
  change
    ((caseThreeContractionIndexCast
      q r).symm j).val =
      (Fin.cast (by omega) j).val
  unfold caseThreeContractionIndexCast
  rw [finCastEquiv_symm_val
    (by omega :
      (2 * q + r) + 1 =
        2 * q + 1 + r)]
  rfl

theorem measurePreserving_caseThreeContractionVariablesEquiv
    (q r : ℕ) :
    MeasurePreserving
      (caseThreeContractionVariablesEquiv q r)
      (Measure.pi fun _ :
        Fin (2 * q + 1 + r) => paperMeasure)
      (paperMeasure.prod
        (Measure.pi fun _ :
          Fin (2 * q + r) => paperMeasure)) := by
  let μold :=
    Measure.pi fun _ :
      Fin (2 * q + 1 + r) => paperMeasure
  let μcast :=
    Measure.pi fun _ :
      Fin ((2 * q + r) + 1) => paperMeasure
  let μt :=
    Measure.pi fun _ :
      Fin (2 * q + r) => paperMeasure
  have hcastForward :
      MeasurePreserving
        (MeasurableEquiv.piCongrLeft
          (fun _ :
            Fin (2 * q + 1 + r) => T4)
          (caseThreeContractionIndexCast q r))
        μcast μold := by
    simpa only [μcast, μold] using
      (measurePreserving_piCongrLeft
        (fun _ :
          Fin (2 * q + 1 + r) =>
            paperMeasure)
        (caseThreeContractionIndexCast q r))
  have hcast :
      MeasurePreserving
        (caseThreeContractionFullCastEquiv q r)
        μold μcast := by
    simpa only [caseThreeContractionFullCastEquiv]
      using hcastForward.symm
  have hinsert :
      MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove
          (fun _ :
            Fin ((2 * q + r) + 1) => T4)
          (⟨2 * q, by omega⟩ :
            Fin ((2 * q + r) + 1)))
        μcast (paperMeasure.prod μt) := by
    simpa only [μcast, μt] using
      (measurePreserving_piFinSuccAbove
        (fun _ :
          Fin ((2 * q + r) + 1) =>
            paperMeasure)
        (⟨2 * q, by omega⟩ :
          Fin ((2 * q + r) + 1)))
  exact hinsert.comp hcast

/-- Fubini after separating the right endpoint `w` of the closed
prefix from the remaining old variables. -/
theorem integral_caseThreeContractionVariables
    (q r : ℕ)
    (f :
      (Fin (2 * q + 1 + r) → T4) → ℝ)
    (hf :
      Integrable f
        (Measure.pi fun _ :
          Fin (2 * q + 1 + r) =>
            paperMeasure)) :
    (∫ v : Fin (2 * q + 1 + r) → T4,
        f v
        ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ w : T4,
        ∫ t : Fin (2 * q + r) → T4,
          f (caseThreeContractionInternal
            q r w t)
          ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure := by
  let e := caseThreeContractionVariablesEquiv q r
  let μold :=
    Measure.pi fun _ :
      Fin (2 * q + 1 + r) => paperMeasure
  let μt :=
    Measure.pi fun _ :
      Fin (2 * q + r) => paperMeasure
  let μtarget := paperMeasure.prod μt
  have hp :
      MeasurePreserving e μold μtarget := by
    simpa only [e, μold, μtarget, μt] using
      measurePreserving_caseThreeContractionVariablesEquiv
        q r
  have hf' :
      Integrable
        (fun p => f (e.symm p)) μtarget := by
    have hiff :=
      hp.integrable_comp_emb
        e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    have hcomp :
        Integrable
          (((fun p => f (e.symm p)) ∘ e))
          μold := by
      convert hf using 1
      funext v
      simp only [Function.comp_apply,
        e.symm_apply_apply]
    exact hcomp
  calc
    (∫ v, f v ∂μold) =
        ∫ p, f (e.symm p) ∂μtarget := by
      simpa only [Function.comp_apply,
        e.symm_apply_apply] using
        hp.integral_comp'
          (fun p => f (e.symm p))
    _ =
        ∫ w : T4,
          ∫ t : Fin (2 * q + r) → T4,
            f (e.symm (w, t))
            ∂μt ∂paperMeasure :=
      integral_prod _ hf'
    _ = _ := by
      simp_rw [e,
        caseThreeContractionVariablesEquiv_symm_apply]
      rfl

@[simp]
theorem caseThreeContractionTuple_last
    (q r : ℕ) (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    caseThreeContractionTuple
        q r x z w y t
        (Fin.last (2 * q + 1 + r + 1)) =
      y := by
  unfold caseThreeContractionTuple
  unfold arithmeticCastTuple ambientTailTuple
  have hslot :
      (⟨1 +
          (Fin.cast
            (by omega :
              2 * q + 1 + r + 2 =
                (2 * (q + 1) + r - 1) + 2)
            (Fin.last
              (2 * q + 1 + r + 1))).val,
        by omega⟩ :
          Fin (2 * (q + 1) + r + 2)) =
        Fin.last (2 * (q + 1) + r + 1) := by
    apply Fin.ext
    simp only [Fin.val_last]
    have hcast :
        (Fin.cast
          (by omega :
            2 * q + 1 + r + 2 =
              (2 * (q + 1) + r - 1) + 2)
          (Fin.last
            (2 * q + 1 + r + 1))).val =
          2 * q + 1 + r + 1 := rfl
    rw [hcast]
    omega
  rw [hslot, assemble_last]

/-- Internal slots of the reindexed old tuple agree with the explicit
`Fin.insertNth` reconstruction used by Fubini. -/
theorem caseThreeContractionTuple_varIdx
    (q r : ℕ) (x z w y : T4)
    (t : Fin (2 * q + r) → T4)
    (i : Fin (2 * q + 1 + r)) :
    caseThreeContractionTuple
        q r x z w y t (varIdx i) =
      caseThreeContractionInternal q r w t i := by
  by_cases hpre : i.val < 2 * q
  · let u : Fin (2 * q) :=
      ⟨i.val, hpre⟩
    have hi :
        i =
          (⟨u.val, by omega⟩ :
            Fin (2 * q + 1 + r)) := by
      apply Fin.ext
      rfl
    rw [hi]
    rw [caseThreeContractionInternal_prefix]
    have hp :=
      congrFun
        (prefixWithLeftTuple_caseThreeContraction
          q r x z w y t) (varIdx u)
    calc
      caseThreeContractionTuple q r x z w y t
          (varIdx
            (⟨u.val, by omega⟩ :
              Fin (2 * q + 1 + r))) =
        prefixWithLeftTuple
            (N := 2 * q + 1 + r)
            (a := 2 * q + 1) (by omega)
            (caseThreeContractionTuple
              q r x z w y t)
            (varIdx u) := by
              unfold prefixWithLeftTuple
              apply congrArg
                (caseThreeContractionTuple
                  q r x z w y t)
              apply Fin.ext
              rfl
      _ =
        detJTupleSucc q z w
          (fun k => t (Fin.castAdd r k))
          (varIdx u) := hp
      _ = t (Fin.castAdd r u) := by
        unfold detJTupleSucc
        rw [show
            Fin.cast (by omega :
              2 * (q + 1) = 2 * q + 2)
              (varIdx u) =
            varIdx u by
          apply Fin.ext
          rfl]
        rw [assemble_varIdx]
  · by_cases hmid : i.val = 2 * q
    · have hi :
          i =
            (⟨2 * q, by omega⟩ :
              Fin (2 * q + 1 + r)) := by
        apply Fin.ext
        exact hmid
      rw [hi]
      rw [caseThreeContractionInternal_middle]
      have hp :=
        congrFun
          (prefixWithLeftTuple_caseThreeContraction
            q r x z w y t)
          (Fin.last (2 * q + 1))
      calc
        caseThreeContractionTuple q r x z w y t
            (varIdx
              (⟨2 * q, by omega⟩ :
                Fin (2 * q + 1 + r))) =
          prefixWithLeftTuple
              (N := 2 * q + 1 + r)
              (a := 2 * q + 1) (by omega)
              (caseThreeContractionTuple
                q r x z w y t)
              (Fin.last (2 * q + 1)) := by
                unfold prefixWithLeftTuple
                apply congrArg
                  (caseThreeContractionTuple
                    q r x z w y t)
                apply Fin.ext
                change
                  2 * q + 1 =
                    (Fin.castLE (by omega)
                      (Fin.last
                        (2 * q + 1))).val
                rfl
        _ =
          detJTupleSucc q z w
            (fun k => t (Fin.castAdd r k))
            (Fin.last (2 * q + 1)) := hp
        _ = w := by
          unfold detJTupleSucc
          rw [show
              Fin.cast (by omega :
                2 * (q + 1) = 2 * q + 2)
                (Fin.last (2 * q + 1)) =
              Fin.last (2 * q + 1) by
            apply Fin.ext
            rfl]
          rw [assemble_last]
    · have hgt : 2 * q < i.val := by omega
      let j : Fin r :=
        ⟨i.val - (2 * q + 1), by
          have := i.isLt
          omega⟩
      have hi :
          i =
            Fin.natAdd (2 * q + 1) j := by
        apply Fin.ext
        change i.val =
          2 * q + 1 + j.val
        dsimp only [j]
        omega
      rw [hi]
      rw [caseThreeContractionInternal_suffix]
      let j' :
          Fin
            (2 * q + 1 + r -
              (2 * q + 1)) :=
        Fin.cast (by omega) j
      have ht :=
        congrFun
          (ambientTailTuple_caseThreeContraction
            q r x z w y t) (varIdx j')
      calc
        caseThreeContractionTuple q r x z w y t
            (varIdx
              (Fin.natAdd (2 * q + 1) j)) =
          ambientTailTuple
              (N := 2 * q + 1 + r)
              (a := 2 * q + 1) (by omega)
              (caseThreeContractionTuple
                q r x z w y t)
              (varIdx j') := by
                rw [ambientTailTuple_varIdx]
                apply congrArg
                  (caseThreeContractionTuple
                    q r x z w y t)
                apply Fin.ext
                rfl
        _ =
          arithmeticCastTuple
              (by omega :
                r =
                  2 * q + 1 + r -
                    (2 * q + 1))
              (caseThreeTailTuple q r w y t)
              (varIdx j') := ht
        _ = t (Fin.natAdd (2 * q) j) := by
          unfold arithmeticCastTuple
          unfold caseThreeTailTuple
          rw [show
              Fin.cast (by omega)
                  (varIdx j') =
                varIdx j by
            apply Fin.ext
            dsimp only [j']
            rfl]
          rw [assemble_varIdx]

/-- The tuple reconstructed by the contraction Fubini equivalence is
the tuple used by the pointwise contraction bridge. -/
theorem assemble_caseThreeContractionInternal
    (q r : ℕ) (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    assemble z y
        (caseThreeContractionInternal q r w t) =
      caseThreeContractionTuple
        q r x z w y t := by
  funext i
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    rw [assemble_zero,
      caseThreeContractionTuple_zero]
  · by_cases hilast :
      i.val = 2 * q + 1 + r + 1
    · have hi :
          i =
            Fin.last (2 * q + 1 + r + 1) := by
        apply Fin.ext
        simpa only [Fin.val_last] using hilast
      rw [hi]
      rw [assemble_last,
        caseThreeContractionTuple_last]
    · let j : Fin (2 * q + 1 + r) :=
        ⟨i.val - 1, by
          have := i.isLt
          omega⟩
      have hi :
          i = varIdx j := by
        apply Fin.ext
        dsimp only [j]
        simp only [varIdx_val]
        omega
      rw [hi]
      rw [assemble_varIdx,
        caseThreeContractionTuple_varIdx]

/-! ## The integrated fixed-data case-(3) bridge -/

/-- The actual marked-single contraction integrand, including the free
left Green edge, before the old variables are separated into
`(w,t)`. -/
def caseThreeHeadContractionWeightedCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x z y : T4)
    (v : Fin (2 * q + 1 + r) → T4)
    (ω : M.Ω) : ℝ :=
  greenFn (x - z) *
    (detIntegrand ρ ε (2 * q + 1 + r)
        (caseThreeHeadDeletionData q r σ τ hσ).pairing
        (assemble z y v) *
      (ρ.etaEpsT4 ε
          (z -
            assemble z y v
              (varIdx
                (caseThreeHeadDeletionData
                  q r σ τ hσ).index)) *
        wickPolynomial
          (fun a b : T4 =>
            ρ.etaEpsT4 ε (a - b))
          (fun a ω' =>
            M.xiEps ρ ε ω' a)
          ((wickAtSingleLabels
              (caseThreeHeadDeletionData
                q r σ τ hσ).pairing
              (assemble z y v)).eraseIdx
            ((caseThreeHeadDeletionData
                q r σ τ hσ).pairing.singles.sort.idxOf
              (caseThreeHeadDeletionData
                q r σ τ hσ).index)) ω))

/-- Separating the closed-prefix endpoint turns the actual contraction
integrand pointwise into the case-(3) joint core. -/
theorem caseThreeHeadContractionWeightedCore_reindex
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x z w y : T4)
    (t : Fin (2 * q + r) → T4)
    (ω : M.Ω) :
    caseThreeHeadContractionWeightedCore
        M ρ ε q r σ τ hσ x z y
        (caseThreeContractionInternal q r w t) ω =
      greenFn (x - z) *
        caseThreeJointCore
          M ρ ε q r σ τ z w y ω t := by
  unfold caseThreeHeadContractionWeightedCore
  rw [assemble_caseThreeContractionInternal
    q r x z w y t]
  rw [caseThreeHeadContractionTerm_eq_jointCore
    M ρ ε q r σ τ hσ x z w y t ω]

/-- **Actual fixed-data case-(3) contraction bridge.**  The
marked-single multiple integral obtained by deleting the paired head
of `appendPairing σ τ` is exactly the existing joint case-(3)
contribution.  The sole analytic assumption is integrability of the
old-variable contraction integrand, which licenses the displayed
Fubini reindexing. -/
theorem headPairedContractionContribution_caseThree_eq_joint
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x y : T4) (ω : M.Ω)
    (hint :
      ∀ᵐ z ∂paperMeasure,
        Integrable
          (fun v : Fin (2 * q + 1 + r) → T4 =>
            caseThreeHeadContractionWeightedCore
              M ρ ε q r σ τ hσ x z y v ω)
          (Measure.pi fun _ => paperMeasure)) :
    headPairedContractionContribution
        M ρ lam ε (2 * q + 1 + r)
        (caseThreeHeadDeletionData q r σ τ hσ)
        x y ω =
      caseThreeJointContribution
        M ρ lam ε q r σ τ x y ω := by
  have hinner :
      ∀ᵐ z ∂paperMeasure,
      (∫ v : Fin (2 * q + 1 + r) → T4,
          caseThreeHeadContractionWeightedCore
            M ρ ε q r σ τ hσ x z y v ω
          ∂(Measure.pi fun _ => paperMeasure)) =
        ∫ w : T4,
          greenFn (x - z) *
            ∫ t : Fin (2 * q + r) → T4,
              caseThreeJointCore
                M ρ ε q r σ τ z w y ω t
              ∂(Measure.pi fun _ => paperMeasure)
          ∂paperMeasure := by
    filter_upwards [hint] with z hz
    calc
      _ =
          ∫ w : T4,
            ∫ t : Fin (2 * q + r) → T4,
              caseThreeHeadContractionWeightedCore
                M ρ ε q r σ τ hσ x z y
                (caseThreeContractionInternal q r w t) ω
              ∂(Measure.pi fun _ => paperMeasure)
            ∂paperMeasure :=
        integral_caseThreeContractionVariables
          q r
          (fun v =>
            caseThreeHeadContractionWeightedCore
              M ρ ε q r σ τ hσ x z y v ω)
          hz
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with w
        calc
          (∫ t : Fin (2 * q + r) → T4,
              caseThreeHeadContractionWeightedCore
                M ρ ε q r σ τ hσ x z y
                (caseThreeContractionInternal q r w t) ω
              ∂(Measure.pi fun _ => paperMeasure)) =
              ∫ t : Fin (2 * q + r) → T4,
                greenFn (x - z) *
                  caseThreeJointCore
                    M ρ ε q r σ τ z w y ω t
                ∂(Measure.pi fun _ => paperMeasure) := by
            apply integral_congr_ae
            filter_upwards with t
            exact
              caseThreeHeadContractionWeightedCore_reindex
                M ρ ε q r σ τ hσ x z w y t ω
          _ = _ := by
            rw [integral_const_mul]
  unfold headPairedContractionContribution
  unfold caseThreeJointContribution
  change
    lamEps lam ε ^ ((2 * q + 1 + r) + 1) *
        (∫ z : T4,
          ∫ v : Fin (2 * q + 1 + r) → T4,
            caseThreeHeadContractionWeightedCore
              M ρ ε q r σ τ hσ x z y v ω
            ∂(Measure.pi fun _ => paperMeasure)
          ∂paperMeasure) =
      lamEps lam ε ^ (2 * (q + 1) + r) *
        ∫ z : T4,
          ∫ w : T4,
            greenFn (x - z) *
              ∫ t : Fin (2 * q + r) → T4,
                caseThreeJointCore
                  M ρ ε q r σ τ z w y ω t
                ∂(Measure.pi fun _ => paperMeasure)
            ∂paperMeasure
          ∂paperMeasure
  have hpow :
      (2 * q + 1 + r) + 1 =
        2 * (q + 1) + r := by
    omega
  rw [hpow]
  apply congrArg
    (lamEps lam ε ^ (2 * (q + 1) + r) * ·)
  apply integral_congr_ae
  filter_upwards [hinner] with z hz
  exact hz

/-- Paper (3.18) form of the actual fixed-data contraction bridge. -/
theorem headPairedContractionContribution_caseThree_eq_factorized
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x y : T4) (ω : M.Ω)
    (hint :
      ∀ᵐ z ∂paperMeasure,
        Integrable
          (fun v : Fin (2 * q + 1 + r) → T4 =>
            caseThreeHeadContractionWeightedCore
              M ρ ε q r σ τ hσ x z y v ω)
          (Measure.pi fun _ => paperMeasure)) :
    headPairedContractionContribution
        M ρ lam ε (2 * q + 1 + r)
        (caseThreeHeadDeletionData q r σ τ hσ)
        x y ω =
      caseThreeFactorizedContribution
        M ρ lam ε q r σ τ x y ω := by
  rw [
    headPairedContractionContribution_caseThree_eq_joint
      M ρ lam ε q r σ τ hσ x y ω hint,
    caseThreeJointContribution_eq_factorized
      M ρ lam ε q r σ τ x y ω]

/-- Integrability ledger for replacing every actual case-(3)
marked-single contraction in a fixed prefix/tail block by its
factorized paper expression.  The inner statement is almost-everywhere
in the outer variable, exactly as required by the subsequent Bochner
integral; endpoint diagonals need not be pointwise integrable in four
dimensions. -/
def CaseThreeHeadContractionIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω) : Prop :=
  ∀ (σ :
      {σ : PartialPairing (Fin (2 * (q + 1))) //
        IsNonSplit σ})
    (τ : PartialPairing (Fin r)),
    ∀ᵐ z ∂paperMeasure,
      Integrable
        (fun v : Fin (2 * q + 1 + r) → T4 =>
          caseThreeHeadContractionWeightedCore
            M ρ ε q r σ.1 τ σ.2 x z y v ω)
        (Measure.pi fun _ => paperMeasure)

/-- The finite non-split-prefix/tail sum of the *actual*
marked-single contraction sources is the ambient appended-pairing sum
plus the collapsed counterterm block.  This is the summation-facing
form of the case-(3) contraction bridge. -/
theorem
    sum_headPairedCaseThreeContribution_eq_randRI_add_counterterm
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω)
    (hhead :
      CaseThreeHeadContractionIntegrability
        M ρ ε q r x y ω)
    (hsum :
      CaseThreeSummationIntegrability
        M ρ lam ε q r x y ω) :
    (∑ σ :
        {σ : PartialPairing (Fin (2 * (q + 1))) //
          IsNonSplit σ},
      ∑ τ : PartialPairing (Fin r),
        headPairedContractionContribution
          M ρ lam ε (2 * q + 1 + r)
          (caseThreeHeadDeletionData
            q r σ.1 τ σ.2)
          x y ω) =
      (∑ σ ∈ Finset.univ.filter
            (fun σ :
              PartialPairing (Fin (2 * (q + 1))) =>
              IsNonSplit σ),
          ∑ τ : PartialPairing (Fin r),
            randRI M ρ lam ε (2 * (q + 1) + r)
              (appendPairing σ τ) x y ω) +
        caseThreeCountertermBlock
          M ρ lam ε (q + 1) r x y ω := by
  classical
  calc
    _ =
        ∑ σ :
            {σ : PartialPairing (Fin (2 * (q + 1))) //
              IsNonSplit σ},
          ∑ τ : PartialPairing (Fin r),
            caseThreeFactorizedContribution
              M ρ lam ε q r σ.1 τ x y ω := by
      apply Fintype.sum_congr
      intro σ
      apply Fintype.sum_congr
      intro τ
      exact
        headPairedContractionContribution_caseThree_eq_factorized
          M ρ lam ε q r σ.1 τ σ.2 x y ω
          (hhead σ τ)
    _ =
        ∑ σ ∈ Finset.univ.filter
            (fun σ :
              PartialPairing (Fin (2 * (q + 1))) =>
              IsNonSplit σ),
          ∑ τ : PartialPairing (Fin r),
            caseThreeFactorizedContribution
              M ρ lam ε q r σ τ x y ω := by
      symm
      apply Finset.sum_subtype
      intro σ
      simp only [Finset.mem_filter,
        Finset.mem_univ, true_and]
    _ = _ :=
      sum_caseThreeFactorizedContribution_eq_randRI_add_counterterm
        M ρ lam ε q r x y ω hsum

end PartialPairing

end

end Anderson4D
