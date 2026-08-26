import Anderson4D.Parametrix.IdentityHeadPaired

/-!
# The no-prefix paired-head extraction

This module proves the combinatorial fact specific to case (2) of
Proposition 3.4: deleting a paired head from a pairing with no fully
paired head prefix simply shifts the extraction list.  The proof tracks
the already removed tail intervals so that a later relative interval
starting at the head would reconstruct a forbidden original prefix.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace PartialPairing

/-- Ambient tail indices which have already been removed from the active
state.  The head itself is always active. -/
def hdRemoved {n : ℕ}
    (active : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  Finset.univ \ hdGlobalActive active

@[simp]
theorem not_mem_hdRemoved_zero
    {n : ℕ} (active : Finset (Fin n)) :
    (0 : Fin (n + 1)) ∉ hdRemoved active := by
  simp [hdRemoved]

@[simp]
theorem mem_hdRemoved_succ
    {n : ℕ} {active : Finset (Fin n)} {i : Fin n} :
    i.succ ∈ hdRemoved active ↔ i ∉ active := by
  simp [hdRemoved]

@[simp]
theorem hdRemoved_univ {n : ℕ} :
    hdRemoved (Finset.univ : Finset (Fin n)) = ∅ := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Removing a successor interval adds exactly that interval to the
ambient removed set. -/
theorem hdRemoved_sdiff_relIcc
    {n : ℕ} (active : Finset (Fin n))
    (l r : Fin n) :
    hdRemoved (active \ relIcc active l r) =
      hdRemoved active ∪
        relIcc (hdGlobalActive active) l.succ r.succ := by
  rw [hdRemoved, ← hdGlobalActive_sdiff_succ]
  unfold hdRemoved
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union]
  tauto

/-- A fully paired removed set stays fully paired after one proper tail
candidate is extracted. -/
theorem hdRemoved_fullyPaired_sdiff
    {n : ℕ} {κ : PartialPairing (Fin (n + 1))}
    {active : Finset (Fin n)} {l r : Fin n}
    (hremoved : IsFullyPairedOn κ (hdRemoved active))
    (hcand :
      IsRelFullyPaired κ
        (hdGlobalActive active) l.succ r.succ) :
    IsFullyPairedOn κ
      (hdRemoved (active \ relIcc active l r)) := by
  rw [hdRemoved_sdiff_relIcc]
  exact hremoved.union hcand.isFullyPairedOn

/-- A fully paired tail candidate cannot remove the marked single
created by deleting the head pair. -/
theorem hdMarkedIndex_mem_sdiff
    {n : ℕ} (d : MarkedSingle (Fin n))
    {active : Finset (Fin n)} {l r : Fin n}
    (hmark : d.index ∈ active)
    (hcand :
      IsRelFullyPaired d.pairing active l r) :
    d.index ∈ active \ relIcc active l r := by
  rw [Finset.mem_sdiff]
  refine ⟨hmark, ?_⟩
  intro hidx
  exact hcand.isFullyPairedOn.ne_of_mem hidx
    (mem_singles.mp d.isSingle)

/-- At an active tail boundary, the part of the removed set lying to its
left is itself fully paired.  Order separation rules out a removed pair
straddling that boundary. -/
theorem hdRemoved_prefix_fullyPaired
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0)
    (active : Finset (Fin n))
    (hremoved : IsFullyPairedOn κ (hdRemoved active))
    (hsep : HdSeparated (headDeletionData κ hκ) active)
    (hmark : (headDeletionData κ hκ).index ∈ active)
    (r : Fin n) (hr : r ∈ active) :
    IsFullyPairedOn κ
      (hdRemoved active ∩
        Finset.univ.filter
          (fun i : Fin (n + 1) => i.val ≤ r.succ.val)) := by
  let d := headDeletionData κ hκ
  constructor
  · intro i hi
    exact hremoved.ne_of_mem (Finset.mem_inter.mp hi).1
  · intro i hi
    have hirem : i ∈ hdRemoved active :=
      (Finset.mem_inter.mp hi).1
    have hibound : i.val ≤ r.succ.val := by
      simpa only [Finset.mem_filter, Finset.mem_univ,
        true_and] using (Finset.mem_inter.mp hi).2
    have hkrem : κ i ∈ hdRemoved active :=
      hremoved.apply_mem hirem
    refine Finset.mem_inter.mpr ⟨hkrem, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine Fin.cases (motive := fun i =>
      i ∈ hdRemoved active →
      i.val ≤ r.succ.val →
      (κ i).val ≤ r.succ.val) ?_ (fun j => ?_) i
      hirem hibound
    · intro hzero
      exact False.elim
        (not_mem_hdRemoved_zero active hzero)
    · intro hjrem hjbound
      have hjnot : j ∉ active :=
        mem_hdRemoved_succ.mp hjrem
      have hjle : j ≤ r := by
        apply Fin.succ_le_succ_iff.mp
        exact Fin.le_def.mpr hjbound
      have hjne : j ≠ d.index := by
        intro heq
        subst j
        exact hjnot hmark
      have hpairle : d.pairing j ≤ r := by
        by_contra hnot
        have hrpair : r ≤ d.pairing j :=
          le_of_lt (lt_of_not_ge hnot)
        exact hsep j hjnot r hr
          (Or.inl ⟨hjle, hrpair⟩)
      rw [headDeletionData_succ_ne κ hκ j hjne]
      exact Fin.succ_le_succ_iff.mpr hpairle

/-- Active and removed indices partition every prefix whose right
endpoint lies in the active tail. -/
theorem hdActivePrefix_union_removedPrefix
    {n : ℕ} (active : Finset (Fin n))
    (r : Fin n) :
    relIcc (hdGlobalActive active) 0 r.succ ∪
        (hdRemoved active ∩
          Finset.univ.filter
            (fun i : Fin (n + 1) =>
              i.val ≤ r.succ.val)) =
      Finset.univ.filter
        (fun i : Fin (n + 1) =>
          i.val ≤ r.succ.val) := by
  ext i
  simp only [Finset.mem_union, mem_relIcc,
    Fin.zero_le, true_and, Finset.mem_inter,
    Finset.mem_filter, Finset.mem_univ, hdRemoved,
    Finset.mem_sdiff]
  tauto

/-- Any fully paired ordinary prefix has positive even size, hence is
one of the paper's `headEvenPrefix` sets. -/
theorem hasFullyPairedHeadPrefix_of_fullyPairedPrefix
    {m : ℕ} (κ : PartialPairing (Fin (m + 1)))
    (b : Fin (m + 1))
    (hfull :
      IsFullyPairedOn κ
        (Finset.univ.filter
          (fun i : Fin (m + 1) => i.val ≤ b.val))) :
    HasFullyPairedHeadPrefix κ := by
  let B : Finset (Fin (m + 1)) :=
    Finset.univ.filter
      (fun i : Fin (m + 1) => i.val ≤ b.val)
  let τ : PartialPairing B :=
    restrictTo κ (by
      intro i hi
      apply hfull.apply_mem
      simpa only [B] using hi)
  have hτfull : τ.IsFull := by
    intro i hfix
    apply hfull.ne_of_mem
        (by simpa only [B] using i.2)
    exact
      (congrArg Subtype.val hfix)
  have heven : Even (Fintype.card B) :=
    hτfull.even_card
  have hcard : Fintype.card B = b.val + 1 := by
    rw [Fintype.card_coe]
    change
      (Finset.univ.filter
        (fun i : Fin (m + 1) =>
          i.val ≤ b.val)).card = b.val + 1
    have hfilter :
        Finset.univ.filter
            (fun i : Fin (m + 1) =>
              i.val ≤ b.val) =
          Finset.univ.filter
            (fun i : Fin (m + 1) =>
              i.val < b.val + 1) := by
      ext i
      simp only [Finset.mem_filter,
        Finset.mem_univ, true_and]
      omega
    rw [hfilter, Fin.card_filter_val_lt,
      Nat.min_eq_right]
    omega
  rw [hcard] at heven
  obtain ⟨q, hq⟩ := heven
  have hqpos : 1 ≤ q := by omega
  have hqle : 2 * q ≤ m + 1 := by
    have hb := b.isLt
    omega
  refine ⟨q, hqpos, hqle, ?_⟩
  have hset :
      headEvenPrefix m q =
        Finset.univ.filter
          (fun i : Fin (m + 1) =>
            i.val ≤ b.val) := by
    ext i
    rw [mem_headEvenPrefix]
    simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]
    omega
  rw [hset]
  exact hfull

/-- Under the removed-set and separation invariants, a relative
candidate beginning at the head would reconstruct an original fully
paired head prefix. -/
theorem no_headCandidate_of_noPrefix
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0)
    (active : Finset (Fin n))
    (hnoprefix : ¬HasFullyPairedHeadPrefix κ)
    (hremoved : IsFullyPairedOn κ (hdRemoved active))
    (hsep : HdSeparated (headDeletionData κ hκ) active)
    (hmark : (headDeletionData κ hκ).index ∈ active) :
    ¬∃ b : Fin (n + 1),
      IsRelFullyPaired κ
        (hdGlobalActive active) 0 b := by
  rintro ⟨b, hb⟩
  obtain rfl | ⟨r, rfl⟩ :=
    Fin.eq_zero_or_eq_succ b
  · have hout :=
      hb.isFullyPairedOn.apply_mem
        hb.left_mem_relIcc
    have houtLe := (mem_relIcc.mp hout).2.2
    apply hκ
    exact Fin.le_zero_iff.mp houtLe
  · have hr : r ∈ active :=
      mem_hdGlobalActive_succ.mp hb.right_mem
    have hremovedPrefix :=
      hdRemoved_prefix_fullyPaired
        κ hκ active hremoved hsep hmark r hr
    have hprefix :
        IsFullyPairedOn κ
          (Finset.univ.filter
            (fun i : Fin (n + 1) =>
              i.val ≤ r.succ.val)) := by
      have hunion :=
        hb.isFullyPairedOn.union hremovedPrefix
      rw [hdActivePrefix_union_removedPrefix] at hunion
      exact hunion
    exact hnoprefix
      (hasFullyPairedHeadPrefix_of_fullyPairedPrefix
        κ r.succ hprefix)

/-- If no relative candidate begins at the head, the deterministic
selector commutes exactly with deleting that head. -/
theorem selectRel_headDeletion_eq_succ_of_no_head
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0)
    (active : Finset (Fin n))
    (hnohead :
      ¬∃ b : Fin (n + 1),
        IsRelFullyPaired κ
          (hdGlobalActive active) 0 b)
    (hg : ∃ l r,
      IsRelFullyPaired κ
        (hdGlobalActive active) l r)
    (hl : ∃ l r,
      IsRelFullyPaired
        (headDeletionData κ hκ).pairing
        active l r) :
    selectRel κ (hdGlobalActive active) hg =
      hdSuccPair
        (selectRel
          (headDeletionData κ hκ).pairing
          active hl) := by
  let d := headDeletionData κ hκ
  let p := selectRel κ (hdGlobalActive active) hg
  let s := selectRel d.pairing active hl
  have hp :
      IsRelFullyPaired κ
        (hdGlobalActive active) p.1 p.2 :=
    selectRel_isRelFullyPaired κ
      (hdGlobalActive active) hg
  have hs :
      IsRelFullyPaired d.pairing active s.1 s.2 :=
    selectRel_isRelFullyPaired d.pairing active hl
  have hsGlobal :
      IsRelFullyPaired κ
        (hdGlobalActive active)
        s.1.succ s.2.succ :=
    (isRelFullyPaired_headDeletion_succ_iff
      κ hκ active s.1 s.2).mpr hs
  have hpFirst :
      ∃ l : Fin n, p.1 = l.succ := by
    obtain hpzero | ⟨l, hlp⟩ :=
      Fin.eq_zero_or_eq_succ p.1
    · exfalso
      apply hnohead
      refine ⟨p.2, ?_⟩
      simpa only [hpzero] using hp
    · exact ⟨l, hlp⟩
  obtain ⟨l, hpl⟩ := hpFirst
  have hpSecond :
      ∃ r : Fin n, p.2 = r.succ := by
    obtain hpzero | ⟨r, hrp⟩ :=
      Fin.eq_zero_or_eq_succ p.2
    · have hle := hp.le
      rw [hpl, hpzero] at hle
      have hlev : l.val + 1 ≤ 0 := hle
      omega
    · exact ⟨r, hrp⟩
  obtain ⟨r, hpr⟩ := hpSecond
  have hlr :
      IsRelFullyPaired d.pairing active l r := by
    apply (isRelFullyPaired_headDeletion_succ_iff
      κ hκ active l r).mp
    simpa only [hpl, hpr] using hp
  have hglobalCardLe :=
    selectRel_card_le hg hsGlobal
  change
    (relIcc (hdGlobalActive active)
        p.1 p.2).card ≤
      (relIcc (hdGlobalActive active)
        s.1.succ s.2.succ).card at hglobalCardLe
  rw [hpl, hpr, card_relIcc_hd_succ,
    card_relIcc_hd_succ] at hglobalCardLe
  have hlocalCardLe :=
    selectRel_card_le hl hlr
  change
    (relIcc active s.1 s.2).card ≤
      (relIcc active l r).card at hlocalCardLe
  have hcard :
      (relIcc active s.1 s.2).card =
        (relIcc active l r).card :=
    le_antisymm hlocalCardLe hglobalCardLe
  have hglobalCard :
      (relIcc (hdGlobalActive active)
          p.1 p.2).card =
        (relIcc (hdGlobalActive active)
          s.1.succ s.2.succ).card := by
    rw [hpl, hpr, card_relIcc_hd_succ,
      card_relIcc_hd_succ]
    exact hcard.symm
  have hglobalFst :=
    selectRel_fst_le hg hsGlobal hglobalCard
  change p.1 ≤ s.1.succ at hglobalFst
  rw [hpl, Fin.succ_le_succ_iff] at hglobalFst
  have hlocalFst :=
    selectRel_fst_le hl hlr hcard
  change s.1 ≤ l at hlocalFst
  have hfst : s.1 = l :=
    le_antisymm hlocalFst hglobalFst
  have hglobalFstEq : p.1 = s.1.succ := by
    rw [hpl, hfst]
  have hglobalSnd :=
    selectRel_snd_le
      hg hsGlobal hglobalCard hglobalFstEq
  change p.2 ≤ s.2.succ at hglobalSnd
  rw [hpr, Fin.succ_le_succ_iff] at hglobalSnd
  have hlocalSnd :=
    selectRel_snd_le hl hlr hcard hfst
  change s.2 ≤ r at hlocalSnd
  have hsnd : s.2 = r :=
    le_antisymm hlocalSnd hglobalSnd
  change p = hdSuccPair s
  have hglobalSndEq : p.2 = s.2.succ := by
    rw [hpr, hsnd]
  exact Prod.ext hglobalFstEq hglobalSndEq

/-- With neither a head candidate nor a tail candidate, the ambient
head-extended state has no candidate at all. -/
theorem no_globalCandidate_of_no_head_no_tail
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0)
    (active : Finset (Fin n))
    (hnohead :
      ¬∃ b : Fin (n + 1),
        IsRelFullyPaired κ
          (hdGlobalActive active) 0 b)
    (hnotail :
      ¬∃ l r,
        IsRelFullyPaired
          (headDeletionData κ hκ).pairing
          active l r) :
    ¬∃ l r,
      IsRelFullyPaired κ
        (hdGlobalActive active) l r := by
  rintro ⟨l, r, hlr⟩
  obtain rfl | ⟨i, rfl⟩ :=
    Fin.eq_zero_or_eq_succ l
  · exact hnohead ⟨r, hlr⟩
  · obtain rfl | ⟨j, rfl⟩ :=
      Fin.eq_zero_or_eq_succ r
    · have hle := hlr.le
      have hlev : i.val + 1 ≤ 0 := hle
      omega
    · apply hnotail
      refine ⟨i, j, ?_⟩
      exact
        (isRelFullyPaired_headDeletion_succ_iff
          κ hκ active i j).mp hlr

/-! ## Exact no-prefix extraction recursion -/

/-- State-level recursion for case (2).  The removed-set invariant is
what rules out a relative head interval after earlier tail intervals
have been extracted. -/
theorem extractAux_headDeletion_noPrefix_state
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0)
    (hnoprefix : ¬HasFullyPairedHeadPrefix κ)
    (fuel : ℕ) :
    ∀ active : Finset (Fin n),
      active.card ≤ 2 * fuel + 1 →
      IsFullyPairedOn κ (hdRemoved active) →
      HdSeparated (headDeletionData κ hκ) active →
      (headDeletionData κ hκ).index ∈ active →
      extractAux κ (fuel + 1)
          (hdGlobalActive active) =
        (extractAux
          (headDeletionData κ hκ).pairing
          fuel active).map hdSuccPair := by
  induction fuel with
  | zero =>
      intro active hcard hremoved hsep hmark
      have hnotail :
          ¬∃ l r,
            IsRelFullyPaired
              (headDeletionData κ hκ).pairing
              active l r := by
        rintro ⟨l, r, hlr⟩
        have htwo := hlr.two_le_card
        have hsub :=
          Finset.card_le_card
            (relIcc_subset_active active l r)
        omega
      have hnohead :=
        no_headCandidate_of_noPrefix
          κ hκ active hnoprefix
          hremoved hsep hmark
      have hnoglobal :=
        no_globalCandidate_of_no_head_no_tail
          κ hκ active hnohead hnotail
      rw [extractAux_succ_neg 0 hnoglobal,
        extractAux_zero]
      rfl
  | succ fuel ih =>
      intro active hcard hremoved hsep hmark
      let d := headDeletionData κ hκ
      have hnohead :=
        no_headCandidate_of_noPrefix
          κ hκ active hnoprefix
          hremoved hsep hmark
      by_cases htail :
          ∃ l r,
            IsRelFullyPaired d.pairing
              active l r
      · let s := selectRel d.pairing active htail
        have hs :
            IsRelFullyPaired d.pairing
              active s.1 s.2 :=
          selectRel_isRelFullyPaired
            d.pairing active htail
        have hsGlobal :
            IsRelFullyPaired κ
              (hdGlobalActive active)
              s.1.succ s.2.succ :=
          (isRelFullyPaired_headDeletion_succ_iff
            κ hκ active s.1 s.2).mpr hs
        let hglobal : ∃ l r,
            IsRelFullyPaired κ
              (hdGlobalActive active) l r :=
          ⟨s.1.succ, s.2.succ, hsGlobal⟩
        have hsel :
            selectRel κ
                (hdGlobalActive active) hglobal =
              hdSuccPair s :=
          selectRel_headDeletion_eq_succ_of_no_head
            κ hκ active hnohead hglobal htail
        let active' :=
          active \ relIcc active s.1 s.2
        have hcard' :
            active'.card ≤ 2 * fuel + 1 := by
          have hshrink :=
            card_sdiff_relIcc_add_two_le hs
          change
            active.card ≤
              2 * (fuel + 1) + 1 at hcard
          change
            (active \
              relIcc active s.1 s.2).card ≤
                2 * fuel + 1
          omega
        have hremoved' :
            IsFullyPairedOn κ
              (hdRemoved active') := by
          exact hdRemoved_fullyPaired_sdiff
            hremoved hsGlobal
        have hsep' :
            HdSeparated d active' :=
          hdSeparated_sdiff_relIcc
            hsep hs.isFullyPairedOn
        have hmark' : d.index ∈ active' :=
          hdMarkedIndex_mem_sdiff
            d hmark hs
        have hrec :=
          ih active' hcard' hremoved'
            hsep' hmark'
        have hglobalStep :
            extractAux κ ((fuel + 1) + 1)
                (hdGlobalActive active) =
              selectRel κ
                  (hdGlobalActive active) hglobal ::
                extractAux κ (fuel + 1)
                  (hdGlobalActive active \
                    relIcc (hdGlobalActive active)
                      (selectRel κ
                        (hdGlobalActive active)
                        hglobal).1
                      (selectRel κ
                        (hdGlobalActive active)
                        hglobal).2) :=
          extractAux_succ_pos (fuel + 1) hglobal
        have hlocalStep :
            extractAux d.pairing
                (fuel + 1) active =
              s ::
                extractAux d.pairing
                  fuel active' := by
          change
            extractAux d.pairing
                (fuel + 1) active =
              selectRel d.pairing active htail ::
                extractAux d.pairing fuel
                  (active \
                    relIcc active
                      (selectRel d.pairing
                        active htail).1
                      (selectRel d.pairing
                        active htail).2)
          exact extractAux_succ_pos fuel htail
        rw [hglobalStep, hlocalStep,
          List.map_cons, hsel]
        change
          hdSuccPair s ::
              extractAux κ (fuel + 1)
                (hdGlobalActive active \
                  relIcc (hdGlobalActive active)
                    s.1.succ s.2.succ) =
            hdSuccPair s ::
              (extractAux d.pairing
                fuel active').map hdSuccPair
        rw [hdGlobalActive_sdiff_succ]
        exact congrArg
          (List.cons (hdSuccPair s)) hrec
      · have hnoglobal :=
          no_globalCandidate_of_no_head_no_tail
            κ hκ active hnohead htail
        rw [extractAux_succ_neg
          (fuel + 1) hnoglobal]
        rw [extractAux_nil_of_no_candidate
          _ htail]
        rfl

/-- Public extraction theorem for a paired head with no fully paired
head prefix: head deletion only shifts the old extraction list. -/
theorem extract_headDeletion_noPrefix
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0)
    (hnoprefix : ¬HasFullyPairedHeadPrefix κ) :
    extract κ =
      (extract
        (headDeletionData κ hκ).pairing).map
          hdSuccPair := by
  unfold extract
  have hstate :=
    extractAux_headDeletion_noPrefix_state
      κ hκ hnoprefix n
      (Finset.univ : Finset (Fin n))
      (by simp; omega)
      (by
        rw [hdRemoved_univ]
        exact isFullyPairedOn_empty κ)
      (hdSeparated_univ
        (headDeletionData κ hκ))
      (by simp)
  simpa only [hdGlobalActive_univ] using hstate

/-- Deleting a head which was introduced from marked-single data recovers
that data exactly. -/
theorem headDeletionData_wickHeadEquiv
    {n : ℕ} (d : MarkedSingle (Fin n))
    (hκ :
      wickHeadEquiv n (Sum.inr d) 0 ≠ 0) :
    headDeletionData
        (wickHeadEquiv n (Sum.inr d)) hκ =
      d := by
  apply (contractionHeadEquiv n).injective
  apply Subtype.ext
  calc
    ((contractionHeadEquiv n)
        (headDeletionData
          (wickHeadEquiv n (Sum.inr d))
          hκ)).1 =
        wickHeadEquiv n (Sum.inr d) :=
      contractionHeadEquiv_headDeletionData
        (wickHeadEquiv n (Sum.inr d)) hκ
    _ = ((contractionHeadEquiv n) d).1 := by
      rfl

/-- The no-prefix head class implies the exact extraction compatibility
used by the analytic case-(2) factorization. -/
theorem contractionExtractCompatible_of_headPairedNoPrefix
    {n : ℕ} (d : MarkedSingle (Fin n))
    (hcase :
      HeadPairedNoPrefix
        (wickHeadEquiv n (Sum.inr d))) :
    ContractionExtractCompatible d := by
  let κ :=
    wickHeadEquiv n (Sum.inr d)
  have hκ : κ 0 ≠ 0 := hcase.1
  have hd :
      headDeletionData κ hκ = d :=
    headDeletionData_wickHeadEquiv d hκ
  have hextract :=
    extract_headDeletion_noPrefix
      κ hκ hcase.2
  rw [hd] at hextract
  exact hextract

/-- Marked old singles whose new head has no fully paired prefix are in
bijection with the paper's case-(2) pairings. -/
def noPrefixMarkedEquiv (n : ℕ) :
    {d : MarkedSingle (Fin n) //
      HeadPairedNoPrefix
        (wickHeadEquiv n (Sum.inr d))} ≃
      {κ : PartialPairing (Fin (n + 1)) //
        HeadPairedNoPrefix κ} where
  toFun d :=
    ⟨wickHeadEquiv n (Sum.inr d.1), d.2⟩
  invFun κ := by
    let d :=
      headDeletionData κ.1 κ.2.1
    refine ⟨d, ?_⟩
    have heq :
        (contractionHeadEquiv n d).1 = κ.1 :=
      contractionHeadEquiv_headDeletionData
        κ.1 κ.2.1
    change
      HeadPairedNoPrefix
        (wickHeadEquiv n (Sum.inr d))
    rw [← contractionHeadEquiv_apply_val,
      heq]
    exact κ.2
  left_inv d := by
    apply Subtype.ext
    exact headDeletionData_wickHeadEquiv
      d.1 d.2.1
  right_inv κ := by
    apply Subtype.ext
    exact contractionHeadEquiv_headDeletionData
      κ.1 κ.2.1

/-- Summed case (2) of Proposition 3.4.  Every marked contraction with
no fully paired head prefix is integrated and reindexed to the
corresponding paper pairing with multiplicity one. -/
theorem sum_headPairedNoPrefixContribution_eq_randRI
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hint :
      ∀ d :
          {d : MarkedSingle (Fin n) //
            HeadPairedNoPrefix
              (wickHeadEquiv n (Sum.inr d))},
        MeasureTheory.Integrable
          (fun u : Fin (n + 1) → T4 =>
            randIntegrand M ρ ε
              (wickHeadEquiv n
                (Sum.inr d.1))
              (assemble x y u) ω)
          (Measure.pi fun _ => paperMeasure)) :
    (∑ d :
        {d : MarkedSingle (Fin n) //
          HeadPairedNoPrefix
            (wickHeadEquiv n (Sum.inr d))},
      headPairedContractionContribution
        M ρ lam ε n d.1 x y ω) =
      ∑ κ :
          {κ : PartialPairing (Fin (n + 1)) //
            HeadPairedNoPrefix κ},
        randRI M ρ lam ε (n + 1)
          κ.1 x y ω := by
  calc
    _ =
        ∑ d :
            {d : MarkedSingle (Fin n) //
              HeadPairedNoPrefix
                (wickHeadEquiv n
                  (Sum.inr d))},
          randRI M ρ lam ε (n + 1)
            (wickHeadEquiv n
              (Sum.inr d.1)) x y ω := by
      apply Fintype.sum_congr
      intro d
      exact
        headPairedContractionContribution_eq_randRI
          M ρ lam ε n d.1
          (contractionExtractCompatible_of_headPairedNoPrefix
            d.1 d.2)
          x y ω (hint d)
    _ = _ :=
      (noPrefixMarkedEquiv n).sum_comp
        (fun κ =>
          randRI M ρ lam ε (n + 1)
            κ.1 x y ω)

end PartialPairing

end

end Anderson4D
