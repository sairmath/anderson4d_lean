import Anderson4D.Parametrix.IdentityCombinatorics

/-!
Extraction compatibility for consecutive pairing blocks.

This file proves that the relative smallest-leftmost extraction algorithm
acts independently on two consecutive closed pairing blocks, up to the
interleaving order recorded by `List.Perm`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

namespace PartialPairing

def eaPrefixEmbedding {N a : ℕ} (ha : a ≤ N) : Fin a ↪ Fin N where
  toFun := Fin.castLE ha
  inj' i j h := by
    apply Fin.ext
    exact congrArg (fun z : Fin N => z.val) h

def eaSuffixEmbedding {N a : ℕ} (ha : a ≤ N) :
    Fin (N - a) ↪ Fin N where
  toFun := suffixFin ha
  inj' i j h := by
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [suffixFin_val] at hv
    omega

def eaPrefixPair {N a : ℕ} (ha : a ≤ N)
    (p : Fin a × Fin a) : Fin N × Fin N :=
  (Fin.castLE ha p.1, Fin.castLE ha p.2)

def eaSuffixPair {N a : ℕ} (ha : a ≤ N)
    (p : Fin (N - a) × Fin (N - a)) : Fin N × Fin N :=
  (suffixFin ha p.1, suffixFin ha p.2)

def eaPrefixActive {N a : ℕ} (ha : a ≤ N)
    (active : Finset (Fin N)) : Finset (Fin a) :=
  Finset.univ.filter fun i => Fin.castLE ha i ∈ active

def eaSuffixActive {N a : ℕ} (ha : a ≤ N)
    (active : Finset (Fin N)) : Finset (Fin (N - a)) :=
  Finset.univ.filter fun j => suffixFin ha j ∈ active

@[simp]
theorem mem_eaPrefixActive {N a : ℕ} (ha : a ≤ N)
    {active : Finset (Fin N)} {i : Fin a} :
    i ∈ eaPrefixActive ha active ↔ Fin.castLE ha i ∈ active := by
  simp [eaPrefixActive]

@[simp]
theorem mem_eaSuffixActive {N a : ℕ} (ha : a ≤ N)
    {active : Finset (Fin N)} {j : Fin (N - a)} :
    j ∈ eaSuffixActive ha active ↔ suffixFin ha j ∈ active := by
  simp [eaSuffixActive]

theorem eaPrefixActive_relIcc_prefix
    {N a : ℕ} (ha : a ≤ N) (active : Finset (Fin N))
    (l r : Fin a) :
    eaPrefixActive ha
        (relIcc active (Fin.castLE ha l) (Fin.castLE ha r)) =
      relIcc (eaPrefixActive ha active) l r := by
  ext i
  simp only [mem_eaPrefixActive, mem_relIcc]
  constructor
  · rintro ⟨hi, hil, hir⟩
    exact ⟨hi, hil, hir⟩
  · rintro ⟨hi, hil, hir⟩
    exact ⟨hi, hil, hir⟩

theorem relIcc_prefix_eq_map
    {N a : ℕ} (ha : a ≤ N) (active : Finset (Fin N))
    (l r : Fin a) :
    relIcc active (Fin.castLE ha l) (Fin.castLE ha r) =
      (relIcc (eaPrefixActive ha active) l r).map
        (eaPrefixEmbedding ha) := by
  ext i
  constructor
  · intro hi
    have hi' := mem_relIcc.mp hi
    have hia : i.val < a :=
      lt_of_le_of_lt (show i.val ≤ r.val from hi'.2.2) r.isLt
    let j : Fin a := ⟨i.val, hia⟩
    have hcast : Fin.castLE ha j = i := Fin.ext rfl
    rw [Finset.mem_map]
    refine ⟨j, ?_, hcast⟩
    rw [mem_relIcc]
    refine ⟨(mem_eaPrefixActive ha).mpr
      (by simpa only [hcast] using hi'.1), ?_, ?_⟩
    · apply Fin.le_def.mpr
      have hil := hi'.2.1
      rw [← hcast] at hil
      exact hil
    · apply Fin.le_def.mpr
      have hir := hi'.2.2
      rw [← hcast] at hir
      exact hir
  · intro hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have hj' := mem_relIcc.mp hj
    rw [mem_relIcc]
    refine ⟨(mem_eaPrefixActive ha).mp hj'.1, ?_, ?_⟩
    · exact hj'.2.1
    · exact hj'.2.2

theorem card_relIcc_prefix
    {N a : ℕ} (ha : a ≤ N) (active : Finset (Fin N))
    (l r : Fin a) :
    (relIcc active (Fin.castLE ha l) (Fin.castLE ha r)).card =
      (relIcc (eaPrefixActive ha active) l r).card := by
  rw [relIcc_prefix_eq_map, Finset.card_map]

@[simp]
theorem mem_relIcc_prefix_iff
    {N a : ℕ} (ha : a ≤ N) {active : Finset (Fin N)}
    (l r i : Fin a) :
    Fin.castLE ha i ∈
        relIcc active (Fin.castLE ha l) (Fin.castLE ha r) ↔
      i ∈ relIcc (eaPrefixActive ha active) l r := by
  simp [mem_relIcc, eaPrefixActive]

theorem eaSuffixActive_relIcc_suffix
    {N a : ℕ} (ha : a ≤ N) (active : Finset (Fin N))
    (l r : Fin (N - a)) :
    eaSuffixActive ha
        (relIcc active (suffixFin ha l) (suffixFin ha r)) =
      relIcc (eaSuffixActive ha active) l r := by
  ext j
  simp only [mem_eaSuffixActive, mem_relIcc]
  constructor
  · rintro ⟨hj, hjl, hjr⟩
    exact ⟨hj, Fin.le_def.mpr (by
      change a + l.val ≤ a + j.val at hjl
      omega), Fin.le_def.mpr (by
      change a + j.val ≤ a + r.val at hjr
      omega)⟩
  · rintro ⟨hj, hjl, hjr⟩
    exact ⟨hj, Fin.le_def.mpr (by
      change l.val ≤ j.val at hjl
      change a + l.val ≤ a + j.val
      omega), Fin.le_def.mpr (by
      change j.val ≤ r.val at hjr
      change a + j.val ≤ a + r.val
      omega)⟩

theorem relIcc_suffix_eq_map
    {N a : ℕ} (ha : a ≤ N) (active : Finset (Fin N))
    (l r : Fin (N - a)) :
    relIcc active (suffixFin ha l) (suffixFin ha r) =
      (relIcc (eaSuffixActive ha active) l r).map
        (eaSuffixEmbedding ha) := by
  ext i
  constructor
  · intro hi
    have hi' := mem_relIcc.mp hi
    have hia : a ≤ i.val := by
      have := hi'.2.1
      change a + l.val ≤ i.val at this
      omega
    let j : Fin (N - a) := ⟨i.val - a, by omega⟩
    have hsuf : suffixFin ha j = i := by
      apply Fin.ext
      simp [j]
      omega
    rw [Finset.mem_map]
    refine ⟨j, ?_, hsuf⟩
    have hiActive : suffixFin ha j ∈ active := by
      simpa only [hsuf] using hi'.1
    have hjl : l ≤ j := by
      apply Fin.le_def.mpr
      have hil := hi'.2.1
      rw [← hsuf] at hil
      change a + l.val ≤ a + j.val at hil
      omega
    have hjr : j ≤ r := by
      apply Fin.le_def.mpr
      have hir := hi'.2.2
      rw [← hsuf] at hir
      change a + j.val ≤ a + r.val at hir
      omega
    exact mem_relIcc.mpr
      ⟨(mem_eaSuffixActive ha).mpr hiActive, hjl, hjr⟩
  · intro hi
    rw [Finset.mem_map] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have hj' := mem_relIcc.mp hj
    rw [mem_relIcc]
    refine ⟨(mem_eaSuffixActive ha).mp hj'.1, ?_, ?_⟩
    · apply Fin.le_def.mpr
      change a + l.val ≤ a + j.val
      exact Nat.add_le_add_left
        (show l.val ≤ j.val from hj'.2.1) a
    · apply Fin.le_def.mpr
      change a + j.val ≤ a + r.val
      exact Nat.add_le_add_left
        (show j.val ≤ r.val from hj'.2.2) a

theorem card_relIcc_suffix
    {N a : ℕ} (ha : a ≤ N) (active : Finset (Fin N))
    (l r : Fin (N - a)) :
    (relIcc active (suffixFin ha l) (suffixFin ha r)).card =
      (relIcc (eaSuffixActive ha active) l r).card := by
  rw [relIcc_suffix_eq_map, Finset.card_map]

@[simp]
theorem mem_relIcc_suffix_iff
    {N a : ℕ} (ha : a ≤ N) {active : Finset (Fin N)}
    (l r i : Fin (N - a)) :
    suffixFin ha i ∈
        relIcc active (suffixFin ha l) (suffixFin ha r) ↔
      i ∈ relIcc (eaSuffixActive ha active) l r := by
  simp only [mem_relIcc, mem_eaSuffixActive]
  constructor
  · rintro ⟨hi, hil, hir⟩
    exact ⟨hi, Fin.le_def.mpr (by
      change a + l.val ≤ a + i.val at hil
      omega), Fin.le_def.mpr (by
      change a + i.val ≤ a + r.val at hir
      omega)⟩
  · rintro ⟨hi, hil, hir⟩
    exact ⟨hi, Fin.le_def.mpr (by
      change l.val ≤ i.val at hil
      change a + l.val ≤ a + i.val
      omega), Fin.le_def.mpr (by
      change i.val ≤ r.val at hir
      change a + i.val ≤ a + r.val
      omega)⟩

theorem isRelFullyPaired_append_prefix_iff
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (active : Finset (Fin N)) (l r : Fin a) :
    IsRelFullyPaired (appendPairingTo ha σ τ) active
        (Fin.castLE ha l) (Fin.castLE ha r) ↔
      IsRelFullyPaired σ (eaPrefixActive ha active) l r := by
  rw [IsRelFullyPaired]
  rw [IsRelFullyPaired]
  constructor
  · rintro ⟨hl, hr, hlr, hfull⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [eaPrefixActive] using hl
    · simpa [eaPrefixActive] using hr
    · exact hlr
    · constructor
      · intro i hi hfix
        have hgi :
            Fin.castLE ha i ∈
              relIcc active (Fin.castLE ha l) (Fin.castLE ha r) := by
          exact (mem_relIcc_prefix_iff ha l r i).mpr hi
        apply hfull.1 (Fin.castLE ha i) hgi
        rw [appendPairingTo_apply_prefix, hfix]
      · intro i hi
        have hgi :
            Fin.castLE ha i ∈
              relIcc active (Fin.castLE ha l) (Fin.castLE ha r) := by
          exact (mem_relIcc_prefix_iff ha l r i).mpr hi
        have hout := hfull.2 (Fin.castLE ha i) hgi
        rw [appendPairingTo_apply_prefix] at hout
        exact (mem_relIcc_prefix_iff ha l r (σ i)).mp hout
  · rintro ⟨hl, hr, hlr, hfull⟩
    refine ⟨(by simpa [eaPrefixActive] using hl),
      (by simpa [eaPrefixActive] using hr), hlr, ?_⟩
    constructor
    · intro i hi hfix
      have hil : i.val < a := by
        have hir : i ≤ Fin.castLE ha r :=
          (mem_relIcc.mp hi).2.2
        exact lt_of_le_of_lt
          (show i.val ≤ r.val from hir) r.isLt
      let j : Fin a := ⟨i.val, hil⟩
      have hcast : Fin.castLE ha j = i := Fin.ext rfl
      have hj :
          j ∈ relIcc (eaPrefixActive ha active) l r := by
        exact (mem_relIcc_prefix_iff ha l r j).mp
          (by simpa only [hcast] using hi)
      apply hfull.1 j hj
      apply Fin.ext
      have hfixv := congrArg Fin.val hfix
      rw [← hcast, appendPairingTo_apply_prefix] at hfixv
      exact hfixv
    · intro i hi
      have hil : i.val < a := by
        have hir : i ≤ Fin.castLE ha r :=
          (mem_relIcc.mp hi).2.2
        exact lt_of_le_of_lt
          (show i.val ≤ r.val from hir) r.isLt
      let j : Fin a := ⟨i.val, hil⟩
      have hcast : Fin.castLE ha j = i := Fin.ext rfl
      have hj :
          j ∈ relIcc (eaPrefixActive ha active) l r := by
        exact (mem_relIcc_prefix_iff ha l r j).mp
          (by simpa only [hcast] using hi)
      have hout := hfull.2 j hj
      have hgout := (mem_relIcc_prefix_iff ha l r (σ j)).mpr hout
      rw [← hcast, appendPairingTo_apply_prefix]
      exact hgout

theorem isRelFullyPaired_append_suffix_iff
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (active : Finset (Fin N)) (l r : Fin (N - a)) :
    IsRelFullyPaired (appendPairingTo ha σ τ) active
        (suffixFin ha l) (suffixFin ha r) ↔
      IsRelFullyPaired τ (eaSuffixActive ha active) l r := by
  rw [IsRelFullyPaired]
  rw [IsRelFullyPaired]
  constructor
  · rintro ⟨hl, hr, hlr, hfull⟩
    refine ⟨(by simpa [eaSuffixActive] using hl),
      (by simpa [eaSuffixActive] using hr),
      Fin.le_def.mpr (by
        change a + l.val ≤ a + r.val at hlr
        omega), ?_⟩
    constructor
    · intro j hj hfix
      have hgj :
          suffixFin ha j ∈
            relIcc active (suffixFin ha l) (suffixFin ha r) := by
        exact (mem_relIcc_suffix_iff ha l r j).mpr hj
      apply hfull.1 (suffixFin ha j) hgj
      rw [appendPairingTo_apply_suffix, hfix]
    · intro j hj
      have hgj :
          suffixFin ha j ∈
            relIcc active (suffixFin ha l) (suffixFin ha r) := by
        exact (mem_relIcc_suffix_iff ha l r j).mpr hj
      have hout := hfull.2 (suffixFin ha j) hgj
      rw [appendPairingTo_apply_suffix] at hout
      exact (mem_relIcc_suffix_iff ha l r (τ j)).mp hout
  · rintro ⟨hl, hr, hlr, hfull⟩
    refine ⟨(by simpa [eaSuffixActive] using hl),
      (by simpa [eaSuffixActive] using hr),
      Fin.le_def.mpr (by
        change l.val ≤ r.val at hlr
        change a + l.val ≤ a + r.val
        omega), ?_⟩
    constructor
    · intro i hi hfix
      have hia : a ≤ i.val := by
        have hil : suffixFin ha l ≤ i :=
          (mem_relIcc.mp hi).2.1
        change a + l.val ≤ i.val at hil
        omega
      let j : Fin (N - a) := ⟨i.val - a, by omega⟩
      have hsuf : suffixFin ha j = i := by
        apply Fin.ext
        simp [j]
        omega
      have hj :
          j ∈ relIcc (eaSuffixActive ha active) l r := by
        exact (mem_relIcc_suffix_iff ha l r j).mp
          (by simpa only [hsuf] using hi)
      apply hfull.1 j hj
      apply Fin.ext
      have hfixv := congrArg Fin.val hfix
      rw [← hsuf, appendPairingTo_apply_suffix] at hfixv
      simp only [suffixFin_val] at hfixv
      omega
    · intro i hi
      have hia : a ≤ i.val := by
        have hil : suffixFin ha l ≤ i :=
          (mem_relIcc.mp hi).2.1
        change a + l.val ≤ i.val at hil
        omega
      let j : Fin (N - a) := ⟨i.val - a, by omega⟩
      have hsuf : suffixFin ha j = i := by
        apply Fin.ext
        simp [j]
        omega
      have hj :
          j ∈ relIcc (eaSuffixActive ha active) l r := by
        exact (mem_relIcc_suffix_iff ha l r j).mp
          (by simpa only [hsuf] using hi)
      have hout := hfull.2 j hj
      have hgout := (mem_relIcc_suffix_iff ha l r (τ j)).mpr hout
      rw [← hsuf, appendPairingTo_apply_suffix]
      exact hgout

theorem eaPrefixActive_sdiff_prefix
    {N a : ℕ} (ha : a ≤ N) (active : Finset (Fin N))
    (l r : Fin a) :
    eaPrefixActive ha
        (active \
          relIcc active (Fin.castLE ha l) (Fin.castLE ha r)) =
      eaPrefixActive ha active \
        relIcc (eaPrefixActive ha active) l r := by
  ext i
  simp only [mem_eaPrefixActive, Finset.mem_sdiff,
    mem_relIcc_prefix_iff]

theorem eaSuffixActive_sdiff_prefix
    {N a : ℕ} (ha : a ≤ N) (active : Finset (Fin N))
    (l r : Fin a) :
    eaSuffixActive ha
        (active \
          relIcc active (Fin.castLE ha l) (Fin.castLE ha r)) =
      eaSuffixActive ha active := by
  ext j
  simp only [mem_eaSuffixActive, Finset.mem_sdiff]
  constructor
  · exact fun h => h.1
  · intro hj
    refine ⟨hj, ?_⟩
    intro hmem
    have hle := (mem_relIcc.mp hmem).2.2
    change a + j.val ≤ r.val at hle
    omega

theorem eaPrefixActive_sdiff_suffix
    {N a : ℕ} (ha : a ≤ N) (active : Finset (Fin N))
    (l r : Fin (N - a)) :
    eaPrefixActive ha
        (active \
          relIcc active (suffixFin ha l) (suffixFin ha r)) =
      eaPrefixActive ha active := by
  ext i
  simp only [mem_eaPrefixActive, Finset.mem_sdiff]
  constructor
  · exact fun h => h.1
  · intro hi
    refine ⟨hi, ?_⟩
    intro hmem
    have hle := (mem_relIcc.mp hmem).2.1
    change a + l.val ≤ i.val at hle
    omega

theorem eaSuffixActive_sdiff_suffix
    {N a : ℕ} (ha : a ≤ N) (active : Finset (Fin N))
    (l r : Fin (N - a)) :
    eaSuffixActive ha
        (active \
          relIcc active (suffixFin ha l) (suffixFin ha r)) =
      eaSuffixActive ha active \
        relIcc (eaSuffixActive ha active) l r := by
  ext j
  simp only [mem_eaSuffixActive, Finset.mem_sdiff,
    mem_relIcc_suffix_iff]

/-- The global selector of a block-diagonal pairing never crosses the
block boundary. -/
theorem selectRel_appendPairingTo_either
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (active : Finset (Fin N))
    (h : ∃ l r,
      IsRelFullyPaired (appendPairingTo ha σ τ) active l r) :
    (∃ l r : Fin a,
        selectRel (appendPairingTo ha σ τ) active h =
          eaPrefixPair ha (l, r)) ∨
      ∃ l r : Fin (N - a),
        selectRel (appendPairingTo ha σ τ) active h =
          eaSuffixPair ha (l, r) := by
  let K := appendPairingTo ha σ τ
  let p := selectRel K active h
  have hp := selectRel_isRelFullyPaired K active h
  by_cases hleft : p.1.val < a
  · by_cases hright : p.2.val < a
    · left
      let l : Fin a := ⟨p.1.val, hleft⟩
      let r : Fin a := ⟨p.2.val, hright⟩
      refine ⟨l, r, ?_⟩
      apply Prod.ext <;> apply Fin.ext <;> rfl
    · have hright' : a ≤ p.2.val := Nat.le_of_not_gt hright
      let rb : Fin (N - a) := ⟨p.2.val - a, by
        have := p.2.isLt
        omega⟩
      have hsufb : suffixFin ha rb = p.2 := by
        apply Fin.ext
        simp only [suffixFin_val]
        dsimp [rb]
        omega
      let A := eaSuffixActive ha active
      have hrbA : rb ∈ A := by
        change rb ∈ eaSuffixActive ha active
        rw [mem_eaSuffixActive]
        simpa only [hsufb] using hp.right_mem
      let s : Finset (Fin (N - a)) :=
        A.filter fun j => j ≤ rb
      have hsne : s.Nonempty := by
        refine ⟨rb, ?_⟩
        simp [s, hrbA]
      let l := s.min' hsne
      have hls : l ∈ s := Finset.min'_mem s hsne
      have hlA : l ∈ A := (Finset.mem_filter.mp hls).1
      have hlrb : l ≤ rb :=
        (Finset.mem_filter.mp hls).2
      have hrel : relIcc A l rb = s := by
        ext j
        simp only [mem_relIcc, s, Finset.mem_filter]
        constructor
        · rintro ⟨hjA, -, hjr⟩
          exact ⟨hjA, hjr⟩
        · rintro ⟨hjA, hjr⟩
          refine ⟨hjA, ?_, hjr⟩
          exact Finset.min'_le s j
            (Finset.mem_filter.mpr ⟨hjA, hjr⟩)
      have hlocal :
          IsRelFullyPaired τ A l rb := by
        refine ⟨hlA, hrbA, hlrb, ?_⟩
        constructor
        · intro j hj hfix
          apply hp.isFullyPairedOn.1 (suffixFin ha j)
          · rw [mem_relIcc]
            have hj' : j ∈ s := by
              rw [← hrel]
              exact hj
            have hjA := (Finset.mem_filter.mp hj').1
            have hjrb := (Finset.mem_filter.mp hj').2
            refine ⟨(by simpa [A, eaSuffixActive] using hjA), ?_, ?_⟩
            · change p.1.val ≤ a + j.val
              omega
            · rw [← hsufb]
              change a + j.val ≤ a + rb.val
              exact Nat.add_le_add_left
                (show j.val ≤ rb.val from hjrb) a
          · rw [appendPairingTo_apply_suffix, hfix]
        · intro j hj
          have hj' : j ∈ s := by
            rw [← hrel]
            exact hj
          have hjA := (Finset.mem_filter.mp hj').1
          have hjrb := (Finset.mem_filter.mp hj').2
          have hgj :
              suffixFin ha j ∈ relIcc active p.1 p.2 := by
            rw [mem_relIcc]
            refine ⟨(by simpa [A, eaSuffixActive] using hjA), ?_, ?_⟩
            · change p.1.val ≤ a + j.val
              omega
            · rw [← hsufb]
              change a + j.val ≤ a + rb.val
              exact Nat.add_le_add_left
                (show j.val ≤ rb.val from hjrb) a
          have hout := hp.isFullyPairedOn.2 (suffixFin ha j) hgj
          rw [appendPairingTo_apply_suffix] at hout
          rw [hrel]
          apply Finset.mem_filter.mpr
          constructor
          · have houtActive := (mem_relIcc.mp hout).1
            simpa [A, eaSuffixActive] using houtActive
          ·
            have houtLe := (mem_relIcc.mp hout).2.2
            rw [← hsufb] at houtLe
            change a + (τ j).val ≤ a + rb.val at houtLe
            omega
      have hcand :
          IsRelFullyPaired K active
            (suffixFin ha l) (suffixFin ha rb) := by
        exact (isRelFullyPaired_append_suffix_iff
          ha σ τ active l rb).mpr hlocal
      have hsub :
          relIcc active (suffixFin ha l) (suffixFin ha rb) ⊂
            relIcc active p.1 p.2 := by
        rw [Finset.ssubset_iff_subset_ne]
        constructor
        · intro i hi
          have hi' := mem_relIcc.mp hi
          rw [mem_relIcc]
          refine ⟨hi'.1, ?_, ?_⟩
          · have hil := hi'.2.1
            change a + l.val ≤ i.val at hil
            omega
          · simpa only [hsufb] using hi'.2.2
        · intro heq
          have hp1 :
              p.1 ∈ relIcc active p.1 p.2 :=
            hp.left_mem_relIcc
          have hp1' :
              p.1 ∈
                relIcc active (suffixFin ha l) (suffixFin ha rb) := by
            rw [heq]
            exact hp1
          have hle := (mem_relIcc.mp hp1').2.1
          have hlev := show a + l.val ≤ p.1.val from hle
          omega
      have hcardlt := Finset.card_lt_card hsub
      have hcardle := selectRel_card_le h hcand
      exact False.elim ((not_lt_of_ge hcardle) hcardlt)
  · right
    have hleft' : a ≤ p.1.val := Nat.le_of_not_gt hleft
    have hright' : a ≤ p.2.val := le_trans hleft' hp.le
    let l : Fin (N - a) := ⟨p.1.val - a, by
      have := p.1.isLt
      omega⟩
    let r : Fin (N - a) := ⟨p.2.val - a, by
      have := p.2.isLt
      omega⟩
    refine ⟨l, r, ?_⟩
    change p = eaSuffixPair ha (l, r)
    apply Prod.ext <;> apply Fin.ext
    · simp [eaSuffixPair, l]
      omega
    · simp [eaSuffixPair, r]
      omega

/-- If the global selector is in the prefix block, it is exactly the
embedded selector of the projected prefix state. -/
theorem selectRel_appendPairingTo_eq_prefix
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (active : Finset (Fin N))
    (h : ∃ l r,
      IsRelFullyPaired (appendPairingTo ha σ τ) active l r)
    (l r : Fin a)
    (hpref :
      selectRel (appendPairingTo ha σ τ) active h =
        eaPrefixPair ha (l, r)) :
    let hlocal : ∃ i j,
        IsRelFullyPaired σ (eaPrefixActive ha active) i j := by
      refine ⟨l, r, ?_⟩
      have hg :=
        selectRel_isRelFullyPaired
          (appendPairingTo ha σ τ) active h
      rw [hpref] at hg
      change
        IsRelFullyPaired (appendPairingTo ha σ τ) active
          (Fin.castLE ha l) (Fin.castLE ha r) at hg
      exact (isRelFullyPaired_append_prefix_iff
        ha σ τ active l r).mp hg
    selectRel (appendPairingTo ha σ τ) active h =
      eaPrefixPair ha
        (selectRel σ (eaPrefixActive ha active) hlocal) := by
  have hlr : IsRelFullyPaired σ
      (eaPrefixActive ha active) l r := by
    have hg :=
      selectRel_isRelFullyPaired
        (appendPairingTo ha σ τ) active h
    rw [hpref] at hg
    change
      IsRelFullyPaired (appendPairingTo ha σ τ) active
        (Fin.castLE ha l) (Fin.castLE ha r) at hg
    exact (isRelFullyPaired_append_prefix_iff
      ha σ τ active l r).mp hg
  let hlocal : ∃ i j,
      IsRelFullyPaired σ (eaPrefixActive ha active) i j :=
    ⟨l, r, hlr⟩
  let s := selectRel σ (eaPrefixActive ha active) hlocal
  have hs :=
    selectRel_isRelFullyPaired σ (eaPrefixActive ha active) hlocal
  have hsGlobal :
      IsRelFullyPaired (appendPairingTo ha σ τ) active
        (Fin.castLE ha s.1) (Fin.castLE ha s.2) :=
    (isRelFullyPaired_append_prefix_iff
      ha σ τ active s.1 s.2).mpr hs
  have hglobalCardLe := selectRel_card_le h hsGlobal
  rw [hpref] at hglobalCardLe
  simp only [eaPrefixPair] at hglobalCardLe
  rw [card_relIcc_prefix, card_relIcc_prefix] at hglobalCardLe
  have hlocalCardLe := selectRel_card_le hlocal hlr
  have hcard :
      (relIcc (eaPrefixActive ha active) s.1 s.2).card =
        (relIcc (eaPrefixActive ha active) l r).card :=
    le_antisymm hlocalCardLe hglobalCardLe
  have hglobalCard :
      (relIcc active
          (selectRel (appendPairingTo ha σ τ) active h).1
          (selectRel (appendPairingTo ha σ τ) active h).2).card =
        (relIcc active (Fin.castLE ha s.1)
          (Fin.castLE ha s.2)).card := by
    rw [hpref]
    simp only [eaPrefixPair]
    rw [card_relIcc_prefix, card_relIcc_prefix]
    exact hcard.symm
  have hprefixFst :=
    selectRel_fst_le h hsGlobal hglobalCard
  have hlocalFst :=
    selectRel_fst_le hlocal hlr hcard
  have hls : l ≤ s.1 := by
    rw [hpref] at hprefixFst
    exact hprefixFst
  have hsl : s.1 ≤ l := hlocalFst
  have hfst : s.1 = l := le_antisymm hsl hls
  have hglobalFst :
      (selectRel (appendPairingTo ha σ τ) active h).1 =
        Fin.castLE ha s.1 := by
    rw [hpref]
    simp only [eaPrefixPair]
    exact congrArg (Fin.castLE ha) hfst.symm
  have hprefixSnd :=
    selectRel_snd_le h hsGlobal hglobalCard hglobalFst
  have hlocalSnd :=
    selectRel_snd_le hlocal hlr hcard hfst
  have hrs : r ≤ s.2 := by
    rw [hpref] at hprefixSnd
    exact hprefixSnd
  have hsr : s.2 ≤ r := hlocalSnd
  have hsnd : s.2 = r := le_antisymm hsr hrs
  change
    selectRel (appendPairingTo ha σ τ) active h =
      eaPrefixPair ha s
  rw [hpref]
  simp only [eaPrefixPair]
  exact Prod.ext
    (congrArg (Fin.castLE ha) hfst.symm)
    (congrArg (Fin.castLE ha) hsnd.symm)

/-- Suffix analogue of `selectRel_appendPairingTo_eq_prefix`. -/
theorem selectRel_appendPairingTo_eq_suffix
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (active : Finset (Fin N))
    (h : ∃ l r,
      IsRelFullyPaired (appendPairingTo ha σ τ) active l r)
    (l r : Fin (N - a))
    (hsuff :
      selectRel (appendPairingTo ha σ τ) active h =
        eaSuffixPair ha (l, r)) :
    let hlocal : ∃ i j,
        IsRelFullyPaired τ (eaSuffixActive ha active) i j := by
      refine ⟨l, r, ?_⟩
      have hg :=
        selectRel_isRelFullyPaired
          (appendPairingTo ha σ τ) active h
      rw [hsuff] at hg
      change
        IsRelFullyPaired (appendPairingTo ha σ τ) active
          (suffixFin ha l) (suffixFin ha r) at hg
      exact (isRelFullyPaired_append_suffix_iff
        ha σ τ active l r).mp hg
    selectRel (appendPairingTo ha σ τ) active h =
      eaSuffixPair ha
        (selectRel τ (eaSuffixActive ha active) hlocal) := by
  have hlr : IsRelFullyPaired τ
      (eaSuffixActive ha active) l r := by
    have hg :=
      selectRel_isRelFullyPaired
        (appendPairingTo ha σ τ) active h
    rw [hsuff] at hg
    change
      IsRelFullyPaired (appendPairingTo ha σ τ) active
        (suffixFin ha l) (suffixFin ha r) at hg
    exact (isRelFullyPaired_append_suffix_iff
      ha σ τ active l r).mp hg
  let hlocal : ∃ i j,
      IsRelFullyPaired τ (eaSuffixActive ha active) i j :=
    ⟨l, r, hlr⟩
  let s := selectRel τ (eaSuffixActive ha active) hlocal
  have hs :=
    selectRel_isRelFullyPaired τ (eaSuffixActive ha active) hlocal
  have hsGlobal :
      IsRelFullyPaired (appendPairingTo ha σ τ) active
        (suffixFin ha s.1) (suffixFin ha s.2) :=
    (isRelFullyPaired_append_suffix_iff
      ha σ τ active s.1 s.2).mpr hs
  have hglobalCardLe := selectRel_card_le h hsGlobal
  rw [hsuff] at hglobalCardLe
  simp only [eaSuffixPair] at hglobalCardLe
  rw [card_relIcc_suffix, card_relIcc_suffix] at hglobalCardLe
  have hlocalCardLe := selectRel_card_le hlocal hlr
  have hcard :
      (relIcc (eaSuffixActive ha active) s.1 s.2).card =
        (relIcc (eaSuffixActive ha active) l r).card :=
    le_antisymm hlocalCardLe hglobalCardLe
  have hglobalCard :
      (relIcc active
          (selectRel (appendPairingTo ha σ τ) active h).1
          (selectRel (appendPairingTo ha σ τ) active h).2).card =
        (relIcc active (suffixFin ha s.1)
          (suffixFin ha s.2)).card := by
    rw [hsuff]
    simp only [eaSuffixPair]
    rw [card_relIcc_suffix, card_relIcc_suffix]
    exact hcard.symm
  have hsuffixFst :=
    selectRel_fst_le h hsGlobal hglobalCard
  have hlocalFst :=
    selectRel_fst_le hlocal hlr hcard
  have hls : l ≤ s.1 := by
    rw [hsuff] at hsuffixFst
    change a + l.val ≤ a + s.1.val at hsuffixFst
    exact Fin.le_def.mpr (by omega)
  have hsl : s.1 ≤ l := hlocalFst
  have hfst : s.1 = l := le_antisymm hsl hls
  have hglobalFst :
      (selectRel (appendPairingTo ha σ τ) active h).1 =
        suffixFin ha s.1 := by
    rw [hsuff]
    simp only [eaSuffixPair]
    exact congrArg (suffixFin ha) hfst.symm
  have hsuffixSnd :=
    selectRel_snd_le h hsGlobal hglobalCard hglobalFst
  have hlocalSnd :=
    selectRel_snd_le hlocal hlr hcard hfst
  have hrs : r ≤ s.2 := by
    rw [hsuff] at hsuffixSnd
    change a + r.val ≤ a + s.2.val at hsuffixSnd
    exact Fin.le_def.mpr (by omega)
  have hsr : s.2 ≤ r := hlocalSnd
  have hsnd : s.2 = r := le_antisymm hsr hrs
  change
    selectRel (appendPairingTo ha σ τ) active h =
      eaSuffixPair ha s
  rw [hsuff]
  simp only [eaSuffixPair]
  exact Prod.ext
    (congrArg (suffixFin ha) hfst.symm)
    (congrArg (suffixFin ha) hsnd.symm)

/-- Stateful/fuel form of extraction compatibility.  The global fuel is
split between the two projected active blocks; the cardinality bounds are
exactly what guarantees that a block with a candidate still has positive
fuel. -/
theorem extractAux_appendPairingTo_perm_state
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (fuel : ℕ) :
    ∀ (fa fb : ℕ) (active : Finset (Fin N)),
      fa + fb = fuel →
      (eaPrefixActive ha active).card ≤ 2 * fa + 1 →
      (eaSuffixActive ha active).card ≤ 2 * fb + 1 →
      (extractAux (appendPairingTo ha σ τ) fuel active).Perm
        ((extractAux σ fa (eaPrefixActive ha active)).map
            (eaPrefixPair ha) ++
          (extractAux τ fb (eaSuffixActive ha active)).map
            (eaSuffixPair ha)) := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro fa fb active hsum hfa hfb
      subst fuel
      let K := appendPairingTo ha σ τ
      let A := eaPrefixActive ha active
      let B := eaSuffixActive ha active
      by_cases hg : ∃ l r, IsRelFullyPaired K active l r
      · rcases selectRel_appendPairingTo_either
          ha σ τ active hg with hpref | hsuff
        · obtain ⟨l, r, hpref⟩ := hpref
          have hlr : IsRelFullyPaired σ A l r := by
            have hsel :=
              selectRel_isRelFullyPaired K active hg
            rw [hpref] at hsel
            change IsRelFullyPaired K active
              (Fin.castLE ha l) (Fin.castLE ha r) at hsel
            exact (isRelFullyPaired_append_prefix_iff
              ha σ τ active l r).mp hsel
          let hlocal : ∃ i j, IsRelFullyPaired σ A i j :=
            ⟨l, r, hlr⟩
          have hfaPos : 0 < fa := by
            have htwo :=
              (selectRel_isRelFullyPaired σ A hlocal).two_le_card
            have hsub :=
              Finset.card_le_card
                (relIcc_subset_active A
                  (selectRel σ A hlocal).1
                  (selectRel σ A hlocal).2)
            by_contra hzero
            have : fa = 0 := Nat.eq_zero_of_not_pos hzero
            subst fa
            change A.card ≤ 1 at hfa
            omega
          obtain ⟨fa', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt hfaPos)
          have hsel :
              selectRel K active hg =
                eaPrefixPair ha (selectRel σ A hlocal) := by
            have hbridge :=
              selectRel_appendPairingTo_eq_prefix
                ha σ τ active hg l r hpref
            change
              selectRel K active hg =
                eaPrefixPair ha (selectRel σ A hlocal)
            exact hbridge
          let active' :=
            active \
              relIcc active (selectRel K active hg).1
                (selectRel K active hg).2
          have hpre :
              eaPrefixActive ha active' =
                A \
                  relIcc A (selectRel σ A hlocal).1
                    (selectRel σ A hlocal).2 := by
            dsimp only [active']
            rw [hsel]
            change
              eaPrefixActive ha
                  (active \
                    relIcc active
                      (Fin.castLE ha (selectRel σ A hlocal).1)
                      (Fin.castLE ha (selectRel σ A hlocal).2)) =
                _
            rw [eaPrefixActive_sdiff_prefix]
          have hsuf :
              eaSuffixActive ha active' = B := by
            dsimp only [active']
            rw [hsel]
            change
              eaSuffixActive ha
                  (active \
                    relIcc active
                      (Fin.castLE ha (selectRel σ A hlocal).1)
                      (Fin.castLE ha (selectRel σ A hlocal).2)) =
                _
            rw [eaSuffixActive_sdiff_prefix]
          have hfa' :
              (eaPrefixActive ha active').card ≤ 2 * fa' + 1 := by
            rw [hpre]
            have hshrink :=
              card_sdiff_relIcc_add_two_le
                (selectRel_isRelFullyPaired σ A hlocal)
            change A.card ≤ 2 * (fa' + 1) + 1 at hfa
            omega
          have hfb' :
              (eaSuffixActive ha active').card ≤ 2 * fb + 1 := by
            rw [hsuf]
            exact hfb
          have hrec :=
            ih (fa' + fb) (by omega)
              fa' fb active' rfl hfa' hfb'
          rw [hpre, hsuf] at hrec
          have hglobalStep :
              extractAux K (fa' + 1 + fb) active =
                selectRel K active hg ::
                  extractAux K (fa' + fb) active' := by
            rw [show fa' + 1 + fb = (fa' + fb) + 1 by omega]
            exact extractAux_succ_pos (fa' + fb) hg
          have hlocalStep :
              extractAux σ (fa' + 1) A =
                selectRel σ A hlocal ::
                  extractAux σ fa'
                    (A \
                      relIcc A (selectRel σ A hlocal).1
                        (selectRel σ A hlocal).2) :=
            extractAux_succ_pos fa' hlocal
          change
            (extractAux K (fa' + 1 + fb) active).Perm
              ((extractAux σ (fa' + 1) A).map
                  (eaPrefixPair ha) ++
                (extractAux τ fb B).map (eaSuffixPair ha))
          rw [hglobalStep, hlocalStep, List.map_cons, hsel]
          exact hrec.cons _
        · obtain ⟨l, r, hsuff⟩ := hsuff
          have hlr : IsRelFullyPaired τ B l r := by
            have hsel :=
              selectRel_isRelFullyPaired K active hg
            rw [hsuff] at hsel
            change IsRelFullyPaired K active
              (suffixFin ha l) (suffixFin ha r) at hsel
            exact (isRelFullyPaired_append_suffix_iff
              ha σ τ active l r).mp hsel
          let hlocal : ∃ i j, IsRelFullyPaired τ B i j :=
            ⟨l, r, hlr⟩
          have hfbPos : 0 < fb := by
            have htwo :=
              (selectRel_isRelFullyPaired τ B hlocal).two_le_card
            have hsub :=
              Finset.card_le_card
                (relIcc_subset_active B
                  (selectRel τ B hlocal).1
                  (selectRel τ B hlocal).2)
            by_contra hzero
            have : fb = 0 := Nat.eq_zero_of_not_pos hzero
            subst fb
            change B.card ≤ 1 at hfb
            omega
          obtain ⟨fb', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt hfbPos)
          have hsel :
              selectRel K active hg =
                eaSuffixPair ha (selectRel τ B hlocal) := by
            have hbridge :=
              selectRel_appendPairingTo_eq_suffix
                ha σ τ active hg l r hsuff
            change
              selectRel K active hg =
                eaSuffixPair ha (selectRel τ B hlocal)
            exact hbridge
          let active' :=
            active \
              relIcc active (selectRel K active hg).1
                (selectRel K active hg).2
          have hpre :
              eaPrefixActive ha active' = A := by
            dsimp only [active']
            rw [hsel]
            change
              eaPrefixActive ha
                  (active \
                    relIcc active
                      (suffixFin ha (selectRel τ B hlocal).1)
                      (suffixFin ha (selectRel τ B hlocal).2)) =
                _
            rw [eaPrefixActive_sdiff_suffix]
          have hsuf :
              eaSuffixActive ha active' =
                B \
                  relIcc B (selectRel τ B hlocal).1
                    (selectRel τ B hlocal).2 := by
            dsimp only [active']
            rw [hsel]
            change
              eaSuffixActive ha
                  (active \
                    relIcc active
                      (suffixFin ha (selectRel τ B hlocal).1)
                      (suffixFin ha (selectRel τ B hlocal).2)) =
                _
            rw [eaSuffixActive_sdiff_suffix]
          have hfa' :
              (eaPrefixActive ha active').card ≤ 2 * fa + 1 := by
            rw [hpre]
            exact hfa
          have hfb' :
              (eaSuffixActive ha active').card ≤ 2 * fb' + 1 := by
            rw [hsuf]
            have hshrink :=
              card_sdiff_relIcc_add_two_le
                (selectRel_isRelFullyPaired τ B hlocal)
            change B.card ≤ 2 * (fb' + 1) + 1 at hfb
            omega
          have hrec :=
            ih (fa + fb') (by omega)
              fa fb' active' rfl hfa' hfb'
          rw [hpre, hsuf] at hrec
          have hglobalStep :
              extractAux K (fa + (fb' + 1)) active =
                selectRel K active hg ::
                  extractAux K (fa + fb') active' := by
            rw [show fa + (fb' + 1) = (fa + fb') + 1 by omega]
            exact extractAux_succ_pos (fa + fb') hg
          have hlocalStep :
              extractAux τ (fb' + 1) B =
                selectRel τ B hlocal ::
                  extractAux τ fb'
                    (B \
                      relIcc B (selectRel τ B hlocal).1
                        (selectRel τ B hlocal).2) :=
            extractAux_succ_pos fb' hlocal
          change
            (extractAux K (fa + (fb' + 1)) active).Perm
              ((extractAux σ fa A).map (eaPrefixPair ha) ++
                (extractAux τ (fb' + 1) B).map
                  (eaSuffixPair ha))
          rw [hglobalStep, hlocalStep, List.map_cons, hsel]
          exact (hrec.cons _).trans List.perm_middle.symm
      · have hpreNone :
            ¬∃ l r, IsRelFullyPaired σ A l r := by
          rintro ⟨l, r, hlr⟩
          exact hg ⟨Fin.castLE ha l, Fin.castLE ha r,
            (isRelFullyPaired_append_prefix_iff
              ha σ τ active l r).mpr hlr⟩
        have hsufNone :
            ¬∃ l r, IsRelFullyPaired τ B l r := by
          rintro ⟨l, r, hlr⟩
          exact hg ⟨suffixFin ha l, suffixFin ha r,
            (isRelFullyPaired_append_suffix_iff
              ha σ τ active l r).mpr hlr⟩
        change
          (extractAux K (fa + fb) active).Perm
            ((extractAux σ fa A).map (eaPrefixPair ha) ++
              (extractAux τ fb B).map (eaSuffixPair ha))
        rw [extractAux_nil_of_no_candidate _ hg,
          extractAux_nil_of_no_candidate _ hpreNone,
          extractAux_nil_of_no_candidate _ hsufNone]
        exact List.Perm.refl []

/-- Extraction of a consecutive block sum is the shuffle of the two local
extractions.  No non-split hypothesis is needed. -/
theorem extract_appendPairingTo_perm
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a))) :
    (extract (appendPairingTo ha σ τ)).Perm
      ((extract σ).map (eaPrefixPair ha) ++
        (extract τ).map (eaSuffixPair ha)) := by
  unfold extract
  have hstate :=
    extractAux_appendPairingTo_perm_state
      ha σ τ N a (N - a) Finset.univ (by omega)
      (by
        simp [eaPrefixActive]
        omega)
      (by
        simp [eaSuffixActive]
        omega)
  simpa [eaPrefixActive, eaSuffixActive] using hstate

/-! ## Closed-form component bookkeeping -/

/-- Right chain-edge numbers extracted from an appended pairing split
into the corresponding prefix and suffix numbers. -/
theorem extractedRightValues_appendPairingTo_perm
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a))) :
    ((extract (appendPairingTo ha σ τ)).map
        (fun p => p.2.val + 1)).Perm
      (((extract σ).map (fun p => p.2.val + 1)) ++
        (extract τ).map (fun p => a + p.2.val + 1)) := by
  have h :=
    (extract_appendPairingTo_perm ha σ τ).map
      (fun p => p.2.val + 1)
  simpa [eaPrefixPair, eaSuffixPair, suffixFin,
    Function.comp_def] using h

/-- The prefix variables of an ambient deterministic tuple, with the
external left slot omitted. -/
def ambientPrefixTuple {N a : ℕ} (ha : a ≤ N)
    (xt : Fin (N + 2) → T4) : Fin a → T4 :=
  fun i => xt (varIdx (Fin.castLE ha i))

/-- The tail tuple starts at the last prefix variable: its slot `0` is
ambient slot `a`, its internal variables are the ambient suffix, and its
last slot is the ambient right endpoint. -/
def ambientTailTuple {N a : ℕ} (ha : a ≤ N)
    (xt : Fin (N + 2) → T4) : Fin (N - a + 2) → T4 :=
  fun j => xt ⟨a + j.val, by omega⟩

/-- The endpoints of the whole nonempty prefix. -/
def wholePrefixPair {a : ℕ} (ha0 : 0 < a) : Fin a × Fin a :=
  (⟨0, ha0⟩, ⟨a - 1, by omega⟩)

@[simp]
theorem ambientTailTuple_varIdx
    {N a : ℕ} (ha : a ≤ N)
    (xt : Fin (N + 2) → T4) (j : Fin (N - a)) :
    ambientTailTuple ha xt (varIdx j) =
      xt (varIdx (suffixFin ha j)) := by
  unfold ambientTailTuple
  apply congrArg xt
  apply Fin.ext
  rfl

@[simp]
theorem ambientTailTuple_after_internal
    {N a : ℕ} (ha : a ≤ N)
    (xt : Fin (N + 2) → T4) (j : Fin (N - a)) :
    ambientTailTuple ha xt
        ⟨j.val + 2, by omega⟩ =
      xt ⟨(suffixFin ha j).val + 2, by omega⟩ := by
  unfold ambientTailTuple
  apply congrArg xt
  apply Fin.ext
  simp only [suffixFin_val]
  omega

@[simp]
theorem ambientPrefixTuple_apply
    {N a : ℕ} (ha : a ≤ N)
    (xt : Fin (N + 2) → T4) (i : Fin a) :
    ambientPrefixTuple ha xt i =
      xt (varIdx (Fin.castLE ha i)) :=
  rfl

/-- The covariance part of the ambient closed form is the product of its
prefix and tail covariance parts. -/
theorem covarianceProduct_appendPairingTo
    (ρ : SmoothCutoff) (ε : ℝ)
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (xt : Fin (N + 2) → T4) :
    (∏ k ∈
        (appendPairingTo ha σ τ).pairSupport.filter
          (fun k => k < appendPairingTo ha σ τ k),
        ρ.etaEpsT4 ε
          (xt (varIdx k) -
            xt (varIdx (appendPairingTo ha σ τ k)))) =
      (∏ i ∈ σ.pairSupport.filter (fun i => i < σ i),
          ρ.etaEpsT4 ε
            (ambientPrefixTuple ha xt i -
              ambientPrefixTuple ha xt (σ i))) *
        ∏ j ∈ τ.pairSupport.filter (fun j => j < τ j),
          ρ.etaEpsT4 ε
            (ambientTailTuple ha xt (varIdx j) -
              ambientTailTuple ha xt (varIdx (τ j))) := by
  simpa only [ambientPrefixTuple_apply,
    ambientTailTuple_varIdx] using
    (prod_orientedPairSupport_appendPairingTo
      ha σ τ
      (fun i j : Fin N =>
        ρ.etaEpsT4 ε
          (xt (varIdx i) - xt (varIdx j))))

/-- The Wick factor of an appended pairing is carried entirely by the
tail whenever the prefix is full. -/
theorem wickAt_appendPairingTo_ambientTuple
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (hσ : σ.IsFull)
    (xt : Fin (N + 2) → T4) (ω : M.Ω) :
    wickAt M ρ ε (appendPairingTo ha σ τ) xt ω =
      wickAt M ρ ε τ (ambientTailTuple ha xt) ω := by
  apply wickAt_appendPairingTo
    M ρ ε ha σ τ hσ xt (ambientTailTuple ha xt)
  intro j
  exact (ambientTailTuple_varIdx ha xt j).symm

/-- Difference factors of a suffix extraction are exactly the tail
`detIntegrand` difference factors. -/
theorem diffFactor_eaSuffixPair
    {N a : ℕ} (ha : a ≤ N)
    (xt : Fin (N + 2) → T4)
    (p : Fin (N - a) × Fin (N - a)) :
    diffFactor xt (eaSuffixPair ha p) =
      diffFactor (ambientTailTuple ha xt) p := by
  unfold diffFactor eaSuffixPair
  simp only [ambientTailTuple_varIdx,
    ambientTailTuple_after_internal]

/-- Before the last prefix coordinate, ambient prefix differences are
the `J`-integrand differences. -/
theorem diffFactor_eaPrefixPair
    {N a : ℕ} (ha : a ≤ N)
    (xt : Fin (N + 2) → T4)
    (p : Fin a × Fin a)
    (hp : p.2.val + 1 < a) :
    diffFactor xt (eaPrefixPair ha p) =
      diffFactorJ (ambientPrefixTuple ha xt) p := by
  unfold diffFactorJ
  rw [dif_pos hp]
  unfold diffFactor eaPrefixPair
  simp only [ambientPrefixTuple_apply]
  apply congrArg₂ (· - ·)
  · apply congrArg greenFn
    apply congrArg₂ (· - ·)
    · rfl
    · apply congrArg xt
      apply Fin.ext
      rfl
  · apply congrArg greenFn
    apply congrArg₂ (· - ·)
    · rfl
    · apply congrArg xt
      apply Fin.ext
      rfl

/-- The ambient difference-factor list is the product of the prefix
factors and the tail factors. -/
theorem differenceProduct_appendPairingTo
    {N a : ℕ} (ha : a ≤ N)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (xt : Fin (N + 2) → T4) :
    ((extract (appendPairingTo ha σ τ)).map
        (diffFactor xt)).prod =
      ((extract σ).map
          (fun p => diffFactor xt (eaPrefixPair ha p))).prod *
        ((extract τ).map
          (diffFactor (ambientTailTuple ha xt))).prod := by
  have h :=
    (extract_appendPairingTo_perm ha σ τ).map
      (diffFactor xt)
  rw [h.prod_eq]
  simp only [List.map_append, List.prod_append,
    List.map_map]
  apply congrArg₂ (· * ·)
  · rfl
  · apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    exact diffFactor_eaSuffixPair ha xt p

/-- The whole-prefix extraction supplies the boundary Green
difference between the last prefix point and the first prefix point. -/
theorem diffFactor_eaPrefixPair_whole
    {N a : ℕ} (ha : a ≤ N) (ha0 : 0 < a)
    (xt : Fin (N + 2) → T4) :
    diffFactor xt
        (eaPrefixPair ha (wholePrefixPair ha0)) =
      greenFn
          (ambientTailTuple ha xt 0 -
            ambientTailTuple ha xt 1) -
        greenFn
          (ambientPrefixTuple ha xt ⟨0, ha0⟩ -
            ambientTailTuple ha xt 1) := by
  unfold diffFactor eaPrefixPair wholePrefixPair
  unfold ambientTailTuple ambientPrefixTuple
  apply congrArg₂ (· - ·)
  · apply congrArg greenFn
    apply congrArg₂ (· - ·)
    · apply congrArg xt
      apply Fin.ext
      change a - 1 + 1 = a + 0
      omega
    · apply congrArg xt
      apply Fin.ext
      change a - 1 + 2 = a + 1
      omega
  · apply congrArg greenFn
    apply congrArg₂ (· - ·)
    · apply congrArg xt
      apply Fin.ext
      rfl
    ·
      apply congrArg xt
      apply Fin.ext
      change a - 1 + 2 = a + 1
      omega

@[simp]
theorem diffFactorJ_wholePrefixPair
    {a : ℕ} (ha0 : 0 < a) (xt : Fin a → T4) :
    diffFactorJ xt (wholePrefixPair ha0) = 1 := by
  unfold diffFactorJ
  change
    (if h : a - 1 + 1 < a then
      greenFn
          (xt (wholePrefixPair ha0).2 -
            xt ⟨a - 1 + 1, h⟩) -
        greenFn
          (xt (wholePrefixPair ha0).1 -
            xt ⟨a - 1 + 1, h⟩)
    else 1) = 1
  rw [dif_neg]
  omega

/-- If the whole prefix is the final extraction, its ambient difference
product is the internal `J` difference product followed by the one
boundary Green difference. -/
theorem prefixDifferenceProduct_eq_detJ_mul_boundary
    {N a : ℕ} (ha : a ≤ N) (ha0 : 0 < a)
    (σ : PartialPairing (Fin a))
    (xt : Fin (N + 2) → T4)
    (proper : List (Fin a × Fin a))
    (hextract :
      (extract σ).Perm
        (proper ++ [wholePrefixPair ha0]))
    (hproper : ∀ p ∈ proper, p.2.val + 1 < a) :
    ((extract σ).map
        (fun p => diffFactor xt (eaPrefixPair ha p))).prod =
      ((extract σ).map
          (diffFactorJ (ambientPrefixTuple ha xt))).prod *
        (greenFn
            (ambientTailTuple ha xt 0 -
              ambientTailTuple ha xt 1) -
          greenFn
            (ambientPrefixTuple ha xt ⟨0, ha0⟩ -
              ambientTailTuple ha xt 1)) := by
  have hamb :=
    (hextract.map
      (fun p => diffFactor xt (eaPrefixPair ha p))).prod_eq
  have hJ :=
    (hextract.map
      (diffFactorJ (ambientPrefixTuple ha xt))).prod_eq
  rw [hamb, hJ]
  simp only [List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton]
  have hproperProd :
      (proper.map
          (fun p => diffFactor xt (eaPrefixPair ha p))).prod =
        (proper.map
          (diffFactorJ (ambientPrefixTuple ha xt))).prod := by
    apply congrArg List.prod
    apply List.map_congr_left
    intro p hp
    exact diffFactor_eaPrefixPair ha xt p (hproper p hp)
  rw [hproperProd, diffFactor_eaPrefixPair_whole,
    diffFactorJ_wholePrefixPair]
  ring

/-! ### Isolating the first tail edge -/

/-- All deterministic factors of `detIntegrand` except its first chain
edge.  Extracted edges are always numbered `r+1`, so edge zero is never
removed. -/
def detIntegrandAfterFirst
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) : ℝ :=
  (∏ e : Fin m,
      if e.succ.val ∈
          ((extract κ).map fun p => p.2.val + 1) then 1
      else greenFn
        (xt e.succ.castSucc - xt e.succ.succ)) *
    ((extract κ).map (diffFactor xt)).prod *
    ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
      ρ.etaEpsT4 ε
        (xt (varIdx i) - xt (varIdx (κ i)))

/-- `detIntegrand` is its unavoidable first Green edge times the
remaining deterministic factors. -/
theorem detIntegrand_eq_first_mul_afterFirst
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) :
    detIntegrand ρ ε m κ xt =
      greenFn (xt 0 - xt 1) *
        detIntegrandAfterFirst ρ ε m κ xt := by
  unfold detIntegrand detIntegrandAfterFirst
  rw [Fin.prod_univ_succ]
  have hzero :
      ¬(0 : ℕ) ∈
        (extract κ).map (fun p => p.2.val + 1) := by
    intro h
    obtain ⟨p, -, hp⟩ := List.mem_map.mp h
    omega
  simp only [Fin.val_zero, if_neg hzero]
  change
    (greenFn (xt 0 - xt 1) * _) * _ * _ =
      greenFn (xt 0 - xt 1) * (_ * _ * _)
  ring

/-- Change only slot zero of a tuple. -/
def setTupleFirst {m : ℕ} (z : T4)
    (xt : Fin (m + 2) → T4) : Fin (m + 2) → T4 :=
  fun j => if j.val = 0 then z else xt j

@[simp]
theorem setTupleFirst_zero
    {m : ℕ} (z : T4) (xt : Fin (m + 2) → T4) :
    setTupleFirst z xt 0 = z := by
  simp [setTupleFirst]

@[simp]
theorem setTupleFirst_of_ne_zero
    {m : ℕ} (z : T4) (xt : Fin (m + 2) → T4)
    (j : Fin (m + 2)) (hj : j.val ≠ 0) :
    setTupleFirst z xt j = xt j := by
  simp [setTupleFirst, hj]

@[simp]
theorem setTupleFirst_varIdx
    {m : ℕ} (z : T4) (xt : Fin (m + 2) → T4)
    (i : Fin m) :
    setTupleFirst z xt (varIdx i) =
      xt (varIdx i) := by
  apply setTupleFirst_of_ne_zero
  simp only [varIdx_val]
  omega

@[simp]
theorem setTupleFirst_after_internal
    {m : ℕ} (z : T4) (xt : Fin (m + 2) → T4)
    (i : Fin m) :
    setTupleFirst z xt
        ⟨i.val + 2, by omega⟩ =
      xt ⟨i.val + 2, by omega⟩ := by
  simp [setTupleFirst]

/-- None of the factors after the first chain edge sees tuple slot zero. -/
theorem detIntegrandAfterFirst_setTupleFirst
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m))
    (z : T4) (xt : Fin (m + 2) → T4) :
    detIntegrandAfterFirst ρ ε m κ
        (setTupleFirst z xt) =
      detIntegrandAfterFirst ρ ε m κ xt := by
  unfold detIntegrandAfterFirst
  apply congrArg₂ (· * ·)
  · apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro e he
      split_ifs
      · rfl
      · congr 2
    · apply congrArg List.prod
      apply List.map_congr_left
      intro p hp
      unfold diffFactor
      simp only [setTupleFirst_varIdx,
        setTupleFirst_after_internal]
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [setTupleFirst_varIdx]

/-- `wickAt` depends only on internal-variable slots. -/
theorem wickAt_setTupleFirst
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {m : ℕ} (κ : PartialPairing (Fin m))
    (z : T4) (xt : Fin (m + 2) → T4)
    (ω : M.Ω) :
    wickAt M ρ ε κ (setTupleFirst z xt) ω =
      wickAt M ρ ε κ xt ω := by
  unfold wickAt
  apply Fintype.sum_congr
  intro κ'
  simp only [setTupleFirst_varIdx]

/-- The random integrand also has an explicit unavoidable first edge. -/
theorem randIntegrand_eq_first_mul_afterFirst
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {m : ℕ} (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) (ω : M.Ω) :
    randIntegrand M ρ ε κ xt ω =
      greenFn (xt 0 - xt 1) *
        (detIntegrandAfterFirst ρ ε m κ xt *
          wickAt M ρ ε κ xt ω) := by
  unfold randIntegrand
  rw [detIntegrand_eq_first_mul_afterFirst]
  ring

/-- Replacing the left endpoint turns subtraction of random integrands
into exactly one Green-kernel difference. -/
theorem randIntegrand_sub_setTupleFirst
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {m : ℕ} (κ : PartialPairing (Fin m))
    (z : T4) (xt : Fin (m + 2) → T4)
    (ω : M.Ω) :
    randIntegrand M ρ ε κ xt ω -
        randIntegrand M ρ ε κ
          (setTupleFirst z xt) ω =
      (greenFn (xt 0 - xt 1) -
          greenFn (z - xt 1)) *
        (detIntegrandAfterFirst ρ ε m κ xt *
          wickAt M ρ ε κ xt ω) := by
  rw [randIntegrand_eq_first_mul_afterFirst,
    randIntegrand_eq_first_mul_afterFirst,
    setTupleFirst_zero,
    setTupleFirst_of_ne_zero,
    detIntegrandAfterFirst_setTupleFirst,
    wickAt_setTupleFirst]
  · ring
  · norm_num

@[simp]
theorem hd_wickHeadEquiv_contraction_zero
    {n : ℕ} (d : MarkedSingle (Fin n)) :
    wickHeadEquiv n (Sum.inr d) 0 = d.index.succ := by
  unfold wickHeadEquiv finHeadEquiv
  simp [optionHeadEquiv, optionHeadAssemble, markedSingleEquiv]
  change
    PartialPairing.congr (finSuccEquiv n).symm
      (optionPaired d.index
        (eraseSingle d.pairing d.index
          (mem_singles.mp d.isSingle))) 0 = d.index.succ
  rw [PartialPairing.congr_apply_apply]
  simp

@[simp]
theorem hd_wickHeadEquiv_contraction_partner
    {n : ℕ} (d : MarkedSingle (Fin n)) :
    wickHeadEquiv n (Sum.inr d) d.index.succ = 0 := by
  unfold wickHeadEquiv finHeadEquiv
  simp [optionHeadEquiv, optionHeadAssemble, markedSingleEquiv]
  change
    PartialPairing.congr (finSuccEquiv n).symm
      (optionPaired d.index
        (eraseSingle d.pairing d.index
          (mem_singles.mp d.isSingle))) d.index.succ = 0
  rw [PartialPairing.congr_apply_apply]
  simp

@[simp]
theorem hd_wickHeadEquiv_contraction_succ_ne
    {n : ℕ} (d : MarkedSingle (Fin n))
    (i : Fin n) (hi : i ≠ d.index) :
    wickHeadEquiv n (Sum.inr d) i.succ =
      (d.pairing i).succ := by
  unfold wickHeadEquiv finHeadEquiv
  simp [optionHeadEquiv, optionHeadAssemble, markedSingleEquiv]
  change
    PartialPairing.congr (finSuccEquiv n).symm
      (optionPaired d.index
        (eraseSingle d.pairing d.index
          (mem_singles.mp d.isSingle))) i.succ =
        (d.pairing i).succ
  rw [PartialPairing.congr_apply_apply]
  simp only [Equiv.symm_symm, finSuccEquiv_succ]
  rw [optionPaired_some_ne d.index
    (eraseSingle d.pairing d.index
      (mem_singles.mp d.isSingle)) i hi]
  rw [eraseSingle_apply_val, finSuccEquiv_symm_some]

/-- Pairing obtained by deleting a paired head and restoring its partner as
a single. -/
def headDeletionData {n : ℕ}
    (κ : PartialPairing (Fin (n + 1))) (hκ : κ 0 ≠ 0) :
    MarkedSingle (Fin n) :=
  (contractionHeadEquiv n).symm ⟨κ, hκ⟩

@[simp]
theorem contractionHeadEquiv_headDeletionData
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0) :
    (contractionHeadEquiv n (headDeletionData κ hκ)).1 = κ := by
  exact congrArg Subtype.val
    ((contractionHeadEquiv n).apply_symm_apply ⟨κ, hκ⟩)

theorem headDeletionData_zero
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0) :
    κ 0 = (headDeletionData κ hκ).index.succ := by
  let d := headDeletionData κ hκ
  have heq : (contractionHeadEquiv n d).1 = κ :=
    contractionHeadEquiv_headDeletionData κ hκ
  calc
    κ 0 = (contractionHeadEquiv n d).1 0 :=
      congrArg (fun ν : PartialPairing (Fin (n + 1)) => ν 0) heq.symm
    _ = d.index.succ :=
      hd_wickHeadEquiv_contraction_zero d

theorem headDeletionData_partner
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0) :
    κ (headDeletionData κ hκ).index.succ = 0 := by
  let d := headDeletionData κ hκ
  have heq : (contractionHeadEquiv n d).1 = κ :=
    contractionHeadEquiv_headDeletionData κ hκ
  calc
    κ d.index.succ =
        (contractionHeadEquiv n d).1 d.index.succ :=
      congrArg
        (fun ν : PartialPairing (Fin (n + 1)) => ν d.index.succ)
        heq.symm
    _ = 0 := hd_wickHeadEquiv_contraction_partner d

theorem headDeletionData_succ_ne
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0)
    (i : Fin n) (hi : i ≠ (headDeletionData κ hκ).index) :
    κ i.succ = ((headDeletionData κ hκ).pairing i).succ := by
  let d := headDeletionData κ hκ
  have heq : (contractionHeadEquiv n d).1 = κ :=
    contractionHeadEquiv_headDeletionData κ hκ
  calc
    κ i.succ = (contractionHeadEquiv n d).1 i.succ :=
      congrArg
        (fun ν : PartialPairing (Fin (n + 1)) => ν i.succ)
        heq.symm
    _ = (d.pairing i).succ :=
      hd_wickHeadEquiv_contraction_succ_ne d i hi

/-! ## The successor copy of the head-deleted active state -/

def hdSuccEmbedding {n : ℕ} : Fin n ↪ Fin (n + 1) where
  toFun := Fin.succ
  inj' := Fin.succ_injective n

def hdSuccPair {n : ℕ}
    (p : Fin n × Fin n) : Fin (n + 1) × Fin (n + 1) :=
  (p.1.succ, p.2.succ)

def hdTailActive {n : ℕ}
    (active : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.succ ∈ active

def hdGlobalActive {n : ℕ}
    (active : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  insert 0 (active.map hdSuccEmbedding)

@[simp]
theorem mem_hdTailActive {n : ℕ}
    {active : Finset (Fin (n + 1))} {i : Fin n} :
    i ∈ hdTailActive active ↔ i.succ ∈ active := by
  simp [hdTailActive]

@[simp]
theorem mem_hdGlobalActive_zero {n : ℕ}
    (active : Finset (Fin n)) :
    (0 : Fin (n + 1)) ∈ hdGlobalActive active := by
  simp [hdGlobalActive]

@[simp]
theorem mem_hdGlobalActive_succ {n : ℕ}
    {active : Finset (Fin n)} {i : Fin n} :
    i.succ ∈ hdGlobalActive active ↔ i ∈ active := by
  simp [hdGlobalActive, hdSuccEmbedding, Fin.succ_ne_zero]

@[simp]
theorem hdTailActive_hdGlobalActive {n : ℕ}
    (active : Finset (Fin n)) :
    hdTailActive (hdGlobalActive active) = active := by
  ext i
  simp

theorem hdGlobalActive_univ {n : ℕ} :
    hdGlobalActive (Finset.univ : Finset (Fin n)) =
      (Finset.univ : Finset (Fin (n + 1))) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

@[simp]
theorem mem_relIcc_hd_succ_iff
    {n : ℕ} {active : Finset (Fin n)}
    (l r i : Fin n) :
    i.succ ∈
        relIcc (hdGlobalActive active) l.succ r.succ ↔
      i ∈ relIcc active l r := by
  simp only [mem_relIcc, mem_hdGlobalActive_succ]
  exact and_congr_right fun _ =>
    and_congr Fin.succ_le_succ_iff Fin.succ_le_succ_iff

theorem relIcc_hd_succ_eq_map
    {n : ℕ} (active : Finset (Fin n))
    (l r : Fin n) :
    relIcc (hdGlobalActive active) l.succ r.succ =
      (relIcc active l r).map hdSuccEmbedding := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [mem_relIcc, hdGlobalActive, hdSuccEmbedding,
      Fin.succ_ne_zero]
  · simp only [mem_relIcc_hd_succ_iff, Finset.mem_map]
    constructor
    · intro hj
      exact ⟨j, hj, rfl⟩
    · rintro ⟨k, hk, hkj⟩
      have : k = j := hdSuccEmbedding.injective hkj
      simpa only [this] using hk

theorem card_relIcc_hd_succ
    {n : ℕ} (active : Finset (Fin n))
    (l r : Fin n) :
    (relIcc (hdGlobalActive active) l.succ r.succ).card =
      (relIcc active l r).card := by
  rw [relIcc_hd_succ_eq_map, Finset.card_map]

theorem hdGlobalActive_sdiff_succ
    {n : ℕ} (active : Finset (Fin n))
    (l r : Fin n) :
    hdGlobalActive active \
        relIcc (hdGlobalActive active) l.succ r.succ =
      hdGlobalActive (active \ relIcc active l r) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [mem_relIcc]
  · simp only [Finset.mem_sdiff, mem_hdGlobalActive_succ,
      mem_relIcc_hd_succ_iff]

/-! ## Proper candidates agree under head deletion -/

theorem isRelFullyPaired_headDeletion_succ_iff
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0)
    (active : Finset (Fin n)) (l r : Fin n) :
    IsRelFullyPaired κ (hdGlobalActive active) l.succ r.succ ↔
      IsRelFullyPaired (headDeletionData κ hκ).pairing active l r := by
  let d := headDeletionData κ hκ
  rw [IsRelFullyPaired, IsRelFullyPaired]
  constructor
  · rintro ⟨hl, hr, hlr, hfull⟩
    refine ⟨(mem_hdGlobalActive_succ.mp hl),
      (mem_hdGlobalActive_succ.mp hr),
      Fin.succ_le_succ_iff.mp hlr, ?_⟩
    constructor
    · intro i hi hfix
      have hgi :
          i.succ ∈ relIcc (hdGlobalActive active) l.succ r.succ :=
        (mem_relIcc_hd_succ_iff l r i).mpr hi
      have hine : i ≠ d.index := by
        intro hieq
        subst i
        have hout := hfull.apply_mem hgi
        rw [headDeletionData_partner κ hκ] at hout
        have hz :
            (0 : Fin (n + 1)) ∉
              relIcc (hdGlobalActive active) l.succ r.succ := by
          simp [mem_relIcc]
        exact hz hout
      apply hfull.ne_of_mem hgi
      rw [headDeletionData_succ_ne κ hκ i hine, hfix]
    · intro i hi
      have hgi :
          i.succ ∈ relIcc (hdGlobalActive active) l.succ r.succ :=
        (mem_relIcc_hd_succ_iff l r i).mpr hi
      have hine : i ≠ d.index := by
        intro hieq
        subst i
        have hout := hfull.apply_mem hgi
        rw [headDeletionData_partner κ hκ] at hout
        have hz :
            (0 : Fin (n + 1)) ∉
              relIcc (hdGlobalActive active) l.succ r.succ := by
          simp [mem_relIcc]
        exact hz hout
      have hout := hfull.apply_mem hgi
      rw [headDeletionData_succ_ne κ hκ i hine] at hout
      exact (mem_relIcc_hd_succ_iff l r (d.pairing i)).mp hout
  · rintro ⟨hl, hr, hlr, hfull⟩
    refine ⟨mem_hdGlobalActive_succ.mpr hl,
      mem_hdGlobalActive_succ.mpr hr,
      Fin.succ_le_succ_iff.mpr hlr, ?_⟩
    constructor
    · intro i
      refine Fin.cases
        (motive := fun i =>
          i ∈ relIcc (hdGlobalActive active) l.succ r.succ →
            κ i = i → False)
        ?_ (fun j => ?_) i
      · intro hi _
        have hz := (mem_relIcc.mp hi).2.1
        have hzv : l.val + 1 ≤ 0 := hz
        omega
      · intro hi hfix
        have hj :
            j ∈ relIcc active l r :=
          (mem_relIcc_hd_succ_iff l r j).mp hi
        have hjne : j ≠ d.index := by
          intro hjeq
          subst j
          exact hfull.ne_of_mem hj
            (mem_singles.mp d.isSingle)
        apply hfull.ne_of_mem hj
        apply Fin.ext
        have hv := congrArg Fin.val hfix
        rw [headDeletionData_succ_ne κ hκ j hjne] at hv
        change Nat.succ (d.pairing j).val = Nat.succ j.val at hv
        exact Nat.succ.inj hv
    · intro i
      refine Fin.cases
        (motive := fun i =>
          i ∈ relIcc (hdGlobalActive active) l.succ r.succ →
            κ i ∈ relIcc (hdGlobalActive active) l.succ r.succ)
        ?_ (fun j => ?_) i
      · intro hi
        have hz := (mem_relIcc.mp hi).2.1
        have hzv : l.val + 1 ≤ 0 := hz
        omega
      · intro hi
        have hj :
            j ∈ relIcc active l r :=
          (mem_relIcc_hd_succ_iff l r j).mp hi
        have hjne : j ≠ d.index := by
          intro hjeq
          subst j
          exact hfull.ne_of_mem hj
            (mem_singles.mp d.isSingle)
        have hout := hfull.apply_mem hj
        have hgout :=
          (mem_relIcc_hd_succ_iff l r (d.pairing j)).mpr hout
        rw [headDeletionData_succ_ne κ hκ j hjne]
        exact hgout

theorem hdTailActive_sdiff_succ
    {n : ℕ} (active : Finset (Fin n))
    (l r : Fin n) :
    hdTailActive
        (hdGlobalActive active \
          relIcc (hdGlobalActive active) l.succ r.succ) =
      active \ relIcc active l r := by
  rw [hdGlobalActive_sdiff_succ, hdTailActive_hdGlobalActive]

/-! ## The order-separation invariant of already removed pairs -/

/-- Every pair already removed from `active` lies entirely in one gap of
the remaining order: it cannot straddle an active index. -/
def HdSeparated {n : ℕ} (d : MarkedSingle (Fin n))
    (active : Finset (Fin n)) : Prop :=
  ∀ i, i ∉ active → ∀ j, j ∈ active →
    ¬((i ≤ j ∧ j ≤ d.pairing i) ∨
      (d.pairing i ≤ j ∧ j ≤ i))

theorem hdSeparated_univ {n : ℕ} (d : MarkedSingle (Fin n)) :
    HdSeparated d Finset.univ := by
  intro i hi
  simp at hi

theorem hdSeparated_sdiff_relIcc
    {n : ℕ} {d : MarkedSingle (Fin n)}
    {active : Finset (Fin n)} {l r : Fin n}
    (hsep : HdSeparated d active)
    (hfull : IsFullyPairedOn d.pairing (relIcc active l r)) :
    HdSeparated d (active \ relIcc active l r) := by
  intro i hi j hj hbetween
  have hjA : j ∈ active := (Finset.mem_sdiff.mp hj).1
  have hjC : j ∉ relIcc active l r :=
    (Finset.mem_sdiff.mp hj).2
  by_cases hiA : i ∈ active
  · have hiC : i ∈ relIcc active l r := by
      by_contra hiC
      exact hi (Finset.mem_sdiff.mpr ⟨hiA, hiC⟩)
    have hdiC : d.pairing i ∈ relIcc active l r :=
      hfull.apply_mem hiC
    have hiBounds := (mem_relIcc.mp hiC).2
    have hdiBounds := (mem_relIcc.mp hdiC).2
    apply hjC
    rw [mem_relIcc]
    refine ⟨hjA, ?_⟩
    rcases hbetween with hbetween | hbetween
    · exact ⟨hiBounds.1.trans hbetween.1,
        hbetween.2.trans hdiBounds.2⟩
    · exact ⟨hdiBounds.1.trans hbetween.1,
        hbetween.2.trans hiBounds.2⟩
  · exact hsep i hiA j hjA hbetween

/-- The ambient active state stays fully paired when a successor candidate
is removed. -/
theorem hdGlobal_fullyPaired_sdiff
    {n : ℕ} {κ : PartialPairing (Fin (n + 1))}
    {active : Finset (Fin n)} {l r : Fin n}
    (hglobal :
      IsFullyPairedOn κ (hdGlobalActive active))
    (hcand :
      IsRelFullyPaired κ (hdGlobalActive active) l.succ r.succ) :
    IsFullyPairedOn κ
      (hdGlobalActive (active \ relIcc active l r)) := by
  rw [← hdGlobalActive_sdiff_succ]
  constructor
  · intro i hi
    exact hglobal.ne_of_mem (Finset.mem_sdiff.mp hi).1
  · intro i hi
    rw [Finset.mem_sdiff] at hi ⊢
    exact ⟨hglobal.apply_mem hi.1,
      hcand.isFullyPairedOn.apply_notMem hi.2⟩

/-! ## Non-splitting rules out a proper relative head prefix -/

/-- General-size version of the paper's non-concatenation condition. -/
def HdNonSplit {n : ℕ}
    (κ : PartialPairing (Fin (n + 1))) : Prop :=
  κ.IsFull ∧
    ¬∃ p ∈ Finset.range (n + 1), p + 1 < n + 1 ∧
      IsFullyPairedOn κ
        (Finset.univ.filter fun i : Fin (n + 1) => i.val ≤ p)

theorem hdMarkedIndex_mem
    {n : ℕ} {κ : PartialPairing (Fin (n + 1))}
    {active : Finset (Fin n)} (hκ : κ 0 ≠ 0)
    (hglobal : IsFullyPairedOn κ (hdGlobalActive active)) :
    (headDeletionData κ hκ).index ∈ active := by
  have hout := hglobal.apply_mem (mem_hdGlobalActive_zero active)
  rw [headDeletionData_zero κ hκ] at hout
  exact mem_hdGlobalActive_succ.mp hout

theorem hdPrefix_fullyPaired_of_head_candidate
    {n : ℕ} {κ : PartialPairing (Fin (n + 1))}
    {active : Finset (Fin n)} (hκ : κ 0 ≠ 0)
    (hfull : κ.IsFull)
    (hglobal : IsFullyPairedOn κ (hdGlobalActive active))
    (hsep : HdSeparated (headDeletionData κ hκ) active)
    {b : Fin (n + 1)}
    (hcand :
      IsRelFullyPaired κ (hdGlobalActive active) 0 b) :
    IsFullyPairedOn κ
      (Finset.univ.filter fun i : Fin (n + 1) =>
        i.val ≤ b.val) := by
  let d := headDeletionData κ hκ
  have hdidx : d.index ∈ active :=
    hdMarkedIndex_mem hκ hglobal
  constructor
  · intro i _
    exact hfull i
  · intro i hi
    have hib : i.val ≤ b.val := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hmemResult :
        κ i ∈ Finset.univ.filter
          (fun z : Fin (n + 1) => z.val ≤ b.val) := by
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · have hzC :
            (0 : Fin (n + 1)) ∈
              relIcc (hdGlobalActive active) 0 b :=
          mem_relIcc.mpr
            ⟨mem_hdGlobalActive_zero active, Fin.zero_le _, hcand.le⟩
        have hout := hcand.isFullyPairedOn.apply_mem hzC
        have houtLe := (mem_relIcc.mp hout).2.2
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
          (show (κ 0).val ≤ b.val from houtLe)
      · by_cases hjA : j ∈ active
        · have hjC :
              j.succ ∈
                relIcc (hdGlobalActive active) 0 b := by
            rw [mem_relIcc]
            exact ⟨mem_hdGlobalActive_succ.mpr hjA,
              Fin.zero_le _, Fin.le_def.mpr hib⟩
          have hout := hcand.isFullyPairedOn.apply_mem hjC
          have houtLe := (mem_relIcc.mp hout).2.2
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
            (show (κ j.succ).val ≤ b.val from houtLe)
        · have hjne : j ≠ d.index := fun hjeq => by
            subst j
            exact hjA hdidx
          obtain rfl | ⟨k, rfl⟩ := Fin.eq_zero_or_eq_succ b
          · have : j.val + 1 ≤ 0 := hib
            omega
          · have hkA : k ∈ active :=
              mem_hdGlobalActive_succ.mp hcand.right_mem
            have hjk : j ≤ k := Fin.succ_le_succ_iff.mp
              (Fin.le_def.mpr hib)
            have hdk : d.pairing j ≤ k := by
              by_contra hnot
              have hkd : k ≤ d.pairing j :=
                le_of_lt (lt_of_not_ge hnot)
              exact hsep j hjA k hkA
                (Or.inl ⟨hjk, hkd⟩)
            rw [headDeletionData_succ_ne κ hκ j hjne]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact Fin.succ_le_succ_iff.mpr hdk
    exact hmemResult

theorem hdHeadCandidate_right_eq_last
    {n : ℕ} {κ : PartialPairing (Fin (n + 1))}
    {active : Finset (Fin n)} (hκ : κ 0 ≠ 0)
    (hns : HdNonSplit κ)
    (hglobal : IsFullyPairedOn κ (hdGlobalActive active))
    (hsep : HdSeparated (headDeletionData κ hκ) active)
    {b : Fin (n + 1)}
    (hcand :
      IsRelFullyPaired κ (hdGlobalActive active) 0 b) :
    b = Fin.last n := by
  by_contra hne
  apply hns.2
  refine ⟨b.val, Finset.mem_range.mpr b.isLt, ?_, ?_⟩
  · have hbLe : b.val ≤ n := Nat.le_of_lt_succ b.isLt
    have hbNe : b.val ≠ n := fun h => hne (Fin.ext h)
    omega
  · exact hdPrefix_fullyPaired_of_head_candidate
      hκ hns.1 hglobal hsep hcand

theorem relIcc_hdGlobal_zero_last
    {n : ℕ} (active : Finset (Fin n)) :
    relIcc (hdGlobalActive active) 0 (Fin.last n) =
      hdGlobalActive active := by
  ext i
  rw [mem_relIcc]
  constructor
  · exact fun hi => hi.1
  · intro hi
    exact ⟨hi, Fin.zero_le _, Fin.le_last _⟩

theorem card_hdGlobalActive
    {n : ℕ} (active : Finset (Fin n)) :
    (hdGlobalActive active).card = active.card + 1 := by
  rw [hdGlobalActive, Finset.card_insert_of_notMem]
  · rw [Finset.card_map]
  · simp [hdSuccEmbedding, Fin.succ_ne_zero]

/-! ## Selector compatibility before the terminal head extraction -/

theorem selectRel_headDeletion_eq_succ
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0)
    (active : Finset (Fin n))
    (hns : HdNonSplit κ)
    (hglobal : IsFullyPairedOn κ (hdGlobalActive active))
    (hsep : HdSeparated (headDeletionData κ hκ) active)
    (hg : ∃ l r,
      IsRelFullyPaired κ (hdGlobalActive active) l r)
    (hl : ∃ l r,
      IsRelFullyPaired (headDeletionData κ hκ).pairing
        active l r) :
    selectRel κ (hdGlobalActive active) hg =
      hdSuccPair
        (selectRel (headDeletionData κ hκ).pairing active hl) := by
  let d := headDeletionData κ hκ
  let p := selectRel κ (hdGlobalActive active) hg
  let s := selectRel d.pairing active hl
  have hp :
      IsRelFullyPaired κ (hdGlobalActive active) p.1 p.2 :=
    selectRel_isRelFullyPaired κ (hdGlobalActive active) hg
  have hs : IsRelFullyPaired d.pairing active s.1 s.2 :=
    selectRel_isRelFullyPaired d.pairing active hl
  have hsGlobal :
      IsRelFullyPaired κ (hdGlobalActive active)
        s.1.succ s.2.succ :=
    (isRelFullyPaired_headDeletion_succ_iff
      κ hκ active s.1 s.2).mpr hs
  have hpFirst :
      ∃ l : Fin n, p.1 = l.succ := by
    obtain hpzero | ⟨l, hlp⟩ := Fin.eq_zero_or_eq_succ p.1
    · exfalso
      have hphead :
          IsRelFullyPaired κ (hdGlobalActive active) 0 p.2 := by
        simpa only [hpzero] using hp
      have hplast :
          p.2 = Fin.last n :=
        hdHeadCandidate_right_eq_last
          hκ hns hglobal hsep hphead
      have hcardle := selectRel_card_le hg hsGlobal
      change
        (relIcc (hdGlobalActive active) p.1 p.2).card ≤
          (relIcc (hdGlobalActive active)
            s.1.succ s.2.succ).card at hcardle
      rw [hpzero, hplast, relIcc_hdGlobal_zero_last,
        card_hdGlobalActive, card_relIcc_hd_succ] at hcardle
      have hsub :=
        Finset.card_le_card
          (relIcc_subset_active active s.1 s.2)
      omega
    · exact ⟨l, hlp⟩
  obtain ⟨l, hpl⟩ := hpFirst
  have hpSecond :
      ∃ r : Fin n, p.2 = r.succ := by
    obtain hpzero | ⟨r, hrp⟩ := Fin.eq_zero_or_eq_succ p.2
    · have hle := hp.le
      rw [hpl, hpzero] at hle
      have hlev : l.val + 1 ≤ 0 := hle
      omega
    · exact ⟨r, hrp⟩
  obtain ⟨r, hpr⟩ := hpSecond
  have hlr : IsRelFullyPaired d.pairing active l r := by
    apply (isRelFullyPaired_headDeletion_succ_iff
      κ hκ active l r).mp
    simpa only [hpl, hpr] using hp
  have hglobalCardLe := selectRel_card_le hg hsGlobal
  change
    (relIcc (hdGlobalActive active) p.1 p.2).card ≤
      (relIcc (hdGlobalActive active)
        s.1.succ s.2.succ).card at hglobalCardLe
  rw [hpl, hpr, card_relIcc_hd_succ,
    card_relIcc_hd_succ] at hglobalCardLe
  have hlocalCardLe := selectRel_card_le hl hlr
  change
    (relIcc active s.1 s.2).card ≤
      (relIcc active l r).card at hlocalCardLe
  have hcard :
      (relIcc active s.1 s.2).card =
        (relIcc active l r).card :=
    le_antisymm hlocalCardLe hglobalCardLe
  have hglobalCard :
      (relIcc (hdGlobalActive active) p.1 p.2).card =
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
    selectRel_snd_le hg hsGlobal hglobalCard hglobalFstEq
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

theorem hdWholeCandidate
    {n : ℕ} {κ : PartialPairing (Fin (n + 1))}
    {active : Finset (Fin n)} (hκ : κ 0 ≠ 0)
    (hns : HdNonSplit κ)
    (hglobal : IsFullyPairedOn κ (hdGlobalActive active))
    (hsep : HdSeparated (headDeletionData κ hκ) active) :
    IsRelFullyPaired κ (hdGlobalActive active) 0 (Fin.last n) := by
  have hne :
      (hdGlobalActive active).Nonempty :=
    ⟨0, mem_hdGlobalActive_zero active⟩
  let b : Fin (n + 1) :=
    (hdGlobalActive active).max' hne
  have hb : b ∈ hdGlobalActive active :=
    Finset.max'_mem _ hne
  have hrel :
      relIcc (hdGlobalActive active) 0 b =
        hdGlobalActive active := by
    ext i
    rw [mem_relIcc]
    constructor
    · exact fun hi => hi.1
    · intro hi
      exact ⟨hi, Fin.zero_le _,
        Finset.le_max' (hdGlobalActive active) i hi⟩
  have hcand :
      IsRelFullyPaired κ (hdGlobalActive active) 0 b :=
    ⟨mem_hdGlobalActive_zero active, hb, Fin.zero_le _,
      by simpa only [hrel] using hglobal⟩
  have hblast :=
    hdHeadCandidate_right_eq_last
      hκ hns hglobal hsep hcand
  simpa only [hblast] using hcand

theorem selectRel_headDeletion_terminal
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0)
    (active : Finset (Fin n))
    (hns : HdNonSplit κ)
    (hglobal : IsFullyPairedOn κ (hdGlobalActive active))
    (hsep : HdSeparated (headDeletionData κ hκ) active)
    (hl : ¬∃ l r,
      IsRelFullyPaired (headDeletionData κ hκ).pairing
        active l r) :
    let hg : ∃ l r,
        IsRelFullyPaired κ (hdGlobalActive active) l r :=
      ⟨0, Fin.last n,
        hdWholeCandidate hκ hns hglobal hsep⟩
    selectRel κ (hdGlobalActive active) hg =
      (0, Fin.last n) := by
  let hg : ∃ l r,
      IsRelFullyPaired κ (hdGlobalActive active) l r :=
    ⟨0, Fin.last n,
      hdWholeCandidate hκ hns hglobal hsep⟩
  let p := selectRel κ (hdGlobalActive active) hg
  have hp :
      IsRelFullyPaired κ (hdGlobalActive active) p.1 p.2 :=
    selectRel_isRelFullyPaired κ (hdGlobalActive active) hg
  have hpzero : p.1 = 0 := by
    obtain hpzero | ⟨l, hpl⟩ := Fin.eq_zero_or_eq_succ p.1
    · exact hpzero
    · obtain hp2zero | ⟨r, hpr⟩ :=
        Fin.eq_zero_or_eq_succ p.2
      · have hle := hp.le
        rw [hpl, hp2zero] at hle
        have hlev : l.val + 1 ≤ 0 := hle
        omega
      · exfalso
        apply hl
        refine ⟨l, r, ?_⟩
        apply (isRelFullyPaired_headDeletion_succ_iff
          κ hκ active l r).mp
        simpa only [hpl, hpr] using hp
  have hphead :
      IsRelFullyPaired κ (hdGlobalActive active) 0 p.2 := by
    simpa only [hpzero] using hp
  have hplast :
      p.2 = Fin.last n :=
    hdHeadCandidate_right_eq_last
      hκ hns hglobal hsep hphead
  change p = (0, Fin.last n)
  exact Prod.ext hpzero hplast

/-! ## Exact recursion and public extraction theorem -/

theorem extractAux_headDeletion_exact_state
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0) (hns : HdNonSplit κ)
    (fuel : ℕ) :
    ∀ active : Finset (Fin n),
      active.card ≤ 2 * fuel + 1 →
      IsFullyPairedOn κ (hdGlobalActive active) →
      HdSeparated (headDeletionData κ hκ) active →
      extractAux κ (fuel + 1) (hdGlobalActive active) =
        (extractAux (headDeletionData κ hκ).pairing
            fuel active).map hdSuccPair ++
          [(0, Fin.last n)] := by
  induction fuel with
  | zero =>
      intro active hcard hglobal hsep
      have hl :
          ¬∃ l r,
            IsRelFullyPaired (headDeletionData κ hκ).pairing
              active l r := by
        rintro ⟨l, r, hlr⟩
        have htwo := hlr.two_le_card
        have hsub :=
          Finset.card_le_card (relIcc_subset_active active l r)
        omega
      let hg : ∃ l r,
          IsRelFullyPaired κ (hdGlobalActive active) l r :=
        ⟨0, Fin.last n,
          hdWholeCandidate hκ hns hglobal hsep⟩
      have hsel :
          selectRel κ (hdGlobalActive active) hg =
            (0, Fin.last n) :=
        selectRel_headDeletion_terminal
          κ hκ active hns hglobal hsep hl
      rw [extractAux_succ_pos 0 hg, hsel,
        relIcc_hdGlobal_zero_last]
      simp
  | succ fuel ih =>
      intro active hcard hglobal hsep
      let d := headDeletionData κ hκ
      by_cases hl :
          ∃ l r, IsRelFullyPaired d.pairing active l r
      · let s := selectRel d.pairing active hl
        have hs : IsRelFullyPaired d.pairing active s.1 s.2 :=
          selectRel_isRelFullyPaired d.pairing active hl
        let hg : ∃ l r,
            IsRelFullyPaired κ (hdGlobalActive active) l r :=
          ⟨s.1.succ, s.2.succ,
            (isRelFullyPaired_headDeletion_succ_iff
              κ hκ active s.1 s.2).mpr hs⟩
        have hsel :
            selectRel κ (hdGlobalActive active) hg =
              hdSuccPair s :=
          selectRel_headDeletion_eq_succ
            κ hκ active hns hglobal hsep hg hl
        let active' :=
          active \ relIcc active s.1 s.2
        have hcard' : active'.card ≤ 2 * fuel + 1 := by
          have hshrink := card_sdiff_relIcc_add_two_le hs
          change active.card ≤ 2 * (fuel + 1) + 1 at hcard
          change
            (active \ relIcc active s.1 s.2).card ≤
              2 * fuel + 1
          omega
        have hglobal' :
            IsFullyPairedOn κ (hdGlobalActive active') := by
          exact hdGlobal_fullyPaired_sdiff hglobal
            ((isRelFullyPaired_headDeletion_succ_iff
              κ hκ active s.1 s.2).mpr hs)
        have hsep' : HdSeparated d active' :=
          hdSeparated_sdiff_relIcc hsep hs.isFullyPairedOn
        have hrec :=
          ih active' hcard' hglobal' hsep'
        have hglobalStep :
            extractAux κ ((fuel + 1) + 1)
                (hdGlobalActive active) =
              selectRel κ (hdGlobalActive active) hg ::
                extractAux κ (fuel + 1)
                  (hdGlobalActive active \
                    relIcc (hdGlobalActive active)
                      (selectRel κ
                        (hdGlobalActive active) hg).1
                      (selectRel κ
                        (hdGlobalActive active) hg).2) :=
          extractAux_succ_pos (fuel + 1) hg
        have hlocalStep :
            extractAux d.pairing (fuel + 1) active =
              s :: extractAux d.pairing fuel active' := by
          change
            extractAux d.pairing (fuel + 1) active =
              selectRel d.pairing active hl ::
                extractAux d.pairing fuel
                  (active \
                    relIcc active
                      (selectRel d.pairing active hl).1
                      (selectRel d.pairing active hl).2)
          exact extractAux_succ_pos fuel hl
        rw [hglobalStep, hlocalStep, List.map_cons, hsel]
        change
          hdSuccPair s ::
              extractAux κ (fuel + 1)
                (hdGlobalActive active \
                  relIcc (hdGlobalActive active)
                    s.1.succ s.2.succ) =
            hdSuccPair s ::
              ((extractAux d.pairing fuel active').map
                hdSuccPair ++ [(0, Fin.last n)])
        rw [hdGlobalActive_sdiff_succ]
        exact congrArg (List.cons (hdSuccPair s)) hrec
      · let hg : ∃ l r,
            IsRelFullyPaired κ (hdGlobalActive active) l r :=
          ⟨0, Fin.last n,
            hdWholeCandidate hκ hns hglobal hsep⟩
        have hsel :
            selectRel κ (hdGlobalActive active) hg =
              (0, Fin.last n) :=
          selectRel_headDeletion_terminal
            κ hκ active hns hglobal hsep hl
        rw [extractAux_succ_pos (fuel + 1) hg, hsel,
          relIcc_hdGlobal_zero_last]
        rw [extractAux_nil_of_no_candidate _ hl]
        have hempty :
            ¬∃ l r,
              IsRelFullyPaired κ
                (∅ : Finset (Fin (n + 1))) l r := by
          rintro ⟨l, r, hlr⟩
          simpa using hlr.left_mem
        rw [Finset.sdiff_self]
        rw [extractAux_nil_of_no_candidate _ hempty]
        simp

theorem extract_headDeletion_exact
    {n : ℕ} (κ : PartialPairing (Fin (n + 1)))
    (hκ : κ 0 ≠ 0) (hns : HdNonSplit κ) :
    extract κ =
      (extract (headDeletionData κ hκ).pairing).map
          hdSuccPair ++
        [(0, Fin.last n)] := by
  unfold extract
  have hstate :=
    extractAux_headDeletion_exact_state
      κ hκ hns n Finset.univ
      (by simp; omega)
      (by
        rw [hdGlobalActive_univ]
        exact isFullyPairedOn_univ_iff.mpr hns.1)
      (hdSeparated_univ (headDeletionData κ hκ))
  simpa only [hdGlobalActive_univ] using hstate

/-- Direct specialization to a positive even non-split block. -/
theorem extract_nonSplit_succ_headDeletion_exact
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (hσ : IsNonSplit σ) :
    extract σ =
      (extract
        (headDeletionData (n := 2 * q + 1) σ
          (hσ.1 0)).pairing).map hdSuccPair ++
        [(0, Fin.last (2 * q + 1))] := by
  have hns : HdNonSplit σ := by
    refine ⟨hσ.1, ?_⟩
    rintro ⟨p, hpRange, hpProper, hpFull⟩
    apply hσ.2
    refine ⟨p, ?_, ?_, ?_⟩
    · simpa [Nat.mul_add, Nat.add_assoc] using hpRange
    · simpa [Nat.mul_add, Nat.add_assoc] using hpProper
    · convert hpFull using 1
      · simp [Nat.mul_add, Nat.add_assoc]
      · ext i
        simp
  exact extract_headDeletion_exact
    (n := 2 * q + 1) σ (hσ.1 0) hns

/-- The direct paper specialization, rewritten with the generic
whole-prefix endpoint pair used by the integrand ledger. -/
theorem extract_nonSplit_eq_proper_append_whole
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (hσ : IsNonSplit σ) :
    extract σ =
      (extract
        (headDeletionData (n := 2 * q + 1) σ
          (hσ.1 0)).pairing).map hdSuccPair ++
        [wholePrefixPair
          (by omega : 0 < 2 * (q + 1))] := by
  rw [extract_nonSplit_succ_headDeletion_exact q σ hσ]
  apply congrArg
    (fun p : Fin (2 * (q + 1)) × Fin (2 * (q + 1)) =>
      (extract
        (headDeletionData (n := 2 * q + 1) σ
          (hσ.1 0)).pairing).map hdSuccPair ++ [p])
  apply Prod.ext
  · apply Fin.ext
    rfl
  · apply Fin.ext
    simp [wholePrefixPair]
    omega

/-- The proper extractions preceding the terminal whole block cannot
share its right endpoint.  This is the precise strict-bound fact needed
to use the non-junk branch of `diffFactorJ`. -/
theorem nonSplit_proper_right_before_whole
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (hσ : IsNonSplit σ)
    (p : Fin (2 * (q + 1)) × Fin (2 * (q + 1)))
    (hp :
      p ∈
        (extract
          (headDeletionData (n := 2 * q + 1) σ
            (hσ.1 0)).pairing).map hdSuccPair) :
    p.2.val + 1 < 2 * (q + 1) := by
  let proper :=
    (extract
      (headDeletionData (n := 2 * q + 1) σ
        (hσ.1 0)).pairing).map hdSuccPair
  have hnodup := extract_map_snd_nodup σ
  rw [extract_nonSplit_eq_proper_append_whole q σ hσ] at hnodup
  change
    ((proper ++
      [wholePrefixPair
        (by omega : 0 < 2 * (q + 1))]).map Prod.snd).Nodup
      at hnodup
  simp only [List.map_append, List.map_singleton] at hnodup
  have hdisjoint :=
    (List.nodup_append'.mp hnodup).2.2
  have hnot :
      (wholePrefixPair
        (by omega : 0 < 2 * (q + 1))).2 ∉
          proper.map Prod.snd := by
    intro hmem
    exact (List.disjoint_left.mp hdisjoint) hmem (by simp)
  by_contra hlt
  apply hnot
  apply List.mem_map.mpr
  refine ⟨p, ?_, ?_⟩
  · simpa only [proper] using hp
  · apply Fin.ext
    unfold wholePrefixPair
    change p.2.val = 2 * (q + 1) - 1
    have hpLt := p.2.isLt
    change p.2.val < 2 * (q + 1) at hpLt
    omega

/-- Non-split specialization of the prefix difference ledger. -/
theorem prefixDifferenceProduct_nonSplit
    {N : ℕ} (q : ℕ)
    (ha : 2 * (q + 1) ≤ N)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (hσ : IsNonSplit σ)
    (xt : Fin (N + 2) → T4) :
    ((extract σ).map
        (fun p => diffFactor xt (eaPrefixPair ha p))).prod =
      ((extract σ).map
          (diffFactorJ (ambientPrefixTuple ha xt))).prod *
        (greenFn
            (ambientTailTuple ha xt 0 -
              ambientTailTuple ha xt 1) -
          greenFn
            (ambientPrefixTuple ha xt
                ⟨0, by omega⟩ -
              ambientTailTuple ha xt 1)) := by
  apply prefixDifferenceProduct_eq_detJ_mul_boundary
    ha (by omega) σ xt
    ((extract
      (headDeletionData (n := 2 * q + 1) σ
        (hσ.1 0)).pairing).map hdSuccPair)
  · rw [extract_nonSplit_eq_proper_append_whole
      q σ hσ]
  · intro p hp
    exact nonSplit_proper_right_before_whole
      q σ hσ p hp

theorem chainProduct_appendPairingTo
    {N a : ℕ} (ha : a ≤ N) (ha0 : 0 < a)
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin (N - a)))
    (xt : Fin (N + 2) → T4)
    (hwhole :
      a ∈ (extract σ).map (fun p => p.2.val + 1)) :
    (∏ e : Fin (N + 1),
        if e.val ∈
            (extract (appendPairingTo ha σ τ)).map
              (fun p => p.2.val + 1) then 1
        else greenFn (xt e.castSucc - xt e.succ)) =
      greenFn (xt 0 - xt 1) *
        (∏ e : Fin (a - 1),
          if e.val ∈
              (extract σ).map (fun p => p.2.val) then 1
          else if h : e.val + 1 < a then
            greenFn
              (ambientPrefixTuple ha xt
                  ⟨e.val, by omega⟩ -
                ambientPrefixTuple ha xt
                  ⟨e.val + 1, h⟩)
          else 1) *
        ∏ e : Fin (N - a),
          if e.succ.val ∈
              (extract τ).map (fun p => p.2.val + 1)
          then 1
          else greenFn
            (ambientTailTuple ha xt e.succ.castSucc -
              ambientTailTuple ha xt e.succ.succ) := by
  let K := appendPairingTo ha σ τ
  let rvK :=
    (extract K).map (fun p => p.2.val + 1)
  let rvσ :=
    (extract σ).map (fun p => p.2.val + 1)
  let rvτ :=
    (extract τ).map (fun p => a + p.2.val + 1)
  have hperm : rvK.Perm (rvσ ++ rvτ) := by
    exact extractedRightValues_appendPairingTo_perm ha σ τ
  have hmem (k : ℕ) :
      k ∈ rvK ↔ k ∈ rvσ ++ rvτ :=
    hperm.mem_iff
  have hzero : 0 ∉ rvK := by
    intro h
    dsimp only [rvK] at h
    obtain ⟨p, hp, hval⟩ := List.mem_map.mp h
    omega
  change
    (∏ e : Fin (N + 1),
        if e.val ∈ rvK then 1
        else greenFn (xt e.castSucc - xt e.succ)) = _
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, if_neg hzero]
  rw [prod_prefix_suffix ha]
  have hsize : a - 1 + 1 = a := by omega
  rw [← Fin.prod_congr'
    (fun i : Fin a =>
      if (Fin.castLE ha i).succ.val ∈ rvK then 1
      else greenFn
        (xt (Fin.castLE ha i).succ.castSucc -
          xt (Fin.castLE ha i).succ.succ))
    hsize]
  rw [Fin.prod_univ_castSucc]
  have hprefixVal (e : Fin (a - 1)) :
      (Fin.castLE ha (e.castSucc.cast hsize)).succ.val =
        e.val + 1 := by
    rfl
  have hsuffixVal (e : Fin (N - a)) :
      (suffixFin ha e).succ.val = a + e.val + 1 := by
    rfl
  have hlastMem :
      (Fin.castLE ha ((Fin.last (a - 1)).cast hsize)).succ.val
          ∈ rvK := by
    have hval :
        (Fin.castLE ha
          ((Fin.last (a - 1)).cast hsize)).succ.val = a := by
      change a - 1 + 1 = a
      omega
    rw [hval]
    apply (hmem a).mpr
    apply List.mem_append_left
    dsimp only [rvσ]
    exact hwhole
  rw [if_pos hlastMem]
  have hprefix (e : Fin (a - 1)) :
      (Fin.castLE ha (e.castSucc.cast hsize)).succ.val
          ∈ rvK ↔
        e.val ∈ (extract σ).map (fun p => p.2.val) := by
    rw [hprefixVal]
    constructor
    · intro hk
      have h := (hmem (e.val + 1)).mp hk
      rcases List.mem_append.mp h with hp | hp
      · dsimp only [rvσ] at hp
        obtain ⟨p, hp, heq⟩ := List.mem_map.mp hp
        exact List.mem_map.mpr ⟨p, hp, by omega⟩
      · dsimp only [rvτ] at hp
        obtain ⟨p, hp, heq⟩ := List.mem_map.mp hp
        have heLt := e.isLt
        omega
    · intro h
      obtain ⟨p, hp, heq⟩ := List.mem_map.mp h
      apply (hmem (e.val + 1)).mpr
      apply List.mem_append_left
      dsimp only [rvσ]
      exact List.mem_map.mpr ⟨p, hp, by omega⟩
  have hsuffix (e : Fin (N - a)) :
      ((suffixFin ha e).succ.val ∈ rvK) ↔
        e.succ.val ∈
          (extract τ).map (fun p => p.2.val + 1) := by
    rw [hsuffixVal]
    constructor
    · intro hk
      have h := (hmem (a + e.val + 1)).mp hk
      rcases List.mem_append.mp h with hp | hp
      · dsimp only [rvσ] at hp
        obtain ⟨p, hp, heq⟩ := List.mem_map.mp hp
        have hpa := p.2.isLt
        omega
      · dsimp only [rvτ] at hp
        obtain ⟨p, hp, heq⟩ := List.mem_map.mp hp
        refine List.mem_map.mpr ⟨p, hp, ?_⟩
        change p.2.val + 1 = e.val + 1
        omega
    · intro h
      obtain ⟨p, hp, heq⟩ := List.mem_map.mp h
      apply (hmem (a + e.val + 1)).mpr
      apply List.mem_append_right
      dsimp only [rvτ]
      refine List.mem_map.mpr ⟨p, hp, ?_⟩
      change p.2.val + 1 = e.val + 1 at heq
      omega
  have hprefixProd :
      (∏ e : Fin (a - 1),
        if
          (Fin.castLE ha
            (e.castSucc.cast hsize)).succ.val ∈ rvK
        then 1
        else greenFn
          (xt
              (Fin.castLE ha
                (e.castSucc.cast hsize)).succ.castSucc -
            xt
              (Fin.castLE ha
                (e.castSucc.cast hsize)).succ.succ)) =
        ∏ e : Fin (a - 1),
          if e.val ∈
              (extract σ).map (fun p => p.2.val) then 1
          else if h : e.val + 1 < a then
            greenFn
              (ambientPrefixTuple ha xt
                  ⟨e.val, by omega⟩ -
                ambientPrefixTuple ha xt
                  ⟨e.val + 1, h⟩)
          else 1 := by
    apply Finset.prod_congr rfl
    intro e he
    by_cases hamb :
        (Fin.castLE ha
          (e.castSucc.cast hsize)).succ.val ∈ rvK
    · have hlocal :
          e.val ∈ (extract σ).map (fun p => p.2.val) :=
        (hprefix e).mp hamb
      rw [if_pos hamb, if_pos hlocal]
    · have hlocal :
          e.val ∉ (extract σ).map (fun p => p.2.val) :=
        fun h => hamb ((hprefix e).mpr h)
      rw [if_neg hamb, if_neg hlocal]
      have heNext : e.val + 1 < a := by
        have := e.isLt
        omega
      rw [dif_pos heNext]
      apply congrArg greenFn
      apply congrArg₂ (· - ·)
      · apply congrArg xt
        apply Fin.ext
        rfl
      · apply congrArg xt
        apply Fin.ext
        rfl
  have hsuffixProd :
      (∏ e : Fin (N - a),
        if (suffixFin ha e).succ.val ∈ rvK then 1
        else greenFn
          (xt (suffixFin ha e).succ.castSucc -
            xt (suffixFin ha e).succ.succ)) =
        ∏ e : Fin (N - a),
          if e.succ.val ∈
              (extract τ).map (fun p => p.2.val + 1)
          then 1
          else greenFn
            (ambientTailTuple ha xt e.succ.castSucc -
              ambientTailTuple ha xt e.succ.succ) := by
    apply Finset.prod_congr rfl
    intro e he
    by_cases hamb : (suffixFin ha e).succ.val ∈ rvK
    · have hlocal :
          e.succ.val ∈
            (extract τ).map (fun p => p.2.val + 1) :=
        (hsuffix e).mp hamb
      rw [if_pos hamb, if_pos hlocal]
    · have hlocal :
          e.succ.val ∉
            (extract τ).map (fun p => p.2.val + 1) :=
        fun h => hamb ((hsuffix e).mpr h)
      rw [if_neg hamb, if_neg hlocal]
      apply congrArg greenFn
      apply congrArg₂ (· - ·)
      · apply congrArg xt
        apply Fin.ext
        rfl
      · apply congrArg xt
        apply Fin.ext
        rfl
  rw [hprefixProd, hsuffixProd]
  change
    greenFn (xt 0 - xt 1) * ((_ * 1) * _) =
      (greenFn (xt 0 - xt 1) * _) * _
  ring

/-- The terminal whole-prefix extraction removes the chain edge numbered
by the prefix length. -/
theorem nonSplit_whole_extractedRightValue
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (hσ : IsNonSplit σ) :
    2 * (q + 1) ∈
      (extract σ).map (fun p => p.2.val + 1) := by
  rw [extract_nonSplit_eq_proper_append_whole q σ hσ]
  apply List.mem_map.mpr
  refine ⟨wholePrefixPair
      (by omega : 0 < 2 * (q + 1)), ?_, ?_⟩
  · apply List.mem_append_right
    simp
  · unfold wholePrefixPair
    change 2 * (q + 1) - 1 + 1 = 2 * (q + 1)
    omega

/-- Deterministic closed-form compatibility for a non-split fully paired
prefix followed by an arbitrary tail.  The terminal extraction is
exactly the boundary difference missing from the internal `J` chain. -/
theorem detIntegrand_appendPairingTo_nonSplit
    (ρ : SmoothCutoff) (ε : ℝ)
    {N : ℕ} (q : ℕ)
    (ha : 2 * (q + 1) ≤ N)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin (N - 2 * (q + 1))))
    (hσ : IsNonSplit σ)
    (xt : Fin (N + 2) → T4) :
    detIntegrand ρ ε N
        (appendPairingTo ha σ τ) xt =
      greenFn (xt 0 - xt 1) *
        detJintegrand ρ ε (q + 1) σ
          (ambientPrefixTuple ha xt) *
        (greenFn
            (ambientTailTuple ha xt 0 -
              ambientTailTuple ha xt 1) -
          greenFn
            (ambientPrefixTuple ha xt
                ⟨0, by omega⟩ -
              ambientTailTuple ha xt 1)) *
        detIntegrandAfterFirst ρ ε
          (N - 2 * (q + 1)) τ
          (ambientTailTuple ha xt) := by
  unfold detIntegrand detJintegrand
  unfold detIntegrandAfterFirst
  rw [chainProduct_appendPairingTo
    ha (by omega) σ τ xt
    (nonSplit_whole_extractedRightValue q σ hσ)]
  rw [differenceProduct_appendPairingTo ha σ τ xt]
  rw [prefixDifferenceProduct_nonSplit q ha σ hσ xt]
  rw [covarianceProduct_appendPairingTo ρ ε ha σ τ xt]
  ring

/-- Random closed-form compatibility for the same block decomposition.
The boundary difference is represented canonically as the difference of
two tail random integrands, exactly the `(J-Cδ)+Cδ` split used in the
paper's case-(3) reduction. -/
theorem randIntegrand_appendPairingTo_nonSplit
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {N : ℕ} (q : ℕ)
    (ha : 2 * (q + 1) ≤ N)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin (N - 2 * (q + 1))))
    (hσ : IsNonSplit σ)
    (xt : Fin (N + 2) → T4) (ω : M.Ω) :
    randIntegrand M ρ ε
        (appendPairingTo ha σ τ) xt ω =
      greenFn (xt 0 - xt 1) *
        detJintegrand ρ ε (q + 1) σ
          (ambientPrefixTuple ha xt) *
        (randIntegrand M ρ ε τ
            (ambientTailTuple ha xt) ω -
          randIntegrand M ρ ε τ
            (setTupleFirst
              (ambientPrefixTuple ha xt
                ⟨0, by omega⟩)
              (ambientTailTuple ha xt)) ω) := by
  change
    detIntegrand ρ ε N
        (appendPairingTo ha σ τ) xt *
      wickAt M ρ ε (appendPairingTo ha σ τ) xt ω = _
  rw [detIntegrand_appendPairingTo_nonSplit
    ρ ε q ha σ τ hσ xt]
  rw [wickAt_appendPairingTo_ambientTuple
    M ρ ε ha σ τ hσ.1 xt ω]
  rw [randIntegrand_sub_setTupleFirst
    M ρ ε τ
    (ambientPrefixTuple ha xt
      ⟨0, by omega⟩)
    (ambientTailTuple ha xt) ω]
  ring

/-- Rearranged pointwise form used directly in paper (3.18): the raw
`J × tail` block is the ambient renormalized integrand plus the diagonal
tail block. -/
theorem rawBlock_eq_ambient_add_diagonal
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {N : ℕ} (q : ℕ)
    (ha : 2 * (q + 1) ≤ N)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin (N - 2 * (q + 1))))
    (hσ : IsNonSplit σ)
    (xt : Fin (N + 2) → T4) (ω : M.Ω) :
    greenFn (xt 0 - xt 1) *
        detJintegrand ρ ε (q + 1) σ
          (ambientPrefixTuple ha xt) *
        randIntegrand M ρ ε τ
          (ambientTailTuple ha xt) ω =
      randIntegrand M ρ ε
          (appendPairingTo ha σ τ) xt ω +
        greenFn (xt 0 - xt 1) *
          detJintegrand ρ ε (q + 1) σ
            (ambientPrefixTuple ha xt) *
          randIntegrand M ρ ε τ
            (setTupleFirst
              (ambientPrefixTuple ha xt
                ⟨0, by omega⟩)
              (ambientTailTuple ha xt)) ω := by
  rw [randIntegrand_appendPairingTo_nonSplit
    M ρ ε q ha σ τ hσ xt ω]
  ring

def arithmeticTailEquiv (a r : ℕ) :
    Fin r ≃ Fin (a + r - a) :=
  (Fin.castOrderIso (by omega : r = a + r - a)).toEquiv

def arithmeticTailPairing {a r : ℕ}
    (τ : PartialPairing (Fin r)) :
    PartialPairing (Fin (a + r - a)) :=
  PartialPairing.congr (arithmeticTailEquiv a r) τ

@[simp]
theorem arithmeticTailPairing_apply
    {a r : ℕ} (τ : PartialPairing (Fin r)) (j : Fin r) :
    arithmeticTailPairing τ (arithmeticTailEquiv a r j) =
      arithmeticTailEquiv a r (τ j) := by
  unfold arithmeticTailPairing
  rw [PartialPairing.congr_apply_apply]
  simp

@[simp]
theorem arithmeticTailEquiv_val
    (a r : ℕ) (j : Fin r) :
    (arithmeticTailEquiv a r j).val = j.val :=
  rfl

theorem appendPairingTo_arithmeticTailPairing
    {a r : ℕ}
    (σ : PartialPairing (Fin a))
    (τ : PartialPairing (Fin r)) :
    appendPairingTo
        (N := a + r) (a := a) (by omega)
        σ (arithmeticTailPairing τ) =
      appendPairing σ τ := by
  apply PartialPairing.ext
  intro k
  refine Fin.addCases (motive := fun k =>
      appendPairingTo
          (N := a + r) (a := a) (by omega)
          σ (arithmeticTailPairing τ) k =
        appendPairing σ τ k)
    ?_ ?_ k
  · intro i
    have hcast :
        Fin.castLE (by omega : a ≤ a + r) i =
          Fin.castAdd r i := Fin.ext rfl
    calc
      appendPairingTo
          (N := a + r) (a := a) (by omega)
          σ (arithmeticTailPairing τ)
          (Fin.castAdd r i) =
        appendPairingTo
          (N := a + r) (a := a) (by omega)
          σ (arithmeticTailPairing τ)
          (Fin.castLE (by omega : a ≤ a + r) i) := by
            rw [hcast]
      _ = Fin.castLE (by omega : a ≤ a + r) (σ i) := by
        rw [appendPairingTo_apply_prefix]
      _ = Fin.castAdd r (σ i) := Fin.ext rfl
      _ = appendPairing σ τ (Fin.castAdd r i) := by
        rw [appendPairing_apply_castAdd]
  · intro j
    let j' := arithmeticTailEquiv a r j
    have hsuffix :
        suffixFin (by omega : a ≤ a + r) j' =
          Fin.natAdd a j := by
      apply Fin.ext
      rfl
    calc
      appendPairingTo
          (N := a + r) (a := a) (by omega)
          σ (arithmeticTailPairing τ)
          (Fin.natAdd a j) =
        appendPairingTo
          (N := a + r) (a := a) (by omega)
          σ (arithmeticTailPairing τ)
          (suffixFin (by omega : a ≤ a + r) j') := by
            rw [hsuffix]
      _ =
        suffixFin (by omega : a ≤ a + r)
          (arithmeticTailPairing τ j') := by
            rw [appendPairingTo_apply_suffix]
      _ =
        suffixFin (by omega : a ≤ a + r)
          (arithmeticTailEquiv a r (τ j)) := by
            rw [arithmeticTailPairing_apply]
      _ = Fin.natAdd a (τ j) := Fin.ext rfl
      _ = appendPairing σ τ (Fin.natAdd a j) := by
        rw [appendPairing_apply_natAdd]

/-! ## Transport across propositionally equal finite cardinalities -/

def arithmeticCastPairing {m n : ℕ} (h : m = n)
    (κ : PartialPairing (Fin m)) :
    PartialPairing (Fin n) :=
  PartialPairing.congr
    (Fin.castOrderIso h).toEquiv κ

def arithmeticCastTuple {m n : ℕ} (h : m = n)
    (xt : Fin (m + 2) → T4) :
    Fin (n + 2) → T4 :=
  fun j => xt (Fin.cast (by omega : n + 2 = m + 2) j)

@[simp]
theorem arithmeticCastPairing_rfl
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    arithmeticCastPairing rfl κ = κ := by
  rfl

@[simp]
theorem arithmeticCastTuple_rfl
    {m : ℕ} (xt : Fin (m + 2) → T4) :
    arithmeticCastTuple rfl xt = xt := by
  rfl

theorem detIntegrandAfterFirst_arithmeticCast
    (ρ : SmoothCutoff) (ε : ℝ)
    {m n : ℕ} (h : m = n)
    (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) :
    detIntegrandAfterFirst ρ ε n
        (arithmeticCastPairing h κ)
        (arithmeticCastTuple h xt) =
      detIntegrandAfterFirst ρ ε m κ xt := by
  subst n
  rfl

theorem wickAt_arithmeticCast
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {m n : ℕ} (h : m = n)
    (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) (ω : M.Ω) :
    wickAt M ρ ε (arithmeticCastPairing h κ)
        (arithmeticCastTuple h xt) ω =
      wickAt M ρ ε κ xt ω := by
  subst n
  rfl

theorem detIntegrand_arithmeticCast
    (ρ : SmoothCutoff) (ε : ℝ)
    {m n : ℕ} (h : m = n)
    (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) :
    detIntegrand ρ ε n
        (arithmeticCastPairing h κ)
        (arithmeticCastTuple h xt) =
      detIntegrand ρ ε m κ xt := by
  subst n
  rfl

theorem randIntegrand_arithmeticCast
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {m n : ℕ} (h : m = n)
    (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) (ω : M.Ω) :
    randIntegrand M ρ ε
        (arithmeticCastPairing h κ)
        (arithmeticCastTuple h xt) ω =
      randIntegrand M ρ ε κ xt ω := by
  unfold randIntegrand
  rw [detIntegrand_arithmeticCast,
    wickAt_arithmeticCast]

/-! ## The actual case-(3) spatial tuple -/

theorem ambientPrefixTuple_caseThree
    (q r : ℕ) (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    ambientPrefixTuple
        (N := 2 * (q + 1) + r)
        (a := 2 * (q + 1)) (by omega)
        (assemble x y
          (caseThreeAmbientInternal q r z w t)) =
      detJTupleSucc q z w
        (fun i => t (Fin.castAdd r i)) := by
  funext i
  rw [ambientPrefixTuple_apply, assemble_varIdx]
  have hcast :
      Fin.castLE
          (by omega :
            2 * (q + 1) ≤ 2 * (q + 1) + r) i =
        Fin.castAdd r i := Fin.ext rfl
  rw [hcast, caseThreeAmbientInternal_prefix]

@[simp]
theorem detJTupleSucc_last
    (q : ℕ) (z w : T4) (u : Fin (2 * q) → T4) :
    detJTupleSucc q z w u
        (Fin.last (2 * (q + 1) - 1)) = w := by
  unfold detJTupleSucc
  rw [show
      Fin.cast (by omega :
        2 * (q + 1) = 2 * q + 2)
        (Fin.last (2 * (q + 1) - 1)) =
        Fin.last (2 * q + 1) by
      apply Fin.ext
      simp
      omega]
  exact assemble_last z w u

theorem ambientTailTuple_caseThree_cast_apply
    (q r : ℕ) (x z w y : T4)
    (t : Fin (2 * q + r) → T4)
    (j : Fin (r + 2)) :
    ambientTailTuple
        (N := 2 * (q + 1) + r)
        (a := 2 * (q + 1)) (by omega)
        (assemble x y
          (caseThreeAmbientInternal q r z w t))
        (Fin.cast
          (by omega :
            r + 2 =
              (2 * (q + 1) + r -
                2 * (q + 1)) + 2) j) =
      caseThreeTailTuple q r w y t j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · let ilast : Fin (2 * (q + 1)) :=
      ⟨2 * (q + 1) - 1, by omega⟩
    unfold ambientTailTuple
    rw [show
        (⟨2 * (q + 1) +
            (Fin.cast
              (by omega :
                r + 2 =
                  (2 * (q + 1) + r -
                    2 * (q + 1)) + 2)
              (0 : Fin (r + 2))).val, by omega⟩ :
          Fin (2 * (q + 1) + r + 2)) =
          varIdx
            (Fin.castAdd r ilast) by
        apply Fin.ext
        change
          2 * (q + 1) + 0 =
            ilast.val + 1
        dsimp only [ilast]
        omega]
    rw [assemble_varIdx,
      caseThreeAmbientInternal_prefix]
    unfold caseThreeTailTuple
    rw [assemble_zero]
    have hilast :
        ilast = Fin.last (2 * (q + 1) - 1) := by
      apply Fin.ext
      rfl
    rw [hilast, detJTupleSucc_last]
  · refine Fin.lastCases ?_ (fun i => ?_) k
    · unfold ambientTailTuple caseThreeTailTuple
      rw [show
          (⟨2 * (q + 1) +
              (Fin.cast
                (by omega :
                  r + 2 =
                    (2 * (q + 1) + r -
                      2 * (q + 1)) + 2)
                (Fin.last r).succ).val, by omega⟩ :
            Fin (2 * (q + 1) + r + 2)) =
            Fin.last (2 * (q + 1) + r + 1) by
          apply Fin.ext
          simp
          omega]
      rw [assemble_last]
      rw [show
          (Fin.last r).succ =
            Fin.last (r + 1) by
          apply Fin.ext
          simp]
      rw [assemble_last]
    · unfold ambientTailTuple caseThreeTailTuple
      have hj :
          (i.castSucc.succ : Fin (r + 2)) =
            varIdx i := Fin.ext rfl
      rw [hj, assemble_varIdx]
      rw [show
          (⟨2 * (q + 1) +
              (Fin.cast
                (by omega :
                  r + 2 =
                    (2 * (q + 1) + r -
                      2 * (q + 1)) + 2)
                (varIdx i)).val, by omega⟩ :
            Fin (2 * (q + 1) + r + 2)) =
            varIdx
              (Fin.natAdd (2 * (q + 1)) i) by
          apply Fin.ext
          rfl]
      rw [assemble_varIdx,
        caseThreeAmbientInternal_suffix]

theorem ambientTailTuple_caseThree
    (q r : ℕ) (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    ambientTailTuple
        (N := 2 * (q + 1) + r)
        (a := 2 * (q + 1)) (by omega)
        (assemble x y
          (caseThreeAmbientInternal q r z w t)) =
      arithmeticCastTuple
        (by omega :
          r =
            (2 * (q + 1) + r -
              2 * (q + 1)))
        (caseThreeTailTuple q r w y t) := by
  funext j
  unfold arithmeticCastTuple
  let j' : Fin (r + 2) :=
    Fin.cast
      (by omega :
        (2 * (q + 1) + r -
          2 * (q + 1)) + 2 = r + 2) j
  have h :=
    ambientTailTuple_caseThree_cast_apply
      q r x z w y t j'
  have hback :
      Fin.cast
          (by omega :
            r + 2 =
              (2 * (q + 1) + r -
                2 * (q + 1)) + 2) j' =
        j := by
    apply Fin.ext
    rfl
  simpa only [hback, j'] using h

theorem arithmeticTailPairing_eq_cast
    {a r : ℕ} (τ : PartialPairing (Fin r)) :
    arithmeticTailPairing (a := a) τ =
      arithmeticCastPairing
        (by omega : r = a + r - a) τ := by
  rfl

/-! ## Pointwise deterministic case-(3) specialization -/

theorem detIntegrand_caseThreeAmbient
    (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    detIntegrand ρ ε (2 * (q + 1) + r)
        (appendPairing σ τ)
        (assemble x y
          (caseThreeAmbientInternal q r z w t)) =
      greenFn (x - z) *
        detJintegrand ρ ε (q + 1) σ
          (detJTupleSucc q z w
            (fun i => t (Fin.castAdd r i))) *
        (greenFn
            (caseThreeTailTuple q r w y t 0 -
              caseThreeTailTuple q r w y t 1) -
          greenFn
            (z -
              caseThreeTailTuple q r w y t 1)) *
        detIntegrandAfterFirst ρ ε r τ
          (caseThreeTailTuple q r w y t) := by
  let a := 2 * (q + 1)
  let N := a + r
  let ha : a ≤ N := by
    dsimp only [a, N]
    omega
  let xt : Fin (N + 2) → T4 :=
    assemble x y
      (caseThreeAmbientInternal q r z w t)
  let τ' : PartialPairing (Fin (N - a)) :=
    arithmeticTailPairing τ
  have hbase :=
    detIntegrand_appendPairingTo_nonSplit
      ρ ε q ha σ τ' hσ xt
  have hpair :
      appendPairingTo ha σ τ' =
        appendPairing σ τ := by
    exact appendPairingTo_arithmeticTailPairing σ τ
  rw [hpair] at hbase
  have hprefix :
      ambientPrefixTuple ha xt =
        detJTupleSucc q z w
          (fun i => t (Fin.castAdd r i)) := by
    exact ambientPrefixTuple_caseThree
      q r x z w y t
  have htail :
      ambientTailTuple ha xt =
        arithmeticCastTuple
          (by omega : r = N - a)
          (caseThreeTailTuple q r w y t) := by
    exact ambientTailTuple_caseThree
      q r x z w y t
  rw [hprefix, htail] at hbase
  have hτ :
      τ' =
        arithmeticCastPairing
          (by omega : r = N - a) τ := by
    exact arithmeticTailPairing_eq_cast τ
  rw [hτ,
    detIntegrandAfterFirst_arithmeticCast] at hbase
  have hxt0 : xt 0 = x := by
    exact assemble_zero x y
      (caseThreeAmbientInternal q r z w t)
  have hxt1 : xt 1 = z := by
    have hone :
        (1 : Fin (N + 2)) =
          varIdx (0 : Fin N) := Fin.ext rfl
    rw [hone]
    dsimp only [xt, N, a]
    rw [assemble_varIdx]
    have hzero :
        (0 : Fin (2 * (q + 1) + r)) =
          Fin.castAdd r
            (0 : Fin (2 * (q + 1))) := Fin.ext rfl
    rw [hzero, caseThreeAmbientInternal_prefix,
      detJTupleSucc_zero]
  have htail0 :
      arithmeticCastTuple
          (by omega : r = N - a)
          (caseThreeTailTuple q r w y t) 0 =
        caseThreeTailTuple q r w y t 0 := by
    unfold arithmeticCastTuple
    apply congrArg
      (caseThreeTailTuple q r w y t)
    apply Fin.ext
    rfl
  have htail1 :
      arithmeticCastTuple
          (by omega : r = N - a)
          (caseThreeTailTuple q r w y t) 1 =
        caseThreeTailTuple q r w y t 1 := by
    unfold arithmeticCastTuple
    apply congrArg
      (caseThreeTailTuple q r w y t)
    apply Fin.ext
    rfl
  have hprefix0 :
      detJTupleSucc q z w
          (fun i => t (Fin.castAdd r i))
          ⟨0, by omega⟩ = z := by
    rw [show
        (⟨0, by omega⟩ :
          Fin (2 * (q + 1))) = 0 by
      apply Fin.ext
      rfl]
    exact detJTupleSucc_zero q z w
      (fun i => t (Fin.castAdd r i))
  rw [hxt0, hxt1, htail0, htail1,
    hprefix0] at hbase
  simpa only [N, a, xt] using hbase

theorem randIntegrand_caseThreeAmbient
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x z w y : T4)
    (t : Fin (2 * q + r) → T4)
    (ω : M.Ω) :
    randIntegrand M ρ ε
        (appendPairing σ τ)
        (assemble x y
          (caseThreeAmbientInternal q r z w t)) ω =
      greenFn (x - z) *
        detJintegrand ρ ε (q + 1) σ
          (detJTupleSucc q z w
            (fun i => t (Fin.castAdd r i))) *
        (greenFn
            (caseThreeTailTuple q r w y t 0 -
              caseThreeTailTuple q r w y t 1) -
          greenFn
            (z -
              caseThreeTailTuple q r w y t 1)) *
        (detIntegrandAfterFirst ρ ε r τ
            (caseThreeTailTuple q r w y t) *
          wickAt M ρ ε τ
            (caseThreeTailTuple q r w y t) ω) := by
  unfold randIntegrand
  rw [detIntegrand_caseThreeAmbient
    ρ ε q r σ τ hσ x z w y t]
  rw [wickAt_caseThreeAmbient
    M ρ ε q r σ τ hσ.1 x z w y t ω]
  ring

/-- Paper-facing form: the boundary Green difference is exactly the
subtraction produced by replacing the tail's left endpoint `w` by `z`. -/
theorem randIntegrand_caseThreeAmbient_eq_tail_sub
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x z w y : T4)
    (t : Fin (2 * q + r) → T4)
    (ω : M.Ω) :
    randIntegrand M ρ ε
        (appendPairing σ τ)
        (assemble x y
          (caseThreeAmbientInternal q r z w t)) ω =
      greenFn (x - z) *
        detJintegrand ρ ε (q + 1) σ
          (detJTupleSucc q z w
            (fun i => t (Fin.castAdd r i))) *
        (randIntegrand M ρ ε τ
            (caseThreeTailTuple q r w y t) ω -
          randIntegrand M ρ ε τ
            (setTupleFirst z
              (caseThreeTailTuple q r w y t)) ω) := by
  rw [randIntegrand_caseThreeAmbient
    M ρ ε q r σ τ hσ x z w y t ω]
  rw [randIntegrand_sub_setTupleFirst
    M ρ ε τ z
      (caseThreeTailTuple q r w y t) ω]
  ring

/-- Raw `J × tail = ambient + diagonal`, the pointwise paper (3.18)
rearrangement before any spatial integration. -/
theorem caseThreeJointCore_eq_ambient_add_diagonal
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x z w y : T4)
    (t : Fin (2 * q + r) → T4)
    (ω : M.Ω) :
    greenFn (x - z) *
        caseThreeJointCore
          M ρ ε q r σ τ z w y ω t =
      randIntegrand M ρ ε
          (appendPairing σ τ)
          (assemble x y
            (caseThreeAmbientInternal q r z w t)) ω +
        greenFn (x - z) *
          detJintegrand ρ ε (q + 1) σ
            (detJTupleSucc q z w
              (fun i => t (Fin.castAdd r i))) *
          randIntegrand M ρ ε τ
            (setTupleFirst z
              (caseThreeTailTuple q r w y t)) ω := by
  rw [randIntegrand_caseThreeAmbient_eq_tail_sub
    M ρ ε q r σ τ hσ x z w y t ω]
  unfold caseThreeJointCore caseThreeTailTuple
  ring

end PartialPairing

end

end Anderson4D
