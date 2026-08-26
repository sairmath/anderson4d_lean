import Anderson4D.DetParametrix.Paper42_Moment.R324DetIntegrability

/-!
# Rigidity of reduction endpoint signatures

The endpoint signature records the left- and right-bracket positions of the
laminar interval family produced by Definition 3.1.  A priori this forgets
which left endpoint is matched to which right endpoint.  This file proves
that no information is lost: a laminar perfect matching with every edge
oriented to the right is uniquely determined by its two endpoint sets.

The proof uses a maximal-disagreement argument.  If two such matchings send
the greatest disagreeing left endpoint to different right endpoints, pulling
the smaller right endpoint back through the other matching either gives a
larger disagreement or forces two intervals to cross.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-! ## The endpoint equivalence carried by an extraction list -/

theorem exists_extractedPairOfLeftEndpoint
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a : leftEndpoints κ) :
    ∃ p : Fin m × Fin m,
      p ∈ extract κ ∧ p.1 = a.1 := by
  have ha : a.1 ∈
      ((extract κ).map Prod.fst).toFinset := by
    simpa only [leftEndpoints] using a.2
  rw [List.mem_toFinset] at ha
  obtain ⟨p, hp, hpa⟩ := List.mem_map.mp ha
  exact ⟨p, hp, hpa⟩

/-- The extracted interval chosen by a given left endpoint. -/
def extractedPairOfLeftEndpoint
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a : leftEndpoints κ) : Fin m × Fin m :=
  Classical.choose
    (exists_extractedPairOfLeftEndpoint κ a)

theorem extractedPairOfLeftEndpoint_mem
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a : leftEndpoints κ) :
    extractedPairOfLeftEndpoint κ a ∈ extract κ :=
  (Classical.choose_spec
    (exists_extractedPairOfLeftEndpoint κ a)).1

@[simp]
theorem extractedPairOfLeftEndpoint_fst
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a : leftEndpoints κ) :
    (extractedPairOfLeftEndpoint κ a).1 = a.1 :=
  (Classical.choose_spec
    (exists_extractedPairOfLeftEndpoint κ a)).2

theorem exists_extractedPairOfRightEndpoint
    {m : ℕ} (κ : PartialPairing (Fin m))
    (b : rightEndpoints κ) :
    ∃ p : Fin m × Fin m,
      p ∈ extract κ ∧ p.2 = b.1 := by
  have hb : b.1 ∈
      ((extract κ).map Prod.snd).toFinset := by
    simpa only [rightEndpoints] using b.2
  rw [List.mem_toFinset] at hb
  obtain ⟨p, hp, hpb⟩ := List.mem_map.mp hb
  exact ⟨p, hp, hpb⟩

/-- The extracted interval chosen by a given right endpoint. -/
def extractedPairOfRightEndpoint
    {m : ℕ} (κ : PartialPairing (Fin m))
    (b : rightEndpoints κ) : Fin m × Fin m :=
  Classical.choose
    (exists_extractedPairOfRightEndpoint κ b)

theorem extractedPairOfRightEndpoint_mem
    {m : ℕ} (κ : PartialPairing (Fin m))
    (b : rightEndpoints κ) :
    extractedPairOfRightEndpoint κ b ∈ extract κ :=
  (Classical.choose_spec
    (exists_extractedPairOfRightEndpoint κ b)).1

@[simp]
theorem extractedPairOfRightEndpoint_snd
    {m : ℕ} (κ : PartialPairing (Fin m))
    (b : rightEndpoints κ) :
    (extractedPairOfRightEndpoint κ b).2 = b.1 :=
  (Classical.choose_spec
    (exists_extractedPairOfRightEndpoint κ b)).2

theorem extractedPair_eq_of_fst_eq
    {m : ℕ} (κ : PartialPairing (Fin m))
    {p q : Fin m × Fin m}
    (hp : p ∈ extract κ) (hq : q ∈ extract κ)
    (hfst : p.1 = q.1) :
    p = q :=
  List.inj_on_of_nodup_map
    (extract_map_fst_nodup κ) hp hq hfst

theorem extractedPair_eq_of_snd_eq
    {m : ℕ} (κ : PartialPairing (Fin m))
    {p q : Fin m × Fin m}
    (hp : p ∈ extract κ) (hq : q ∈ extract κ)
    (hsnd : p.2 = q.2) :
    p = q :=
  List.inj_on_of_nodup_map
    (extract_map_snd_nodup κ) hp hq hsnd

/-- The extraction list is a perfect matching from its left endpoint set to
its right endpoint set. -/
def extractedEndpointEquiv
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    leftEndpoints κ ≃ rightEndpoints κ where
  toFun a :=
    ⟨(extractedPairOfLeftEndpoint κ a).2, by
      unfold rightEndpoints
      rw [List.mem_toFinset]
      exact List.mem_map.mpr
        ⟨extractedPairOfLeftEndpoint κ a,
          extractedPairOfLeftEndpoint_mem κ a, rfl⟩⟩
  invFun b :=
    ⟨(extractedPairOfRightEndpoint κ b).1, by
      unfold leftEndpoints
      rw [List.mem_toFinset]
      exact List.mem_map.mpr
        ⟨extractedPairOfRightEndpoint κ b,
          extractedPairOfRightEndpoint_mem κ b, rfl⟩⟩
  left_inv a := by
    apply Subtype.ext
    let p := extractedPairOfLeftEndpoint κ a
    let b : rightEndpoints κ :=
      ⟨p.2, by
        unfold rightEndpoints
        rw [List.mem_toFinset]
        exact List.mem_map.mpr
          ⟨p, extractedPairOfLeftEndpoint_mem κ a, rfl⟩⟩
    let q := extractedPairOfRightEndpoint κ b
    have hp : p ∈ extract κ :=
      extractedPairOfLeftEndpoint_mem κ a
    have hq : q ∈ extract κ :=
      extractedPairOfRightEndpoint_mem κ b
    have hpq : q = p := by
      apply extractedPair_eq_of_snd_eq κ hq hp
      exact extractedPairOfRightEndpoint_snd κ b
    change q.1 = a.1
    rw [hpq]
    exact extractedPairOfLeftEndpoint_fst κ a
  right_inv b := by
    apply Subtype.ext
    let q := extractedPairOfRightEndpoint κ b
    let a : leftEndpoints κ :=
      ⟨q.1, by
        unfold leftEndpoints
        rw [List.mem_toFinset]
        exact List.mem_map.mpr
          ⟨q, extractedPairOfRightEndpoint_mem κ b, rfl⟩⟩
    let p := extractedPairOfLeftEndpoint κ a
    have hp : p ∈ extract κ :=
      extractedPairOfLeftEndpoint_mem κ a
    have hq : q ∈ extract κ :=
      extractedPairOfRightEndpoint_mem κ b
    have hpq : p = q := by
      apply extractedPair_eq_of_fst_eq κ hp hq
      exact extractedPairOfLeftEndpoint_fst κ a
    change p.2 = b.1
    rw [hpq]
    exact extractedPairOfRightEndpoint_snd κ b

@[simp]
theorem extractedEndpointEquiv_apply
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a : leftEndpoints κ) :
    (extractedEndpointEquiv κ a).1 =
      (extractedPairOfLeftEndpoint κ a).2 :=
  rfl

theorem extractedEndpointEquiv_lt
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a : leftEndpoints κ) :
    a.1 < (extractedEndpointEquiv κ a).1 := by
  have hp :=
    extract_mem_fst_lt_snd κ
      (extractedPairOfLeftEndpoint κ a)
      (extractedPairOfLeftEndpoint_mem κ a)
  simpa only [extractedEndpointEquiv_apply,
    extractedPairOfLeftEndpoint_fst] using hp

/-- Public membership form of the pairwise laminarity theorem. -/
theorem extractedIntervals_laminar
    {m : ℕ} (κ : PartialPairing (Fin m))
    {p q : Fin m × Fin m}
    (hp : p ∈ extract κ) (hq : q ∈ extract κ)
    (hpq : p ≠ q) :
    ReductionIntervalsLaminar p q := by
  obtain ⟨i, hi⟩ := List.get_of_mem hp
  obtain ⟨j, hj⟩ := List.get_of_mem hq
  have hij : i ≠ j := by
    intro hij
    apply hpq
    rw [← hi, ← hj, hij]
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hrel :=
      (extract_pairwise_laminar κ).rel_get_of_lt hij
    simpa only [hi, hj] using hrel
  · have hrel :=
      (extract_pairwise_laminar κ).rel_get_of_lt hji
    have hqp : ReductionIntervalsLaminar q p := by
      simpa only [hi, hj] using hrel
    exact hqp.symm

theorem extractedEndpointEquiv_laminar
    {m : ℕ} (κ : PartialPairing (Fin m))
    {a d : leftEndpoints κ} (had : a ≠ d) :
    ReductionIntervalsLaminar
      (a.1, (extractedEndpointEquiv κ a).1)
      (d.1, (extractedEndpointEquiv κ d).1) := by
  let p := extractedPairOfLeftEndpoint κ a
  let q := extractedPairOfLeftEndpoint κ d
  have hp : p ∈ extract κ :=
    extractedPairOfLeftEndpoint_mem κ a
  have hq : q ∈ extract κ :=
    extractedPairOfLeftEndpoint_mem κ d
  have hpq : p ≠ q := by
    intro hpq
    apply had
    apply Subtype.ext
    calc
      a.1 = p.1 :=
        (extractedPairOfLeftEndpoint_fst κ a).symm
      _ = q.1 := congrArg Prod.fst hpq
      _ = d.1 :=
        extractedPairOfLeftEndpoint_fst κ d
  have hlam :=
    extractedIntervals_laminar κ hp hq hpq
  have hpform :
      p =
        (a.1, (extractedEndpointEquiv κ a).1) := by
    apply Prod.ext
    · exact extractedPairOfLeftEndpoint_fst κ a
    · rfl
  have hqform :
      q =
        (d.1, (extractedEndpointEquiv κ d).1) := by
    apply Prod.ext
    · exact extractedPairOfLeftEndpoint_fst κ d
    · rfl
  rwa [hpform, hqform] at hlam

/-! ## Uniqueness of a laminar endpoint matching -/

/-- Two right-oriented laminar perfect matchings on the same endpoint sets
are equal. -/
theorem rightOrientedLaminarEquiv_unique
    {m : ℕ} {L R : Finset (Fin m)}
    (f g : L ≃ R)
    (hf_lt : ∀ a, a.1 < (f a).1)
    (hg_lt : ∀ a, a.1 < (g a).1)
    (hf_laminar : ∀ {a d : L}, a ≠ d →
      ReductionIntervalsLaminar
        (a.1, (f a).1) (d.1, (f d).1))
    (hg_laminar : ∀ {a d : L}, a ≠ d →
      ReductionIntervalsLaminar
        (a.1, (g a).1) (d.1, (g d).1)) :
    f = g := by
  apply Equiv.ext
  by_contra hne
  have hnonempty :
      ((Finset.univ : Finset L).filter
        fun a => f a ≠ g a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hne
    intro a
    have ha :
        a ∉ (Finset.univ : Finset L).filter
          fun b => f b ≠ g b := by
      rw [hempty]
      simp
    simpa using ha
  let D : Finset L :=
    (Finset.univ : Finset L).filter fun a => f a ≠ g a
  let d : L := D.max' hnonempty
  have hdD : d ∈ D :=
    Finset.max'_mem D hnonempty
  have hdne : f d ≠ g d := by
    exact (Finset.mem_filter.mp hdD).2
  have hdmax :
      ∀ a ∈ D, a ≤ d := by
    intro a ha
    exact Finset.le_max' D a ha
  rcases lt_or_gt_of_ne
      (show (f d).1 ≠ (g d).1 from
        fun h => hdne (Subtype.ext h)) with hfg | hgf
  · let a : L := g.symm (f d)
    change (f d).1 < (g d).1 at hfg
    have hga : g a = f d :=
      g.apply_symm_apply (f d)
    have had : a ≠ d := by
      intro had
      apply hdne
      calc
        f d = g a := hga.symm
        _ = g d := congrArg g had
    have hadlt : a < d := by
      by_contra hnot
      have hdalt : d < a :=
        lt_of_le_of_ne (le_of_not_gt hnot) had.symm
      have haNot : a ∉ D := by
        intro haD
        exact (not_lt_of_ge (hdmax a haD)) hdalt
      have hfa : f a = g a := by
        simpa [D] using haNot
      have hfad : f a = f d := hfa.trans hga
      exact had (f.injective hfad)
    change a.1 < d.1 at hadlt
    have hlam := hg_laminar had
    have hlam' :
        ReductionIntervalsLaminar
          (a.1, (f d).1) (d.1, (g d).1) := by
      simpa only [hga] using hlam
    change
      (f d).1 < d.1 ∨
        (g d).1 < a.1 ∨
        (a.1 < d.1 ∧ (g d).1 < (f d).1) ∨
        (d.1 < a.1 ∧ (f d).1 < (g d).1)
      at hlam'
    have hdf := hf_lt d
    change d.1 < (f d).1 at hdf
    rcases hlam' with hlam | hlam | hlam | hlam
    · omega
    · omega
    · omega
    · omega
  · let a : L := f.symm (g d)
    change (g d).1 < (f d).1 at hgf
    have hfa : f a = g d :=
      f.apply_symm_apply (g d)
    have had : a ≠ d := by
      intro had
      apply hdne
      calc
        f d = f a := (congrArg f had).symm
        _ = g d := hfa
    have hadlt : a < d := by
      by_contra hnot
      have hdalt : d < a :=
        lt_of_le_of_ne (le_of_not_gt hnot) had.symm
      have haNot : a ∉ D := by
        intro haD
        exact (not_lt_of_ge (hdmax a haD)) hdalt
      have hga : g a = f a := by
        symm
        simpa [D] using haNot
      have hgad : g a = g d := hga.trans hfa
      exact had (g.injective hgad)
    change a.1 < d.1 at hadlt
    have hlam := hf_laminar had
    have hlam' :
        ReductionIntervalsLaminar
          (a.1, (g d).1) (d.1, (f d).1) := by
      simpa only [hfa] using hlam
    change
      (g d).1 < d.1 ∨
        (f d).1 < a.1 ∨
        (a.1 < d.1 ∧ (f d).1 < (g d).1) ∨
        (d.1 < a.1 ∧ (g d).1 < (f d).1)
      at hlam'
    have hdg := hg_lt d
    change d.1 < (g d).1 at hdg
    rcases hlam' with hlam | hlam | hlam | hlam
    · omega
    · omega
    · omega
    · omega

/-! ## Rigidity consequences for extraction -/

/-- Equality of finsets induces the value-preserving equivalence of their
element subtypes. -/
def finsetSubtypeEquivOfEq
    {α : Type*} [DecidableEq α]
    {A B : Finset α} (h : A = B) :
    A ≃ B where
  toFun a := ⟨a.1, by simpa only [← h] using a.2⟩
  invFun b := ⟨b.1, by simpa only [h] using b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem finsetSubtypeEquivOfEq_apply_val
    {α : Type*} [DecidableEq α]
    {A B : Finset α} (h : A = B) (a : A) :
    (finsetSubtypeEquivOfEq h a).1 = a.1 :=
  rfl

/-- Transport the endpoint matching of `κ'` back to the endpoint subtype
of `κ`. -/
def transportedExtractedEndpointEquiv
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hleft : leftEndpoints κ = leftEndpoints κ')
    (hright : rightEndpoints κ = rightEndpoints κ') :
    leftEndpoints κ ≃ rightEndpoints κ :=
  (finsetSubtypeEquivOfEq hleft).trans
    ((extractedEndpointEquiv κ').trans
      (finsetSubtypeEquivOfEq hright).symm)

@[simp]
theorem transportedExtractedEndpointEquiv_apply_val
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hleft : leftEndpoints κ = leftEndpoints κ')
    (hright : rightEndpoints κ = rightEndpoints κ')
    (a : leftEndpoints κ) :
    (transportedExtractedEndpointEquiv
      κ κ' hleft hright a).1 =
      (extractedEndpointEquiv κ'
        (finsetSubtypeEquivOfEq hleft a)).1 :=
  rfl

/-- Equal endpoint sets force equality after the canonical subtype
transport. -/
theorem extractedEndpointEquiv_eq_transport
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hleft : leftEndpoints κ = leftEndpoints κ')
    (hright : rightEndpoints κ = rightEndpoints κ') :
    extractedEndpointEquiv κ =
      transportedExtractedEndpointEquiv
        κ κ' hleft hright := by
  apply rightOrientedLaminarEquiv_unique
  · exact extractedEndpointEquiv_lt κ
  · intro a
    change a.1 <
      (extractedEndpointEquiv κ'
        (finsetSubtypeEquivOfEq hleft a)).1
    simpa only [finsetSubtypeEquivOfEq_apply_val] using
      extractedEndpointEquiv_lt κ'
        (finsetSubtypeEquivOfEq hleft a)
  · exact fun {_a _d} had =>
      extractedEndpointEquiv_laminar κ had
  · intro a d had
    have had' :
        finsetSubtypeEquivOfEq hleft a ≠
          finsetSubtypeEquivOfEq hleft d :=
      (finsetSubtypeEquivOfEq hleft).injective.ne had
    have hlam :=
      extractedEndpointEquiv_laminar κ' had'
    simpa only [finsetSubtypeEquivOfEq_apply_val,
      transportedExtractedEndpointEquiv_apply_val] using hlam

/-- Every extracted interval is the graph of the endpoint equivalence. -/
theorem mem_extract_iff_exists_extractedEndpoint
    {m : ℕ} (κ : PartialPairing (Fin m))
    (p : Fin m × Fin m) :
    p ∈ extract κ ↔
      ∃ a : leftEndpoints κ,
        p =
          (a.1, (extractedEndpointEquiv κ a).1) := by
  constructor
  · intro hp
    have haMem : p.1 ∈ leftEndpoints κ := by
      unfold leftEndpoints
      rw [List.mem_toFinset]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    let a : leftEndpoints κ := ⟨p.1, haMem⟩
    have hchosen :
        extractedPairOfLeftEndpoint κ a = p := by
      apply extractedPair_eq_of_fst_eq κ
      · exact extractedPairOfLeftEndpoint_mem κ a
      · exact hp
      · exact extractedPairOfLeftEndpoint_fst κ a
    refine ⟨a, ?_⟩
    apply Prod.ext
    · rfl
    · change p.2 =
        (extractedPairOfLeftEndpoint κ a).2
      exact congrArg Prod.snd hchosen.symm
  · rintro ⟨a, rfl⟩
    have hp :=
      extractedPairOfLeftEndpoint_mem κ a
    have hpair :
        extractedPairOfLeftEndpoint κ a =
          (a.1, (extractedEndpointEquiv κ a).1) := by
      apply Prod.ext
      · exact extractedPairOfLeftEndpoint_fst κ a
      · rfl
    rwa [hpair] at hp

/-- Equality of endpoint sets transports membership in the extraction
interval family. -/
theorem mem_extract_of_endpointSets_eq
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hleft : leftEndpoints κ = leftEndpoints κ')
    (hright : rightEndpoints κ = rightEndpoints κ')
    {p : Fin m × Fin m}
    (hp : p ∈ extract κ) :
    p ∈ extract κ' := by
  obtain ⟨a, rfl⟩ :=
    (mem_extract_iff_exists_extractedEndpoint κ p).mp hp
  let a' : leftEndpoints κ' :=
    finsetSubtypeEquivOfEq hleft a
  have hequiv :=
    extractedEndpointEquiv_eq_transport
      κ κ' hleft hright
  have happly :=
    congrArg (fun e : leftEndpoints κ ≃ rightEndpoints κ =>
      e a) hequiv
  have hrightValue :
      (extractedEndpointEquiv κ a).1 =
        (extractedEndpointEquiv κ' a').1 := by
    exact congrArg Subtype.val happly
  apply
    (mem_extract_iff_exists_extractedEndpoint κ'
      (a.1, (extractedEndpointEquiv κ a).1)).mpr
  refine ⟨a', ?_⟩
  apply Prod.ext
  · rfl
  · exact hrightValue

/-- The interval lists attached to equal endpoint signatures contain exactly
the same intervals.  Their recursion order is irrelevant for all commutative
Green products used in the closed formula. -/
theorem extract_perm_of_endpointSets_eq
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hleft : leftEndpoints κ = leftEndpoints κ')
    (hright : rightEndpoints κ = rightEndpoints κ') :
    List.Perm (extract κ) (extract κ') := by
  apply
    (List.perm_ext_iff_of_nodup
      (extract_nodup κ) (extract_nodup κ')).mpr
  intro p
  constructor
  · exact mem_extract_of_endpointSets_eq
      κ κ' hleft hright
  · exact mem_extract_of_endpointSets_eq
      κ' κ hleft.symm hright.symm

/-- Reduction endpoint signatures determine the extraction interval family
up to the immaterial list order. -/
theorem extract_perm_of_reductionEndpointSignature_eq
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hsignature :
      reductionEndpointSignature κ =
        reductionEndpointSignature κ') :
    List.Perm (extract κ) (extract κ') := by
  apply extract_perm_of_endpointSets_eq κ κ'
  · exact congrArg Prod.fst hsignature
  · exact congrArg Prod.snd hsignature

/-- Replaced chain-edge sets depend only on the extraction interval family,
not on its list order. -/
theorem extractedRightEdges_eq_of_extract_perm
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hperm : List.Perm (extract κ) (extract κ')) :
    extractedRightEdges κ = extractedRightEdges κ' := by
  unfold extractedRightEdges
  exact
    List.toFinset_eq_of_perm _ _
      (hperm.map extractedRightEdge)

/-- The commutative Green skeleton is invariant under a permutation of the
extraction interval list. -/
theorem renormalizedGreenSkeleton_eq_of_extract_perm
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hperm : List.Perm (extract κ) (extract κ')) :
    renormalizedGreenSkeleton κ =
      renormalizedGreenSkeleton κ' := by
  funext x
  unfold renormalizedGreenSkeleton
  rw [extractedRightEdges_eq_of_extract_perm κ κ' hperm]
  apply congrArg₂ (· * ·) rfl
  exact
    (hperm.map fun p =>
      originalGreenEdge x (extractedRightEdge p) -
        (greenFn
          (x (varIdx p.1) -
            x (extractedRightEdge p).succ) : ℂ)).prod_eq

/-- Endpoint signatures therefore determine the entire signed Green
skeleton used in the closed renormalized integrand. -/
theorem renormalizedGreenSkeleton_eq_of_reductionEndpointSignature_eq
    {m : ℕ} (κ κ' : PartialPairing (Fin m))
    (hsignature :
      reductionEndpointSignature κ =
        reductionEndpointSignature κ') :
    renormalizedGreenSkeleton κ =
      renormalizedGreenSkeleton κ' :=
  renormalizedGreenSkeleton_eq_of_extract_perm κ κ'
    (extract_perm_of_reductionEndpointSignature_eq
      κ κ' hsignature)

end

end Anderson4D
