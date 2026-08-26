import Anderson4D.DetParametrix.Paper42_Moment.R324TailLedgerClosure

/-!
# The last chain slot: splitting the tail external point off the headless integrand

`r324DetHeadless ρ ε m κ (assemble x y v)` reads the assembled tuple only
at slots `≥ 1`, and the *tail* external point `y` sits at the last slot
`m + 1`.  Exactly one factor of the headless integrand touches that slot:

* the last chain edge `greenFn (v_{m-1} - y)`, unless the slot is
  excluded, i.e. unless some extracted pair `p` has `p.2.val + 1 = m`;
* in that case the difference factor of that pair,
  `greenFn (v_{m-1} - y) - greenFn (v_{p.1} - y)`.

The right endpoints of `extract κ` are pairwise distinct
(`extract_map_snd_nodup`), so there is **at most one** such pair: the two
cases above are exhaustive and mutually exclusive, and in both the
`y`-dependence is the single kernel `r324BetaTailKernel`.  Everything else
is `r324DetTailless`, which reads only the internal variables.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The tail pair -/

/-- The last internal vertex `v_{m-1}`, the fixed end of the tail leg. -/
def r324TailLastIdx {m : ℕ} (hm : 0 < m) : Fin m := ⟨m - 1, by omega⟩

/-- The extracted pairs whose difference factor touches the tail external
slot `m + 1`. -/
def r324TailPairs {m : ℕ} (κ : PartialPairing (Fin m)) :
    List (Fin m × Fin m) :=
  (extract κ).filter fun p => decide (p.2.val + 1 = m)

/-- The extracted pairs whose difference factor is tail free. -/
def r324TailRest {m : ℕ} (κ : PartialPairing (Fin m)) :
    List (Fin m × Fin m) :=
  (extract κ).filter fun p => !decide (p.2.val + 1 = m)

/-- The shortcut anchor of the tail leg: `some ℓ` when the last chain slot
has been replaced by the difference factor of the extracted pair `(ℓ, m-1)`,
and `none` when the last chain edge survives. -/
def r324TailAnchor {m : ℕ} (κ : PartialPairing (Fin m)) : Option (Fin m) :=
  (r324TailPairs κ).head?.map Prod.fst

/-- **The tail leg.**  The only factor of the headless integrand that sees
the tail external point. -/
def r324BetaTailKernel {m : ℕ} (hm : 0 < m) (κ : PartialPairing (Fin m))
    (v : Fin m → T4) (y : T4) : ℝ :=
  greenFn (v (r324TailLastIdx hm) - y) -
    (match r324TailAnchor κ with
      | none => 0
      | some b => greenFn (v b - y))

/-! ## At most one tail pair -/

theorem r324TailPairs_mem {m : ℕ} {κ : PartialPairing (Fin m)}
    {p : Fin m × Fin m} (hp : p ∈ r324TailPairs κ) :
    p ∈ extract κ ∧ p.2.val + 1 = m := by
  unfold r324TailPairs at hp
  rw [List.mem_filter] at hp
  exact ⟨hp.1, by simpa using hp.2⟩

/-- The extracted right endpoints are distinct, so a tail pair is unique. -/
theorem r324TailPairs_length_le {m : ℕ} (κ : PartialPairing (Fin m)) :
    (r324TailPairs κ).length ≤ 1 := by
  match hL : r324TailPairs κ with
  | [] => simp
  | [_] => simp
  | p :: q :: t =>
    exfalso
    have hnd : (r324TailPairs κ).Nodup :=
      ((extract_map_snd_nodup κ).of_map).filter _
    rw [hL] at hnd
    have hpq : p ≠ q := by
      simp only [List.nodup_cons, List.mem_cons] at hnd
      exact fun h => hnd.1 (Or.inl h)
    have hp := r324TailPairs_mem (κ := κ) (p := p) (by rw [hL]; simp)
    have hq := r324TailPairs_mem (κ := κ) (p := q) (by rw [hL]; simp)
    have hsnd : p.2 = q.2 := Fin.ext (by omega)
    exact hpq (List.inj_on_of_nodup_map (extract_map_snd_nodup κ)
      hp.1 hq.1 hsnd)

/-- The tail-pair list is either empty or a single pair. -/
theorem r324TailPairs_eq {m : ℕ} (κ : PartialPairing (Fin m)) :
    r324TailPairs κ = [] ∨
      ∃ p : Fin m × Fin m, r324TailPairs κ = [p] := by
  have h := r324TailPairs_length_le κ
  match hL : r324TailPairs κ with
  | [] => exact Or.inl rfl
  | [p] => exact Or.inr ⟨p, rfl⟩
  | _ :: _ :: _ => rw [hL] at h; simp at h

/-! ## Index bookkeeping at the last chain slot -/

theorem r324Tail_succ_val {m : ℕ} (hm : 0 < m) :
    ((r324TailLastIdx hm).succ : Fin (m + 1)).val = m := by
  simp [r324TailLastIdx]
  omega

theorem r324Tail_castSucc_eq {m : ℕ} (hm : 0 < m) :
    ((((r324TailLastIdx hm).succ : Fin (m + 1)).castSucc : Fin (m + 2))) =
      varIdx (r324TailLastIdx hm) :=
  Fin.ext (by simp [r324TailLastIdx, varIdx])

theorem r324Tail_succ_eq {m : ℕ} (hm : 0 < m) :
    ((((r324TailLastIdx hm).succ : Fin (m + 1)).succ : Fin (m + 2))) =
      Fin.last (m + 1) :=
  Fin.ext (by simp [r324TailLastIdx]; omega)

/-- The last chain slot is excluded exactly when a tail pair exists. -/
theorem r324Tail_mem_excluded_iff {m : ℕ} (κ : PartialPairing (Fin m)) :
    m ∈ ((extract κ).map fun p => p.2.val + 1) ↔ r324TailPairs κ ≠ [] := by
  constructor
  · intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨p, hp, hval⟩ := hmem
    intro hnil
    unfold r324TailPairs at hnil
    rw [List.filter_eq_nil_iff] at hnil
    exact absurd hval (by simpa using hnil p hp)
  · intro hne
    unfold r324TailPairs at hne
    rw [Ne, List.filter_eq_nil_iff] at hne
    push Not at hne
    obtain ⟨p, hp, hval⟩ := hne
    exact List.mem_map.2 ⟨p, hp, by simpa using hval⟩

/-! ## The tail-free remainder -/

/-- `r324DetHeadless` with the tail leg deleted as well: the last chain
edge is dropped and the difference factors are restricted to the pairs
that do not reach the tail slot.  Every remaining factor reads the
assembled tuple only at the internal slots `1, …, m`. -/
def r324DetTailless
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) : ℝ :=
  (∏ e : Fin m,
      if e.val + 1 = m then 1
      else if (e.succ : Fin (m + 1)).val ∈
          ((extract κ).map fun p => p.2.val + 1) then 1
      else greenFn (xt (e.succ : Fin (m + 1)).castSucc -
        xt (e.succ : Fin (m + 1)).succ)) *
    ((r324TailRest κ).map (diffFactor xt)).prod *
    ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
      ρ.etaEpsT4 ε (xt (varIdx i) - xt (varIdx (κ i)))

/-- The tail-free remainder reads neither the head slot `0` nor the tail
slot `m + 1`. -/
theorem r324DetTailless_congr
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (κ : PartialPairing (Fin m))
    {xt xt' : Fin (m + 2) → T4}
    (h : ∀ j : Fin (m + 2), j.val ≠ 0 → j.val ≠ m + 1 → xt j = xt' j) :
    r324DetTailless ρ ε m κ xt = r324DetTailless ρ ε m κ xt' := by
  have hvar : ∀ i : Fin m, xt (varIdx i) = xt' (varIdx i) := by
    intro i
    have := i.isLt
    exact h _ (by simp) (by simp; omega)
  have hdiff : ∀ p ∈ r324TailRest κ,
      diffFactor (m := m) xt p = diffFactor (m := m) xt' p := by
    intro p hp
    have hne : p.2.val + 1 ≠ m := by
      unfold r324TailRest at hp
      rw [List.mem_filter] at hp
      simpa using hp.2
    have h2 := p.2.isLt
    have hslot : xt ⟨p.2.val + 2, by omega⟩ = xt' ⟨p.2.val + 2, by omega⟩ :=
      h _ (by simp) (by simp; omega)
    unfold diffFactor
    rw [hvar p.2, hvar p.1, hslot]
  have hchain : ∀ e : Fin m,
      (if e.val + 1 = m then 1
        else if (e.succ : Fin (m + 1)).val ∈
            ((extract κ).map fun p => p.2.val + 1) then 1
        else greenFn (xt (e.succ : Fin (m + 1)).castSucc -
          xt (e.succ : Fin (m + 1)).succ)) =
      (if e.val + 1 = m then 1
        else if (e.succ : Fin (m + 1)).val ∈
            ((extract κ).map fun p => p.2.val + 1) then 1
        else greenFn (xt' (e.succ : Fin (m + 1)).castSucc -
          xt' (e.succ : Fin (m + 1)).succ)) := by
    intro e
    by_cases hlast : e.val + 1 = m
    · rw [if_pos hlast, if_pos hlast]
    have he := e.isLt
    have ha : xt (e.succ : Fin (m + 1)).castSucc =
        xt' (e.succ : Fin (m + 1)).castSucc :=
      h _ (by simp) (by simp; omega)
    have hb : xt (e.succ : Fin (m + 1)).succ =
        xt' (e.succ : Fin (m + 1)).succ :=
      h _ (by simp) (by simp; omega)
    rw [ha, hb]
  have hcov : (∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
        ρ.etaEpsT4 ε (xt (varIdx i) - xt (varIdx (κ i)))) =
      ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
        ρ.etaEpsT4 ε (xt' (varIdx i) - xt' (varIdx (κ i))) :=
    Finset.prod_congr rfl fun i _ => by rw [hvar i, hvar (κ i)]
  unfold r324DetTailless
  rw [Finset.prod_congr rfl fun e _ => hchain e, hcov,
    List.map_congr_left hdiff]

/-! ## The split -/

/-- The difference factor of a tail pair *is* the tail leg. -/
theorem diffFactor_assemble_tail {m : ℕ} (hm : 0 < m) (x y : T4)
    (v : Fin m → T4) (p : Fin m × Fin m) (hp : p.2.val + 1 = m) :
    diffFactor (assemble x y v) p =
      greenFn (v (r324TailLastIdx hm) - y) - greenFn (v p.1 - y) := by
  have h2 : (⟨p.2.val + 2, by have := p.2.isLt; omega⟩ : Fin (m + 2)) =
      Fin.last (m + 1) := Fin.ext (by simp; omega)
  have hv : v p.2 = v (r324TailLastIdx hm) :=
    congrArg v (Fin.ext (by simp [r324TailLastIdx]; omega))
  unfold diffFactor
  rw [h2, assemble_last, assemble_varIdx, assemble_varIdx, hv]

/-- **The tail split.**  The headless integrand is the tail leg times a
tail-free remainder; the tail leg is the *only* factor that sees the tail
external point. -/
theorem r324DetHeadless_eq_tail_mul_tailless
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (x y : T4) (v : Fin m → T4) :
    r324DetHeadless ρ ε m κ (assemble x y v) =
      r324BetaTailKernel hm κ v y *
        r324DetTailless ρ ε m κ (assemble x y v) := by
  classical
  have hlast : (r324TailLastIdx hm).val + 1 = m := by
    simp [r324TailLastIdx]; omega
  have hchain :
      (∏ e : Fin m,
        if (e.succ : Fin (m + 1)).val ∈
            ((extract κ).map fun p => p.2.val + 1) then 1
        else greenFn (assemble x y v (e.succ : Fin (m + 1)).castSucc -
          assemble x y v (e.succ : Fin (m + 1)).succ)) =
        (if m ∈ ((extract κ).map fun p => p.2.val + 1) then 1
          else greenFn (v (r324TailLastIdx hm) - y)) *
        ∏ e : Fin m,
          (if e.val + 1 = m then 1
            else if (e.succ : Fin (m + 1)).val ∈
              ((extract κ).map fun p => p.2.val + 1) then 1
            else greenFn (assemble x y v (e.succ : Fin (m + 1)).castSucc -
              assemble x y v (e.succ : Fin (m + 1)).succ)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (r324TailLastIdx hm)),
      ← Finset.mul_prod_erase (Finset.univ : Finset (Fin m)) _
        (Finset.mem_univ (r324TailLastIdx hm)), if_pos hlast, one_mul]
    congr 1
    · rw [r324Tail_succ_val hm, r324Tail_castSucc_eq hm, r324Tail_succ_eq hm,
        assemble_varIdx, assemble_last]
    · refine Finset.prod_congr rfl fun e he => ?_
      have hne : e ≠ r324TailLastIdx hm := (Finset.mem_erase.1 he).1
      have hval : e.val + 1 ≠ m := fun h =>
        hne (Fin.ext (by simp [r324TailLastIdx]; omega))
      rw [if_neg hval]
  have hdiff :
      ((extract κ).map (diffFactor (assemble x y v))).prod =
        ((r324TailPairs κ).map (diffFactor (assemble x y v))).prod *
          ((r324TailRest κ).map (diffFactor (assemble x y v))).prod := by
    unfold r324TailPairs r324TailRest
    rw [← List.prod_append, ← List.map_append]
    exact ((List.filter_append_perm
      (fun p : Fin m × Fin m => decide (p.2.val + 1 = m))
      (extract κ)).map _).prod_eq.symm
  have hfactor :
      (if m ∈ ((extract κ).map fun p => p.2.val + 1) then (1 : ℝ)
        else greenFn (v (r324TailLastIdx hm) - y)) *
        ((r324TailPairs κ).map (diffFactor (assemble x y v))).prod =
      r324BetaTailKernel hm κ v y := by
    rcases r324TailPairs_eq κ with hnil | ⟨p, hp⟩
    · rw [if_neg (by rw [r324Tail_mem_excluded_iff]; simp [hnil]), hnil]
      unfold r324BetaTailKernel r324TailAnchor
      rw [hnil]
      simp
    · rw [if_pos (by rw [r324Tail_mem_excluded_iff, hp]; simp), hp, one_mul]
      have hmem := r324TailPairs_mem (κ := κ) (p := p) (by rw [hp]; simp)
      unfold r324BetaTailKernel r324TailAnchor
      rw [hp]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, List.head?_cons, Option.map_some]
      exact diffFactor_assemble_tail hm x y v p hmem.2
  unfold r324DetHeadless r324DetTailless
  rw [hchain, hdiff, ← hfactor]
  ring

/-- The tail-free remainder as a function of the internal variables
alone. -/
def r324DetTaillessV
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (κ : PartialPairing (Fin m))
    (v : Fin m → T4) : ℝ :=
  r324DetTailless ρ ε m κ (assemble 0 0 v)

theorem r324DetTailless_assemble_eq
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (κ : PartialPairing (Fin m))
    (x y : T4) (v : Fin m → T4) :
    r324DetTailless ρ ε m κ (assemble x y v) =
      r324DetTaillessV ρ ε m κ v := by
  refine r324DetTailless_congr ρ ε m κ fun j hj0 hjl => ?_
  have hj := j.isLt
  have hjv : j = varIdx ⟨j.val - 1, by omega⟩ := Fin.ext (by simp; omega)
  rw [hjv, assemble_varIdx, assemble_varIdx]

/-- **The tail split, in tail-free form.** -/
theorem r324DetHeadless_eq_tail_mul_taillessV
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (x y : T4) (v : Fin m → T4) :
    r324DetHeadless ρ ε m κ (assemble x y v) =
      r324BetaTailKernel hm κ v y * r324DetTaillessV ρ ε m κ v := by
  rw [r324DetHeadless_eq_tail_mul_tailless ρ ε hm κ x y v,
    r324DetTailless_assemble_eq]

/-! ## The `β`-Fourier coefficient of the tail leg -/

theorem charT4_point_zero (k : Z4) : charT4 k (0 : T4) = 1 := by
  have h : charT4 k (0 : T4) * charT4 k (0 : T4) = charT4 k 0 * 1 := by
    rw [← charT4_add_argument, add_zero, mul_one]
  have hne : charT4 k (0 : T4) ≠ 0 := by
    intro h0
    have hn := norm_charT4 k (0 : T4)
    rw [h0] at hn
    simp at hn
  exact mul_left_cancel₀ hne h

instance instIsNegInvariantVolumeT4 : (volume : Measure T4).IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_regular volume

theorem integrable_greenFn_sub_left (u : T4) :
    Integrable (fun y : T4 => greenFn (u - y)) paperMeasure := by
  rw [paperMeasure_eq_volume]
  have h := integrable_greenFn_paper
  rw [paperMeasure_eq_volume] at h
  exact h.comp_sub_left u

/-- **The reversed Green mode.**  The Green kernel is a bona fide
convolution kernel: harvesting a character against `G(u - ·)` gives the
same translated mode as against `G(· - u)`. -/
theorem integral_charT4_mul_greenFn_sub_left (k : Z4) (u : T4) :
    (∫ y : T4, charT4 k y * ((greenFn (u - y) : ℝ) : ℂ) ∂paperMeasure) =
      translatedGreenMode k u := by
  have hzero : (∫ z : T4, charT4 (-k) z * ((greenFn z : ℝ) : ℂ)
      ∂paperMeasure) = ((paperSecondOrderModeDecay k : ℝ) : ℂ) := by
    have h : (∫ z : T4, charT4 (-k) z * ((greenFn (z - 0) : ℝ) : ℂ)
        ∂paperMeasure) = translatedGreenMode (-k) 0 := rfl
    simp only [sub_zero] at h
    rw [h, translatedGreenMode_eq_paper, charT4_point_zero, one_mul,
      paperSecondOrderModeDecay_neg]
  have hself : (∫ y : T4, charT4 k y * ((greenFn (u - y) : ℝ) : ℂ)
      ∂paperMeasure) =
      ∫ z : T4, charT4 k (u - z) * ((greenFn z : ℝ) : ℂ) ∂paperMeasure := by
    rw [paperMeasure_eq_volume]
    refine Eq.trans ?_ (integral_sub_left_eq_self
      (fun z : T4 => charT4 k (u - z) * ((greenFn z : ℝ) : ℂ)) volume u)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [sub_sub_cancel]
  rw [hself]
  have hpt : ∀ z : T4, charT4 k (u - z) * ((greenFn z : ℝ) : ℂ) =
      charT4 k u * (charT4 (-k) z * ((greenFn z : ℝ) : ℂ)) := by
    intro z
    rw [charT4_sub_argument]
    ring
  simp only [hpt]
  rw [integral_const_mul, hzero, translatedGreenMode_eq_paper]

/-- **The transported tail character.**  What the tail leg becomes once
its `β`-harvest has been performed: the `β` character at the two candidate
tail anchors, *inside* the internal integral.  This is the object the
central bracket is built from — the mode `β` now sits on the internal
vertices, against the covariance symbols. -/
def r324BetaTailChar {m : ℕ} (β : Z4) (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (v : Fin m → T4) : ℂ :=
  charT4 β (v (r324TailLastIdx hm)) -
    (match r324TailAnchor κ with
      | none => 0
      | some b => charT4 β (v b))

/-- The transported tail character is a difference of at most two
unimodular characters. -/
theorem norm_r324BetaTailChar_le {m : ℕ} (β : Z4) (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (v : Fin m → T4) :
    ‖r324BetaTailChar β hm κ v‖ ≤ 2 := by
  unfold r324BetaTailChar
  rcases hA : r324TailAnchor κ with _ | b
  · simp [norm_charT4]
  · refine le_trans (norm_sub_le _ _) ?_
    rw [norm_charT4, norm_charT4]
    norm_num

theorem integrable_charT4_mul_greenFn_sub_left (k : Z4) (u : T4) :
    Integrable
      (fun y : T4 => charT4 k y * ((greenFn (u - y) : ℝ) : ℂ))
      paperMeasure :=
  (integrable_greenFn_sub_left u).ofReal.bdd_mul (c := 1)
    (continuous_charT4 k).measurable.aestronglyMeasurable
    (.of_forall fun q => by rw [norm_charT4])

theorem integrable_charT4_mul_r324BetaTailKernel
    {m : ℕ} (β : Z4) (hm : 0 < m) (κ : PartialPairing (Fin m))
    (v : Fin m → T4) :
    Integrable
      (fun y : T4 => charT4 β y * ((r324BetaTailKernel hm κ v y : ℝ) : ℂ))
      paperMeasure := by
  rcases hA : r324TailAnchor κ with _ | b
  · refine (integrable_charT4_mul_greenFn_sub_left β
      (v (r324TailLastIdx hm))).congr (.of_forall fun y => ?_)
    simp [r324BetaTailKernel, hA]
  · refine ((integrable_charT4_mul_greenFn_sub_left β
      (v (r324TailLastIdx hm))).sub
      (integrable_charT4_mul_greenFn_sub_left β (v b))).congr
      (.of_forall fun y => ?_)
    simp only [Pi.sub_apply, r324BetaTailKernel, hA]
    push_cast
    ring

/-- **The tail harvest.**  The `β`-Fourier coefficient of the tail leg is
`⟨β⟩⁻²` times the transported tail character — an *identity*: the whole
second-order decay factors out and the entity-dependent anchor survives as
a character, not as a constant `2`. -/
theorem integral_charT4_mul_r324BetaTailKernel
    {m : ℕ} (β : Z4) (hm : 0 < m) (κ : PartialPairing (Fin m))
    (v : Fin m → T4) :
    (∫ y : T4, charT4 β y * ((r324BetaTailKernel hm κ v y : ℝ) : ℂ)
      ∂paperMeasure) =
      ((paperSecondOrderModeDecay β : ℝ) : ℂ) * r324BetaTailChar β hm κ v := by
  rcases hA : r324TailAnchor κ with _ | b
  · have hpt : ∀ y : T4,
        charT4 β y * ((r324BetaTailKernel hm κ v y : ℝ) : ℂ) =
          charT4 β y * ((greenFn (v (r324TailLastIdx hm) - y) : ℝ) : ℂ) := by
      intro y; simp [r324BetaTailKernel, hA]
    simp only [hpt, r324BetaTailChar, hA]
    rw [integral_charT4_mul_greenFn_sub_left, translatedGreenMode_eq_paper]
    ring
  · have hpt : ∀ y : T4,
        charT4 β y * ((r324BetaTailKernel hm κ v y : ℝ) : ℂ) =
          charT4 β y * ((greenFn (v (r324TailLastIdx hm) - y) : ℝ) : ℂ) -
            charT4 β y * ((greenFn (v b - y) : ℝ) : ℂ) := by
      intro y
      simp only [r324BetaTailKernel, hA]
      push_cast
      ring
    simp only [hpt, r324BetaTailChar, hA]
    rw [integral_sub (integrable_charT4_mul_greenFn_sub_left β _)
        (integrable_charT4_mul_greenFn_sub_left β _),
      integral_charT4_mul_greenFn_sub_left,
      integral_charT4_mul_greenFn_sub_left,
      translatedGreenMode_eq_paper, translatedGreenMode_eq_paper]
    ring


/-! ## The left copy: harvesting `y` -/

/-- The summed core after the two head Green edges *and* the left tail leg
have been harvested: the left tail leg has become the transported
character `r324BetaTailChar`, still inside the entity sum. -/
def r324BetaLeftTransported
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m))
    (w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  ∑ e ∈ F,
    r324BetaTailChar β hm e.1 (fun i => v (leftMomentIndex i)) *
      ((r324DetTaillessV ρ ε m e.1 (fun i => v (leftMomentIndex i)) *
        r324DetHeadless ρ ε m e.2.1
          (assemble w w fun i => v (rightMomentIndex i)) *
        momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v : ℝ) : ℂ)

theorem r324Beta_charY_pointwise
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m))
    (y w : T4) (v : Fin (2 * m) → T4) :
    charT4 β y * ((r324CMDoubleHeadlessCore ρ ε m F y w v : ℝ) : ℂ) =
      ∑ e ∈ F,
        (charT4 β y *
            ((r324BetaTailKernel hm e.1
              (fun i => v (leftMomentIndex i)) y : ℝ) : ℂ)) *
          ((r324DetTaillessV ρ ε m e.1 (fun i => v (leftMomentIndex i)) *
            r324DetHeadless ρ ε m e.2.1
              (assemble w w fun i => v (rightMomentIndex i)) *
            momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v : ℝ) : ℂ) := by
  unfold r324CMDoubleHeadlessCore
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _he => ?_
  rw [r324DetHeadless_eq_tail_mul_taillessV ρ ε hm e.1 y y
    (fun i => v (leftMomentIndex i))]
  push_cast
  ring

theorem r324Beta_integrable_charY
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (β : Z4) (hm : 0 < m)
    (e : MomentContraction m) (w : T4) (v : Fin (2 * m) → T4) :
    Integrable
      (fun y : T4 =>
        (charT4 β y *
            ((r324BetaTailKernel hm e.1
              (fun i => v (leftMomentIndex i)) y : ℝ) : ℂ)) *
          ((r324DetTaillessV ρ ε m e.1 (fun i => v (leftMomentIndex i)) *
            r324DetHeadless ρ ε m e.2.1
              (assemble w w fun i => v (rightMomentIndex i)) *
            momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v : ℝ) : ℂ))
      paperMeasure :=
  (integrable_charT4_mul_r324BetaTailKernel β hm e.1 _).mul_const _

/-- **The left tail harvest.**  `⟨β⟩⁻²` factors out of the entity sum
exactly. -/
theorem r324TailBetaCoefficient_eq
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m))
    (s : T4 × (Fin (2 * m) → T4)) :
    r324TailBetaCoefficient ρ ε m β F s =
      ((paperSecondOrderModeDecay β : ℝ) : ℂ) *
        r324BetaLeftTransported ρ ε m β hm F s.1 s.2 := by
  unfold r324TailBetaCoefficient r324BetaLeftTransported
  rw [integral_congr_ae (Filter.Eventually.of_forall fun y =>
      r324Beta_charY_pointwise ρ ε β hm F y s.1 s.2),
    integral_finsetSum _
      (fun e _ => r324Beta_integrable_charY ρ ε β hm e s.1 s.2),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _he => ?_
  rw [integral_mul_const, integral_charT4_mul_r324BetaTailKernel]
  ring

/-! ## The right copy: harvesting `w` -/

/-- **The tail-amputated core with all four external modes transported
inside.**  Both head Green edges and both tail legs have been harvested;
what is left of every entity is the product of its two tail-free
remainders and its internal covariance product, weighted by the two
transported tail characters.  The entity sum is still *inside*. -/
def r324BetaQuadCore
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m))
    (v : Fin (2 * m) → T4) : ℂ :=
  ∑ e ∈ F,
    r324BetaTailChar β hm e.1 (fun i => v (leftMomentIndex i)) *
      r324BetaTailChar (-β) hm e.2.1 (fun i => v (rightMomentIndex i)) *
      ((r324DetTaillessV ρ ε m e.1 (fun i => v (leftMomentIndex i)) *
        r324DetTaillessV ρ ε m e.2.1 (fun i => v (rightMomentIndex i)) *
        momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v : ℝ) : ℂ)

theorem r324Beta_charW_pointwise
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m))
    (w : T4) (v : Fin (2 * m) → T4) :
    charT4 (-β) w * r324BetaLeftTransported ρ ε m β hm F w v =
      ∑ e ∈ F,
        (charT4 (-β) w *
            ((r324BetaTailKernel hm e.2.1
              (fun i => v (rightMomentIndex i)) w : ℝ) : ℂ)) *
          (r324BetaTailChar β hm e.1 (fun i => v (leftMomentIndex i)) *
            ((r324DetTaillessV ρ ε m e.1 (fun i => v (leftMomentIndex i)) *
              r324DetTaillessV ρ ε m e.2.1 (fun i => v (rightMomentIndex i)) *
              momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v : ℝ) :
                ℂ)) := by
  unfold r324BetaLeftTransported
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _he => ?_
  rw [r324DetHeadless_eq_tail_mul_taillessV ρ ε hm e.2.1 w w
    (fun i => v (rightMomentIndex i))]
  push_cast
  ring

/-- **The right tail harvest.**  The second `⟨β⟩⁻²` factors out of the
entity sum exactly. -/
theorem r324Beta_integral_w
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m)) (v : Fin (2 * m) → T4) :
    (∫ w : T4, charT4 (-β) w * r324BetaLeftTransported ρ ε m β hm F w v
      ∂paperMeasure) =
      ((paperSecondOrderModeDecay β : ℝ) : ℂ) *
        r324BetaQuadCore ρ ε m β hm F v := by
  unfold r324BetaQuadCore
  rw [integral_congr_ae (Filter.Eventually.of_forall fun w =>
      r324Beta_charW_pointwise ρ ε β hm F w v),
    integral_finsetSum _ (fun e _ =>
      (integrable_charT4_mul_r324BetaTailKernel (-β) hm e.2.1 _).mul_const _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _he => ?_
  rw [integral_mul_const, integral_charT4_mul_r324BetaTailKernel,
    paperSecondOrderModeDecay_neg]
  ring

/-! ## The quadruple harvest -/

/-- **What clause B reduces to on the tail region.**  All four external
characters have been harvested; the two head modes `α` sit transported at
the internal head anchors and the two tail modes `β` sit transported at
the internal tail anchors, all *inside* the internal integral and with the
entity sum inside as well.  The only decay still to be produced is the
central bracket at the conserved mode `α + β`. -/
def r324BetaQuadHarvest
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m)) : ℂ :=
  ∫ v : Fin (2 * m) → T4,
    charT4 α (v (leftMomentIndex ⟨0, hm⟩)) *
        charT4 (-α) (v (rightMomentIndex ⟨0, hm⟩)) *
      r324BetaQuadCore ρ ε m β hm F v
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

theorem r324Beta_integrable_headHarvestIntegrand
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 0 < m) (α β : Z4) (F : Finset (MomentContraction m)) :
    Integrable
      (fun s : T4 × (Fin (2 * m) → T4) =>
        charT4 α (s.2 (leftMomentIndex ⟨0, hm⟩)) *
          charT4 (-α) (s.2 (rightMomentIndex ⟨0, hm⟩)) *
          charT4 (-β) s.1 * r324TailBetaCoefficient ρ ε m β F s)
      (r324TailInnerMeasure m) := by
  have h := r324Tail_integrable_charCore ρ hε hε1 α β F
  unfold r324PhysicalMeasure r324PhysicalRestMeasure at h
  have h3 :=
    h.integral_prod_right.integral_prod_right.integral_prod_right
  have hA : ((paperFourthOrderModeDecay α : ℝ) : ℂ) ≠ 0 := by
    simpa using (paperFourthOrderModeDecay_pos α).ne'
  unfold r324TailInnerMeasure
  refine ((h3.congr (Filter.Eventually.of_forall fun s =>
    r324Tail_inner_xyz ρ ε hm α β F s)).const_mul
      (((paperFourthOrderModeDecay α : ℝ) : ℂ))⁻¹).congr
    (Filter.Eventually.of_forall fun s => ?_)
  simp only [inv_mul_cancel_left₀ hA]

/-- **The `⟨β⟩⁻⁴` harvest, exactly.**  The head-harvested integral is the
*fourth*-order mode decay at `β` times the quadruple harvest.  Like the
head harvest this is an identity, so the remaining decay still multiplies
on: no cancellation has been spent, and the entity sum has never left the
integrand. -/
theorem r324Beta_headHarvest_eq
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 0 < m) (α β : Z4) (F : Finset (MomentContraction m)) :
    r324TailHeadHarvest ρ ε m α β F ⟨0, hm⟩ =
      ((paperFourthOrderModeDecay β : ℝ) : ℂ) *
        r324BetaQuadHarvest ρ ε m α β hm F := by
  have hpt : ∀ s : T4 × (Fin (2 * m) → T4),
      charT4 α (s.2 (leftMomentIndex ⟨0, hm⟩)) *
          charT4 (-α) (s.2 (rightMomentIndex ⟨0, hm⟩)) *
          charT4 (-β) s.1 * r324TailBetaCoefficient ρ ε m β F s =
        ((paperSecondOrderModeDecay β : ℝ) : ℂ) *
          (charT4 α (s.2 (leftMomentIndex ⟨0, hm⟩)) *
            charT4 (-α) (s.2 (rightMomentIndex ⟨0, hm⟩)) *
            (charT4 (-β) s.1 *
              r324BetaLeftTransported ρ ε m β hm F s.1 s.2)) := by
    intro s
    rw [r324TailBetaCoefficient_eq ρ ε β hm F s]
    ring
  have hint := r324Beta_integrable_headHarvestIntegrand ρ hε hε1 hm α β F
  unfold r324TailHeadHarvest
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_const_mul]
  have hswap :
      (∫ s : T4 × (Fin (2 * m) → T4),
        charT4 α (s.2 (leftMomentIndex ⟨0, hm⟩)) *
          charT4 (-α) (s.2 (rightMomentIndex ⟨0, hm⟩)) *
          (charT4 (-β) s.1 *
            r324BetaLeftTransported ρ ε m β hm F s.1 s.2)
        ∂(r324TailInnerMeasure m)) =
      ∫ v : Fin (2 * m) → T4, ∫ w : T4,
        charT4 α (v (leftMomentIndex ⟨0, hm⟩)) *
          charT4 (-α) (v (rightMomentIndex ⟨0, hm⟩)) *
          (charT4 (-β) w * r324BetaLeftTransported ρ ε m β hm F w v)
        ∂paperMeasure ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
    have hint' : Integrable
        (fun s : T4 × (Fin (2 * m) → T4) =>
          charT4 α (s.2 (leftMomentIndex ⟨0, hm⟩)) *
            charT4 (-α) (s.2 (rightMomentIndex ⟨0, hm⟩)) *
            (charT4 (-β) s.1 *
              r324BetaLeftTransported ρ ε m β hm F s.1 s.2))
        (r324TailInnerMeasure m) := by
      have hApos : (0 : ℝ) < paperSecondOrderModeDecay β := by
        unfold paperSecondOrderModeDecay paperModeNormSq
        positivity
      have hA : ((paperSecondOrderModeDecay β : ℝ) : ℂ) ≠ 0 := by
        simpa using hApos.ne'
      refine ((hint.congr (Filter.Eventually.of_forall hpt)).const_mul
        (((paperSecondOrderModeDecay β : ℝ) : ℂ))⁻¹).congr
        (Filter.Eventually.of_forall fun s => ?_)
      simp only [inv_mul_cancel_left₀ hA]
    unfold r324TailInnerMeasure at hint' ⊢
    exact integral_prod_symm _ hint'
  rw [hswap]
  have hinner : ∀ v : Fin (2 * m) → T4,
      (∫ w : T4,
        charT4 α (v (leftMomentIndex ⟨0, hm⟩)) *
          charT4 (-α) (v (rightMomentIndex ⟨0, hm⟩)) *
          (charT4 (-β) w * r324BetaLeftTransported ρ ε m β hm F w v)
        ∂paperMeasure) =
      ((paperSecondOrderModeDecay β : ℝ) : ℂ) *
        (charT4 α (v (leftMomentIndex ⟨0, hm⟩)) *
          charT4 (-α) (v (rightMomentIndex ⟨0, hm⟩)) *
          r324BetaQuadCore ρ ε m β hm F v) := by
    intro v
    rw [integral_const_mul, r324Beta_integral_w]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner),
    integral_const_mul]
  unfold r324BetaQuadHarvest
  rw [paperFourthOrderModeDecay_eq_sq]
  push_cast
  ring

/-! ## The central bracket -/

/-- **The central-bracket ledger.**  Everything the four external
harvests leave: with all four external characters transported to internal
anchors (`α` at `v_{L,0}`, `-α` at `v_{R,0}`, `β` and `-β` at the two tail
anchors) and integrated against the tail-amputated core — entity sum
inside — produce the eighth-order decay at the *conserved* mode `α + β`.

This is the exact residue of clause B on the tail region: by
`r324Beta_headHarvest_eq` together with
`r324Tail_sum_eq_alphaDecay_mul_headHarvest` the clause-B left-hand side
equals `⟨α⟩⁻⁴ ⟨β⟩⁻⁴ · r324BetaQuadHarvest`, both factorizations being
identities. -/
def R324BetaQuadBracketLedger (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        r324CMBracketWeight ε α β ≤ 1 →
          ∀ (F : Finset (MomentContraction m)) (hm : 0 < m),
            ‖r324BetaQuadHarvest ρ ε m α β hm F‖ ≤
              K ^ m * |Real.log ε| ^ (m - 1) *
                eighthOrderFrequencyDecay
                  ‖z4EuclideanFrequency (α + β)‖

/-- **The tail residual from the central-bracket ledger.**  The `⟨β⟩⁻⁴`
harvest is an identity, so the two decays multiply. -/
theorem R324BracketTailResidual_of_quadBracket
    {ρ : SmoothCutoff} {K : ℝ} (h : R324BetaQuadBracketLedger ρ K) :
    R324BracketTailResidual ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap hW F hm
  rw [r324Beta_headHarvest_eq ρ hε hε1 hm α β F, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperFourthOrderModeDecay_nonneg β)]
  calc
    paperFourthOrderModeDecay β *
        ‖r324BetaQuadHarvest ρ ε m α β hm F‖ ≤
        paperFourthOrderModeDecay β *
          (K ^ m * |Real.log ε| ^ (m - 1) *
            eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖) :=
      mul_le_mul_of_nonneg_left
        (h m α β hε hε1 hlog hm2 hcap hW F hm)
        (paperFourthOrderModeDecay_nonneg β)
    _ = K ^ m * |Real.log ε| ^ (m - 1) *
          (paperFourthOrderModeDecay β *
            eighthOrderFrequencyDecay
              ‖z4EuclideanFrequency (α + β)‖) := by ring

/-- **Clause B from clause A and the central-bracket ledger.** -/
theorem R324CappedBracketDensityLedger_of_quadBracket
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (hA : R324CappedDensityLedger ρ K)
    (h : R324BetaQuadBracketLedger ρ K) :
    R324CappedBracketDensityLedger ρ K :=
  R324CappedBracketDensityLedger_of_residual hK hA
    (R324BracketTailResidual_of_quadBracket h)

/-- **The strong capped ledger from the grading and central-bracket
estimates.**  The tail estimate is reduced to one statement
about the tail-amputated core. -/
theorem R324CappedCrossLedgerStrong_of_quadBracket
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (hA : R324CappedDensityLedger ρ K)
    (h : R324BetaQuadBracketLedger ρ K) :
    R324CappedCrossLedgerStrong ρ K :=
  R324CappedCrossLedgerStrong_of_residual hK hA
    (R324BracketTailResidual_of_quadBracket h)

/-- **The full endpoint factorization.**  Both endpoint decays come out of
clause B as an identity, with the entity sum never leaving the
integrand. -/
theorem r324Beta_sum_eq_endpointDecays_mul_quadHarvest
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 0 < m) (α β : Z4)
    (F : Finset (MomentContraction m)) :
    (∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e) =
      ((paperFourthOrderModeDecay α * paperFourthOrderModeDecay β : ℝ) : ℂ) *
        r324BetaQuadHarvest ρ ε m α β hm F := by
  rw [r324Tail_sum_eq_alphaDecay_mul_headHarvest ρ hε hε1 hm α β F,
    r324Beta_headHarvest_eq ρ hε hε1 hm α β F]
  push_cast
  ring

/-- **The central-bracket ledger is not an over-assumption.**  It is
*implied* by the `ε`-free tail ledger it is used to prove: the two
endpoint decays divide out exactly.  So `R324BetaQuadBracketLedger`
measures precisely the central bracket and nothing more. -/
theorem R324BetaQuadBracketLedger_of_tailPaperLedger
    {ρ : SmoothCutoff} {K : ℝ}
    (h : ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
      0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m → m ≤ truncOrder ε →
        r324CMBracketWeight ε α β ≤ 1 →
          ∀ F : Finset (MomentContraction m),
            ‖∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e‖ ≤
              K ^ m * |Real.log ε| ^ (m - 1) *
                r324BracketPaperWeight α β) :
    R324BetaQuadBracketLedger ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap hW F hm
  have hpos : 0 < paperFourthOrderModeDecay α * paperFourthOrderModeDecay β :=
    mul_pos (paperFourthOrderModeDecay_pos α) (paperFourthOrderModeDecay_pos β)
  have key := h m α β hε hε1 hlog hm2 hcap hW F
  rw [r324Beta_sum_eq_endpointDecays_mul_quadHarvest ρ hε hε1 hm α β F,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpos.le] at key
  refine le_of_mul_le_mul_left ?_ hpos
  refine le_trans key (le_of_eq ?_)
  unfold r324BracketPaperWeight
  ring

/-! ## The modulus fallback -/

/-- Dropping the two transported head characters costs only the triangle
inequality — but it also destroys the central bracket, so this route
proves clause B *without* the `⟨‖α+β‖⟩⁻⁸` factor.  It is recorded to make
the split precise: an `L¹` ledger for the tail-amputated core
`r324BetaQuadCore` is exactly what is *not* enough, and the gap is exactly
the central bracket. -/
theorem norm_r324BetaQuadHarvest_le
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (α β : Z4) (hm : 0 < m)
    (F : Finset (MomentContraction m)) :
    ‖r324BetaQuadHarvest ρ ε m α β hm F‖ ≤
      ∫ v : Fin (2 * m) → T4, ‖r324BetaQuadCore ρ ε m β hm F v‖
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  unfold r324BetaQuadHarvest
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [norm_mul, norm_charT4, one_mul]

end

end Anderson4D
