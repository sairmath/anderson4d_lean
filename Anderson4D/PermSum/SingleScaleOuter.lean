import Anderson4D.PermSum.SingleScaleSetup
import Anderson4D.Combinatorics.BinomialBounds
import Anderson4D.Combinatorics.SequenceCount

/-!
# Outer dyadic summation in the single-scale estimate

This file formalizes the finite combinatorial ledger used in Step 3 of the
proof of Proposition 5.10, equations (5.76)--(5.86): the
simple/compound majority partition and estimates (5.83)--(5.85), followed by
the ordering and absorption argument in (5.86).

The companion `SingleScaleSequence` module supplies the `P`-sequence gain
(5.77), including the at-most-99 skipped positions; the assembly modules
combine it with the declarations below for the actual copy permutations.

The first sections record the exact conditional class-word count (5.79) and
the multinomial factorizations behind (5.80)--(5.82).  The subsequent sections
specialize them to the `(N,X) → (N,Y) → P` classification constructed in
`SingleScaleSetup`.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## A generic two-level multinomial identity -/

/--
Exact multinomial factorization through finite fibers.

This is the algebraic identity used twice below: first to group `(N,X)`
classes by `(N,Y)`, and later to group `(N,Y)` classes by their common
maximal scale `X*`.  Empty fibers cause no problem, since their multinomial
coefficient is one.
-/
theorem multinomial_fiberwise
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → ℕ)
    (hmap : ∀ i ∈ s, g i ∈ t) :
    Nat.multinomial s f =
      Nat.multinomial t
          (fun j => ∑ i ∈ s with g i = j, f i) *
        ∏ j ∈ t, Nat.multinomial (s.filter fun i => g i = j) f := by
  let F : κ → Finset ι := fun j => s.filter fun i => g i = j
  let mass : κ → ℕ := fun j => ∑ i ∈ F j, f i
  have hden :
      (∏ i ∈ s, (f i).factorial) =
        ∏ j ∈ t, ∏ i ∈ F j, (f i).factorial := by
    symm
    simpa only [F] using
      (Finset.prod_fiberwise_of_maps_to hmap fun i => (f i).factorial)
  have hmass :
      (∑ j ∈ t, mass j) = ∑ i ∈ s, f i := by
    simpa only [mass, F] using
      (Finset.sum_fiberwise_of_maps_to hmap f)
  apply Nat.eq_of_mul_eq_mul_left (Nat.prod_factorial_pos s f)
  rw [Nat.multinomial_spec]
  symm
  calc
    (∏ i ∈ s, (f i).factorial) *
          (Nat.multinomial t mass *
            ∏ j ∈ t, Nat.multinomial (F j) f) =
        Nat.multinomial t mass *
          ∏ j ∈ t,
            ((∏ i ∈ F j, (f i).factorial) *
              Nat.multinomial (F j) f) := by
      rw [hden, Finset.prod_mul_distrib]
      ring
    _ = Nat.multinomial t mass *
          ∏ j ∈ t, (mass j).factorial := by
      apply congrArg (Nat.multinomial t mass * ·)
      apply Finset.prod_congr rfl
      intro j hj
      exact Nat.multinomial_spec (F j) f
    _ = (∏ j ∈ t, (mass j).factorial) *
          Nat.multinomial t mass := by ring
    _ = (∑ j ∈ t, mass j).factorial :=
      Nat.multinomial_spec t mass
    _ = (∑ i ∈ s, f i).factorial := by rw [hmass]

/-- Replacing a finite carrier by its subtype does not change its
multinomial coefficient. -/
theorem multinomial_subtype_eq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    Nat.multinomial (Finset.univ : Finset {i // i ∈ s})
        (fun i => f i.1) =
      Nat.multinomial s f := by
  let emb := Function.Embedding.subtype fun i => i ∈ s
  have himage :
      (Finset.univ : Finset {i // i ∈ s}).map emb = s := by
    ext i
    simp [emb]
  calc
    Nat.multinomial (Finset.univ : Finset {i // i ∈ s})
        (fun i => f i.1) =
        Nat.multinomial
          ((Finset.univ : Finset {i // i ∈ s}).map emb) f := by
      rw [multinomial_map]
      rfl
    _ = Nat.multinomial s f := by rw [himage]

/-! ## Counting fine words over a fixed coarse word -/

/--
The number of admissible words with multiplicity function `mult` is the
corresponding multinomial coefficient.  This is the finite word-count bridge
needed before applying the fiberwise identities above.
-/
theorem card_validWords_eq_multinomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ℕ} (mult : ι → ℕ) (hM : ∑ i, mult i = M) :
    (validWords (M := M) mult).card =
      Nat.multinomial Finset.univ mult := by
  have hcard :
      Fintype.card (Fin M) =
        Fintype.card (Σ i : ι, Fin (mult i)) := by
    simp [hM]
  let e : Fin M ≃ Σ i : ι, Fin (mult i) :=
    Fintype.equivOfCardEq hcard
  have hledger := ledger_sum (M := M) mult (fun _ => 1)
  have harrangements :
      Fintype.card (Fin M ≃ Σ i : ι, Fin (mult i)) = M.factorial := by
    simpa using Fintype.card_equiv e
  have hcount :
      (∏ i : ι, (mult i).factorial) *
          (validWords (M := M) mult).card =
        M.factorial := by
    simpa [harrangements] using hledger.symm
  have hmulti :
      (∏ i : ι, (mult i).factorial) *
          Nat.multinomial Finset.univ mult =
        M.factorial := by
    simpa [hM] using Nat.multinomial_spec Finset.univ mult
  apply Nat.eq_of_mul_eq_mul_left
    (show 0 < ∏ i : ι, (mult i).factorial by positivity)
  exact hcount.trans hmulti.symm

/--
Fine words with prescribed multiplicities which refine a fixed coarse word
through `g`.
-/
def validRefinements
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (mult : ι → ℕ) (g : ι → κ) (y : Fin M → κ) :
    Finset (Fin M → ι) :=
  (validWords (M := M) mult).filter fun x => ∀ j, g (x j) = y j

private abbrev CoarsePosition
    {κ : Type*} {M : ℕ} (y : Fin M → κ) (b : κ) :=
  {j : Fin M // y j = b}

private abbrev FineFiber
    {ι κ : Type*} (g : ι → κ) (b : κ) :=
  {i : ι // g i = b}

private def refinementFiberMultiplicity
    {ι κ : Type*} (mult : ι → ℕ) (g : ι → κ) (b : κ) :
    FineFiber g b → ℕ :=
  fun i => mult i.1

private def validAssignments
    {δ ι : Type*} [Fintype δ] [Fintype ι]
    [DecidableEq δ] [DecidableEq ι]
    (mult : ι → ℕ) : Finset (δ → ι) :=
  Finset.univ.filter fun w =>
    ∀ i, (Finset.univ.filter fun j => w j = i).card = mult i

private theorem card_filter_comp_equiv
    {δ ε ι : Type*} [Fintype δ] [Fintype ε]
    [DecidableEq δ] [DecidableEq ε] [DecidableEq ι]
    (e : δ ≃ ε) (f : ε → ι) (a : ι) :
    ((Finset.univ : Finset δ).filter fun j => f (e j) = a).card =
      ((Finset.univ : Finset ε).filter fun j => f j = a).card := by
  refine Finset.card_bij (fun j _hj => e j) ?_ ?_ ?_
  · intro j hj
    simpa using hj
  · intro j₁ _hj₁ j₂ _hj₂ h
    exact e.injective h
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ _, by simpa using hj.2⟩

private theorem card_validAssignments_eq_multinomial
    {δ ι : Type*} [Fintype δ] [Fintype ι]
    [DecidableEq δ] [DecidableEq ι]
    (mult : ι → ℕ) (hcard : ∑ i, mult i = Fintype.card δ) :
    (validAssignments (δ := δ) mult).card =
      Nat.multinomial Finset.univ mult := by
  let e : Fin (Fintype.card δ) ≃ δ :=
    (Fintype.equivFin δ).symm
  calc
    (validAssignments (δ := δ) mult).card =
        (validWords (M := Fintype.card δ) mult).card := by
      refine Finset.card_bij (fun f _hf => f ∘ e) ?_ ?_ ?_
      · intro f hf
        rw [validWords, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro a
        calc
          ((Finset.univ : Finset (Fin (Fintype.card δ))).filter fun j =>
              (f ∘ e) j = a).card =
              ((Finset.univ : Finset δ).filter fun j => f j = a).card := by
            simpa [Function.comp_apply] using
              card_filter_comp_equiv e f a
          _ = mult a := (Finset.mem_filter.mp hf).2 a
      · intro f _hf h _hh heq
        funext j
        have := congrFun heq (e.symm j)
        simpa [Function.comp_apply] using this
      · intro w hw
        let f : δ → ι := w ∘ e.symm
        refine ⟨f, ?_, ?_⟩
        · rw [validAssignments, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          intro a
          have h :=
            card_filter_comp_equiv e.symm w a
          simpa [f, Function.comp_apply] using
            h.trans ((Finset.mem_filter.mp hw).2 a)
        · funext j
          simp [f, Function.comp_apply]
    _ = Nat.multinomial Finset.univ mult :=
      card_validWords_eq_multinomial mult hcard

private def refinementBundles
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (mult : ι → ℕ) (g : ι → κ) (y : Fin M → κ) :
    Finset (∀ b : κ, CoarsePosition y b → FineFiber g b) :=
  Fintype.piFinset fun b =>
    validAssignments
      (δ := CoarsePosition y b)
      (refinementFiberMultiplicity mult g b)

private noncomputable def encodeRefinement
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (g : ι → κ) (y : Fin M → κ)
    (x : Fin M → ι) (hx : ∀ j, g (x j) = y j) :
    ∀ b : κ, CoarsePosition y b → FineFiber g b :=
  fun _b j => ⟨x j.1, (hx j.1).trans j.2⟩

private noncomputable def decodeRefinement
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (g : ι → κ) (y : Fin M → κ)
    (F : ∀ b : κ, CoarsePosition y b → FineFiber g b) :
    Fin M → ι :=
  fun j =>
    let p := (Equiv.sigmaFiberEquiv y).symm j
    (F p.1 p.2).1

private theorem decodeRefinement_coarse
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (g : ι → κ) (y : Fin M → κ)
    (F : ∀ b : κ, CoarsePosition y b → FineFiber g b) :
    ∀ j, g (decodeRefinement g y F j) = y j := by
  intro j
  let p := (Equiv.sigmaFiberEquiv y).symm j
  have hp : p.2.1 = j := by
    simp [p]
  calc
    g (decodeRefinement g y F j) = p.1 := (F p.1 p.2).2
    _ = y p.2.1 := p.2.2.symm
    _ = y j := by rw [hp]

private theorem decode_encodeRefinement
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (g : ι → κ) (y : Fin M → κ)
    (x : Fin M → ι) (hx : ∀ j, g (x j) = y j) :
    decodeRefinement g y (encodeRefinement g y x hx) = x := by
  funext j
  let p := (Equiv.sigmaFiberEquiv y).symm j
  have hp : p.2.1 = j := by
    simp [p]
  change x p.2.1 = x j
  rw [hp]

private theorem encode_decodeRefinement
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (g : ι → κ) (y : Fin M → κ)
    (F : ∀ b : κ, CoarsePosition y b → FineFiber g b) :
    encodeRefinement g y (decodeRefinement g y F)
        (decodeRefinement_coarse g y F) =
      F := by
  funext b j
  apply Subtype.ext
  have hp :
      (Equiv.sigmaFiberEquiv y).symm j.1 =
        ⟨b, j⟩ := by
    simpa using (Equiv.sigmaFiberEquiv y).symm_apply_apply ⟨b, j⟩
  change (F ((Equiv.sigmaFiberEquiv y).symm j.1).1
      ((Equiv.sigmaFiberEquiv y).symm j.1).2).1 = (F b j).1
  rw [hp]

private theorem encodeRefinement_fiber_card
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (g : ι → κ) (y : Fin M → κ)
    (x : Fin M → ι) (hx : ∀ j, g (x j) = y j)
    (b : κ) (a : FineFiber g b) :
    ((Finset.univ : Finset (CoarsePosition y b)).filter fun j =>
        encodeRefinement g y x hx b j = a).card =
      ((Finset.univ : Finset (Fin M)).filter fun j => x j = a.1).card := by
  refine Finset.card_bij (fun j _hj => j.1) ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ _, congrArg Subtype.val hj.2⟩
  · intro j₁ _hj₁ j₂ _hj₂ h
    exact Subtype.ext h
  · intro j hj
    rw [Finset.mem_filter] at hj
    have hjb : y j = b := by
      calc
        y j = g (x j) := (hx j).symm
        _ = g a.1 := congrArg g hj.2
        _ = b := a.2
    let k : CoarsePosition y b := ⟨j, hjb⟩
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    apply Subtype.ext
    exact hj.2

private theorem encodeRefinement_mem_bundles
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (mult : ι → ℕ) (g : ι → κ) (y : Fin M → κ)
    {x : Fin M → ι} (hx : x ∈ validRefinements mult g y) :
    encodeRefinement g y x (Finset.mem_filter.mp hx).2 ∈
      refinementBundles mult g y := by
  rw [refinementBundles, Fintype.mem_piFinset]
  intro b
  rw [validAssignments, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro a
  rw [encodeRefinement_fiber_card]
  exact (Finset.mem_filter.mp
    (Finset.mem_filter.mp hx).1).2 a.1

private theorem decodeRefinement_mem_validRefinements
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (mult : ι → ℕ) (g : ι → κ) (y : Fin M → κ)
    {F : ∀ b : κ, CoarsePosition y b → FineFiber g b}
    (hF : F ∈ refinementBundles mult g y) :
    decodeRefinement g y F ∈ validRefinements mult g y := by
  rw [validRefinements, Finset.mem_filter]
  refine ⟨?_, decodeRefinement_coarse g y F⟩
  rw [validWords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro a
  have hFmem :
      ∀ b, F b ∈ validAssignments
        (δ := CoarsePosition y b)
        (refinementFiberMultiplicity mult g b) := by
    simpa only [refinementBundles, Fintype.mem_piFinset] using hF
  have hlocal :=
    (Finset.mem_filter.mp (hFmem (g a))).2
      (⟨a, rfl⟩ : FineFiber g (g a))
  have hencoded :
      encodeRefinement g y (decodeRefinement g y F)
          (decodeRefinement_coarse g y F) (g a) =
        F (g a) :=
    congrFun (encode_decodeRefinement g y F) (g a)
  calc
    ((Finset.univ : Finset (Fin M)).filter fun j =>
        decodeRefinement g y F j = a).card =
        ((Finset.univ : Finset (CoarsePosition y (g a))).filter fun j =>
          encodeRefinement g y (decodeRefinement g y F)
            (decodeRefinement_coarse g y F) (g a) j =
              (⟨a, rfl⟩ : FineFiber g (g a))).card :=
      (encodeRefinement_fiber_card g y
        (decodeRefinement g y F) (decodeRefinement_coarse g y F)
        (g a) ⟨a, rfl⟩).symm
    _ = ((Finset.univ : Finset (CoarsePosition y (g a))).filter fun j =>
          F (g a) j = (⟨a, rfl⟩ : FineFiber g (g a))).card := by
      rw [hencoded]
    _ = mult a := hlocal

/--
Conditional word count through a finite coarse map.

If the fixed coarse word `y` uses each coarse letter `b` exactly as often
as the total fine multiplicity above `b`, then the number of admissible fine
words refining `y` is the product of the fiber multinomial coefficients.
This is the abstract counting statement behind paper (5.79).
-/
theorem card_validRefinements
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (mult : ι → ℕ) (g : ι → κ) (y : Fin M → κ)
    (hmass : ∀ b : κ,
      (∑ a : {i : ι // g i = b}, mult a.1) =
        Fintype.card {j : Fin M // y j = b}) :
    (validRefinements mult g y).card =
      ∏ b : κ,
        Nat.multinomial Finset.univ
          (fun a : {i : ι // g i = b} => mult a.1) := by
  calc
    (validRefinements mult g y).card =
        (refinementBundles mult g y).card := by
      refine Finset.card_bij
        (fun x hx =>
          encodeRefinement g y x (Finset.mem_filter.mp hx).2) ?_ ?_ ?_
      · intro x hx
        exact encodeRefinement_mem_bundles mult g y hx
      · intro x hx x' hx' h
        calc
          x = decodeRefinement g y
              (encodeRefinement g y x (Finset.mem_filter.mp hx).2) :=
            (decode_encodeRefinement g y x
              (Finset.mem_filter.mp hx).2).symm
          _ = decodeRefinement g y
              (encodeRefinement g y x' (Finset.mem_filter.mp hx').2) :=
            congrArg (decodeRefinement g y) h
          _ = x' :=
            decode_encodeRefinement g y x'
              (Finset.mem_filter.mp hx').2
      · intro F hF
        let x := decodeRefinement g y F
        have hx : x ∈ validRefinements mult g y :=
          decodeRefinement_mem_validRefinements mult g y hF
        refine ⟨x, hx, ?_⟩
        simpa [x] using encode_decodeRefinement g y F
    _ = ∏ b : κ,
        (validAssignments
          (δ := CoarsePosition y b)
          (refinementFiberMultiplicity mult g b)).card := by
      rw [refinementBundles, Fintype.card_piFinset]
    _ = ∏ b : κ,
        Nat.multinomial Finset.univ
          (fun a : {i : ι // g i = b} => mult a.1) := by
      apply Finset.prod_congr rfl
      intro b _hb
      exact card_validAssignments_eq_multinomial
        (refinementFiberMultiplicity mult g b) (hmass b)

/-! ## A finite dyadic-window lemma -/

/--
At most three distinct powers of two can be pairwise within a strict factor
`8`.  This is the finite cardinality fact used to turn
`m_{N,X} ∼ XY` into the lacunarity required by Lemma 5.12.
-/
theorem card_le_three_of_pow_two_pairwise_lt_eight
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x e : ι → ℕ)
    (hpow : ∀ a ∈ s, x a = 2 ^ e a)
    (hinj : Set.InjOn e s)
    (hclose : ∀ a ∈ s, ∀ b ∈ s, x a < 8 * x b) :
    s.card ≤ 3 := by
  by_cases hs : s.Nonempty
  · obtain ⟨a0, ha0, hmin⟩ := Finset.exists_min_image s e hs
    have hmaps : Set.MapsTo e (s : Set ι)
        (Finset.Ico (e a0) (e a0 + 3) : Set ℕ) := by
      intro a ha
      rw [Finset.coe_Ico]
      refine ⟨hmin a ha, ?_⟩
      by_contra hnot
      have he : e a0 + 3 ≤ e a := by omega
      have hp : 8 * x a0 ≤ x a := by
        rw [hpow a ha, hpow a0 ha0]
        calc
          8 * 2 ^ e a0 = 2 ^ (e a0 + 3) := by
            rw [pow_add]
            norm_num [Nat.mul_comm]
          _ ≤ 2 ^ e a := Nat.pow_le_pow_right (by omega) he
      exact (not_lt_of_ge hp) (hclose a ha a0 ha0)
    calc
      s.card ≤ (Finset.Ico (e a0) (e a0 + 3)).card :=
        Finset.card_le_card_of_injOn e hmaps hinj
      _ = 3 := by simp
  · simp only [Finset.not_nonempty_iff_eq_empty] at hs
    simp [hs]

/-- Four-point version used after grouping the `(N,Y)` classes by `X*`. -/
theorem card_le_four_of_pow_two_pairwise_lt_sixteen
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x e : ι → ℕ)
    (hpow : ∀ a ∈ s, x a = 2 ^ e a)
    (hinj : Set.InjOn e s)
    (hclose : ∀ a ∈ s, ∀ b ∈ s, x a < 16 * x b) :
    s.card ≤ 4 := by
  by_cases hs : s.Nonempty
  · obtain ⟨a0, ha0, hmin⟩ := Finset.exists_min_image s e hs
    have hmaps : Set.MapsTo e (s : Set ι)
        (Finset.Ico (e a0) (e a0 + 4) : Set ℕ) := by
      intro a ha
      rw [Finset.coe_Ico]
      refine ⟨hmin a ha, ?_⟩
      by_contra hnot
      have he : e a0 + 4 ≤ e a := by omega
      have hp : 16 * x a0 ≤ x a := by
        rw [hpow a ha, hpow a0 ha0]
        calc
          16 * 2 ^ e a0 = 2 ^ (e a0 + 4) := by
            rw [pow_add]
            norm_num [Nat.mul_comm]
          _ ≤ 2 ^ e a := Nat.pow_le_pow_right (by omega) he
      exact (not_lt_of_ge hp) (hclose a ha a0 ha0)
    calc
      s.card ≤ (Finset.Ico (e a0) (e a0 + 4)).card :=
        Finset.card_le_card_of_injOn e hmaps hinj
      _ = 4 := by simp
  · simp only [Finset.not_nonempty_iff_eq_empty] at hs
    simp [hs]

/-- Passing from a finset to its subtype carrier preserves `Lacunary`. -/
theorem lacunary_subtype
    {ι : Type*} [DecidableEq ι] {K : ℕ}
    (s : Finset ι) (f : ι → ℕ) (h : Lacunary K s f) :
    Lacunary K Finset.univ (fun a : {x // x ∈ s} => f a.1) := by
  intro X hX
  let u := (Finset.univ : Finset {x // x ∈ s}).filter fun a =>
    X ≤ f a.1 ∧ f a.1 < 2 * X
  let v := s.filter fun a => X ≤ f a ∧ f a < 2 * X
  have himage : u.image (fun a => a.1) = v := by
    ext a
    simp [u, v, and_left_comm, and_comm]
  calc
    ((Finset.univ : Finset {x // x ∈ s}).filter fun a =>
        X ≤ f a.1 ∧ f a.1 < 2 * X).card =
        (u.image fun a => a.1).card := by
      rw [Finset.card_image_of_injective u Subtype.val_injective]
    _ = v.card := by rw [himage]
    _ ≤ K := h X hX

/--
Finset-indexed form of Lemma 5.12 (5.51).

`BinomialBounds` states the result for tuples on `Fin r`; this wrapper
reindexes an arbitrary finite carrier without changing
either the multinomial coefficient or its total mass.
-/
theorem multinomial_le_pow_of_lacunary_finset (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ),
        Lacunary K s f →
          (Nat.multinomial s f : ℝ) ≤ C ^ (∑ i ∈ s, f i) := by
  obtain ⟨C, hC, hbound⟩ := multinomial_le_pow_of_lacunary K hK
  refine ⟨C, hC, ?_⟩
  intro ι _ s f hlac
  let r := Fintype.card {x // x ∈ s}
  let e : Fin r ≃ {x // x ∈ s} :=
    (Fintype.equivFin {x // x ∈ s}).symm
  let fsub : {x // x ∈ s} → ℕ := fun a => f a.1
  let n : Fin r → ℕ := fsub ∘ e
  have hlacSub : Lacunary K Finset.univ fsub := by
    exact lacunary_subtype s f hlac
  have hlacFin : Lacunary K Finset.univ n := by
    exact lacunary_comp_equiv e hlacSub
  have hmultiSub :
      Nat.multinomial s f =
        Nat.multinomial (Finset.univ : Finset {x // x ∈ s}) fsub := by
    let emb := Function.Embedding.subtype fun x => x ∈ s
    have himage :
        (Finset.univ : Finset {x // x ∈ s}).map emb = s := by
      ext x
      simp [emb]
    calc
      Nat.multinomial s f =
          Nat.multinomial
            ((Finset.univ : Finset {x // x ∈ s}).map emb) f := by
        exact congrArg (fun u => Nat.multinomial u f) himage.symm
      _ = Nat.multinomial (Finset.univ : Finset {x // x ∈ s})
          (f ∘ emb) :=
        multinomial_map emb
          (Finset.univ : Finset {x // x ∈ s}) f
      _ = Nat.multinomial (Finset.univ : Finset {x // x ∈ s}) fsub := by
        apply Nat.multinomial_congr
        intro a ha
        rfl
  have hmultiFin :
      Nat.multinomial (Finset.univ : Finset (Fin r)) n =
        Nat.multinomial (Finset.univ : Finset {x // x ∈ s}) fsub := by
    exact multinomial_comp_equiv e fsub
  have hsumSub :
      (∑ a : {x // x ∈ s}, fsub a) = ∑ i ∈ s, f i := by
    calc
      (∑ a : {x // x ∈ s}, fsub a) =
          ∑ a ∈ s.attach, f a.1 := by
        rw [Finset.attach_eq_univ]
      _ = ∑ i ∈ s, f i := Finset.sum_attach s f
  have hsumFin :
      (∑ i : Fin r, n i) = ∑ i ∈ s, f i := by
    calc
      (∑ i : Fin r, n i) =
          ∑ a : {x // x ∈ s}, fsub a := by
        simpa [n, Function.comp_apply] using Equiv.sum_comp e fsub
      _ = ∑ i ∈ s, f i := hsumSub
  simpa [hmultiSub, hmultiFin, hsumFin] using hbound r n hlacFin

/-! ## The fixed-`P` carriers -/

/-- The active class map `(N,X) ↦ P = YN⁴`. -/
def activeNXToP {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) :
    ActiveNXClass Nm mu → ActivePClass Nm mu :=
  fun a =>
    ⟨singleScaleSigma3 (singleScaleSigma2 Nm mu a.1),
      Finset.mem_image_of_mem _
        (Finset.mem_image_of_mem _ a.2)⟩

/-- Multiplicity of an active `(N,X)` class. -/
def activeNXMultiplicity {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) : ActiveNXClass Nm mu → ℕ :=
  fun a => multiplicityNX Nm mu a.1

/-- Multiplicity of an active `P` class. -/
def activePMultiplicity {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) : ActivePClass Nm mu → ℕ :=
  fun P => multiplicityP Nm mu P.1

/-- Active `(N,X)` classes whose image under `σ₃ ∘ σ₂` is `P`. -/
def nxAtP {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (P : ℕ) : Finset NXClass :=
  (nxCarrier Nm mu).filter fun a =>
    singleScaleSigma3 (singleScaleSigma2 Nm mu a) = P

/-- The class map `(N,X) ↦ (N,Y)` used inside a fixed `P` fiber. -/
def nxToNY {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) : NXClass → NYClass :=
  singleScaleSigma2 Nm mu

theorem nxAtP_mapsTo_nyAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (P : ℕ)
    {a : NXClass} (ha : a ∈ nxAtP Nm mu P) :
    nxToNY Nm mu a ∈ nyAtP Nm mu P := by
  rw [nxAtP] at ha
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mp ha).1,
      (Finset.mem_filter.mp ha).2⟩

theorem nxAtP_fiber_eq_nxAtNY {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (P : ℕ)
    {q : NYClass} (hq : q ∈ nyAtP Nm mu P) :
    (nxAtP Nm mu P).filter (fun a => nxToNY Nm mu a = q) =
      nxAtNY Nm mu q := by
  ext a
  have hqP := (Finset.mem_filter.mp hq).2
  simp only [nxAtP, nxAtNY, nxToNY, Finset.mem_filter]
  constructor
  · rintro ⟨⟨ha, _⟩, haq⟩
    exact ⟨ha, haq⟩
  · rintro ⟨ha, haq⟩
    refine ⟨⟨ha, ?_⟩, haq⟩
    simpa [haq] using hqP

theorem nxAtP_fiber_mass {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (P : ℕ)
    {q : NYClass} (hq : q ∈ nyAtP Nm mu P) :
    (∑ a ∈ nxAtP Nm mu P with nxToNY Nm mu a = q,
        multiplicityNX Nm mu a) =
      multiplicityNY Nm mu q := by
  rw [show (nxAtP Nm mu P).filter (fun a => nxToNY Nm mu a = q) =
      nxAtNY Nm mu q from nxAtP_fiber_eq_nxAtNY Nm mu P hq]
  rfl

/-- The total multiplicity in a fixed `P` fiber can be summed directly over
its `(N,X)` classes. -/
theorem multiplicityP_eq_sum_NX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (P : ℕ) :
    multiplicityP Nm mu P =
      ∑ a ∈ nxAtP Nm mu P, multiplicityNX Nm mu a := by
  rw [multiplicityP_eq_fiber_sum]
  symm
  calc
    (∑ a ∈ nxAtP Nm mu P, multiplicityNX Nm mu a) =
        ∑ q ∈ nyAtP Nm mu P,
          ∑ a ∈ nxAtP Nm mu P with nxToNY Nm mu a = q,
            multiplicityNX Nm mu a := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun a ha => nxAtP_mapsTo_nyAtP Nm mu P ha)
        (multiplicityNX Nm mu)
    _ = ∑ q ∈ nyAtP Nm mu P, multiplicityNY Nm mu q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact nxAtP_fiber_mass Nm mu P hq

noncomputable def activeNXFiberEquiv {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (P : ActivePClass Nm mu) :
    {a : ActiveNXClass Nm mu // activeNXToP Nm mu a = P} ≃
      {a : NXClass // a ∈ nxAtP Nm mu P.1} where
  toFun a :=
    ⟨a.1.1, Finset.mem_filter.mpr
      ⟨a.1.2, congrArg Subtype.val a.2⟩⟩
  invFun a :=
    ⟨⟨a.1, (Finset.mem_filter.mp a.2).1⟩, by
      apply Subtype.ext
      exact (Finset.mem_filter.mp a.2).2⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    rfl

@[simp] theorem activeNXFiberEquiv_val {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (P : ActivePClass Nm mu)
    (a : {a : ActiveNXClass Nm mu // activeNXToP Nm mu a = P}) :
    (activeNXFiberEquiv Nm mu P a).1 = a.1.1 :=
  rfl

theorem activeNX_fiber_mass {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (P : ActivePClass Nm mu) :
    (∑ a : {a : ActiveNXClass Nm mu // activeNXToP Nm mu a = P},
        activeNXMultiplicity Nm mu a.1) =
      activePMultiplicity Nm mu P := by
  rw [activePMultiplicity, multiplicityP_eq_sum_NX]
  let e := activeNXFiberEquiv Nm mu P
  calc
    (∑ a : {a : ActiveNXClass Nm mu // activeNXToP Nm mu a = P},
        activeNXMultiplicity Nm mu a.1) =
        ∑ a : {a : NXClass // a ∈ nxAtP Nm mu P.1},
          multiplicityNX Nm mu a.1 := by
      simpa [e, activeNXMultiplicity, Function.comp_apply] using
        Equiv.sum_comp e
          (fun a : {a : NXClass // a ∈ nxAtP Nm mu P.1} =>
            multiplicityNX Nm mu a.1)
    _ = ∑ a ∈ nxAtP Nm mu P.1, multiplicityNX Nm mu a := by
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach (nxAtP Nm mu P.1) (multiplicityNX Nm mu)

theorem activeNX_fiber_multinomial {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (P : ActivePClass Nm mu) :
    Nat.multinomial
        (Finset.univ :
          Finset {a : ActiveNXClass Nm mu // activeNXToP Nm mu a = P})
        (fun a => activeNXMultiplicity Nm mu a.1) =
      Nat.multinomial (nxAtP Nm mu P.1) (multiplicityNX Nm mu) := by
  let e := activeNXFiberEquiv Nm mu P
  calc
    Nat.multinomial
        (Finset.univ :
          Finset {a : ActiveNXClass Nm mu // activeNXToP Nm mu a = P})
        (fun a => activeNXMultiplicity Nm mu a.1) =
        Nat.multinomial
          (Finset.univ : Finset {a : NXClass // a ∈ nxAtP Nm mu P.1})
          (fun a => multiplicityNX Nm mu a.1) := by
      let f :=
        fun a : {a : NXClass // a ∈ nxAtP Nm mu P.1} =>
          multiplicityNX Nm mu a.1
      have hfun :
          (fun a :
              {a : ActiveNXClass Nm mu // activeNXToP Nm mu a = P} =>
            activeNXMultiplicity Nm mu a.1) =
            f ∘ e := by
        funext a
        rfl
      rw [hfun]
      exact multinomial_comp_equiv e f
    _ = Nat.multinomial (nxAtP Nm mu P.1) (multiplicityNX Nm mu) :=
      multinomial_subtype_eq (nxAtP Nm mu P.1) (multiplicityNX Nm mu)

/--
Paper (5.79), in the word representation used by this project.

For a fixed valid `P`-word, the admissible `(N,X)` class words refining it
are counted by the product, over active `P`, of the multinomial coefficients
of the `(N,X)` multiplicities in that fiber.
-/
theorem paper579_conditional_classWord_count {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (y : Fin (totalMultiplicity mu) → ActivePClass Nm mu)
    (hy : y ∈ validWords (M := totalMultiplicity mu)
      (activePMultiplicity Nm mu)) :
    (validRefinements
      (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y).card =
      ∏ P ∈ pCarrier Nm mu,
        Nat.multinomial (nxAtP Nm mu P) (multiplicityNX Nm mu) := by
  have hmass : ∀ P : ActivePClass Nm mu,
      (∑ a :
          {a : ActiveNXClass Nm mu // activeNXToP Nm mu a = P},
        activeNXMultiplicity Nm mu a.1) =
        Fintype.card {j : Fin (totalMultiplicity mu) // y j = P} := by
    intro P
    calc
      (∑ a :
          {a : ActiveNXClass Nm mu // activeNXToP Nm mu a = P},
        activeNXMultiplicity Nm mu a.1) =
          activePMultiplicity Nm mu P :=
        activeNX_fiber_mass Nm mu P
      _ = ((Finset.univ : Finset (Fin (totalMultiplicity mu))).filter
          fun j => y j = P).card :=
        ((Finset.mem_filter.mp hy).2 P).symm
      _ = Fintype.card
          {j : Fin (totalMultiplicity mu) // y j = P} := by
        rw [Fintype.card_subtype]
  calc
    (validRefinements
      (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y).card =
        ∏ P : ActivePClass Nm mu,
          Nat.multinomial Finset.univ
            (fun a :
              {a : ActiveNXClass Nm mu //
                activeNXToP Nm mu a = P} =>
              activeNXMultiplicity Nm mu a.1) :=
      card_validRefinements
        (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y hmass
    _ = ∏ P : ActivePClass Nm mu,
        Nat.multinomial (nxAtP Nm mu P.1) (multiplicityNX Nm mu) := by
      apply Finset.prod_congr rfl
      intro P _hP
      exact activeNX_fiber_multinomial Nm mu P
    _ = ∏ P ∈ pCarrier Nm mu,
        Nat.multinomial (nxAtP Nm mu P) (multiplicityNX Nm mu) := by
      exact Finset.prod_coe_sort
        (pCarrier Nm mu)
        (fun P : ℕ =>
          Nat.multinomial (nxAtP Nm mu P) (multiplicityNX Nm mu))

/--
Exact two-level decomposition used in the reduction (5.80) to (5.81):

`multinomial((m_{N,X})_{P})`
equals the multinomial of the `(N,Y)` masses times the product of the
within-`(N,Y)` multinomials.
-/
theorem fixedP_multinomial_decomposition {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (P : ℕ) :
    Nat.multinomial (nxAtP Nm mu P) (multiplicityNX Nm mu) =
      Nat.multinomial (nyAtP Nm mu P) (multiplicityNY Nm mu) *
        ∏ q ∈ nyAtP Nm mu P,
          Nat.multinomial (nxAtNY Nm mu q) (multiplicityNX Nm mu) := by
  calc
    Nat.multinomial (nxAtP Nm mu P) (multiplicityNX Nm mu) =
        Nat.multinomial (nyAtP Nm mu P)
            (fun q => ∑ a ∈ nxAtP Nm mu P with nxToNY Nm mu a = q,
              multiplicityNX Nm mu a) *
          ∏ q ∈ nyAtP Nm mu P,
            Nat.multinomial
              ((nxAtP Nm mu P).filter fun a => nxToNY Nm mu a = q)
              (multiplicityNX Nm mu) :=
      multinomial_fiberwise
        (nxAtP Nm mu P) (nyAtP Nm mu P) (nxToNY Nm mu)
        (multiplicityNX Nm mu)
        (fun a ha => nxAtP_mapsTo_nyAtP Nm mu P ha)
    _ = Nat.multinomial (nyAtP Nm mu P) (multiplicityNY Nm mu) *
          ∏ q ∈ nyAtP Nm mu P,
            Nat.multinomial (nxAtNY Nm mu q) (multiplicityNX Nm mu) := by
      congr 1
      · apply Nat.multinomial_congr
        intro q hq
        exact nxAtP_fiber_mass Nm mu P hq
      · apply Finset.prod_congr rfl
        intro q hq
        rw [nxAtP_fiber_eq_nxAtNY Nm mu P hq]

/-! ## Lacunarity inside one `(N,Y)` class -/

theorem nyClass_Y_pos {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    0 < q.2 := by
  obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hq
  rw [← haq]
  simp only [singleScaleSigma2, dyadicFloor]
  positivity

/--
The family `(m_{N,X})_X` in a fixed `(N,Y)` class is `3`-lacunary.

Indeed, `XY ≤ m_{N,X} < 4XY`; if two such masses lie in the same
window `[Z,2Z)`, their dyadic `X` values differ by a strict factor less
than `8`.  Hence at most three distinct powers of two occur.
-/
theorem multiplicityNX_lacunary {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    Lacunary 3 (nxAtNY Nm mu q) (multiplicityNX Nm mu) := by
  intro Z hZ
  let s := (nxAtNY Nm mu q).filter fun a =>
    Z ≤ multiplicityNX Nm mu a ∧ multiplicityNX Nm mu a < 2 * Z
  have hactive : ∀ a ∈ s, a ∈ nxCarrier Nm mu := by
    intro a ha
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have hclass : ∀ a ∈ s, singleScaleSigma2 Nm mu a = q := by
    intro a ha
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
  have hpow : ∀ a ∈ s, a.2 = 2 ^ Nat.log 2 a.2 := by
    intro a ha
    exact nxClass_second_eq_pow_log Nm mu (hactive a ha)
  have hinj : Set.InjOn (fun a : NXClass => Nat.log 2 a.2) s := by
    intro a ha b hb hab
    apply Prod.ext
    · have ha1 := congrArg Prod.fst (hclass a ha)
      have hb1 := congrArg Prod.fst (hclass b hb)
      simpa [singleScaleSigma2] using ha1.trans hb1.symm
    · calc
        a.2 = 2 ^ Nat.log 2 a.2 := hpow a ha
        _ = 2 ^ Nat.log 2 b.2 := by
          change Nat.log 2 a.2 = Nat.log 2 b.2 at hab
          rw [hab]
        _ = b.2 := (hpow b hb).symm
  have hclose : ∀ a ∈ s, ∀ b ∈ s, a.2 < 8 * b.2 := by
    intro a ha b hb
    have haWindow := (Finset.mem_filter.mp ha).2
    have hbWindow := (Finset.mem_filter.mp hb).2
    have haBounds := multiplicityNX_bounds Nm mu (hactive a ha)
    have hbBounds := multiplicityNX_bounds Nm mu (hactive b hb)
    rw [hclass a ha] at haBounds
    rw [hclass b hb] at hbBounds
    have hmul :
        a.2 * q.2 < (8 * b.2) * q.2 := by
      calc
        a.2 * q.2 ≤ multiplicityNX Nm mu a := haBounds.1
        _ < 2 * Z := haWindow.2
        _ ≤ 2 * multiplicityNX Nm mu b :=
          Nat.mul_le_mul_left 2 hbWindow.1
        _ < 2 * (4 * b.2 * q.2) :=
          (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hbBounds.2
        _ = (8 * b.2) * q.2 := by ring
    exact (Nat.mul_lt_mul_right (nyClass_Y_pos Nm mu hq)).mp hmul
  change s.card ≤ 3
  exact card_le_three_of_pow_two_pairwise_lt_eight
    s Prod.snd (fun a => Nat.log 2 a.2) hpow hinj hclose

/-! ### The second lacunary grouping in (5.86) -/

/-- Fixed-`P` `(N,Y)` classes with a prescribed maximal multiplicity scale
`X*`.  These are the paper's blocks `B(i)`. -/
def nyAtPX {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (P X : ℕ) : Finset NYClass :=
  (nyAtP Nm mu P).filter fun q => maxXAtNY Nm mu q = X

theorem nyAtPX_active {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {P X : ℕ} {q : NYClass} (hq : q ∈ nyAtPX Nm mu P X) :
    q ∈ nyCarrier Nm mu :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1

theorem nyAtPX_P {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {P X : ℕ} {q : NYClass} (hq : q ∈ nyAtPX Nm mu P X) :
    singleScaleSigma3 q = P :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2

theorem nyAtPX_maxX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {P X : ℕ} {q : NYClass} (hq : q ∈ nyAtPX Nm mu P X) :
    maxXAtNY Nm mu q = X :=
  (Finset.mem_filter.mp hq).2

theorem nyClass_second_eq_pow_log {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    q.2 = 2 ^ Nat.log 2 q.2 := by
  obtain ⟨k, hk⟩ := (nyClass_dyadic Nm mu hq).2
  rw [hk, Nat.log_pow Nat.one_lt_two]

theorem one_le_maxXAtNY {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    1 ≤ maxXAtNY Nm mu q := by
  rw [← maxNXAtNY_snd Nm mu q hq]
  exact one_le_nxClass_X Nm mu (maxNXAtNY_active Nm mu q hq)

/--
For fixed `P` and fixed `X*`, the masses `m_{N,Y}` are `4`-lacunary.

The bounds `X*Y ≤ m_{N,Y} ≤ 8X*Y` put all `Y` values in one mass
window within a strict factor `16`.  At fixed `P = YN⁴`, distinct classes
have distinct dyadic `Y`, so there can be at most four.
-/
theorem multiplicityNY_lacunary_fixed_P_X {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (P X : ℕ) :
    Lacunary 4 (nyAtPX Nm mu P X) (multiplicityNY Nm mu) := by
  intro Z hZ
  let s := (nyAtPX Nm mu P X).filter fun q =>
    Z ≤ multiplicityNY Nm mu q ∧ multiplicityNY Nm mu q < 2 * Z
  have hbase : ∀ q ∈ s, q ∈ nyAtPX Nm mu P X := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hactive : ∀ q ∈ s, q ∈ nyCarrier Nm mu :=
    fun q hq => nyAtPX_active Nm mu (hbase q hq)
  have hpow : ∀ q ∈ s, q.2 = 2 ^ Nat.log 2 q.2 := by
    intro q hq
    exact nyClass_second_eq_pow_log Nm mu (hactive q hq)
  have hinj : Set.InjOn (fun q : NYClass => Nat.log 2 q.2) s := by
    intro q hq r hr he
    have hY : q.2 = r.2 := by
      calc
        q.2 = 2 ^ Nat.log 2 q.2 := hpow q hq
        _ = 2 ^ Nat.log 2 r.2 := by
          change Nat.log 2 q.2 = Nat.log 2 r.2 at he
          rw [he]
        _ = r.2 := (hpow r hr).symm
    have hqP := nyAtPX_P Nm mu (hbase q hq)
    have hrP := nyAtPX_P Nm mu (hbase r hr)
    have hpowN : q.1 ^ 4 = r.1 ^ 4 := by
      apply Nat.eq_of_mul_eq_mul_left (nyClass_Y_pos Nm mu (hactive q hq))
      simpa [singleScaleSigma3, hY] using hqP.trans hrP.symm
    have hN : q.1 = r.1 :=
      pow_left_injective (by norm_num : (4 : ℕ) ≠ 0) hpowN
    exact Prod.ext hN hY
  have hclose : ∀ q ∈ s, ∀ r ∈ s, q.2 < 16 * r.2 := by
    intro q hq r hr
    have hqWindow := (Finset.mem_filter.mp hq).2
    have hrWindow := (Finset.mem_filter.mp hr).2
    have hqBounds := multiplicityNY_bounds Nm mu (hactive q hq)
    have hrBounds := multiplicityNY_bounds Nm mu (hactive r hr)
    rw [nyAtPX_maxX Nm mu (hbase q hq)] at hqBounds
    rw [nyAtPX_maxX Nm mu (hbase r hr)] at hrBounds
    have hX : 0 < X := by
      rw [← nyAtPX_maxX Nm mu (hbase q hq)]
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one
        (one_le_maxXAtNY Nm mu (hactive q hq))
    have hmul : X * q.2 < X * (16 * r.2) := by
      calc
        X * q.2 ≤ multiplicityNY Nm mu q := hqBounds.1
        _ < 2 * Z := hqWindow.2
        _ ≤ 2 * multiplicityNY Nm mu r :=
          Nat.mul_le_mul_left 2 hrWindow.1
        _ ≤ 2 * (8 * X * r.2) :=
          Nat.mul_le_mul_left 2 hrBounds.2
        _ = X * (16 * r.2) := by ring
    exact (Nat.mul_lt_mul_left hX).mp hmul
  change s.card ≤ 4
  exact card_le_four_of_pow_two_pairwise_lt_sixteen
    s Prod.snd (fun q => Nat.log 2 q.2) hpow hinj hclose

/-- The active `X*` values among `(N,Y)` classes at fixed `P`. -/
def xStarCarrierAtP {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (P : ℕ) : Finset ℕ :=
  (nyAtP Nm mu P).image fun q => maxXAtNY Nm mu q

/-- Paper's `q(i)`: total `(N,Y)` mass in a fixed `X*` block. -/
def multiplicityPX {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (P X : ℕ) : ℕ :=
  ∑ q ∈ nyAtPX Nm mu P X, multiplicityNY Nm mu q

/-- Paper's `W(i)`: the sum of the dyadic `Y` values in one `X*` block. -/
def yMassPX {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (P X : ℕ) : ℕ :=
  ∑ q ∈ nyAtPX Nm mu P X, q.2

theorem nyAtP_mapsTo_xStarCarrier {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (P : ℕ)
    {q : NYClass} (hq : q ∈ nyAtP Nm mu P) :
    maxXAtNY Nm mu q ∈ xStarCarrierAtP Nm mu P :=
  Finset.mem_image_of_mem _ hq

theorem multiplicityP_eq_sum_PX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (P : ℕ) :
    multiplicityP Nm mu P =
      ∑ X ∈ xStarCarrierAtP Nm mu P, multiplicityPX Nm mu P X := by
  rw [multiplicityP_eq_fiber_sum]
  symm
  simpa [multiplicityPX, nyAtPX] using
    (Finset.sum_fiberwise_of_maps_to
      (s := nyAtP Nm mu P) (t := xStarCarrierAtP Nm mu P)
      (g := fun q => maxXAtNY Nm mu q)
      (fun q hq => nyAtP_mapsTo_xStarCarrier Nm mu P hq)
      (multiplicityNY Nm mu))

theorem xStarCarrier_dyadic {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {P X : ℕ} (hX : X ∈ xStarCarrierAtP Nm mu P) :
    IsDyadicNat X := by
  obtain ⟨q, hqP, hqX⟩ := Finset.mem_image.mp hX
  have hq : q ∈ nyCarrier Nm mu := (Finset.mem_filter.mp hqP).1
  have ha := maxNXAtNY_active Nm mu q hq
  have hdy := (nxClass_dyadic Nm mu ha).2
  rw [← hqX, ← maxNXAtNY_snd Nm mu q hq]
  exact hdy

theorem xStarCarrier_pos {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {P X : ℕ} (hX : X ∈ xStarCarrierAtP Nm mu P) :
    0 < X := by
  obtain ⟨q, hqP, hqX⟩ := Finset.mem_image.mp hX
  have hq : q ∈ nyCarrier Nm mu := (Finset.mem_filter.mp hqP).1
  rw [← hqX]
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_maxXAtNY Nm mu hq)

/-- The comparison `q(i) ∼ Z(i)W(i)` used immediately below (5.86), with
explicit constants `1` and `8`. -/
theorem multiplicityPX_bounds {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (P X : ℕ) :
    X * yMassPX Nm mu P X ≤ multiplicityPX Nm mu P X ∧
      multiplicityPX Nm mu P X ≤ 8 * X * yMassPX Nm mu P X := by
  constructor
  · rw [multiplicityPX, yMassPX, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hactive := nyAtPX_active Nm mu hq
    have hb := (multiplicityNY_bounds Nm mu hactive).1
    rwa [nyAtPX_maxX Nm mu hq] at hb
  · rw [multiplicityPX, yMassPX]
    calc
      (∑ q ∈ nyAtPX Nm mu P X, multiplicityNY Nm mu q) ≤
          ∑ q ∈ nyAtPX Nm mu P X, 8 * X * q.2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hactive := nyAtPX_active Nm mu hq
        have hb := (multiplicityNY_bounds Nm mu hactive).2
        rwa [nyAtPX_maxX Nm mu hq] at hb
      _ = 8 * X * ∑ q ∈ nyAtPX Nm mu P X, q.2 := by
        rw [Finset.mul_sum]

/--
Exact block decomposition at the start of (5.86), grouping equal `X*`
values and writing their masses as `q(i)`.
-/
theorem fixedP_NY_multinomial_decomposition {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (P : ℕ) :
    Nat.multinomial (nyAtP Nm mu P) (multiplicityNY Nm mu) =
      Nat.multinomial (xStarCarrierAtP Nm mu P)
          (multiplicityPX Nm mu P) *
        ∏ X ∈ xStarCarrierAtP Nm mu P,
          Nat.multinomial (nyAtPX Nm mu P X) (multiplicityNY Nm mu) := by
  calc
    Nat.multinomial (nyAtP Nm mu P) (multiplicityNY Nm mu) =
        Nat.multinomial (xStarCarrierAtP Nm mu P)
            (fun X => ∑ q ∈ nyAtP Nm mu P with
              maxXAtNY Nm mu q = X, multiplicityNY Nm mu q) *
          ∏ X ∈ xStarCarrierAtP Nm mu P,
            Nat.multinomial
              ((nyAtP Nm mu P).filter fun q => maxXAtNY Nm mu q = X)
              (multiplicityNY Nm mu) :=
      multinomial_fiberwise
        (nyAtP Nm mu P) (xStarCarrierAtP Nm mu P)
        (fun q => maxXAtNY Nm mu q) (multiplicityNY Nm mu)
        (fun q hq => nyAtP_mapsTo_xStarCarrier Nm mu P hq)
    _ = Nat.multinomial (xStarCarrierAtP Nm mu P)
          (multiplicityPX Nm mu P) *
        ∏ X ∈ xStarCarrierAtP Nm mu P,
          Nat.multinomial (nyAtPX Nm mu P X) (multiplicityNY Nm mu) := by
      rfl

/-- Lemma 5.12 applied inside every fixed-`X*` block `B(i)`. -/
theorem withinPX_multinomial_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (P X : ℕ),
        (Nat.multinomial (nyAtPX Nm mu P X) (multiplicityNY Nm mu) : ℝ) ≤
          C ^ multiplicityPX Nm mu P X := by
  obtain ⟨C, hC, hbound⟩ :=
    multinomial_le_pow_of_lacunary_finset 4 (by omega)
  refine ⟨C, hC, ?_⟩
  intro t Nm mu P X
  simpa [multiplicityPX] using
    hbound (nyAtPX Nm mu P X) (multiplicityNY Nm mu)
      (multiplicityNY_lacunary_fixed_P_X Nm mu P X)

theorem withinPX_multinomial_product_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (P : ℕ),
        ((∏ X ∈ xStarCarrierAtP Nm mu P,
            Nat.multinomial (nyAtPX Nm mu P X)
              (multiplicityNY Nm mu) : ℕ) : ℝ) ≤
          C ^ multiplicityP Nm mu P := by
  obtain ⟨C, hC, hpoint⟩ := withinPX_multinomial_le
  refine ⟨C, hC, ?_⟩
  intro t Nm mu P
  calc
    ((∏ X ∈ xStarCarrierAtP Nm mu P,
        Nat.multinomial (nyAtPX Nm mu P X)
          (multiplicityNY Nm mu) : ℕ) : ℝ) =
        ∏ X ∈ xStarCarrierAtP Nm mu P,
          (Nat.multinomial (nyAtPX Nm mu P X)
            (multiplicityNY Nm mu) : ℝ) := by push_cast; rfl
    _ ≤ ∏ X ∈ xStarCarrierAtP Nm mu P,
        C ^ multiplicityPX Nm mu P X := by
      apply Finset.prod_le_prod
      · intro X hX
        positivity
      · intro X hX
        exact hpoint Nm mu P X
    _ = C ^ (∑ X ∈ xStarCarrierAtP Nm mu P,
        multiplicityPX Nm mu P X) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = C ^ multiplicityP Nm mu P := by
      rw [multiplicityP_eq_sum_PX]

/--
First reduction in (5.86): after the lacunary estimates inside the blocks
`B(i)`, only the multinomial of the block masses `q(i)` remains.
-/
theorem fixedP_NY_multinomial_le_XStar :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (P : ℕ),
        (Nat.multinomial (nyAtP Nm mu P) (multiplicityNY Nm mu) : ℝ) ≤
          C ^ multiplicityP Nm mu P *
            (Nat.multinomial (xStarCarrierAtP Nm mu P)
              (multiplicityPX Nm mu P) : ℝ) := by
  obtain ⟨C, hC, hprod⟩ := withinPX_multinomial_product_le
  refine ⟨C, hC, ?_⟩
  intro t Nm mu P
  have hp := hprod Nm mu P
  push_cast at hp
  rw [fixedP_NY_multinomial_decomposition]
  push_cast
  calc
    (Nat.multinomial (xStarCarrierAtP Nm mu P)
        (multiplicityPX Nm mu P) : ℝ) *
        (∏ X ∈ xStarCarrierAtP Nm mu P,
          (Nat.multinomial (nyAtPX Nm mu P X)
            (multiplicityNY Nm mu) : ℝ)) ≤
      (Nat.multinomial (xStarCarrierAtP Nm mu P)
        (multiplicityPX Nm mu P) : ℝ) *
        C ^ multiplicityP Nm mu P :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = C ^ multiplicityP Nm mu P *
        (Nat.multinomial (xStarCarrierAtP Nm mu P)
          (multiplicityPX Nm mu P) : ℝ) := by ring

/--
The within-`(N,Y)` multinomial in (5.80) is exponentially bounded in
`m_{N,Y}`.  This is the precise application of Lemma 5.12 justified by
`multiplicityNX_lacunary`.
-/
theorem withinNY_multinomial_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        {q : NYClass}, q ∈ nyCarrier Nm mu →
          (Nat.multinomial (nxAtNY Nm mu q) (multiplicityNX Nm mu) : ℝ) ≤
            C ^ multiplicityNY Nm mu q := by
  obtain ⟨C, hC, hbound⟩ :=
    multinomial_le_pow_of_lacunary_finset 3 (by omega)
  refine ⟨C, hC, ?_⟩
  intro t Nm mu q hq
  simpa [multiplicityNY] using
    hbound (nxAtNY Nm mu q) (multiplicityNX Nm mu)
      (multiplicityNX_lacunary Nm mu hq)

/--
Product form of the within-`(N,Y)` estimate at fixed `P`.

The exponent is exactly `m_P`, because the `(N,Y)` fibers in `nyAtP`
partition the `P`-class.
-/
theorem withinNY_multinomial_product_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (P : ℕ),
        ((∏ q ∈ nyAtP Nm mu P,
            Nat.multinomial (nxAtNY Nm mu q) (multiplicityNX Nm mu) : ℕ) : ℝ) ≤
          C ^ multiplicityP Nm mu P := by
  obtain ⟨C, hC, hpoint⟩ := withinNY_multinomial_le
  refine ⟨C, hC, ?_⟩
  intro t Nm mu P
  calc
    ((∏ q ∈ nyAtP Nm mu P,
        Nat.multinomial (nxAtNY Nm mu q) (multiplicityNX Nm mu) : ℕ) : ℝ) =
        ∏ q ∈ nyAtP Nm mu P,
          (Nat.multinomial (nxAtNY Nm mu q)
            (multiplicityNX Nm mu) : ℝ) := by push_cast; rfl
    _ ≤ ∏ q ∈ nyAtP Nm mu P, C ^ multiplicityNY Nm mu q := by
      apply Finset.prod_le_prod
      · intro q hq
        positivity
      · intro q hq
        exact hpoint Nm mu (Finset.mem_filter.mp hq).1
    _ = C ^ (∑ q ∈ nyAtP Nm mu P, multiplicityNY Nm mu q) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = C ^ multiplicityP Nm mu P := by
      rw [multiplicityP_eq_fiber_sum]

/--
Reduction from (5.80) to (5.81): at fixed `P`, summing over all `(N,X)`
classes costs only an exponential factor times the multinomial of the
coarser `(N,Y)` masses.
-/
theorem fixedP_multinomial_le_outerNY :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (P : ℕ),
        (Nat.multinomial (nxAtP Nm mu P) (multiplicityNX Nm mu) : ℝ) ≤
          C ^ multiplicityP Nm mu P *
            (Nat.multinomial (nyAtP Nm mu P) (multiplicityNY Nm mu) : ℝ) := by
  obtain ⟨C, hC, hprod⟩ := withinNY_multinomial_product_le
  refine ⟨C, hC, ?_⟩
  intro t Nm mu P
  have hp := hprod Nm mu P
  push_cast at hp
  rw [fixedP_multinomial_decomposition]
  push_cast
  calc
    (Nat.multinomial (nyAtP Nm mu P) (multiplicityNY Nm mu) : ℝ) *
        (∏ q ∈ nyAtP Nm mu P,
          (Nat.multinomial (nxAtNY Nm mu q)
            (multiplicityNX Nm mu) : ℝ)) ≤
      (Nat.multinomial (nyAtP Nm mu P) (multiplicityNY Nm mu) : ℝ) *
        C ^ multiplicityP Nm mu P :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = C ^ multiplicityP Nm mu P *
        (Nat.multinomial (nyAtP Nm mu P) (multiplicityNY Nm mu) : ℝ) := by
      ring

/-! ## The algebraic skeleton of the `S/C` partition in (5.82)

The actual majority predicate and its simple/compound payoffs are deliberately
left to the remaining (5.83)--(5.85) assembly listed in the module header.
-/

def boolFiber {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → Bool) (b : Bool) : Finset ι :=
  s.filter fun i => p i = b

theorem boolFiber_union {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → Bool) :
    boolFiber s p false ∪ boolFiber s p true = s := by
  ext i
  cases h : p i <;> simp [boolFiber, h]

theorem boolFiber_disjoint {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → Bool) :
    Disjoint (boolFiber s p false) (boolFiber s p true) := by
  exact Finset.disjoint_left.mpr fun i hiFalse hiTrue => by
    have hf := (Finset.mem_filter.mp hiFalse).2
    have ht := (Finset.mem_filter.mp hiTrue).2
    rw [hf] at ht
    exact Bool.false_ne_true ht

theorem multinomial_bool (f : Bool → ℕ) :
    Nat.multinomial Finset.univ f = (f false + f true).choose (f false) := by
  rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
  rw [Nat.multinomial_insert (by decide)]
  simp

/--
Exact factorial split underlying (5.82).  The leading binomial chooses which
copies belong to the `false` and `true` groups; the two remaining factors
permute within the groups.
-/
theorem multinomial_bool_partition
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (p : ι → Bool) :
    Nat.multinomial s f =
      ((∑ i ∈ boolFiber s p false, f i) +
          ∑ i ∈ boolFiber s p true, f i).choose
            (∑ i ∈ boolFiber s p false, f i) *
        Nat.multinomial (boolFiber s p false) f *
        Nat.multinomial (boolFiber s p true) f := by
  have h := multinomial_fiberwise s (Finset.univ : Finset Bool) p f
    (fun i hi => Finset.mem_univ (p i))
  rw [multinomial_bool] at h
  calc
    Nat.multinomial s f =
        ((∑ i ∈ boolFiber s p false, f i) +
          ∑ i ∈ boolFiber s p true, f i).choose
            (∑ i ∈ boolFiber s p false, f i) *
          (Nat.multinomial (boolFiber s p true) f *
            Nat.multinomial (boolFiber s p false) f) := by
      simpa [boolFiber] using h
    _ = ((∑ i ∈ boolFiber s p false, f i) +
          ∑ i ∈ boolFiber s p true, f i).choose
            (∑ i ∈ boolFiber s p false, f i) *
        Nat.multinomial (boolFiber s p false) f *
        Nat.multinomial (boolFiber s p true) f := by ring

/--
The generic algebraic inequality underlying paper (5.82), with loss
`2^(∑ i, f i)`.  Its paper specialization has exponent `m_P`; the theorem
is independent of the simple/compound majority predicate.
-/
theorem multinomial_bool_partition_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (p : ι → Bool) :
    Nat.multinomial s f ≤
      2 ^ (∑ i ∈ s, f i) *
        Nat.multinomial (boolFiber s p false) f *
        Nat.multinomial (boolFiber s p true) f := by
  rw [multinomial_bool_partition]
  have hsum :
      (∑ i ∈ boolFiber s p false, f i) +
          ∑ i ∈ boolFiber s p true, f i =
        ∑ i ∈ s, f i := by
    rw [← Finset.sum_union (boolFiber_disjoint s p), boolFiber_union]
  rw [hsum]
  exact Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _
      (Nat.choose_le_two_pow (∑ i ∈ s, f i)
        (∑ i ∈ boolFiber s p false, f i)))

end

end Anderson4D
