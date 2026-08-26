import Anderson4D.PermSum.SingleScaleOuter

/-!
# Copy-permutation bridge for the single-scale class words

The factorial ledger converts the paper sum to labeled arrangements.  The
outer dyadic argument instead counts `(N,X)` words refining a fixed `P`
word.  This file proves that the actual arrangement carrier maps
canonically into those class-word carriers:

* every labeled arrangement induces a valid active `(N,X)` word;
* its image is a valid active `P` word;
* the `(N,X)` word belongs to `validRefinements` above that `P` word.

Consequently the conditional count in paper (5.79) applies directly to an
actual copy permutation, rather than only to an abstract compatible word.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## A generic composition-of-fibers lemma -/

/--
The fiber of a composite word `g ∘ w` is the sigma of the fibers of `w`
over all fine letters mapping to the prescribed coarse letter.
-/
def composedWordFiberEquiv
    {δ ι κ : Type*} (g : ι → κ) (w : δ → ι) (b : κ) :
    {j : δ // g (w j) = b} ≃
      Σ a : {i : ι // g i = b}, {j : δ // w j = a.1} where
  toFun j := ⟨⟨w j.1, j.2⟩, ⟨j.1, rfl⟩⟩
  invFun p := ⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩
  left_inv j := by
    apply Subtype.ext
    rfl
  right_inv := by
    rintro ⟨⟨a, ha⟩, ⟨j, hj⟩⟩
    cases hj
    rfl

/-- Cardinality form of `composedWordFiberEquiv`. -/
theorem card_comp_word_fiber
    {δ ι κ : Type*} [Fintype δ] [Fintype ι]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq κ]
    (g : ι → κ) (w : δ → ι) (b : κ) :
    ((Finset.univ : Finset δ).filter fun j => g (w j) = b).card =
      ∑ a : {i : ι // g i = b},
        ((Finset.univ : Finset δ).filter fun j => w j = a.1).card := by
  calc
    ((Finset.univ : Finset δ).filter fun j => g (w j) = b).card =
        Fintype.card {j : δ // g (w j) = b} := by
      rw [Fintype.card_subtype]
    _ = Fintype.card
        (Σ a : {i : ι // g i = b}, {j : δ // w j = a.1}) :=
      Fintype.card_congr (composedWordFiberEquiv g w b)
    _ = ∑ a : {i : ι // g i = b},
        Fintype.card {j : δ // w j = a.1} :=
      Fintype.card_sigma
    _ = ∑ a : {i : ι // g i = b},
        ((Finset.univ : Finset δ).filter fun j => w j = a.1).card := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Fintype.card_subtype]

/--
Mapping a valid fine word through `g` gives a valid coarse word whenever
the coarse multiplicity is the sum of the fine multiplicities in each
fiber.
-/
theorem map_mem_validWords_of_fiber_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : ℕ} (fineMult : ι → ℕ) (coarseMult : κ → ℕ)
    (g : ι → κ) (w : Fin M → ι)
    (hw : w ∈ validWords (M := M) fineMult)
    (hmass : ∀ b : κ,
      (∑ a : {i : ι // g i = b}, fineMult a.1) = coarseMult b) :
    (fun j => g (w j)) ∈ validWords (M := M) coarseMult := by
  rw [validWords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro b
  rw [card_comp_word_fiber]
  calc
    (∑ a : {i : ι // g i = b},
        ((Finset.univ : Finset (Fin M)).filter fun j =>
          w j = a.1).card) =
        ∑ a : {i : ι // g i = b}, fineMult a.1 := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact (Finset.mem_filter.mp hw).2 a.1
    _ = coarseMult b := hmass b

/-! ## The actual arrangement-induced class words -/

/-- The labeled-copy arrangements appearing in the statement-boundary
factorial ledger. -/
abbrev HeppArrangement {t : PlaneTree} (mu : Multiplicities t) :=
  Fin (totalMultiplicity mu) ≃
    Σ l : HeppLeaf t, Fin (leafMultiplicity mu l)

/-- Send a leaf to its active `(N,X)` class. -/
def leafActiveNX {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (l : HeppLeaf t) :
    ActiveNXClass Nm mu :=
  ⟨singleScaleSigma1 Nm mu l, Finset.mem_image_of_mem _ (Finset.mem_univ l)⟩

/-- The `(N,X)` class word induced by an actual labeled arrangement. -/
def arrangementNXWord {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (σ : HeppArrangement mu) :
    Fin (totalMultiplicity mu) → ActiveNXClass Nm mu :=
  fun j => leafActiveNX Nm mu (inducedWord (leafMultiplicity mu) σ j)

/-- The coarse `P` word induced by the same labeled arrangement. -/
def arrangementPWord {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (σ : HeppArrangement mu) :
    Fin (totalMultiplicity mu) → ActivePClass Nm mu :=
  fun j => activeNXToP Nm mu (arrangementNXWord Nm mu σ j)

/-- A fiber of `leafActiveNX` is exactly the corresponding `leavesAtNX`
finset, expressed as an equivalence of subtypes. -/
def leafActiveNXFiberEquiv {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (a : ActiveNXClass Nm mu) :
    {l : HeppLeaf t // leafActiveNX Nm mu l = a} ≃
      {l : HeppLeaf t // l ∈ leavesAtNX Nm mu a.1} where
  toFun l := ⟨l.1, by
    simp only [leavesAtNX, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [leafActiveNX] using congrArg Subtype.val l.2⟩
  invFun l := ⟨l.1, by
    apply Subtype.ext
    simpa only [leafActiveNX, leavesAtNX, Finset.mem_filter,
      Finset.mem_univ, true_and] using l.2⟩
  left_inv l := by
    apply Subtype.ext
    rfl
  right_inv l := by
    apply Subtype.ext
    rfl

/-- The leaf multiplicities above an active `(N,X)` letter sum to the
paper mass `m_{N,X}`. -/
theorem sum_leafMultiplicity_leafActiveNX_fiber {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (a : ActiveNXClass Nm mu) :
    (∑ l : {l : HeppLeaf t // leafActiveNX Nm mu l = a},
        leafMultiplicity mu l.1) =
      activeNXMultiplicity Nm mu a := by
  let e := leafActiveNXFiberEquiv Nm mu a
  calc
    (∑ l : {l : HeppLeaf t // leafActiveNX Nm mu l = a},
        leafMultiplicity mu l.1) =
        ∑ l : {l : HeppLeaf t // l ∈ leavesAtNX Nm mu a.1},
          leafMultiplicity mu l.1 := by
      exact Fintype.sum_equiv e
        (fun l : {l : HeppLeaf t // leafActiveNX Nm mu l = a} =>
          leafMultiplicity mu l.1)
        (fun l : {l : HeppLeaf t // l ∈ leavesAtNX Nm mu a.1} =>
          leafMultiplicity mu l.1)
        (fun _l => rfl)
    _ = ∑ l ∈ leavesAtNX Nm mu a.1, leafMultiplicity mu l := by
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach
        (leavesAtNX Nm mu a.1) (leafMultiplicity mu)
    _ = activeNXMultiplicity Nm mu a := rfl

/-- Every actual copy permutation induces a valid `(N,X)` class word. -/
theorem arrangementNXWord_mem_validWords {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (σ : HeppArrangement mu) :
    arrangementNXWord Nm mu σ ∈
      validWords (M := totalMultiplicity mu)
        (activeNXMultiplicity Nm mu) := by
  apply map_mem_validWords_of_fiber_sum
    (leafMultiplicity mu) (activeNXMultiplicity Nm mu)
    (leafActiveNX Nm mu)
    (inducedWord (leafMultiplicity mu) σ)
  · exact inducedWord_mem_validWords (leafMultiplicity mu) σ
  · exact sum_leafMultiplicity_leafActiveNX_fiber Nm mu

/-- The coarse `P` word of every arrangement has the exact `m_P`
multiplicities. -/
theorem arrangementPWord_mem_validWords {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (σ : HeppArrangement mu) :
    arrangementPWord Nm mu σ ∈
      validWords (M := totalMultiplicity mu)
        (activePMultiplicity Nm mu) := by
  apply map_mem_validWords_of_fiber_sum
    (activeNXMultiplicity Nm mu) (activePMultiplicity Nm mu)
    (activeNXToP Nm mu) (arrangementNXWord Nm mu σ)
  · exact arrangementNXWord_mem_validWords Nm mu σ
  · exact activeNX_fiber_mass Nm mu

/--
The actual `(N,X)` word belongs to the exact refinement fiber above its
actual `P` word.
-/
theorem arrangementNXWord_mem_validRefinements {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (σ : HeppArrangement mu) :
    arrangementNXWord Nm mu σ ∈
      validRefinements
        (activeNXMultiplicity Nm mu) (activeNXToP Nm mu)
        (arrangementPWord Nm mu σ) := by
  rw [validRefinements, Finset.mem_filter]
  exact ⟨arrangementNXWord_mem_validWords Nm mu σ, fun _j => rfl⟩

/--
Arrangement-facing specialization of the conditional **class-word** count
(5.79).  Its left side is the refinement fiber containing the class word
induced by the given copy permutation; it is not the number of labeled
arrangements having that `P` word, which additionally carries the internal
factorial ledger.
-/
theorem paper579_arrangement_classWord_count {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (σ : HeppArrangement mu) :
    (validRefinements
      (activeNXMultiplicity Nm mu) (activeNXToP Nm mu)
      (arrangementPWord Nm mu σ)).card =
      ∏ P ∈ pCarrier Nm mu,
        Nat.multinomial (nxAtP Nm mu P) (multiplicityNX Nm mu) :=
  paper579_conditional_classWord_count Nm mu
    (arrangementPWord Nm mu σ)
    (arrangementPWord_mem_validWords Nm mu σ)

end

end Anderson4D
