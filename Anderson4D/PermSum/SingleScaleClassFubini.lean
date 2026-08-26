import Anderson4D.PermSum.SingleScaleCopyGlue

/-!
# Exact finite Fubini decomposition for the single-scale proof

This file groups the labeled arrangements from the factorial ledger first by
their active `P` word and then by the refining active `(N,X)` word.  It is
the finite statement-boundary decomposition used before applying the outer
class-word count and the conditioned inner estimates.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- Arrangements inducing a prescribed active `(N,X)` word. -/
def arrangementsAtNXWord {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t)
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) :
    Finset (HeppArrangement mu) :=
  Finset.univ.filter fun σ => arrangementNXWord Nm mu σ = x

/-- Exact grouping of all labeled arrangements by their `(N,X)` word. -/
theorem sum_arrangements_eq_sum_NXWords {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (F : HeppArrangement mu → ℝ) :
    (∑ σ : HeppArrangement mu, F σ) =
      ∑ x ∈ validWords (M := totalMultiplicity mu)
          (activeNXMultiplicity Nm mu),
        ∑ σ ∈ arrangementsAtNXWord Nm mu x, F σ := by
  symm
  simpa [arrangementsAtNXWord] using
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (HeppArrangement mu)))
      (t := validWords (M := totalMultiplicity mu)
        (activeNXMultiplicity Nm mu))
      (g := arrangementNXWord Nm mu)
      (fun σ _hσ => arrangementNXWord_mem_validWords Nm mu σ) F)

/-- The coarse word obtained from an abstract active `(N,X)` word. -/
def nxWordToPWord {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t)
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) :
    Fin (totalMultiplicity mu) → ActivePClass Nm mu :=
  fun j => activeNXToP Nm mu (x j)

theorem nxWordToPWord_mem_validWords {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu}
    (hx : x ∈ validWords (M := totalMultiplicity mu)
      (activeNXMultiplicity Nm mu)) :
    nxWordToPWord Nm mu x ∈
      validWords (M := totalMultiplicity mu)
        (activePMultiplicity Nm mu) := by
  apply map_mem_validWords_of_fiber_sum
    (activeNXMultiplicity Nm mu) (activePMultiplicity Nm mu)
    (activeNXToP Nm mu) x hx
  exact activeNX_fiber_mass Nm mu

theorem nxWordToPWord_eq_arrangementPWord {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (σ : HeppArrangement mu) :
    nxWordToPWord Nm mu (arrangementNXWord Nm mu σ) =
      arrangementPWord Nm mu σ :=
  rfl

/-- The fiber of `nxWordToPWord` inside valid `(N,X)` words is exactly the
project's `validRefinements` carrier. -/
theorem validNXWords_fiber_eq_validRefinements {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (y : Fin (totalMultiplicity mu) → ActivePClass Nm mu) :
    (validWords (M := totalMultiplicity mu)
        (activeNXMultiplicity Nm mu)).filter
        (fun x => nxWordToPWord Nm mu x = y) =
      validRefinements
        (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y := by
  ext x
  simp only [validRefinements, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, ?_⟩
    intro j
    exact congrFun hxy j
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, ?_⟩
    funext j
    exact hxy j

/--
Exact two-level grouping of an arbitrary statistic on valid `(N,X)` words:
first fix the `P` word, then sum over its valid refinements.
-/
theorem sum_validNXWords_eq_sum_PWords_refinements {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (G : (Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) → ℝ) :
    (∑ x ∈ validWords (M := totalMultiplicity mu)
        (activeNXMultiplicity Nm mu), G x) =
      ∑ y ∈ validWords (M := totalMultiplicity mu)
          (activePMultiplicity Nm mu),
        ∑ x ∈ validRefinements
            (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
          G x := by
  have h :=
    Finset.sum_fiberwise_of_maps_to
      (s := validWords (M := totalMultiplicity mu)
        (activeNXMultiplicity Nm mu))
      (t := validWords (M := totalMultiplicity mu)
        (activePMultiplicity Nm mu))
      (g := nxWordToPWord Nm mu)
      (fun x hx => nxWordToPWord_mem_validWords Nm mu hx) G
  symm
  simpa only [validNXWords_fiber_eq_validRefinements] using h

/--
The complete finite Fubini decomposition of the labeled-arrangement sum.
No positivity or analytic estimate is used: this is an exact identity.
-/
theorem sum_arrangements_eq_sum_PWords_NXWords {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (F : HeppArrangement mu → ℝ) :
    (∑ σ : HeppArrangement mu, F σ) =
      ∑ y ∈ validWords (M := totalMultiplicity mu)
          (activePMultiplicity Nm mu),
        ∑ x ∈ validRefinements
            (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
          ∑ σ ∈ arrangementsAtNXWord Nm mu x, F σ := by
  calc
    (∑ σ : HeppArrangement mu, F σ) =
        ∑ x ∈ validWords (M := totalMultiplicity mu)
            (activeNXMultiplicity Nm mu),
          ∑ σ ∈ arrangementsAtNXWord Nm mu x, F σ :=
      sum_arrangements_eq_sum_NXWords Nm mu F
    _ = _ :=
      sum_validNXWords_eq_sum_PWords_refinements Nm mu
        (fun x => ∑ σ ∈ arrangementsAtNXWord Nm mu x, F σ)

/--
Paper-sum statement-boundary form of the same decomposition.  The analytic
summand remains a function of the induced leaf word, exactly as in
`SingleScaleEstimate`.
-/
theorem paperSum_eq_sum_PWords_NXWords_arrangements {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (F : (Fin (totalMultiplicity mu) → HeppLeaf t) → ℝ) :
    paperSum (M := totalMultiplicity mu) (leafMultiplicity mu) F =
      ∑ y ∈ validWords (M := totalMultiplicity mu)
          (activePMultiplicity Nm mu),
        ∑ x ∈ validRefinements
            (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
          ∑ σ ∈ arrangementsAtNXWord Nm mu x,
            F (inducedWord (leafMultiplicity mu) σ) := by
  rw [paperSum_eq_sum_arrangements]
  exact sum_arrangements_eq_sum_PWords_NXWords Nm mu
    (fun σ => F (inducedWord (leafMultiplicity mu) σ))

end

end Anderson4D
