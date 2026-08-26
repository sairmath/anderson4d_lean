import Anderson4D.Combinatorics.PrimitiveWord
import Anderson4D.HeppTree.Leaves

/-!
# Paper-facing permutation-sum statements

This file freezes the statements of Propositions 5.7, 5.9, and 5.10 of
Deng--Shen, *The four-dimensional Anderson model: a case study for critical
SPDEs* (arXiv:2607.10105v1).  It contains no proof of those estimates.

The left sides use the factorial-ledger normalization `paperSum`.  Thus they
are sums over permutations of distinct copies, although their internal carrier
is the pure word model of `PermSum.Words`.

## Totalization conventions

* Adjacent positions are represented by `AdjacentIndex m`; this type is empty
  when `m = 0`, so no out-of-range successor is ever read.
* The subtractions in `(n - |W|)!`, `(m - 2|W|)!`, and `(m - s)!` are natural
  subtraction.  In every estimate below the stated tree, multiplicity, and
  skipped-set hypotheses imply that no truncation occurs.  Those inequalities
  are proof obligations, rather than extra assumptions weakening the paper's
  propositions.
* Parent scales are read only on non-root branch nodes.  Root scales are read
  only under the explicit hypothesis that the root is a branch node.  Hence
  the junk values of `HeppMarking.Nexp` away from `BranchNodes` are never used.
* The compound-leaf set is required to be a subset of `Leaves`; the junk
  values of `Multiplicities.m` away from `Leaves` are never used.
* Real powers (`3/4` and `m/2`) use mathlib's totalized `Real.rpow`.  Their
  bases are positive on the stated domains.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators
noncomputable section

/-! ## Common paper data and weights -/

/-- The leaf carrier of a Hepp tree. -/
abbrev HeppLeaf (t : PlaneTree) := {v // v ∈ Leaves t}

/-- The multiplicity function restricted to its meaningful leaf carrier. -/
def leafMultiplicity {t : PlaneTree} (mu : Multiplicities t) :
    HeppLeaf t → ℕ :=
  fun l => mu.m l.1

/-- Total word length `m = ∑_l m_l` from Definition 5.3. -/
def totalMultiplicity {t : PlaneTree} (mu : Multiplicities t) : ℕ :=
  ∑ l : HeppLeaf t, leafMultiplicity mu l

/-- The non-root branch nodes.  Every parent-scale ratio in (5.15), (5.33),
and (5.39) is indexed by this set. -/
def nonrootBranches (t : PlaneTree) : Finset (VPos t) :=
  (BranchNodes t).erase (rootV t)

/-- Branch nodes in the subtree rooted at `v`; this is paper notation
`B_v = {u ∈ B : u ≤ v}` from Definition 5.3. -/
def branchNodesUnder {t : PlaneTree} (v : VPos t) : Finset (VPos t) :=
  (BranchNodes t).filter fun u => v.1 <+: u.1

/-- The quantity `N'_v = ∑_{u ≤ v} γ_u^∞ N_u` used in (5.32) and (5.38). -/
def accumulatedScale {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (v : VPos t) : ℕ :=
  ∑ u ∈ branchNodesUnder v, gammaInf mu u * scaleN Nm u

/-- Definition 5.4(a), without the unrelated boundedness and linking clauses:
the leaf embedding is injective and separated at the LCA scale. -/
def IsSeparatedEmbedding {t : PlaneTree} (Nm : HeppMarking t)
    (z : HeppLeaf t → Fin 4 → ℤ) : Prop :=
  Function.Injective z ∧
    ∀ l l', l ≠ l' →
      (scaleN Nm (lcaV l.1 l'.1) : ℝ) / 2 ≤ znorm (z l - z l')

/-- Condition (5.32): every pair of leaves below a branch node is at distance
at most `N'_v`. -/
def SatisfiesSubtreeDiameter {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (z : HeppLeaf t → Fin 4 → ℤ) : Prop :=
  ∀ v ∈ BranchNodes t, ∀ l ∈ leavesUnder v, ∀ l' ∈ leavesUnder v,
    znorm (z l - z l') ≤ (accumulatedScale Nm mu v : ℝ)

/-- Condition (5.38)(a): `N_{v⁺} ≤ 8 N'_v` for every non-root branch node. -/
def SatisfiesSingleScaleCondition {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) : Prop :=
  ∀ v ∈ nonrootBranches t,
    scaleN Nm (parentV v) ≤ 8 * accumulatedScale Nm mu v

/-- Natural dyadic numbers, used for the scale `R` in Proposition 5.10. -/
def IsDyadicNat (R : ℕ) : Prop :=
  ∃ k : ℕ, R = 2 ^ k

/-- Positions having a successor.  This is the zero-based version of the
paper's index set `{1, ..., m-1}`. -/
abbrev AdjacentIndex (m : ℕ) := {j : Fin m // j.1 + 1 < m}

/-- The position immediately to the right of an adjacency index. -/
def adjacentSucc {m : ℕ} (j : AdjacentIndex m) : Fin m :=
  ⟨j.1.1 + 1, j.2⟩

/-- The exact factor `⟨x-y⟩⁻² = (1 + |x-y|²)⁻¹` in (5.15), (5.33), and
(5.39), using the project's fixed lattice sup norm. -/
def latticeEdgeWeight (x y : Fin 4 → ℤ) : ℝ :=
  (1 + znorm (x - y) ^ 2)⁻¹

/-- Product of all adjacent edge weights in a word. -/
def heppChainWeight {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (w : Fin m → HeppLeaf t) : ℝ :=
  ∏ j : AdjacentIndex m, latticeEdgeWeight (z (w j.1)) (z (w (adjacentSucc j)))

/-- Product in (5.39), omitting exactly the adjacency indices in `O`. -/
def heppChainWeightExcept {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (O : Finset (AdjacentIndex m))
    (w : Fin m → HeppLeaf t) : ℝ :=
  ∏ j : AdjacentIndex m,
    if j ∈ O then 1 else latticeEdgeWeight (z (w j.1)) (z (w (adjacentSucc j)))

/-- Proposition 5.10's adjacency condition: equal consecutive leaves are
forbidden outside the skipped set `O`; no primitivity is imposed. -/
def NoAdjacentOutside {α : Type*} {m : ℕ} [DecidableEq α]
    (O : Finset (AdjacentIndex m)) (w : Fin m → α) : Prop :=
  ∀ j : AdjacentIndex m, j ∉ O → w j.1 ≠ w (adjacentSucc j)

instance {α : Type*} {m : ℕ} [DecidableEq α]
    (O : Finset (AdjacentIndex m)) (w : Fin m → α) :
    Decidable (NoAdjacentOutside O w) :=
  inferInstanceAs
    (Decidable (∀ j : AdjacentIndex m, j ∉ O → w j.1 ≠ w (adjacentSucc j)))

/-- The (5.15) summand, including precisely the word-level primitivity
condition (5.11)(c). -/
def primitiveChainWeight {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (w : Fin m → HeppLeaf t) : ℝ :=
  if NoProperLeafBlock w then heppChainWeight z w else 0

/-- The (5.33) summand: primitivity together with no adjacent equal leaves. -/
def primitiveSeparatedChainWeight {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (w : Fin m → HeppLeaf t) : ℝ :=
  if NoProperLeafBlock w ∧ NoAdjacentEqual w then heppChainWeight z w else 0

/-- The (5.39) summand: omitted factors at `O`, the adjacency restriction
outside `O`, and deliberately no primitivity condition. -/
def singleScaleChainWeight {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (O : Finset (AdjacentIndex m))
    (w : Fin m → HeppLeaf t) : ℝ :=
  if NoAdjacentOutside O w then heppChainWeightExcept z O w else 0

/-- `(k!)^{1/2}` in the paper. -/
def sqrtFactorial (k : ℕ) : ℝ :=
  Real.sqrt (k.factorial : ℝ)

/-- `(k!)^{3/4}` in the paper, represented by `Real.rpow`. -/
def factorialThreeQuarters (k : ℕ) : ℝ :=
  (k.factorial : ℝ) ^ (3 / 4 : ℝ)

/-- The scale ratio `N_v / N_{v⁺}`, used only for non-root branch nodes. -/
def parentScaleRatio {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) : ℝ :=
  (scaleN Nm v : ℝ) / (scaleN Nm (parentV v) : ℝ)

/-! ## Proposition 5.7, equation (5.15) -/

/-- The right-hand side of (5.15), with `W` ranging over subsets of the
non-root branch nodes. -/
def permSumRHS (C : ℝ) (n : ℕ) (t : PlaneTree) (Nm : HeppMarking t)
    (mu : Multiplicities t) : ℝ :=
  C ^ n *
    ∑ W ∈ (nonrootBranches t).powerset,
      ((n - W.card).factorial : ℝ) *
        (∏ l : HeppLeaf t, sqrtFactorial (leafMultiplicity mu l)) *
        (∏ v ∈ BranchNodes t,
          (scaleN Nm v : ℝ) ^
            ((-4 : ℤ) * (((childrenOf v).card : ℤ) - 1))) *
        (scaleN Nm (rootV t) : ℝ) ^ (-2 : ℤ) *
        ∏ v ∈ (nonrootBranches t) \ W, parentScaleRatio Nm v

/-- **Proposition 5.7 / (5.15), frozen statement.**

`C` is the single absolute constant.  The hypotheses spell out the ambient
`n ≥ 2` context, a valid nontrivial Hepp tree, even leaf multiplicities of
total `2n`, and realization by a fully admissible embedding. -/
def PermSumEstimate (C : ℝ) : Prop :=
  0 < C ∧
    ∀ (n M : ℕ) (t : PlaneTree) (Nm : HeppMarking t)
      (mu : Multiplicities t) (z : HeppLeaf t → Fin 4 → ℤ),
      2 ≤ n →
      t.isValid = true →
      rootV t ∈ BranchNodes t →
      totalMultiplicity mu = 2 * n →
      (∀ l : HeppLeaf t, Even (leafMultiplicity mu l)) →
      IsAdmissible Nm M z →
      paperSum (M := 2 * n) (leafMultiplicity mu)
          (primitiveChainWeight (m := 2 * n) z) ≤
        permSumRHS C n t Nm mu

/-! ## Proposition 5.9, equations (5.32)--(5.33) -/

/-- The right-hand side of (5.33).  `compound` is exactly the set
`L_C`; `simpleLeaves t compound` is `L_S`. -/
def inductiveRHS (C0 D : ℝ) (m : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) : ℝ :=
  C0 ^ m * D ^ (BranchNodes t).card *
    ∑ W ∈ (nonrootBranches t).powerset,
      sqrtFactorial (m - 2 * W.card) *
        (∏ l ∈ simpleLeaves t compound, sqrtFactorial (mu.m l)) *
        (∏ l ∈ compoundLeaves t compound, factorialThreeQuarters (mu.m l)) *
        (∏ v ∈ BranchNodes t,
          (scaleN Nm v : ℝ) ^
            ((-2 : ℤ) * ((gamma2 mu compound v : ℤ) - 1))) *
        (∏ v ∈ nonrootBranches t, (parentScaleRatio Nm v) ^ 2) *
        ∏ v ∈ (nonrootBranches t) \ W, parentScaleRatio Nm v

/-- **Proposition 5.9 / (5.32)--(5.33), frozen statement.**

The named constants remain parameters with the literal hypotheses
`C0 > 1000` and `D = exp(C0^10)`.  Compound multiplicities need not be even.
The left side retains both primitivity and the no-adjacent-equal restriction. -/
def InductiveEstimate (C0 D : ℝ) : Prop :=
  1000 < C0 ∧
    D = Real.exp (C0 ^ 10) ∧
    ∀ (m : ℕ) (t : PlaneTree) (Nm : HeppMarking t)
      (mu : Multiplicities t) (compound : Finset (VPos t))
      (z : HeppLeaf t → Fin 4 → ℤ),
      t.isValid = true →
      rootV t ∈ BranchNodes t →
      compound ⊆ Leaves t →
      totalMultiplicity mu = m →
      IsSeparatedEmbedding Nm z →
      SatisfiesSubtreeDiameter Nm mu z →
      paperSum (M := m) (leafMultiplicity mu)
          (primitiveSeparatedChainWeight (m := m) z) ≤
        inductiveRHS C0 D m t Nm mu compound

/-! ## Proposition 5.10, equations (5.38)--(5.39) -/

/-- The right-hand side of (5.39).  The exponent `m/2` on `C0` is a real
half-power, not natural-number division. -/
def singleScaleRHS (C0 : ℝ) (m s R : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) : ℝ :=
  C0 ^ ((m : ℝ) / 2) *
    sqrtFactorial (m - s) *
    (∏ l ∈ simpleLeaves t compound, sqrtFactorial (mu.m l)) *
    (∏ l ∈ compoundLeaves t compound, factorialThreeQuarters (mu.m l)) *
    (∏ v ∈ BranchNodes t,
      (scaleN Nm v : ℝ) ^
        ((-2 : ℤ) * ((gamma2 mu compound v : ℤ) - 1))) *
    (R : ℝ) ^ (2 * s) *
    (∏ v ∈ nonrootBranches t, (parentScaleRatio Nm v) ^ 3) *
    (((scaleN Nm (rootV t) : ℝ) / (R : ℝ)) ^ min (2 * s) 3)

/-- **Proposition 5.10 / (5.38)--(5.39), frozen statement.**

`R` is explicitly dyadic and dominates `N'_r`; `O` is a set of adjacency
indices with `|O| = s`.  The left side has no primitivity restriction. -/
def SingleScaleEstimate (C0 : ℝ) : Prop :=
  1000 < C0 ∧
    ∀ (m s R : ℕ) (t : PlaneTree) (Nm : HeppMarking t)
      (mu : Multiplicities t) (compound : Finset (VPos t))
      (z : HeppLeaf t → Fin 4 → ℤ) (O : Finset (AdjacentIndex m)),
      t.isValid = true →
      rootV t ∈ BranchNodes t →
      compound ⊆ Leaves t →
      totalMultiplicity mu = m →
      IsSeparatedEmbedding Nm z →
      SatisfiesSingleScaleCondition Nm mu →
      IsDyadicNat R →
      accumulatedScale Nm mu (rootV t) ≤ R →
      O.card = s →
      paperSum (M := m) (leafMultiplicity mu)
          (singleScaleChainWeight (m := m) z O) ≤
        singleScaleRHS C0 m s R t Nm mu compound

end
end Anderson4D
