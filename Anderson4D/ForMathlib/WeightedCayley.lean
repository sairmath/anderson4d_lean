import Mathlib

/-!
# A parent-function substitute for the weighted Cayley identity

Paper (5.24)--(5.25) needs only an upper bound for a weighted sum over
labelled link trees.  We do not formalize the stronger weighted Cayley
identity used in the paper.  Instead, after choosing a root, orient every
edge toward it and encode each of the other `q - 1` vertices by its parent.
This injects the relevant trees into

`ParentCode q = (Fin (q - 1) → Fin q)`.

The sum over *all* parent functions factorizes exactly.  With parent weights
`1 + w i` it is

`(q + ∑ i, w i) ^ (q - 1)`.

Thus any injectively parent-encoded tree family whose tree weight is bounded
by its code weight satisfies the inequality required at (5.24).  This is a
documented proof substitution: the conclusion is weaker than the paper's
exact weighted Cayley formula, but is precisely the estimate consumed by
Proposition 5.6.

All statements below include `q = 0` and `q = 1`.  In both cases the parent
slot type is empty and the empty product is `1`; explicit endpoint lemmas are
provided at the end.
-/

namespace Anderson4D

/-- A rooted parent-function code on `q` labels: one parent choice for each
of the `q - 1` non-root slots. -/
abbrev ParentCode (q : ℕ) := Fin (q - 1) → Fin q

/-- Multiplicative weight of a parent-function code. -/
def parentCodeWeight {R : Type*} [CommMonoid R] {q : ℕ}
    (a : Fin q → R) (p : ParentCode q) : R :=
  ∏ j, a (p j)

/-- Exact factorization of the sum over all parent functions. -/
theorem sum_parentCodeWeight {R : Type*} [CommSemiring R] (q : ℕ)
    (a : Fin q → R) :
    ∑ p : ParentCode q, parentCodeWeight a p =
      (∑ i, a i) ^ (q - 1) := by
  simpa [parentCodeWeight] using (Fintype.sum_pow a (q - 1)).symm

/-! ## Natural weights -/

/-- For natural weights, restricting to any finite set of parent functions
can only decrease the total weight. -/
theorem sum_parentCodeWeight_subset_nat (q : ℕ) (a : Fin q → ℕ)
    (P : Finset (ParentCode q)) :
    ∑ p ∈ P, parentCodeWeight a p ≤ (∑ i, a i) ^ (q - 1) := by
  calc
    ∑ p ∈ P, parentCodeWeight a p
        ≤ ∑ p : ParentCode q, parentCodeWeight a p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P)
        (fun p _ _ => Nat.zero_le (parentCodeWeight a p))
    _ = (∑ i, a i) ^ (q - 1) := sum_parentCodeWeight q a

/-- Exact all-parent-functions formula with the paper's natural weights
`1 + w i`. -/
theorem sum_parentCodeWeight_one_add_nat (q : ℕ) (w : Fin q → ℕ) :
    ∑ p : ParentCode q, parentCodeWeight (fun i => 1 + w i) p =
      (q + ∑ i, w i) ^ (q - 1) := by
  rw [sum_parentCodeWeight]
  congr 1
  simp [Finset.sum_add_distrib]

/-- Parent-function upper bound with natural weights, in the exact form used
by the proof substitution for paper (5.24)--(5.25). -/
theorem parentCode_one_add_bound_nat (q : ℕ) (w : Fin q → ℕ)
    (P : Finset (ParentCode q)) :
    ∑ p ∈ P, parentCodeWeight (fun i => 1 + w i) p ≤
      (q + ∑ i, w i) ^ (q - 1) := by
  calc
    ∑ p ∈ P, parentCodeWeight (fun i => 1 + w i) p
        ≤ ∑ p : ParentCode q, parentCodeWeight (fun i => 1 + w i) p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P)
        (fun p _ _ => Nat.zero_le _)
    _ = (q + ∑ i, w i) ^ (q - 1) :=
      sum_parentCodeWeight_one_add_nat q w

/-! ## Nonnegative real weights -/

theorem parentCodeWeight_nonneg_real {q : ℕ} {a : Fin q → ℝ}
    (ha : ∀ i, 0 ≤ a i) (p : ParentCode q) :
    0 ≤ parentCodeWeight a p := by
  exact Finset.prod_nonneg fun j _ => ha (p j)

/-- For nonnegative real weights, restricting to a finite set of parent
functions can only decrease the total weight. -/
theorem sum_parentCodeWeight_subset_real (q : ℕ) (a : Fin q → ℝ)
    (ha : ∀ i, 0 ≤ a i) (P : Finset (ParentCode q)) :
    ∑ p ∈ P, parentCodeWeight a p ≤ (∑ i, a i) ^ (q - 1) := by
  calc
    ∑ p ∈ P, parentCodeWeight a p
        ≤ ∑ p : ParentCode q, parentCodeWeight a p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P)
        (fun p _ _ => parentCodeWeight_nonneg_real ha p)
    _ = (∑ i, a i) ^ (q - 1) := sum_parentCodeWeight q a

/-- Exact all-parent-functions formula with nonnegative real weights
`1 + w i`.  Nonnegativity is not needed for the identity itself. -/
theorem sum_parentCodeWeight_one_add_real (q : ℕ) (w : Fin q → ℝ) :
    ∑ p : ParentCode q, parentCodeWeight (fun i => 1 + w i) p =
      ((q : ℝ) + ∑ i, w i) ^ (q - 1) := by
  rw [sum_parentCodeWeight]
  congr 1
  simp [Finset.sum_add_distrib]

/-- Parent-function upper bound for nonnegative real weights, in the exact
form consumed by paper (5.24)--(5.25). -/
theorem parentCode_one_add_bound_real (q : ℕ) (w : Fin q → ℝ)
    (hw : ∀ i, 0 ≤ w i) (P : Finset (ParentCode q)) :
    ∑ p ∈ P, parentCodeWeight (fun i => 1 + w i) p ≤
      ((q : ℝ) + ∑ i, w i) ^ (q - 1) := by
  calc
    ∑ p ∈ P, parentCodeWeight (fun i => 1 + w i) p
        ≤ ∑ p : ParentCode q, parentCodeWeight (fun i => 1 + w i) p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P)
        (fun p _ _ => parentCodeWeight_nonneg_real
          (fun i => add_nonneg zero_le_one (hw i)) p)
    _ = ((q : ℝ) + ∑ i, w i) ^ (q - 1) :=
      sum_parentCodeWeight_one_add_real q w

/-! ## Injectively encoded finite tree families -/

/-- **Parent-function proof substitution for weighted Cayley.**

Let `trees` be any finite family, `encode` an injection from that family into
rooted parent functions, and `degree` its degree data.  If the intended tree
weight `∏ i, (1 + w i) ^ (degree T i - 1)` is bounded by the corresponding
parent-code weight (the missing root factor is `≥ 1`), then the weighted tree
sum is at most `(q + ∑ i, w i)^(q-1)`.

This is the directly reusable interface for Proposition 5.6, Step 5; the
caller supplies only the combinatorial encoding and its pointwise weight
comparison. -/
theorem weightedCayley_le_of_parent_injection
    {τ : Type*} [DecidableEq τ] (q : ℕ)
    (trees : Finset τ) (encode : τ → ParentCode q)
    (hencode : Set.InjOn encode trees)
    (degree : τ → Fin q → ℕ) (w : Fin q → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hweight : ∀ T ∈ trees,
      (∏ i, (1 + w i) ^ (degree T i - 1)) ≤
        parentCodeWeight (fun i => 1 + w i) (encode T)) :
    ∑ T ∈ trees, ∏ i, (1 + w i) ^ (degree T i - 1) ≤
      ((q : ℝ) + ∑ i, w i) ^ (q - 1) := by
  calc
    ∑ T ∈ trees, ∏ i, (1 + w i) ^ (degree T i - 1)
        ≤ ∑ T ∈ trees,
            parentCodeWeight (fun i => 1 + w i) (encode T) :=
      Finset.sum_le_sum fun T hT => hweight T hT
    _ = ∑ p ∈ trees.image encode,
          parentCodeWeight (fun i => 1 + w i) p :=
      (Finset.sum_image hencode).symm
    _ ≤ ((q : ℝ) + ∑ i, w i) ^ (q - 1) :=
      parentCode_one_add_bound_real q w hw (trees.image encode)

/-- Natural-weight analogue of
`weightedCayley_le_of_parent_injection`. -/
theorem weightedCayley_le_of_parent_injection_nat
    {τ : Type*} [DecidableEq τ] (q : ℕ)
    (trees : Finset τ) (encode : τ → ParentCode q)
    (hencode : Set.InjOn encode trees)
    (degree : τ → Fin q → ℕ) (w : Fin q → ℕ)
    (hweight : ∀ T ∈ trees,
      (∏ i, (1 + w i) ^ (degree T i - 1)) ≤
        parentCodeWeight (fun i => 1 + w i) (encode T)) :
    ∑ T ∈ trees, ∏ i, (1 + w i) ^ (degree T i - 1) ≤
      (q + ∑ i, w i) ^ (q - 1) := by
  calc
    ∑ T ∈ trees, ∏ i, (1 + w i) ^ (degree T i - 1)
        ≤ ∑ T ∈ trees,
            parentCodeWeight (fun i => 1 + w i) (encode T) :=
      Finset.sum_le_sum fun T hT => hweight T hT
    _ = ∑ p ∈ trees.image encode,
          parentCodeWeight (fun i => 1 + w i) p :=
      (Finset.sum_image hencode).symm
    _ ≤ (q + ∑ i, w i) ^ (q - 1) :=
      parentCode_one_add_bound_nat q w (trees.image encode)

/-! ## Explicit small-cardinality endpoints -/

@[simp] theorem parentCodeWeight_zero {R : Type*} [CommMonoid R]
    (a : Fin 0 → R) (p : ParentCode 0) :
    parentCodeWeight a p = 1 := by
  simp [parentCodeWeight]

@[simp] theorem parentCodeWeight_one {R : Type*} [CommMonoid R]
    (a : Fin 1 → R) (p : ParentCode 1) :
    parentCodeWeight a p = 1 := by
  simp [parentCodeWeight]

/-- Natural-weight endpoint at `q = 0`. -/
theorem parentCode_one_add_bound_nat_zero (w : Fin 0 → ℕ)
    (P : Finset (ParentCode 0)) :
    ∑ p ∈ P, parentCodeWeight (fun i => 1 + w i) p ≤ 1 := by
  simpa using parentCode_one_add_bound_nat 0 w P

/-- Natural-weight endpoint at `q = 1`. -/
theorem parentCode_one_add_bound_nat_one (w : Fin 1 → ℕ)
    (P : Finset (ParentCode 1)) :
    ∑ p ∈ P, parentCodeWeight (fun i => 1 + w i) p ≤ 1 := by
  simpa using parentCode_one_add_bound_nat 1 w P

/-- At `q = 0`, every subset of parent codes has total real weight at most
the empty-product value `1`. -/
theorem parentCode_one_add_bound_real_zero (w : Fin 0 → ℝ)
    (P : Finset (ParentCode 0)) :
    ∑ p ∈ P, parentCodeWeight (fun i => 1 + w i) p ≤ 1 := by
  simpa using parentCode_one_add_bound_real 0 w (fun i => Fin.elim0 i) P

/-- At `q = 1`, there are no parent slots, so every subset of parent codes
has total real weight at most `1`. -/
theorem parentCode_one_add_bound_real_one (w : Fin 1 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (P : Finset (ParentCode 1)) :
    ∑ p ∈ P, parentCodeWeight (fun i => 1 + w i) p ≤ 1 := by
  simpa using parentCode_one_add_bound_real 1 w hw P

end Anderson4D
