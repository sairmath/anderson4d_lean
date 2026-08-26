import Mathlib
import Anderson4D.Continuum.Basic
import Anderson4D.Continuum.GreenFunction
import Anderson4D.Combinatorics.Pairing
import Anderson4D.Combinatorics.PairingExtract

/-!
# Deterministic parametrix: renormalized kernels and constants

Paper: D-Kdet — (3.1)–(3.2) — deterministic profile kernels

Definition layer for the deterministic side of the parametrix
expansion of Deng–Shen (arXiv:2607.10105): blueprint nodes **D-Kdet**
(the closed-form renormalized integrand, paper (3.6)), **D-RI closed
form** (the kernels `detRIfull`/`detRIprofile` and the `J` kernels,
paper (3.12)) and **D-C2q** (the renormalization constants,
paper (3.10)–(3.11)).  All paper indices `1..m` are shifted down by one
(0-based `Fin` indices); the external points `x = x_0`, `y = x_{m+1}`
occupy the two extra slots of `assemble`.

## Junk-totalization (DESIGN §5.7)

Every analytic definition below is total:
* `tsum` and Bochner integrals default to `0` off
  summability/integrability;
* index-overflow branches (which the good combinatorial class never
  hits) produce the factor `1` via `dite`;
* `detJ` at `q = 0` is `0`.
The analytic estimates carry the hypotheses excluding the junk branches.
-/

namespace Anderson4D

noncomputable section

open MeasureTheory

variable (ρ : SmoothCutoff) (lam ε : ℝ)

/-- The periodized mollified covariance `η_ε` on the torus:
`η_ε(x) = ε⁻⁴ η(x/ε)` with `η = ρ ⋆ ρ` (`SmoothCutoff.eta`), periodized
over the lattice `2πℤ⁴` through the canonical lift.  The `tsum` is
junk-totalized: it is `0` if the family is not summable; genuine cutoffs give
a finite sum. -/
def SmoothCutoff.etaEpsT4 (z : T4) : ℝ :=
  ∑' k : Z4, ε⁻¹ ^ (dim : ℕ) *
    ρ.eta fun i => ε⁻¹ * (torusLift z i + 2 * Real.pi * (k i : ℝ))

/-- The slot of the `i`-th integration variable inside the assembled
`(m+2)`-tuple: paper variable `x_{i+1}` (0-based shift). -/
def varIdx {m : ℕ} (i : Fin m) : Fin (m + 2) :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

@[simp] theorem varIdx_val {m : ℕ} (i : Fin m) : (varIdx i).val = i.val + 1 :=
  rfl

/-- Assemble the external points `x, y` and the `m` integration
variables `v` into the full `(m+2)`-tuple `(x, v_0, …, v_{m-1}, y)`:
slot `0` is `x`, slot `m+1` is `y`, slot `j` (for `1 ≤ j ≤ m`) is
`v (j-1)`. -/
def assemble {m : ℕ} (x y : T4) (v : Fin m → T4) : Fin (m + 2) → T4 :=
  fun j =>
    if _h0 : j.val = 0 then x
    else if _hm : j.val = m + 1 then y
    else v ⟨j.val - 1, by have := j.isLt; omega⟩

@[simp] theorem assemble_zero {m : ℕ} (x y : T4) (v : Fin m → T4) :
    assemble x y v 0 = x := by
  simp [assemble]

@[simp] theorem assemble_last {m : ℕ} (x y : T4) (v : Fin m → T4) :
    assemble x y v (Fin.last (m + 1)) = y := by
  simp [assemble]

@[simp] theorem assemble_varIdx {m : ℕ} (x y : T4) (v : Fin m → T4)
    (i : Fin m) : assemble x y v (varIdx i) = v i := by
  have hi := i.isLt
  simp only [assemble, varIdx]
  rw [dif_neg (by omega), dif_neg (by omega)]
  exact congrArg v (Fin.ext (by simp))

/-! ## The renormalized integrand (paper (3.6), node D-Kdet) -/

/-- Difference factor of the closed form (3.6) attached to an extracted
pair `p = (l, r)` (0-based):
`G(x_{r+1} - x_{r+2}) - G(x_{l+1} - x_{r+2})` in assembled-slot indices
(`varIdx` shifts by one; the slot `r+2` is always in range since
`r < m`).  No junk branch is needed here. -/
def diffFactor {m : ℕ} (xt : Fin (m + 2) → T4) (p : Fin m × Fin m) : ℝ :=
  greenFn (xt (varIdx p.2) - xt ⟨p.2.val + 2, by have := p.2.isLt; omega⟩) -
    greenFn (xt (varIdx p.1) - xt ⟨p.2.val + 2, by have := p.2.isLt; omega⟩)

/-- **Closed form of the renormalized integrand** (paper (3.6), 0-based;
node D-Kdet), evaluated on the assembled tuple
`xt = (x, v_0, …, v_{m-1}, y) : Fin (m+2) → T4`:

* chain part: over each edge `e : Fin (m+1)` the factor
  `G(xt e - xt (e+1))`, *excluded* (replaced by `1`) precisely when
  `e = r + 1` for some extracted pair `(l, r) ∈ extract κ` — the paper
  replaces that chain factor by the difference factor;
* difference part: the product of `diffFactor` over `extract κ`;
* covariance part: `η_ε(xt (i+1) - xt (κ i + 1))` over the pairs of `κ`
  (each pair counted once via its smaller endpoint).

Total by construction (`greenFn`, `etaEpsT4` are junk-totalized). -/
def detIntegrand (m : ℕ) (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) : ℝ :=
  (∏ e : Fin (m + 1),
      if e.val ∈ ((extract κ).map fun p => p.2.val + 1) then 1
      else greenFn (xt e.castSucc - xt e.succ)) *
    ((extract κ).map (diffFactor xt)).prod *
    ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
      ρ.etaEpsT4 ε (xt (varIdx i) - xt (varIdx (κ i)))

/-! ## The renormalized kernels (node D-RI closed form) -/

/-- **Fully integrated renormalized kernel** `(R^I λ_ε ξ_ε)`-type value
(paper (3.6) with all `m` internal variables integrated against
`paperMeasure^{⊗m}`): the deterministic value of the order-`m` term for
fully paired `κ`, and the total-integral form of the profile.  The
Bochner integral is junk-totalized (`0` off integrability). -/
def detRIfull (m : ℕ) (κ : PartialPairing (Fin m)) (x y : T4) : ℝ :=
  lamEps lam ε ^ m *
    ∫ v : Fin m → T4, detIntegrand ρ ε m κ (assemble x y v)
      ∂(Measure.pi fun _ => paperMeasure)

/-- **Profile kernel with singles free** (feeds the random layer): only
the paired variables (indices in `κ.pairSupport`) are integrated; the
single-index values are supplied by `z` (only the values of `z` on the
singles of `κ` matter).  Junk-totalized Bochner integral. -/
def detRIprofile (m : ℕ) (κ : PartialPairing (Fin m)) (x y : T4)
    (z : Fin m → T4) : ℝ :=
  lamEps lam ε ^ m *
    ∫ w : (↥κ.pairSupport → T4),
      detIntegrand ρ ε m κ (assemble x y fun i =>
        if h : i ∈ κ.pairSupport then w ⟨i, h⟩ else z i)
      ∂(Measure.pi fun _ => paperMeasure)

/-! ## The `J` kernels (paper (3.12), node D-C2q input) -/

/-- Difference factor of the `J` closed form (3.12) attached to an
extracted pair `p = (l, r)` of a pairing of the full tuple (no external
slots): `G(xtJ r - xtJ (r+1)) - G(xtJ l - xtJ (r+1))`.  Junk branch: if
`r + 1` overflows (`r` is the last index — never the case on the good
combinatorial class), the factor is `1`. -/
def diffFactorJ {n : ℕ} (xtJ : Fin n → T4) (p : Fin n × Fin n) : ℝ :=
  if h : p.2.val + 1 < n then
    greenFn (xtJ p.2 - xtJ ⟨p.2.val + 1, h⟩) -
      greenFn (xtJ p.1 - xtJ ⟨p.2.val + 1, h⟩)
  else 1

/-- **Closed form of the `J` integrand** (paper (3.12), 0-based): the
tuple `xtJ : Fin (2q) → T4` *is* the paper tuple `(x_1, …, x_{2q})`.
Chain factors `G(xtJ e - xtJ (e+1))` over `e : Fin (2q-1)`, excluded
(replaced by `1`) precisely when `e = r` for some `(l, r) ∈ extract σ`
(paper: the chain factor with left paper-index `r_i` is replaced by the
difference factor); then the `diffFactorJ` product and the covariance
product over the pairs of `σ`.  The chain indexing is guarded by a
`dite` (junk factor `1`) so that the formula is total also at `q = 0`;
the guard `e.val + 1 < 2q` always holds for `e : Fin (2q - 1)`. -/
def detJintegrand (q : ℕ) (σ : PartialPairing (Fin (2 * q)))
    (xtJ : Fin (2 * q) → T4) : ℝ :=
  (∏ e : Fin (2 * q - 1),
      if e.val ∈ ((extract σ).map fun p => p.2.val) then 1
      else if h : e.val + 1 < 2 * q then
        greenFn (xtJ ⟨e.val, by omega⟩ - xtJ ⟨e.val + 1, h⟩)
      else 1) *
    ((extract σ).map (diffFactorJ xtJ)).prod *
    ∏ i ∈ σ.pairSupport.filter (fun i => i < σ i),
      ρ.etaEpsT4 ε (xtJ i - xtJ (σ i))

/-- **The kernel `J_{2q,σ}`** (paper (3.12)): first and last of the `2q`
variables fixed at `z` and `w`, the internal `2q - 2` integrated against
`paperMeasure^{⊗(2q-2)}`; the assembled tuple `assemble z w v` (of
length `(2q-2)+2 = 2q`) is reindexed to `Fin (2q)` by `Fin.cast`.
Junk value `0` at `q = 0` (the paper only uses `q ≥ 1`); the Bochner
integral is junk-totalized. -/
def detJ : (q : ℕ) → PartialPairing (Fin (2 * q)) → T4 → T4 → ℝ
  | 0, _, _, _ => 0
  | q' + 1, σ, z, w =>
      lamEps lam ε ^ (2 * (q' + 1)) *
        ∫ v : Fin (2 * q') → T4,
          detJintegrand ρ ε (q' + 1) σ (fun j =>
            assemble z w v (Fin.cast (by omega : 2 * (q' + 1) = 2 * q' + 2) j))
          ∂(Measure.pi fun _ => paperMeasure)

/-- **The non-concatenation class** of paper §3.2: `σ` is full and no
proper prefix `{i : Fin (2q) | i ≤ p}` (with `p + 1 < 2q`) is fully
paired — equivalently (given fullness) `σ` does not split into two
pairings of complementary prefixes.  Stated with the bounded existential
over `p ∈ Finset.range (2q)` (no loss: `p + 1 < 2q` forces
`p < 2q`), which makes the predicate decidable. -/
def IsNonSplit {q : ℕ} (σ : PartialPairing (Fin (2 * q))) : Prop :=
  σ.IsFull ∧
    ¬∃ p ∈ Finset.range (2 * q), p + 1 < 2 * q ∧
      IsFullyPairedOn σ (Finset.univ.filter fun i : Fin (2 * q) => i.val ≤ p)

instance {q : ℕ} (σ : PartialPairing (Fin (2 * q))) :
    Decidable (IsNonSplit σ) :=
  decidable_of_iff (σ.IsFull ∧
    ¬∃ p ∈ Finset.range (2 * q), p + 1 < 2 * q ∧
      IsFullyPairedOn σ (Finset.univ.filter fun i : Fin (2 * q) => i.val ≤ p))
    Iff.rfl

/-! ## The renormalization constants (paper (3.10)–(3.11), node D-C2q) -/

/-- **The order-`2q` renormalization constant** (paper (3.10)): the sum
over the non-concatenation class of full pairings `σ` of `Fin (2q)` of
the total integral of `J_{2q,σ}(z, 0)` in `z` (translation invariance
makes fixing the second argument at `0` harmless — an M-layer lemma,
not part of this definition).  Junk-totalized integral. -/
def renormC2q (q : ℕ) : ℝ :=
  ∑ σ ∈ Finset.univ.filter
      (fun σ : PartialPairing (Fin (2 * q)) => IsNonSplit σ),
    ∫ z, detJ ρ lam ε q σ z 0 ∂paperMeasure

/-- **The renormalization constant `C_ε`** (paper (3.11)): the sum of
`renormC2q` over `1 ≤ q ≤ A = truncOrder ε = ⌊|log ε|⌋`. -/
def renormCEps : ℝ :=
  ∑ q ∈ Finset.Icc 1 (truncOrder ε), renormC2q ρ lam ε q

/-! ## Sanity: the `m = 0` kernel is the free Green's function -/

/-- Sanity check on the closed form: at order `m = 0` there are no
integration variables and no pairs (`extract κ = []`), the chain is the
single edge `x → y`, and the empty product measure is the Dirac
probability measure, so `detRIfull` collapses to `G(x - y)`. -/
theorem detRIfull_zero (κ : PartialPairing (Fin 0)) (x y : T4) :
    detRIfull ρ lam ε 0 κ x y = greenFn (x - y) := by
  have hconst : ∀ v : Fin 0 → T4,
      detIntegrand ρ ε 0 κ (assemble x y v) = greenFn (x - y) := by
    intro v
    have hext : extract κ = [] := rfl
    have hps := Finset.eq_empty_of_isEmpty
      (κ.pairSupport.filter fun i => i < κ i)
    simp [detIntegrand, hext, hps, assemble]
  have hμ : (Measure.pi fun _ : Fin 0 => paperMeasure) Set.univ = 1 := by
    rw [Measure.pi_of_empty]
    exact Measure.dirac_apply_of_mem (Set.mem_univ _)
  unfold detRIfull
  rw [integral_congr_ae (Filter.Eventually.of_forall hconst), integral_const]
  simp [measureReal_def, hμ]

end

end Anderson4D
