import Anderson4D.DetParametrix.Paper41_Renorm.R322SelectedBlockFubiniClosure
import Anderson4D.DetParametrix.Paper41_Renorm.R322ReductionClosure
import Anderson4D.DetParametrix.Paper41_Renorm.R322Collapse

/-!
# The exact selected-block kernel update for R-322

After the signed Fubini reindex, the selected primitive pairing coordinate
is summed and integrated before any absolute value is taken.  This file
identifies that complete kernel with `primitiveKernelDiff` and records the
result as an update of one named slot in a heterogeneous edge family.

All complementary coordinates, remaining finite sums, and remaining
integrals can be carried by an arbitrary outer parameter type.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The complete signed primitive coordinate -/

/-- The complete generalized `J` kernel carried by one selected primitive
block, with the right endpoint translated to zero. -/
def r322SelectedPrimitiveKernelSum
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z : T4) : ℝ :=
  ∑ σ ∈ primitiveFullPairings n,
    detJWith ρ lam ε n hn G σ z 0

/-- Summing the selected primitive pairing coordinate and all of its
internal variables gives exactly the signed kernel used by the collapse. -/
theorem r322SelectedPrimitiveKernelSum_eq_primitiveKernelDiff
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ) :
    r322SelectedPrimitiveKernelSum
        ρ lam ε n hn G =
      primitiveKernelDiff ρ lam ε n hn G := by
  funext z
  unfold r322SelectedPrimitiveKernelSum
    primitiveKernelDiff
  exact
    sum_detJWith_primitive_eq_primitiveKernel
      ρ lam ε n hn G z 0

/-! ## Updating exactly one heterogeneous edge -/

/-- Replace one named heterogeneous edge by the concrete proper-block
collapse.  Every other edge is retained definitionally. -/
def r322ReplaceEdge
    {ι : Type*} [DecidableEq ι]
    (edges : ι → T4 → ℝ) (slot : ι)
    (Gp J Gr : T4 → ℝ) :
    ι → T4 → ℝ :=
  Function.update edges slot (r322Collapse Gp J Gr)

@[simp]
theorem r322ReplaceEdge_apply_same
    {ι : Type*} [DecidableEq ι]
    (edges : ι → T4 → ℝ) (slot : ι)
    (Gp J Gr : T4 → ℝ) (u : T4) :
    r322ReplaceEdge edges slot Gp J Gr slot u =
      r322Collapse Gp J Gr u := by
  simp [r322ReplaceEdge]

theorem r322ReplaceEdge_apply_ne
    {ι : Type*} [DecidableEq ι]
    (edges : ι → T4 → ℝ) (slot other : ι)
    (hother : other ≠ slot)
    (Gp J Gr : T4 → ℝ) (u : T4) :
    r322ReplaceEdge edges slot Gp J Gr other u =
      edges other u := by
  simp [r322ReplaceEdge, hother]

/-- **Exact one-selected-block kernel identity.**

The inner product integral containing the complete primitive pairing sum is
literally the value of the updated heterogeneous edge at `slot`.  This is a
signed equality: neither the primitive sum nor the Green difference is put
under an absolute value. -/
theorem selectedPrimitiveInnerIntegral_eq_replacementEdge
    {ι : Type*} [DecidableEq ι]
    (edges : ι → T4 → ℝ) (slot : ι)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (Gp Gr : T4 → ℝ) (u : T4) :
    (∫ p,
        r322CollapseIntegrand Gp
          (r322SelectedPrimitiveKernelSum
            ρ lam ε n hn G)
          Gr u p
        ∂(paperMeasure.prod paperMeasure)) =
      r322ReplaceEdge edges slot Gp
        (primitiveKernelDiff
          ρ lam ε n hn G)
        Gr slot u := by
  rw [
    r322SelectedPrimitiveKernelSum_eq_primitiveKernelDiff]
  rw [r322ReplaceEdge_apply_same]
  rfl

/-! ## Complement coordinates and remaining sums stay outside -/

/-- Parameterized outer form of the exact update.

`ω` may contain all complementary spatial coordinates, the complementary
pairing fibre, and any remaining dependent finite-sum coordinates.  Hence
this equality can be inserted beneath the next outer sum or product measure
without changing their order. -/
theorem integral_outer_selectedPrimitiveInner_eq_updatedEdge
    {ι Ω : Type*} [DecidableEq ι]
    [MeasurableSpace Ω]
    (ν : Measure Ω)
    (outer : Ω → ℝ)
    (edges : Ω → ι → T4 → ℝ) (slot : ι)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Ω → Fin (2 * n - 1) → T4 → ℝ)
    (Gp Gr : Ω → T4 → ℝ)
    (u : Ω → T4) :
    (∫ ω,
        outer ω *
          (∫ p,
            r322CollapseIntegrand (Gp ω)
              (r322SelectedPrimitiveKernelSum
                ρ lam ε n hn (G ω))
              (Gr ω) (u ω) p
            ∂(paperMeasure.prod paperMeasure))
        ∂ν) =
      ∫ ω,
        outer ω *
          r322ReplaceEdge (edges ω) slot (Gp ω)
            (primitiveKernelDiff
              ρ lam ε n hn (G ω))
            (Gr ω) slot (u ω)
        ∂ν := by
  apply integral_congr_ae
  filter_upwards with ω
  rw [
    selectedPrimitiveInnerIntegral_eq_replacementEdge
      (edges := edges ω) (slot := slot)]

end

end Anderson4D
