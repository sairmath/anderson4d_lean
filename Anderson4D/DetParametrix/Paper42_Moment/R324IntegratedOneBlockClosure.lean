import Anderson4D.DetParametrix.Paper42_Moment.R324IntegratedCollapseClosure

/-!
# One genuine integrated primitive-block collapse for R-324

This file specializes the abstract one-block engine to the actual primitive
pairing sum supplied by Proposition 4.1.  The constants are chosen uniformly
before the scale, coupling, order, input family, and outer kernel.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- One concrete primitive block can be removed with the paper's exact
perturbative order.  Both the `E`-class fact and the pointwise majorant for
the genuine primitive sum are supplied by the proved Proposition 4.1. -/
theorem exists_r324OnePrimitiveCollapse_le_at_truncation
    (ρ : SmoothCutoff) :
    ∃ supportConstant primitiveConstant collapseConstant : ℝ,
      0 < supportConstant ∧
      0 < primitiveConstant ∧
      0 < collapseConstant ∧
      ∀ (lam ε A : ℝ) (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ)
        (Gp : T4 → ℝ) (x : T4),
        0 < lam → 0 ≤ A →
        0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
        n ≤ truncOrder ε →
        x ≠ 0 →
        (∀ j, Measurable (G j)) →
        IsAdmissiblePrimitiveInput n G →
        (∀ z, z ≠ 0 →
          |Gp z| ≤ A * invSqKer z) →
        Integrable
          (r322CollapseIntegrand Gp
            (primitiveKernelDiff
              ρ lam ε n hn G)
            greenFn x)
          (paperMeasure.prod paperMeasure) →
        |r322Collapse Gp
            (primitiveKernelDiff
              ρ lam ε n hn G)
            greenFn x| ≤
          A * (primitiveConstant * lam) ^ (2 * n) *
            collapseConstant * invSqKer x := by
  obtain ⟨supportConstant, primitiveConstant,
      hsupport, hprimitiveConstant, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨collapseConstant, hcollapseConstant,
      hcollapse⟩ :=
    exists_r322Collapse_le hsupport
  refine
    ⟨supportConstant, primitiveConstant, collapseConstant,
      hsupport, hprimitiveConstant, hcollapseConstant, ?_⟩
  intro lam ε A n hn G Gp x
    hlam hA hε hε1 hlog hntrunc hx
    hGmeas hinput hGp hint
  have hprimitive :=
    hprop lam ε n hn G hlam hε hε1 hntrunc hinput
  exact
    hcollapse primitiveConstant lam ε A n Gp
      (primitiveKernelDiff ρ lam ε n hn G) x
      hprimitiveConstant.le hlam.le hA
      hε hε1 hlog hx
      (measurable_primitiveKernelDiff
        ρ lam ε n hn G hGmeas)
      hprimitive.1
      (fun u => (hprimitive.2.2 u).1)
      hGp hint

/-- After one genuine primitive collapse, division by its proved scale and
the harmless diagonal adjustment produce an admissible input family for every
later primitive order.  This is the concrete induction step used in the
successive block collapse. -/
theorem
    exists_normalized_r324OnePrimitiveCollapse_admissible_at_truncation
    (ρ : SmoothCutoff) :
    ∃ supportConstant primitiveConstant collapseConstant : ℝ,
      0 < supportConstant ∧
      0 < primitiveConstant ∧
      0 < collapseConstant ∧
      ∀ (lam ε A : ℝ) (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ)
        (Gp : T4 → ℝ),
        0 < lam → 0 < A →
        0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
        n ≤ truncOrder ε →
        (∀ j, Measurable (G j)) →
        IsAdmissiblePrimitiveInput n G →
        MemEClassT4 Gp →
        (∀ z, z ≠ 0 →
          |Gp z| ≤ A * invSqKer z) →
        (∀ x,
          Integrable
            (r322CollapseIntegrand Gp
              (primitiveKernelDiff
                ρ lam ε n hn G)
              greenFn x)
            (paperMeasure.prod paperMeasure)) →
        ∀ laterOrder : ℕ,
          IsAdmissiblePrimitiveInput laterOrder
            (fun _ =>
              normalizedOffDiagonalRepresentative
                (A *
                  (primitiveConstant * lam) ^ (2 * n) *
                  collapseConstant)
                (r322Collapse Gp
                  (primitiveKernelDiff
                    ρ lam ε n hn G)
                  greenFn)) := by
  obtain ⟨supportConstant, primitiveConstant,
      hsupport, hprimitiveConstant, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨collapseConstant, hcollapseConstant,
      hnormalize⟩ :=
    exists_normalized_r322Collapse_admissible hsupport
  refine
    ⟨supportConstant, primitiveConstant, collapseConstant,
      hsupport, hprimitiveConstant, hcollapseConstant, ?_⟩
  intro lam ε A n hn G Gp
    hlam hA hε hε1 hlog hntrunc
    hGmeas hinput hGpMem hGpBound hint laterOrder
  have hprimitive :=
    hprop lam ε n hn G hlam hε hε1 hntrunc hinput
  exact
    hnormalize primitiveConstant lam ε A n Gp
      (primitiveKernelDiff ρ lam ε n hn G)
      hprimitiveConstant hlam hA hε hε1 hlog
      (measurable_primitiveKernelDiff
        ρ lam ε n hn G hGmeas)
      hGpMem hprimitive.1
      (fun u => (hprimitive.2.2 u).1)
      hGpBound hint laterOrder

end

end Anderson4D
