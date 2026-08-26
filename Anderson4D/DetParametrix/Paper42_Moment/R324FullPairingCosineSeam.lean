import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingTerminalFourier
import Anderson4D.Continuum.PrimitiveSymmetry

/-!
# The full-pairing terminal primitive kernel and its cosine seam

The endpoint Fourier identity leaves a complete, signed primitive-pairing
density on the retained terminal block.  This file performs the next two
exact operations from paper §4.2 Step 1:

* the terminal internal variables are integrated while the complete finite
  pairing sum remains inside the integral, producing the genuine
  heterogeneous `primitiveKernel`;
* after translation to the endpoint gap, membership in the paper's class
  `𝓔` kills the odd character component under the integral and leaves the
  real character cosine minus one.

No pointwise sine cancellation is asserted.  The cosine theorem carries
the two precise real integrability assumptions needed for Bochner
linearity; proving them from the reachable edge certificate is a separate
analytic step.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory ComplexConjugate
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

namespace R324FullPairingStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    {initialScale : Fin (2 * q + 1) → ℝ}

/-- The complete signed density on the retained terminal block, expressed
with the generalized closed integrand.  For primitive full pairings this
is exactly the standard primitive density; the formulation is chosen so
finite-sum Fubini feeds directly into the production terminal-collapse
theorem. -/
def terminalCompletePrimitiveDensity
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (t :
      Fin
          (2 * residualBlockOrder
            data.terminalData.terminal.2) →
        T4) : ℝ :=
  ∑ κB :
      {κB : PartialPairing
          (Fin
            (2 * residualBlockOrder
              data.terminalData.terminal.2)) //
        κB ∈ primitiveFullPairings
          (residualBlockOrder
            data.terminalData.terminal.2)},
    detJclosedIntegrandWith ρ ε
      (2 * residualBlockOrder
        data.terminalData.terminal.2)
      κB.1
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).internalEdges
      t

/-- The generalized terminal density is literally the complete standard
primitive-pairing sum. -/
theorem terminalCompletePrimitiveDensity_eq_sum_primitiveIntegrand
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (t :
      Fin
          (2 * residualBlockOrder
            data.terminalData.terminal.2) →
        T4) :
    data.terminalCompletePrimitiveDensity t =
      ∑ κB ∈
          primitiveFullPairings
            (residualBlockOrder
              data.terminalData.terminal.2),
        primitiveIntegrand ρ ε
          (residualBlockOrder
            data.terminalData.terminal.2)
          (data.trace.stopPrefix.headContext
            data.terminalData.terminal []
            data.stop_remaining_eq_singleton).one_le_blockOrder
          (data.trace.stopPrefix.headContext
            data.terminalData.terminal []
            data.stop_remaining_eq_singleton).internalEdges
          κB t := by
  unfold terminalCompletePrimitiveDensity
  exact
    sum_terminal_detJclosedIntegrandWith_eq_primitiveIntegrand
      ρ ε
      (residualBlockOrder data.terminalData.terminal.2)
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).one_le_blockOrder
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).internalEdges
      t

/-- The scalar left by endpoint Fourier integration is one genuine
predecessor edge times the complete terminal primitive density. -/
theorem terminalGroupedPrimitiveCore_eq_predecessor_mul_completeDensity
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (x : T4)
    (t :
      Fin
          (2 * residualBlockOrder
            data.terminalData.terminal.2) →
        T4) :
    data.terminalGroupedPrimitiveCore x t =
      data.trace.stopPrefix.state.edges
          (r324WithinHalfPredecessorSlot
            data.trace.stopPrefix.state
            data.terminalData.terminal)
          (x - t ⟨0, by
            have hn :=
              (data.trace.stopPrefix.headContext
                data.terminalData.terminal []
                data.stop_remaining_eq_singleton).one_le_blockOrder
            exact Nat.mul_pos (by decide)
              (Nat.zero_lt_of_lt hn)⟩) *
        data.terminalCompletePrimitiveDensity t := by
  rw [data.terminalCompletePrimitiveDensity_eq_sum_primitiveIntegrand]
  unfold terminalGroupedPrimitiveCore primitiveIntegrand
  have hcov :
      (∑ κB :
          {κB : PartialPairing
              (Fin
                (2 * residualBlockOrder
                  data.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder
                data.terminalData.terminal.2)},
          primitiveCovarianceProduct ρ ε
            (residualBlockOrder
              data.terminalData.terminal.2)
            κB.1 t) =
        ∑ κB ∈
            primitiveFullPairings
              (residualBlockOrder
                data.terminalData.terminal.2),
          primitiveCovarianceProduct ρ ε
            (residualBlockOrder
              data.terminalData.terminal.2)
            κB t := by
    symm
    apply Finset.sum_subtype
    intro κB
    rfl
  rw [hcov, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κB _hκB
  ring

/-- **Exact terminal-kernel integration.**  The complete pairing sum is
integrated as one grouped density and becomes the heterogeneous
`primitiveKernel` on the two retained endpoints. -/
theorem lamEps_pow_integral_terminalCompletePrimitiveDensity_eq_primitiveKernel
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (z w : T4)
    (hint :
      ∀ κB :
          {κB : PartialPairing
              (Fin
                (2 * residualBlockOrder
                  data.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder
                data.terminalData.terminal.2)},
        Integrable
          (fun u :
              Fin
                  (2 * residualBlockOrder
                    data.terminalData.terminal.2 - 2) →
                T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder
                data.terminalData.terminal.2)
              κB.1
              (data.trace.stopPrefix.headContext
                data.terminalData.terminal []
                data.stop_remaining_eq_singleton).internalEdges
              (primitiveAssemble
                (residualBlockOrder
                  data.terminalData.terminal.2)
                (data.trace.stopPrefix.headContext
                  data.terminalData.terminal []
                  data.stop_remaining_eq_singleton).one_le_blockOrder
                z w u))
          (Measure.pi fun _ => paperMeasure)) :
    lamEps lam ε ^
          (2 * residualBlockOrder
            data.terminalData.terminal.2) *
        (∫ u :
            Fin
                (2 * residualBlockOrder
                  data.terminalData.terminal.2 - 2) →
              T4,
          data.terminalCompletePrimitiveDensity
            (primitiveAssemble
              (residualBlockOrder
                data.terminalData.terminal.2)
              (data.trace.stopPrefix.headContext
                data.terminalData.terminal []
                data.stop_remaining_eq_singleton).one_le_blockOrder
              z w u)
          ∂Measure.pi fun _ => paperMeasure) =
      primitiveKernel ρ lam ε
        (residualBlockOrder
          data.terminalData.terminal.2)
        (data.trace.stopPrefix.headContext
          data.terminalData.terminal []
          data.stop_remaining_eq_singleton).one_le_blockOrder
        (data.trace.stopPrefix.headContext
          data.terminalData.terminal []
          data.stop_remaining_eq_singleton).internalEdges
        z w := by
  unfold terminalCompletePrimitiveDensity
  exact
    integral_sum_terminal_detJclosedIntegrandWith_eq_primitiveKernel
      ρ lam ε
      (residualBlockOrder data.terminalData.terminal.2)
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).one_le_blockOrder
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).internalEdges
      z w hint

/-- The terminal heterogeneous primitive kernel depends only on its
endpoint gap. -/
theorem terminalPrimitiveKernel_eq_diff
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (z w : T4) :
    primitiveKernel ρ lam ε
        (residualBlockOrder
          data.terminalData.terminal.2)
        (data.trace.stopPrefix.headContext
          data.terminalData.terminal []
          data.stop_remaining_eq_singleton).one_le_blockOrder
        (data.trace.stopPrefix.headContext
          data.terminalData.terminal []
          data.stop_remaining_eq_singleton).internalEdges
        z w =
      primitiveKernelDiff ρ lam ε
        (residualBlockOrder
          data.terminalData.terminal.2)
        (data.trace.stopPrefix.headContext
          data.terminalData.terminal []
          data.stop_remaining_eq_singleton).one_le_blockOrder
        (data.trace.stopPrefix.headContext
          data.terminalData.terminal []
          data.stop_remaining_eq_singleton).internalEdges
        (z - w) := by
  unfold primitiveKernelDiff
  rw [
    ← sum_detJWith_primitive_eq_primitiveKernel
      ρ lam ε
      (residualBlockOrder data.terminalData.terminal.2)
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).one_le_blockOrder
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).internalEdges
      z w,
    ← sum_detJWith_primitive_eq_primitiveKernel
      ρ lam ε
      (residualBlockOrder data.terminalData.terminal.2)
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).one_le_blockOrder
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).internalEdges
      (z - w) 0]
  apply Finset.sum_congr rfl
  intro κB _hκB
  exact
    detJWith_eq_diff ρ lam ε
      (residualBlockOrder data.terminalData.terminal.2)
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).one_le_blockOrder
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).internalEdges
      κB z w

end R324FullPairingStopTraceAssembly

end R324WithinHalfResidualPrefix

/-! ## Odd-character cancellation under `𝓔` symmetry -/

/-- The real and odd parts of a torus character.  The first is the
coordinate-free formal representative of `cos(β · u)`, avoiding any
choice of lift at the torus cut. -/
def r324CharacterCos (β : Z4) (u : T4) : ℝ :=
  (charT4 β u).re

def r324CharacterSin (β : Z4) (u : T4) : ℝ :=
  (charT4 β u).im

private def r324NegT4MeasurableEquiv : T4 ≃ᵐ T4 :=
  MeasurableEquiv.neg T4

private theorem measurePreserving_r324NegT4 :
    MeasurePreserving r324NegT4MeasurableEquiv
      paperMeasure paperMeasure := by
  rw [paperMeasure_eq_volume]
  change
    MeasurePreserving
      (fun u : T4 => fun i => -u i)
      (volume : Measure T4) (volume : Measure T4)
  exact
    measurePreserving_pi
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (f := fun _ u => -u) fun _ =>
        Measure.measurePreserving_neg _

private theorem charT4_neg_argument_conj
    (β : Z4) (u : T4) :
    charT4 β (-u) = conj (charT4 β u) := by
  calc
    charT4 β (-u) = charT4 (-β) u := by
      unfold charT4
      apply Finset.prod_congr rfl
      intro i _hi
      rw [fourier_apply, fourier_apply]
      rw [Pi.neg_apply, Pi.neg_apply, smul_neg, neg_smul]
    _ = conj (charT4 β u) := charT4_neg β u

@[simp]
theorem r324CharacterCos_neg_argument
    (β : Z4) (u : T4) :
    r324CharacterCos β (-u) = r324CharacterCos β u := by
  unfold r324CharacterCos
  rw [charT4_neg_argument_conj, Complex.conj_re]

@[simp]
theorem r324CharacterSin_neg_argument
    (β : Z4) (u : T4) :
    r324CharacterSin β (-u) = -r324CharacterSin β u := by
  unfold r324CharacterSin
  rw [charT4_neg_argument_conj, Complex.conj_im]

@[simp]
theorem r324CharacterCos_neg_frequency
    (β : Z4) (u : T4) :
    r324CharacterCos (-β) u = r324CharacterCos β u := by
  unfold r324CharacterCos
  rw [charT4_neg, Complex.conj_re]

/-- The sine component of a character has zero integral against an
`𝓔`-kernel.  Cancellation is obtained by the measure-preserving involution
`u ↦ -u`; it is not a pointwise assertion. -/
theorem integral_memEClass_mul_r324CharacterSin_eq_zero
    {J : T4 → ℝ}
    (hJ : MemEClassT4 J)
    (β : Z4)
    (_hint :
      Integrable
        (fun u =>
          J u * r324CharacterSin β u)
        paperMeasure) :
    (∫ u,
        J u * r324CharacterSin β u
        ∂paperMeasure) = 0 := by
  let F : T4 → ℝ :=
    fun u => J u * r324CharacterSin β u
  have hchange :
      (∫ u,
          F (r324NegT4MeasurableEquiv u)
          ∂paperMeasure) =
        ∫ u, F u ∂paperMeasure :=
    measurePreserving_r324NegT4.integral_comp' F
  have hodd :
      ∀ u,
        F (r324NegT4MeasurableEquiv u) = -F u := by
    intro u
    change
      J (-u) * r324CharacterSin β (-u) =
        -(J u * r324CharacterSin β u)
    rw [hJ.neg_invariant, r324CharacterSin_neg_argument]
    ring
  have hneg :
      (∫ u,
          F (r324NegT4MeasurableEquiv u)
          ∂paperMeasure) =
        -(∫ u, F u ∂paperMeasure) := by
    calc
      (∫ u,
          F (r324NegT4MeasurableEquiv u)
          ∂paperMeasure) =
          ∫ u, -F u ∂paperMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hodd
      _ = -(∫ u, F u ∂paperMeasure) := integral_neg F
  linarith

/-- **Cosine seam.**  Under an `𝓔`-kernel the integrated phase difference
is real and equals the same integral with the literal factor
`Re(e^{iβ·u}) - 1 = cos(β·u) - 1`.

The separate cosine and sine integrability assumptions are exactly what
is used by `integral_add`; in particular this theorem does not exploit the
junk value of a non-integrable Bochner integral. -/
theorem integral_memEClass_mul_characterSubOne_eq_cos
    {J : T4 → ℝ}
    (hJ : MemEClassT4 J)
    (β : Z4)
    (hcos :
      Integrable
        (fun u =>
          J u * (r324CharacterCos β u - 1))
        paperMeasure)
    (hsin :
      Integrable
        (fun u =>
          J u * r324CharacterSin β u)
        paperMeasure) :
    (∫ u,
        (J u : ℂ) * (charT4 β u - 1)
        ∂paperMeasure) =
      ∫ u,
        ((J u *
          (r324CharacterCos β u - 1) : ℝ) : ℂ)
        ∂paperMeasure := by
  let Fc : T4 → ℂ :=
    fun u =>
      ((J u *
        (r324CharacterCos β u - 1) : ℝ) : ℂ)
  let Fs : T4 → ℂ :=
    fun u =>
      Complex.I *
        ((J u * r324CharacterSin β u : ℝ) : ℂ)
  have hFc : Integrable Fc paperMeasure := by
    exact hcos.ofReal
  have hFs : Integrable Fs paperMeasure := by
    exact hsin.ofReal.const_mul Complex.I
  have hpoint :
      ∀ u,
        (J u : ℂ) * (charT4 β u - 1) =
          Fc u + Fs u := by
    intro u
    apply Complex.ext
    · simp [Fc, Fs, r324CharacterCos, r324CharacterSin]
    · simp [Fc, Fs, r324CharacterCos, r324CharacterSin]
  calc
    (∫ u,
        (J u : ℂ) * (charT4 β u - 1)
        ∂paperMeasure) =
        ∫ u, Fc u + Fs u ∂paperMeasure := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ =
        (∫ u, Fc u ∂paperMeasure) +
          ∫ u, Fs u ∂paperMeasure :=
      integral_add hFc hFs
    _ = ∫ u, Fc u ∂paperMeasure := by
      have hsinZero :=
        integral_memEClass_mul_r324CharacterSin_eq_zero
          hJ β hsin
      unfold Fs
      rw [integral_const_mul]
      have hcast :
          (∫ a : T4,
              ((J a * r324CharacterSin β a : ℝ) : ℂ)
              ∂paperMeasure) =
            ((∫ a : T4,
                J a * r324CharacterSin β a
                ∂paperMeasure : ℝ) : ℂ) :=
        integral_ofReal
      rw [hcast, hsinZero]
      simp
    _ = _ := by
      rfl

/-- Terminal specialization in the exact gap orientation left by
`charT4 β w - charT4 β z`: after factoring `charT4 β z`, the gap phase is
`charT4 (-β) (z-w) - 1`, whose real part is the same cosine. -/
theorem integral_terminalPrimitiveKernelDiff_mul_negCharacterSubOne_eq_cos
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (β : Z4)
    (hcos :
      Integrable
        (fun u =>
          primitiveKernelDiff ρ lam ε n hn G u *
            (r324CharacterCos β u - 1))
        paperMeasure)
    (hsin :
      Integrable
        (fun u =>
          primitiveKernelDiff ρ lam ε n hn G u *
            r324CharacterSin (-β) u)
        paperMeasure) :
    (∫ u,
        (primitiveKernelDiff ρ lam ε n hn G u : ℂ) *
          (charT4 (-β) u - 1)
        ∂paperMeasure) =
      ∫ u,
        ((primitiveKernelDiff ρ lam ε n hn G u *
          (r324CharacterCos β u - 1) : ℝ) : ℂ)
        ∂paperMeasure := by
  have h :=
    integral_memEClass_mul_characterSubOne_eq_cos
      (primitiveKernelDiff_memE
        ρ lam ε n hn G hG)
      (-β)
      (by
        simpa only [r324CharacterCos_neg_frequency] using hcos)
      hsin
  simpa only [r324CharacterCos_neg_frequency] using h

end

end Anderson4D
