import Anderson4D.Parametrix.L2CoefficientOperator

/-!
# The conditioned Hilbert--Schmidt resolvent difference

Mathlib does not presently expose a named Hilbert--Schmidt ideal API for
bounded operators on the torus `L²` space.  Following DESIGN §5.2, this file
therefore uses square summability of the matrix in the complete torus Fourier
basis as the certificate.

The central point is that this certificate is an operator ideal on the left:
left composition by a bounded operator preserves the double square sum.  The
algebraic identity `inverseGreen_sub_G` can consequently transfer any honest
certificate for `G * M * G` to the recentered inverse.  No certificate is
asserted for `G` itself.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators InnerProductSpace

/-- Fourier-matrix replacement for a Hilbert--Schmidt certificate.

The product index is ordered `(input, output)`, so Tonelli first sums the
output Fourier coefficients of the image of one basis vector. -/
def TorusFourierHSCertificate
    (A : TorusL2 →L[ℂ] TorusL2) : Prop :=
  Summable fun p : Z4 × Z4 =>
    ‖torusFourierMatrixCoeff A p.2 p.1‖ ^ 2

/-- Every fixed column of the Fourier matrix of a bounded operator is square
summable.  This is Parseval, not a Hilbert--Schmidt assertion: the outer sum
over columns need not converge. -/
theorem summable_normSq_torusFourierMatrixCoeff_column
    (A : TorusL2 →L[ℂ] TorusL2) (β : Z4) :
    Summable fun α : Z4 =>
      ‖torusFourierMatrixCoeff A α β‖ ^ 2 := by
  have hbase :=
    torusFourierBasis.orthonormal.inner_products_summable
      (x := A (torusFourierBasis β))
  have hneg :=
    hbase.comp_injective (Equiv.neg Z4).injective
  apply hneg.congr
  intro α
  rfl

/-- Quantitative column estimate under left composition. -/
theorem tsum_normSq_torusFourierMatrixCoeff_left_mul_le
    (L A : TorusL2 →L[ℂ] TorusL2) (β : Z4) :
    (∑' α : Z4,
        ‖torusFourierMatrixCoeff (L * A) α β‖ ^ 2) ≤
      ‖L‖ ^ 2 *
        ∑' α : Z4,
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 := by
  rw [tsum_norm_sq_torusFourierMatrixCoeff,
    tsum_norm_sq_torusFourierMatrixCoeff]
  have hnorm :
      ‖L (A (torusFourierBasis β))‖ ≤
        ‖L‖ * ‖A (torusFourierBasis β)‖ :=
    ContinuousLinearMap.le_opNorm L _
  simp only [mul_apply_eq_comp]
  simpa only [mul_pow] using
    pow_le_pow_left₀
      (norm_nonneg (L (A (torusFourierBasis β))))
      hnorm 2

/-- The Fourier square-summability certificate is preserved by left
composition by an arbitrary bounded operator. -/
theorem torusFourierHSCertificate_left_mul
    (L A : TorusL2 →L[ℂ] TorusL2)
    (hA : TorusFourierHSCertificate A) :
    TorusFourierHSCertificate (L * A) := by
  rw [TorusFourierHSCertificate,
    summable_prod_of_nonneg (fun _ => sq_nonneg _)] at hA ⊢
  refine ⟨fun β =>
    summable_normSq_torusFourierMatrixCoeff_column (L * A) β, ?_⟩
  have hmajor :
      Summable fun β : Z4 =>
        ‖L‖ ^ 2 *
          ∑' α : Z4,
            ‖torusFourierMatrixCoeff A α β‖ ^ 2 :=
    hA.2.mul_left _
  exact hmajor.of_nonneg_of_le
    (fun _ => tsum_nonneg fun _ => sq_nonneg _)
    (tsum_normSq_torusFourierMatrixCoeff_left_mul_le L A)

/-- Quantitative ideal estimate for the complete Fourier double sum. -/
theorem tsum_torusFourierMatrixCoeff_left_mul_le
    (L A : TorusL2 →L[ℂ] TorusL2)
    (hA : TorusFourierHSCertificate A) :
    (∑' p : Z4 × Z4,
        ‖torusFourierMatrixCoeff (L * A) p.2 p.1‖ ^ 2) ≤
      ‖L‖ ^ 2 *
        ∑' p : Z4 × Z4,
          ‖torusFourierMatrixCoeff A p.2 p.1‖ ^ 2 := by
  have hLA := torusFourierHSCertificate_left_mul L A hA
  have hAprod :
      (∑' p : Z4 × Z4,
          ‖torusFourierMatrixCoeff A p.2 p.1‖ ^ 2) =
        ∑' β : Z4, ∑' α : Z4,
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 :=
    hA.tsum_prod
  have hLAprod :
      (∑' p : Z4 × Z4,
          ‖torusFourierMatrixCoeff (L * A) p.2 p.1‖ ^ 2) =
        ∑' β : Z4, ∑' α : Z4,
          ‖torusFourierMatrixCoeff (L * A) α β‖ ^ 2 :=
    hLA.tsum_prod
  rw [hLAprod, hAprod, ← tsum_mul_left]
  have hAouter :
      Summable fun β : Z4 =>
        ∑' α : Z4,
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 :=
    (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mp hA |>.2
  exact
    ((torusFourierHSCertificate_left_mul L A hA |> fun h =>
      (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mp h |>.2)).tsum_le_tsum
      (tsum_normSq_torusFourierMatrixCoeff_left_mul_le L A)
      (hAouter.mul_left _)

/-- Conditioned Hilbert--Schmidt difference checkpoint from DESIGN §5.2.

Only `G * M * G` is assumed square summable.  The conclusion follows from
the resolvent identity and bounded left composition; in particular this does
not assume or claim that `G` itself has a square-summable Fourier matrix. -/
theorem inverseGreen_sub_G_torusFourierHSCertificate
    (G M : TorusL2 →L[ℂ] TorusL2)
    (h : LopInvertible G M)
    (hGMG : TorusFourierHSCertificate (G * M * G)) :
    TorusFourierHSCertificate (inverseGreen G M h - G) := by
  rw [inverseGreen_sub_G G M h]
  exact torusFourierHSCertificate_left_mul
    (((h.unit⁻¹ : (TorusL2 →L[ℂ] TorusL2)ˣ) :
      TorusL2 →L[ℂ] TorusL2))
    (G * M * G) hGMG

/-- Quantitative form of the conditioned difference checkpoint. -/
theorem tsum_inverseGreen_sub_G_fourierMatrixCoeff_le
    (G M : TorusL2 →L[ℂ] TorusL2)
    (h : LopInvertible G M)
    (hGMG : TorusFourierHSCertificate (G * M * G)) :
    (∑' p : Z4 × Z4,
        ‖torusFourierMatrixCoeff
          (inverseGreen G M h - G) p.2 p.1‖ ^ 2) ≤
      ‖((h.unit⁻¹ : (TorusL2 →L[ℂ] TorusL2)ˣ) :
          TorusL2 →L[ℂ] TorusL2)‖ ^ 2 *
        ∑' p : Z4 × Z4,
          ‖torusFourierMatrixCoeff (G * M * G) p.2 p.1‖ ^ 2 := by
  rw [inverseGreen_sub_G G M h]
  exact tsum_torusFourierMatrixCoeff_left_mul_le
    (((h.unit⁻¹ : (TorusL2 →L[ℂ] TorusL2)ˣ) :
      TorusL2 →L[ℂ] TorusL2))
    (G * M * G) hGMG

/-! ## The Green sandwich and the critical Fourier condition -/

/-- The Fourier matrix of `G * M * G` has one Green symbol at each
endpoint.  This statement holds for every bounded `M`; multiplication
structure is only used below to identify the middle coefficient as a function
of the conserved frequency `α + β`. -/
theorem torusFourierMatrixCoeff_greenL2Op_mul_mul_greenL2Op
    (M : TorusL2 →L[ℂ] TorusL2) (α β : Z4) :
    torusFourierMatrixCoeff
        (greenL2Op * M * greenL2Op) α β =
      greenL2Symbol α *
        torusFourierMatrixCoeff M α β *
          greenL2Symbol β := by
  have hright :
      greenL2Op (torusFourierBasis β) =
        greenL2Symbol β • torusFourierBasis β := by
    simpa only [coe_torusFourierBasis] using greenL2Op_char β
  have hleft (x : TorusL2) :
      ⟪torusFourierBasis (-α), greenL2Op x⟫_ℂ =
        greenL2Symbol α *
          ⟪torusFourierBasis (-α), x⟫_ℂ := by
    calc
      ⟪torusFourierBasis (-α), greenL2Op x⟫_ℂ =
          torusFourierCoeff (greenL2Op x) (-α) := by
        rw [← torusFourierBasis_repr,
          HilbertBasis.repr_apply_apply]
      _ = greenL2Symbol (-α) *
          torusFourierCoeff x (-α) :=
        torusFourierCoeff_greenL2Op x (-α)
      _ = greenL2Symbol α *
          ⟪torusFourierBasis (-α), x⟫_ℂ := by
        rw [greenL2Symbol_neg]
        rw [← torusFourierBasis_repr,
          HilbertBasis.repr_apply_apply]
  unfold torusFourierMatrixCoeff
  simp only [mul_apply_eq_comp, hright, map_smul,
    inner_smul_right, hleft]
  ring

/-- Fourier translation structure of a multiplication operator in the
paper's non-conjugated `(α, β)` sign convention. -/
def HasMultiplicationFourierProfile
    (M : TorusL2 →L[ℂ] TorusL2) (a : Z4 → ℂ) : Prop :=
  ∀ α β : Z4,
    torusFourierMatrixCoeff M α β = a (α + β)

/-- The exact Green-square convolution whose critical four-dimensional
estimate supplies the logarithm in DESIGN §5.2. -/
def greenL2SquaredConvolutionSummand
    (γ α : Z4) : ℝ :=
  ‖greenL2Symbol α‖ ^ 2 *
    ‖greenL2Symbol (γ - α)‖ ^ 2

theorem norm_greenL2Symbol_eq_paperSecondOrderModeDecay
    (k : Z4) :
    ‖greenL2Symbol k‖ = paperSecondOrderModeDecay k := by
  simp only [greenL2Symbol, paperSecondOrderModeDecay,
    paperModeNormSq, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg]
  positivity

theorem normSq_greenL2Symbol_le_l2LatticeRadialWeight
    (k : Z4) :
    ‖greenL2Symbol k‖ ^ 2 ≤
      4 * l2LatticeRadialWeight 4 k := by
  rw [norm_greenL2Symbol_eq_paperSecondOrderModeDecay,
    paperSecondOrderModeDecay_sq]
  exact (paperFourthOrderModeDecay_le k).trans
    (fourthOrderModeDecay_le_l2LatticeRadialWeight k)

theorem greenL2SquaredConvolutionSummand_le
    (γ α : Z4) :
    greenL2SquaredConvolutionSummand γ α ≤
      16 *
        (l2LatticeRadialWeight 4 α *
          l2LatticeRadialWeight 4 (γ - α)) := by
  unfold greenL2SquaredConvolutionSummand
  calc
    ‖greenL2Symbol α‖ ^ 2 *
          ‖greenL2Symbol (γ - α)‖ ^ 2 ≤
        (4 * l2LatticeRadialWeight 4 α) *
          (4 * l2LatticeRadialWeight 4 (γ - α)) := by
      exact mul_le_mul
        (normSq_greenL2Symbol_le_l2LatticeRadialWeight α)
        (normSq_greenL2Symbol_le_l2LatticeRadialWeight (γ - α))
        (sq_nonneg _)
        (mul_nonneg (by norm_num)
          (by unfold l2LatticeRadialWeight; positivity))
    _ = 16 *
        (l2LatticeRadialWeight 4 α *
          l2LatticeRadialWeight 4 (γ - α)) := by ring

/-- The exact Green-square convolution is summable without any critical
logarithmic estimate.  Only its *sharp* decay in the conserved frequency
remains separate below. -/
theorem summable_greenL2SquaredConvolutionSummand (γ : Z4) :
    Summable (greenL2SquaredConvolutionSummand γ) := by
  have hmajor :
      Summable fun α : Z4 =>
        16 *
          (l2LatticeRadialWeight 4 α *
            l2LatticeRadialWeight 4 (γ - α)) :=
    (summable_l2Lattice_convolution γ).mul_left 16
  exact hmajor.of_nonneg_of_le
    (fun α => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (greenL2SquaredConvolutionSummand_le γ)

/-- An unconditional, deliberately non-sharp `⟨γ⟩⁻³` bound obtained from
the existing lattice convolution library.  DESIGN §5.2 needs the sharper
critical `⟨γ⟩⁻⁴(1+log⟨γ⟩)` estimate isolated below. -/
theorem tsum_greenL2SquaredConvolutionSummand_le_coarse
    (γ : Z4) :
    (∑' α : Z4,
        greenL2SquaredConvolutionSummand γ α) ≤
      256 * l2LatticeRadialWeight 3 γ *
        ∑' α : Z4, l2LatticeRadialWeight 5 α := by
  have hmajor :
      Summable fun α : Z4 =>
        16 *
          (l2LatticeRadialWeight 4 α *
            l2LatticeRadialWeight 4 (γ - α)) :=
    (summable_l2Lattice_convolution γ).mul_left 16
  calc
    (∑' α : Z4,
        greenL2SquaredConvolutionSummand γ α) ≤
        ∑' α : Z4,
          16 *
            (l2LatticeRadialWeight 4 α *
              l2LatticeRadialWeight 4 (γ - α)) :=
      (summable_greenL2SquaredConvolutionSummand γ).tsum_le_tsum
        (greenL2SquaredConvolutionSummand_le γ) hmajor
    _ = 16 *
        ∑' α : Z4,
          (l2LatticeRadialWeight 4 α *
            l2LatticeRadialWeight 4 (γ - α)) := by
      rw [tsum_mul_left]
    _ ≤ 16 *
        (16 * l2LatticeRadialWeight 3 γ *
          ∑' α : Z4, l2LatticeRadialWeight 5 α) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_l2Lattice_convolution_bound γ) (by norm_num)
    _ = 256 * l2LatticeRadialWeight 3 γ *
        ∑' α : Z4, l2LatticeRadialWeight 5 α := by ring

/-- The Euclidean Japanese bracket `⟨γ⟩ = (1 + |γ|²)^(1/2)`. -/
def designJapaneseBracket (γ : Z4) : ℝ :=
  Real.sqrt (1 + ∑ i, (γ i : ℝ) ^ 2)

theorem one_le_designJapaneseBracket (γ : Z4) :
    1 ≤ designJapaneseBracket γ := by
  rw [designJapaneseBracket, Real.one_le_sqrt]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => sq_nonneg (γ i : ℝ))

/-- The literal sufficient weight from DESIGN §5.2:
`⟨γ⟩⁻⁴ (1 + log ⟨γ⟩)`. -/
def designCriticalHSWeight (γ : Z4) : ℝ :=
  (designJapaneseBracket γ ^ 4)⁻¹ *
    (1 + Real.log (designJapaneseBracket γ))

theorem designCriticalHSWeight_nonneg (γ : Z4) :
    0 ≤ designCriticalHSWeight γ := by
  exact mul_nonneg
    (inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) 4))
    (by
      have hlog :
          0 ≤ Real.log (designJapaneseBracket γ) :=
        Real.log_nonneg (one_le_designJapaneseBracket γ)
      linarith)

/-- The isolated critical lattice estimate needed to turn the exact Green
convolution into the logarithmic sufficient condition.  It is deliberately
separate from the operator conclusion: this is the remaining scalar
four-dimensional convolution lemma, not a disguised Hilbert--Schmidt
assumption. -/
def CriticalGreenSquaredConvolutionEstimate (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ γ : Z4,
      (∑' α : Z4,
          greenL2SquaredConvolutionSummand γ α) ≤
        C * designCriticalHSWeight γ

/-- Input/output coordinates followed by the conserved-frequency shear:
`(β, α) ↦ (α + β, α)`. -/
def torusHSInputOutputShear :
    (Z4 × Z4) ≃ (Z4 × Z4) :=
  (Equiv.prodComm Z4 Z4).trans l2LatticePairShear

/-- The DESIGN §5.2 logarithmic Fourier condition is sufficient for the
Green sandwich to have a square-summable Fourier matrix, once the independent
critical scalar convolution estimate is available. -/
theorem torusFourierHSCertificate_greenL2Op_mul_mul_greenL2Op
    (M : TorusL2 →L[ℂ] TorusL2) (a : Z4 → ℂ) (C : ℝ)
    (hprofile : HasMultiplicationFourierProfile M a)
    (hcritical : CriticalGreenSquaredConvolutionEstimate C)
    (ha :
      Summable fun γ : Z4 =>
        ‖a γ‖ ^ 2 * designCriticalHSWeight γ) :
    TorusFourierHSCertificate
      (greenL2Op * M * greenL2Op) := by
  let f : Z4 × Z4 → ℝ := fun q =>
    ‖a q.1‖ ^ 2 *
      greenL2SquaredConvolutionSummand q.1 q.2
  have hf : Summable f := by
    rw [summable_prod_of_nonneg]
    · constructor
      · intro γ
        exact ((summable_greenL2SquaredConvolutionSummand γ).mul_left
          (‖a γ‖ ^ 2)).congr
          (fun α => rfl)
      · have hmajor :
            Summable fun γ : Z4 =>
              C * (‖a γ‖ ^ 2 *
                designCriticalHSWeight γ) :=
          ha.mul_left C
        apply hmajor.of_nonneg_of_le
        · intro γ
          exact tsum_nonneg fun α =>
            mul_nonneg (sq_nonneg _)
              (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        · intro γ
          change
            (∑' α : Z4,
                ‖a γ‖ ^ 2 *
                  greenL2SquaredConvolutionSummand γ α) ≤ _
          rw [tsum_mul_left]
          calc
            ‖a γ‖ ^ 2 *
                  ∑' α : Z4,
                    greenL2SquaredConvolutionSummand γ α ≤
                ‖a γ‖ ^ 2 *
                  (C * designCriticalHSWeight γ) :=
              mul_le_mul_of_nonneg_left
                (hcritical.2 γ) (sq_nonneg _)
            _ = C * (‖a γ‖ ^ 2 *
                  designCriticalHSWeight γ) := by ring
    · intro q
      exact mul_nonneg (sq_nonneg _)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hshear :
      Summable fun p : Z4 × Z4 =>
        f (torusHSInputOutputShear p) :=
    hf.comp_injective torusHSInputOutputShear.injective
  unfold TorusFourierHSCertificate
  apply hshear.congr
  rintro ⟨β, α⟩
  rw [torusFourierMatrixCoeff_greenL2Op_mul_mul_greenL2Op,
    hprofile α β]
  dsimp [f, torusHSInputOutputShear, l2LatticePairShear,
    greenL2SquaredConvolutionSummand]
  rw [add_sub_cancel_left]
  rw [norm_mul, norm_mul, mul_pow, mul_pow]
  ring

/-- Concrete conditioned resolvent-difference consequence of the logarithmic
Fourier sufficient condition. -/
theorem inverseGreen_sub_greenL2Op_torusFourierHSCertificate
    (M : TorusL2 →L[ℂ] TorusL2) (a : Z4 → ℂ) (C : ℝ)
    (h : LopInvertible greenL2Op M)
    (hprofile : HasMultiplicationFourierProfile M a)
    (hcritical : CriticalGreenSquaredConvolutionEstimate C)
    (ha :
      Summable fun γ : Z4 =>
        ‖a γ‖ ^ 2 * designCriticalHSWeight γ) :
    TorusFourierHSCertificate
      (inverseGreen greenL2Op M h - greenL2Op) :=
  inverseGreen_sub_G_torusFourierHSCertificate
    greenL2Op M h
    (torusFourierHSCertificate_greenL2Op_mul_mul_greenL2Op
      M a C hprofile hcritical ha)

end

end Anderson4D
