import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualChainSignature

/-!
# Residual-refined physical fibres for R-324

Inside one fixed within-half contraction signature, the residual nested
schedule can still vary.  This file performs the second exact regrouping
used in paper Section 4.2: first by the residual endpoint signature and
then, within each refined fibre, with one common Fourier/Green skeleton.

Every covariance factor is nonnegative.  Consequently the norm of the
original fixed-signature physical integrand is exactly the sum of the
norms of the residual-refined integrands, not merely bounded by it.  This
is the pointwise cancellation-preserving entry to the recursive primitive
block collapse.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- Residual endpoint signatures realized inside one concrete
within-half signature fibre. -/
def momentResidualChainSignaturesAt
    (m : ℕ)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    Finset
      (Finset (Fin (2 * m)) ×
        Finset (Fin (2 * m))) :=
  (momentContractionFiber m s).image fun e =>
    momentResidualChainSignature e.1 e.2.1 e.2.2

/-- The contraction entities with both a fixed within-half signature and a
fixed residual-chain endpoint signature. -/
def momentRefinedContractionFiber
    (m : ℕ)
    (s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    Finset (MomentContraction m) :=
  (momentContractionFiber m s).filter fun e =>
    momentResidualChainSignature e.1 e.2.1 e.2.2 = r

@[simp]
theorem mem_momentRefinedContractionFiber
    {m : ℕ}
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    {e : MomentContraction m} :
    e ∈ momentRefinedContractionFiber m s r ↔
      momentContractionSignature e = s ∧
        momentResidualChainSignature e.1 e.2.1 e.2.2 = r := by
  simp [momentRefinedContractionFiber]

/-- The extra residual grouping costs at most `4^(2m)`. -/
theorem card_momentResidualChainSignaturesAt_le
    (m : ℕ)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    (momentResidualChainSignaturesAt m s).card ≤
      4 ^ (2 * m) := by
  calc
    (momentResidualChainSignaturesAt m s).card ≤
        Fintype.card
          (Finset (Fin (2 * m)) ×
            Finset (Fin (2 * m))) :=
      Finset.card_le_univ _
    _ = 4 ^ (2 * m) := by
      simp only [Fintype.card_prod,
        Fintype.card_finset, Fintype.card_fin]
      rw [show (4 : ℕ) = 2 * 2 by norm_num,
        mul_pow]

/-- Exact second regrouping of a fixed moment-signature fibre. -/
theorem sum_momentContractionFiber_by_residualChainSignature
    {m : ℕ}
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    {A : Type*} [AddCommMonoid A]
    (F : MomentContraction m → A) :
    (∑ r ∈ momentResidualChainSignaturesAt m s,
        ∑ e ∈ momentRefinedContractionFiber m s r,
          F e) =
      ∑ e ∈ momentContractionFiber m s, F e := by
  apply Finset.sum_fiberwise_of_maps_to
  intro e he
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

/-- All entities in one refined fibre have literally the same primitive
block schedule. -/
theorem momentNonemptyPrimitiveBlocks_eq_of_mem_refinedFiber
    {m : ℕ}
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    {e e' : MomentContraction m}
    (he : e ∈ momentRefinedContractionFiber m s r)
    (he' : e' ∈ momentRefinedContractionFiber m s r) :
    momentNonemptyPrimitiveBlocks e.1 e.2.1 e.2.2 =
      momentNonemptyPrimitiveBlocks e'.1 e'.2.1 e'.2.2 := by
  have heSig := mem_momentRefinedContractionFiber.mp he
  have he'Sig := mem_momentRefinedContractionFiber.mp he'
  exact momentNonemptyPrimitiveBlocks_eq_of_signatures_eq
    e e'
    (heSig.1.trans he'Sig.1.symm)
    (heSig.2.trans he'Sig.2.symm)

/-- The pointwise physical integrand of one residual-refined fibre. -/
def momentRefinedPhysicalIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  ∑ e ∈ momentRefinedContractionFiber m s r,
    deterministicMomentIntegrand ρ ε m α β
      e.1 e.2.1 e.2.2 x y z w v

/-- Exact regrouping of the physical integrand by residual endpoint
signature. -/
theorem momentSignaturePhysicalIntegrand_eq_sum_refined
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    momentSignaturePhysicalIntegrand
        ρ ε m α β s x y z w v =
      ∑ r ∈ momentResidualChainSignaturesAt m s,
        momentRefinedPhysicalIntegrand
          ρ ε m α β s r x y z w v := by
  unfold momentSignaturePhysicalIntegrand
    momentRefinedPhysicalIntegrand
  exact
    (sum_momentContractionFiber_by_residualChainSignature
      s fun e =>
        deterministicMomentIntegrand ρ ε m α β
          e.1 e.2.1 e.2.2 x y z w v).symm

/-- On every refined fibre the Fourier phase and both renormalized Green
skeletons remain common, while only the nonnegative covariance product is
summed. -/
theorem
    momentRefinedPhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentContractionFiber m s)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    momentRefinedPhysicalIntegrand
        ρ ε m α β s r x y z w v =
      momentFourierPhase α β x y z w *
        renormalizedGreenSkeleton e₀.1
          (assemble x y fun i => v (leftMomentIndex i)) *
        renormalizedGreenSkeleton e₀.2.1
          (assemble z w fun i => v (rightMomentIndex i)) *
        ∑ e ∈ momentRefinedContractionFiber m s r,
          (primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ) := by
  unfold momentRefinedPhysicalIntegrand
  apply Eq.trans ?_ (Finset.mul_sum _ _ _).symm
  apply Finset.sum_congr rfl
  intro e he
  rw [deterministicMomentIntegrand_eq_skeletons_mul_fullCovariance]
  have heSignature :
      momentContractionSignature e = s :=
    (mem_momentRefinedContractionFiber.mp he).1
  have he₀Signature :
      momentContractionSignature e₀ = s :=
    mem_momentContractionFiber.mp he₀
  obtain ⟨hleft, hright⟩ :=
    renormalizedGreenSkeletons_eq_of_momentContractionSignature_eq
      e e₀ (heSignature.trans he₀Signature.symm)
  rw [hleft, hright]

/-- Norm form of the refined common-skeleton factorization. -/
theorem
    norm_momentRefinedPhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentContractionFiber m s)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ‖momentRefinedPhysicalIntegrand
        ρ ε m α β s r x y z w v‖ =
      ‖renormalizedGreenSkeleton e₀.1
          (assemble x y fun i => v (leftMomentIndex i))‖ *
        ‖renormalizedGreenSkeleton e₀.2.1
          (assemble z w fun i => v (rightMomentIndex i))‖ *
        ∑ e ∈ momentRefinedContractionFiber m s r,
          primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing e.1 e.2.1 e.2.2) v := by
  rw [
    momentRefinedPhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
      ρ ε m α β s r e₀ he₀ x y z w v]
  have hphase :
      ‖momentFourierPhase α β x y z w‖ = 1 := by
    unfold momentFourierPhase
    simp only [norm_mul, norm_charT4, mul_one]
  have hsumNonneg :
      0 ≤ ∑ e ∈ momentRefinedContractionFiber m s r,
        primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing e.1 e.2.1 e.2.2) v := by
    exact Finset.sum_nonneg fun e _he =>
      primitiveCovarianceProduct_nonneg ρ ε m
        (momentCombinedPairing e.1 e.2.1 e.2.2) v
  rw [norm_mul, norm_mul, norm_mul, hphase, one_mul]
  have hcast :
      (∑ e ∈ momentRefinedContractionFiber m s r,
          (primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ)) =
        ((∑ e ∈ momentRefinedContractionFiber m s r,
          primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hsumNonneg]

/-- Pointwise exact additivity of the norm across residual-refined fibres.
No triangle inequality or pairing-cardinality loss occurs here. -/
theorem norm_momentSignaturePhysicalIntegrand_eq_sum_refined
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    ‖momentSignaturePhysicalIntegrand
        ρ ε m α β s x y z w v‖ =
      ∑ r ∈ momentResidualChainSignaturesAt m s,
        ‖momentRefinedPhysicalIntegrand
          ρ ε m α β s r x y z w v‖ := by
  obtain ⟨e₀, he₀⟩ :=
    momentContractionFiber_nonempty_iff_mem_signatures.mpr hs
  let skeletonNorm : ℝ :=
    ‖renormalizedGreenSkeleton e₀.1
        (assemble x y fun i => v (leftMomentIndex i))‖ *
      ‖renormalizedGreenSkeleton e₀.2.1
        (assemble z w fun i => v (rightMomentIndex i))‖
  have hfullToEntity :
      (∑ κ ∈ momentFullPairingFiber m s,
          primitiveCovarianceProduct ρ ε m κ.1 v) =
        ∑ e ∈ momentContractionFiber m s,
          primitiveCovarianceProduct ρ ε m
            (momentCombinedPairing e.1 e.2.1 e.2.2) v := by
    symm
    have h :=
      sum_momentContractionFiber_eq_sum_fullPairingFiber
        s fun κ =>
          primitiveCovarianceProduct ρ ε m κ.1 v
    change
      (∑ e ∈ momentContractionFiber m s,
        primitiveCovarianceProduct ρ ε m
          (momentCombinedPairing e.1 e.2.1 e.2.2) v) =
        ∑ κ ∈ momentFullPairingFiber m s,
          primitiveCovarianceProduct ρ ε m κ.1 v at h
    exact h
  calc
    ‖momentSignaturePhysicalIntegrand
        ρ ε m α β s x y z w v‖ =
        skeletonNorm *
          ∑ κ ∈ momentFullPairingFiber m s,
            primitiveCovarianceProduct ρ ε m κ.1 v := by
      exact
        norm_momentSignaturePhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
          ρ ε m α β s e₀ he₀ x y z w v
    _ = skeletonNorm *
          ∑ e ∈ momentContractionFiber m s,
            primitiveCovarianceProduct ρ ε m
              (momentCombinedPairing e.1 e.2.1 e.2.2) v := by
      rw [hfullToEntity]
    _ = skeletonNorm *
          ∑ r ∈ momentResidualChainSignaturesAt m s,
            ∑ e ∈ momentRefinedContractionFiber m s r,
              primitiveCovarianceProduct ρ ε m
                (momentCombinedPairing e.1 e.2.1 e.2.2) v := by
      rw [sum_momentContractionFiber_by_residualChainSignature]
    _ = ∑ r ∈ momentResidualChainSignaturesAt m s,
          skeletonNorm *
            ∑ e ∈ momentRefinedContractionFiber m s r,
              primitiveCovarianceProduct ρ ε m
                (momentCombinedPairing e.1 e.2.1 e.2.2) v := by
      rw [Finset.mul_sum]
    _ = ∑ r ∈ momentResidualChainSignaturesAt m s,
        ‖momentRefinedPhysicalIntegrand
          ρ ε m α β s r x y z w v‖ := by
      apply Finset.sum_congr rfl
      intro r _hr
      exact
        (norm_momentRefinedPhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
          ρ ε m α β s r e₀ he₀ x y z w v).symm

/-- Absorb the exponential number of residual schedules into a single
coarse `4^(2m)` factor. -/
theorem norm_momentSignaturePhysicalIntegrand_le_four_pow_mul_of_refined
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m)
    (x y z w : T4) (v : Fin (2 * m) → T4)
    (B : ℝ) (hB : 0 ≤ B)
    (hrefined :
      ∀ r ∈ momentResidualChainSignaturesAt m s,
        ‖momentRefinedPhysicalIntegrand
          ρ ε m α β s r x y z w v‖ ≤ B) :
    ‖momentSignaturePhysicalIntegrand
        ρ ε m α β s x y z w v‖ ≤
      4 ^ (2 * m) * B := by
  rw [norm_momentSignaturePhysicalIntegrand_eq_sum_refined
    ρ ε m α β s hs x y z w v]
  calc
    (∑ r ∈ momentResidualChainSignaturesAt m s,
        ‖momentRefinedPhysicalIntegrand
          ρ ε m α β s r x y z w v‖) ≤
        ∑ _r ∈ momentResidualChainSignaturesAt m s, B :=
      Finset.sum_le_sum fun r hr => hrefined r hr
    _ = ((momentResidualChainSignaturesAt m s).card : ℝ) * B := by
      simp
    _ ≤ (4 : ℝ) ^ (2 * m) * B := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_momentResidualChainSignaturesAt_le m s
      · exact hB

/-- Per-refined-schedule inserted bounds assemble into the exact
fixed-signature pointwise majorant, with the residual signature count
absorbed by replacing `C` with `4C`. -/
theorem
    scaled_norm_momentSignaturePhysicalIntegrand_le_insertedMajorant_of_refined
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m)
    (x y z w : T4) (v : Fin (2 * m) → T4)
    (scale C supportConstant : ℝ)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hrefined :
      ∀ r ∈ momentResidualChainSignaturesAt m s,
        scale *
            ‖momentRefinedPhysicalIntegrand
              ρ ε m α β s r x y z w v‖ ≤
          primitiveInsertedMajorant C lam ε
            supportConstant m x) :
    scale *
        ‖momentSignaturePhysicalIntegrand
          ρ ε m α β s x y z w v‖ ≤
      primitiveInsertedMajorant
        (4 * C) lam ε supportConstant m x := by
  rw [norm_momentSignaturePhysicalIntegrand_eq_sum_refined
    ρ ε m α β s hs x y z w v,
    Finset.mul_sum]
  calc
    (∑ r ∈ momentResidualChainSignaturesAt m s,
        scale *
          ‖momentRefinedPhysicalIntegrand
            ρ ε m α β s r x y z w v‖) ≤
        ∑ _r ∈ momentResidualChainSignaturesAt m s,
          primitiveInsertedMajorant C lam ε
            supportConstant m x :=
      Finset.sum_le_sum fun r hr => hrefined r hr
    _ = ((momentResidualChainSignaturesAt m s).card : ℝ) *
          primitiveInsertedMajorant C lam ε
            supportConstant m x := by
      simp
    _ ≤ (4 : ℝ) ^ (2 * m) *
          primitiveInsertedMajorant C lam ε
            supportConstant m x := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_momentResidualChainSignaturesAt_le m s
      · exact primitiveInsertedMajorant_nonneg hC hlam
    _ = primitiveInsertedMajorant
          (4 * C) lam ε supportConstant m x := by
      unfold primitiveInsertedMajorant
      rw [show (4 * C) * lam =
          4 * (C * lam) by ring,
        mul_pow]
      ring

end

end Anderson4D
