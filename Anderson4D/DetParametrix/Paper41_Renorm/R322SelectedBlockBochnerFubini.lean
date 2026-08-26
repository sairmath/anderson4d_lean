import Anderson4D.DetParametrix.Paper41_Renorm.R322SelectedBlockFubiniClosure

/-!
# Bochner-valued selected-block Fubini for R-322/R-324

The first selected-coordinate theorem was stated for real-valued kernels.
R-324 carries a signed complex Fourier factor outside the real primitive
kernel, so this file records the same exact product-measure reindex for an
arbitrary complete real normed target.  It also gives the concrete
`Finset (Fin m)` adapter used by the block selectors.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Complete normed target -/

/-- Exact selected/complement Fubini reindex for a complete
Bochner-valued integrand.  In particular, this applies with `E = ℂ`. -/
theorem integral_pi_eq_integral_complement_integral_selected_bochner
    {ι X E : Type*} [Fintype ι]
    [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (μ : Measure X) [SigmaFinite μ]
    (selected : ι → Prop) [DecidablePred selected]
    (f : (ι → X) → E)
    (hf :
      Integrable f
        (Measure.pi fun _ : ι => μ)) :
    (∫ x, f x ∂Measure.pi fun _ : ι => μ) =
      ∫ xC : (i : {i : ι // ¬ selected i}) → X,
        ∫ xB : (i : {i : ι // selected i}) → X,
          f
            ((MeasurableEquiv.piEquivPiSubtypeProd
                (fun _ : ι => X) selected).symm
              (xB, xC))
          ∂Measure.pi fun _ : {i : ι // selected i} => μ
        ∂Measure.pi fun _ : {i : ι // ¬ selected i} => μ := by
  let e :=
    MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : ι => X) selected
  let μB : Measure ((i : {i : ι // selected i}) → X) :=
    Measure.pi fun _ : {i : ι // selected i} => μ
  let μC : Measure ((i : {i : ι // ¬ selected i}) → X) :=
    Measure.pi fun _ : {i : ι // ¬ selected i} => μ
  have hpres :
      MeasurePreserving e
        (Measure.pi fun _ : ι => μ)
        (μB.prod μC) := by
    exact
      measurePreserving_piEquivPiSubtypeProd
        (fun _ : ι => μ) selected
  have hsplit :
      Integrable (fun x => f (e.symm x))
        (μB.prod μC) := by
    have hiff :=
      hpres.symm.integrable_comp_emb
        e.symm.measurableEmbedding
        (g := f)
    change Integrable (f ∘ e.symm) (μB.prod μC)
    exact hiff.mpr hf
  calc
    (∫ x, f x ∂Measure.pi fun _ : ι => μ) =
        ∫ x, f (e.symm x) ∂μB.prod μC := by
          symm
          simpa only [Function.comp_apply] using
            hpres.symm.integral_comp' f
    _ =
        ∫ xC, ∫ xB, f (e.symm (xB, xC)) ∂μB
          ∂μC :=
      integral_prod_symm _ hsplit

/-! ## Concrete finite-index block adapter -/

/-- Predicate form of membership in a selected `Fin` block.  Keeping this
as a named predicate gives the selected and complementary subtype products
the same canonical `Subtype.fintype` instances as the generic theorem. -/
def r322SelectedFinPredicate
    {m : ℕ} (B : Finset (Fin m)) (i : Fin m) : Prop :=
  i ∈ B

instance r322SelectedFinPredicate_decidable
    {m : ℕ} (B : Finset (Fin m)) :
    DecidablePred (r322SelectedFinPredicate B) := by
  intro i
  exact inferInstanceAs (Decidable (i ∈ B))

@[simp]
theorem r322SelectedFinPredicate_iff
    {m : ℕ} (B : Finset (Fin m)) (i : Fin m) :
    r322SelectedFinPredicate B i ↔ i ∈ B :=
  Iff.rfl

/-- Reassemble a `Fin m` tuple from its selected block coordinates and
its complementary coordinates. -/
def r322MergeSelectedFinCoordinates
    {m : ℕ} {X : Type*}
    (B : Finset (Fin m))
    (xB :
      {i : Fin m // r322SelectedFinPredicate B i} → X)
    (xC :
      {i : Fin m // ¬r322SelectedFinPredicate B i} → X) :
    Fin m → X :=
  (Equiv.piEquivPiSubtypeProd
      (r322SelectedFinPredicate B) (fun _ => X)).symm
    (xB, xC)

@[simp]
theorem r322MergeSelectedFinCoordinates_apply_mem
    {m : ℕ} {X : Type*}
    (B : Finset (Fin m))
    (xB :
      {i : Fin m // r322SelectedFinPredicate B i} → X)
    (xC :
      {i : Fin m // ¬r322SelectedFinPredicate B i} → X)
    (i : Fin m) (hi : i ∈ B) :
    r322MergeSelectedFinCoordinates B xB xC i =
      xB ⟨i, hi⟩ := by
  simp [r322MergeSelectedFinCoordinates,
    Equiv.piEquivPiSubtypeProd_symm_apply, hi]

@[simp]
theorem r322MergeSelectedFinCoordinates_apply_not_mem
    {m : ℕ} {X : Type*}
    (B : Finset (Fin m))
    (xB :
      {i : Fin m // r322SelectedFinPredicate B i} → X)
    (xC :
      {i : Fin m // ¬r322SelectedFinPredicate B i} → X)
    (i : Fin m) (hi : i ∉ B) :
    r322MergeSelectedFinCoordinates B xB xC i =
      xC ⟨i, hi⟩ := by
  simp [r322MergeSelectedFinCoordinates,
    Equiv.piEquivPiSubtypeProd_symm_apply, hi]

/-- `Finset (Fin m)` specialization of the exact Bochner Fubini split.
The selected block is the inner integral and the complement remains the
outer parameter tuple. -/
theorem integral_fin_pi_eq_integral_complement_integral_block_bochner
    {m : ℕ} {X E : Type*}
    [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (μ : Measure X) [SigmaFinite μ]
    (B : Finset (Fin m))
    (f : (Fin m → X) → E)
    (hf :
      Integrable f
        (Measure.pi fun _ : Fin m => μ)) :
    (∫ x, f x ∂Measure.pi fun _ : Fin m => μ) =
      ∫ xC :
          {i : Fin m //
            ¬r322SelectedFinPredicate B i} → X,
        ∫ xB :
            {i : Fin m //
              r322SelectedFinPredicate B i} → X,
          f (r322MergeSelectedFinCoordinates B xB xC)
          ∂Measure.pi fun _ :
            {i : Fin m //
              r322SelectedFinPredicate B i} => μ
        ∂Measure.pi fun _ :
          {i : Fin m //
            ¬r322SelectedFinPredicate B i} => μ := by
  convert
    integral_pi_eq_integral_complement_integral_selected_bochner
      μ (r322SelectedFinPredicate B) f hf using 1
  apply integral_congr_ae
  filter_upwards with xC
  apply integral_congr_ae
  filter_upwards with xB
  rfl

end

end Anderson4D
