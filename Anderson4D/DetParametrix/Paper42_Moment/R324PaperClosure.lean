import Anderson4D.DetParametrix.Paper42_Moment.R324PaperIteration
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep23
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep4
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticResidualIteration
import Anderson4D.Main.DeterministicClosure

/-!
# Paper §4.2, Steps 2--4 closed onto the frozen deterministic moment

Paper: R-324 — §4.2 Steps 2(a)–(f) at one interval configuration
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The `(Cλ)^{2n}` scaling of the integrated (4.4) majorant -/

theorem primitiveInsertedMajorant_eq_base (C lam ε supportConstant : ℝ)
    (n : ℕ) (z : T4) :
    primitiveInsertedMajorant C lam ε supportConstant n z =
      (C * lam) ^ (2 * n) *
        primitiveInsertedMajorant 1 1 ε supportConstant 0 z := by
  unfold primitiveInsertedMajorant
  norm_num

theorem integral_primitiveInsertedMajorant_eq_base
    (C lam ε supportConstant : ℝ) (n : ℕ) :
    (∫ z, primitiveInsertedMajorant C lam ε supportConstant n z
        ∂paperMeasure) =
      (C * lam) ^ (2 * n) *
        ∫ z, primitiveInsertedMajorant 1 1 ε supportConstant 0 z
          ∂paperMeasure := by
  rw [← integral_const_mul]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun z =>
      primitiveInsertedMajorant_eq_base C lam ε supportConstant n z)

/-! ## Step 2(a): the frozen moment as a sum over full pairings of `[1,2m]` -/

/-- The (4.18) term attached to a full pairing `κ'` of `[1, 2m]`: the
value of the `2m+4`-fold integral at the unique contraction triple
`(κ₊, κ₋, π)` glued by `momentCombinedPairing` into `κ'`. -/
def r324Step2FullTerm (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull}) : ℂ :=
  deterministicMomentContractionTerm ρ ε m α β
    ((momentContractionEquivFullPairing m).symm κ)

/-- Step 2(a) in the abstract form of `r324Step2_wick_regroup`: a sum of
contraction terms is a sum over full pairings of `[1, 2m]`. -/
theorem r324Step2_sum_fullPairing (m : ℕ) {A : Type*} [AddCommMonoid A]
    (F : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} → A) :
    (∑ e : MomentContraction m,
        F (momentContractionEquivFullPairing m e)) =
      ∑ κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull}, F κ :=
  Equiv.sum_comp (momentContractionEquivFullPairing m) F

/-- **Step 2(a), on the frozen moment.**  By Wick the `(κ₊, κ₋, π)` sum
defining `deterministicMomentPairingSum` is the sum over full pairings
`κ'` of `[1, 2m]`. -/
theorem r324Step2_deterministicMomentPairingSum_eq (ρ : SmoothCutoff)
    (lam ε : ℝ) (m : ℕ) (α β : Z4) :
    deterministicMomentPairingSum ρ lam ε m α β =
      (lamEps lam ε ^ (2 * m) : ℂ) *
        ∑ κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull},
          r324Step2FullTerm ρ ε m α β κ := by
  have hsum :
      (∑ e : MomentContraction m,
          deterministicMomentContractionTerm ρ ε m α β e) =
        ∑ κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull},
          r324Step2FullTerm ρ ε m α β κ := by
    rw [← r324Step2_sum_fullPairing m (r324Step2FullTerm ρ ε m α β)]
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold r324Step2FullTerm
    rw [Equiv.symm_apply_apply]
  rw [deterministicMomentPairingSum_eq_contractionTerms, hsum]

/-! ## Step 2(c) and 2(f): fix the positions, then take absolute values -/

/-- The set of full pairings whose Definition 3.1 interval configuration
is `c`.  `cfg` is the Step 2(b) datum: the positions of the fully paired
subintervals extracted inside `[1, m]` and inside `[m+1, 2m]`. -/
def r324Step2ConfigFibre {m : ℕ}
    (cfg : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} →
      Finset (Fin (2 * m) × Fin (2 * m)))
    (c : Finset (Fin (2 * m) × Fin (2 * m))) :
    Finset {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} :=
  Finset.univ.filter fun κ => cfg κ = c

/-- The contribution of one *fixed positional configuration* to the
frozen deterministic moment.  No absolute value has been taken inside
it: this is exactly the quantity (4.18) that Steps 2(d)–(e) and Step 3
reduce, and only the outer sum over configurations is estimated in
modulus (Step 2(f)). -/
def r324Step2ConfigSum (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (cfg : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} →
      Finset (Fin (2 * m) × Fin (2 * m)))
    (c : Finset (Fin (2 * m) × Fin (2 * m))) : ℂ :=
  (lamEps lam ε ^ (2 * m) : ℂ) *
    ∑ κ ∈ r324Step2ConfigFibre cfg c, r324Step2FullTerm ρ ε m α β κ

theorem r324Step2_deterministicMomentPairingSum_eq_configSum
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (cfg : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} →
      Finset (Fin (2 * m) × Fin (2 * m)))
    (hcfg : ∀ κ, cfg κ ∈ intervalConfigs (2 * m)) :
    deterministicMomentPairingSum ρ lam ε m α β =
      ∑ c ∈ intervalConfigs (2 * m),
        r324Step2ConfigSum ρ lam ε m α β cfg c := by
  have hfib :
      (∑ c ∈ intervalConfigs (2 * m),
          ∑ κ ∈ r324Step2ConfigFibre cfg c, r324Step2FullTerm ρ ε m α β κ) =
        ∑ κ : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull},
          r324Step2FullTerm ρ ε m α β κ :=
    Finset.sum_fiberwise_of_maps_to (fun κ _ => hcfg κ) _
  rw [r324Step2_deterministicMomentPairingSum_eq]
  unfold r324Step2ConfigSum
  rw [← Finset.mul_sum, hfib]

/-- **Step 2(c) and 2(f), assembled.**  "We may fix the positions of
these subintervals at `O(C^m)` cost", and only *after* the removals do
we take absolute values.  The positional count is the proved
`card_intervalConfigs_two_mul_le`, so the cost is `16^m`. -/
theorem r324Step2_norm_le_of_configBound
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (cfg : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} →
      Finset (Fin (2 * m) × Fin (2 * m)))
    (hcfg : ∀ κ, cfg κ ∈ intervalConfigs (2 * m))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ c ∈ intervalConfigs (2 * m),
      ‖r324Step2ConfigSum ρ lam ε m α β cfg c‖ ≤ B) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤ (16 : ℝ) ^ m * B := by
  rw [r324Step2_deterministicMomentPairingSum_eq_configSum ρ lam ε m α β
    cfg hcfg]
  have hcard : (((intervalConfigs (2 * m)).card : ℕ) : ℝ) ≤ (16 : ℝ) ^ m := by
    have := card_intervalConfigs_two_mul_le m
    calc (((intervalConfigs (2 * m)).card : ℕ) : ℝ) ≤ ((16 ^ m : ℕ) : ℝ) :=
          Nat.cast_le.mpr this
      _ = (16 : ℝ) ^ m := by push_cast; ring
  calc
    ‖∑ c ∈ intervalConfigs (2 * m),
        r324Step2ConfigSum ρ lam ε m α β cfg c‖ ≤
        ∑ c ∈ intervalConfigs (2 * m),
          ‖r324Step2ConfigSum ρ lam ε m α β cfg c‖ := norm_sum_le _ _
    _ ≤ ((intervalConfigs (2 * m)).card : ℝ) * B := by
        simpa [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (intervalConfigs (2 * m))
            (fun c => ‖r324Step2ConfigSum ρ lam ε m α β cfg c‖) B hB
    _ ≤ (16 : ℝ) ^ m * B := mul_le_mul_of_nonneg_right hcard hB0

/-! ## Step 2(d)–(e): the successive removal, instantiated at `[1, 2m]`

The paper removes the fully paired subintervals extracted inside `[1, m]`
and, independently, those extracted inside `[m+1, 2m]`.  Definition 3.1's
subintervals never straddle the cut, so on a surviving chain slot of
`Ĩ₀ = [1, 2m] \ ∪ I_i` the two families simply concatenate. -/

theorem r324RemovedSites_append (Is Js : List R324RemovedInterval) :
    r324RemovedSites (Is ++ Js) =
      r324RemovedSites Is + r324RemovedSites Js := by
  simp only [r324RemovedSites, List.map_append, List.sum_append]
  ring

/-- **The §4.1 iteration at the doubled carrier.**  One application of
`exists_r324ReducedInput_admissible` per surviving slot of `Ĩ₀`, fed with
the subintervals removed on that slot from either half.  The surviving
inputs are the admissible `H`'s of (4.13) and the gained factors multiply
to `(Cλ)^{#removed}` by `Finset.prod_pow_eq_pow_sum`. -/
theorem exists_r324Step2Iteration (ρ : SmoothCutoff) :
    ∃ Citer : ℝ, 0 < Citer ∧
      ∀ (lam ε : ℝ) (k : ℕ) (Gp : Fin (2 * k - 1) → T4 → ℝ)
        (IsL IsR : Fin (2 * k - 1) → List R324RemovedInterval),
        0 < lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        IsAdmissiblePrimitiveInput k Gp →
        (∀ j, Measurable (Gp j)) →
        (∀ j, ∀ I ∈ IsL j, I.order ≤ truncOrder ε) →
        (∀ j, ∀ I ∈ IsR j, I.order ≤ truncOrder ε) →
        (∀ j, R324RemovalIntegrable ρ lam ε (Gp j) (IsL j ++ IsR j)) →
          IsAdmissiblePrimitiveInput k
              (fun j => r324ReducedInput ρ lam ε Citer (Gp j)
                (IsL j ++ IsR j)) ∧
            (∀ j, Measurable
              (r324ReducedInput ρ lam ε Citer (Gp j) (IsL j ++ IsR j))) ∧
            ∏ j, r324RemovalScale Citer lam (IsL j ++ IsR j) =
              (Citer * lam) ^
                ∑ j, (r324RemovedSites (IsL j) + r324RemovedSites (IsR j)) := by
  obtain ⟨Citer, hCiter, hiter⟩ := exists_r324PaperIteration ρ
  refine ⟨Citer, hCiter, ?_⟩
  intro lam ε k Gp IsL IsR hlam hε hε1 hlog hGp hGpmeas htruncL htruncR hint
  obtain ⟨hadm, hmeas, hprod⟩ :=
    hiter lam ε k Gp (fun j => IsL j ++ IsR j) hlam hε hε1 hlog hGp hGpmeas
      (fun j I hI => by
        rcases List.mem_append.mp hI with h | h
        · exact htruncL j I h
        · exact htruncR j I h) hint
  refine ⟨hadm, hmeas, hprod.trans ?_⟩
  exact congrArg _
    (Finset.sum_congr rfl fun j _ => r324RemovedSites_append (IsL j) (IsR j))

/-! ## Steps 2(d)–3: what the removal leaves, at one fixed configuration

After the removals only a *primitive* pairing `κ₀` on `2k` sites survives,
carrying the new inputs `H` of (4.13); Step 3 integrates the four external
legs, reduces the nested chain by the elementary eight-dimensional
integral, and applies (4.4) one last time — leaving the single integral
`∫ |J̃_{2k,prim}|` of the surviving primitive kernel. -/

/-- **The one input Steps 2–3 take from the §4.1 iteration**, at one fixed
positional configuration, in exactly the form `R324Step1Reduction` records
it for Step 1: `V` is the configuration's contribution to (4.18), the
schedules `IsL`, `IsR` are the fully paired subintervals removed inside
`[1, m]` and inside `[m+1, 2m]`, they delete `2m - 2k` sites in total, and
after the removal `V` is dominated by the gained factor times the integral
of the surviving primitive kernel `J̃_{2k,prim}` built from the `H`'s. -/
def R324Step23FibreRemoval (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (Citer : ℝ) (k : ℕ) (hk : 1 ≤ k) (V : ℂ) : Prop :=
  ∃ (Gp : Fin (2 * k - 1) → T4 → ℝ)
    (IsL IsR : Fin (2 * k - 1) → List R324RemovedInterval),
    IsAdmissiblePrimitiveInput k Gp ∧
      (∀ j, Measurable (Gp j)) ∧
      (∀ j, ∀ I ∈ IsL j, I.order ≤ truncOrder ε) ∧
      (∀ j, ∀ I ∈ IsR j, I.order ≤ truncOrder ε) ∧
      (∀ j, R324RemovalIntegrable ρ lam ε (Gp j) (IsL j ++ IsR j)) ∧
      (∑ j, (r324RemovedSites (IsL j) + r324RemovedSites (IsR j))) =
        2 * m - 2 * k ∧
      ‖V‖ ≤ (∏ j, r324RemovalScale Citer lam (IsL j ++ IsR j)) *
        ∫ z, |primitiveKernelInsertedDiff ρ lam ε k hk
            (fun j => r324ReducedInput ρ lam ε Citer (Gp j)
              (IsL j ++ IsR j)) z|
          ∂paperMeasure

/-- **Steps 2(d)–3 at one configuration, closed.**  The surviving inputs
are admissible (the doubled-carrier iteration), so Proposition 4.1 applies
to the surviving primitive pairing and (4.4) bounds the last integral by
the inserted majorant.  Together with the `(Cλ)^{2m-2k}` gained by the
removals this is the per-configuration form of (4.19)–(4.20). -/
theorem exists_r324Step23_fibre_bound (ρ : SmoothCutoff) :
    ∃ Cred supportConstant Citer : ℝ,
      0 < Cred ∧ 0 < supportConstant ∧ 0 < Citer ∧
      ∀ (lam ε : ℝ) (m k : ℕ) (hk : 1 ≤ k) (V : ℂ),
        0 < lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → k ≤ truncOrder ε →
        R324Step23FibreRemoval ρ lam ε m Citer k hk V →
          ‖V‖ ≤ (Cred * lam) ^ (2 * m - 2 * k) *
            ∫ z, primitiveInsertedMajorant Cred lam ε supportConstant k z
              ∂paperMeasure := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨Citer, hCiter, hiter⟩ := exists_r324Step2Iteration ρ
  refine ⟨max Citer C, supportConstant, Citer,
    lt_max_of_lt_left hCiter, hsupport, hCiter, ?_⟩
  intro lam ε m k hk V hlam hε hε1 hlog hktrunc hrem
  obtain ⟨Gp, IsL, IsR, hGp, hGpmeas, htruncL, htruncR, hint, hsites, hV⟩ :=
    hrem
  set G : Fin (2 * k - 1) → T4 → ℝ :=
    fun j => r324ReducedInput ρ lam ε Citer (Gp j) (IsL j ++ IsR j) with hGdef
  obtain ⟨hadm, hmeas, hprod⟩ :=
    hiter lam ε k Gp IsL IsR hlam hε hε1 hlog hGp hGpmeas htruncL htruncR hint
  have hbounds := (hprop lam ε k hk G hlam hε hε1 hktrunc hadm).2.2
  -- the last application of (4.4)
  have hlast :
      (∫ z, |primitiveKernelInsertedDiff ρ lam ε k hk G z| ∂paperMeasure) ≤
        ∫ z, primitiveInsertedMajorant C lam ε supportConstant k z
          ∂paperMeasure :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
      (integrable_primitiveInsertedMajorant C lam ε supportConstant k hε)
      (Filter.Eventually.of_forall fun z => (hbounds z).2)
  have hM0 : (0 : ℝ) ≤
      ∫ z, primitiveInsertedMajorant 1 1 ε supportConstant 0 z ∂paperMeasure :=
    integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg zero_le_one zero_le_one
  have hscale0 : (0 : ℝ) ≤ ∏ j, r324RemovalScale Citer lam (IsL j ++ IsR j) :=
    Finset.prod_nonneg fun j _ =>
      (r324RemovalScale_pos hCiter hlam _).le
  have hbase : (0 : ℝ) ≤ Citer * lam := mul_nonneg hCiter.le hlam.le
  have hmono : ∀ n : ℕ, (Citer * lam) ^ n ≤ (max Citer C * lam) ^ n := by
    intro n
    exact pow_le_pow_left₀ hbase
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hlam.le) n
  have hmonoC : ∀ n : ℕ, (C * lam) ^ n ≤ (max Citer C * lam) ^ n := by
    intro n
    exact pow_le_pow_left₀ (mul_nonneg hC.le hlam.le)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hlam.le) n
  calc
    ‖V‖ ≤ (∏ j, r324RemovalScale Citer lam (IsL j ++ IsR j)) *
        ∫ z, |primitiveKernelInsertedDiff ρ lam ε k hk G z| ∂paperMeasure :=
      hV
    _ ≤ (∏ j, r324RemovalScale Citer lam (IsL j ++ IsR j)) *
          ∫ z, primitiveInsertedMajorant C lam ε supportConstant k z
            ∂paperMeasure :=
      mul_le_mul_of_nonneg_left hlast hscale0
    _ = (Citer * lam) ^ (2 * m - 2 * k) *
          ((C * lam) ^ (2 * k) *
            ∫ z, primitiveInsertedMajorant 1 1 ε supportConstant 0 z
              ∂paperMeasure) := by
      rw [hprod, hsites, integral_primitiveInsertedMajorant_eq_base]
    _ ≤ (max Citer C * lam) ^ (2 * m - 2 * k) *
          ((max Citer C * lam) ^ (2 * k) *
            ∫ z, primitiveInsertedMajorant 1 1 ε supportConstant 0 z
              ∂paperMeasure) := by
      refine mul_le_mul (hmono _) ?_ ?_ (pow_nonneg (by positivity) _)
      · exact mul_le_mul_of_nonneg_right (hmonoC _) hM0
      · exact mul_nonneg (pow_nonneg (mul_nonneg hC.le hlam.le) _) hM0
    _ = (max Citer C * lam) ^ (2 * m - 2 * k) *
          ∫ z, primitiveInsertedMajorant (max Citer C) lam ε supportConstant
            k z ∂paperMeasure := by
      rw [integral_primitiveInsertedMajorant_eq_base (max Citer C) lam ε
        supportConstant k]

/-! ## Steps 2--3 in the per-configuration shape the paper produces

`R324Step23Reduction` (`R324PaperStep23.lean`) records the output of
Steps 2--3 with a *single* surviving order `k`.  That is not what the
paper's Step 2 produces: the positional count fixes the interval
configuration first, and the surviving primitive pairing `κ₀` — hence
its order `k` — depends on the configuration.  This section restates the
hypothesis in that shape and shows that the paper's own arithmetic is
insensitive to the dependence: each configuration's bound

`(Cλ)^{2m-2k} · ∫ J̃_{k,prim}  ≤  (Cλ)^{2m-2k} · (Cλ)^{2k} · D/|log ε|`

collapses to the *`k`-free* number `(Cλ)^{2m} · D/|log ε|`, so the
positional `16^m` multiplies a single uniform bound exactly as in
Step 2(c). -/

/-- **The output of Steps 2(d)--3, per interval configuration.**

`cfg` is the Step 2(b) datum assigning to each full pairing of `[1,2m]`
the positions of its Definition 3.1 fully paired subintervals inside
`[1,m]` and inside `[m+1,2m]`.  For each configuration `c` the successive
removal deletes `2m - 2k` sites, gains `(Cλ)^{2m-2k}`, and leaves the
single integral of the surviving primitive inserted kernel — with `k`
allowed to depend on `c`. -/
def R324Step23ConfigReduction (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (Cred supportConstant : ℝ) : Prop :=
  ∃ cfg : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} →
      Finset (Fin (2 * m) × Fin (2 * m)),
    (∀ κ, cfg κ ∈ intervalConfigs (2 * m)) ∧
      ∀ c ∈ intervalConfigs (2 * m),
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧
          ‖r324Step2ConfigSum ρ lam ε m α β cfg c‖ ≤
            (Cred * lam) ^ (2 * m - 2 * k) *
              ∫ z, primitiveInsertedMajorant Cred lam ε supportConstant k z
                ∂paperMeasure

/-- **Steps 2 and 3 of §4.2, complete, in the per-configuration shape.**

Same conclusion as `exists_r324Step23_bound` — the paper's

`|E|P̂_m(α,β)|²| ≤ (Cλ)^{2m}|log ε|⁻¹ = λ_ε² · C (Cλ)^{2m-2}`,

i.e. (3.24) with `1` on the right — but consuming the honest
configuration-indexed output of the removal instead of a single global
surviving order.  The proof is the paper's: bound each configuration by
the `k`-free number `(Cλ)^{2m} D/|log ε|` via (4.4), then pay the
positional count `16^m` once. -/
theorem exists_r324Step23_config_bound (ρ : SmoothCutoff)
    {Cred supportConstant : ℝ}
    (hCred : 0 < Cred) (hsupport : 0 < supportConstant) :
    ∃ outerC powerC : ℝ, 0 < outerC ∧ 0 < powerC ∧
      ∀ (lam ε : ℝ) (m : ℕ) (α β : Z4),
        0 ≤ lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
        R324Step23ConfigReduction ρ lam ε m α β Cred supportConstant →
          ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
            lamEps lam ε ^ 2 * outerC * (powerC * lam) ^ (2 * m - 2) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hmaj⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  set D : ℝ := Cball * supportConstant ^ 2 + 2 * Creg with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  refine ⟨(4 * Cred * (D + 1)) ^ 2, 4 * Cred * (D + 1), by positivity,
    by positivity, ?_⟩
  intro lam ε m α β hlam hε hε1 hlog hm hred
  obtain ⟨cfg, hcfg, hconf⟩ := hred
  have hlog0 : (0 : ℝ) < |Real.log ε| := lt_of_lt_of_le one_pos hlog
  have hbase : (0 : ℝ) ≤ Cred * lam := mul_nonneg hCred.le hlam
  -- the `k`-free per-configuration bound
  set B : ℝ := (Cred * lam) ^ (2 * m) * (D / |Real.log ε|) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (pow_nonneg hbase _) (by positivity)
  have hB : ∀ c ∈ intervalConfigs (2 * m),
      ‖r324Step2ConfigSum ρ lam ε m α β cfg c‖ ≤ B := by
    intro c hc
    obtain ⟨k, hk1, hkm, hbound⟩ := hconf c hc
    have hsplit : (2 * m - 2 * k) + 2 * k = 2 * m := by omega
    have hpre : (0 : ℝ) ≤ (Cred * lam) ^ (2 * m - 2 * k) :=
      pow_nonneg hbase _
    calc
      ‖r324Step2ConfigSum ρ lam ε m α β cfg c‖ ≤
          (Cred * lam) ^ (2 * m - 2 * k) *
            ∫ z, primitiveInsertedMajorant Cred lam ε supportConstant k z
              ∂paperMeasure := hbound
      _ ≤ (Cred * lam) ^ (2 * m - 2 * k) *
            ((Cred * lam) ^ (2 * k) * (D / |Real.log ε|)) :=
        mul_le_mul_of_nonneg_left
          (hmaj Cred lam ε supportConstant k hε hε1 hsupport hlog) hpre
      _ = B := by
        rw [hBdef, ← mul_assoc, ← pow_add, hsplit]
  -- the positional count, paid once
  have hstep2 :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤ (16 : ℝ) ^ m * B :=
    r324Step2_norm_le_of_configBound ρ lam ε m α β cfg hcfg hB0 hB
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤ (16 : ℝ) ^ m * B :=
      hstep2
    _ = ((4 * Cred) * lam) ^ (2 * m) * D / |Real.log ε| := by
      have h16 : ((4 : ℝ) * Cred * lam) ^ (2 * m) =
          16 ^ m * (Cred * lam) ^ (2 * m) := by
        rw [show (4 : ℝ) * Cred * lam = 4 * (Cred * lam) by ring, mul_pow,
          show ((4 : ℝ) ^ (2 * m)) = 16 ^ m by rw [pow_mul]; norm_num]
      rw [hBdef, h16]; field_simp
    _ ≤ ((4 * Cred * (D + 1)) * lam) ^ (2 * m) / |Real.log ε| := by
      rw [div_le_div_iff_of_pos_right hlog0]
      have := mul_constant_le_absorbed_even_pow
        (base := (4 * Cred) * lam) (K := D) (q := m)
        (by positivity) hD0.le hm
      calc ((4 * Cred) * lam) ^ (2 * m) * D ≤
            (((4 * Cred) * lam) * (D + 1)) ^ (2 * m) := this
        _ = ((4 * Cred * (D + 1)) * lam) ^ (2 * m) := by ring_nf
    _ = lamEps lam ε ^ 2 * (4 * Cred * (D + 1)) ^ 2 *
          ((4 * Cred * (D + 1)) * lam) ^ (2 * m - 2) :=
      r324Step23_output_identity _ lam ε hm

/-- The per-configuration hypothesis is exactly what
`exists_r324Step23_fibre_bound` produces once the physical bridge
supplies `R324Step23FibreRemoval` at each configuration: the fibre bound
already delivers the shape `(Cλ)^{2m-2k} · ∫ J̃_{k,prim}` with `k`
depending on the configuration. -/
theorem r324Step23ConfigReduction_of_fibre
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {Cred supportConstant Citer : ℝ}
    (hfibre : ∀ (lam' ε' : ℝ) (m' k : ℕ) (hk : 1 ≤ k) (V : ℂ),
      0 < lam' → 0 < ε' → ε' ≤ 1 → 1 ≤ |Real.log ε'| → k ≤ truncOrder ε' →
      R324Step23FibreRemoval ρ lam' ε' m' Citer k hk V →
        ‖V‖ ≤ (Cred * lam') ^ (2 * m' - 2 * k) *
          ∫ z, primitiveInsertedMajorant Cred lam' ε' supportConstant k z
            ∂paperMeasure)
    (hlam : 0 < lam) (hε : 0 < ε) (hε1 : ε ≤ 1) (hlog : 1 ≤ |Real.log ε|)
    (cfg : {κ : PartialPairing (Fin (2 * m)) // κ.IsFull} →
      Finset (Fin (2 * m) × Fin (2 * m)))
    (hcfg : ∀ κ, cfg κ ∈ intervalConfigs (2 * m))
    (hremoval : ∀ c ∈ intervalConfigs (2 * m),
      ∃ (k : ℕ) (hk : 1 ≤ k), k ≤ m ∧ k ≤ truncOrder ε ∧
        R324Step23FibreRemoval ρ lam ε m Citer k hk
          (r324Step2ConfigSum ρ lam ε m α β cfg c)) :
    R324Step23ConfigReduction ρ lam ε m α β Cred supportConstant := by
  refine ⟨cfg, hcfg, ?_⟩
  intro c hc
  obtain ⟨k, hk, hkm, hktrunc, hrem⟩ := hremoval c hc
  exact ⟨k, hk, hkm,
    hfibre lam ε m k hk _ hlam hε hε1 hlog hktrunc hrem⟩

end

end Anderson4D
