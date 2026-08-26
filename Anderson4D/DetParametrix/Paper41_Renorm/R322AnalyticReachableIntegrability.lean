import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProperPrefixReachability
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticResidualFubini
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticEdgeCertificate
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticIterationClosure
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProperStepEstimate
import Anderson4D.DetParametrix.Paper42_Moment.R324IntegratedCollapseClosure

/-!
# Analytic side conditions for reachable R-322 states

The production R-322 state machine replaces one edge at a time by a genuine
two-variable collapse.  This file records analytic properties of those
reachable heterogeneous edge families.  In particular, measurability is
derived from the construction and is not carried as an extra hypothesis by
the residual-integral induction.

The substantially stronger section-integrability statements needed by the
current one-step Fubini API are kept separate below: they require absolute
integrability of generalized primitive blocks, not merely measurability of
their input kernels.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-! ## Measurability of a genuine collapse -/

/-- The R-322 collapse integrand is jointly measurable in its external
argument and its two integration variables. -/
theorem measurable_r322CollapseIntegrand_joint
    {Gp J Gr : T4 → ℝ}
    (hGp : Measurable Gp)
    (hJ : Measurable J)
    (hGr : Measurable Gr) :
    Measurable fun p : T4 × (T4 × T4) =>
      r322CollapseIntegrand Gp J Gr p.1 p.2 := by
  unfold r322CollapseIntegrand
  have hu : Measurable fun p : T4 × (T4 × T4) => p.1 :=
    measurable_fst
  have hleft : Measurable fun p : T4 × (T4 × T4) => p.2.1 :=
    measurable_fst.comp measurable_snd
  have hright : Measurable fun p : T4 × (T4 × T4) => p.2.2 :=
    measurable_snd.comp measurable_snd
  exact
    ((hGp.comp (hu.sub hleft)).mul
      (hJ.comp (hleft.sub hright))).mul
        ((hGr.comp hright).sub (hGr.comp hleft))

/-- A collapse of measurable kernels is measurable, independently of
whether a later quantitative argument has established its integrability.
This is legitimate for mathlib's totalized Bochner integral. -/
theorem measurable_r322Collapse
    {Gp J Gr : T4 → ℝ}
    (hGp : Measurable Gp)
    (hJ : Measurable J)
    (hGr : Measurable Gr) :
    Measurable (r322Collapse Gp J Gr) := by
  unfold r322Collapse
  exact
    (measurable_r322CollapseIntegrand_joint hGp hJ hGr)
      |>.stronglyMeasurable.integral_prod_right.measurable

/-! ## Absolute integrability of a generalized primitive block -/

/-- At every order at least two, the R-51 `lintegral` estimate implies
genuine Bochner integrability of each individual primitive summand.

This extraction is deliberately separate from Proposition 4.1's pointwise
kernel bound: it rules out the junk value of the totalized integral. -/
theorem integrable_primitiveIntegrand_assemble_of_admissible_ge_two
    (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {n : ℕ} (hn : 2 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hG : IsAdmissiblePrimitiveInput n G)
    (κB :
      {κ : PartialPairing (Fin (2 * n)) //
        κ ∈ primitiveFullPairings n})
    (z w : T4) :
    Integrable
      (fun v : Fin (2 * n - 2) → T4 =>
        primitiveIntegrand ρ ε n (by omega) G κB.1
          (primitiveAssemble n (by omega) z w v))
      (Measure.pi fun _ => paperMeasure) := by
  let hn1 : 1 ≤ n := by omega
  let μ : Measure (Fin (2 * n - 2) → T4) :=
    Measure.pi fun _ => paperMeasure
  let ordinarySum : ℝ≥0∞ :=
    ∑ κ ∈ primitiveFullPairings n,
      ∫⁻ v,
        ENNReal.ofReal
          |primitiveIntegrand ρ ε n hn1 G κ
            (primitiveAssemble n hn1 z w v)|
        ∂μ
  let insertedSum : ℝ≥0∞ :=
    ∑ κ ∈ primitiveFullPairings n,
      ∫⁻ v,
        ENNReal.ofReal
          |primitiveInsertedIntegrand ρ ε n hn1 G κ
            (primitiveAssemble n hn1 z w v)|
        ∂μ
  obtain ⟨Cperm, hperm⟩ := permSum_estimate
  obtain ⟨Ccov, Ccell, _hCcov, _hCcell, hsum⟩ :=
    sum_primitiveInsertedIntegrand_lintegral_le_r51GlobalDecayBound
      hperm ρ
  let q : ℕ := (compatibleCellCount ε).toNat
  have hqε : (q : ℤ) = compatibleCellCount ε := by
    dsimp only [q]
    exact Int.toNat_of_nonneg
      (compatibleCellCount_pos hε).le
  have hqpos : 0 < q := by
    by_contra hq
    have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq
    have hqNonpos :
        compatibleCellCount ε ≤ 0 := by
      apply Int.toNat_eq_zero.mp
      simpa only [q] using hqzero
    exact (not_le_of_gt (compatibleCellCount_pos hε)) hqNonpos
  letI : NeZero q := NeZero.of_pos hqpos
  have hnL :
      n ≤ n * (Nat.log 2 (4 * (2 * q)) + 1) := by
    calc
      n = n * 1 := by simp
      _ ≤ n * (Nat.log 2 (4 * (2 * q)) + 1) :=
        Nat.mul_le_mul_left n (Nat.succ_le_succ (Nat.zero_le _))
  let R : ℝ := 1 + 4 * ρ.radius
  let δ : ℝ := compatibleMeshSize ε
  let farCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4)
  let nearCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4)
  let Q : ℝ := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  have hinsertedBound :
      insertedSum ≤
        ENNReal.ofReal Q *
          (ENNReal.ofReal farCoeff +
            ENNReal.ofReal nearCoeff) *
          ENNReal.ofReal
            (primitiveR51GlobalDecayBound
              Cperm n q n δ R z w) := by
    simpa only [insertedSum, μ, R, δ, farCoeff,
      nearCoeff, Q, hn1] using
      hsum n hn G hG hε hε1 hqε n hnL z w
  have hinsertedTop : insertedSum < ⊤ :=
    hinsertedBound.trans_lt
      (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.add_lt_top.mpr
            ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩))
        ENNReal.ofReal_lt_top)
  let D : ℝ := ε ^ 2 + torusDistSq (z - w)
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith [torusDistSq_nonneg (z - w), sq_pos_of_pos hε]
  have hcomparison :
      ENNReal.ofReal D * ordinarySum ≤ insertedSum := by
    simpa only [D, ordinarySum, insertedSum, μ, hn1] using
      endpointFactor_mul_sum_primitiveIntegrand_lintegral_le_inserted
        ρ ε n hn1 G z w
  have hordinaryTop : ordinarySum < ⊤ := by
    have hproductTop :
        ENNReal.ofReal D * ordinarySum < ⊤ :=
      hcomparison.trans_lt hinsertedTop
    by_contra hnot
    have htop : ordinarySum = ⊤ :=
      top_unique (le_of_not_gt hnot)
    rw [htop] at hproductTop
    have hD0 : ENNReal.ofReal D ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hD)
    have heq : ENNReal.ofReal D * ⊤ = ⊤ := by
      simp [hD0]
    rw [heq] at hproductTop
    exact (lt_irrefl ⊤ hproductTop).elim
  have htermTop :
      (∫⁻ v,
          ENNReal.ofReal
            |primitiveIntegrand ρ ε n hn1 G κB.1
              (primitiveAssemble n hn1 z w v)|
          ∂μ) < ⊤ := by
    apply lt_of_le_of_lt _ hordinaryTop
    dsimp only [ordinarySum]
    exact Finset.single_le_sum
      (fun κ _hκ => (bot_le : (0 : ℝ≥0∞) ≤ _)) κB.2
  have hmeas :
      Measurable
        (fun v : Fin (2 * n - 2) → T4 =>
          primitiveIntegrand ρ ε n hn1 G κB.1
            (primitiveAssemble n hn1 z w v)) :=
    (measurable_primitiveIntegrand
      ρ ε n hn1 G hGmeas κB.1).comp
        (measurable_primitiveAssemble n hn1 z w)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa only [Real.norm_eq_abs, μ, hn1] using htermTop

/-- At primitive order one there are no internal variables.  Consequently
every assembled primitive summand is integrable over the zero-fold paper
product, without any analytic hypothesis on the input edge. -/
theorem integrable_primitiveIntegrand_assemble_one
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin 1 → T4 → ℝ)
    (κB :
      {κ : PartialPairing (Fin 2) //
        κ ∈ primitiveFullPairings 1})
    (z w : T4) :
    Integrable
      (fun v : Fin 0 → T4 =>
        primitiveIntegrand ρ ε 1 (by omega) G κB.1
          (primitiveAssemble 1 (by omega) z w v))
      (Measure.pi fun _ => paperMeasure) :=
  Integrable.of_subsingleton

/-- A measurable kernel remains measurable after zeroing its value at the
identity and dividing by a fixed normalization constant. -/
private theorem measurable_normalizedOffDiagonalRepresentative
    (C : ℝ) {f : T4 → ℝ} (hf : Measurable f) :
    Measurable (normalizedOffDiagonalRepresentative C f) := by
  unfold normalizedOffDiagonalRepresentative
  apply Measurable.const_mul
  unfold offDiagonalRepresentative
  exact Measurable.ite (measurableSet_singleton 0)
    measurable_const hf

/-- Absolute integrability of each raw generalized primitive summand from
the exact hypotheses carried by an edge certificate.

For orders at least two, each input edge is normalized off the identity,
the R-51 estimate is applied to the resulting admissible family, and the
heterogeneous scale product is restored.  The two integrands agree almost
everywhere because every primitive-chain edge avoids its diagonal almost
surely.  Order one is the zero-dimensional base case. -/
theorem integrable_primitiveIntegrand_assemble_of_scaled_offDiagonal
    (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {n : ℕ} (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (Cedge : Fin (2 * n - 1) → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hCedge : ∀ j, 0 < Cedge j)
    (hGmem : ∀ j, MemEClassT4 (G j))
    (hGbound : ∀ j z, z ≠ 0 →
      |G j z| ≤ Cedge j * invSqKer z)
    (κB :
      {κ : PartialPairing (Fin (2 * n)) //
        κ ∈ primitiveFullPairings n})
    (z w : T4) :
    Integrable
      (fun v : Fin (2 * n - 2) → T4 =>
        primitiveIntegrand ρ ε n hn G κB.1
          (primitiveAssemble n hn z w v))
      (Measure.pi fun _ => paperMeasure) := by
  by_cases hnOne : n = 1
  · subst n
    exact integrable_primitiveIntegrand_assemble_one
      ρ ε G κB z w
  · have hnTwo : 2 ≤ n := by omega
    let H : Fin (2 * n - 1) → T4 → ℝ :=
      fun j =>
        normalizedOffDiagonalRepresentative
          (Cedge j) (G j)
    have hHmeas : ∀ j, Measurable (H j) := by
      intro j
      exact measurable_normalizedOffDiagonalRepresentative
        (Cedge j) (hGmeas j)
    have hHadmissible : IsAdmissiblePrimitiveInput n H :=
      normalizedOffDiagonalRepresentative_admissible
        hCedge hGmem hGbound
    have hHintegrable :
        Integrable
          (fun v : Fin (2 * n - 2) → T4 =>
            primitiveIntegrand ρ ε n (by omega) H κB.1
              (primitiveAssemble n (by omega) z w v))
          (Measure.pi fun _ => paperMeasure) :=
      integrable_primitiveIntegrand_assemble_of_admissible_ge_two
        ρ hε hε1 hnTwo H hHmeas hHadmissible κB z w
    have hscaledIntegrable :
        Integrable
          (fun v : Fin (2 * n - 2) → T4 =>
            (∏ j, Cedge j) *
              primitiveIntegrand ρ ε n (by omega) H κB.1
                (primitiveAssemble n (by omega) z w v))
          (Measure.pi fun _ => paperMeasure) :=
      hHintegrable.const_mul _
    have haeRawScaled :
        (fun v : Fin (2 * n - 2) → T4 =>
          primitiveIntegrand ρ ε n (by omega) G κB.1
            (primitiveAssemble n (by omega) z w v)) =ᵐ[
              Measure.pi fun _ => paperMeasure]
        (fun v : Fin (2 * n - 2) → T4 =>
          primitiveIntegrand ρ ε n (by omega)
            (fun j u => Cedge j * H j u) κB.1
            (primitiveAssemble n (by omega) z w v)) := by
      apply primitiveIntegrand_congr_ae_offDiagonal
        ρ ε n hnTwo G
          (fun j u => Cedge j * H j u)
      intro j u hu
      exact
        (mul_normalizedOffDiagonalRepresentative_eq
          (hCedge j) (G j) hu).symm
    apply hscaledIntegrable.congr
    filter_upwards [haeRawScaled] with v hv
    rw [primitiveIntegrand_family_mul] at hv
    exact hv.symm

/-! ## Joint integrability of heterogeneous Haar paths -/

/-- Adjoining one translated copy of an integrable measurable kernel in a
new Haar variable preserves joint integrability. -/
private theorem integrable_kernel_sub_mul_lift
    {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν]
    (K : T4 → ℝ) (f : Y → ℝ) (shift : Y → T4)
    (hK : Integrable K paperMeasure)
    (hKmeas : Measurable K)
    (hf : Integrable f ν)
    (hshift : Measurable shift) :
    Integrable
      (fun p : T4 × Y =>
        K (p.1 - shift p.2) * f p.2)
      (paperMeasure.prod ν) := by
  let Knorm : T4 → ℝ := fun z => ‖K z‖
  have hKnorm : Integrable Knorm paperMeasure := hK.norm
  have hjointMeas :
      AEStronglyMeasurable
        (fun p : T4 × Y =>
          K (p.1 - shift p.2) * f p.2)
        (paperMeasure.prod ν) :=
    (hKmeas.comp
        (measurable_fst.sub
          (hshift.comp measurable_snd))).aestronglyMeasurable.mul
      hf.aestronglyMeasurable.comp_snd
  rw [integrable_prod_iff' hjointMeas]
  constructor
  · filter_upwards with y
    have htranslated :
        Integrable
          (fun x : T4 => K (x - shift y))
          paperMeasure :=
      ((measurePreserving_sub_paper (shift y)).integrable_comp
        hK.aestronglyMeasurable).mpr hK
    exact htranslated.mul_const (f y)
  · have hnormIntegral (y : Y) :
        (∫ x : T4,
            ‖K (x - shift y) * f y‖
            ∂paperMeasure) =
          (∫ x : T4, Knorm x ∂paperMeasure) * ‖f y‖ := by
      calc
        (∫ x : T4,
            ‖K (x - shift y) * f y‖
            ∂paperMeasure) =
            ∫ x : T4,
              Knorm (x - shift y) * ‖f y‖
              ∂paperMeasure := by
                apply integral_congr_ae
                filter_upwards with x
                simp only [norm_mul, Knorm]
        _ =
            (∫ x : T4,
              Knorm (x - shift y)
              ∂paperMeasure) * ‖f y‖ := by
                rw [integral_mul_const]
        _ =
            (∫ x : T4, Knorm x
              ∂paperMeasure) * ‖f y‖ := by
                have hp :
                    MeasurePreserving
                      (MeasurableEquiv.subRight (shift y))
                      paperMeasure paperMeasure :=
                  (measurePreserving_sub_paper (shift y)).congr
                    (MeasurableEquiv.subRight
                      (shift y)).measurable
                    (Filter.Eventually.of_forall fun _ => rfl)
                have hpi := hp.integral_comp' Knorm
                change
                  (∫ x : T4,
                    Knorm (x - shift y)
                    ∂paperMeasure) =
                    ∫ x : T4, Knorm x
                      ∂paperMeasure at hpi
                rw [hpi]
    convert
      hf.norm.const_mul
        (∫ x : T4, Knorm x ∂paperMeasure) using 1
    funext y
    exact hnormIntegral y

/-- A measurable off-diagonal inverse-square bound gives genuine `L¹`
integrability; the uncontrolled value at the identity is null. -/
private theorem integrable_of_offDiagonal_invSqKer_bound
    {K : T4 → ℝ} {C : ℝ}
    (hKmeas : Measurable K)
    (hC : 0 ≤ C)
    (hbound : ∀ z, z ≠ 0 →
      |K z| ≤ C * invSqKer z) :
    Integrable K paperMeasure := by
  refine
    (integrable_invSqKer.const_mul C).mono
      hKmeas.aestronglyMeasurable ?_
  filter_upwards
      [compl_mem_ae_iff.mpr
        (paperMeasure_singleton (0 : T4))] with z hz
  rw [Real.norm_eq_abs,
    Real.norm_eq_abs,
    abs_of_nonneg
      (mul_nonneg hC (invSqKer_nonneg z))]
  apply hbound z
  simpa only [Set.mem_compl_iff,
    Set.mem_singleton_iff] using hz

/-- Product of heterogeneous kernels along a linearly ordered path, with
an integrable weight at its terminal vertex. -/
private def terminalWeightedKernelPath
    {m : ℕ}
    (K : Fin m → T4 → ℝ)
    (terminalWeight : T4 → ℝ)
    (x : Fin (m + 1) → T4) : ℝ :=
  (∏ i : Fin m,
      K i (x i.castSucc - x i.succ)) *
    terminalWeight (x (Fin.last m))

/-- A terminally weighted heterogeneous Haar path is jointly integrable
when every edge kernel and the terminal weight are integrable and
measurable. -/
private theorem integrable_terminalWeightedKernelPath :
    ∀ {m : ℕ}
      (K : Fin m → T4 → ℝ)
      (terminalWeight : T4 → ℝ),
      (∀ i, Integrable (K i) paperMeasure) →
      (∀ i, Measurable (K i)) →
      Integrable terminalWeight paperMeasure →
      Integrable
        (terminalWeightedKernelPath K terminalWeight)
        (Measure.pi fun _ : Fin (m + 1) =>
          paperMeasure) := by
  intro m
  induction m with
  | zero =>
      intro K terminalWeight _hK _hKmeas hterminal
      let e : (Fin 1 → T4) ≃ᵐ T4 :=
        MeasurableEquiv.funUnique (Fin 1) T4
      have hp :
          MeasurePreserving e
            (Measure.pi fun _ : Fin 1 => paperMeasure)
            paperMeasure :=
        measurePreserving_funUnique paperMeasure (Fin 1)
      have hcomp :
          Integrable (terminalWeight ∘ e)
            (Measure.pi fun _ : Fin 1 => paperMeasure) :=
        (hp.integrable_comp_emb e.measurableEmbedding).mpr
          hterminal
      convert hcomp using 1
      funext x
      simp [terminalWeightedKernelPath, e]
  | succ m ih =>
      intro K terminalWeight hK hKmeas hterminal
      let tailK : Fin m → T4 → ℝ :=
        fun i => K i.succ
      let μtail :=
        Measure.pi fun _ : Fin (m + 1) =>
          paperMeasure
      let tailPath : (Fin (m + 1) → T4) → ℝ :=
        terminalWeightedKernelPath tailK terminalWeight
      have htail :
          Integrable tailPath μtail := by
        simpa only [tailPath, tailK, μtail] using
          ih tailK terminalWeight
            (fun i => hK i.succ)
            (fun i => hKmeas i.succ)
            hterminal
      let e :=
        MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (m + 2) => T4) 0
      have hp :
          MeasurePreserving e
            (Measure.pi fun _ : Fin (m + 2) =>
              paperMeasure)
            (paperMeasure.prod μtail) := by
        simpa only [e, μtail] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (m + 2) => paperMeasure) 0)
      have htarget :
          Integrable
            (fun p : T4 × (Fin (m + 1) → T4) =>
              K 0 (p.1 - p.2 0) * tailPath p.2)
            (paperMeasure.prod μtail) :=
        integrable_kernel_sub_mul_lift
          (K 0) tailPath (fun v => v 0)
          (hK 0) (hKmeas 0) htail
          (measurable_pi_apply 0)
      have heinv
          (y : T4) (v : Fin (m + 1) → T4) :
          e.symm (y, v) = Fin.cons y v := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [e]
        · simp [e]
      have htarget' :
          Integrable
            (fun p : T4 × (Fin (m + 1) → T4) =>
              terminalWeightedKernelPath K terminalWeight
                (e.symm p))
            (paperMeasure.prod μtail) := by
        apply htarget.congr
        filter_upwards with p
        rcases p with ⟨y, v⟩
        rw [heinv y v]
        simp only [terminalWeightedKernelPath,
          Fin.prod_univ_succ, Fin.cons_succ]
        change
          K 0 (y - v 0) * tailPath v =
            (K 0 (y - v 0) *
              ∏ i : Fin m,
                K i.succ
                  (v i.castSucc - v i.succ)) *
              terminalWeight (v (Fin.last m))
        unfold tailPath terminalWeightedKernelPath tailK
        ring
      have hpull :
          Integrable
            ((fun p : T4 × (Fin (m + 1) → T4) =>
              terminalWeightedKernelPath K terminalWeight
                (e.symm p)) ∘ e)
            (Measure.pi fun _ : Fin (m + 2) =>
              paperMeasure) :=
        (hp.integrable_comp_emb e.measurableEmbedding).mpr
          htarget'
      convert hpull using 1
      funext x
      simp only [Function.comp_apply,
        e.symm_apply_apply]

/-- Product of heterogeneous kernels along a linearly ordered path, with
an integrable weight at its initial vertex. -/
private def initialWeightedKernelPath
    {m : ℕ}
    (initialWeight : T4 → ℝ)
    (K : Fin m → T4 → ℝ)
    (x : Fin (m + 1) → T4) : ℝ :=
  initialWeight (x 0) *
    ∏ i : Fin m,
      K i (x i.castSucc - x i.succ)

/-- Initial-weight version of heterogeneous Haar-path integrability.
Class-`E` evenness reverses the terminal edge into the orientation required
by `integrable_kernel_sub_mul_lift`. -/
private theorem integrable_initialWeightedKernelPath :
    ∀ {m : ℕ}
      (initialWeight : T4 → ℝ)
      (K : Fin m → T4 → ℝ),
      Integrable initialWeight paperMeasure →
      (∀ i, Integrable (K i) paperMeasure) →
      (∀ i, Measurable (K i)) →
      (∀ i, MemEClassT4 (K i)) →
      Integrable
        (initialWeightedKernelPath initialWeight K)
        (Measure.pi fun _ : Fin (m + 1) =>
          paperMeasure) := by
  intro m
  induction m with
  | zero =>
      intro initialWeight K hinitial _hK _hKmeas _hKmem
      let e : (Fin 1 → T4) ≃ᵐ T4 :=
        MeasurableEquiv.funUnique (Fin 1) T4
      have hp :
          MeasurePreserving e
            (Measure.pi fun _ : Fin 1 => paperMeasure)
            paperMeasure :=
        measurePreserving_funUnique paperMeasure (Fin 1)
      have hcomp :
          Integrable (initialWeight ∘ e)
            (Measure.pi fun _ : Fin 1 => paperMeasure) :=
        (hp.integrable_comp_emb e.measurableEmbedding).mpr
          hinitial
      convert hcomp using 1
      funext x
      simp [initialWeightedKernelPath, e]
  | succ m ih =>
      intro initialWeight K hinitial hK hKmeas hKmem
      let initK : Fin m → T4 → ℝ :=
        fun i => K i.castSucc
      let μinit :=
        Measure.pi fun _ : Fin (m + 1) =>
          paperMeasure
      let initPath : (Fin (m + 1) → T4) → ℝ :=
        initialWeightedKernelPath initialWeight initK
      have hinit :
          Integrable initPath μinit := by
        simpa only [initPath, initK, μinit] using
          ih initialWeight initK hinitial
            (fun i => hK i.castSucc)
            (fun i => hKmeas i.castSucc)
            (fun i => hKmem i.castSucc)
      let e :=
        MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (m + 2) => T4)
          (Fin.last (m + 1))
      have hp :
          MeasurePreserving e
            (Measure.pi fun _ : Fin (m + 2) =>
              paperMeasure)
            (paperMeasure.prod μinit) := by
        simpa only [e, μinit] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (m + 2) => paperMeasure)
            (Fin.last (m + 1)))
      have htarget :
          Integrable
            (fun p : T4 × (Fin (m + 1) → T4) =>
              K (Fin.last m)
                  (p.1 - p.2 (Fin.last m)) *
                initPath p.2)
            (paperMeasure.prod μinit) :=
        integrable_kernel_sub_mul_lift
          (K (Fin.last m)) initPath
          (fun v => v (Fin.last m))
          (hK (Fin.last m))
          (hKmeas (Fin.last m))
          hinit (measurable_pi_apply (Fin.last m))
      have heinv
          (y : T4) (v : Fin (m + 1) → T4) :
          e.symm (y, v) = Fin.snoc v y := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [e]
        · simp [e]
      have htarget' :
          Integrable
            (fun p : T4 × (Fin (m + 1) → T4) =>
              initialWeightedKernelPath initialWeight K
                (e.symm p))
            (paperMeasure.prod μinit) := by
        apply htarget.congr
        filter_upwards with p
        rcases p with ⟨y, v⟩
        rw [heinv y v]
        have heven :
            K (Fin.last m)
                (v (Fin.last m) - y) =
              K (Fin.last m)
                (y - v (Fin.last m)) := by
          have h :=
            (hKmem (Fin.last m)).neg_invariant
              (y - v (Fin.last m))
          simpa only [neg_sub] using h
        have hzero :
            (0 : Fin (m + 2)) =
              (0 : Fin (m + 1)).castSucc := by
          apply Fin.ext
          rfl
        have hsucc (i : Fin m) :
            i.castSucc.succ = i.succ.castSucc := by
          apply Fin.ext
          rfl
        have hlast :
            (Fin.last m).succ =
              Fin.last (m + 1) := by
          apply Fin.ext
          rfl
        simp only [initialWeightedKernelPath,
          Fin.prod_univ_castSucc]
        rw [hzero, Fin.snoc_castSucc]
        simp_rw [hsucc, Fin.snoc_castSucc]
        rw [hlast, Fin.snoc_last]
        unfold initPath initialWeightedKernelPath initK
        rw [heven]
        ring
      have hpull :
          Integrable
            ((fun p : T4 × (Fin (m + 1) → T4) =>
              initialWeightedKernelPath initialWeight K
                (e.symm p)) ∘ e)
            (Measure.pi fun _ : Fin (m + 2) =>
              paperMeasure) :=
        (hp.integrable_comp_emb e.measurableEmbedding).mpr
          htarget'
      convert hpull using 1
      funext x
      simp only [Function.comp_apply,
        e.symm_apply_apply]

/-- Joint integrability of a primitive-chain skeleton with an incoming
kernel and a terminal endpoint kernel. -/
private theorem integrable_predecessor_primitiveChain_terminal
    {n : ℕ} (hn : 1 ≤ n)
    (Gp : T4 → ℝ)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (Gr : T4 → ℝ)
    (hGp : Integrable Gp paperMeasure)
    (hGpmeas : Measurable Gp)
    (hG : ∀ j, Integrable (G j) paperMeasure)
    (hGmeas : ∀ j, Measurable (G j))
    (hGr : Integrable Gr paperMeasure) :
    Integrable
      (fun p :
          T4 × (Fin (2 * n) → T4) =>
        Gp (p.1 - p.2 ⟨0, by omega⟩) *
          primitiveChainProduct n hn G p.2 *
          Gr (p.2 (primitiveLast n hn)))
      (paperMeasure.prod
        (Measure.pi fun _ : Fin (2 * n) =>
          paperMeasure)) := by
  let edgeCard : (2 * n - 1) + 1 = 2 * n := by
    omega
  let edgeEquiv :
      Fin ((2 * n - 1) + 1) ≃ Fin (2 * n) :=
    finCongr edgeCard
  let K : Fin (2 * n) → T4 → ℝ :=
    fun i =>
      Fin.cases Gp G (edgeEquiv.symm i)
  have hK : ∀ i, Integrable (K i) paperMeasure := by
    intro i
    unfold K
    generalize edgeEquiv.symm i = j
    exact Fin.cases hGp (fun k => hG k) j
  have hKmeas : ∀ i, Measurable (K i) := by
    intro i
    unfold K
    generalize edgeEquiv.symm i = j
    exact Fin.cases hGpmeas (fun k => hGmeas k) j
  have hpath :
      Integrable
        (terminalWeightedKernelPath K Gr)
        (Measure.pi fun _ : Fin (2 * n + 1) =>
          paperMeasure) :=
    integrable_terminalWeightedKernelPath
      K Gr hK hKmeas hGr
  let e :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (2 * n + 1) => T4) 0
  have hp :
      MeasurePreserving e
        (Measure.pi fun _ : Fin (2 * n + 1) =>
          paperMeasure)
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * n) =>
            paperMeasure)) := by
    simpa only [e] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (2 * n + 1) => paperMeasure) 0)
  have heinv
      (u : T4) (t : Fin (2 * n) → T4) :
      e.symm (u, t) = Fin.cons u t := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e]
    · simp [e]
  have htarget :
      Integrable
        (fun p :
            T4 × (Fin (2 * n) → T4) =>
          terminalWeightedKernelPath K Gr (e.symm p))
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * n) =>
            paperMeasure)) := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p :
            T4 × (Fin (2 * n) → T4) =>
          terminalWeightedKernelPath K Gr (e.symm p))
    apply hiff.mp
    convert hpath using 1
    funext x
    simp only [Function.comp_apply,
      e.symm_apply_apply]
  apply htarget.congr
  filter_upwards with p
  rcases p with ⟨u, t⟩
  rw [heinv u t]
  have hprod :
      (∏ i : Fin (2 * n),
          K i
            ((Fin.cons u t :
                Fin (2 * n + 1) → T4) i.castSucc -
              (Fin.cons u t :
                Fin (2 * n + 1) → T4) i.succ)) =
        Gp (u - t ⟨0, by omega⟩) *
          primitiveChainProduct n hn G t := by
    let F : Fin (2 * n) → ℝ := fun i =>
      K i
        ((Fin.cons u t :
            Fin (2 * n + 1) → T4) i.castSucc -
          (Fin.cons u t :
            Fin (2 * n + 1) → T4) i.succ)
    calc
      (∏ i : Fin (2 * n), F i) =
          ∏ j : Fin ((2 * n - 1) + 1),
            F (edgeEquiv j) := by
              exact
                (Equiv.prod_comp edgeEquiv F).symm
      _ =
          F (edgeEquiv 0) *
            ∏ j : Fin (2 * n - 1),
              F (edgeEquiv j.succ) := by
              rw [Fin.prod_univ_succ]
      _ =
          Gp (u - t ⟨0, by omega⟩) *
            primitiveChainProduct n hn G t := by
              have hFzero :
                  F (edgeEquiv 0) =
                    Gp (u - t ⟨0, by omega⟩) := by
                unfold F K
                rw [edgeEquiv.symm_apply_apply]
                simp only [Fin.cases_zero]
                have hleft :
                    (edgeEquiv
                      (0 : Fin ((2 * n - 1) + 1))).castSucc =
                        (0 : Fin (2 * n + 1)) := by
                  apply Fin.ext
                  rfl
                have hright :
                    (edgeEquiv
                      (0 : Fin ((2 * n - 1) + 1))).succ =
                        (⟨0, by omega⟩ :
                          Fin (2 * n)).succ := by
                  apply Fin.ext
                  rfl
                rw [hleft, hright, Fin.cons_zero,
                  Fin.cons_succ]
              have hFsucc
                  (j : Fin (2 * n - 1)) :
                  F (edgeEquiv j.succ) =
                    G j
                      (t (primitiveEdgeLeft n hn j) -
                        t (primitiveEdgeRight n hn j)) := by
                unfold F K
                rw [edgeEquiv.symm_apply_apply]
                simp only [Fin.cases_succ]
                have hleft :
                    (edgeEquiv j.succ).castSucc =
                      (primitiveEdgeLeft n hn j).succ := by
                  apply Fin.ext
                  rfl
                have hright :
                    (edgeEquiv j.succ).succ =
                      (primitiveEdgeRight n hn j).succ := by
                  apply Fin.ext
                  rfl
                rw [hleft, hright, Fin.cons_succ,
                  Fin.cons_succ]
              unfold primitiveChainProduct
              rw [hFzero]
              apply congrArg₂ (· * ·) rfl
              apply Finset.prod_congr rfl
              intro j _hj
              exact hFsucc j
  unfold terminalWeightedKernelPath
  rw [hprod]
  have hlast :
      (Fin.cons u t :
          Fin (2 * n + 1) → T4) (Fin.last (2 * n)) =
        t (primitiveLast n hn) := by
    have hi :
        Fin.last (2 * n) =
          (primitiveLast n hn).succ := by
      apply Fin.ext
      change 2 * n = 2 * n - 1 + 1
      omega
    rw [hi, Fin.cons_succ]
  rw [hlast]

/-- Joint integrability of the second endpoint term, in which the outgoing
kernel is evaluated at the initial primitive vertex. -/
private theorem integrable_predecessor_primitiveChain_initial
    {n : ℕ} (hn : 1 ≤ n)
    (Gp : T4 → ℝ)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (Gr : T4 → ℝ)
    (hGp : Integrable Gp paperMeasure)
    (hGpmeas : Measurable Gp)
    (hG : ∀ j, Integrable (G j) paperMeasure)
    (hGmeas : ∀ j, Measurable (G j))
    (hGmem : ∀ j, MemEClassT4 (G j))
    (hGr : Integrable Gr paperMeasure) :
    Integrable
      (fun p :
          T4 × (Fin (2 * n) → T4) =>
        Gp (p.1 - p.2 ⟨0, by omega⟩) *
          primitiveChainProduct n hn G p.2 *
          Gr (p.2 ⟨0, by omega⟩))
      (paperMeasure.prod
        (Measure.pi fun _ : Fin (2 * n) =>
          paperMeasure)) := by
  let edgeCard : (2 * n - 1) + 1 = 2 * n := by
    omega
  let edgeEquiv :
      Fin ((2 * n - 1) + 1) ≃ Fin (2 * n) :=
    finCongr edgeCard
  let e :=
    MeasurableEquiv.piCongrLeft
      (fun _ : Fin (2 * n) => T4) edgeEquiv
  have hp :
      MeasurePreserving e
        (Measure.pi fun _ : Fin ((2 * n - 1) + 1) =>
          paperMeasure)
        (Measure.pi fun _ : Fin (2 * n) =>
          paperMeasure) := by
    simpa only [e] using
      (measurePreserving_piCongrLeft
        (fun _ : Fin (2 * n) => paperMeasure)
        edgeEquiv)
  have htailSmall :
      Integrable (initialWeightedKernelPath Gr G)
        (Measure.pi fun _ : Fin ((2 * n - 1) + 1) =>
          paperMeasure) :=
    integrable_initialWeightedKernelPath
      Gr G hGr hG hGmeas hGmem
  have htail :
      Integrable
        (fun t : Fin (2 * n) → T4 =>
          Gr (t ⟨0, by omega⟩) *
            primitiveChainProduct n hn G t)
        (Measure.pi fun _ : Fin (2 * n) =>
          paperMeasure) := by
    have htransport :
        Integrable
          (fun t : Fin (2 * n) → T4 =>
            initialWeightedKernelPath Gr G
              (e.symm t))
          (Measure.pi fun _ : Fin (2 * n) =>
            paperMeasure) := by
      have hiff :=
        hp.integrable_comp_emb e.measurableEmbedding
          (g := fun t : Fin (2 * n) → T4 =>
            initialWeightedKernelPath Gr G (e.symm t))
      apply hiff.mp
      convert htailSmall using 1
      funext t
      simp only [Function.comp_apply,
        e.symm_apply_apply]
    apply htransport.congr
    filter_upwards with t
    have heval
        (j : Fin ((2 * n - 1) + 1)) :
        e.symm t j = t (edgeEquiv j) := by
      calc
        e.symm t j =
            e (e.symm t) (edgeEquiv j) := by
              symm
              simpa only [e] using
                (MeasurableEquiv.piCongrLeft_apply_apply
                  (β := fun _ : Fin (2 * n) => T4)
                  edgeEquiv (e.symm t) j)
        _ = t (edgeEquiv j) := by
              rw [e.apply_symm_apply]
    have hzero :
        edgeEquiv
            (0 : Fin ((2 * n - 1) + 1)) =
          (⟨0, by omega⟩ : Fin (2 * n)) := by
      apply Fin.ext
      rfl
    unfold initialWeightedKernelPath primitiveChainProduct
    rw [heval 0, hzero]
    apply congrArg₂ (· * ·) rfl
    apply Finset.prod_congr rfl
    intro j _hj
    rw [heval j.castSucc, heval j.succ]
    apply congrArg (G j)
    apply congrArg₂ (· - ·)
    · apply congrArg t
      apply Fin.ext
      rfl
    · apply congrArg t
      apply Fin.ext
      rfl
  have hlift :
      Integrable
        (fun p :
            T4 × (Fin (2 * n) → T4) =>
          Gp (p.1 - p.2 ⟨0, by omega⟩) *
            (Gr (p.2 ⟨0, by omega⟩) *
              primitiveChainProduct n hn G p.2))
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * n) =>
            paperMeasure)) :=
    integrable_kernel_sub_mul_lift
      Gp
      (fun t : Fin (2 * n) → T4 =>
        Gr (t ⟨0, by omega⟩) *
          primitiveChainProduct n hn G t)
      (fun t => t ⟨0, by omega⟩)
      hGp hGpmeas htail
      (measurable_pi_apply
        (⟨0, by omega⟩ : Fin (2 * n)))
  apply hlift.congr
  filter_upwards with p
  ring

/-! ## Reachable edge families -/

/-- Every edge in a production-reachable R-322 state is measurable.

The induction is over the actual absorption history.  At the updated slot
the new edge is a collapse whose middle kernel is the genuine primitive
kernel built from the previous state's measurable edges; all other slots are
definitionally unchanged. -/
theorem R322AnalyticAbsorbedState.measurable_edges
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {state : R322AnalyticEdgeState q hq}
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ state) :
    ∀ edge, Measurable (state.edges edge) := by
  induction hstate with
  | initial =>
      intro edge
      simpa [r322InitialAnalyticEdgeState] using measurable_greenFn
  | update ctx hpairing previous ih =>
      intro edge
      by_cases hedge : edge = ctx.predecessorEdge
      · subst edge
        have hmeas :
            Measurable
              (r322Collapse
                (ctx.state.edges ctx.predecessorEdge)
                (primitiveKernelDiff ρ lam ε
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder ctx.internalEdges)
                (ctx.state.edges ctx.outgoingEdge)) := by
          apply measurable_r322Collapse
          · exact ih ctx.predecessorEdge
          · exact
              measurable_primitiveKernelDiff
                ρ lam ε
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder ctx.internalEdges
                (fun j => ih (ctx.internalEdge j))
          · exact ih ctx.outgoingEdge
        convert hmeas using 1
        funext u
        exact ctx.nextState_predecessor_eq_r322Collapse ρ lam ε u
      · rw [ctx.nextState_edges_eq_of_ne ρ lam ε edge hedge]
        exact ih edge

/-- The current primitive middle kernel at any proper step issued from a
reachable state is measurable. -/
theorem R322AnalyticAbsorbedState.measurable_stepPrimitiveKernel
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    (ctx : R322AnalyticProperStepContext q hq)
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ ctx.state) :
    Measurable
      (primitiveKernelDiff ρ lam ε
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges) :=
  measurable_primitiveKernelDiff
    ρ lam ε
    (residualBlockOrder ctx.step.2)
    ctx.one_le_blockOrder ctx.internalEdges
    (fun j => hstate.measurable_edges (ctx.internalEdge j))

/-- The generalized closed primitive integrand at a reachable proper step is
jointly measurable in its complete block tuple. -/
theorem R322AnalyticAbsorbedState.measurable_stepClosedIntegrand
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    (ctx : R322AnalyticProperStepContext q hq)
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ ctx.state)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder ctx.step.2)) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder ctx.step.2)}) :
    Measurable
      (detJclosedIntegrandWith ρ ε
        (2 * residualBlockOrder ctx.step.2)
        κB.1 ctx.internalEdges) := by
  obtain ⟨hfull, hprimitive⟩ :=
    mem_primitiveFullPairings.mp κB.2
  have hmeas :=
    measurable_primitiveIntegrand
      ρ ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      (fun j => hstate.measurable_edges (ctx.internalEdge j))
      κB.1
  convert hmeas using 1
  funext x
  exact
    detJclosedIntegrandWith_eq_primitiveIntegrand_of_full_primitive
      ρ ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      κB.1 hfull hprimitive x

/-- Every closed primitive summand occurring at a production-reachable
proper step has an absolutely integrable internal section.

This is the concrete discharge of the `hinternal` side condition in the
one-step R-322 Fubini identity.  It uses only reachability for measurability
and the current edge certificate for the class-`E` and off-diagonal
majorant hypotheses. -/
theorem R322AnalyticAbsorbedState.integrable_stepClosedIntegrand_section
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {scale : Fin (2 * q - 1) → ℝ}
    (ctx : R322AnalyticProperStepContext q hq)
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ ctx.state)
    (hcert : R322AnalyticEdgeCertificate ctx.state scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (κB :
      {τ : PartialPairing
          (Fin (2 * residualBlockOrder ctx.step.2)) //
        τ ∈ primitiveFullPairings
          (residualBlockOrder ctx.step.2)})
    (z w : T4) :
    Integrable
      (fun v :
          Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
        detJclosedIntegrandWith ρ ε
          (2 * residualBlockOrder ctx.step.2)
          κB.1 ctx.internalEdges
          (primitiveAssemble
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder z w v))
      (Measure.pi fun _ => paperMeasure) := by
  obtain ⟨hfull, hprimitive⟩ :=
    mem_primitiveFullPairings.mp κB.2
  have hraw :
      Integrable
        (fun v :
            Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
          primitiveIntegrand ρ ε
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder ctx.internalEdges κB.1
            (primitiveAssemble
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder z w v))
        (Measure.pi fun _ => paperMeasure) :=
    integrable_primitiveIntegrand_assemble_of_scaled_offDiagonal
      ρ hε hε1 ctx.one_le_blockOrder
      ctx.internalEdges
      (fun j => scale (ctx.internalEdge j))
      (fun j => hstate.measurable_edges (ctx.internalEdge j))
      (fun j => hcert.scale_pos (ctx.internalEdge j))
      (fun j => hcert.memE (ctx.internalEdge j))
      (fun j u hu => hcert.bound (ctx.internalEdge j) u hu)
      κB z w
  apply hraw.congr
  filter_upwards with v
  exact
    (detJclosedIntegrandWith_eq_primitiveIntegrand_of_full_primitive
      ρ ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      κB.1 hfull hprimitive
      (primitiveAssemble
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder z w v)).symm

/-- Uniform-in-pairing, almost-everywhere endpoint form consumed by the
production proper-step Fubini API.  In fact the section theorem above is
pointwise in both endpoints; the weaker a.e. packaging prevents downstream
interfaces from demanding unnecessary diagonal statements. -/
theorem
    R322AnalyticAbsorbedState.eventually_integrable_stepClosedIntegrand_section
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {scale : Fin (2 * q - 1) → ℝ}
    (ctx : R322AnalyticProperStepContext q hq)
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ ctx.state)
    (hcert : R322AnalyticEdgeCertificate ctx.state scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
      ∀ κB :
          {τ : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        Integrable
          (fun v :
              Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder ctx.step.2)
              κB.1 ctx.internalEdges
              (primitiveAssemble
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder p.1 p.2 v))
          (Measure.pi fun _ => paperMeasure) := by
  filter_upwards with p
  intro κB
  exact hstate.integrable_stepClosedIntegrand_section
    ctx hcert hε hε1 κB p.1 p.2

/-- The complete local integrand of a reachable proper step is measurable
in its standard block coordinates. -/
theorem R322AnalyticAbsorbedState.measurable_localIntegrand
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    (ctx : R322AnalyticProperStepContext q hq)
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ ctx.state)
    (u : T4) :
    Measurable (ctx.localIntegrand ρ ε u) := by
  unfold R322AnalyticProperStepContext.localIntegrand
  have hzero :
      Measurable fun
          t : Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
        t ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩ :=
    measurable_pi_apply _
  have hlast :
      Measurable fun
          t : Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
        t (primitiveLast
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder) :=
    measurable_pi_apply _
  have hpred :
      Measurable fun
          t : Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
        ctx.state.edges ctx.predecessorEdge
          (u - t ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩) :=
    (hstate.measurable_edges ctx.predecessorEdge).comp
      (measurable_const.sub hzero)
  have hmiddle :
      Measurable fun
          t : Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
        ∑ κB :
            {τ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              τ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          detJclosedIntegrandWith ρ ε
            (2 * residualBlockOrder ctx.step.2)
            κB.1 ctx.internalEdges t := by
    apply Finset.measurable_sum
    intro κB _hκB
    exact hstate.measurable_stepClosedIntegrand ctx κB
  have hout :
      Measurable fun
          t : Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
        ctx.state.edges ctx.outgoingEdge
            (t (primitiveLast
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder)) -
          ctx.state.edges ctx.outgoingEdge
            (t ⟨0, by
              have hn := ctx.one_le_blockOrder
              omega⟩) :=
    ((hstate.measurable_edges ctx.outgoingEdge).comp hlast).sub
      ((hstate.measurable_edges ctx.outgoingEdge).comp hzero)
  exact (hpred.mul hmiddle).mul hout

/-- The complete local integrand at a production-reachable proper step is
jointly integrable in the external predecessor point and every block
coordinate.

The proof uses only the actual edge certificate.  Each reachable edge is
`L¹` by its measurable off-diagonal inverse-square bound.  The two terms
of the outgoing difference are then heterogeneous Haar paths, while the
finite primitive covariance sum is a bounded measurable multiplier at a
fixed positive mollification scale. -/
theorem R322AnalyticAbsorbedState.integrable_localIntegrand_joint
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {scale : Fin (2 * q - 1) → ℝ}
    (ctx : R322AnalyticProperStepContext q hq)
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ ctx.state)
    (hcert : R322AnalyticEdgeCertificate ctx.state scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable
      (fun p :
          T4 ×
            (Fin (2 * residualBlockOrder ctx.step.2) → T4) =>
        ctx.localIntegrand ρ ε p.1 p.2)
      (paperMeasure.prod
        (Measure.pi fun _ :
            Fin (2 * residualBlockOrder ctx.step.2) =>
          paperMeasure)) := by
  let n : ℕ := residualBlockOrder ctx.step.2
  let Gp : T4 → ℝ :=
    ctx.state.edges ctx.predecessorEdge
  let G : Fin (2 * n - 1) → T4 → ℝ :=
    ctx.internalEdges
  let Gr : T4 → ℝ :=
    ctx.state.edges ctx.outgoingEdge
  have hn : 1 ≤ n := ctx.one_le_blockOrder
  have hedgeIntegrable :
      ∀ edge, Integrable (ctx.state.edges edge) paperMeasure := by
    intro edge
    exact integrable_of_offDiagonal_invSqKer_bound
      (hstate.measurable_edges edge)
      (hcert.scale_pos edge).le
      (fun z hz => hcert.bound edge z hz)
  have hGpInt : Integrable Gp paperMeasure :=
    hedgeIntegrable ctx.predecessorEdge
  have hGpMeas : Measurable Gp :=
    hstate.measurable_edges ctx.predecessorEdge
  have hGInt : ∀ j, Integrable (G j) paperMeasure :=
    fun j => hedgeIntegrable (ctx.internalEdge j)
  have hGMeas : ∀ j, Measurable (G j) :=
    fun j => hstate.measurable_edges (ctx.internalEdge j)
  have hGMem : ∀ j, MemEClassT4 (G j) :=
    fun j => hcert.memE (ctx.internalEdge j)
  have hGrInt : Integrable Gr paperMeasure :=
    hedgeIntegrable ctx.outgoingEdge
  have hterminal :
      Integrable
        (fun p : T4 × (Fin (2 * n) → T4) =>
          Gp (p.1 - p.2 ⟨0, by omega⟩) *
            primitiveChainProduct n hn G p.2 *
            Gr (p.2 (primitiveLast n hn)))
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * n) =>
            paperMeasure)) :=
    integrable_predecessor_primitiveChain_terminal
      hn Gp G Gr hGpInt hGpMeas hGInt hGMeas hGrInt
  have hinitial :
      Integrable
        (fun p : T4 × (Fin (2 * n) → T4) =>
          Gp (p.1 - p.2 ⟨0, by omega⟩) *
            primitiveChainProduct n hn G p.2 *
            Gr (p.2 ⟨0, by omega⟩))
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * n) =>
            paperMeasure)) :=
    integrable_predecessor_primitiveChain_initial
      hn Gp G Gr hGpInt hGpMeas hGInt hGMeas hGMem hGrInt
  have hskeleton :
      Integrable
        (fun p : T4 × (Fin (2 * n) → T4) =>
          Gp (p.1 - p.2 ⟨0, by omega⟩) *
            primitiveChainProduct n hn G p.2 *
            (Gr (p.2 (primitiveLast n hn)) -
              Gr (p.2 ⟨0, by omega⟩)))
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * n) =>
            paperMeasure)) := by
    apply hterminal.sub hinitial |>.congr
    filter_upwards with p
    simp only [Pi.sub_apply]
    ring
  let covarianceSum : (Fin (2 * n) → T4) → ℝ :=
    fun t =>
      ∑ κB :
          {τ : PartialPairing (Fin (2 * n)) //
            τ ∈ primitiveFullPairings n},
        primitiveCovarianceProduct ρ ε n κB.1 t
  have hcovarianceMeas : Measurable covarianceSum := by
    dsimp only [covarianceSum]
    apply Finset.measurable_sum
    intro κB _hκB
    unfold primitiveCovarianceProduct
    apply Finset.measurable_prod
    intro i _hi
    exact
      (ρ.measurable_etaEpsT4_of_pos_of_le_one
        hε hε1).comp
          ((measurable_pi_apply i).sub
            (measurable_pi_apply (κB.1 i)))
  obtain ⟨Cη, hCη, hcovariance⟩ :=
    exists_primitiveCovarianceProduct_uniform_bound ρ
  let A : ℝ := (ε⁻¹ ^ (dim : ℕ) * Cη) ^ n
  let B : ℝ :=
    ((primitiveFullPairings n).card : ℝ) * A
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hcovarianceBound :
      ∀ t, ‖covarianceSum t‖ ≤ B := by
    intro t
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun κB _ =>
        primitiveCovarianceProduct_nonneg
          ρ ε n κB.1 t)]
    calc
      covarianceSum t ≤
          ∑ _κB :
              {τ : PartialPairing (Fin (2 * n)) //
                τ ∈ primitiveFullPairings n},
            A := by
              dsimp only [covarianceSum]
              apply Finset.sum_le_sum
              intro κB _hκB
              exact hcovariance n κB.1
                (mem_primitiveFullPairings.mp κB.2).1
                hε hε1 t
      _ = B := by
            simp [B]
  have hproduct :
      Integrable
        (fun p : T4 × (Fin (2 * n) → T4) =>
          (Gp (p.1 - p.2 ⟨0, by omega⟩) *
            primitiveChainProduct n hn G p.2 *
            (Gr (p.2 (primitiveLast n hn)) -
              Gr (p.2 ⟨0, by omega⟩))) *
            covarianceSum p.2)
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * n) =>
            paperMeasure)) :=
    hskeleton.mul_bdd
      ((hcovarianceMeas.comp measurable_snd).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p =>
        hcovarianceBound p.2)
  apply hproduct.congr
  filter_upwards with p
  change
    (Gp (p.1 - p.2 ⟨0, by omega⟩) *
        primitiveChainProduct n hn G p.2 *
        (Gr (p.2 (primitiveLast n hn)) -
          Gr (p.2 ⟨0, by omega⟩))) *
      covarianceSum p.2 =
    ctx.localIntegrand ρ ε p.1 p.2
  rw [← ctx.rawLocalIntegrand_eq_localIntegrand
    ρ ε p.1 p.2]
  unfold R322AnalyticProperStepContext.rawLocalIntegrand
    covarianceSum Gp G Gr n
  ring

/-- The exact a.e. section form required as `hstandard` by the production
proper-step Fubini API. -/
theorem
    R322AnalyticAbsorbedState.eventually_integrable_localIntegrand
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    {κ : PartialPairing (Fin (2 * q))}
    {hκ : κ ∈ nonSplitPairings q}
    {scale : Fin (2 * q - 1) → ℝ}
    (ctx : R322AnalyticProperStepContext q hq)
    (hstate :
      R322AnalyticAbsorbedState
        ρ lam ε hq κ hκ ctx.state)
    (hcert : R322AnalyticEdgeCertificate ctx.state scale)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ u ∂paperMeasure,
      Integrable (ctx.localIntegrand ρ ε u)
        (Measure.pi fun _ :
            Fin (2 * residualBlockOrder ctx.step.2) =>
          paperMeasure) :=
  (hstate.integrable_localIntegrand_joint
    ctx hcert hε hε1).prod_right_ae

end

end Anderson4D
