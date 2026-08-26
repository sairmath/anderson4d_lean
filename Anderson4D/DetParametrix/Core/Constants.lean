import Anderson4D.DetParametrix.Core.Renormalized

/-!
# Recursive `J` kernels and Proposition 3.3

Paper: D-C2q — §3.2 (3.8)–(3.11) — the renormalization constants

This file applies the edge-replacement recursion of Proposition 3.2 to the
internal `J` chain of paper §3.2.  The final extraction of a full interval has
no right chain edge; it is represented by the value `1`, exactly as in the
totalized closed formula `detJintegrand`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- A generalized internal chain edge for a tuple of length `n`. -/
def jChainEdgeWith {n : ℕ}
    (G : Fin (n - 1) → T4 → ℝ) (xt : Fin n → T4)
    (e : Fin (n - 1)) : ℝ :=
  G e (xt ⟨e.val, by have := e.isLt; omega⟩ -
    xt ⟨e.val + 1, by have := e.isLt; omega⟩)

/-- Generalized endpoint difference for the internal `J` chain.  The last
endpoint of the whole interval has no edge to its right and contributes
`1`. -/
def diffFactorJWith {n : ℕ}
    (G : Fin (n - 1) → T4 → ℝ) (xt : Fin n → T4)
    (p : Fin n × Fin n) : ℝ :=
  if h : p.2.val + 1 < n then
    G ⟨p.2.val, by omega⟩
        (xt p.2 - xt ⟨p.2.val + 1, h⟩) -
      G ⟨p.2.val, by omega⟩
        (xt p.1 - xt ⟨p.2.val + 1, h⟩)
  else 1

/-- Valid edge replacements extracted from a list of endpoint pairs. -/
def jReplacementList {n : ℕ}
    (G : Fin (n - 1) → T4 → ℝ) (xt : Fin n → T4) :
    List (Fin n × Fin n) → List (Fin (n - 1) × ℝ)
  | [] => []
  | p :: ps =>
      if h : p.2.val + 1 < n then
        (⟨p.2.val, by omega⟩, diffFactorJWith G xt p) ::
          jReplacementList G xt ps
      else
        jReplacementList G xt ps

/-- Invalid (whole-interval) endpoints contribute `1`, so filtering them
from the replacement recursion preserves the product of differences. -/
theorem jReplacementList_values
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ) (xt : Fin n → T4)
    (ps : List (Fin n × Fin n)) :
    ((jReplacementList G xt ps).map Prod.snd).prod =
      (ps.map (diffFactorJWith G xt)).prod := by
  induction ps with
  | nil =>
      simp [jReplacementList]
  | cons p ps ih =>
      by_cases h : p.2.val + 1 < n
      · simp [jReplacementList, diffFactorJWith, h, ih]
      · simp [jReplacementList, diffFactorJWith, h, ih]

/-- Edges replaced in the internal `J` chain. -/
def extractedJRightEdges {n : ℕ}
    (G : Fin (n - 1) → T4 → ℝ) (xt : Fin n → T4)
    (ps : List (Fin n × Fin n)) : Finset (Fin (n - 1)) :=
  ((jReplacementList G xt ps).map Prod.fst).toFinset

/-- Closed generalized `J` integrand obtained from the replacement list. -/
def detJclosedIntegrandWith
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ)
    (σ : PartialPairing (Fin n))
    (G : Fin (n - 1) → T4 → ℝ) (xt : Fin n → T4) : ℝ :=
  (∏ e : Fin (n - 1),
      if e ∈ extractedJRightEdges G xt (extract σ) then 1
      else jChainEdgeWith G xt e) *
    (((jReplacementList G xt (extract σ)).map Prod.snd).prod) *
    ∏ i ∈ σ.pairSupport.filter (fun i => i < σ i),
      ρ.etaEpsT4 ε (xt i - xt (σ i))

/-- Recursive Definition 3.1 semantics for the internal `J` chain. -/
def detJrecursiveIntegrandWith
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ)
    (σ : PartialPairing (Fin n))
    (G : Fin (n - 1) → T4 → ℝ) (xt : Fin n → T4) : ℝ :=
  replacementProduct (jChainEdgeWith G xt)
      (jReplacementList G xt (extract σ)) Finset.univ *
    ∏ i ∈ σ.pairSupport.filter (fun i => i < σ i),
      ρ.etaEpsT4 ε (xt i - xt (σ i))

/-- **Proposition 3.3, generalized-input integrand form.** -/
theorem detJrecursiveIntegrandWith_eq_prod
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ)
    (σ : PartialPairing (Fin n))
    (G : Fin (n - 1) → T4 → ℝ) (xt : Fin n → T4) :
    detJrecursiveIntegrandWith ρ ε n σ G xt =
      detJclosedIntegrandWith ρ ε n σ G xt := by
  unfold detJrecursiveIntegrandWith detJclosedIntegrandWith
  rw [replacementProduct_eq_prod]
  rw [prod_if_mem_eq_prod_sdiff]
  unfold extractedJRightEdges
  ring

/-! ## Green specialization and the frozen `J` formula -/

@[simp]
theorem diffFactorJWith_green
    {n : ℕ} (xt : Fin n → T4) (p : Fin n × Fin n) :
    diffFactorJWith (fun _ : Fin (n - 1) => greenFn) xt p =
      diffFactorJ xt p := by
  unfold diffFactorJWith diffFactorJ
  split <;> rfl

/-- The valid replacement keys are exactly the right-endpoint values which
can index an internal chain edge.  A whole-interval right endpoint is
automatically impossible on the left. -/
theorem mem_jReplacementList_keys_iff
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ) (xt : Fin n → T4)
    (ps : List (Fin n × Fin n)) (e : Fin (n - 1)) :
    e ∈ (jReplacementList G xt ps).map Prod.fst ↔
      e.val ∈ ps.map (fun p => p.2.val) := by
  induction ps with
  | nil =>
      simp [jReplacementList]
  | cons p ps ih =>
      by_cases h : p.2.val + 1 < n
      · simp [jReplacementList, h, ih, Fin.ext_iff]
      · have hne : e.val ≠ p.2.val := by
          intro heq
          have he := e.isLt
          omega
        simp [jReplacementList, h, ih, hne]

theorem mem_extractedJRightEdges_iff
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ) (xt : Fin n → T4)
    (ps : List (Fin n × Fin n)) (e : Fin (n - 1)) :
    e ∈ extractedJRightEdges G xt ps ↔
      e.val ∈ ps.map (fun p => p.2.val) := by
  simp only [extractedJRightEdges, List.mem_toFinset]
  exact mem_jReplacementList_keys_iff G xt ps e

/-- The generalized closed `J` integrand at the constant Green family is
the frozen formula (3.12) from `Kernels.lean`. -/
theorem detJclosedIntegrandWith_green_eq_detJintegrand
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (xt : Fin (2 * q) → T4) :
    detJclosedIntegrandWith ρ ε (2 * q) σ
        (fun _ => greenFn) xt =
      detJintegrand ρ ε q σ xt := by
  have hchain :
      (∏ e : Fin (2 * q - 1),
          if e ∈ extractedJRightEdges (fun _ => greenFn) xt (extract σ)
          then 1
          else jChainEdgeWith (fun _ => greenFn) xt e) =
        ∏ e : Fin (2 * q - 1),
          if e.val ∈ (extract σ).map (fun p => p.2.val) then 1
          else if h : e.val + 1 < 2 * q then
            greenFn (xt ⟨e.val, by omega⟩ - xt ⟨e.val + 1, h⟩)
          else 1 := by
    apply Finset.prod_congr rfl
    intro e _
    have he : e.val + 1 < 2 * q := by
      have := e.isLt
      omega
    by_cases hk :
        e ∈ extractedJRightEdges (fun _ => greenFn) xt (extract σ)
    · have hv :=
        (mem_extractedJRightEdges_iff
          (fun _ : Fin (2 * q - 1) => greenFn) xt (extract σ) e).mp hk
      simp [hk, hv]
    · have hv : ¬e.val ∈ (extract σ).map (fun p => p.2.val) := by
        intro hv
        exact hk ((mem_extractedJRightEdges_iff
          (fun _ : Fin (2 * q - 1) => greenFn)
          xt (extract σ) e).mpr hv)
      simp [hk, hv, jChainEdgeWith, he]
  have hvalues :
      ((jReplacementList (fun _ : Fin (2 * q - 1) => greenFn)
          xt (extract σ)).map Prod.snd).prod =
        ((extract σ).map (diffFactorJ xt)).prod := by
    rw [jReplacementList_values]
    apply congrArg List.prod
    apply List.map_congr_left
    intro p _
    exact diffFactorJWith_green xt p
  unfold detJclosedIntegrandWith detJintegrand
  rw [hchain, hvalues]

/-- Recursive `J_{2q,σ}` obtained by integrating the recursive integrand. -/
def detJrecursive
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    (q : ℕ) → PartialPairing (Fin (2 * q)) → T4 → T4 → ℝ
  | 0, _, _, _ => 0
  | q' + 1, σ, z, w =>
      lamEps lam ε ^ (2 * (q' + 1)) *
        ∫ v : Fin (2 * q') → T4,
          detJrecursiveIntegrandWith ρ ε (2 * (q' + 1)) σ
            (fun _ => greenFn) (fun j =>
              assemble z w v
                (Fin.cast (by omega : 2 * (q' + 1) = 2 * q' + 2) j))
          ∂(MeasureTheory.Measure.pi fun _ => paperMeasure)

/-- **Proposition 3.3, integrated form.**  The recursively renormalized
`J` kernel equals the closed formula used by `detJ`. -/
theorem renormJ_eq_prod
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q))) (z w : T4) :
    detJrecursive ρ lam ε q σ z w =
      detJ ρ lam ε q σ z w := by
  cases q with
  | zero =>
      rfl
  | succ q =>
      rw [detJrecursive, detJ]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with v
      exact (detJrecursiveIntegrandWith_eq_prod ρ ε
        (2 * (q + 1)) σ (fun _ => greenFn) _).trans
          (detJclosedIntegrandWith_green_eq_detJintegrand
            ρ ε (q + 1) σ _)

end

end Anderson4D
