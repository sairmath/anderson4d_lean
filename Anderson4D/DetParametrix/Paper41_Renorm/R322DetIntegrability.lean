import Anderson4D.DetParametrix.Paper41_Renorm.R322FiberTail
import Anderson4D.DetParametrix.Paper42_Moment.R324TreeIntegrability
import Anderson4D.DetParametrix.Core.ReductionBase

/-!
# All-order integrability of the R-322 `J` kernels

The pointwise reduction output used in (3.22) carries an integrability
field.  This file discharges that field at every positive order.

Each valid replacement in the closed `J` chain removes the edge immediately
to the right of an extracted interval and inserts a difference.  Expanding
the differences chooses either the original edge or a shortcut from an
earlier vertex.  Every branch is therefore an increasing Green tree, so the
joint tree-integrability theorem applies.  The covariance product is
measurable and bounded at a fixed positive scale.

Joint integrability is finally transported to the fixed terminal endpoint
`w = 0`.  Fubini first supplies one integrable terminal section; simultaneous
translation of every spatial variable identifies that section with the
zero section.  Thus no unjustified pointwise Fubini claim is used.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Valid extracted right edges of the internal `J` chain -/

/-- The valid extracted right edges of a `J` chain.  An extracted interval
ending at the last vertex has no edge to its right and is intentionally
absent. -/
def jExtractedRightEdges
    {n : ℕ} (σ : PartialPairing (Fin n.succ)) :
    Finset (Fin n) :=
  Finset.univ.filter fun e =>
    e.val ∈ (extract σ).map fun p => p.2.val

@[simp]
theorem mem_jExtractedRightEdges
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (e : Fin n) :
    e ∈ jExtractedRightEdges σ ↔
      e.val ∈ (extract σ).map (fun p => p.2.val) := by
  simp [jExtractedRightEdges]

/-- Positive-length specialization of the generalized `J` difference. -/
def diffFactorJSuccWith
    {n : ℕ} (G : Fin n → T4 → ℝ)
    (x : Fin n.succ → T4)
    (p : Fin n.succ × Fin n.succ) : ℝ :=
  if h : p.2.val + 1 < n.succ then
    G ⟨p.2.val, by omega⟩
        (x p.2 - x ⟨p.2.val + 1, h⟩) -
      G ⟨p.2.val, by omega⟩
        (x p.1 - x ⟨p.2.val + 1, h⟩)
  else 1

@[simp]
theorem diffFactorJSuccWith_green
    {n : ℕ} (x : Fin n.succ → T4)
    (p : Fin n.succ × Fin n.succ) :
    diffFactorJSuccWith (fun _ : Fin n => greenFn) x p =
      diffFactorJ x p := by
  unfold diffFactorJSuccWith diffFactorJ
  split <;> rfl

/-- Positive-length specialization of `jReplacementList`, with its edge
carrier written definitionally as `Fin n` rather than `Fin (n.succ - 1)`.
This avoids dependent casts in the tree expansion. -/
def jSuccReplacementList
    {n : ℕ} (G : Fin n → T4 → ℝ)
    (x : Fin n.succ → T4) :
    List (Fin n.succ × Fin n.succ) →
      List (Fin n × ℝ)
  | [] => []
  | p :: ps =>
      if h : p.2.val + 1 < n.succ then
        (⟨p.2.val, by omega⟩,
          diffFactorJSuccWith G x p) ::
          jSuccReplacementList G x ps
      else
        jSuccReplacementList G x ps

/-- The specialized list retains exactly the product of all closed-form
difference factors; an invalid terminal extraction contributes `1`. -/
theorem jSuccReplacementList_values
    {n : ℕ} (G : Fin n → T4 → ℝ)
    (x : Fin n.succ → T4)
    (ps : List (Fin n.succ × Fin n.succ)) :
    ((jSuccReplacementList G x ps).map Prod.snd).prod =
      (ps.map (diffFactorJSuccWith G x)).prod := by
  induction ps with
  | nil =>
      simp [jSuccReplacementList]
  | cons p ps ih =>
      by_cases h : p.2.val + 1 < n.succ
      · simp [jSuccReplacementList, diffFactorJSuccWith, h, ih]
      · simp [jSuccReplacementList, diffFactorJSuccWith, h, ih]

/-- Membership of specialized replacement keys is exactly membership of
the extracted right-endpoint value list. -/
theorem mem_jSuccReplacementList_keys_iff
    {n : ℕ} (G : Fin n → T4 → ℝ)
    (x : Fin n.succ → T4)
    (ps : List (Fin n.succ × Fin n.succ))
    (e : Fin n) :
    e ∈ (jSuccReplacementList G x ps).map Prod.fst ↔
      e.val ∈ ps.map (fun p => p.2.val) := by
  induction ps with
  | nil =>
      simp [jSuccReplacementList]
  | cons p ps ih =>
      by_cases h : p.2.val + 1 < n.succ
      · simp [jSuccReplacementList, h, ih, Fin.ext_iff]
      · have hne : e.val ≠ p.2.val := by
          intro heq
          have he := e.isLt
          omega
        simp [jSuccReplacementList, h, ih, hne]

/-- Membership in the valid edge set is witnessed by an actual extracted
interval with that right endpoint. -/
theorem exists_jExtractedPairOfRightEdge
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (e : Fin n) (he : e ∈ jExtractedRightEdges σ) :
    ∃ p, p ∈ extract σ ∧ p.2.val = e.val := by
  have hm :
      e.val ∈ (extract σ).map (fun p => p.2.val) :=
    (mem_jExtractedRightEdges σ e).mp he
  simpa only [List.mem_map] using hm

/-- The unique extracted interval represented by a valid right edge. -/
noncomputable def jExtractedPairOfRightEdge
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (e : Fin n) (he : e ∈ jExtractedRightEdges σ) :
    Fin n.succ × Fin n.succ :=
  Classical.choose (exists_jExtractedPairOfRightEdge σ e he)

theorem jExtractedPairOfRightEdge_mem
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (e : Fin n) (he : e ∈ jExtractedRightEdges σ) :
    jExtractedPairOfRightEdge σ e he ∈ extract σ :=
  (Classical.choose_spec
    (exists_jExtractedPairOfRightEdge σ e he)).1

theorem jExtractedPairOfRightEdge_right
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (e : Fin n) (he : e ∈ jExtractedRightEdges σ) :
    (jExtractedPairOfRightEdge σ e he).2.val = e.val :=
  (Classical.choose_spec
    (exists_jExtractedPairOfRightEdge σ e he)).2

/-- The chosen inverse of a valid extracted right edge returns its original
extracted interval. -/
theorem jExtractedPairOfRightEdge_eq
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (p : Fin n.succ × Fin n.succ)
    (hp : p ∈ extract σ)
    (hvalid : p.2.val + 1 < n.succ) :
    jExtractedPairOfRightEdge σ
        ⟨p.2.val, by omega⟩
        ((mem_jExtractedRightEdges σ
          ⟨p.2.val, by omega⟩).2
            (List.mem_map.mpr ⟨p, hp, rfl⟩)) =
      p := by
  let e : Fin n := ⟨p.2.val, by omega⟩
  let he : e ∈ jExtractedRightEdges σ :=
    (mem_jExtractedRightEdges σ e).2
      (List.mem_map.mpr ⟨p, hp, rfl⟩)
  apply List.inj_on_of_nodup_map
    (extract_map_snd_nodup σ)
  · exact jExtractedPairOfRightEdge_mem σ e he
  · exact hp
  · apply Fin.ext
    change
      (jExtractedPairOfRightEdge σ e he).2.val =
        p.2.val
    rw [jExtractedPairOfRightEdge_right σ e he]

/-- The shortcut parent is the left endpoint of the extracted interval. -/
def jExtractedShortcutParent
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (e : Fin n) (he : e ∈ jExtractedRightEdges σ) :
    Fin (e.val + 1) := by
  let p := jExtractedPairOfRightEdge σ e he
  refine ⟨p.1.val, ?_⟩
  have hp :=
    extract_spec σ p
      (jExtractedPairOfRightEdge_mem σ e he)
  have hr :=
    jExtractedPairOfRightEdge_right σ e he
  change p.1.val ≤ p.2.val at hp
  change p.2.val = e.val at hr
  omega

/-! ## Increasing-tree expansion of the signed Green skeleton -/

/-- Original internal chain edge with right vertex `e+1`. -/
def jOriginalGreenEdge
    {n : ℕ} (x : Fin n.succ → T4) (e : Fin n) : ℂ :=
  (greenFn (x e.castSucc - x e.succ) : ℂ)

/-- The predecessor of an ordinary internal `J` edge. -/
def jOrdinaryEdgeParent {n : ℕ} (e : Fin n) :
    Fin (e.val + 1) :=
  ⟨e.val, by omega⟩

/-- Shortcut edge at a valid extracted right endpoint, and zero at every
unextracted endpoint. -/
def jExtractedShortcutGreenEdge
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (x : Fin n.succ → T4) (e : Fin n) : ℂ :=
  if he : e ∈ jExtractedRightEdges σ then
    (greenFn
      (x (Fin.castLE (by omega)
          (jExtractedShortcutParent σ e he)) -
        x e.succ) : ℂ)
  else 0

/-- Parent map of one branch in the powerset expansion. -/
def expandedJGreenTreeParent
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (original : Finset (Fin n)) :
    IncreasingTreeParent n :=
  fun e =>
    if e ∈ original then jOrdinaryEdgeParent e
    else if he : e ∈ jExtractedRightEdges σ then
      jExtractedShortcutParent σ e he
    else jOrdinaryEdgeParent e

/-- One powerset branch of the internal `J` Green product. -/
def expandedJGreenBranch
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (original : Finset (Fin n))
    (x : Fin n.succ → T4) : ℂ :=
  (∏ e ∈ original, jOriginalGreenEdge x e) *
    ∏ e ∈ originalᶜ,
      jExtractedShortcutGreenEdge σ x e

private theorem expandedJGreenTreeParentVertex_original
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (original : Finset (Fin n))
    (e : Fin n) (he : e ∈ original) :
    increasingTreeParentVertex
        (expandedJGreenTreeParent σ original) e =
      e.castSucc := by
  apply Fin.ext
  unfold increasingTreeParentVertex
    expandedJGreenTreeParent
  rw [if_pos he]
  rfl

private theorem expandedJGreenTreeParentVertex_shortcut
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (original : Finset (Fin n))
    (e : Fin n) (he : e ∉ original)
    (hextract : e ∈ jExtractedRightEdges σ) :
    increasingTreeParentVertex
        (expandedJGreenTreeParent σ original) e =
      Fin.castLE (by omega)
        (jExtractedShortcutParent σ e hextract) := by
  apply Fin.ext
  unfold increasingTreeParentVertex
    expandedJGreenTreeParent
  rw [if_neg he, dif_pos hextract]

/-- A branch that only chooses existing shortcuts is exactly an increasing
Green tree. -/
theorem expandedJGreenBranch_eq_tree
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (original : Finset (Fin n))
    (hshortcut :
      ∀ e : Fin n, e ∉ original →
        e ∈ jExtractedRightEdges σ) :
    expandedJGreenBranch σ original =
      increasingTreeGreenProduct
        (expandedJGreenTreeParent σ original) := by
  funext x
  have hfactor :
      ∀ e : Fin n,
        (greenFn
          (x (increasingTreeParentVertex
              (expandedJGreenTreeParent σ original) e) -
            x e.succ) : ℂ) =
          if e ∈ original then jOriginalGreenEdge x e
          else jExtractedShortcutGreenEdge σ x e := by
    intro e
    by_cases he : e ∈ original
    · rw [if_pos he,
        expandedJGreenTreeParentVertex_original
          σ original e he]
      rfl
    · have hextract := hshortcut e he
      rw [if_neg he,
        expandedJGreenTreeParentVertex_shortcut
          σ original e he hextract]
      simp only [jExtractedShortcutGreenEdge,
        dif_pos hextract]
  unfold expandedJGreenBranch increasingTreeGreenProduct
  rw [show
      (∏ e : Fin n,
          (greenFn
            (x (increasingTreeParentVertex
                (expandedJGreenTreeParent σ original) e) -
              x e.succ) : ℂ)) =
        ∏ e : Fin n,
          if e ∈ original then jOriginalGreenEdge x e
          else jExtractedShortcutGreenEdge σ x e by
    apply Finset.prod_congr rfl
    intro e _he
    exact hfactor e]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  have hcompl :
      {e ∈ (Finset.univ : Finset (Fin n)) |
          ¬e ∈ original} =
        originalᶜ := by
    ext e
    simp
  rw [hcompl]

/-- Every expansion branch is jointly integrable.  A branch asking for a
nonexistent shortcut is identically zero. -/
theorem integrable_expandedJGreenBranch
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (original : Finset (Fin n)) :
    Integrable (expandedJGreenBranch σ original)
      (Measure.pi fun _ : Fin n.succ => paperMeasure) := by
  by_cases hshortcut :
      ∀ e : Fin n, e ∉ original →
        e ∈ jExtractedRightEdges σ
  · rw [expandedJGreenBranch_eq_tree σ original hshortcut]
    exact integrable_increasingTreeGreenProduct
      (expandedJGreenTreeParent σ original)
  · push Not at hshortcut
    obtain ⟨e, he, hnotExtracted⟩ := hshortcut
    have heCompl : e ∈ originalᶜ := by
      simpa using he
    have hzero :
        ∀ x : Fin n.succ → T4,
          (∏ j ∈ originalᶜ,
            jExtractedShortcutGreenEdge σ x j) = 0 := by
      intro x
      apply Finset.prod_eq_zero heCompl
      unfold jExtractedShortcutGreenEdge
      rw [dif_neg hnotExtracted]
    have hfun :
        expandedJGreenBranch σ original =
          fun _ : Fin n.succ → T4 => 0 := by
      funext x
      unfold expandedJGreenBranch
      rw [hzero x, mul_zero]
    rw [hfun]
    exact integrable_zero _ _ _

/-- Product of edgewise sums dominating the signed expansion. -/
def expandedJGreenMajorant
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (x : Fin n.succ → T4) : ℂ :=
  ∏ e : Fin n,
    (jOriginalGreenEdge x e +
      jExtractedShortcutGreenEdge σ x e)

theorem expandedJGreenMajorant_eq_sum_branches
    {n : ℕ} (σ : PartialPairing (Fin n.succ)) :
    expandedJGreenMajorant σ =
      fun x => ∑ original : Finset (Fin n),
        expandedJGreenBranch σ original x := by
  funext x
  unfold expandedJGreenMajorant expandedJGreenBranch
  exact Fintype.prod_add
    (fun e : Fin n => jOriginalGreenEdge x e)
    (fun e : Fin n =>
      jExtractedShortcutGreenEdge σ x e)

theorem integrable_expandedJGreenMajorant
    {n : ℕ} (σ : PartialPairing (Fin n.succ)) :
    Integrable (expandedJGreenMajorant σ)
      (Measure.pi fun _ : Fin n.succ => paperMeasure) := by
  rw [expandedJGreenMajorant_eq_sum_branches]
  exact integrable_finsetSum Finset.univ fun original _ =>
    integrable_expandedJGreenBranch σ original

/-! ## Identification with the frozen signed skeleton -/

/-- Filtering invalid whole-interval replacements preserves distinctness of
right-edge keys. -/
theorem jReplacementList_keys_nodup_of_right_nodup
    {n : ℕ} (G : Fin n → T4 → ℝ)
    (x : Fin n.succ → T4)
    (ps : List (Fin n.succ × Fin n.succ))
    (hps : (ps.map Prod.snd).Nodup) :
    ((jSuccReplacementList G x ps).map Prod.fst).Nodup := by
  induction ps with
  | nil =>
      simp [jSuccReplacementList]
  | cons p ps ih =>
      simp only [List.map_cons, List.nodup_cons] at hps
      by_cases hvalid : p.2.val + 1 < n.succ
      · simp only [jSuccReplacementList, hvalid, ↓reduceDIte,
          List.map_cons, List.nodup_cons]
        constructor
        · intro hmem
          have hv :
              p.2.val ∈ ps.map (fun r => r.2.val) :=
            (mem_jSuccReplacementList_keys_iff
              G x ps ⟨p.2.val, by omega⟩).mp hmem
          apply hps.1
          rcases List.mem_map.mp hv with
            ⟨r, hr, hright⟩
          exact List.mem_map.mpr
            ⟨r, hr, Fin.ext hright⟩
        · exact ih hps.2
      · simp only [jSuccReplacementList, hvalid, ↓reduceDIte]
        exact ih hps.2

/-- Products over the valid edge finset can be reindexed by the exact
replacement list. -/
theorem prod_jExtractedRightEdges_eq_jReplacementList
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (x : Fin n.succ → T4)
    {M : Type*} [CommMonoid M]
    (f : Fin n → M) :
    (∏ e ∈ jExtractedRightEdges σ, f e) =
      ((jSuccReplacementList
        (fun _ : Fin n => greenFn)
        x (extract σ)).map fun u => f u.1).prod := by
  have hkeys :
      ((jSuccReplacementList
        (fun _ : Fin n => greenFn)
        x (extract σ)).map Prod.fst).Nodup :=
    jReplacementList_keys_nodup_of_right_nodup
      (fun _ : Fin n => greenFn)
      x (extract σ) (extract_map_snd_nodup σ)
  have hset :
      jExtractedRightEdges σ =
        ((jSuccReplacementList
          (fun _ : Fin n => greenFn)
          x (extract σ)).map Prod.fst).toFinset := by
    ext e
    rw [List.mem_toFinset,
      mem_jSuccReplacementList_keys_iff,
      mem_jExtractedRightEdges]
  rw [hset]
  rw [List.prod_toFinset f hkeys]
  simp only [List.map_map, Function.comp_def]

/-- Every entry of a replacement list comes from a valid source interval. -/
theorem mem_jReplacementList_exists_source
    {n : ℕ} (G : Fin n → T4 → ℝ)
    (x : Fin n.succ → T4)
    (ps : List (Fin n.succ × Fin n.succ))
    (u : Fin n × ℝ)
    (hu : u ∈ jSuccReplacementList G x ps) :
    ∃ p, p ∈ ps ∧ p.2.val + 1 < n.succ ∧
      u.1.val = p.2.val ∧
      u.2 = diffFactorJSuccWith G x p := by
  induction ps with
  | nil =>
      simp [jSuccReplacementList] at hu
  | cons p ps ih =>
      by_cases hvalid : p.2.val + 1 < n.succ
      · simp only [jSuccReplacementList, hvalid, ↓reduceDIte,
          List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact ⟨p, List.mem_cons_self, hvalid, rfl, rfl⟩
        · obtain ⟨r, hr, hrvalid, hkey, hvalue⟩ := ih hu
          exact
            ⟨r, List.mem_cons_of_mem p hr, hrvalid,
              hkey, hvalue⟩
      · simp only [jSuccReplacementList, hvalid, ↓reduceDIte] at hu
        obtain ⟨r, hr, hrvalid, hkey, hvalue⟩ := ih hu
        exact
          ⟨r, List.mem_cons_of_mem p hr, hrvalid,
            hkey, hvalue⟩

/-- At a valid extracted interval, the chosen shortcut is the Green edge
from its left endpoint to the vertex immediately after its right endpoint. -/
theorem jExtractedShortcutGreenEdge_at_pair
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (p : Fin n.succ × Fin n.succ)
    (hp : p ∈ extract σ)
    (hvalid : p.2.val + 1 < n.succ)
    (x : Fin n.succ → T4) :
    jExtractedShortcutGreenEdge σ x
        ⟨p.2.val, by omega⟩ =
      (greenFn
        (x p.1 -
          x ⟨p.2.val + 1, hvalid⟩) : ℂ) := by
  let e : Fin n := ⟨p.2.val, by omega⟩
  have he : e ∈ jExtractedRightEdges σ :=
    (mem_jExtractedRightEdges σ e).2
      (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hchosen :
      jExtractedPairOfRightEdge σ e he = p := by
    exact jExtractedPairOfRightEdge_eq
      σ p hp hvalid
  unfold jExtractedShortcutGreenEdge
  rw [dif_pos he]
  have hleft :
      Fin.castLE (by omega)
          (jExtractedShortcutParent σ e he) =
        p.1 := by
    apply Fin.ext
    simp only [Fin.castLE, jExtractedShortcutParent]
    rw [hchosen]
  have hright :
      e.succ =
        (⟨p.2.val + 1, hvalid⟩ :
          Fin n.succ) := by
    apply Fin.ext
    rfl
  rw [hleft, hright]

/-- Each concrete replacement-list value is its original edge minus its
chosen shortcut. -/
theorem jReplacementList_green_entry_eq_difference
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (x : Fin n.succ → T4)
    (u : Fin n × ℝ)
    (hu : u ∈
      jSuccReplacementList
        (fun _ : Fin n => greenFn) x (extract σ)) :
    (u.2 : ℂ) =
      jOriginalGreenEdge x u.1 -
        jExtractedShortcutGreenEdge σ x u.1 := by
  obtain ⟨p, hp, hvalid, hkey, hvalue⟩ :=
    mem_jReplacementList_exists_source
      (fun _ : Fin n => greenFn)
      x (extract σ) u hu
  have hedge :
      u.1 = (⟨p.2.val, by omega⟩ : Fin n) := by
    apply Fin.ext
    exact hkey
  have hvalue' :
      u.2 = diffFactorJ x p := by
    exact hvalue.trans
      (diffFactorJSuccWith_green x p)
  rw [hedge,
    jExtractedShortcutGreenEdge_at_pair
      σ p hp hvalid x]
  rw [hvalue']
  unfold jOriginalGreenEdge diffFactorJ
  rw [dif_pos hvalid]
  rw [Complex.ofReal_sub]
  congr 2

/-- The product of signed edge differences is exactly the replacement-list
value product, including the convention that a whole-interval extraction
contributes `1`. -/
theorem prod_jGreenDifference_eq_extract_diffFactorJ
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (x : Fin n.succ → T4) :
    (∏ e ∈ jExtractedRightEdges σ,
        (jOriginalGreenEdge x e -
          jExtractedShortcutGreenEdge σ x e)) =
      (((extract σ).map fun p =>
        (diffFactorJ x p : ℂ)).prod) := by
  let replacements : List (Fin n × ℝ) :=
    jSuccReplacementList
      (fun _ : Fin n => greenFn) x (extract σ)
  calc
    (∏ e ∈ jExtractedRightEdges σ,
        (jOriginalGreenEdge x e -
          jExtractedShortcutGreenEdge σ x e)) =
        (replacements.map fun u =>
          jOriginalGreenEdge x u.1 -
            jExtractedShortcutGreenEdge σ x u.1).prod := by
      exact prod_jExtractedRightEdges_eq_jReplacementList
        σ x (fun e =>
          jOriginalGreenEdge x e -
            jExtractedShortcutGreenEdge σ x e)
    _ = (replacements.map fun u => (u.2 : ℂ)).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro u hu
      exact
        (jReplacementList_green_entry_eq_difference
          σ x u hu).symm
    _ = ((replacements.map Prod.snd).prod : ℂ) := by
      induction replacements with
      | nil =>
          simp
      | cons u us ih =>
          simp only [List.map_cons, List.prod_cons]
          rw [ih]
          norm_num
    _ = (((extract σ).map
          (diffFactorJSuccWith
            (fun _ : Fin n => greenFn) x)).prod : ℂ) := by
      rw [jSuccReplacementList_values]
    _ = (((extract σ).map fun p =>
          (diffFactorJ x p : ℂ)).prod) := by
      induction extract σ with
      | nil =>
          simp
      | cons p ps ih =>
          simp only [List.map_cons, List.prod_cons]
          rw [Complex.ofReal_mul, ih]
          congr 1

/-- Uniform signed edge-difference product. -/
def expandedJGreenDifferenceProduct
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (x : Fin n.succ → T4) : ℂ :=
  ∏ e : Fin n,
    (jOriginalGreenEdge x e -
      jExtractedShortcutGreenEdge σ x e)

/-- The frozen `J` Green skeleton is exactly the uniform edge-difference
product. -/
theorem renormalizedJGreenSkeleton_eq_differenceProduct
    {n : ℕ} (σ : PartialPairing (Fin n.succ)) :
    (fun x => (renormalizedJGreenSkeleton σ x : ℂ)) =
      expandedJGreenDifferenceProduct σ := by
  funext x
  let E : Finset (Fin n) :=
    jExtractedRightEdges σ
  let U : Finset (Fin n) := Finset.univ
  let F : Fin n → ℂ := fun e =>
    jOriginalGreenEdge x e -
      jExtractedShortcutGreenEdge σ x e
  have hEU : E ⊆ U := Finset.subset_univ E
  have hchain :
      Complex.ofRealHom
        (∏ e : Fin n,
          if e.val ∈
              (extract σ).map (fun p => p.2.val) then
            (1 : ℝ)
          else if h : e.val + 1 < n.succ then
            greenFn
              (x ⟨e.val, by omega⟩ -
                x ⟨e.val + 1, h⟩)
          else 1) =
        ∏ e ∈ U \ E, jOriginalGreenEdge x e := by
    have hleft :
        (∏ e : Fin n,
            Complex.ofRealHom
              (if e.val ∈
                (extract σ).map (fun p => p.2.val) then
              (1 : ℝ)
            else if h : e.val + 1 < n.succ then
              greenFn
                (x ⟨e.val, by omega⟩ -
                  x ⟨e.val + 1, h⟩)
            else 1)) =
          ∏ e : Fin n,
            if e ∈ E then 1
            else jOriginalGreenEdge x e := by
      apply Finset.prod_congr rfl
      intro e _he
      have hedge : e.val + 1 < n.succ := by
        have := e.isLt
        omega
      by_cases hextract : e ∈ E
      · have hv :
            e.val ∈
              (extract σ).map (fun p => p.2.val) :=
          (mem_jExtractedRightEdges σ e).mp hextract
        simp [hextract, hv]
      · have hv :
            e.val ∉
              (extract σ).map (fun p => p.2.val) := by
          exact fun hv =>
            hextract
              ((mem_jExtractedRightEdges σ e).2 hv)
        simp only [hextract, hv, if_false,
          dif_pos hedge, jOriginalGreenEdge]
        congr 2
    change
      Complex.ofRealHom
          (∏ e : Fin n,
            if e.val ∈
                (extract σ).map (fun p => p.2.val) then
              (1 : ℝ)
            else if h : e.val + 1 < n.succ then
              greenFn
                (x ⟨e.val, by omega⟩ -
                  x ⟨e.val + 1, h⟩)
            else 1) =
        _
    rw [map_prod, hleft, Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
    congr 1
    ext e
    simp [U, E]
  have hunextracted :
      (∏ e ∈ U \ E, F e) =
        ∏ e ∈ U \ E, jOriginalGreenEdge x e := by
    apply Finset.prod_congr rfl
    intro e he
    have heE : e ∉ E :=
      (Finset.mem_sdiff.mp he).2
    unfold F
    unfold jExtractedShortcutGreenEdge
    rw [dif_neg heE, sub_zero]
  have hextracted :
      (∏ e ∈ E, F e) =
        (((extract σ).map fun p =>
          (diffFactorJ x p : ℂ)).prod) := by
    exact prod_jGreenDifference_eq_extract_diffFactorJ
      σ x
  have hpartition :
      (∏ e ∈ U, F e) =
        (∏ e ∈ U \ E, F e) *
          ∏ e ∈ E, F e :=
    (Finset.prod_sdiff hEU).symm
  have hdiff :
      Complex.ofRealHom
          ((extract σ).map
            (diffFactorJ x)).prod =
        (((extract σ).map fun p =>
          (diffFactorJ x p : ℂ)).prod) := by
    induction extract σ with
    | nil =>
        simp
    | cons p ps ih =>
        simp only [List.map_cons, List.prod_cons]
        rw [map_mul, ih]
        rfl
  unfold renormalizedJGreenSkeleton
    expandedJGreenDifferenceProduct
  change
    Complex.ofRealHom
        ((∏ e : Fin n,
          if e.val ∈
              (extract σ).map (fun p => p.2.val) then
            (1 : ℝ)
          else if h : e.val + 1 < n.succ then
            greenFn
              (x ⟨e.val, by omega⟩ -
                x ⟨e.val + 1, h⟩)
          else 1) *
          ((extract σ).map (diffFactorJ x)).prod) =
      _
  rw [map_mul, hchain, hdiff,
    ← hunextracted, ← hextracted, ← hpartition]

/-! ## Joint integrability of the signed skeleton -/

theorem measurable_jOriginalGreenEdge
    {n : ℕ} (e : Fin n) :
    Measurable
      (fun x : Fin n.succ → T4 =>
        jOriginalGreenEdge x e) := by
  unfold jOriginalGreenEdge
  exact
    (measurable_greenFn.comp
      ((measurable_pi_apply e.castSucc).sub
        (measurable_pi_apply e.succ))).complex_ofReal

theorem measurable_jExtractedShortcutGreenEdge
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (e : Fin n) :
    Measurable
      (fun x : Fin n.succ → T4 =>
        jExtractedShortcutGreenEdge σ x e) := by
  by_cases he : e ∈ jExtractedRightEdges σ
  · simp only [jExtractedShortcutGreenEdge, dif_pos he]
    exact
      (measurable_greenFn.comp
        ((measurable_pi_apply
          (Fin.castLE (by omega)
            (jExtractedShortcutParent σ e he))).sub
          (measurable_pi_apply e.succ))).complex_ofReal
  · simp [jExtractedShortcutGreenEdge, he]

theorem measurable_expandedJGreenDifferenceProduct
    {n : ℕ} (σ : PartialPairing (Fin n.succ)) :
    Measurable (expandedJGreenDifferenceProduct σ) := by
  unfold expandedJGreenDifferenceProduct
  apply Finset.measurable_prod
  intro e _he
  exact (measurable_jOriginalGreenEdge e).sub
    (measurable_jExtractedShortcutGreenEdge σ e)

/-- Edgewise triangle inequality between the signed expansion and the
nonnegative product-of-sums majorant. -/
theorem norm_expandedJGreenDifferenceProduct_le
    {n : ℕ} (σ : PartialPairing (Fin n.succ))
    (x : Fin n.succ → T4) :
    ‖expandedJGreenDifferenceProduct σ x‖ ≤
      ‖expandedJGreenMajorant σ x‖ := by
  unfold expandedJGreenDifferenceProduct
    expandedJGreenMajorant
  rw [norm_prod, norm_prod]
  apply Finset.prod_le_prod
  · intro e _he
    exact norm_nonneg _
  intro e _he
  by_cases he : e ∈ jExtractedRightEdges σ
  · let a := greenFn (x e.castSucc - x e.succ)
    let b := greenFn
      (x (Fin.castLE (by omega)
          (jExtractedShortcutParent σ e he)) -
        x e.succ)
    have haeq :
        jOriginalGreenEdge x e = (a : ℂ) := by
      rfl
    have hbeq :
        jExtractedShortcutGreenEdge σ x e =
          (b : ℂ) := by
      unfold jExtractedShortcutGreenEdge
      rw [dif_pos he]
    rw [haeq, hbeq]
    have ha : 0 ≤ a := greenFn_nonneg _
    have hb : 0 ≤ b := greenFn_nonneg _
    calc
      ‖(a : ℂ) - (b : ℂ)‖ ≤
          ‖(a : ℂ)‖ + ‖(b : ℂ)‖ :=
        norm_sub_le _ _
      _ = a + b := by
        simp [abs_of_nonneg ha, abs_of_nonneg hb]
      _ = ‖(a : ℂ) + (b : ℂ)‖ := by
        have hcast :
            (a : ℂ) + (b : ℂ) =
              ((a + b : ℝ) : ℂ) := by
          norm_num
        rw [hcast, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg ha hb)]
  · simp [jExtractedShortcutGreenEdge, he]

/-- Joint integrability of the signed Green skeleton of every positive-
length `J` tuple. -/
theorem integrable_renormalizedJGreenSkeleton
    {n : ℕ} (σ : PartialPairing (Fin n.succ)) :
    Integrable
      (fun x : Fin n.succ → T4 =>
        (renormalizedJGreenSkeleton σ x : ℂ))
      (Measure.pi fun _ => paperMeasure) := by
  have hmajor := integrable_expandedJGreenMajorant σ
  rw [renormalizedJGreenSkeleton_eq_differenceProduct σ]
  exact hmajor.mono
    (measurable_expandedJGreenDifferenceProduct σ).aestronglyMeasurable
    (.of_forall fun x =>
      norm_expandedJGreenDifferenceProduct_le σ x)

/-- Cardinality-generic positive-length form of
`integrable_renormalizedJGreenSkeleton`. -/
theorem integrable_renormalizedJGreenSkeleton_of_pos
    {n : ℕ} (hn : 0 < n)
    (σ : PartialPairing (Fin n)) :
    Integrable
      (fun x : Fin n → T4 =>
        (renormalizedJGreenSkeleton σ x : ℂ))
      (Measure.pi fun _ => paperMeasure) := by
  cases n with
  | zero => omega
  | succ n =>
      exact integrable_renormalizedJGreenSkeleton σ

/-! ## Bounded covariance factor and the complete `J` integrand -/

/-- Covariance product of the internal `J` tuple, in the complex scalar
field used for joint integrability. -/
def detJCovarianceFactor
    (ρ : SmoothCutoff) (ε : ℝ) {n : ℕ}
    (σ : PartialPairing (Fin n))
    (x : Fin n → T4) : ℂ :=
  (pairingCovarianceProductOn
    ρ ε σ Finset.univ x : ℝ)

theorem measurable_detJCovarianceFactor
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {n : ℕ} (σ : PartialPairing (Fin n)) :
    Measurable (detJCovarianceFactor ρ ε σ) := by
  unfold detJCovarianceFactor
    pairingCovarianceProductOn
  apply Measurable.complex_ofReal
  apply Finset.measurable_prod
  intro i _hi
  exact
    (ρ.measurable_etaEpsT4_of_pos_of_le_one
      hε hε1).comp
        ((measurable_pi_apply i).sub
          (measurable_pi_apply (σ i)))

/-- At a fixed positive small scale the complete covariance product is
uniformly bounded on the compact tuple space. -/
theorem exists_norm_detJCovarianceFactor_le
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {n : ℕ} (σ : PartialPairing (Fin n)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : Fin n → T4,
        ‖detJCovarianceFactor ρ ε σ x‖ ≤ B := by
  obtain ⟨Cη, hCη, heta⟩ :=
    ρ.exists_pos_etaEpsT4_uniform_bound
  let A : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη
  let B : ℝ := (1 + A) ^ n
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hbase : 1 ≤ 1 + A := by
    linarith
  refine ⟨B, pow_nonneg (by linarith) _, ?_⟩
  intro x
  unfold detJCovarianceFactor
    pairingCovarianceProductOn
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg fun i _ =>
      ρ.etaEpsT4_nonneg ε
        (x i - x (σ i)))]
  calc
    (∏ i ∈ (Finset.univ : Finset (Fin n)).filter
          (fun i => i < σ i),
        ρ.etaEpsT4 ε (x i - x (σ i))) ≤
        ∏ _i ∈ (Finset.univ : Finset (Fin n)).filter
          (fun i => i < σ i),
          (1 + A) := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact ρ.etaEpsT4_nonneg ε
          (x i - x (σ i))
      · intro i _hi
        calc
          ρ.etaEpsT4 ε (x i - x (σ i)) ≤ A := by
            simpa only [A] using
              heta hε hε1 (x i - x (σ i))
          _ ≤ 1 + A := by linarith
    _ = (1 + A) ^
        ((Finset.univ : Finset (Fin n)).filter
          (fun i => i < σ i)).card := by
      simp
    _ ≤ (1 + A) ^ n := by
      apply pow_le_pow_right₀ hbase
      calc
        ((Finset.univ : Finset (Fin n)).filter
            (fun i => i < σ i)).card ≤
            (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_univ _
        _ = n := by simp
    _ = B := rfl

/-- Exact complex factorization of the frozen `J` integrand. -/
theorem detJintegrand_eq_renormalizedJGreenSkeleton_mul_covariance
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (x : Fin (2 * q) → T4) :
    (detJintegrand ρ ε q σ x : ℂ) =
      (renormalizedJGreenSkeleton σ x : ℂ) *
        detJCovarianceFactor ρ ε σ x := by
  rw [detJintegrand_eq_skeleton_mul_covariance]
  unfold detJCovarianceFactor
  exact Complex.ofReal_mul _ _

/-- Joint integrability of every positive-order frozen `J` integrand in all
of its spatial vertices. -/
theorem integrable_detJintegrand_joint
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1)))) :
    Integrable
      (fun x : Fin (2 * (q + 1)) → T4 =>
        (detJintegrand ρ ε (q + 1) σ x : ℂ))
      (Measure.pi fun _ => paperMeasure) := by
  obtain ⟨B, _hB, hcovBound⟩ :=
    exists_norm_detJCovarianceFactor_le
      ρ hε hε1 σ
  have hskeleton :
      Integrable
        (fun x : Fin (2 * (q + 1)) → T4 =>
          (renormalizedJGreenSkeleton σ x : ℂ))
        (Measure.pi fun _ => paperMeasure) := by
    exact
      integrable_renormalizedJGreenSkeleton_of_pos
        (by omega) σ
  have hprod :=
    hskeleton.mul_bdd
      (measurable_detJCovarianceFactor
        ρ hε hε1 σ).aestronglyMeasurable
      (.of_forall hcovBound)
  convert hprod using 1
  funext x
  exact
    detJintegrand_eq_renormalizedJGreenSkeleton_mul_covariance
      ρ ε (q + 1) σ x

/-- The tuple `(z,u,w)` used by a positive-order `J` kernel. -/
def r322DetJTupleSucc (q : ℕ) (z w : T4)
    (u : Fin (2 * q) → T4) :
    Fin (2 * (q + 1)) → T4 :=
  fun j =>
    assemble z w u
      (Fin.cast
        (by omega : 2 * (q + 1) = 2 * q + 2) j)

@[simp]
theorem r322DetJTupleSucc_zero
    (q : ℕ) (z w : T4)
    (u : Fin (2 * q) → T4) :
    r322DetJTupleSucc q z w u 0 = z := by
  simp [r322DetJTupleSucc]

/-! ## Fubini coordinates for the two endpoints -/

/-- Split the first and last vertices from a tuple of canonical length
`m+2`.  The inverse is `assemble`. -/
def r322FlatAssembleMeasurableEquiv (m : ℕ) :
    (Fin (m + 2) → T4) ≃ᵐ
      T4 × (T4 × (Fin m → T4)) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 2) => T4) 0).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (m + 1) => T4) (Fin.last m)))

@[simp]
theorem r322FlatAssembleMeasurableEquiv_symm_apply
    (m : ℕ) (x y : T4) (v : Fin m → T4) :
    (r322FlatAssembleMeasurableEquiv m).symm
        (x, y, v) =
      assemble x y v := by
  simp only [r322FlatAssembleMeasurableEquiv,
    MeasurableEquiv.trans_symm,
    MeasurableEquiv.trans_apply]
  have hprod :
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (m + 1) => T4)
          (Fin.last m))).symm (x, y, v) =
        (x, (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (m + 1) => T4)
          (Fin.last m)).symm (y, v)) := by
    rfl
  rw [hprod]
  simp only [
    MeasurableEquiv.piFinSuccAbove_symm_apply]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [assemble]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [assemble]
    · simp [assemble, show k.val ≠ m by omega]

theorem measurePreserving_r322FlatAssembleMeasurableEquiv
    (m : ℕ) :
    MeasurePreserving
      (r322FlatAssembleMeasurableEquiv m)
      (Measure.pi fun _ : Fin (m + 2) =>
        paperMeasure)
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin m =>
            paperMeasure))) := by
  have hhead :
      MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (m + 2) => T4) 0)
        (Measure.pi fun _ : Fin (m + 2) =>
          paperMeasure)
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (m + 1) =>
            paperMeasure)) := by
    simpa using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (m + 2) => paperMeasure) 0)
  have hlast :
      MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (m + 1) => T4)
          (Fin.last m))
        (Measure.pi fun _ : Fin (m + 1) =>
          paperMeasure)
        (paperMeasure.prod
          (Measure.pi fun _ : Fin m =>
            paperMeasure)) := by
    simpa only [Fin.succAbove_last] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (m + 1) => paperMeasure)
        (Fin.last m))
  exact
    ((MeasurePreserving.id paperMeasure).prod hlast).comp
      hhead

/-- Cast the algebraic cardinality `2(q+1)` to the canonical endpoint
presentation `2q+2`, then split the two endpoints. -/
def r322DetJFlatMeasurableEquiv (q : ℕ) :
    (Fin (2 * (q + 1)) → T4) ≃ᵐ
      T4 × (T4 × (Fin (2 * q) → T4)) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (2 * q + 2) => T4)
      (finCongr
        (by omega :
          2 * (q + 1) = 2 * q + 2))).trans
    (r322FlatAssembleMeasurableEquiv (2 * q))

@[simp]
theorem r322DetJFlatMeasurableEquiv_symm_apply
    (q : ℕ) (x y : T4)
    (v : Fin (2 * q) → T4) :
    (r322DetJFlatMeasurableEquiv q).symm
        (x, y, v) =
      fun j => assemble x y v
        (Fin.cast
          (by omega :
            2 * (q + 1) = 2 * q + 2) j) := by
  funext j
  simp only [r322DetJFlatMeasurableEquiv,
    MeasurableEquiv.trans_symm,
    MeasurableEquiv.trans_apply,
    r322FlatAssembleMeasurableEquiv_symm_apply]
  rfl

theorem measurePreserving_r322DetJFlatMeasurableEquiv
    (q : ℕ) :
    MeasurePreserving
      (r322DetJFlatMeasurableEquiv q)
      (Measure.pi fun _ : Fin (2 * (q + 1)) =>
        paperMeasure)
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * q) =>
            paperMeasure))) := by
  let castEquiv :
      (Fin (2 * (q + 1)) → T4) ≃ᵐ
        (Fin (2 * q + 2) → T4) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : Fin (2 * q + 2) => T4)
      (finCongr
        (by omega :
          2 * (q + 1) = 2 * q + 2))
  have hcast :
      MeasurePreserving castEquiv
        (Measure.pi
          fun _ : Fin (2 * (q + 1)) =>
            paperMeasure)
        (Measure.pi
          fun _ : Fin (2 * q + 2) =>
            paperMeasure) := by
    simpa only [castEquiv] using
      (measurePreserving_piCongrLeft
        (fun _ : Fin (2 * q + 2) =>
          paperMeasure)
        (finCongr
          (by omega :
            2 * (q + 1) = 2 * q + 2)))
  exact
    (measurePreserving_r322FlatAssembleMeasurableEquiv
      (2 * q)).comp hcast

/-- Move the terminal endpoint to the front of the flat coordinate
triple. -/
def r322MoveMiddleMeasurableEquiv
    (A B C : Type*) [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] :
    A × (B × C) ≃ᵐ B × (A × C) :=
  (MeasurableEquiv.prodAssoc
      (α := A) (β := B) (γ := C)).symm.trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodComm :
        A × B ≃ᵐ B × A)
      (MeasurableEquiv.refl C)).trans
      (MeasurableEquiv.prodAssoc
        (α := B) (β := A) (γ := C)))

theorem measurePreserving_r322MoveMiddleMeasurableEquiv
    {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (τ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite τ] :
    MeasurePreserving
      (r322MoveMiddleMeasurableEquiv A B C)
      (μ.prod (ν.prod τ))
      (ν.prod (μ.prod τ)) := by
  exact
    (measurePreserving_prodAssoc ν μ τ).comp
      (((Measure.measurePreserving_swap
        (μ := μ) (ν := ν)).prod
          (MeasurePreserving.id τ)).comp
        (measurePreserving_prodAssoc μ ν τ).symm)

@[simp]
theorem r322MoveMiddleMeasurableEquiv_symm_apply
    (A B C : Type*) [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (b : B) (a : A) (c : C) :
    (r322MoveMiddleMeasurableEquiv A B C).symm
        (b, a, c) =
      (a, b, c) := by
  rfl

/-- Joint integrability in the flat `(z,w,v)` coordinates used by
`detJ`. -/
theorem integrable_detJintegrand_flat_r322
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1)))) :
    Integrable
      (fun p :
          T4 × (T4 × (Fin (2 * q) → T4)) =>
        detJintegrand ρ ε (q + 1) σ
          (r322DetJTupleSucc q
            p.1 p.2.1 p.2.2))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * q) =>
            paperMeasure))) := by
  let e := r322DetJFlatMeasurableEquiv q
  let μ :=
    Measure.pi fun _ : Fin (2 * (q + 1)) =>
      paperMeasure
  let ν :=
    paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : Fin (2 * q) =>
          paperMeasure))
  have hp : MeasurePreserving e μ ν :=
    measurePreserving_r322DetJFlatMeasurableEquiv q
  have hsourceComplex :=
    integrable_detJintegrand_joint
      ρ hε hε1 q σ
  have hsource :
      Integrable
        (fun x : Fin (2 * (q + 1)) → T4 =>
          detJintegrand ρ ε (q + 1) σ x)
        μ := by
    convert hsourceComplex.re using 1
    funext x
    exact Complex.ofReal_re _
  have htarget :
      Integrable
        (fun p :
            T4 × (T4 × (Fin (2 * q) → T4)) =>
          detJintegrand ρ ε (q + 1) σ
            (e.symm p))
        ν := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p :
          T4 × (T4 × (Fin (2 * q) → T4)) =>
            detJintegrand ρ ε (q + 1) σ
              (e.symm p))
    apply hiff.mp
    convert hsource using 1
    funext x
    simp only [Function.comp_apply,
      e.symm_apply_apply]
  convert htarget using 1
  funext p
  rcases p with ⟨z, w, v⟩
  rw [show e.symm (z, w, v) =
      r322DetJTupleSucc q z w v by
    unfold e r322DetJTupleSucc
    exact
      r322DetJFlatMeasurableEquiv_symm_apply
        q z w v]

/-- The same joint integrability with the terminal endpoint first. -/
theorem integrable_detJintegrand_terminalFirst_r322
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1)))) :
    Integrable
      (fun p :
          T4 × (T4 × (Fin (2 * q) → T4)) =>
        detJintegrand ρ ε (q + 1) σ
          (r322DetJTupleSucc q
            p.2.1 p.1 p.2.2))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * q) =>
            paperMeasure))) := by
  let τ :=
    Measure.pi fun _ : Fin (2 * q) =>
      paperMeasure
  let e :=
    r322MoveMiddleMeasurableEquiv
      T4 T4 (Fin (2 * q) → T4)
  let f :
      T4 × (T4 × (Fin (2 * q) → T4)) → ℝ :=
    fun p =>
      detJintegrand ρ ε (q + 1) σ
        (r322DetJTupleSucc q
          p.1 p.2.1 p.2.2)
  have hp :
      MeasurePreserving e
        (paperMeasure.prod (paperMeasure.prod τ))
        (paperMeasure.prod (paperMeasure.prod τ)) :=
    measurePreserving_r322MoveMiddleMeasurableEquiv
      paperMeasure paperMeasure τ
  have hf :
      Integrable f
        (paperMeasure.prod
          (paperMeasure.prod τ)) := by
    simpa only [f, τ] using
      integrable_detJintegrand_flat_r322
        ρ hε hε1 q σ
  have htarget :
      Integrable
        (fun p :
            T4 × (T4 × (Fin (2 * q) → T4)) =>
          f (e.symm p))
        (paperMeasure.prod
          (paperMeasure.prod τ)) := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p :
          T4 × (T4 × (Fin (2 * q) → T4)) =>
            f (e.symm p))
    apply hiff.mp
    convert hf using 1
    funext p
    simp only [Function.comp_apply,
      e.symm_apply_apply]
  convert htarget using 1
  funext p
  rcases p with ⟨w, z, v⟩
  rfl

/-- Fubini supplies at least one terminal endpoint whose remaining
`(z,v)` section is integrable. -/
theorem exists_integrable_detJintegrand_endpoint_section
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1)))) :
    ∃ w : T4,
      Integrable
        (fun p : T4 × (Fin (2 * q) → T4) =>
          detJintegrand ρ ε (q + 1) σ
            (r322DetJTupleSucc q
              p.1 w p.2))
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * q) =>
            paperMeasure)) := by
  have hterminal :=
    integrable_detJintegrand_terminalFirst_r322
      ρ hε hε1 q σ
  have hae := hterminal.prod_right_ae
  have hpaper : paperMeasure ≠ 0 := by
    intro hzero
    have hmass :=
      congrArg
        (fun μ : Measure T4 => μ Set.univ)
        hzero
    simp [paperMeasure] at hmass
    have hpos :
        0 < (2 * Real.pi) ^ (dim : ℕ) := by
      positivity
    linarith
  letI : NeZero paperMeasure := ⟨hpaper⟩
  exact Filter.Eventually.exists hae

/-- Integrability of one raw endpoint section descends through the
internal Bochner integral defining `detJ`. -/
theorem integrable_detJ_of_endpoint_section
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (w : T4)
    (hsection :
      Integrable
        (fun p : T4 × (Fin (2 * q) → T4) =>
          detJintegrand ρ ε (q + 1) σ
            (r322DetJTupleSucc q p.1 w p.2))
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (2 * q) =>
            paperMeasure))) :
    Integrable
      (fun z : T4 =>
        detJ ρ lam ε (q + 1) σ z w)
      paperMeasure := by
  have hinner :=
    hsection.integral_prod_left
  have hscaled :=
    hinner.const_mul
      (lamEps lam ε ^ (2 * (q + 1)))
  convert hscaled using 1
  funext z
  rfl

/-! ## Translation invariance of the complete `J` kernel -/

theorem assemble_add_const_r322
    {n : ℕ} (x y a : T4) (v : Fin n → T4)
    (j : Fin (n + 2)) :
    assemble (x + a) (y + a)
        (fun i => v i + a) j =
      assemble x y v j + a := by
  unfold assemble
  split_ifs <;> rfl

/-- The frozen `J` integrand contains only differences, so a simultaneous
translation of all vertices cancels pointwise. -/
theorem detJintegrand_add_const_r322
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (x : Fin (2 * q) → T4) (a : T4) :
    detJintegrand ρ ε q σ (fun i => x i + a) =
      detJintegrand ρ ε q σ x := by
  unfold detJintegrand
  apply congrArg₂ (· * ·)
  · apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro e _he
      split_ifs
      · rfl
      · rw [add_sub_add_right_eq_sub]
      · rfl
    · apply congrArg List.prod
      apply List.map_congr_left
      intro p _hp
      unfold diffFactorJ
      split_ifs
      · simp only [add_sub_add_right_eq_sub]
      · rfl
  · apply Finset.prod_congr rfl
    intro i _hi
    rw [add_sub_add_right_eq_sub]

/-- Simultaneously translating both endpoints leaves a `J` kernel
unchanged.  The internal variables are reindexed by Haar translation. -/
theorem detJ_add_const_r322
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (z w a : T4) :
    detJ ρ lam ε q σ (z + a) (w + a) =
      detJ ρ lam ε q σ z w := by
  cases q with
  | zero =>
      rfl
  | succ q =>
      simp only [detJ]
      apply congrArg (fun t : ℝ =>
        lamEps lam ε ^ (2 * (q + 1)) * t)
      let shift :
          (Fin (2 * q) → T4) ≃ᵐ
            (Fin (2 * q) → T4) :=
        MeasurableEquiv.piCongrRight fun _ =>
          MeasurableEquiv.addRight a
      have hcoord (_i : Fin (2 * q)) :
          MeasurePreserving (fun x : T4 => x + a)
            paperMeasure paperMeasure := by
        rw [paperMeasure_eq_volume]
        exact
          measurePreserving_add_right
            (volume : Measure T4) a
      have hp :
          MeasurePreserving shift
            (Measure.pi fun _ : Fin (2 * q) =>
              paperMeasure)
            (Measure.pi fun _ : Fin (2 * q) =>
              paperMeasure) := by
        change
          MeasurePreserving
            (fun v i => v i + a)
            (Measure.pi fun _ : Fin (2 * q) =>
              paperMeasure)
            (Measure.pi fun _ : Fin (2 * q) =>
              paperMeasure)
        exact
          measurePreserving_pi
            (fun _ : Fin (2 * q) => paperMeasure)
            (fun _ : Fin (2 * q) => paperMeasure)
            hcoord
      let fLeft : (Fin (2 * q) → T4) → ℝ :=
        fun v =>
          detJintegrand ρ ε (q + 1) σ
            (r322DetJTupleSucc q
              (z + a) (w + a) v)
      let fRight : (Fin (2 * q) → T4) → ℝ :=
        fun v =>
          detJintegrand ρ ε (q + 1) σ
            (r322DetJTupleSucc q z w v)
      calc
        (∫ v : Fin (2 * q) → T4,
            detJintegrand ρ ε (q + 1) σ
              (r322DetJTupleSucc q
                (z + a) (w + a) v)
            ∂(Measure.pi fun _ => paperMeasure)) =
            ∫ v : Fin (2 * q) → T4,
              fLeft (shift v)
              ∂(Measure.pi fun _ => paperMeasure) := by
          exact (hp.integral_comp' fLeft).symm
        _ = ∫ v : Fin (2 * q) → T4,
              fRight v
              ∂(Measure.pi fun _ => paperMeasure) := by
          apply integral_congr_ae
          filter_upwards with v
          unfold fLeft fRight
          change
            detJintegrand ρ ε (q + 1) σ
                (r322DetJTupleSucc q
                  (z + a) (w + a)
                  (fun i => v i + a)) =
              detJintegrand ρ ε (q + 1) σ
                (r322DetJTupleSucc q z w v)
          have htuple :
              r322DetJTupleSucc q
                  (z + a) (w + a)
                  (fun i => v i + a) =
                fun j =>
                  r322DetJTupleSucc q z w v j + a := by
            funext j
            unfold r322DetJTupleSucc
            exact assemble_add_const_r322 z w a v _
          rw [htuple, detJintegrand_add_const_r322]
        _ = _ := rfl

/-- Difference form of translation invariance. -/
theorem detJ_eq_diff_r322
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (z w : T4) :
    detJ ρ lam ε q σ z w =
      detJ ρ lam ε q σ (z - w) 0 := by
  have h :=
    detJ_add_const_r322
      ρ lam ε q σ (z - w) 0 w
  simpa using h

/-- Every positive-order frozen `J` kernel is genuinely integrable at
the fixed endpoint `w=0`.  The exceptional endpoint supplied by Fubini
is moved to zero by simultaneous Haar translation. -/
theorem integrable_detJ_zero
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q : ℕ) (hq : 1 ≤ q)
    (σ : PartialPairing (Fin (2 * q))) :
    Integrable
      (fun z : T4 =>
        detJ ρ lam ε q σ z 0)
      paperMeasure := by
  cases q with
  | zero =>
      omega
  | succ q =>
      obtain ⟨w, hsection⟩ :=
        exists_integrable_detJintegrand_endpoint_section
          ρ hε hε1 q σ
      have hdet :
          Integrable
            (fun z : T4 =>
              detJ ρ lam ε (q + 1) σ z w)
            paperMeasure :=
        integrable_detJ_of_endpoint_section
          ρ lam ε q σ w hsection
      let shift : T4 ≃ᵐ T4 :=
        MeasurableEquiv.piCongrRight fun i =>
          MeasurableEquiv.addRight (w i)
      have hp :
          MeasurePreserving shift
            paperMeasure paperMeasure := by
        rw [paperMeasure_eq_volume]
        change
          MeasurePreserving
            (fun z : T4 => fun i => z i + w i)
            (volume : Measure T4)
            (volume : Measure T4)
        exact
          measurePreserving_pi
            (fun _ : Fin dim =>
              (volume :
                Measure (AddCircle (2 * Real.pi))))
            (fun _ : Fin dim =>
              (volume :
                Measure (AddCircle (2 * Real.pi))))
            (fun i =>
              measurePreserving_add_right
                (volume :
                  Measure (AddCircle (2 * Real.pi)))
                (w i))
      have htranslated :=
        hp.integrable_comp_of_integrable hdet
      have hfun :
          ((fun z : T4 =>
              detJ ρ lam ε (q + 1) σ z w) ∘
              shift) =
            fun z : T4 =>
              detJ ρ lam ε (q + 1) σ z 0 := by
        funext z
        change
          detJ ρ lam ε (q + 1) σ
              (fun i => z i + w i) w =
            detJ ρ lam ε (q + 1) σ z 0
        have hzadd :
            (fun i => z i + w i) = z + w := by
          rfl
        rw [hzadd]
        simpa only [zero_add] using
          (detJ_add_const_r322
            ρ lam ε (q + 1) σ z 0 w)
      rw [hfun] at htranslated
      exact htranslated

end

end Anderson4D
