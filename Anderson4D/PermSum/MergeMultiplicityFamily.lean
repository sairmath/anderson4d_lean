import Anderson4D.PermSum.MergeExpansionCount

/-!
# Finite families of run-compressed multiplicity profiles

For an original multiplicity function `ml`, every run-compressed
multiplicity lies coordinatewise in `Fin (ml a + 1)`.  This gives a finite
profile carrier of size at most `2 ^ ∑ a, ml a`, and hence the same bound for
every realized image.  The final section packages exact finite regrouping by
these profiles and a uniform nonnegative fiber bound.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Count/list bridge used to read the defining equation of `validWords`. -/
private theorem profile_count_ofFn {β : Type*}
    [BEq β] [LawfulBEq β] [DecidableEq β] :
    ∀ {n : ℕ} (g : Fin n → β) (b : β),
      (List.ofFn g).count b =
        (Finset.univ.filter fun i => g i = b).card
  | 0, g, b => by simp
  | n + 1, g, b => by
      rw [List.ofFn_succ, List.count_cons,
        profile_count_ofFn (fun i => g i.succ) b,
        Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
      simp only [beq_iff_eq]
      omega

/-- Coordinatewise-bounded multiplicity profiles produced by run
compression. -/
abbrev MergeMultiplicityProfile (ml : α → ℕ) :=
  ∀ a, Fin (ml a + 1)

/-- A valid original word, retained as a subtype so its multiplicity proof
is available when its compressed profile is constructed. -/
abbrev MergeValidWord {M : ℕ} (ml : α → ℕ) :=
  ↥(validWords (M := M) ml)

/-- The merged multiplicity of a valid word, packaged in the finite profile
carrier. -/
def mergedMultiplicityProfile {M : ℕ} (ml : α → ℕ)
    (w : MergeValidWord (M := M) ml) :
    MergeMultiplicityProfile ml :=
  fun a =>
    ⟨mergedMultiplicity w.1 a,
      Nat.lt_succ_iff.mpr <| by
        calc
          mergedMultiplicity w.1 a ≤
              (List.ofFn w.1).count a :=
            mergedMultiplicity_le_originalCount w.1 a
          _ =
              (Finset.univ.filter fun i => w.1 i = a).card := by
            rw [profile_count_ofFn]
          _ = ml a := (Finset.mem_filter.mp w.2).2 a⟩

@[simp]
theorem mergedMultiplicityProfile_val {M : ℕ} (ml : α → ℕ)
    (w : MergeValidWord (M := M) ml) (a : α) :
    (mergedMultiplicityProfile ml w a : ℕ) =
      mergedMultiplicity w.1 a := by
  rfl

/-- The natural-valued function underlying a finite profile. -/
def MergeMultiplicityProfile.toNat {ml : α → ℕ}
    (p : MergeMultiplicityProfile ml) : α → ℕ :=
  fun a => p a

@[simp]
theorem mergedMultiplicityProfile_toNat {M : ℕ} (ml : α → ℕ)
    (w : MergeValidWord (M := M) ml) :
    (mergedMultiplicityProfile ml w).toNat =
      mergedMultiplicity w.1 := by
  funext a
  rfl

/-- The entries of the packaged profile sum to the compressed word length. -/
theorem sum_mergedMultiplicityProfile {M : ℕ} (ml : α → ℕ)
    (w : MergeValidWord (M := M) ml) :
    ∑ a : α, (mergedMultiplicityProfile ml w a : ℕ) =
      (mergedWordList w.1).length := by
  simpa using sum_mergedMultiplicity w.1

/-- Elementary coordinate bound used in the profile-cardinality product. -/
private theorem succ_le_two_pow (k : ℕ) :
    k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      omega

/-- Exact cardinality of the full coordinatewise profile carrier. -/
theorem card_mergeMultiplicityProfile (ml : α → ℕ) :
    Fintype.card (MergeMultiplicityProfile ml) =
      ∏ a : α, (ml a + 1) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro a _
  exact Fintype.card_fin _

/-- The full finite profile carrier has at most `2 ^ ∑ a, ml a` elements. -/
theorem card_mergeMultiplicityProfile_le_two_pow_sum
    (ml : α → ℕ) :
    Fintype.card (MergeMultiplicityProfile ml) ≤
      2 ^ (∑ a : α, ml a) := by
  rw [card_mergeMultiplicityProfile]
  calc
    (∏ a : α, (ml a + 1)) ≤
        ∏ a : α, 2 ^ ml a := by
      gcongr with a
      exact succ_le_two_pow (ml a)
    _ = 2 ^ (∑ a : α, ml a) := by
      rw [Finset.prod_pow_eq_pow_sum]

/-- Profiles realized by an arbitrary finite family of valid words. -/
def mergeMultiplicityProfileImage {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml)) :
    Finset (MergeMultiplicityProfile ml) := by
  classical
  exact s.image (mergedMultiplicityProfile ml)

/-- The realized image is no larger than the full profile carrier. -/
theorem card_mergeMultiplicityProfileImage_le_two_pow_sum
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml)) :
    (mergeMultiplicityProfileImage ml s).card ≤
      2 ^ (∑ a : α, ml a) := by
  classical
  calc
    (mergeMultiplicityProfileImage ml s).card ≤
        Fintype.card (MergeMultiplicityProfile ml) := by
      simpa using Finset.card_le_univ
        (mergeMultiplicityProfileImage ml s)
    _ ≤ 2 ^ (∑ a : α, ml a) :=
      card_mergeMultiplicityProfile_le_two_pow_sum ml

/-- All compressed multiplicity profiles realized by valid words. -/
def possibleMergeMultiplicityProfiles {M : ℕ} (ml : α → ℕ) :
    Finset (MergeMultiplicityProfile ml) := by
  classical
  exact mergeMultiplicityProfileImage (M := M) ml
    (Finset.univ : Finset (MergeValidWord (M := M) ml))

/-- The set of all possible compressed profiles has the same exponential
cardinality bound. -/
theorem card_possibleMergeMultiplicityProfiles_le_two_pow_sum
    {M : ℕ} (ml : α → ℕ) :
    (possibleMergeMultiplicityProfiles (M := M) ml).card ≤
      2 ^ (∑ a : α, ml a) := by
  classical
  exact card_mergeMultiplicityProfileImage_le_two_pow_sum
    (M := M) ml
    (Finset.univ : Finset (MergeValidWord (M := M) ml))

/-- Exact regrouping of an arbitrary finite weighted sum by its packaged
run-compressed multiplicity profile. -/
theorem sum_eq_sum_mergeMultiplicityProfile_fibers
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (F : MergeValidWord (M := M) ml → ℝ) :
    (∑ w ∈ s, F w) =
      ∑ p ∈ mergeMultiplicityProfileImage ml s,
        ∑ w ∈ s.filter
            (fun w => mergedMultiplicityProfile ml w = p),
          F w := by
  classical
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun w hw =>
      Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    F

/-- A nonnegative uniformly bounded statistic on realized profiles costs at
most the profile-carrier cardinality. -/
theorem sum_mergeMultiplicityProfileImage_le_two_pow_mul
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (G : MergeMultiplicityProfile ml → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hGB : ∀ p ∈ mergeMultiplicityProfileImage ml s, G p ≤ B) :
    (∑ p ∈ mergeMultiplicityProfileImage ml s, G p) ≤
      (2 : ℝ) ^ (∑ a : α, ml a) * B := by
  classical
  calc
    (∑ p ∈ mergeMultiplicityProfileImage ml s, G p) ≤
        ∑ _p ∈ mergeMultiplicityProfileImage ml s, B := by
      exact Finset.sum_le_sum fun p hp => hGB p hp
    _ = ((mergeMultiplicityProfileImage ml s).card : ℝ) * B := by
      simp
    _ ≤ (2 : ℝ) ^ (∑ a : α, ml a) * B := by
      gcongr
      exact_mod_cast
        card_mergeMultiplicityProfileImage_le_two_pow_sum ml s

/-- Uniform nonnegative fiber estimate after exact profile regrouping. -/
theorem sum_le_two_pow_mul_of_profileFiber_le
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (F : MergeValidWord (M := M) ml → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hfiber :
      ∀ p ∈ mergeMultiplicityProfileImage ml s,
        (∑ w ∈ s.filter
            (fun w => mergedMultiplicityProfile ml w = p),
          F w) ≤ B) :
    (∑ w ∈ s, F w) ≤
      (2 : ℝ) ^ (∑ a : α, ml a) * B := by
  classical
  rw [sum_eq_sum_mergeMultiplicityProfile_fibers]
  apply sum_mergeMultiplicityProfileImage_le_two_pow_mul
  · exact hB
  · exact hfiber

/-- Bundled nonnegative version of the uniform fiber interface. -/
theorem sum_nonneg_and_le_two_pow_mul_of_profileFiber_le
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (F : MergeValidWord (M := M) ml → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hF0 : ∀ w ∈ s, 0 ≤ F w)
    (hfiber :
      ∀ p ∈ mergeMultiplicityProfileImage ml s,
        (∑ w ∈ s.filter
            (fun w => mergedMultiplicityProfile ml w = p),
          F w) ≤ B) :
    0 ≤ (∑ w ∈ s, F w) ∧
      (∑ w ∈ s, F w) ≤
        (2 : ℝ) ^ (∑ a : α, ml a) * B := by
  constructor
  · exact Finset.sum_nonneg fun w hw => hF0 w hw
  · exact sum_le_two_pow_mul_of_profileFiber_le
      ml s F B hB hfiber

end

end Anderson4D
