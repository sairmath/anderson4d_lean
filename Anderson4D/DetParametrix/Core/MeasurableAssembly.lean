import Anderson4D.DetParametrix.Core.Kernels

/-!
# Deterministic measurability of the parametrix tuple assembler

The tuple assembler is part of the deterministic kernel layer.  Keeping its
measurability theorem here prevents continuum and deterministic-parametrix
files from importing the random-parametrix measurability module.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- Joint measurability of the external/internal tuple assembler. -/
theorem measurable_assemble_prod (m : ℕ) :
    Measurable fun p : T4 × (T4 × (Fin m → T4)) =>
      assemble p.1 p.2.1 p.2.2 := by
  apply measurable_pi_lambda
  intro j
  unfold assemble
  by_cases h0 : j.val = 0
  · simp only [h0, dite_true]
    exact measurable_fst
  · simp only [h0, dite_false]
    by_cases hlast : j.val = m + 1
    · simp only [hlast, dite_true]
      exact measurable_fst.comp measurable_snd
    · simp only [hlast, dite_false]
      let i : Fin m :=
        ⟨j.val - 1, by have := j.isLt; omega⟩
      exact (measurable_pi_apply i).comp
        (measurable_snd.comp measurable_snd)

end Anderson4D
