/-
Reader's entry point. Open this file in a Lean-aware editor or IDE *after*
`lake build` has finished; nothing here is part of the proof, it only
*displays* what was proved. Inspect each `#check` line in the editor's Lean
output view (called InfoView in VS Code), then jump to its declaration to
read the implementation.
-/
import Anderson4D.Main.Final

open Anderson4D

/- 1. The theorem itself: the conditional form of Deng-Shen Theorem 1.1. -/
#check @Anderson4D.main_conditional_law

/- 2. What its conclusion unfolds to: every finite family of Fourier modes
      converges in distribution to the explicit Gaussian law. -/
#check Anderson4D.MainLawStatement

/- 3. What that limit law is. -/
#check Anderson4D.gaussianLimitLaw

/- 4. The sole external input (paper Prop. 3.6, quoted from Gabriel-Rosati).
      It is an ordinary hypothesis of the theorem, not an added axiom. -/
#check Anderson4D.Prop36Family

/- 5. The hardest paper estimates used by the final theorem.

      The full axiom audit deliberately lives in `bash scripts/release_gate.sh`:
      traversing the complete dependency graph is much slower than this
      reader-facing file and checks the whole public theorem spine. -/
#check @Anderson4D.deterministic_second_moment_bound
#check Anderson4D.permSum_estimate
#check Anderson4D.volume_estimate
#check Anderson4D.proposition41
