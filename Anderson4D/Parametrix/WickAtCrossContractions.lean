import Anderson4D.Probability.CrossWickEquiv
import Anderson4D.Parametrix.WickAtBridge

/-!
# Cross contractions for `wickAt`

This file transports the generic list-indexed Wick orthogonality output to
the paper's sum over bijections between the single sets of two partial
pairings.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The cross-contraction list sum for two `wickAt` label lists is exactly
the finite sum over bijections between the two single-index subtypes. -/
theorem crossWickList_wickAtSingleLabels_eq_crossSingles
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (xtp xtm : Fin (m + 2) → T4)
    (C : T4 → T4 → ℝ) :
    crossWickList C
        (wickAtSingleLabels κp xtp)
        (wickAtSingleLabels κm xtm) =
      crossSinglesEquivCovarianceSum κp κm
        (fun i j =>
          C (xtp (varIdx i.val)) (xtm (varIdx j.val))) := by
  rw [crossWickList_eq_listEquivCovarianceSum]
  simpa only [wickAtSingleLabels,
      Finset.coe_orderIsoOfFin_apply,
      crossSinglesEquivCovarianceSum,
      crossSinglesEquivCovarianceProduct] using
    (listEquivCovarianceSum_orderedFinsets
      κp.singles κm.singles C
      (fun i => xtp (varIdx i.val))
      (fun j => xtm (varIdx j.val)))

end

end Anderson4D
