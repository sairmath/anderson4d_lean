import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualCompletePrimitiveHead

/-!
# Why the central gap factor is there

Paper: R-324 — §4.2 Step 3, the cut edge that does not exist

A nested cross block straddles the cut: its sites lie partly in the left
copy and partly in the right one.  Read in the block's *own* increasing
order it is a chain of `2k` sites with `2k-1` edges — but one of those
edges runs from the last left site to the first right site, and **that edge
exists in neither half's chain**.  The two halves are separate chains; the
cut is exactly where they stop.

The nested machinery handles this by carrying `torusDistSq(gap)` as an
explicit numerator:

```lean
crossGapPrimitiveIntegrand ctx ρ ε G x =
  torusDistSq (x ctx.leftGapIndex - x ctx.rightGapIndex) *
    primitiveIntegrand ρ ε ctx.order ctx.one_le_order G ctx.blockPairing x
```

and `normalizedHeadDensity` instantiates `G := normalizedInput = |·|⁻²` at
*every* edge, the spurious cut edge included.  The two cancel:

```
torusDistSq z · invSqKer z = 1     (off the diagonal)
```

So the central gap factor is not an estimate and not a device — it is the
exact compensation for the one normalized edge the physical chains do not
contain.  This module records that, because it is what fixes the shape of
the chain-side factorization: the two half chain products must reproduce
*all* the block's edges **except** the cut one, plus the two boundary
edges of `ctx.connector`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- **The central gap factor cancels the spurious normalized cut edge.**

`invSqKer` is `(torusDistSq)⁻¹`, so off the diagonal the explicit
`torusDistSq(gap)` numerator of `crossGapPrimitiveIntegrand` exactly undoes
the `|gap|⁻²` that `normalizedInput` places on the block's cut edge — the
edge that exists in the block's own ordering but in neither half chain. -/
theorem torusDistSq_mul_invSqKer (z : T4) (hz : torusDistSq z ≠ 0) :
    torusDistSq z * invSqKer z = 1 := by
  unfold invSqKer
  exact mul_inv_cancel₀ hz

/-- The same cancellation in the order the head density presents it. -/
theorem invSqKer_mul_torusDistSq (z : T4) (hz : torusDistSq z ≠ 0) :
    invSqKer z * torusDistSq z = 1 := by
  rw [mul_comm]
  exact torusDistSq_mul_invSqKer z hz

/-- On the diagonal the compensation degenerates to `0`, matching the
junk value `invSqKer 0 = 0⁻¹ = 0` mathlib assigns there. -/
@[simp] theorem torusDistSq_mul_invSqKer_self_zero :
    torusDistSq (0 : T4) * invSqKer (0 : T4) = 0 := by
  unfold invSqKer
  rw [(torusDistSq_eq_zero_iff (0 : T4)).mpr rfl]
  simp

end Anderson4D
