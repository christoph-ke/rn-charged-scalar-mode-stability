module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon

/-!
# `ModeStability.radiusOf`

Spherical research notes in preparation, p. 2, (2.2); p. 3, (2.11).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- The inverse of the coordinate `x = 1/g(r)` of (2.2), in the explicit form (2.11):
`r = a + d / (e^{d/x} − 1)`. Characterized by `radiusOf_spec`. -/
noncomputable def radiusOf (M Q x : ℝ) : ℝ :=
  outerHorizon M Q + (outerHorizon M Q - innerHorizon M Q) /
    (Real.exp ((outerHorizon M Q - innerHorizon M Q) / x) - 1)

end ModeStability

end
