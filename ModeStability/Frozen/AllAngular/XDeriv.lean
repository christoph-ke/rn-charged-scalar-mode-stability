module

public import Mathlib
public import ModeStability.Frozen.Delta

/-!
# `ModeStability.AllAngular.xDeriv`

All-angular research notes in preparation, p. 2, (2.2) and the sentence after it (x' = 1/(Δg²)).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- The derivative in the coordinate `x` of (2.2), written in `r`: since `x' = 1/(Δg²)`,
`∂_x = Δ g² ∂_r` (p. 2). -/
noncomputable def xDeriv (M Q : ℝ) (g f : ℝ → ℝ) (r : ℝ) : ℝ :=
  delta M Q r * g r ^ 2 * deriv f r

end ModeStability.AllAngular

end
