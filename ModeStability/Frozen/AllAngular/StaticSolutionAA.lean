module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon

/-!
# `ModeStability.AllAngular.staticSolutionAA`

All-angular research notes in preparation, p. 2, (2.1).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- The positive spherical static solution `h` of (2.1):
`h = (2δ)⁻¹ log((r − b)/(r − a))` for `δ > 0` and `h = 1/(r − M)` for `δ = 0`. -/
noncomputable def staticSolutionAA (M Q r : ℝ) : ℝ :=
  if 0 < M ^ 2 - Q ^ 2 then
    1 / (2 * Real.sqrt (M ^ 2 - Q ^ 2)) *
      Real.log ((r - innerHorizon M Q) / (r - outerHorizon M Q))
  else 1 / (r - M)

end ModeStability.AllAngular

end
