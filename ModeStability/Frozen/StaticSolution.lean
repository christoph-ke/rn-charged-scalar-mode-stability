module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon

/-!
# `ModeStability.staticSolution`

Spherical research notes in preparation, p. 2, (2.1).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- The static solution `g(r) = d⁻¹ log((r − b)/(r − a))` of (2.1). -/
noncomputable def staticSolution (M Q r : ℝ) : ℝ :=
  1 / (outerHorizon M Q - innerHorizon M Q) *
    Real.log ((r - innerHorizon M Q) / (r - outerHorizon M Q))

end ModeStability

end
