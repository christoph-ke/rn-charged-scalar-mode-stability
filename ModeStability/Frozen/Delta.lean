module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon

/-!
# `ModeStability.delta`

Spherical research notes in preparation, p. 1, (1.1).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- `Δ(r) = (r − a)(r − b)` of (1.1). -/
noncomputable def delta (M Q r : ℝ) : ℝ := (r - outerHorizon M Q) * (r - innerHorizon M Q)

end ModeStability

end
