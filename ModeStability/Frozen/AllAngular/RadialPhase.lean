module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK

/-!
# `ModeStability.AllAngular.radialPhase`

All-angular research notes in preparation, p. 1, (1.3).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- The phase `Θ(r) = ∫^r K/Δ dρ` of (1.3), with the base point fixed at `a + 1` (any base point
in the exterior changes `Θ` by a constant, absorbed into the leading coefficients). -/
noncomputable def radialPhase (M Q e ω r : ℝ) : ℝ :=
  ∫ ρ in (outerHorizon M Q + 1)..r, radialK e ω ρ / delta M Q ρ

end ModeStability.AllAngular

end
