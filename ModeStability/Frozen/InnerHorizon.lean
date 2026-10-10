module

public import Mathlib

/-!
# `ModeStability.innerHorizon`

Spherical research notes in preparation, p. 1, (1.1).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- The inner horizon radius `b = M − √(M² − Q²)` of (1.1). -/
noncomputable def innerHorizon (M Q : ℝ) : ℝ := M - Real.sqrt (M ^ 2 - Q ^ 2)

end ModeStability

end
