module

public import Mathlib

/-!
# `ModeStability.outerHorizon`

Spherical research notes in preparation, p. 1, (1.1).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- The outer (event) horizon radius `a = M + √(M² − Q²)` of (1.1). -/
noncomputable def outerHorizon (M Q : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - Q ^ 2)

end ModeStability

end
