module

public import Mathlib

/-!
# `ModeStability.radialK`

Spherical research notes in preparation, p. 1, (1.2).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- `K(r) = ω r² − e r` of (1.2); callers pass `e = q Q`. -/
def radialK (e ω r : ℝ) : ℝ := ω * r ^ 2 - e * r

end ModeStability

end
