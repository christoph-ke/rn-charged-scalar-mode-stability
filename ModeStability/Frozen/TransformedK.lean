module

public import Mathlib
public import ModeStability.Frozen.StaticSolution
public import ModeStability.Frozen.RadiusOf
public import ModeStability.Frozen.RadialK

/-!
# `ModeStability.transformedK`

Spherical research notes in preparation, p. 2, (2.2).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- The transformed coefficient `k(x) = g(r)² K(r)` of (2.2), at `r = r(x)`. -/
noncomputable def transformedK (M Q q ω x : ℝ) : ℝ :=
  staticSolution M Q (radiusOf M Q x) ^ 2 * radialK (q * Q) ω (radiusOf M Q x)

end ModeStability

end
