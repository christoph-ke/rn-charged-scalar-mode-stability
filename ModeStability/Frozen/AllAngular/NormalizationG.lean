module

public import Mathlib
public import ModeStability.Frozen.AllAngular.StaticSolutionAA

/-!
# `ModeStability.AllAngular.normalizationG`

All-angular research notes in preparation, p. 2, (2.2), in the superradiant regime (1.7).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- The frequency-dependent normalization `g` of (2.2), in the superradiant regime (1.7):
`g = 1` if `a < r₀ < 2M` and `g = h` if `r₀ ≥ 2M`, where `r₀ = e/ω`. -/
noncomputable def normalizationG (M Q e ω r : ℝ) : ℝ :=
  if e / ω < 2 * M then 1 else staticSolutionAA M Q r

end ModeStability.AllAngular

end
