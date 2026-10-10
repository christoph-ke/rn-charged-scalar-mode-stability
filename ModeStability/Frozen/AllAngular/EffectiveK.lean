module

public import Mathlib
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.AllAngular.NormalizationG

/-!
# `ModeStability.AllAngular.effectiveK`

All-angular research notes in preparation, p. 4, (3.2).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- The signed effective frequency `k̂ = sgn(K) g² √(K² − LΔ)` of (3.2) (`k̂ = k = g²K` when
`L = 0`). -/
noncomputable def effectiveK (M Q e ω L r : ℝ) : ℝ :=
  SignType.sign (radialK e ω r) * normalizationG M Q e ω r ^ 2 *
    Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r)

end ModeStability.AllAngular

end
