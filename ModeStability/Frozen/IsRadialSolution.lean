module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK

/-!
# `ModeStability.IsRadialSolution`

Spherical research notes in preparation, p. 1, (1.2).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- `R` solves the spherical radial equation (1.2), `(Δ R')' + K²/Δ · R = 0`, on the
exterior `r > a`, with `K(r) = ω r² − q Q r`. -/
def IsRadialSolution (M Q q ω : ℝ) (R : ℝ → ℂ) : Prop :=
  ∀ r ∈ Ioi (outerHorizon M Q),
    DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK (q * Q) ω r) ^ 2 / delta M Q r : ℝ) : ℂ) * R r) r

end ModeStability

end
