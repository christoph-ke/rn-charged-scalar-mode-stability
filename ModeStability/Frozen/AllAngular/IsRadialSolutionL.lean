module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK

/-!
# `ModeStability.AllAngular.IsRadialSolutionL`

All-angular research notes in preparation, p. 1, (1.2) and the sentence after it; p. 2, the
sentence after Theorem 1.1.
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- `R` solves the radial equation (1.2), `(ΔR')' + (K²/Δ − L) R = 0`, on the exterior `r > a`,
with `K(r) = ωr² − er` and `e` an independent real coefficient (p. 2: the charged scalar problem
is `e = qQ`); `L ≥ 0` is a real angular parameter (`L = ℓ(ℓ + 1)` physically). -/
def IsRadialSolutionL (M Q e ω L : ℝ) (R : ℝ → ℂ) : Prop :=
  ∀ r ∈ Ioi (outerHorizon M Q),
    DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r

end ModeStability.AllAngular

end
