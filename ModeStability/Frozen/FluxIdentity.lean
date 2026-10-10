module

public import Mathlib
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Provider.FluxIdentity

/-!
# `ModeStability.flux_identity`

Spherical research notes in preparation, p. 1, (1.5).
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- **(1.5)** (conserved radial flux) for a solution satisfying both boundary conditions. -/
theorem flux_identity :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ), IsRadialSolution M Q q ω R →
        HorizonCondition M Q q ω R BH → InfinityCondition M Q q ω R BI →
          (∀ r ∈ Ioi (outerHorizon M Q),
            delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im =
              -radialK (q * Q) ω (outerHorizon M Q) * ‖BH‖ ^ 2) ∧
            -radialK (q * Q) ω (outerHorizon M Q) * ‖BH‖ ^ 2 = ω * ‖BI‖ ^ 2 :=
  by exact ModeStability.Provider.flux_identity

end ModeStability

end
