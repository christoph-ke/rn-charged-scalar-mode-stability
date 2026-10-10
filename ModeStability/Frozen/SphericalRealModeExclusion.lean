module

public import Mathlib
public import ModeStability.Frozen.ComplementaryBandExclusion
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Provider.SphericalRealModeExclusion

/-!
# `ModeStability.spherical_real_mode_exclusion`

Spherical research notes in preparation, p. 1, Theorem 1.1.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- **Theorem 1.1** (spherical real mode exclusion), conditional on the Appendix A trust
boundary `ComplementaryBandExclusion`. -/
theorem spherical_real_mode_exclusion :
    ComplementaryBandExclusion →
      ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → ω ≠ 0 →
        ∀ (R : ℝ → ℂ) (BH BI : ℂ), IsRadialSolution M Q q ω R →
          HorizonCondition M Q q ω R BH → InfinityCondition M Q q ω R BI →
            EqOn R 0 (Ioi (outerHorizon M Q)) :=
  by exact ModeStability.Provider.spherical_real_mode_exclusion

end ModeStability

end
