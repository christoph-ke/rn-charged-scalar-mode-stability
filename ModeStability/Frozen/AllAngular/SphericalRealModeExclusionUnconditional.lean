module

public import Mathlib
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Provider.AllAngular.SphericalRealModeExclusionUnconditional

/-!
# `ModeStability.AllAngular.spherical_real_mode_exclusion_unconditional`

All-angular research notes in preparation, p. 2, Theorem 1.1, case L = 0, e = qQ, |Q| < M
(bridge corollary), stated in the encodings of the spherical research notes, p. 1, Theorem 1.1.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- The spherical Theorem 1.1 (`ModeStability.spherical_real_mode_exclusion`) without the trust
boundary. -/
theorem spherical_real_mode_exclusion_unconditional :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → ω ≠ 0 →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ), ModeStability.IsRadialSolution M Q q ω R →
        ModeStability.HorizonCondition M Q q ω R BH → ModeStability.InfinityCondition M Q q ω R BI →
          EqOn R 0 (Ioi (outerHorizon M Q)) :=
  by exact ModeStability.Provider.AllAngular.spherical_real_mode_exclusion_unconditional

end ModeStability.AllAngular

end
