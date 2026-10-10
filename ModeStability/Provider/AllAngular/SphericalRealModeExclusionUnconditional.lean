module

public import Mathlib
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.SphericalRealModeExclusion
public import ModeStability.Frozen.AllAngular.ComplementaryBandExclusionHolds

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.SphericalRealModeExclusionUnconditional` supplies the proof
of the corresponding source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Set

namespace ModeStability.Provider.AllAngular

theorem spherical_real_mode_exclusion_unconditional :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → ω ≠ 0 →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ), ModeStability.IsRadialSolution M Q q ω R →
        ModeStability.HorizonCondition M Q q ω R BH →
          ModeStability.InfinityCondition M Q q ω R BI →
            EqOn R 0 (Ioi (ModeStability.outerHorizon M Q)) :=
  ModeStability.spherical_real_mode_exclusion
    ModeStability.AllAngular.complementaryBandExclusion_holds

end ModeStability.Provider.AllAngular

end
