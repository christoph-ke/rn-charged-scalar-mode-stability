module

public import ModeStability.Main.Reduction
public import ModeStability.Frozen.SeparationAtCorotation

/-!
# Proof implementation

`ModeStability.Provider.SphericalRealModeExclusion` supplies the proof of the corresponding
source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Provider

theorem spherical_real_mode_exclusion :
    ComplementaryBandExclusion →
      ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → ω ≠ 0 →
        ∀ (R : ℝ → ℂ) (BH BI : ℂ), IsRadialSolution M Q q ω R →
          HorizonCondition M Q q ω R BH → InfinityCondition M Q q ω R BI →
            EqOn R 0 (Ioi (outerHorizon M Q)) :=
  Main.mode_exclusion_of_separation ModeStability.separation_at_corotation

end ModeStability.Provider

end
