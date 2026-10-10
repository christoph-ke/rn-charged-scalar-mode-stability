module

public import ModeStability.Frozen.SphericalRealModeExclusion
public import ModeStability.AllAngular.BandExclusionFinal

/-!
# The spherical Theorem 1.1 without the trust boundary

The sealed `ModeStability.spherical_real_mode_exclusion` (Theorem 1.1 of
the spherical research notes in preparation) takes `ComplementaryBandExclusion` as its only
non-source hypothesis. `AllAngular.complementaryBandExclusion_proved` proves that hypothesis by
the method of the all-angular research notes in preparation (at `L = 0`), so the spherical
theorem holds unconditionally. The source-facing bridge theorem is also proved.
-/

public section

open Set

namespace ModeStability.AllAngular

/-- The spherical real mode exclusion (Theorem 1.1 of the spherical paper), unconditionally. -/
theorem spherical_real_mode_exclusion_unconditional_aux :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → ω ≠ 0 →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ), ModeStability.IsRadialSolution M Q q ω R →
        ModeStability.HorizonCondition M Q q ω R BH →
          ModeStability.InfinityCondition M Q q ω R BI →
            EqOn R 0 (Ioi (outerHorizon M Q)) :=
  ModeStability.spherical_real_mode_exclusion complementaryBandExclusion_proved

end ModeStability.AllAngular

end
