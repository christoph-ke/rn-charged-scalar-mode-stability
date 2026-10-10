module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition

/-!
# `ModeStability.ComplementaryBandExclusion`

Spherical research notes in preparation, pp. 1–2 (Section 1) and Appendix A, pp. 6–7.
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- Complementary-band exclusion from Section 1 and Appendix A: for subextremal
parameters with `ω > 0` and `2Mω − e ≥ 0` (`e = q Q`), every solution of (1.2)
satisfying (1.3) and (1.4) vanishes on the exterior. The spherical Theorem 1.1
takes this proposition as an explicit hypothesis. The theorem
`AllAngular.complementaryBandExclusion_holds` proves it by the all-angular route;
the transform outlined in Appendix A is not formalized. -/
def ComplementaryBandExclusion : Prop :=
  ∀ M Q q ω : ℝ, 0 < M → |Q| < M → 0 < ω → 0 ≤ 2 * M * ω - q * Q →
    ∀ (R : ℝ → ℂ) (BH BI : ℂ), IsRadialSolution M Q q ω R →
      HorizonCondition M Q q ω R BH → InfinityCondition M Q q ω R BI →
        EqOn R 0 (Ioi (outerHorizon M Q))

end ModeStability

end
