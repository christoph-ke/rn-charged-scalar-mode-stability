module

public import Mathlib
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.StaticSolution
public import ModeStability.Provider.SeparationAtCorotation

/-!
# `ModeStability.separation_at_corotation`

Spherical research notes in preparation, p. 3, Proposition 2.3, (2.16); band (1.6) on p. 2.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- **Proposition 2.3** (separation at corotation), in band (1.6): nonvanishing at `r₀`,
the inequalities (2.16), and the nonvanishing radial Wronskian. -/
theorem separation_at_corotation :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → 0 < ω →
      ∀ (r₀ : ℝ), r₀ = q * Q / ω → 2 * M < r₀ →
        ∀ (RH RI : ℝ → ℂ) (BH BI : ℂ),
          IsRadialSolution M Q q ω RH → HorizonCondition M Q q ω RH BH →
          ¬ EqOn RH 0 (Ioi (outerHorizon M Q)) →
          IsRadialSolution M Q q ω RI → InfinityCondition M Q q ω RI BI →
          ¬ EqOn RI 0 (Ioi (outerHorizon M Q)) →
            RH r₀ ≠ 0 ∧ RI r₀ ≠ 0 ∧
              -1 / (delta M Q r₀ * staticSolution M Q r₀) < (deriv RH r₀ / RH r₀).re ∧
              (deriv RI r₀ / RI r₀).re < -1 / (delta M Q r₀ * staticSolution M Q r₀) ∧
              delta M Q r₀ * (RH r₀ * deriv RI r₀ - deriv RH r₀ * RI r₀) ≠ 0 :=
  by exact ModeStability.Provider.separation_at_corotation

end ModeStability

end
