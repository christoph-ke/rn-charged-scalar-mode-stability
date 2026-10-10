module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL
public import ModeStability.Provider.AllAngular.RealModeExclusion

/-!
# `ModeStability.AllAngular.real_mode_exclusion`

All-angular research notes in preparation, p. 2, Theorem 1.1 and the sentence after it; the
conditions (1.2)–(1.5) on p. 1.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- **Theorem 1.1** (real-frequency exclusion) of the all-angular paper: for `M > 0`, `|Q| ≤ M`,
real `e`, `L ≥ 0` and real `ω ≠ 0`, every solution of (1.2) satisfying the future-horizon and
outgoing-infinity conditions vanishes on the exterior. -/
theorem real_mode_exclusion :
    ∀ (M Q e ω L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L → ω ≠ 0 →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ), IsRadialSolutionL M Q e ω L R →
        HorizonConditionL M Q e ω R BH → InfinityConditionL M Q e ω R BI →
          EqOn R 0 (Ioi (outerHorizon M Q)) :=
  by exact ModeStability.Provider.AllAngular.real_mode_exclusion

end ModeStability.AllAngular

end
