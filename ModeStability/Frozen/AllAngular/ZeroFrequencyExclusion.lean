module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.Provider.AllAngular.ZeroFrequencyExclusion

/-!
# `ModeStability.AllAngular.zero_frequency_exclusion`

All-angular research notes in preparation, p. 9, Proposition 7.1, (7.1).
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

theorem zero_frequency_exclusion :
    ∀ (M Q e L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L →
      ∀ (R : ℝ → ℂ) (BH : ℂ), IsRadialSolutionL M Q e 0 L R →
        HorizonConditionL M Q e 0 R BH →
        IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi (outerHorizon M Q)) →
          EqOn R 0 (Ioi (outerHorizon M Q)) :=
  by exact ModeStability.Provider.AllAngular.zero_frequency_exclusion

end ModeStability.AllAngular

end
