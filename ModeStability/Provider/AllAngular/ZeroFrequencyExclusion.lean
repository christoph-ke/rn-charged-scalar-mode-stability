module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.AllAngular.ZeroFrequencyExclusion

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.ZeroFrequencyExclusion` supplies the proof of the
corresponding source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Set

namespace ModeStability.Provider.AllAngular

theorem zero_frequency_exclusion :
    ∀ (M Q e L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L →
      ∀ (R : ℝ → ℂ) (BH : ℂ), ModeStability.AllAngular.IsRadialSolutionL M Q e 0 L R →
        ModeStability.AllAngular.HorizonConditionL M Q e 0 R BH →
        MeasureTheory.IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi (ModeStability.outerHorizon M Q)) →
          EqOn R 0 (Ioi (ModeStability.outerHorizon M Q)) :=
  ModeStability.AllAngular.zero_frequency_exclusion_integralPhase

end ModeStability.Provider.AllAngular

end
