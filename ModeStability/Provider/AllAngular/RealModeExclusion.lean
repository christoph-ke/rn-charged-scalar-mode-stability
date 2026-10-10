module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL
public import ModeStability.AllAngular.RealModeExclusionL

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.RealModeExclusion` supplies the proof of the corresponding
source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Provider.AllAngular

theorem real_mode_exclusion :
    ∀ (M Q e ω L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L → ω ≠ 0 →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ), ModeStability.AllAngular.IsRadialSolutionL M Q e ω L R →
        ModeStability.AllAngular.HorizonConditionL M Q e ω R BH →
          ModeStability.AllAngular.InfinityConditionL M Q e ω R BI →
            EqOn R 0 (Ioi (ModeStability.outerHorizon M Q)) :=
  ModeStability.AllAngular.real_mode_exclusion_integralPhase

end ModeStability.Provider.AllAngular

end
