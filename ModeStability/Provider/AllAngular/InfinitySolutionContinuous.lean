module

public import Mathlib
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL
public import ModeStability.AllAngular.SolutionContinuity

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.InfinitySolutionContinuous` supplies the proof of the
corresponding source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.Provider.AllAngular

/-- ω-continuity of the normalized outgoing solutions on `{ω ≠ 0} × (a, ∞)`. -/
theorem infinity_solution_continuous :
    ∀ (M Q e L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L →
      ∃ RI : ℝ → ℝ → ℂ,
        (∀ ω : ℝ, ω ≠ 0 →
          ModeStability.AllAngular.IsRadialSolutionL M Q e ω L (RI ω) ∧
            ModeStability.AllAngular.InfinityConditionL M Q e ω (RI ω) 1) ∧
        ContinuousOn (fun p : ℝ × ℝ => RI p.1 p.2) ({ω : ℝ | ω ≠ 0} ×ˢ Ioi
          (ModeStability.outerHorizon M Q)) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (RI p.1) p.2)
          ({ω : ℝ | ω ≠ 0} ×ˢ Ioi (ModeStability.outerHorizon M Q)) := by
  exact ModeStability.AllAngular.infinity_solution_continuous_aux

end ModeStability.Provider.AllAngular

end
