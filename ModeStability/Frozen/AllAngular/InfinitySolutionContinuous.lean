module

public import Mathlib
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL
public import ModeStability.Provider.AllAngular.InfinitySolutionContinuous

/-!
# `ModeStability.AllAngular.infinity_solution_continuous`

All-angular research notes in preparation, pp. 7–8, Proposition 6.1, (6.1)–(6.2); p. 10, R_H,
R_I normalized by (1.4)/(1.5) and their continuous dependence.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

/-- ω-continuity of the normalized outgoing solutions on `{ω ≠ 0} × (a, ∞)`. -/
theorem infinity_solution_continuous :
    ∀ (M Q e L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L →
      ∃ RI : ℝ → ℝ → ℂ,
        (∀ ω : ℝ, ω ≠ 0 →
          IsRadialSolutionL M Q e ω L (RI ω) ∧ InfinityConditionL M Q e ω (RI ω) 1) ∧
        ContinuousOn (fun p : ℝ × ℝ => RI p.1 p.2) ({ω : ℝ | ω ≠ 0} ×ˢ Ioi (outerHorizon M Q)) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (RI p.1) p.2)
          ({ω : ℝ | ω ≠ 0} ×ˢ Ioi (outerHorizon M Q)) :=
  by exact ModeStability.Provider.AllAngular.infinity_solution_continuous

end ModeStability.AllAngular

end
