module

public import Mathlib
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL
public import ModeStability.Provider.AllAngular.InfinitySolutionExistsUnique

/-!
# `ModeStability.AllAngular.infinity_solution_existsUnique`

All-angular research notes in preparation, pp. 7–8, Proposition 6.1, (6.1)–(6.2); p. 10, R_H,
R_I normalized by (1.4)/(1.5) and their continuous dependence.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

/-- Well-definedness of the normalized outgoing solution `R_I` (infinity condition (1.5) with
leading coefficient `1`), at a real frequency `ω ≠ 0`. -/
theorem infinity_solution_existsUnique :
    ∀ (M Q e ω L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L → ω ≠ 0 →
      ∃! f : Ioi (outerHorizon M Q) → ℂ, ∃ R : ℝ → ℂ,
        (∀ r : Ioi (outerHorizon M Q), R r = f r) ∧
          IsRadialSolutionL M Q e ω L R ∧ InfinityConditionL M Q e ω R 1 :=
  by exact ModeStability.Provider.AllAngular.infinity_solution_existsUnique

end ModeStability.AllAngular

end
