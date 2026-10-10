module

public import Mathlib
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.Provider.AllAngular.HorizonSolutionContinuous

/-!
# `ModeStability.AllAngular.horizon_solution_continuous`

All-angular research notes in preparation, pp. 7–8, Proposition 6.1, (6.1)–(6.2); p. 10, R_H,
R_I normalized by (1.4)/(1.5) and their continuous dependence.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

/-- ω-continuity of the normalized ingoing solutions: for fixed `(M, Q, e, L)` there is a family
`RH ω` consisting, for every real `ω` with `K(a) ≠ 0`, of the normalized solution of
`horizon_solution_existsUnique` (unique on `(a, ∞)`), such that `(ω, r) ↦ R_H(ω, r)` and
`(ω, r) ↦ ∂_r R_H(ω, r)` are jointly continuous on `{K(a) ≠ 0} × (a, ∞)`. -/
theorem horizon_solution_continuous :
    ∀ (M Q e L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L →
      ∃ RH : ℝ → ℝ → ℂ,
        (∀ ω : ℝ, radialK e ω (outerHorizon M Q) ≠ 0 →
          IsRadialSolutionL M Q e ω L (RH ω) ∧ HorizonConditionL M Q e ω (RH ω) 1) ∧
        ContinuousOn (fun p : ℝ × ℝ => RH p.1 p.2)
          ({ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ Ioi (outerHorizon M Q)) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (RH p.1) p.2)
          ({ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ Ioi (outerHorizon M Q)) :=
  by exact ModeStability.Provider.AllAngular.horizon_solution_continuous

end ModeStability.AllAngular

end
