module

public import Mathlib
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.AllAngular.SolutionContinuity

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.HorizonSolutionContinuous` supplies the proof of the
corresponding source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.Provider.AllAngular

/-- ω-continuity of the normalized ingoing solutions: for fixed `(M, Q, e, L)` there is a family
`RH ω` consisting, for every real `ω` with `K(a) ≠ 0`, of the normalized solution of
`horizon_solution_existsUnique` (unique on `(a, ∞)`), such that `(ω, r) ↦ R_H(ω, r)` and
`(ω, r) ↦ ∂_r R_H(ω, r)` are jointly continuous on `{K(a) ≠ 0} × (a, ∞)`. -/
theorem horizon_solution_continuous :
    ∀ (M Q e L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L →
      ∃ RH : ℝ → ℝ → ℂ,
        (∀ ω : ℝ, ModeStability.radialK e ω (ModeStability.outerHorizon M Q) ≠ 0 →
          ModeStability.AllAngular.IsRadialSolutionL M Q e ω L (RH ω) ∧
            ModeStability.AllAngular.HorizonConditionL M Q e ω (RH ω) 1) ∧
        ContinuousOn (fun p : ℝ × ℝ => RH p.1 p.2)
          ({ω | ModeStability.radialK e ω (ModeStability.outerHorizon M Q) ≠ 0} ×ˢ Ioi
            (ModeStability.outerHorizon M Q)) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (RH p.1) p.2)
          ({ω | ModeStability.radialK e ω (ModeStability.outerHorizon M Q) ≠ 0} ×ˢ Ioi
            (ModeStability.outerHorizon M Q)) := by
  exact ModeStability.AllAngular.horizon_solution_continuous_aux

end ModeStability.Provider.AllAngular

end
