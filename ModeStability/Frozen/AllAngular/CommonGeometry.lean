module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.AllAngular.StaticSolutionAA
public import ModeStability.Provider.AllAngular.CommonGeometry

/-!
# `ModeStability.AllAngular.common_geometry`

All-angular research notes in preparation, p. 3, Lemma 2.1, (2.8); notation (1.1), (2.1), (2.3),
(2.5) on pp. 1–2.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- **Lemma 2.1** (common geometry): for `ω > 0`, `r₀ = e/ω > a` and `r > a`, `T > δ|K|` with
`T = ΔK' − zK`, `z = r − M`; and with `χ = h⁻¹`, `ε = z − χ`: `0 ≤ ε ≤ δ`, `ε(δ + χ) ≤ δ²`,
`0 < χ ≤ z`, the first two upper bounds strict when `δ > 0`, and `ε = 0`, `χ = z` when `δ = 0`. -/
theorem common_geometry :
    ∀ (M Q e ω : ℝ), 0 < M → |Q| ≤ M → 0 < ω → ∀ (r₀ : ℝ), r₀ = e / ω →
      outerHorizon M Q < r₀ → ∀ r ∈ Ioi (outerHorizon M Q),
        Real.sqrt (M ^ 2 - Q ^ 2) * |radialK e ω r| <
            delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r ∧
          0 ≤ (r - M) - 1 / staticSolutionAA M Q r ∧
          (r - M) - 1 / staticSolutionAA M Q r ≤ Real.sqrt (M ^ 2 - Q ^ 2) ∧
          ((r - M) - 1 / staticSolutionAA M Q r) *
              (Real.sqrt (M ^ 2 - Q ^ 2) + 1 / staticSolutionAA M Q r) ≤ M ^ 2 - Q ^ 2 ∧
          0 < 1 / staticSolutionAA M Q r ∧ 1 / staticSolutionAA M Q r ≤ r - M ∧
          (0 < M ^ 2 - Q ^ 2 →
            (r - M) - 1 / staticSolutionAA M Q r < Real.sqrt (M ^ 2 - Q ^ 2) ∧
            ((r - M) - 1 / staticSolutionAA M Q r) *
              (Real.sqrt (M ^ 2 - Q ^ 2) + 1 / staticSolutionAA M Q r) < M ^ 2 - Q ^ 2) ∧
          (M ^ 2 - Q ^ 2 = 0 →
            (r - M) - 1 / staticSolutionAA M Q r = 0 ∧ 1 / staticSolutionAA M Q r = r - M) :=
  by exact ModeStability.Provider.AllAngular.common_geometry

end ModeStability.AllAngular

end
