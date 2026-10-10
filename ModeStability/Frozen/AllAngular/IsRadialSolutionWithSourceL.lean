module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK

/-!
# `ModeStability.AllAngular.IsRadialSolutionWithSourceL`

All-angular research notes in preparation, pp. 7–8, Proposition 6.1, (6.1)–(6.2); p. 10, R_H,
R_I normalized by (1.4)/(1.5) and their continuous dependence.
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

/-- The radial equation with a source, (6.1) in `r`: `(ΔR')' + (K²/Δ − L)R = S` on the exterior,
in integrated form (`S` locally integrable). -/
def IsRadialSolutionWithSourceL (M Q e ω L : ℝ) (R S : ℝ → ℂ) : Prop :=
  (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r) ∧
    ∀ ρ₁ ∈ Ioi (outerHorizon M Q), ∀ ρ₂ ∈ Ioi (outerHorizon M Q),
      IntervalIntegrable S volume ρ₁ ρ₂ ∧
        (delta M Q ρ₂ : ℂ) * deriv R ρ₂ - (delta M Q ρ₁ : ℂ) * deriv R ρ₁ =
          ∫ r in ρ₁..ρ₂, (S r - (((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r)

end ModeStability.AllAngular

end
