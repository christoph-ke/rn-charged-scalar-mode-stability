module

public import Mathlib
public import ModeStability.Frozen.AllAngular.IsRadialSolutionWithSourceL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL
public import ModeStability.Provider.AllAngular.SourceSolutionExistsUnique

/-!
# `ModeStability.AllAngular.source_solution_existsUnique`

All-angular research notes in preparation, pp. 7–8, Proposition 6.1, (6.1)–(6.2); p. 10, R_H,
R_I normalized by (1.4)/(1.5) and their continuous dependence.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

/-- The Green-formula solution of (6.1) (p. 7.), in the strictly superradiant range
(1.7), for a source in `L²` supported in a compact `[ρ₁, ρ₂] ⊂ (a, ∞)`. -/
theorem source_solution_existsUnique :
    ∀ (M Q e ω L : ℝ), 0 < M → |Q| ≤ M → 0 < e → 0 < ω → ω < e / outerHorizon M Q → 0 ≤ L →
      ∀ (ρ₁ ρ₂ : ℝ), outerHorizon M Q < ρ₁ → ρ₁ < ρ₂ →
        ∀ S : ℝ → ℂ, (∀ r, r ∉ Icc ρ₁ ρ₂ → S r = 0) →
          MemLp S 2 (volume.restrict (Icc ρ₁ ρ₂)) →
            ∃! f : Ioi (outerHorizon M Q) → ℂ, ∃ (R : ℝ → ℂ) (BH BI : ℂ),
              (∀ r : Ioi (outerHorizon M Q), R r = f r) ∧
                IsRadialSolutionWithSourceL M Q e ω L R S ∧
                  HorizonConditionL M Q e ω R BH ∧ InfinityConditionL M Q e ω R BI :=
  by exact ModeStability.Provider.AllAngular.source_solution_existsUnique

end ModeStability.AllAngular

end
