module

public import Mathlib
public import ModeStability.Frozen.AllAngular.IsRadialSolutionWithSourceL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL
public import ModeStability.AllAngular.GreenFormula

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.SourceSolutionExistsUnique` supplies the proof of the
corresponding source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.Provider.AllAngular

/-- The Green-formula solution of (6.1) (p. 7.), in the strictly superradiant range
(1.7), for a source in `L²` supported in a compact `[ρ₁, ρ₂] ⊂ (a, ∞)`. -/
theorem source_solution_existsUnique :
    ∀ (M Q e ω L : ℝ), 0 < M → |Q| ≤ M → 0 < e → 0 < ω → ω < e / ModeStability.outerHorizon M Q →
      0 ≤ L →
      ∀ (ρ₁ ρ₂ : ℝ), ModeStability.outerHorizon M Q < ρ₁ → ρ₁ < ρ₂ →
        ∀ S : ℝ → ℂ, (∀ r, r ∉ Icc ρ₁ ρ₂ → S r = 0) →
          MemLp S 2 (volume.restrict (Icc ρ₁ ρ₂)) →
            ∃! f : Ioi (ModeStability.outerHorizon M Q) → ℂ, ∃ (R : ℝ → ℂ) (BH BI : ℂ),
              (∀ r : Ioi (ModeStability.outerHorizon M Q), R r = f r) ∧
                ModeStability.AllAngular.IsRadialSolutionWithSourceL M Q e ω L R S ∧
                  ModeStability.AllAngular.HorizonConditionL M Q e ω R BH ∧
                    ModeStability.AllAngular.InfinityConditionL M Q e ω R BI := by
  intro M Q e ω L hM hQ he hω hωa hL ρ₁ ρ₂ hρ₁ hρ S hS0 hS
  exact ModeStability.AllAngular.existsUnique_source_solution hM hQ he hω hωa hL hρ₁ hρ hS0 hS

end ModeStability.Provider.AllAngular

end
