module

public import Mathlib
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL
public import ModeStability.AllAngular.InfinitySolution
public import ModeStability.AllAngular.MainAssembly

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.InfinitySolutionExistsUnique` supplies the proof of the
corresponding source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.Provider.AllAngular

/-- Well-definedness of the normalized outgoing solution `R_I` (infinity condition (1.5) with
leading coefficient `1`), at a real frequency `ω ≠ 0`. -/
theorem infinity_solution_existsUnique :
    ∀ (M Q e ω L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L → ω ≠ 0 →
      ∃! f : Ioi (ModeStability.outerHorizon M Q) → ℂ, ∃ R : ℝ → ℂ,
        (∀ r : Ioi (ModeStability.outerHorizon M Q), R r = f r) ∧
          ModeStability.AllAngular.IsRadialSolutionL M Q e ω L R ∧
            ModeStability.AllAngular.InfinityConditionL M Q e ω R 1 := by
  intro M Q e ω L hM hQ _ hω
  have hΘ : ∀ r ∈ Ioi (ModeStability.outerHorizon M Q),
      HasDerivAt (ModeStability.AllAngular.radialPhase M Q e ω)
        (ModeStability.radialK e ω r / ModeStability.delta M Q r) r :=
    fun r hr => ModeStability.AllAngular.hasDerivAt_integral_radialK_div_delta hr
  obtain ⟨R, hR, hI⟩ := ModeStability.AllAngular.exists_infinity_solution
    (L := L) hM hQ hω hΘ
  refine ⟨fun r => R r, ⟨R, fun _ => rfl, hR, hI⟩, ?_⟩
  rintro f ⟨R', hf, hR', hI'⟩
  funext r
  rw [← hf r]
  exact ModeStability.AllAngular.infinity_solution_unique hM hQ hω hΘ
    hR' hR hI'.1 hI'.2 hI.1 hI.2 r.property

end ModeStability.Provider.AllAngular

end
