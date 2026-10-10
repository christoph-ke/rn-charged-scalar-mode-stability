module

public import Mathlib
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.AllAngular.HorizonSolution
public import ModeStability.AllAngular.MainAssembly

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.HorizonSolutionExistsUnique` supplies the proof of the
corresponding source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.Provider.AllAngular

/-- Well-definedness of the normalized ingoing solution `R_H` (horizon condition (1.4) with
leading coefficient `1`), at a non-synchronized horizon. -/
theorem horizon_solution_existsUnique :
    ∀ (M Q e ω L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L → ModeStability.radialK e ω
      (ModeStability.outerHorizon M Q) ≠ 0 →
      ∃! f : Ioi (ModeStability.outerHorizon M Q) → ℂ, ∃ R : ℝ → ℂ,
        (∀ r : Ioi (ModeStability.outerHorizon M Q), R r = f r) ∧
          ModeStability.AllAngular.IsRadialSolutionL M Q e ω L R ∧
            ModeStability.AllAngular.HorizonConditionL M Q e ω R 1 := by
  intro M Q e ω L hM hQ _ hK
  have hΘ : ∀ r ∈ Ioi (ModeStability.outerHorizon M Q),
      HasDerivAt (ModeStability.AllAngular.radialPhase M Q e ω)
        (ModeStability.radialK e ω r / ModeStability.delta M Q r) r :=
    fun r hr => ModeStability.AllAngular.hasDerivAt_integral_radialK_div_delta hr
  obtain ⟨R, hR, hu⟩ := ModeStability.AllAngular.existsUnique_horizon_solution
    (L := L) hM hQ hK hΘ
  have hH : ModeStability.AllAngular.HorizonConditionL M Q e ω R 1 := by
    simpa [ModeStability.AllAngular.HorizonConditionL, hK] using hR.2
  refine ⟨fun r => R r, ⟨R, fun _ => rfl, hR.1, hH⟩, ?_⟩
  rintro f ⟨R', hf, hODE, hH'⟩
  have hC := hH'
  simp only [ModeStability.AllAngular.HorizonConditionL, hK, and_false, ite_false] at hC
  funext r
  rw [← hf r]
  exact hu R' ⟨hODE, hC⟩ r.property

end ModeStability.Provider.AllAngular

end
