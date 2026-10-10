module

public import ModeStability.Exterior.Basic

/-!
# Proof implementation

`ModeStability.Provider.RadiusOfSpec` supplies the proof of the corresponding source-facing
theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Set

namespace ModeStability.Provider

theorem radiusOf_spec :
    ∀ (M Q : ℝ), 0 < M → |Q| < M →
      BijOn (radiusOf M Q) (Ioi 0) (Ioi (outerHorizon M Q)) ∧
        ∀ x ∈ Ioi (0 : ℝ), 1 / staticSolution M Q (radiusOf M Q x) = x := by
  intro M Q _ hQ
  have hinv : ∀ x ∈ Ioi (0 : ℝ), 1 / staticSolution M Q (radiusOf M Q x) = x := by
    intro x hx
    rw [staticSolution_radiusOf hQ hx]
    simp
  refine ⟨⟨fun x hx => outerHorizon_lt_radiusOf hQ hx, ?_, ?_⟩, hinv⟩
  · intro x hx y hy hxy
    rw [← hinv x hx, ← hinv y hy, hxy]
  · intro r hr
    exact ⟨1 / staticSolution M Q r, one_div_pos.2 (staticSolution_pos hQ hr),
      radiusOf_one_div_staticSolution hQ hr⟩

end ModeStability.Provider

end
