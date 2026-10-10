module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.AllAngular.StaticSolutionAA
public import ModeStability.AllAngular.Geometry
public import ModeStability.AllAngular.NormalizationFacts

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.CommonGeometry` supplies the proof of the corresponding
source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Set

namespace ModeStability.Provider.AllAngular

theorem common_geometry :
    ∀ (M Q e ω : ℝ), 0 < M → |Q| ≤ M → 0 < ω → ∀ (r₀ : ℝ), r₀ = e / ω →
      ModeStability.outerHorizon M Q < r₀ → ∀ r ∈ Ioi (ModeStability.outerHorizon M Q),
        Real.sqrt (M ^ 2 - Q ^ 2) * |ModeStability.radialK e ω r| <
            ModeStability.delta M Q r * (2 * ω * r - e) -
              (r - M) * ModeStability.radialK e ω r ∧
          0 ≤ (r - M) - 1 / ModeStability.AllAngular.staticSolutionAA M Q r ∧
          (r - M) - 1 / ModeStability.AllAngular.staticSolutionAA M Q r ≤
            Real.sqrt (M ^ 2 - Q ^ 2) ∧
          ((r - M) - 1 / ModeStability.AllAngular.staticSolutionAA M Q r) *
              (Real.sqrt (M ^ 2 - Q ^ 2) +
                1 / ModeStability.AllAngular.staticSolutionAA M Q r) ≤ M ^ 2 - Q ^ 2 ∧
          0 < 1 / ModeStability.AllAngular.staticSolutionAA M Q r ∧
          1 / ModeStability.AllAngular.staticSolutionAA M Q r ≤ r - M ∧
          (0 < M ^ 2 - Q ^ 2 →
            (r - M) - 1 / ModeStability.AllAngular.staticSolutionAA M Q r <
              Real.sqrt (M ^ 2 - Q ^ 2) ∧
            ((r - M) - 1 / ModeStability.AllAngular.staticSolutionAA M Q r) *
              (Real.sqrt (M ^ 2 - Q ^ 2) +
                1 / ModeStability.AllAngular.staticSolutionAA M Q r) < M ^ 2 - Q ^ 2) ∧
          (M ^ 2 - Q ^ 2 = 0 →
            (r - M) - 1 / ModeStability.AllAngular.staticSolutionAA M Q r = 0 ∧
              1 / ModeStability.AllAngular.staticSolutionAA M Q r = r - M) := by
  intro M Q e ω hM hQ hω r₀ hr₀ ha r hr
  rw [mem_Ioi] at hr
  have he : ω * r₀ = e := by
    rw [hr₀]
    field_simp
  have hT := ModeStability.AllAngular.mul_abs_K_lt_T hM hQ hω ha hr
  rw [he] at hT
  refine ⟨hT, ?_⟩
  by_cases hδ : 0 < M ^ 2 - Q ^ 2
  · rw [ModeStability.AllAngular.NormalizationFacts.staticSolutionAA_eq_staticSolution hδ]
    obtain ⟨h1, h2, h3, h4, h5⟩ := ModeStability.AllAngular.chi_bounds
      (ModeStability.AllAngular.NormalizationFacts.abs_lt_of_sub_sq_pos hM hδ) hr
    exact ⟨h1.le, h2.le, h3.le, h4, h5.le, fun _ => ⟨h2, h3⟩, fun h => absurd h hδ.ne'⟩
  · obtain ⟨h0, hs, -, -⟩ := ModeStability.AllAngular.NormalizationFacts.extremal_facts hQ hδ
    have hχ : 1 / ModeStability.AllAngular.staticSolutionAA M Q r = r - M := by
      rw [ModeStability.AllAngular.NormalizationFacts.staticSolutionAA_eq_extremal hδ]
      exact one_div_one_div (r - M)
    rw [hχ, hs, h0, sub_self]
    exact ⟨le_rfl, le_rfl, (zero_mul _).le,
      ModeStability.AllAngular.NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr, le_rfl,
      fun h => absurd h (lt_irrefl 0), fun _ => ⟨rfl, rfl⟩⟩

end ModeStability.Provider.AllAngular

end
