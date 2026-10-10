module

public import Mathlib
public import ModeStability.Frozen.TransformedK
public import ModeStability.Section3.Representation
public import ModeStability.Section3.Inequalities

/-!
# Proof implementation

`ModeStability.Provider.CoefficientInequalities` supplies the proof of the corresponding
source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Provider

theorem coefficient_inequalities :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → 0 < ω →
      ∀ (r₀ : ℝ), r₀ = q * Q / ω → 2 * M < r₀ →
        ContDiffOn ℝ 2 (transformedK M Q q ω) (Ioi 0) ∧
          ∀ x ∈ Ioi (0 : ℝ), 0 < deriv (transformedK M Q q ω) x ∧
            0 < 2 * deriv (transformedK M Q q ω) x ^ 2 -
              transformedK M Q q ω x * deriv (deriv (transformedK M Q q ω)) x := by
  intro M Q q ω hM hQ hω r₀ hr₀ h2M
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = Real.sqrt (M ^ 2 - Q ^ 2) := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = (r₀ - 2 * M) / δ := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ, χ = (M / δ - 1) * (M / δ + 1 + ν) := ⟨_, rfl⟩
  have hδpos : 0 < δ := hδ ▸ Section3.sqrt_pos_of_abs_lt hQ
  have hνpos : 0 < ν := hν ▸ div_pos (sub_pos.2 h2M) hδpos
  have hμ : 1 ≤ M / δ := (one_le_div hδpos).2 (hδ ▸ Section3.sqrt_le_of_abs_lt hM)
  have hχnn : 0 ≤ χ := by
    rw [hχ]
    have h1 : 0 ≤ M / δ - 1 := sub_nonneg.2 hμ
    have h2 : 0 ≤ M / δ + 1 + ν := by linarith
    positivity
  exact Section3.coefficient_inequalities_of_eqOn hω hδpos hνpos hχnn
    (fun x hx => Section3.transformedK_eq hQ hω hr₀ hδ hν hχ hx)

end ModeStability.Provider

end
