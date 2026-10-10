module

public import Mathlib
public import ModeStability.Frozen.Dephase
public import ModeStability.Frozen.DephasedCurrent
public import ModeStability.Provider.DephasedCurrentLemma

/-!
# `ModeStability.dephased_current`

Spherical research notes in preparation, p. 2, Lemma 2.2, (2.5)–(2.8).
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- **Lemma 2.2** (dephased current): (2.7) on `x > 0` and (2.8) at `x₀`. -/
theorem dephased_current :
    ∀ (k : ℝ → ℝ) (U : ℝ → ℂ) (x₀ : ℝ), 0 < x₀ →
      ContDiffOn ℝ 2 k (Ioi 0) → (∀ x ∈ Ioi (0 : ℝ), 0 < deriv k x) →
      (∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
        HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x) →
      k x₀ = 0 → ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
        (∀ x ∈ Ioi (0 : ℝ), HasDerivAt (dephasedCurrent k (dephase k x₀ σ U))
            (-((2 * deriv k x ^ 2 - k x * deriv (deriv k) x) / deriv k x ^ 2) *
              ‖deriv (dephase k x₀ σ U) x‖ ^ 2) x) ∧
          dephasedCurrent k (dephase k x₀ σ U) x₀ =
            -(deriv U x₀ * (starRingEnd ℂ) (U x₀)).re :=
  by exact ModeStability.Provider.dephased_current

end ModeStability

end
