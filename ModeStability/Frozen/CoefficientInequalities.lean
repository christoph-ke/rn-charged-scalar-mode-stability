module

public import Mathlib
public import ModeStability.Frozen.TransformedK
public import ModeStability.Provider.CoefficientInequalities

/-!
# `ModeStability.coefficient_inequalities`

Spherical research notes in preparation, p. 2, Lemma 2.1, (2.4); Section 3, pp. 4–5.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- **Lemma 2.1, (2.4)** (coefficient inequalities, proved in Section 3), in band (1.6). -/
theorem coefficient_inequalities :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → 0 < ω →
      ∀ (r₀ : ℝ), r₀ = q * Q / ω → 2 * M < r₀ →
        ContDiffOn ℝ 2 (transformedK M Q q ω) (Ioi 0) ∧
          ∀ x ∈ Ioi (0 : ℝ), 0 < deriv (transformedK M Q q ω) x ∧
            0 < 2 * deriv (transformedK M Q q ω) x ^ 2 -
              transformedK M Q q ω x * deriv (deriv (transformedK M Q q ω)) x :=
  by exact ModeStability.Provider.coefficient_inequalities

end ModeStability

end
