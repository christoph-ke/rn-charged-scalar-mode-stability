module

public import Mathlib
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.RadiusOf
public import ModeStability.Frozen.TransformedK
public import ModeStability.Provider.ExactReduction

/-!
# `ModeStability.exact_reduction`

Spherical research notes in preparation, p. 2, Lemma 2.1, (2.3).
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- **Lemma 2.1, (2.3)** (exact reduction): `U(x) = x R(r(x))` solves `U_xx + k² U = 0`
on `x > 0`. -/
theorem exact_reduction :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M →
      ∀ (R : ℝ → ℂ), IsRadialSolution M Q q ω R →
        ∀ x ∈ Ioi (0 : ℝ),
          DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x ∧
            HasDerivAt (deriv fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))
              (-((transformedK M Q q ω x ^ 2 : ℝ) : ℂ) * ((x : ℂ) * R (radiusOf M Q x))) x :=
  by exact ModeStability.Provider.exact_reduction

end ModeStability

end
