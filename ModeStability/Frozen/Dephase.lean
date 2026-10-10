module

public import Mathlib

/-!
# `ModeStability.dephase`

Spherical research notes in preparation, p. 2, (2.5).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- The dephased function `v = e^{iσϑ} U` of (2.5), with phase `ϑ(x) = ∫_{x₀}^x k(ξ) dξ`;
`σ = ±1` selects `v_±`. -/
noncomputable def dephase (k : ℝ → ℝ) (x₀ σ : ℝ) (U : ℝ → ℂ) (x : ℝ) : ℂ :=
  exp (σ * (∫ ξ in x₀..x, k ξ) * I) * U x

end ModeStability

end
