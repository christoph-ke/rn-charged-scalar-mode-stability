module

public import Mathlib

/-!
# `ModeStability.InfinityCondition`

Spherical research notes in preparation, p. 1, (1.4) and the paragraph after it.
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- The future-null-infinity outgoing condition (1.4) with leading coefficient `B`:
`R(r) = r⁻¹ e^{iωr} r^{i(2Mω − e)} (B + O(r⁻¹))` as `r → ∞`, `e = q Q`, with the
differentiated remainder: `R̃(r) = r e^{−iωr} r^{−i(2Mω − e)} R(r)` satisfies
`R̃ − B = O(r⁻¹)` and `R̃' = O(r⁻²)`. -/
def InfinityCondition (M Q q ω : ℝ) (R : ℝ → ℂ) (B : ℂ) : Prop :=
  (fun r : ℝ => (r : ℂ) * exp (-(I * ω * r)) * (r : ℂ) ^ (-(I * (2 * M * ω - q * Q))) * R r - B)
      =O[atTop] (fun r : ℝ => r⁻¹) ∧
    deriv (fun r : ℝ => (r : ℂ) * exp (-(I * ω * r)) * (r : ℂ) ^ (-(I * (2 * M * ω - q * Q))) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)

end ModeStability

end
