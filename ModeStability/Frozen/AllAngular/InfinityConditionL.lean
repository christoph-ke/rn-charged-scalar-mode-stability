module

public import Mathlib
public import ModeStability.Frozen.AllAngular.RadialPhase

/-!
# `ModeStability.AllAngular.InfinityConditionL`

All-angular research notes in preparation, p. 1, (1.5) and the sentence after it.
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- The outgoing infinity condition (1.5): `R = r⁻¹e^{iΘ}(B + O(r⁻¹))` as `r → ∞` with
differentiated remainder, i.e. `R̃ = r e^{−iΘ}R` has `R̃ − B = O(r⁻¹)` and `R̃' = O(r⁻²)`. -/
def InfinityConditionL (M Q e ω : ℝ) (R : ℝ → ℂ) (B : ℂ) : Prop :=
  (fun r : ℝ => (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * R r - B)
      =O[atTop] (fun r : ℝ => r⁻¹) ∧
    deriv (fun r : ℝ => (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)

end ModeStability.AllAngular

end
