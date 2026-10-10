module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.AllAngular.RadialPhase

/-!
# `ModeStability.AllAngular.HorizonConditionL`

All-angular research notes in preparation, p. 1, (1.4), the sentence after (1.5) and the last
paragraph of p. 1.
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- The future-horizon condition. If `K(a) ≠ 0` or the horizon is subextremal, this is (1.4):
`R = e^{−iΘ}(B + O(r − a))` as `r ↓ a` with differentiated remainder, i.e. `R̃ = e^{iΘ}R` has
`R̃ − B = O(r − a)` and `R̃' = O(1)`. (For a subextremal horizon with `K(a) = 0`, `Θ` is smooth at
`a` and this is the regular branch, as p. 1 requires.) At an extremal synchronized horizon
(`a = b`, `K(a) = 0`) the paper requires a bounded mode (p. 1), and `B` plays no role. -/
def HorizonConditionL (M Q e ω : ℝ) (R : ℝ → ℂ) (B : ℂ) : Prop :=
  if innerHorizon M Q = outerHorizon M Q ∧ radialK e ω (outerHorizon M Q) = 0 then
    (fun r => R r) =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))
  else
    (fun r : ℝ => exp (I * radialPhase M Q e ω r) * R r - B)
        =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) ∧
      deriv (fun r : ℝ => exp (I * radialPhase M Q e ω r) * R r)
        =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))

end ModeStability.AllAngular

end
