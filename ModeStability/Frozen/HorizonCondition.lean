module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.RadialK

/-!
# `ModeStability.HorizonCondition`

Spherical research notes in preparation, p. 1, (1.3) and the paragraph after (1.4).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- The future-horizon ingoing condition (1.3) with leading coefficient `B`:
`R(r) = (r − a)^{−iK(a)/d} (B + O(r − a))` as `r ↓ a`, `d = a − b`, with the differentiated
remainder: after removing the oscillation, `R̃(r) = (r − a)^{iK(a)/d} R(r)` satisfies
`R̃ − B = O(r − a)` and `R̃' = O(1)` as `r ↓ a`. -/
def HorizonCondition (M Q q ω : ℝ) (R : ℝ → ℂ) (B : ℂ) : Prop :=
  (fun r : ℝ => ((r - outerHorizon M Q : ℝ) : ℂ) ^
        (I * ((radialK (q * Q) ω (outerHorizon M Q) /
          (outerHorizon M Q - innerHorizon M Q) : ℝ) : ℂ)) * R r - B)
      =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) ∧
    deriv (fun r : ℝ => ((r - outerHorizon M Q : ℝ) : ℂ) ^
        (I * ((radialK (q * Q) ω (outerHorizon M Q) /
          (outerHorizon M Q - innerHorizon M Q) : ℝ) : ℂ)) * R r)
      =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))

end ModeStability

end
