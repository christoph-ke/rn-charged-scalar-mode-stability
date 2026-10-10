module

public import Mathlib
public import ModeStability.Frozen.RadiusOf
public import ModeStability.Frozen.StaticSolution
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Provider.RadiusOfSpec

/-!
# `ModeStability.radiusOf_spec`

Spherical research notes in preparation, p. 2, (2.2) and the sentence after it; p. 3, (2.11).
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- Characterization of `radiusOf`: it maps `(0, ∞)` bijectively onto `(a, ∞)` and inverts
`x = 1/g(r)`. -/
theorem radiusOf_spec :
    ∀ (M Q : ℝ), 0 < M → |Q| < M →
      BijOn (radiusOf M Q) (Ioi 0) (Ioi (outerHorizon M Q)) ∧
        ∀ x ∈ Ioi (0 : ℝ), 1 / staticSolution M Q (radiusOf M Q x) = x :=
  by exact ModeStability.Provider.radiusOf_spec

end ModeStability

end
