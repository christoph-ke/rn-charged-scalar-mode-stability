module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.AllAngular.NormalizationG
public import ModeStability.Frozen.AllAngular.XDeriv
public import ModeStability.Frozen.AllAngular.EffectiveK
public import ModeStability.Provider.AllAngular.AngularPositivity

/-!
# `ModeStability.AllAngular.angular_positivity`

All-angular research notes in preparation, p. 4, (3.2), Proposition 3.1, (3.3)–(3.4).
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- **Proposition 3.1** (positivity survives the angular barrier): on the allowed set
`K² > LΔ`, `k̂_x > 0`, `E_k̂ = 2k̂_x² − k̂k̂_xx > 0`, and `E_k̂/k̂_x² ≥ min{E_k/k_x², 2}`. -/
theorem angular_positivity :
    ∀ (M Q e ω L : ℝ), 0 < M → |Q| ≤ M → 0 < ω → 0 ≤ L → ∀ (r₀ : ℝ), r₀ = e / ω →
      outerHorizon M Q < r₀ → ∀ r ∈ Ioi (outerHorizon M Q), L * delta M Q r < radialK e ω r ^ 2 →
        0 < xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ∧
          0 < 2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2 -
              effectiveK M Q e ω L r *
                xDeriv M Q (normalizationG M Q e ω)
                  (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) r ∧
          min ((2 * xDeriv M Q (normalizationG M Q e ω)
                  (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s) r ^ 2 -
                normalizationG M Q e ω r ^ 2 * radialK e ω r *
                  xDeriv M Q (normalizationG M Q e ω)
                    (xDeriv M Q (normalizationG M Q e ω)
                      (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s)) r) /
                xDeriv M Q (normalizationG M Q e ω)
                  (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s) r ^ 2) 2 ≤
            (2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2 -
                effectiveK M Q e ω L r *
                  xDeriv M Q (normalizationG M Q e ω)
                    (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) r) /
              xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2 :=
  by exact ModeStability.Provider.AllAngular.angular_positivity

end ModeStability.AllAngular

end
