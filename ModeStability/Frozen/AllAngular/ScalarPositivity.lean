module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.AllAngular.StaticSolutionAA
public import ModeStability.Frozen.AllAngular.NormalizationG
public import ModeStability.Frozen.AllAngular.XDeriv
public import ModeStability.Provider.AllAngular.ScalarPositivity

/-!
# `ModeStability.AllAngular.scalar_positivity`

All-angular research notes in preparation, p. 3, Lemma 2.2; (2.2), (2.3), (2.5)–(2.7) on p. 2.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- **Lemma 2.2** (scalar positivity): for the frequency-dependent choice (2.2) (`χ = 0` if
`r₀ < 2M`, `χ = h⁻¹` if `r₀ ≥ 2M`), `H = ΔK' − 2χK > 0` and
`A₀ = 2Δ²K'² − 2Δ(χ + z)KK' − Δ²KK'' + 2χ²K² > 0` on the exterior; in particular, with
`k = g²K`, `k_x > 0` and `E_k = 2k_x² − k k_xx > 0`. -/
theorem scalar_positivity :
    ∀ (M Q e ω : ℝ), 0 < M → |Q| ≤ M → 0 < ω → ∀ (r₀ : ℝ), r₀ = e / ω →
      outerHorizon M Q < r₀ → ∀ r ∈ Ioi (outerHorizon M Q),
        0 < delta M Q r * (2 * ω * r - e) -
            2 * (if r₀ < 2 * M then 0 else 1 / staticSolutionAA M Q r) * radialK e ω r ∧
          0 < 2 * delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
            2 * delta M Q r * ((if r₀ < 2 * M then 0 else 1 / staticSolutionAA M Q r) + (r - M)) *
              radialK e ω r * (2 * ω * r - e) -
            delta M Q r ^ 2 * radialK e ω r * (2 * ω) +
            2 * (if r₀ < 2 * M then 0 else 1 / staticSolutionAA M Q r) ^ 2 * radialK e ω r ^ 2 ∧
          0 < xDeriv M Q (normalizationG M Q e ω)
              (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s) r ∧
          0 < 2 * xDeriv M Q (normalizationG M Q e ω)
                (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s) r ^ 2 -
              normalizationG M Q e ω r ^ 2 * radialK e ω r *
                xDeriv M Q (normalizationG M Q e ω)
                  (xDeriv M Q (normalizationG M Q e ω)
                    (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s)) r :=
  by exact ModeStability.Provider.AllAngular.scalar_positivity

end ModeStability.AllAngular

end
