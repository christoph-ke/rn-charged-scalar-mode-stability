module

public import ModeStability.Corotation.Assembly
public import ModeStability.Endpoint.Horizon
public import ModeStability.Endpoint.Infinity

/-!
# Proof implementation

`ModeStability.Provider.SeparationAtCorotation` supplies the proof of the corresponding
source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Provider

theorem separation_at_corotation :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → 0 < ω →
      ∀ (r₀ : ℝ), r₀ = q * Q / ω → 2 * M < r₀ →
        ∀ (RH RI : ℝ → ℂ) (BH BI : ℂ),
          IsRadialSolution M Q q ω RH → HorizonCondition M Q q ω RH BH →
          ¬ EqOn RH 0 (Ioi (outerHorizon M Q)) →
          IsRadialSolution M Q q ω RI → InfinityCondition M Q q ω RI BI →
          ¬ EqOn RI 0 (Ioi (outerHorizon M Q)) →
            RH r₀ ≠ 0 ∧ RI r₀ ≠ 0 ∧
              -1 / (delta M Q r₀ * staticSolution M Q r₀) < (deriv RH r₀ / RH r₀).re ∧
              (deriv RI r₀ / RI r₀).re < -1 / (delta M Q r₀ * staticSolution M Q r₀) ∧
              delta M Q r₀ * (RH r₀ * deriv RI r₀ - deriv RH r₀ * RI r₀) ≠ 0 := by
  intro M Q q ω hM hQ hω r₀ hr₀ hband RH RI BH BI hRH hH hRH0 hRI hI hRI0
  have hKa : radialK (q * Q) ω (outerHorizon M Q) ≠ 0 :=
    (radialK_outerHorizon_neg hM hω hr₀ hband).ne
  have hc : 2 * M * ω - q * Q ≠ 0 := (two_mul_sub_neg_of_band hω hr₀ hband).ne
  have hx₀ : 0 < 1 / staticSolution M Q r₀ := (corotation_point hM hQ hω hr₀ hband).1
  exact Corotation.separation_at_corotation_of_limits M Q q ω hM hQ hω r₀ hr₀ hband RH RI BH BI
    hRH hH hRH0 hRI hI hRI0 (Endpoint.horizon_current_tendsto hM hQ hKa hx₀ hRH hH)
    (Endpoint.infinity_current_tendsto hM hQ hc hx₀ hRI hI)

end ModeStability.Provider

end
