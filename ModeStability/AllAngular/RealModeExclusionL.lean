module

public import Mathlib
public import ModeStability.AllAngular.MainAssembly
import ModeStability.AllAngular.SuperradiantSubReciprocal
import ModeStability.AllAngular.SuperradiantSubConstant
import ModeStability.AllAngular.SuperradiantExtReciprocal
import ModeStability.AllAngular.SuperradiantExtConstant

/-!
# Theorem 1.1 of the all-angular paper (helper encoding), unconditional

Source: the all-angular research notes in preparation, Theorem 1.1 (p. 2) and its proof
(Sections 1–5). `superradiantExclusionL_proved` discharges the internal statement
`SuperradiantExclusionL` (ω > 0, K(a) < 0) by the case split of (2.2) (`a < r₀ < 2M`: constant
normalization; `r₀ ≥ 2M`: reciprocal normalization) and subextremal/extremal horizons.
Together with `MainAssembly` (flux band, extremal synchronized horizon, conjugation) this gives
Theorem 1.1 for all `L ≥ 0`, `|Q| ≤ M`, `ω ≠ 0`:

* `real_mode_exclusion_theta`: with any phase Θ, Θ' = K/Δ;
* `real_mode_exclusion_integralPhase`: with Θ = ∫_{a+1}^r K/Δ (the endpoint
  encodings unfold to this form definitionally).

These helpers provide the implementation used by the source-facing theorem anchors.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- The superradiant case of Theorem 1.1 (ω > 0, K(a) < 0), all `L ≥ 0`, `|Q| ≤ M`. -/
theorem superradiantExclusionL_proved : SuperradiantExclusionL := by
  intro M Q e ω L hM hQ hL hω hKa Θ hΘ R BH BI hR hH1 hH2 hI1 hI2
  rcases hQ.lt_or_eq with hQ' | hQ'
  · by_cases hN : e / ω < 2 * M
    · exact superradiant_sub_constant hM hQ' hL hω hKa hN hΘ hR hH1 hH2 hI1 hI2
    · exact superradiant_sub_reciprocal hM hQ' hL hω hKa (not_lt.mp hN) hΘ hR hH1 hH2 hI1 hI2
  · by_cases hN : e / ω < 2 * M
    · exact superradiant_ext_constant hM hQ' hL hω hKa hN hΘ hR hH1 hH2 hI1 hI2
    · exact superradiant_ext_reciprocal hM hQ' hL hω hKa (not_lt.mp hN) hΘ hR hH1 hH2 hI1 hI2

/-- **Theorem 1.1** (helper encoding, any phase Θ with Θ' = K/Δ). -/
theorem real_mode_exclusion_theta :
    ∀ M Q e ω L : ℝ, 0 < M → |Q| ≤ M → 0 ≤ L → ω ≠ 0 →
      ∀ (Θ : ℝ → ℝ),
        (∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r) →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ),
        (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
          HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
            (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) →
        (if innerHorizon M Q = outerHorizon M Q ∧ radialK e ω (outerHorizon M Q) = 0 then
          (fun r => R r) =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))
        else
          ((fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - BH)
              =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) ∧
            deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r)
              =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))) →
        ((fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - BI)
            =O[atTop] (fun r : ℝ => r⁻¹) ∧
          deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
            =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) →
        EqOn R 0 (Ioi (outerHorizon M Q)) :=
  real_mode_exclusion_theta_of_superradiant superradiantExclusionL_proved

/-- **Theorem 1.1** (helper encoding, Θ = ∫_{a+1}^r K/Δ). -/
theorem real_mode_exclusion_integralPhase :
    ∀ M Q e ω L : ℝ, 0 < M → |Q| ≤ M → 0 ≤ L → ω ≠ 0 →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ),
        (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
          HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
            (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) →
        (if innerHorizon M Q = outerHorizon M Q ∧ radialK e ω (outerHorizon M Q) = 0 then
          (fun r => R r) =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))
        else
          ((fun r : ℝ => exp (I * ((∫ ρ in (outerHorizon M Q + 1)..r,
                  radialK e ω ρ / delta M Q ρ : ℝ) : ℂ)) * R r - BH)
              =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) ∧
            deriv (fun r : ℝ => exp (I * ((∫ ρ in (outerHorizon M Q + 1)..r,
                  radialK e ω ρ / delta M Q ρ : ℝ) : ℂ)) * R r)
              =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))) →
        ((fun r : ℝ => (r : ℂ) * exp (-(I * ((∫ ρ in (outerHorizon M Q + 1)..r,
                radialK e ω ρ / delta M Q ρ : ℝ) : ℂ))) * R r - BI)
            =O[atTop] (fun r : ℝ => r⁻¹) ∧
          deriv (fun r : ℝ => (r : ℂ) * exp (-(I * ((∫ ρ in (outerHorizon M Q + 1)..r,
                radialK e ω ρ / delta M Q ρ : ℝ) : ℂ))) * R r)
            =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) →
        EqOn R 0 (Ioi (outerHorizon M Q)) :=
  real_mode_exclusion_integralPhase_of_superradiant superradiantExclusionL_proved

end ModeStability.AllAngular

end
