module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
import ModeStability.AllAngular.ZeroFrequencyNeutral
import ModeStability.AllAngular.ZeroFrequencyInfinity
import ModeStability.AllAngular.HorizonUniqueness
import ModeStability.AllAngular.MainAssembly

/-!
# Proposition 7.1: zero frequency in the finite-energy class

Source: the all-angular research notes in preparation, p. 9, Proposition 7.1. Let `M > 0`, `|Q|
≤ M`, `e ∈ ℝ`, `L ≥ 0`. A
solution of (1.2) with `ω = 0`, satisfying the ingoing future-horizon condition when `e ≠ 0` and
the regular horizon condition when `e = 0`, vanishes identically if `∫_a^∞ |R|² dr < ∞` (7.1).

The horizon condition is the one of (1.4) with the phase `Θ(r) = ∫_{a+1}^r K/Δ` of (1.3), where
`K = −er` at `ω = 0`: `e^{iΘ}R − B = O(r − a)`, `(e^{iΘ}R)' = O(1)` as `r ↓ a`, except at an
extremal synchronized horizon (`b = a`, `K(a) = 0`), where a bounded mode is required (p. 1).
For `e ≠ 0` this is the ingoing condition (`K(a) = −ea ≠ 0`); for `e = 0` we have `Θ ≡ 0`, so it
is
the regular condition `R − B = O(r − a)`, `R' = O(1)` at a subextremal horizon and the
bounded-mode
condition at an extremal one.

* `zero_frequency_exclusion_integralPhase`: Proposition 7.1, first sentence.

The proof assembles landed pieces. For `e ≠ 0`, `zero_frequency_charged` (the flux of an `L²`
solution vanishes, while it tends to `e a ‖B‖²` at the horizon) gives `B = 0`, and then
`eqOn_zero_of_horizon_coefficient_zero` (uniqueness at the horizon, `K(a) ≠ 0`) gives `R = 0`.
For `e = 0`, `zero_frequency_neutral_of_radial` (regular horizon) resp.
`zero_frequency_neutral_extremal_of_radial` (bounded mode, `|Q| = M`) gives `R = 0`.

The clause of Proposition 7.1 on Gajic's weighted energy `𝓔_p` is not encoded.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

private theorem zx_outerHorizon_pos {M Q : ℝ} (hM : 0 < M) : 0 < outerHorizon M Q := by
  unfold outerHorizon
  have := Real.sqrt_nonneg (M ^ 2 - Q ^ 2)
  linarith

/-- Coincident horizons `b = a` force `|Q| = M` (given `|Q| ≤ M`). -/
private theorem zx_abs_eq_of_innerHorizon_eq {M Q : ℝ} (hQ : |Q| ≤ M)
    (h : innerHorizon M Q = outerHorizon M Q) : |Q| = M := by
  unfold innerHorizon outerHorizon at h
  have hs : Real.sqrt (M ^ 2 - Q ^ 2) = 0 := by linarith
  have h0 : M ^ 2 - Q ^ 2 ≤ 0 := Real.sqrt_eq_zero'.1 hs
  have hM0 : 0 ≤ M := (abs_nonneg Q).trans hQ
  refine le_antisymm hQ ((sq_le_sq₀ hM0 (abs_nonneg Q)).1 ?_)
  rw [sq_abs]
  linarith

private theorem zx_radialK_zero (r : ℝ) : radialK 0 0 r = 0 := by
  unfold radialK
  ring

/-- **Proposition 7.1** (p. 9), first sentence, with the phase `Θ(r) = ∫_{a+1}^r K/Δ` of (1.3):
for `M > 0`, `|Q| ≤ M`, real `e` and `L ≥ 0`, a solution of the radial equation (1.2) at `ω = 0`
on `r > a` with the horizon condition (1.4) (bounded mode at an extremal synchronized horizon)
and `∫_a^∞ |R|² dr < ∞` (7.1) vanishes on `r > a`. -/
theorem zero_frequency_exclusion_integralPhase :
    ∀ (M Q e L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L →
      ∀ (R : ℝ → ℂ) (BH : ℂ),
        (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
          HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
            (-(((radialK e 0 r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) →
        (if innerHorizon M Q = outerHorizon M Q ∧ radialK e 0 (outerHorizon M Q) = 0 then
            (fun r => R r) =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))
          else
            (fun r : ℝ => exp (I * ((∫ ρ in (outerHorizon M Q + 1)..r,
                radialK e 0 ρ / delta M Q ρ : ℝ) : ℂ)) * R r - BH)
                =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) ∧
              deriv (fun r : ℝ => exp (I * ((∫ ρ in (outerHorizon M Q + 1)..r,
                  radialK e 0 ρ / delta M Q ρ : ℝ) : ℂ)) * R r)
                =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))) →
        IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi (outerHorizon M Q)) →
          EqOn R 0 (Ioi (outerHorizon M Q)) := by
  intro M Q e L hM hQ hL R BH hR hH hint
  have ha := zx_outerHorizon_pos (Q := Q) hM
  by_cases he : e = 0
  · subst he
    by_cases hb : innerHorizon M Q = outerHorizon M Q
    · rw [ite_eq_left ⟨hb, zx_radialK_zero _⟩] at hH
      exact zero_frequency_neutral_extremal_of_radial hM (zx_abs_eq_of_innerHorizon_eq hQ hb) hL
        hR hH hint
    · rw [ite_eq_right (fun h => hb h.1)] at hH
      have hΘ0 : ∀ r : ℝ,
          (∫ ρ in (outerHorizon M Q + 1)..r, radialK 0 0 ρ / delta M Q ρ) = 0 := by
        intro r
        simp only [zx_radialK_zero, zero_div, intervalIntegral.integral_zero]
      simp only [hΘ0, ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hH
      exact zero_frequency_neutral_of_radial hM hQ hL hR hH.1 hH.2 hint
  · have hKa : radialK e 0 (outerHorizon M Q) ≠ 0 := by
      have hK : radialK e 0 (outerHorizon M Q) = -(e * outerHorizon M Q) := by
        unfold radialK
        ring
      rw [hK, neg_ne_zero]
      exact mul_ne_zero he ha.ne'
    rw [ite_eq_right (fun h => hKa h.2)] at hH
    have hΘ : ∀ r ∈ Ioi (outerHorizon M Q),
        HasDerivAt (fun r => ∫ ρ in (outerHorizon M Q + 1)..r, radialK e 0 ρ / delta M Q ρ)
          (radialK e 0 r / delta M Q r) r :=
      fun _ hr => hasDerivAt_integral_radialK_div_delta hr
    have hB : BH = 0 := zero_frequency_charged hM he hΘ hR hH.1 hH.2 hint
    subst hB
    refine eqOn_zero_of_horizon_coefficient_zero hM hQ hKa hΘ hR ?_ hH.2
    simpa only [sub_zero] using hH.1

end ModeStability.AllAngular

end
