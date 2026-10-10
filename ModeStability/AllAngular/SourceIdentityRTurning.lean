module

public import Mathlib
public import ModeStability.AllAngular.TurningPoint

/-!
# Turning-point currents for an absolutely continuous source reduction

Source: the all-angular research notes in preparation and (4.6).
The source flux `Ux` is continuous, although its derivative exists only
almost everywhere. Turning-point matching needs just this continuity and
the coefficient ratio limit, rather than a pointwise second derivative of U.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

private theorem sr_current_limit_of_ratio {f fx : ℝ → ℝ} {U V : ℝ → ℂ}
    {l : Filter ℝ} {rj σ : ℝ} (hl : l ≤ 𝓝 rj)
    (hγ : Tendsto (fun r => f r / fx r) l (𝓝 0))
    (hf : ContinuousAt f rj) (hU : ContinuousAt U rj) (hV : ContinuousAt V rj) :
    Tendsto (fun r => -(f r / fx r) * ‖V r + σ * f r * I * U r‖ ^ 2 -
      (V r * (starRingEnd ℂ) (U r)).re)
      l (𝓝 (-(V rj * (starRingEnd ℂ) (U rj)).re)) := by
  have hft := hf.tendsto.mono_left hl
  have hUt := hU.tendsto.mono_left hl
  have hVt := hV.tendsto.mono_left hl
  have hn := (hVt.add (((hft.ofReal.const_mul (σ : ℂ)).mul_const I).mul hUt)).norm.pow 2
  have hp := continuous_re.tendsto (V rj * (starRingEnd ℂ) (U rj)) |>.comp
    (hVt.mul ((continuous_star.tendsto (U rj)).comp hUt))
  have ht := (hγ.neg.mul hn).sub hp
  simpa only [neg_zero, zero_mul, zero_sub, Function.comp_apply, starRingEnd_apply] using ht

/-- Current matching at a left simple turning point, with `V = Ux`
independent of `deriv U`. The positive coordinate density is `d = Δg²`.
Only continuity of the source flux is required. -/
theorem source_radial_turning_current_left {F d : ℝ → ℝ} {rj s σ : ℝ}
    (hs : s = 1 ∨ s = -1) (hF : ContDiffAt ℝ 2 F rj)
    (hF0 : F rj = 0) (hF1 : deriv F rj < 0)
    (hd : ContinuousAt d rj) (hd0 : d rj ≠ 0)
    {U V : ℝ → ℂ} (hU : ContinuousAt U rj) (hV : ContinuousAt V rj) :
    let f : ℝ → ℝ := fun r => s * Real.sqrt (F r)
    Tendsto (fun r => -(f r / (d r * deriv f r)) * ‖V r + σ * f r * I * U r‖ ^ 2 -
      (V r * (starRingEnd ℂ) (U r)).re)
      (𝓝[<] rj) (𝓝 (-(V rj * (starRingEnd ℂ) (U rj)).re)) := by
  have hγ := (tendsto_khat_div_deriv_left hs hF hF0 hF1).div
    (hd.tendsto.mono_left nhdsWithin_le_nhds) hd0
  simp only [zero_div] at hγ
  apply sr_current_limit_of_ratio nhdsWithin_le_nhds (hγ.congr fun r => ?_)
    (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp hF.continuousAt)) hU hV
  simp only [div_eq_mul_inv, mul_inv_rev, Pi.mul_apply, Pi.inv_apply, Function.comp_apply]
  ring

/-- The right simple turning point has the same matching value. -/
theorem source_radial_turning_current_right {F d : ℝ → ℝ} {rj s σ : ℝ}
    (hs : s = 1 ∨ s = -1) (hF : ContDiffAt ℝ 2 F rj)
    (hF0 : F rj = 0) (hF1 : 0 < deriv F rj)
    (hd : ContinuousAt d rj) (hd0 : d rj ≠ 0)
    {U V : ℝ → ℂ} (hU : ContinuousAt U rj) (hV : ContinuousAt V rj) :
    let f : ℝ → ℝ := fun r => s * Real.sqrt (F r)
    Tendsto (fun r => -(f r / (d r * deriv f r)) * ‖V r + σ * f r * I * U r‖ ^ 2 -
      (V r * (starRingEnd ℂ) (U r)).re)
      (𝓝[>] rj) (𝓝 (-(V rj * (starRingEnd ℂ) (U rj)).re)) := by
  have hγ := (tendsto_khat_div_deriv_right hs hF hF0 hF1).div
    (hd.tendsto.mono_left nhdsWithin_le_nhds) hd0
  simp only [zero_div] at hγ
  apply sr_current_limit_of_ratio nhdsWithin_le_nhds (hγ.congr fun r => ?_)
    (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp hF.continuousAt)) hU hV
  simp only [div_eq_mul_inv, mul_inv_rev, Pi.mul_apply, Pi.inv_apply, Function.comp_apply]
  ring

end ModeStability.AllAngular

end
