module

public import Mathlib
public import ModeStability.AllAngular.Prop61Interface
public import ModeStability.AllAngular.CoordinateCoefficientsAux
public import ModeStability.AllAngular.CoordinateCoefficients
public import ModeStability.AllAngular.NormalizationFacts

/-!
# The constant coefficients in the exact radial notation

Source: the all-angular research notes in preparation and (3.3), with `g = 1` and `x = −h`.
These are regularity and positivity statements for the frozen `effectiveK`
and `xDeriv`, rather than for a separately defined coordinate coefficient.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

open CoordinateCoefficients

/-- On the allowed set the frozen signed frequency is `C²`, its `x` derivative
is positive, and its current coefficient numerator is positive. -/
theorem ssc_coefficient_props {M Q e ω L r : ℝ}
    (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω) (hL : 0 ≤ L)
    (ha : outerHorizon M Q < e / ω) (hN : e / ω < 2 * M)
    (hr : outerHorizon M Q < r) (hP : L * delta M Q r < radialK e ω r ^ 2) :
    ContDiffAt ℝ 2 (effectiveK M Q e ω L) r ∧
      0 < xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ∧
      0 < 2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2 -
        effectiveK M Q e ω L r * xDeriv M Q (normalizationG M Q e ω)
          (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) r := by
  rw [NormalizationFacts.effectiveK_eq_effectiveKAux,
    NormalizationFacts.normalizationG_eq_one hN]
  obtain ⟨hH, hA⟩ := scalar_positivity_constant hM hQ.le hω ha hN hr
  rw [mul_div_cancel₀ e hω.ne'] at hH hA
  have hK0 : radialK e ω r ≠ 0 := by
    have hΔ := delta_pos hQ hr
    intro hz
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hP
    exact (not_lt.mpr (mul_nonneg hL hΔ.le)) hP
  refine ⟨contDiffAt_effectiveKAux contDiffAt_const hK0 (sub_pos.mpr hP), ?_⟩
  exact xDeriv_khat_pos (c := 0) (χ := 0) hM hQ.le hω hL ha hr one_pos hP
    (eventually_hasDerivAt_one M Q r) (by simp) le_rfl
      (sub_pos_of_outerHorizon_lt hr).le (by simpa using hH) (by simpa using hA)

/-- For `L = 0` the frequency is the smooth signed function `g²K`, including
at corotation; this avoids differentiating `sqrt(K²)` at its zero. -/
theorem ssc_effectiveK_zero (M Q e ω : ℝ) :
    effectiveK M Q e ω 0 = fun r => normalizationG M Q e ω r ^ 2 * radialK e ω r := by
  funext r
  unfold effectiveK
  rw [mul_right_comm, sign_mul_sqrt_L0]
  ring

/-- The constant coefficient properties extend through corotation for
`L = 0`, as required when the two turning points coincide. -/
theorem ssc_coefficient_props_zero {M Q e ω r : ℝ}
    (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) (hN : e / ω < 2 * M)
    (hr : outerHorizon M Q < r) :
    ContDiffAt ℝ 2 (effectiveK M Q e ω 0) r ∧
      0 < xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0) r ∧
      0 < 2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0) r ^ 2 -
        effectiveK M Q e ω 0 r * xDeriv M Q (normalizationG M Q e ω)
          (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0)) r := by
  rw [ssc_effectiveK_zero, NormalizationFacts.normalizationG_eq_one hN]
  obtain ⟨hH, hA⟩ := scalar_positivity_constant hM hQ.le hω ha hN hr
  rw [mul_div_cancel₀ e hω.ne'] at hH hA
  refine ⟨contDiffAt_const.pow 2 |>.mul
    (contDiff_radialK e ω).contDiffAt, ?_⟩
  exact xDeriv_k_pos (c := 0) (χ := 0) hr one_pos
    (eventually_hasDerivAt_one M Q r) (by simp) (by simpa using hH) (by simpa using hA)

end ModeStability.AllAngular

end
