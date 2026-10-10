module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtReciprocalAux
public import ModeStability.AllAngular.CoordinateCoefficients

/-!
# The reciprocal coefficients in the exact radial notation

Source: the all-angular research notes in preparation and (3.3).
These are regularity and positivity statements for the frozen `effectiveK`
and `xDeriv`, rather than for a separately defined coordinate coefficient.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

open CoordinateCoefficients

private theorem ser_static_derivative_eventually {M Q r : ℝ} (hQ : |Q| = M)
    (hr : outerHorizon M Q < r) :
    ∀ᶠ s in 𝓝 r, HasDerivAt (ser_g M) (-1 / delta M Q s) s := by
  filter_upwards [Ioi_mem_nhds hr] with s hs
  simpa only [neg_div, one_div] using ser_g_derivative hQ hs

/-- On the allowed set the frozen signed frequency is `C²`, its `x` derivative
is positive, and its current coefficient numerator is positive. -/
theorem ser_coefficient_props {M Q e ω L r : ℝ}
    (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω) (hL : 0 ≤ L)
    (ha : outerHorizon M Q < e / ω) (hN : 2 * M ≤ e / ω)
    (hr : outerHorizon M Q < r) (hP : L * delta M Q r < radialK e ω r ^ 2) :
    ContDiffAt ℝ 2 (effectiveK M Q e ω L) r ∧
      0 < xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ∧
      0 < 2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2 -
        effectiveK M Q e ω L r * xDeriv M Q (normalizationG M Q e ω)
          (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) r := by
  rw [NormalizationFacts.effectiveK_eq_effectiveKAux,
    ser_normalization hQ hN]
  have hz : r - M - (r - M) = 0 := sub_self _
  have hs : M ^ 2 - Q ^ 2 = 0 := by rw [← sq_abs Q, hQ, sub_self]
  have hx := NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr
  obtain ⟨hH, hA⟩ := scalar_positivity_reciprocal hM hQ.le hω ha hN hr hx
    (by rw [hz]) (by rw [hz]; exact Real.sqrt_nonneg _) (by rw [hz, zero_mul, hs])
  rw [mul_div_cancel₀ e hω.ne'] at hH hA
  have hK0 : radialK e ω r ≠ 0 := by
    have hΔ := delta_pos_of_lt hr
    intro hz
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hP
    exact (not_lt.mpr (mul_nonneg hL hΔ.le)) hP
  refine ⟨contDiffAt_effectiveKAux (ser_g_smooth hQ hr) hK0 (sub_pos.mpr hP), ?_⟩
  exact xDeriv_khat_pos (g := ser_g M) (χ := r - M) hM hQ.le hω hL ha hr (ser_g_pos hQ hr) hP
    (ser_static_derivative_eventually hQ hr)
    (by dsimp [ser_g]; rw [neg_neg, one_div_one_div]) hx.le le_rfl hH hA

/-- For `L = 0` the frequency is the smooth signed function `g²K`, including
at corotation; this avoids differentiating `sqrt(K²)` at its zero. -/
theorem ser_effectiveK_zero (M Q e ω : ℝ) :
    effectiveK M Q e ω 0 = fun r => normalizationG M Q e ω r ^ 2 * radialK e ω r := by
  funext r
  unfold effectiveK
  rw [mul_right_comm, sign_mul_sqrt_L0]
  ring

/-- The reciprocal coefficient properties extend through corotation for
`L = 0`, as required when the two turning points coincide. -/
theorem ser_coefficient_props_zero {M Q e ω r : ℝ}
    (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) (hN : 2 * M ≤ e / ω)
    (hr : outerHorizon M Q < r) :
    ContDiffAt ℝ 2 (effectiveK M Q e ω 0) r ∧
      0 < xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0) r ∧
      0 < 2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0) r ^ 2 -
        effectiveK M Q e ω 0 r * xDeriv M Q (normalizationG M Q e ω)
          (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0)) r := by
  rw [ser_effectiveK_zero, ser_normalization hQ hN]
  have hz : r - M - (r - M) = 0 := sub_self _
  have hs : M ^ 2 - Q ^ 2 = 0 := by rw [← sq_abs Q, hQ, sub_self]
  have hx := NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr
  obtain ⟨hH, hA⟩ := scalar_positivity_reciprocal hM hQ.le hω ha hN hr hx
    (by rw [hz]) (by rw [hz]; exact Real.sqrt_nonneg _) (by rw [hz, zero_mul, hs])
  rw [mul_div_cancel₀ e hω.ne'] at hH hA
  refine ⟨(ser_g_smooth hQ hr).pow 2 |>.mul
    (contDiff_radialK e ω).contDiffAt, ?_⟩
  exact xDeriv_k_pos (g := ser_g M) (χ := r - M) hr (ser_g_pos hQ hr)
    (ser_static_derivative_eventually hQ hr) (by dsimp [ser_g]; rw [neg_neg, one_div_one_div]) hH hA

/-- Squaring the signed effective frequency recovers the radial potential
on the allowed region. -/
theorem ser_effectiveK_sq {M Q e ω L r : ℝ} (hL : 0 ≤ L)
    (hr : outerHorizon M Q < r) (hP : L * delta M Q r < radialK e ω r ^ 2) :
    effectiveK M Q e ω L r ^ 2 = normalizationG M Q e ω r ^ 4 *
      (radialK e ω r ^ 2 - L * delta M Q r) := by
  have h0 : radialK e ω r = 0 → radialK e ω r ^ 2 - L * delta M Q r = 0 := by
    intro hz
    have hnn := mul_nonneg hL (delta_pos_of_lt hr).le
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hP
    exact False.elim ((not_lt.mpr hnn) hP)
  have hs := sq_sign_mul_sqrt (sub_pos.mpr hP).le h0
  unfold effectiveK
  calc
    _ = normalizationG M Q e ω r ^ 4 *
        ((SignType.sign (radialK e ω r) : ℝ) *
          Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r)) ^ 2 := by ring
    _ = _ := by rw [hs]

end ModeStability.AllAngular

end
