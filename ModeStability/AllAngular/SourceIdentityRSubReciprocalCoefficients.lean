module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityRSubReciprocalAux
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

private theorem sr_static_derivative_eventually {M Q r : ℝ} (hQ : |Q| < M)
    (hr : outerHorizon M Q < r) :
    ∀ᶠ s in 𝓝 r, HasDerivAt (staticSolution M Q) (-1 / delta M Q s) s := by
  filter_upwards [Ioi_mem_nhds hr] with s hs
  simpa only [neg_div, one_div] using hasDerivAt_staticSolution hQ hs

/-- On the allowed set the frozen signed frequency is `C²`, its `x` derivative
is positive, and its current coefficient numerator is positive. -/
theorem source_sub_reciprocal_coefficient_props {M Q e ω L r : ℝ}
    (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω) (hL : 0 ≤ L)
    (ha : outerHorizon M Q < e / ω) (hN : 2 * M ≤ e / ω)
    (hr : outerHorizon M Q < r) (hP : L * delta M Q r < radialK e ω r ^ 2) :
    ContDiffAt ℝ 2 (effectiveK M Q e ω L) r ∧
      0 < xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ∧
      0 < 2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2 -
        effectiveK M Q e ω L r * xDeriv M Q (normalizationG M Q e ω)
          (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) r := by
  rw [NormalizationFacts.effectiveK_eq_effectiveKAux,
    source_sub_reciprocal_normalization hQ hN]
  obtain ⟨h1, h2, h3, h4, h5⟩ := chi_bounds hQ hr
  obtain ⟨hH, hA⟩ := scalar_positivity_reciprocal hM hQ.le hω ha hN hr h4 h1.le h2.le h3.le
  rw [mul_div_cancel₀ e hω.ne'] at hH hA
  have hK0 : radialK e ω r ≠ 0 := by
    have hΔ := delta_pos hQ hr
    intro hz
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hP
    exact (not_lt.mpr (mul_nonneg hL hΔ.le)) hP
  refine ⟨contDiffAt_effectiveKAux (contDiffAt_staticSolution hQ hr) hK0 (sub_pos.mpr hP), ?_⟩
  exact xDeriv_khat_pos hM hQ.le hω hL ha hr (staticSolution_pos hQ hr) hP
    (sr_static_derivative_eventually hQ hr) (by rw [neg_neg]) h4.le h5.le hH hA

/-- For `L = 0` the frequency is the smooth signed function `g²K`, including
at corotation; this avoids differentiating `sqrt(K²)` at its zero. -/
theorem source_effectiveK_zero (M Q e ω : ℝ) :
    effectiveK M Q e ω 0 = fun r => normalizationG M Q e ω r ^ 2 * radialK e ω r := by
  funext r
  unfold effectiveK
  rw [mul_right_comm, sign_mul_sqrt_L0]
  ring

/-- The reciprocal coefficient properties extend through corotation for
`L = 0`, as required when the two turning points coincide. -/
theorem source_sub_reciprocal_coefficient_props_zero {M Q e ω r : ℝ}
    (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) (hN : 2 * M ≤ e / ω)
    (hr : outerHorizon M Q < r) :
    ContDiffAt ℝ 2 (effectiveK M Q e ω 0) r ∧
      0 < xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0) r ∧
      0 < 2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0) r ^ 2 -
        effectiveK M Q e ω 0 r * xDeriv M Q (normalizationG M Q e ω)
          (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0)) r := by
  rw [source_effectiveK_zero, source_sub_reciprocal_normalization hQ hN]
  obtain ⟨h1, h2, h3, h4, -⟩ := chi_bounds hQ hr
  obtain ⟨hH, hA⟩ := scalar_positivity_reciprocal hM hQ.le hω ha hN hr h4 h1.le h2.le h3.le
  rw [mul_div_cancel₀ e hω.ne'] at hH hA
  refine ⟨(contDiffAt_staticSolution hQ hr).pow 2 |>.mul
    (contDiff_radialK e ω).contDiffAt, ?_⟩
  exact xDeriv_k_pos hr (staticSolution_pos hQ hr)
    (sr_static_derivative_eventually hQ hr) (by rw [neg_neg]) hH hA

end ModeStability.AllAngular

end
