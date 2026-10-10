module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityRSubReciprocalCoefficients
public import ModeStability.AllAngular.CoordinateCoefficientsExtremal

/-!
# Radial coefficients for the extremal constant source identity

Source: the all-angular research notes in preparation, identity (6.3),
and Proposition 3.1. The constant normalization is `g = 1`; the positive
radial derivative `xDeriv` is the negative of differentiation in the
reflected coordinate `y = 1/(r − M)`.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

open CoordinateCoefficients

/-- The exact frozen frequency is regular and its current coefficients are positive
on the allowed region in the extremal constant system. -/
theorem sec_coefficient_props {M Q e ω L r : ℝ}
    (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω) (hL : 0 ≤ L)
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
    intro hz
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hP
    exact (not_lt.mpr (mul_nonneg hL (delta_pos_of_lt hr).le)) hP
  refine ⟨contDiffAt_effectiveKAux contDiffAt_const hK0 (sub_pos.mpr hP), ?_⟩
  apply xDeriv_khat_pos (c := 0) (χ := 0) hM hQ.le hω hL ha hr one_pos hP
    (eventually_hasDerivAt_one M Q r) (by simp) le_rfl
    (sub_pos_of_outerHorizon_lt hr).le
  · simpa using hH
  · simpa using hA

/-- At zero angular potential the signed frequency is smooth through corotation. -/
theorem sec_coefficient_props_zero {M Q e ω r : ℝ}
    (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) (hN : e / ω < 2 * M)
    (hr : outerHorizon M Q < r) :
    ContDiffAt ℝ 2 (effectiveK M Q e ω 0) r ∧
      0 < xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0) r ∧
      0 < 2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0) r ^ 2 -
        effectiveK M Q e ω 0 r * xDeriv M Q (normalizationG M Q e ω)
          (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0)) r := by
  rw [source_effectiveK_zero, NormalizationFacts.normalizationG_eq_one hN]
  obtain ⟨hH, hA⟩ := scalar_positivity_constant hM hQ.le hω ha hN hr
  rw [mul_div_cancel₀ e hω.ne'] at hH hA
  refine ⟨contDiffAt_const.pow 2 |>.mul (contDiff_radialK e ω).contDiffAt, ?_⟩
  apply xDeriv_k_pos (c := 0) (χ := 0) hr one_pos
    (eventually_hasDerivAt_one M Q r) (by simp)
  · simpa using hH
  · simpa using hA

end ModeStability.AllAngular

end
