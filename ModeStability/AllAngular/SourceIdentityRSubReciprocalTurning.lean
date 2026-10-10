module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityRTurning
public import ModeStability.AllAngular.SourceIdentityRSubReciprocalCoefficients

/-!
# Radial turning-point matching in the subextremal reciprocal system

Source: the all-angular research notes in preparation and (4.6).
The effective potential is `g⁴(K² − LΔ)`. Its simple radial zeros give the
same matching currents with `khx = xDeriv kh`; only continuity of U and Ux
is used, so the statement applies to the rough-source Green reduction.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

open CoordinateCoefficients CoefficientIdentities

private theorem sr_potential_data {M Q e ω L rj : ℝ}
    (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) (hr : outerHorizon M Q < rj)
    (hP0 : radialK e ω rj ^ 2 - L * delta M Q rj = 0) :
    let g := normalizationG M Q e ω
    let F := fun r => g r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r)
    ContDiffAt ℝ 2 F rj ∧ F rj = 0 ∧
      deriv F rj = g rj ^ 4 *
        (2 * radialK e ω rj * (2 * ω * rj - e) - L * (2 * (rj - M))) := by
  rw [source_sub_reciprocal_normalization hQ hN]
  dsimp only
  have hg := contDiffAt_staticSolution hQ hr
  have hP : ContDiffAt ℝ 2 (fun r => radialK e ω r ^ 2 - L * delta M Q r) rj :=
    ((contDiff_radialK e ω).contDiffAt.pow 2).sub
      (contDiffAt_const.mul (contDiff_delta M Q).contDiffAt)
  refine ⟨(hg.pow 4).mul hP, by rw [hP0, mul_zero], ?_⟩
  rw [(((hasDerivAt_staticSolution hQ hr).fun_pow 4).fun_mul
    (hasDerivAt_radicand M Q e ω L rj)).deriv, hP0, mul_zero, zero_add]

private theorem sr_effective_sqrt {M Q e ω L r : ℝ} {s : ℝ}
    (hg : 0 ≤ normalizationG M Q e ω r)
    (hs : (SignType.sign (radialK e ω r) : ℝ) = s) :
    effectiveK M Q e ω L r = s *
      Real.sqrt (normalizationG M Q e ω r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r)) := by
  unfold effectiveK
  rw [hs, Real.sqrt_mul (pow_nonneg hg 4),
    show normalizationG M Q e ω r ^ 4 = (normalizationG M Q e ω r ^ 2) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
  ring

private theorem sr_density_continuous {M Q e ω rj : ℝ}
    (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) (hr : outerHorizon M Q < rj) :
    ContinuousAt (fun r => delta M Q r * normalizationG M Q e ω r ^ 2) rj ∧
      delta M Q rj * normalizationG M Q e ω rj ^ 2 ≠ 0 := by
  rw [source_sub_reciprocal_normalization hQ hN]
  exact ⟨((contDiff_delta M Q).contDiffAt.mul
    ((contDiffAt_staticSolution hQ hr).pow 2)).continuousAt,
    (mul_pos (delta_pos hQ hr) (sq_pos_of_pos (staticSolution_pos hQ hr))).ne'⟩

/-- The exact radial allowed current matches `−Re(Ux conj U)` at the
horizon-side simple turning point for a continuous source flux. -/
theorem source_sub_reciprocal_turning_current_left {M Q e ω L rj σ : ℝ}
    (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) (hr : outerHorizon M Q < rj)
    (hK : radialK e ω rj < 0) (hP0 : radialK e ω rj ^ 2 - L * delta M Q rj = 0)
    (hP1 : 2 * radialK e ω rj * (2 * ω * rj - e) - L * (2 * (rj - M)) < 0)
    {U V : ℝ → ℂ} (hU : ContinuousAt U rj) (hV : ContinuousAt V rj) :
    let kh := effectiveK M Q e ω L
    let fx := xDeriv M Q (normalizationG M Q e ω) kh
    Tendsto (fun r => -(kh r / fx r) * ‖V r + σ * kh r * I * U r‖ ^ 2 -
      (V r * (starRingEnd ℂ) (U r)).re)
      (𝓝[<] rj) (𝓝 (-(V rj * (starRingEnd ℂ) (U rj)).re)) := by
  obtain ⟨hF, hF0, hF1⟩ := sr_potential_data hQ hN hr hP0
  obtain ⟨hd, hd0⟩ := sr_density_continuous hQ hN hr
  have hg0 : 0 < normalizationG M Q e ω rj := by
    rw [source_sub_reciprocal_normalization hQ hN]
    exact staticSolution_pos hQ hr
  have hFneg : deriv (fun r => normalizationG M Q e ω r ^ 4 *
      (radialK e ω r ^ 2 - L * delta M Q r)) rj < 0 := by
    rw [hF1]
    exact mul_neg_of_pos_of_neg (pow_pos hg0 4) hP1
  have ht := source_radial_turning_current_left (s := -1) (σ := σ) (Or.inr rfl)
    hF hF0 hFneg hd hd0 hU hV
  have he : effectiveK M Q e ω L =ᶠ[𝓝 rj] fun r => -1 *
      Real.sqrt (normalizationG M Q e ω r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r)) := by
    filter_upwards [Ioi_mem_nhds hr,
      (contDiff_radialK e ω).continuous.continuousAt.eventually (gt_mem_nhds hK)] with r hra hkr
    apply sr_effective_sqrt
    · rw [source_sub_reciprocal_normalization hQ hN]
      exact (staticSolution_pos hQ hra).le
    · rw [sign_neg hkr, SignType.coe_neg_one]
  apply ht.congr'
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,
    he.eventuallyEq_nhds.filter_mono nhdsWithin_le_nhds] with r h0 h1
  unfold xDeriv
  rw [h0, h1.deriv_eq]

/-- The infinity-side simple turning point has the same radial matching
value. The current's endpoint sign may be any real number. -/
theorem source_sub_reciprocal_turning_current_right {M Q e ω L rj σ : ℝ}
    (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) (hr : outerHorizon M Q < rj)
    (hK : 0 < radialK e ω rj) (hP0 : radialK e ω rj ^ 2 - L * delta M Q rj = 0)
    (hP1 : 0 < 2 * radialK e ω rj * (2 * ω * rj - e) - L * (2 * (rj - M)))
    {U V : ℝ → ℂ} (hU : ContinuousAt U rj) (hV : ContinuousAt V rj) :
    let kh := effectiveK M Q e ω L
    let fx := xDeriv M Q (normalizationG M Q e ω) kh
    Tendsto (fun r => -(kh r / fx r) * ‖V r + σ * kh r * I * U r‖ ^ 2 -
      (V r * (starRingEnd ℂ) (U r)).re)
      (𝓝[>] rj) (𝓝 (-(V rj * (starRingEnd ℂ) (U rj)).re)) := by
  obtain ⟨hF, hF0, hF1⟩ := sr_potential_data hQ hN hr hP0
  obtain ⟨hd, hd0⟩ := sr_density_continuous hQ hN hr
  have hg0 : 0 < normalizationG M Q e ω rj := by
    rw [source_sub_reciprocal_normalization hQ hN]
    exact staticSolution_pos hQ hr
  have hFpos : 0 < deriv (fun r => normalizationG M Q e ω r ^ 4 *
      (radialK e ω r ^ 2 - L * delta M Q r)) rj := by
    rw [hF1]
    exact mul_pos (pow_pos hg0 4) hP1
  have ht := source_radial_turning_current_right (s := 1) (σ := σ) (Or.inl rfl)
    hF hF0 hFpos hd hd0 hU hV
  have he : effectiveK M Q e ω L =ᶠ[𝓝 rj] fun r => 1 *
      Real.sqrt (normalizationG M Q e ω r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r)) := by
    filter_upwards [Ioi_mem_nhds hr,
      (contDiff_radialK e ω).continuous.continuousAt.eventually (lt_mem_nhds hK)] with r hra hkr
    apply sr_effective_sqrt
    · rw [source_sub_reciprocal_normalization hQ hN]
      exact (staticSolution_pos hQ hra).le
    · rw [sign_pos hkr, SignType.coe_one]
  apply ht.congr'
  filter_upwards [he.filter_mono nhdsWithin_le_nhds,
    he.eventuallyEq_nhds.filter_mono nhdsWithin_le_nhds] with r h0 h1
  unfold xDeriv
  rw [h0, h1.deriv_eq]

/-- At `L = 0` both one-sided currents match the middle flux at corotation.
The frequency is smooth there, and its positive `x` derivative prevents a
singularity in the ratio. -/
theorem source_sub_reciprocal_turning_current_zero {M Q e ω σ : ℝ}
    (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) (hN : 2 * M ≤ e / ω)
    {U V : ℝ → ℂ} (hU : ContinuousAt U (e / ω)) (hV : ContinuousAt V (e / ω))
    {l : Filter ℝ} (hl : l ≤ 𝓝 (e / ω)) :
    let kh := effectiveK M Q e ω 0
    let fx := xDeriv M Q (normalizationG M Q e ω) kh
    Tendsto (fun r => -(kh r / fx r) * ‖V r + σ * kh r * I * U r‖ ^ 2 -
      (V r * (starRingEnd ℂ) (U r)).re)
      l (𝓝 (-(V (e / ω) * (starRingEnd ℂ) (U (e / ω))).re)) := by
  obtain ⟨hkC, hfx0, -⟩ := source_sub_reciprocal_coefficient_props_zero hM hQ hω ha hN ha
  have hD := (sr_density_continuous hQ hN ha).1
  have hfxC : ContinuousAt
      (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω 0)) (e / ω) :=
    hD.mul (hkC.derivWithin (m := 1) (by norm_num)).continuousAt
  have hγ := hkC.continuousAt.div hfxC hfx0.ne'
  have hk0 : effectiveK M Q e ω 0 (e / ω) = 0 := by
    rw [source_effectiveK_zero]
    simp only [radialK_corotation_eq_zero e hω.ne', mul_zero]
  have hNrm : ContinuousAt (fun r =>
      ‖V r + σ * effectiveK M Q e ω 0 r * I * U r‖ ^ 2) (e / ω) := by
    have hk := hkC.continuousAt
    fun_prop
  have hp : ContinuousAt (fun r => (V r * (starRingEnd ℂ) (U r)).re) (e / ω) := by
    fun_prop
  have ht := (hγ.neg.mul hNrm).sub hp |>.tendsto.mono_left hl
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply,
    hk0, zero_div, neg_zero, zero_mul, zero_sub] at ht
  apply ht.congr
  intro r
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply]

end ModeStability.AllAngular

end
