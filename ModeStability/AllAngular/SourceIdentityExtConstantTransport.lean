module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtConstantCoefficients
public import ModeStability.AllAngular.CoordinateIntervalsExtremal

/-!
# Current transport for the reflected extremal constant coordinate

Source: the all-angular research notes in preparation, identity (6.3),
and the constant normalization (2.2). With `y = 1/(r − M)`, the amplitude
derivative is `−Ux` and the frequency is `−k̂`. Consequently the current
in `y` is the negative of the radial current. Both endpoint limits are zero.
-/

public section

open Complex Set Filter Topology Asymptotics

namespace ModeStability.AllAngular

open CoordinateCoefficients

/-- First jets under the reflected constant coordinate, and the current sign. -/
theorem sec_current_jet {M Q e ω L σ : ℝ}
    (hQ : |Q| = M) (hN : e / ω < 2 * M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    {y : ℝ} (hy : 0 < y)
    (hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L) (M + 1 / y)) :
    let f : ℝ → ℝ := fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
      Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))
    let A := fun t : ℝ => R (M + 1 / t)
    let g := normalizationG M Q e ω
    let U := fun r => R r / (g r : ℂ)
    let V := fun r => ((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r
    let kh := effectiveK M Q e ω L
    let fx := xDeriv M Q g kh
    (-(f y / deriv f y) * ‖deriv A y + σ * f y * I * A y‖ ^ 2 -
        (deriv A y * (starRingEnd ℂ) (A y)).re =
      -(-(kh (M + 1 / y) / fx (M + 1 / y)) *
        ‖V (M + 1 / y) + σ * kh (M + 1 / y) * I * U (M + 1 / y)‖ ^ 2 -
        (V (M + 1 / y) * (starRingEnd ℂ) (U (M + 1 / y))).re)) := by
  dsimp only
  let kh := effectiveK M Q e ω L
  let f : ℝ → ℝ := fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
    Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))
  have he : f =ᶠ[𝓝 y] fun t => -1 * kh (M + 1 / t) := by
    apply Eventually.of_forall
    intro t
    dsimp [f, kh, effectiveK]
    rw [NormalizationFacts.normalizationG_eq_one hN, delta_of_abs_eq hQ,
      add_sub_cancel_left]
    simp only [one_pow, mul_one, div_pow, mul_one_div, neg_one_mul]
  have hρ : ∀ᶠ t in 𝓝 y, HasDerivAt (fun t => M + 1 / t)
      (-1 * (delta M Q (M + 1 / t) * normalizationG M Q e ω (M + 1 / t) ^ 2)) t := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    apply (extremal_constant_hasDerivAt M ht).congr_deriv
    rw [NormalizationFacts.normalizationG_eq_one hN, delta_of_abs_eq hQ,
      add_sub_cancel_left]
    ring
  have hG : DifferentiableAt ℝ (fun r => delta M Q r * normalizationG M Q e ω r ^ 2 *
      deriv kh r) (M + 1 / y) := by
    rw [NormalizationFacts.normalizationG_eq_one hN]
    exact ((((contDiff_delta M Q).contDiffAt.mul (contDiffAt_const.pow 2)).of_le
      (by norm_num)).mul
      (hf.derivWithin (m := 1) (by norm_num))).differentiableAt_one
  obtain ⟨h0, h1, -, -⟩ := coordinate_chain_rule (by norm_num : (-1 : ℝ) * -1 = 1)
    he hρ (hf.eventually (by norm_num) |>.mono fun _ h =>
      (h.of_le (by norm_num)).differentiableAt_one) hG
  have hd : deriv (fun t => R (M + 1 / t)) y = -(y ^ 2)⁻¹ • deriv R (M + 1 / y) := by
    simpa only [Function.comp_def] using
      ((hR _ (extremal_constant_mapsTo hQ hy)).hasDerivAt.scomp y
        (extremal_constant_hasDerivAt M hy)).deriv
  have hd' : deriv (fun t => R (M + 1 / t)) y =
      -((delta M Q (M + 1 / y) : ℂ) * deriv R (M + 1 / y)) := by
    rw [hd, delta_of_abs_eq hQ, add_sub_cancel_left]
    simp only [one_div, ofReal_neg, ofReal_inv, ofReal_pow, Complex.real_smul]
    ring
  change -(f y / deriv f y) *
      ‖deriv (fun t => R (M + 1 / t)) y + (σ : ℂ) * (f y : ℂ) * I * R (M + 1 / y)‖ ^ 2 -
      (deriv (fun t => R (M + 1 / t)) y * (starRingEnd ℂ) (R (M + 1 / y))).re = _
  rw [h0, h1, hd', NormalizationFacts.normalizationG_eq_one hN]
  simp only [one_pow, mul_one, ofReal_one, div_one]
  have hn : -((delta M Q (M + 1 / y) : ℂ) * deriv R (M + 1 / y)) +
      (σ : ℂ) * ((-1 * kh (M + 1 / y) : ℝ) : ℂ) * I * R (M + 1 / y) =
      -((delta M Q (M + 1 / y) : ℂ) * deriv R (M + 1 / y) +
        (σ : ℂ) * (kh (M + 1 / y) : ℂ) * I * R (M + 1 / y)) := by
    push_cast
    ring
  rw [hn, norm_neg]
  simp only [xDeriv, neg_mul, neg_re, neg_div, one_mul, one_pow, mul_one]
  ring

/-- The inverse reflected coordinate approaches infinity at the horizon. -/
theorem sec_coordinate_horizon {M Q : ℝ} (hQ : |Q| = M) :
    Tendsto (fun r => 1 / (r - M)) (𝓝[>] (outerHorizon M Q)) atTop := by
  rw [outerHorizon_of_abs_eq hQ]
  have ht : Tendsto (fun r : ℝ => r - M) (𝓝[>] M) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · exact ((continuous_sub_right M).tendsto' M 0 (sub_self M)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact sub_pos.mpr hr
  simpa only [Function.comp_def, one_div] using tendsto_inv_nhdsGT_zero.comp ht

/-- The inverse reflected coordinate approaches zero from above at infinity. -/
theorem sec_coordinate_infinity (M : ℝ) :
    Tendsto (fun r => 1 / (r - M)) atTop (𝓝[>] 0) := by
  simpa only [Function.comp_def, one_div, sub_eq_add_neg, id_eq] using
    (tendsto_inv_atTop_nhdsGT_zero.comp (tendsto_atTop_add_const_right atTop (-M) tendsto_id))

end ModeStability.AllAngular

end
