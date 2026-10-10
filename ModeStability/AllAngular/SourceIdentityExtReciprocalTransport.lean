module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtReciprocalCoefficients
public import ModeStability.AllAngular.SourceIdentityRLocality
public import ModeStability.AllAngular.SourceIdentityRRegions

/-!
# First-jet transport in the extremal reciprocal coordinate

Source: the all-angular research notes in preparation, pp. 7–8.
Here `r = M+x`, `U(x) = xR(M+x)` and the coordinate density is one.
The phase-free current is transported to the exact shared radial definitions.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

open CoordinateCoefficients

theorem ser_coordinate_horizon {M Q : ℝ} (hQ : |Q| = M) :
    Tendsto (fun r => r - M) (𝓝[>] (outerHorizon M Q)) (𝓝[>] 0) := by
  rw [outerHorizon_of_abs_eq hQ]
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · exact ((continuous_id.sub continuous_const).tendsto' M 0 (sub_self M)).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact sub_pos.mpr hr

theorem ser_coordinate_infinity (M : ℝ) :
    Tendsto (fun r => r - M) atTop atTop := tendsto_atTop_add_const_right atTop (-M) tendsto_id

theorem ser_amplitude_jet {M Q e ω : ℝ} (hQ : |Q| = M) (hN : 2 * M ≤ e / ω)
    {R : ℝ → ℂ} (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    {x : ℝ} (hx : 0 < x) :
    let U := P61.uR M Q e ω R
    ((x : ℂ) * R (M + x) = U (M + x)) ∧
      deriv (fun y : ℝ => (y : ℂ) * R (M + y)) x = P61.uxR M Q e ω R (M + x) := by
  have hr : outerHorizon M Q < M + x := by rw [outerHorizon_of_abs_eq hQ]; linarith
  have he : (fun y : ℝ => (y : ℂ) * R (M + y)) =ᶠ[𝓝 x]
      fun y => P61.uR M Q e ω R (M + y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    dsimp [P61.uR]
    rw [ser_normalization hQ hN]
    dsimp [ser_g]
    rw [add_sub_cancel_left, ofReal_div, ofReal_one]
    field_simp
  have hg0 : (normalizationG M Q e ω (M + x) : ℂ) ≠ 0 := by
    rw [ser_normalization hQ hN]
    exact ofReal_ne_zero.mpr (ser_g_pos hQ hr).ne'
  have hdg : HasDerivAt (normalizationG M Q e ω) (-1 / delta M Q (M + x)) (M + x) := by
    rw [ser_normalization hQ hN]
    exact ser_g_derivative hQ hr
  have hU := (hR _ hr).hasDerivAt.div hdg.ofReal_comp hg0
  have hd := hU.scomp x ((hasDerivAt_id' x).const_add M)
  refine ⟨he.eq_of_nhds, ?_⟩
  rw [he.deriv_eq]
  have hdx : deriv (fun y => P61.uR M Q e ω R (M + y)) x =
      (deriv R (M + x) * ↑(normalizationG M Q e ω (M + x)) -
        R (M + x) * ↑(-1 / delta M Q (M + x))) /
          ↑(normalizationG M Q e ω (M + x)) ^ 2 := by
    simpa only [Function.comp_def, P61.uR, Pi.div_apply, one_smul] using hd.deriv
  rw [hdx]
  dsimp [P61.uxR, P61.uR]
  rw [ser_density hQ hN hr, ofReal_one, one_mul]
  change _ = deriv (R / fun y => (normalizationG M Q e ω y : ℂ)) (M + x)
  exact hU.deriv.symm

theorem ser_frequency_jet {M Q e ω L : ℝ} (hQ : |Q| = M) (hN : 2 * M ≤ e / ω)
    {x : ℝ} (hx : 0 < x) (hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L) (M + x)) :
    let f : ℝ → ℝ := fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
      Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)
    f x = effectiveK M Q e ω L (M + x) ∧
      deriv f x = xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) (M + x) ∧
      deriv (deriv f) x = xDeriv M Q (normalizationG M Q e ω)
        (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) (M + x) := by
  have hr : outerHorizon M Q < M + x := by rw [outerHorizon_of_abs_eq hQ]; linarith
  have he : (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
      Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) =ᶠ[𝓝 x]
      fun y => 1 * effectiveK M Q e ω L (M + y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    unfold effectiveK
    rw [ser_normalization hQ hN, delta_of_abs_eq hQ]
    simp only [ser_g, add_sub_cancel_left, one_mul]
  have hρ : ∀ᶠ y in 𝓝 x, HasDerivAt (fun t => M + t)
      (1 * (delta M Q (M + y) * normalizationG M Q e ω (M + y) ^ 2)) y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hry : outerHorizon M Q < M + y := by
      rw [outerHorizon_of_abs_eq hQ]
      exact lt_add_of_pos_right M hy
    rw [ser_density hQ hN hry, one_mul]
    exact (hasDerivAt_id' y).const_add M
  have hw : ContDiffAt ℝ 1 (fun r => delta M Q r * normalizationG M Q e ω r ^ 2)
      (M + x) := by
    rw [ser_normalization hQ hN]
    exact ((contDiff_delta M Q).contDiffAt.mul ((ser_g_smooth hQ hr).pow 2)).of_le
      (by norm_num)
  have hd : DifferentiableAt ℝ (fun r => delta M Q r * normalizationG M Q e ω r ^ 2 *
      deriv (effectiveK M Q e ω L) r) (M + x) :=
    (hw.mul (hf.derivWithin (m := 1) (by norm_num))).differentiableAt_one
  obtain ⟨h0, h1, h2, -⟩ := coordinate_chain_rule (one_mul 1) he hρ
    (hf.eventually (by norm_num) |>.mono fun _ h =>
      (h.of_le (by norm_num)).differentiableAt_one) hd
  refine ⟨by simpa only [one_mul] using h0, h1, ?_⟩
  unfold xDeriv
  simpa only [one_mul] using h2

theorem ser_current_jet {M Q e ω L σ : ℝ} (hQ : |Q| = M) (hN : 2 * M ≤ e / ω)
    {R : ℝ → ℂ} (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    {x : ℝ} (hx : 0 < x) (hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L) (M + x)) :
    let f : ℝ → ℝ := fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
      Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)
    let A := fun t : ℝ => (t : ℂ) * R (M + t)
    (-(f x / deriv f x) * ‖deriv A x + σ * f x * I * A x‖ ^ 2 -
        (deriv A x * (starRingEnd ℂ) (A x)).re =
      -(effectiveK M Q e ω L (M + x) / P61.khxR M Q e ω L (M + x)) *
        ‖P61.uxR M Q e ω R (M + x) + σ * effectiveK M Q e ω L (M + x) * I *
          P61.uR M Q e ω R (M + x)‖ ^ 2 -
        (P61.uxR M Q e ω R (M + x) * (starRingEnd ℂ) (P61.uR M Q e ω R (M + x))).re) := by
  obtain ⟨hf0, hf1, -⟩ := ser_frequency_jet hQ hN hx hf
  obtain ⟨hU, hV⟩ := ser_amplitude_jet hQ hN hR hx
  dsimp only at hf0 hf1 hU hV ⊢
  rw [hf0, hf1, hV, hU]
  rfl

end ModeStability.AllAngular

end
