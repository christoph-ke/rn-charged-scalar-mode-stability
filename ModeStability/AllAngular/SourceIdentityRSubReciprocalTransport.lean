module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityRSubReciprocalCoefficients
public import ModeStability.AllAngular.SourceIdentityRLocality
public import ModeStability.AllAngular.SourceIdentityRRegions

/-!
# Reciprocal first jets and endpoint filters in radial variables

Source: the all-angular research notes in preparation, pp. 7–8.
The inverse coordinate and the first jets identify the phase-free current
with its exact radial expression using the frozen `xDeriv`.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

open CoordinateCoefficients

/-- The reciprocal inverse coordinate takes the radial horizon filter to
`x → 0⁺`. The proof uses the monotone inverse, without an asymptotic expansion. -/
theorem source_sub_reciprocal_coordinate_horizon {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (fun r => 1 / staticSolution M Q r)
      (𝓝[>] (outerHorizon M Q)) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_order.mpr ⟨?_, ?_⟩, ?_⟩
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hb.trans (reciprocal_inverse hQ hr).1
  · intro b hb
    have hrb := outerHorizon_lt_radiusOf hQ hb
    filter_upwards [Ioo_mem_nhdsGT hrb] with r hr
    have hi := reciprocal_inverse hQ hr.1
    exact ((reciprocal_strictMonoOn hQ).lt_iff_lt hi.1 hb).mp (by rw [hi.2]; exact hr.2)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (reciprocal_inverse hQ hr).1

/-- The reciprocal inverse coordinate tends to `+∞` at radial infinity. -/
theorem source_sub_reciprocal_coordinate_infinity {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (fun r => 1 / staticSolution M Q r) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  let c := max b 1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  filter_upwards [Ioi_mem_atTop (max (outerHorizon M Q) (radiusOf M Q c))] with r hr
  have hi := reciprocal_inverse hQ ((le_max_left _ _).trans_lt hr)
  have hlt : c < 1 / staticSolution M Q r :=
    ((reciprocal_strictMonoOn hQ).lt_iff_lt hc hi.1).mp (by
      rw [hi.2]
      exact (le_max_right _ _).trans_lt hr)
  exact (le_max_left b 1).trans hlt.le

/-- The first jet of the transformed amplitude in `x` is exactly
`U = R/g`, `Ux = Δg²∂ᵣU` in `r`. Only first differentiability is needed. -/
theorem source_sub_reciprocal_amplitude_jet {M Q e ω : ℝ}
    (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    {x : ℝ} (hx : 0 < x) :
    let g := normalizationG M Q e ω
    let U := fun r => R r / (g r : ℂ)
    ((x : ℂ) * R (radiusOf M Q x) = U (radiusOf M Q x)) ∧
      deriv (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x =
        ((delta M Q (radiusOf M Q x) * g (radiusOf M Q x) ^ 2 : ℝ) : ℂ) *
          deriv U (radiusOf M Q x) := by
  rw [source_sub_reciprocal_normalization hQ hN]
  dsimp only
  have he : (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) =ᶠ[𝓝 x]
      fun y => R (radiusOf M Q y) / (staticSolution M Q (radiusOf M Q y) : ℂ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [staticSolution_radiusOf hQ hy, ofReal_div, ofReal_one]
    field_simp
  have hr := outerHorizon_lt_radiusOf hQ hx
  have hd := ((hR _ hr).hasDerivAt.div (hasDerivAt_staticSolution hQ hr).ofReal_comp
    (ofReal_ne_zero.mpr (staticSolution_pos hQ hr).ne')).scomp x
      (hasDerivAt_radiusOf_eq_mul_sq hQ hx)
  refine ⟨he.eq_of_nhds, ?_⟩
  rw [he.deriv_eq]
  have hd' := hd.deriv
  dsimp only [Function.comp_def, Pi.div_apply] at hd'
  rw [hd']
  rw [← Complex.real_smul]
  congr 1
  exact ((hR _ hr).hasDerivAt.div (hasDerivAt_staticSolution hQ hr).ofReal_comp
    (ofReal_ne_zero.mpr (staticSolution_pos hQ hr).ne')).deriv.symm

/-- The signed coordinate frequency and its first two derivatives agree
with `effectiveK`, `khx = xDeriv kh`, and `khxx = xDeriv khx`. -/
theorem source_sub_reciprocal_frequency_jet {M Q e ω L : ℝ}
    (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) {x : ℝ} (hx : 0 < x)
    (hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L) (radiusOf M Q x)) :
    let f : ℝ → ℝ := fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
      Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))
    f x = effectiveK M Q e ω L (radiusOf M Q x) ∧
      deriv f x = xDeriv M Q (normalizationG M Q e ω)
        (effectiveK M Q e ω L) (radiusOf M Q x) ∧
      deriv (deriv f) x = xDeriv M Q (normalizationG M Q e ω)
        (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) (radiusOf M Q x) := by
  have hg := source_sub_reciprocal_normalization hQ hN
  have hr := outerHorizon_lt_radiusOf hQ hx
  have he : (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
      Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) =ᶠ[𝓝 x]
      fun y => 1 * effectiveK M Q e ω L (radiusOf M Q y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    unfold effectiveK
    rw [hg, staticSolution_radiusOf hQ hy, one_mul]
  have hρ : ∀ᶠ y in 𝓝 x, HasDerivAt (radiusOf M Q)
      (1 * (delta M Q (radiusOf M Q y) * normalizationG M Q e ω (radiusOf M Q y) ^ 2)) y := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simpa only [one_mul, hg] using hasDerivAt_radiusOf_eq_mul_sq hQ hy
  have hw : ContDiffAt ℝ 1 (fun r => delta M Q r * normalizationG M Q e ω r ^ 2)
      (radiusOf M Q x) := by
    rw [hg]
    exact ((contDiff_delta M Q).contDiffAt.mul
      ((contDiffAt_staticSolution hQ hr).pow 2)).of_le (by norm_num)
  have hd : DifferentiableAt ℝ (fun r => delta M Q r * normalizationG M Q e ω r ^ 2 *
      deriv (effectiveK M Q e ω L) r) (radiusOf M Q x) :=
    (hw.mul (hf.derivWithin (m := 1) (by norm_num))).differentiableAt_one
  obtain ⟨h0, h1, h2, -⟩ := coordinate_chain_rule (one_mul 1) he hρ
    (hf.eventually (by norm_num) |>.mono fun _ h =>
      (h.of_le (by norm_num)).differentiableAt_one) hd
  refine ⟨by simpa only [one_mul] using h0, h1, ?_⟩
  unfold xDeriv
  simpa only [one_mul] using h2

/-- The coordinate current equals its exact frozen radial expression. -/
theorem source_sub_reciprocal_current_jet {M Q e ω L σ : ℝ}
    (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    {x : ℝ} (hx : 0 < x)
    (hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L) (radiusOf M Q x)) :
    let f : ℝ → ℝ := fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
      Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))
    let A := fun t : ℝ => (t : ℂ) * R (radiusOf M Q t)
    let g := normalizationG M Q e ω
    let U := fun r => R r / (g r : ℂ)
    let V := fun r => ((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r
    let kh : ℝ → ℝ := effectiveK M Q e ω L
    let fx : ℝ → ℝ := xDeriv M Q g kh
    (-(f x / deriv f x) * ‖deriv A x + σ * f x * I * A x‖ ^ 2 -
        (deriv A x * (starRingEnd ℂ) (A x)).re =
      -(kh (radiusOf M Q x) / fx (radiusOf M Q x)) *
        ‖V (radiusOf M Q x) + σ * kh (radiusOf M Q x) * I * U (radiusOf M Q x)‖ ^ 2 -
        (V (radiusOf M Q x) * (starRingEnd ℂ) (U (radiusOf M Q x))).re) := by
  obtain ⟨hf0, hf1, -⟩ := source_sub_reciprocal_frequency_jet hQ hN hx hf
  obtain ⟨hU, hV⟩ := source_sub_reciprocal_amplitude_jet hQ hN hR hx
  dsimp only at hf0 hf1 hU hV ⊢
  rw [hf0, hf1, hV, hU]

end ModeStability.AllAngular

end
