module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentitySubConstantReduction
public import ModeStability.AllAngular.SourceIdentitySubConstantCoefficients

/-!
# The integrated allowed current in the subextremal constant system

Source: the all-angular research notes in preparation, pp. 7–8,
identity (6.3). This is the concrete radial current equation for a locally
integrable source. Its variables and multiplier use the frozen definitions
in the inhomogeneous equation, and its second derivative equation is only almost everywhere.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

open CoordinateCoefficients

/-- Squaring the signed effective frequency recovers the radial potential
on the allowed region. -/
theorem ssc_effectiveK_sq {M Q e ω L r : ℝ} (hL : 0 ≤ L)
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

/-- The exact radial allowed-current equation, integrated on any compact
interval contained in the allowed set. It holds for rough sources and
both choices of endpoint sign. -/
theorem ssc_allowed_integral {M Q e ω L b c σ : ℝ}
    (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω) (hL : 0 ≤ L)
    (ha : outerHorizon M Q < e / ω) (hN : e / ω < 2 * M)
    (hb : outerHorizon M Q < b) (hc : outerHorizon M Q < c)
    (hP : ∀ r ∈ uIcc b c, L * delta M Q r < radialK e ω r ^ 2)
    (hσ : σ = 1 ∨ σ = -1) {R S : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    (hS : ∀ u ∈ Ioi (outerHorizon M Q), ∀ v ∈ Ioi (outerHorizon M Q),
      IntervalIntegrable S volume u v)
    (hint : ∀ u ∈ Ioi (outerHorizon M Q), ∀ v ∈ Ioi (outerHorizon M Q),
      (delta M Q v : ℂ) * deriv R v - (delta M Q u : ℂ) * deriv R u =
        ∫ r in u..v, S r - (((radialK e ω r ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r)) :
    let g := normalizationG M Q e ω
    let U := fun r => R r / (g r : ℂ)
    let Ux := fun r => ((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r
    let kh := effectiveK M Q e ω L
    let khx := xDeriv M Q g kh
    let khxx := xDeriv M Q g khx
    let w := fun r => 1 / (delta M Q r * g r ^ 2)
    let J := fun r => -(kh r / khx r) * ‖Ux r + σ * kh r * I * U r‖ ^ 2 -
      (Ux r * (starRingEnd ℂ) (U r)).re
    (∫ r in b..c, w r * (-((2 * khx r ^ 2 - kh r * khxx r) / khx r ^ 2) *
      ‖Ux r + σ * kh r * I * U r‖ ^ 2 -
      (((delta M Q r * g r ^ 3 : ℝ) : ℂ) * S r *
        (starRingEnd ℂ) (U r + 2 * (kh r / khx r) *
          (Ux r + σ * kh r * I * U r))).re)) = J c - J b := by
  dsimp only
  let g := normalizationG M Q e ω
  let U := fun r => R r / (g r : ℂ)
  let V := fun r => ((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r
  let kh := effectiveK M Q e ω L
  let fx := xDeriv M Q g kh
  have hsub : uIcc b c ⊆ Ioi (outerHorizon M Q) :=
    fun r hr => (lt_min hb hc).trans_le hr.1
  obtain ⟨hUC, hred⟩ := ssc_reduction hQ hN hR hS hint
  obtain ⟨hVac, hdV⟩ := hred b hb c hc
  have hkh : ContDiffOn ℝ 2 kh (uIcc b c) := fun r hr =>
    (ssc_coefficient_props hM hQ hω hL ha hN
      (hsub hr) (hP r hr)).1.contDiffWithinAt
  have hwC : ∀ r ∈ uIcc b c,
      ContDiffAt ℝ 1 (fun r => delta M Q r * g r ^ 2) r := by
    intro r hr
    dsimp [g]
    rw [NormalizationFacts.normalizationG_eq_one hN]
    simpa only [one_pow, mul_one] using (contDiff_delta M Q).contDiffAt.of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hfxC : ContDiffOn ℝ 1 fx (uIcc b c) := by
    intro r hr
    have hkC := (ssc_coefficient_props hM hQ hω hL ha hN
      (hsub hr) (hP r hr)).1
    exact ((hwC r hr).mul (hkC.derivWithin (m := 1) (by norm_num))).contDiffWithinAt
  have hfx0 : ∀ r ∈ uIcc b c, fx r ≠ 0 := fun r hr =>
    (ssc_coefficient_props hM hQ hω hL ha hN (hsub hr) (hP r hr)).2.1.ne'
  apply source_weighted_current_integral hσ
    (((hkh.of_le (by norm_num)).div hfxC hfx0).absolutelyContinuousOnInterval)
    (hkh.of_le (by norm_num)).absolutelyContinuousOnInterval
    (hUC.mono hsub).absolutelyContinuousOnInterval hVac
  filter_upwards [hdV] with r hr hmem
  have hra := hsub hmem
  have hg0 : g r ≠ 0 := by
    dsimp [g]
    rw [NormalizationFacts.normalizationG_eq_one hN]
    exact one_ne_zero
  have hd0 : delta M Q r * g r ^ 2 ≠ 0 :=
    mul_ne_zero (delta_pos hQ hra).ne' (pow_ne_zero 2 hg0)
  have hΔ0 : delta M Q r ≠ 0 := (delta_pos hQ hra).ne'
  have hkC := (ssc_coefficient_props hM hQ hω hL ha hN hra (hP r hmem)).1
  have hfx : DifferentiableAt ℝ fx r :=
    ((hwC r hmem).mul (hkC.derivWithin (m := 1) (by norm_num))).differentiableAt_one
  refine ⟨?_, ?_, hfx0 r hmem, ?_, ?_⟩
  · convert (hkC.of_le (by norm_num)).differentiableAt_one.hasDerivAt using 1
    change (1 / (delta M Q r * g r ^ 2)) *
      (delta M Q r * g r ^ 2 * deriv kh r) = deriv kh r
    field_simp [hΔ0, hg0]
  · convert hfx.hasDerivAt using 1
    change (1 / (delta M Q r * g r ^ 2)) *
      (delta M Q r * g r ^ 2 * deriv fx r) = deriv fx r
    field_simp [hΔ0, hg0]
  · have hdU := (hUC.contDiffAt (Ioi_mem_nhds hra)).differentiableAt_one.hasDerivAt
    convert hdU using 1
    change ((1 / (delta M Q r * g r ^ 2) : ℝ) : ℂ) *
      (((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r) = deriv U r
    push_cast
    field_simp [ofReal_ne_zero.mpr hΔ0, ofReal_ne_zero.mpr hg0]
  · have he := hr hmem
    rw [← ssc_effectiveK_sq hL hra (hP r hmem)] at he
    exact he

/-- The exact radial flux equation on a compact interval. On the forbidden
region its bulk density is nonnegative. No pointwise source equation or
second derivative of the amplitude is assumed. -/
theorem ssc_forbidden_integral {M Q e ω L b c : ℝ}
    (hQ : |Q| < M) (hN : e / ω < 2 * M)
    (hb : outerHorizon M Q < b) (hc : outerHorizon M Q < c) {R S : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    (hS : ∀ u ∈ Ioi (outerHorizon M Q), ∀ v ∈ Ioi (outerHorizon M Q),
      IntervalIntegrable S volume u v)
    (hint : ∀ u ∈ Ioi (outerHorizon M Q), ∀ v ∈ Ioi (outerHorizon M Q),
      (delta M Q v : ℂ) * deriv R v - (delta M Q u : ℂ) * deriv R u =
        ∫ r in u..v, S r - (((radialK e ω r ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r)) :
    let g := normalizationG M Q e ω
    let U := fun r => R r / (g r : ℂ)
    let V := fun r => ((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r
    let w := fun r => 1 / (delta M Q r * g r ^ 2)
    (∫ r in b..c, w r * (-(‖V r‖ ^ 2 +
        g r ^ 4 * (L * delta M Q r - radialK e ω r ^ 2) * ‖U r‖ ^ 2) -
      (((delta M Q r * g r ^ 3 : ℝ) : ℂ) * S r * (starRingEnd ℂ) (U r)).re)) =
      -(V c * (starRingEnd ℂ) (U c)).re - -(V b * (starRingEnd ℂ) (U b)).re := by
  dsimp only
  let g := normalizationG M Q e ω
  let U := fun r => R r / (g r : ℂ)
  let V := fun r => ((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r
  have hsub : uIcc b c ⊆ Ioi (outerHorizon M Q) :=
    fun r hr => (lt_min hb hc).trans_le hr.1
  obtain ⟨hUC, hred⟩ := ssc_reduction hQ hN hR hS hint
  obtain ⟨hVac, hdV⟩ := hred b hb c hc
  have hUac := (hUC.mono hsub).absolutelyContinuousOnInterval
  have hconj := Complex.conjLIE.lipschitzWith.comp_absolutelyContinuousOnInterval hUac
  have hJ := (reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval
    (hVac.smul hconj)).neg
  apply source_current_integral_of_ae hJ
  filter_upwards [hdV] with r hr hmem
  have hra := hsub hmem
  have hg0 : g r ≠ 0 := by
    dsimp [g]
    rw [NormalizationFacts.normalizationG_eq_one hN]
    exact one_ne_zero
  have hΔ0 : delta M Q r ≠ 0 := (delta_pos hQ hra).ne'
  have hdU : HasDerivAt U (((1 / (delta M Q r * g r ^ 2) : ℝ) : ℂ) * V r) r := by
    convert (hUC.contDiffAt (Ioi_mem_nhds hra)).differentiableAt_one.hasDerivAt using 1
    change ((1 / (delta M Q r * g r ^ 2) : ℝ) : ℂ) *
      (((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r) = deriv U r
    push_cast
    field_simp [ofReal_ne_zero.mpr hΔ0, ofReal_ne_zero.mpr hg0]
  apply (source_weighted_flux_hasDerivAt
    (P := g r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r))
    (G := fun r => ((delta M Q r * g r ^ 3 : ℝ) : ℂ) * S r)
    hdU (hr hmem)).congr_deriv
  dsimp only [g, U]
  ring

end ModeStability.AllAngular

end
