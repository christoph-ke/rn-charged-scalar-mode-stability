module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentitySubConstantTransport

/-!
# Homogeneous endpoint pieces give the radial Green current limits

Source: the all-angular research notes in preparation, pp. 7–8.
The Green solution equals a homogeneous endpoint piece outside the compact
source support. Locality, inverse-coordinate filters and first-jet transport
give zero limits for the exact current in radial variables.
-/

public section

open Complex Set Filter Topology Asymptotics

namespace ModeStability.AllAngular

/-- Zero horizon-current limit in exact radial notation for any amplitude
equal to a homogeneous ingoing piece near the horizon. -/
theorem ssc_horizon_current {M Q e ω L b : ℝ}
    (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω) (hL : 0 ≤ L)
    (hKa : radialK e ω (outerHorizon M Q) < 0) (hN : e / ω < 2 * M)
    (hb : outerHorizon M Q < b) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R T : ℝ → ℂ} (hEq : EqOn R T (Ioo (outerHorizon M Q) b))
    (_hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    (hT : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ T r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv T s)
        (-(((radialK e ω r ^ 2 / delta M Q r - L : ℝ) : ℂ)) * T r) r)
    {B : ℂ}
    (hH1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * T r - B)
      =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q))
    (hH2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * T r)
      =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))) :
    let g := normalizationG M Q e ω
    let U := fun r => R r / (g r : ℂ)
    let V := fun r => ((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r
    let kh := effectiveK M Q e ω L
    let fx := xDeriv M Q g kh
    Tendsto (fun r => -(kh r / fx r) * ‖V r + (kh r : ℂ) * I * U r‖ ^ 2 -
      (V r * (starRingEnd ℂ) (U r)).re) (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
  have ha := outerHorizon_lt_corotation hM hω hKa
  have hlH : 0 < 2 * ω * outerHorizon M Q - e -
      L * (outerHorizon M Q - innerHorizon M Q) / (2 * radialK e ω (outerHorizon M Q)) := by
    have hMa : M ≤ outerHorizon M Q := by
      unfold outerHorizon
      linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
    have hab : 0 ≤ outerHorizon M Q - innerHorizon M Q := by
      unfold outerHorizon innerHorizon
      linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
    have he := (div_lt_iff₀ hω).mp hN
    have hωa := mul_le_mul_of_nonneg_left hMa (by positivity : 0 ≤ 2 * ω)
    have hq := div_nonpos_of_nonneg_of_nonpos (mul_nonneg hL hab)
      (by linarith : 2 * radialK e ω (outerHorizon M Q) ≤ 0)
    linarith
  have ht := constant_horizon_current_tendsto_L hQ hL hKa.ne hlH.ne' hΘ hT hH1 hH2
  have hcomp := ht.neg.comp (ssc_coordinate_horizon hQ)
  simp only [neg_zero] at hcomp
  apply hcomp.congr'
  obtain ⟨r₁, r₂, hr₁, -, hAH, -, -⟩ := source_radial_regions hM hQ.le hω hL hKa
  have he := ssc_current_eqOn isOpen_Ioo hEq (delta M Q) (effectiveK M Q e ω L)
    (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) 1
  filter_upwards [Ioo_mem_nhdsGT hr₁, Ioo_mem_nhdsGT hb] with r hr hrs
  have hi := constant_inverse hQ hr.1
  have hPr : L * delta M Q r < radialK e ω r ^ 2 := by
    have hm : r ∈ {r | outerHorizon M Q < r ∧ r < e / ω ∧
        L * delta M Q r < radialK e ω r ^ 2} := by rw [hAH]; exact hr
    exact hm.2.2
  have hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L)
      (radiusOf M Q (1 / staticSolution M Q r)) := by
    rw [hi.2]
    exact (ssc_coefficient_props hM hQ hω hL ha hN hr.1 hPr).1
  have hj := congrArg Neg.neg (ssc_current_jet (σ := 1) hQ hN
    (fun r hr => (hT r hr).1) hi.1 hf)
  dsimp only [Function.comp_apply] at hj ⊢
  rw [hi.2] at hj ⊢
  simp only [neg_neg] at hj ⊢
  rw [hj]
  simpa only [NormalizationFacts.normalizationG_eq_one hN, one_pow, mul_one,
    ofReal_one, div_one, one_mul] using (he hrs).symm

/-- Zero infinity-current limit in exact radial notation for an amplitude
equal to a homogeneous outgoing piece beyond the source support, in
the constant normalization `e/ω < 2M`. -/
theorem ssc_infinity_current {M Q e ω L b : ℝ}
    (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω) (hL : 0 ≤ L)
    (hKa : radialK e ω (outerHorizon M Q) < 0) (hN : e / ω < 2 * M)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R T : ℝ → ℂ} (hEq : EqOn R T (Ioi b))
    (_hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    (hT : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ T r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv T s)
        (-(((radialK e ω r ^ 2 / delta M Q r - L : ℝ) : ℂ)) * T r) r)
    {B : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * T r - B)
      =O[atTop] (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * T r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    let g := normalizationG M Q e ω
    let U := fun r => R r / (g r : ℂ)
    let V := fun r => ((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r
    let kh := effectiveK M Q e ω L
    let fx := xDeriv M Q g kh
    Tendsto (fun r => -(kh r / fx r) * ‖V r - (kh r : ℂ) * I * U r‖ ^ 2 -
      (V r * (starRingEnd ℂ) (U r)).re) atTop (𝓝 0) := by
  have ha := outerHorizon_lt_corotation hM hω hKa
  have ht := constant_infinity_current_tendsto_L hQ hL hω.ne' hΘ hT hI1 hI2
    (f := fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
      Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
        L * delta M Q (radiusOf M Q (1 / t)))))
    (fun _ _ => rfl) (U := fun t => T (radiusOf M Q (1 / t))) (fun _ _ => rfl)
  have hcomp := ht.neg.comp (ssc_coordinate_infinity hQ)
  simp only [neg_zero] at hcomp
  apply hcomp.congr'
  obtain ⟨r₁, r₂, hr₁, h₁₂, -, -, hAI⟩ := source_radial_regions hM hQ.le hω hL hKa
  have he := ssc_current_eqOn isOpen_Ioi hEq (delta M Q) (effectiveK M Q e ω L)
    (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) (-1)
  filter_upwards [Ioi_mem_atTop r₂, Ioi_mem_atTop b] with r hr hrs
  have hra := hr₁.trans_le h₁₂ |>.trans hr
  have hi := constant_inverse hQ hra
  have hPr : L * delta M Q r < radialK e ω r ^ 2 := by
    have hm : r ∈ {r | e / ω < r ∧ L * delta M Q r < radialK e ω r ^ 2} := by
      rw [hAI]; exact hr
    exact hm.2
  have hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L)
      (radiusOf M Q (1 / staticSolution M Q r)) := by
    rw [hi.2]
    exact (ssc_coefficient_props hM hQ hω hL ha hN hra hPr).1
  have hj := congrArg Neg.neg (ssc_current_jet (σ := -1) hQ hN
    (fun r hr => (hT r hr).1) hi.1 hf)
  dsimp only [Function.comp_apply] at hj ⊢
  rw [hi.2] at hj ⊢
  simp only [neg_neg, ofReal_neg, ofReal_one, neg_mul,
    one_mul, ← sub_eq_add_neg] at hj ⊢
  rw [hj]
  simpa only [NormalizationFacts.normalizationG_eq_one hN, one_pow, mul_one,
    ofReal_one, div_one, ofReal_neg, neg_one_mul, neg_mul, one_mul,
    ← sub_eq_add_neg] using (he hrs).symm

end ModeStability.AllAngular

end
