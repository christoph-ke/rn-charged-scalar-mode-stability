module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtConstantTransport
public import ModeStability.AllAngular.ExtremalHorizonLimits
public import ModeStability.AllAngular.InfinityLimitsL
public import ModeStability.AllAngular.SourceIdentityRRegions

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
theorem sec_horizon_current {M Q e ω L b : ℝ}
    (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω) (hL : 0 ≤ L)
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
  let f := fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
    Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))
  have hKM : radialK e ω M ≠ 0 := by
    simpa only [outerHorizon_of_abs_eq hQ] using hKa.ne
  have hK' : 2 * ω * M - e ≠ 0 := by
    have hn := (div_lt_iff₀ hω).mp hN
    linarith
  have ht := extremal_constant_horizon_current_tendsto_L hQ hL hKM hK' hΘ hT hH1 hH2
  have hcomp := (ht.comp (sec_coordinate_horizon hQ)).neg
  have hrad : Tendsto (fun r =>
      -(effectiveK M Q e ω L r / xDeriv M Q (normalizationG M Q e ω)
        (effectiveK M Q e ω L) r) *
        ‖((delta M Q r * normalizationG M Q e ω r ^ 2 : ℝ) : ℂ) *
          deriv (fun s => T s / (normalizationG M Q e ω s : ℂ)) r +
          (effectiveK M Q e ω L r : ℂ) * I * (T r / (normalizationG M Q e ω r : ℂ))‖ ^ 2 -
        ((((delta M Q r * normalizationG M Q e ω r ^ 2 : ℝ) : ℂ) *
          deriv (fun s => T s / (normalizationG M Q e ω s : ℂ)) r) *
          (starRingEnd ℂ) (T r / (normalizationG M Q e ω r : ℂ))).re)
      (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
    simp only [neg_zero] at hcomp
    apply hcomp.congr'
    obtain ⟨r₁, r₂, hr₁, -, hAH, -, -⟩ := source_radial_regions hM hQ.le hω hL hKa
    filter_upwards [Ioo_mem_nhdsGT hr₁] with r hr
    have hi := extremal_constant_inverse hQ hr.1
    have hPr : L * delta M Q r < radialK e ω r ^ 2 := by
      have hm : r ∈ {r | outerHorizon M Q < r ∧ r < e / ω ∧
          L * delta M Q r < radialK e ω r ^ 2} := by rw [hAH]; exact hr
      exact hm.2.2
    have hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L)
        (M + 1 / (1 / (r - M))) := by
      rw [hi.2]
      exact (sec_coefficient_props hM hQ hω hL ha hN hr.1 hPr).1
    have hj := sec_current_jet (σ := 1) hQ hN (fun r hr => (hT r hr).1) hi.1 hf
    dsimp only at hj ⊢
    rw [hi.2] at hj
    simpa only [Function.comp_apply, f, hi.2, ofReal_one, one_mul, neg_neg] using
      congrArg Neg.neg hj
  apply hrad.congr'
  filter_upwards [Ioo_mem_nhdsGT hb] with r hr
  have he := eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hr) hEq
  have hu : (fun s => R s / (normalizationG M Q e ω s : ℂ)) =ᶠ[𝓝 r]
      (fun s => T s / (normalizationG M Q e ω s : ℂ)) :=
    he.mono fun s hs => congrArg (fun z : ℂ => z / (normalizationG M Q e ω s : ℂ)) hs
  rw [hu.deriv_eq, hEq hr]

/-- Zero infinity-current limit in exact radial notation for an amplitude
equal to a homogeneous outgoing piece beyond the source support. -/
theorem sec_infinity_current {M Q e ω L b : ℝ}
    (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω) (hL : 0 ≤ L)
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
  have ht := extremal_constant_infinity_current_tendsto_L hQ hL hω.ne' hΘ hT hI1 hI2
    (f := fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
      Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) (fun _ _ => rfl)
    (U := fun t => T (M + 1 / t)) (fun _ _ => rfl)
  have hcomp := (ht.comp (sec_coordinate_infinity M)).neg
  have hrad : Tendsto (fun r =>
      -(effectiveK M Q e ω L r / xDeriv M Q (normalizationG M Q e ω)
        (effectiveK M Q e ω L) r) *
        ‖((delta M Q r * normalizationG M Q e ω r ^ 2 : ℝ) : ℂ) *
          deriv (fun s => T s / (normalizationG M Q e ω s : ℂ)) r -
          (effectiveK M Q e ω L r : ℂ) * I * (T r / (normalizationG M Q e ω r : ℂ))‖ ^ 2 -
        ((((delta M Q r * normalizationG M Q e ω r ^ 2 : ℝ) : ℂ) *
          deriv (fun s => T s / (normalizationG M Q e ω s : ℂ)) r) *
          (starRingEnd ℂ) (T r / (normalizationG M Q e ω r : ℂ))).re)
      atTop (𝓝 0) := by
    simp only [neg_zero] at hcomp
    apply hcomp.congr'
    obtain ⟨r₁, r₂, hr₁, h₁₂, -, -, hAI⟩ := source_radial_regions hM hQ.le hω hL hKa
    filter_upwards [Ioi_mem_atTop r₂] with r hr
    have hra := hr₁.trans_le h₁₂ |>.trans hr
    have hi := extremal_constant_inverse hQ hra
    have hPr : L * delta M Q r < radialK e ω r ^ 2 := by
      have hm : r ∈ {r | e / ω < r ∧ L * delta M Q r < radialK e ω r ^ 2} := by
        rw [hAI]; exact hr
      exact hm.2
    have hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L) (M + 1 / (1 / (r - M))) := by
      rw [hi.2]
      exact (sec_coefficient_props hM hQ hω hL ha hN hra hPr).1
    have hj := sec_current_jet (σ := -1) hQ hN (fun r hr => (hT r hr).1) hi.1 hf
    dsimp only at hj ⊢
    rw [hi.2] at hj
    simpa only [Function.comp_apply, hi.2, ofReal_neg, ofReal_one, neg_one_mul,
      neg_mul, one_mul, ← sub_eq_add_neg, neg_neg] using congrArg Neg.neg hj
  apply hrad.congr'
  filter_upwards [Ioi_mem_atTop b] with r hr
  have he := eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hr) hEq
  have hu : (fun s => R s / (normalizationG M Q e ω s : ℂ)) =ᶠ[𝓝 r]
      (fun s => T s / (normalizationG M Q e ω s : ℂ)) := by
    filter_upwards [he] with s hs
    rw [hs]
  rw [hu.deriv_eq, hEq hr]

end ModeStability.AllAngular

end
