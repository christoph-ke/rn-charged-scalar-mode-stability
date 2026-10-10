module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtReciprocalTransport
public import ModeStability.AllAngular.ExtremalHorizonLimits

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
theorem ser_horizon_current {M Q e ω L b : ℝ}
    (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω) (hL : 0 ≤ L)
    (hKa : radialK e ω (outerHorizon M Q) < 0) (hN : 2 * M ≤ e / ω)
    (hb : outerHorizon M Q < b) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R T : ℝ → ℂ} (hEq : EqOn R T (Ioo (outerHorizon M Q) b))
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
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
  let f := fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
    Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)
  have hKM : radialK e ω M ≠ 0 := by
    have hh := hKa.ne
    rwa [outerHorizon_of_abs_eq hQ] at hh
  have ht := extremal_reciprocal_horizon_current_tendsto_L hQ hL hKM hΘ hT hH1 hH2
  have hloc := ht.congr' (by
    have he : EqOn (fun x : ℝ => (x : ℂ) * T (M + x))
        (fun x : ℝ => (x : ℂ) * R (M + x)) (Ioo 0 (b - M)) := by
      intro x hx
      have hr : M + x ∈ Ioo (outerHorizon M Q) b := by
        rw [outerHorizon_of_abs_eq hQ]
        constructor <;> linarith [hx.1, hx.2]
      dsimp only
      rw [hEq hr]
    have hj := source_current_eqOn isOpen_Ioo he f 1
    have hbm : 0 < b - M := by rw [outerHorizon_of_abs_eq hQ] at hb; linarith
    filter_upwards [Ioo_mem_nhdsGT hbm] with x hx
    exact hj hx)
  have hcomp := hloc.comp (ser_coordinate_horizon hQ)
  apply hcomp.congr'
  obtain ⟨r₁, r₂, hr₁, -, hAH, -, -⟩ := source_radial_regions hM hQ.le hω hL hKa
  filter_upwards [Ioo_mem_nhdsGT hr₁] with r hr
  have hi : 0 < r - M := NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr.1
  have hinv : M + (r - M) = r := by ring
  have hPr : L * delta M Q r < radialK e ω r ^ 2 := by
    have hm : r ∈ {r | outerHorizon M Q < r ∧ r < e / ω ∧
        L * delta M Q r < radialK e ω r ^ 2} := by rw [hAH]; exact hr
    exact hm.2.2
  have hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L)
      (M + (r - M)) := by
    rw [hinv]
    exact (ser_coefficient_props hM hQ hω hL ha hN hr.1 hPr).1
  have hj := ser_current_jet (σ := 1) hQ hN hR hi hf
  dsimp only at hj ⊢
  rw [hinv] at hj
  unfold P61.uxR P61.uR P61.khxR at hj
  simpa only [Function.comp_apply, f, hinv, P61.uR, P61.uxR, P61.khxR, ofReal_one, one_mul] using hj

/-- Zero infinity-current limit in exact radial notation for an amplitude
equal to a homogeneous outgoing piece beyond the source support. The
interface `2Mω = e` uses its separate proved homogeneous limit. -/
theorem ser_infinity_current {M Q e ω L b : ℝ}
    (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω) (hL : 0 ≤ L)
    (hKa : radialK e ω (outerHorizon M Q) < 0) (hN : 2 * M ≤ e / ω)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R T : ℝ → ℂ} (hEq : EqOn R T (Ioi b))
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
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
  let f := fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
    Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)
  have ht : Tendsto (fun x => -(f x / deriv f x) *
      ‖deriv (fun y : ℝ => (y : ℂ) * T (M + y)) x +
        ((-1 : ℝ) : ℂ) * (f x : ℂ) * I * ((x : ℂ) * T (M + x))‖ ^ 2 -
      (deriv (fun y : ℝ => (y : ℂ) * T (M + y)) x *
        (starRingEnd ℂ) ((x : ℂ) * T (M + x))).re) atTop (𝓝 0) := by
    exact extremal_reciprocal_infinity_current_tendsto_L hM hQ hL hω.ne' hΘ hT hI1 hI2
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hloc := ht.congr' (by
    have he : EqOn (fun x : ℝ => (x : ℂ) * T (M + x))
        (fun x : ℝ => (x : ℂ) * R (M + x)) (Ioi (b - M)) := by
      intro x hx
      dsimp only
      have hx' : b - M < x := hx
      rw [hEq (show b < M + x by linarith)]
    have hj := source_current_eqOn isOpen_Ioi he f (-1)
    filter_upwards [Ioi_mem_atTop (b - M)] with x hx
    exact hj hx)
  have hcomp := hloc.comp (ser_coordinate_infinity M)
  apply hcomp.congr'
  obtain ⟨r₁, r₂, hr₁, h₁₂, -, -, hAI⟩ := source_radial_regions hM hQ.le hω hL hKa
  filter_upwards [Ioi_mem_atTop r₂] with r hr
  have hra := hr₁.trans_le h₁₂ |>.trans hr
  have hi : 0 < r - M := NormalizationFacts.sub_M_pos_of_outerHorizon_lt hra
  have hinv : M + (r - M) = r := by ring
  have hPr : L * delta M Q r < radialK e ω r ^ 2 := by
    have hm : r ∈ {r | e / ω < r ∧ L * delta M Q r < radialK e ω r ^ 2} := by
      rw [hAI]; exact hr
    exact hm.2
  have hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L)
      (M + (r - M)) := by
    rw [hinv]
    exact (ser_coefficient_props hM hQ hω hL ha hN hra hPr).1
  have hj := ser_current_jet (σ := -1) hQ hN hR hi hf
  dsimp only at hj ⊢
  rw [hinv] at hj
  unfold P61.uxR P61.uR P61.khxR at hj
  simpa only [Function.comp_apply, f, hinv, P61.uR, P61.uxR, P61.khxR,
    ofReal_neg, ofReal_one, neg_one_mul, neg_mul, one_mul, ← sub_eq_add_neg] using hj

end ModeStability.AllAngular

end
