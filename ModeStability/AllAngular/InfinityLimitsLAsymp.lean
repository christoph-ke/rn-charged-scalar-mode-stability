module

public import ModeStability.AllAngular.InfinityLimitsLAux

/-!
# Asymptotics at infinity for the current with angular term

Real-variable asymptotics as `r → ∞` behind the infinity half of (4.4) and the interface
expansion (4.5) of the all-angular research notes in preparation, Section 4, pp. 5–6, stated for
an
abstract gauge function `g` with `r g → 1` (both `g = h` and the extremal `g = 1/(r − M)`), with
`K = ωr² − er`, `K' = 2ωr − e`, `S = K² − LΔ` and

`N = ΔKK' − LΔ(r − M) − 2 g⁻¹ S`,

so that in the reciprocal normalization `k̂/k̂_x = x² S/N` at `x = 1/g`.

* `il_coef_tendsto_of_ne`: if `(gΔK' − 2K)/r → −c` with `c ≠ 0`, then `gS/N → 0`
  (`k̂_x ~ −c/x²`, the case `C = −c > 0` of p. 6);
* `il_coef_tendsto_of_eq`: if `gΔK' − 2K → ℓ` with `ωℓ + L ≠ 0`, then `gS/N → ω²/(ωℓ + L)`
  (the interface (4.5): `ℓ = 2ω(M² + 2Q²)/3`, `ωℓ + L = 2ωD`, `D = ω(M² + 2Q²)/3 + L/(2ω)`);
* `il_constant_coef_tendsto`: `−S/(Δ(KK' − L(r − M))) → 0`, the constant-normalization ratio
  `f̂/f̂_y = O(1/r)`;
* `il_reciprocal_isBigO`, `il_constant_isBigO`: the brackets expressing `|U' − ik̂U|` through the
  Θ-profile `R̃` of (1.5) are bounded, given `R̃ → B` and `R̃' = O(r⁻²)`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-! ### Elementary algebra -/

/-- `rg(S/r⁴)/N₄ · (1/r) = gS/N` when `N = r⁴N₄`. -/
theorem il_div_eq_of_four {g S N N4 r : ℝ} (hr : r ≠ 0) (hN : N = r ^ 4 * N4) :
    r * g * (S / r ^ 4) / N4 * (1 / r) = g * S / N := by
  subst hN
  rcases eq_or_ne N4 0 with h | h
  · simp [h]
  · field_simp

/-- `rg(S/r⁴)/N₃ = gS/N` when `N = r³N₃`. -/
theorem il_div_eq_of_three {g S N N3 r : ℝ} (hr : r ≠ 0) (hN : N = r ^ 3 * N3) :
    r * g * (S / r ^ 4) / N3 = g * S / N := by
  subst hN
  rcases eq_or_ne N3 0 with h | h
  · simp [h]
  · field_simp

/-- `−(S/r⁴)/((Δ/r²)G₃) · (1/r) = −S/(ΔG)` when `G = r³G₃`. -/
theorem il_div_eq_constant {S Δ G G3 r : ℝ} (hr : r ≠ 0) (hG : G = r ^ 3 * G3) :
    -(S / r ^ 4 / (Δ / r ^ 2 * G3)) * (1 / r) = -S / (Δ * G) := by
  subst hG
  rcases eq_or_ne Δ 0 with h | h
  · simp [h]
  rcases eq_or_ne G3 0 with h' | h'
  · simp [h']
  field_simp

/-! ### The coefficient `k̂/k̂_x` -/

/-- `1/(rg) → 1` from `rg → 1`. -/
theorem il_tendsto_one_div_mul {g : ℝ → ℝ} (hrg : Tendsto (fun r => r * g r) atTop (𝓝 1)) :
    Tendsto (fun r => 1 / (r * g r)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).div hrg one_ne_zero
  rwa [div_one] at h

/-- If `(gΔK' − 2K)/r → −c` with `c ≠ 0` and `ω ≠ 0`, then `gS/N → 0`. -/
theorem il_coef_tendsto_of_ne {M Q e ω L c : ℝ} (hω : ω ≠ 0) (hc : c ≠ 0) {g : ℝ → ℝ}
    (hrg : Tendsto (fun r => r * g r) atTop (𝓝 1))
    (hK : Tendsto (fun r => (g r * delta M Q r * (2 * ω * r - e) - 2 * radialK e ω r) / r)
      atTop (𝓝 (-c))) :
    Tendsto (fun r => g r * (radialK e ω r ^ 2 - L * delta M Q r) /
        (delta M Q r * radialK e ω r * (2 * ω * r - e) - L * delta M Q r * (r - M) -
          2 * (1 / g r) * (radialK e ω r ^ 2 - L * delta M Q r))) atTop (𝓝 0) := by
  have hi : Tendsto (fun r : ℝ => 1 / r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hirg := il_tendsto_one_div_mul hrg
  have hN4 := (((Infinity.tendsto_radialK_div_sq e ω).mul hirg).mul hK).sub
    (((il_tendsto_delta_div_sq M Q).const_mul L).mul
      ((hi.sub ((hi.const_mul M).mul hi)).sub ((hirg.const_mul 2).mul hi)))
  have hlim : ω * 1 * -c - L * 1 * (0 - M * 0 * 0 - 2 * 1 * 0) = -(c * ω) := by ring
  rw [hlim] at hN4
  have h := ((hrg.mul (il_tendsto_radicand_div M Q e ω L)).div hN4
    (neg_ne_zero.2 (mul_ne_zero hc hω))).mul hi
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hrg.eventually_ne one_ne_zero] with r hr hrg0
  have hg0 : g r ≠ 0 := right_ne_zero_of_mul hrg0
  have hr0 : r ≠ 0 := hr.ne'
  exact il_div_eq_of_four hr0 (by field_simp; ring)

/-- If `gΔK' − 2K → ℓ` with `ωℓ + L ≠ 0`, then `gS/N → ω²/(ωℓ + L)`. -/
theorem il_coef_tendsto_of_eq {M Q e ω L ℓ : ℝ} (hℓ : ω * ℓ + L ≠ 0) {g : ℝ → ℝ}
    (hrg : Tendsto (fun r => r * g r) atTop (𝓝 1))
    (hK : Tendsto (fun r => g r * delta M Q r * (2 * ω * r - e) - 2 * radialK e ω r)
      atTop (𝓝 ℓ)) :
    Tendsto (fun r => g r * (radialK e ω r ^ 2 - L * delta M Q r) /
        (delta M Q r * radialK e ω r * (2 * ω * r - e) - L * delta M Q r * (r - M) -
          2 * (1 / g r) * (radialK e ω r ^ 2 - L * delta M Q r))) atTop
      (𝓝 (ω ^ 2 / (ω * ℓ + L))) := by
  have hi : Tendsto (fun r : ℝ => 1 / r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hirg := il_tendsto_one_div_mul hrg
  have hN3 := (((Infinity.tendsto_radialK_div_sq e ω).mul hirg).mul hK).sub
    (((il_tendsto_delta_div_sq M Q).const_mul L).mul
      (((tendsto_const_nhds (x := (1 : ℝ))).sub (hi.const_mul M)).sub (hirg.const_mul 2)))
  have hlim : ω * 1 * ℓ - L * 1 * (1 - M * 0 - 2 * 1) = ω * ℓ + L := by ring
  rw [hlim] at hN3
  have h := (hrg.mul (il_tendsto_radicand_div M Q e ω L)).div hN3 hℓ
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hrg.eventually_ne one_ne_zero] with r hr hrg0
  have hg0 : g r ≠ 0 := right_ne_zero_of_mul hrg0
  have hr0 : r ≠ 0 := hr.ne'
  exact il_div_eq_of_three hr0 (by field_simp; ring)

/-- The constant-normalization ratio: `−S/(Δ(KK' − L(r − M))) → 0` for `ω ≠ 0`. -/
theorem il_constant_coef_tendsto {M Q e ω L : ℝ} (hω : ω ≠ 0) :
    Tendsto (fun r => -(radialK e ω r ^ 2 - L * delta M Q r) /
      (delta M Q r * (radialK e ω r * (2 * ω * r - e) - L * (r - M)))) atTop (𝓝 0) := by
  have hi : Tendsto (fun r : ℝ => 1 / r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hG := ((Infinity.tendsto_radialK_div_sq e ω).mul (il_tendsto_radialK'_div e ω)).sub
    ((hi.const_mul L).mul (hi.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub (hi.const_mul M))))
  have hlim : ω * (2 * ω) - L * 0 * (0 * (1 - M * 0)) = 2 * ω ^ 2 := by ring
  rw [hlim] at hG
  have hD := (il_tendsto_delta_div_sq M Q).mul hG
  rw [one_mul] at hD
  have h := ((il_tendsto_radicand_div M Q e ω L).div hD (by positivity)).neg.mul hi
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hr0 : r ≠ 0 := hr.ne'
  exact il_div_eq_constant hr0 (by field_simp)

/-! ### The brackets -/

/-- `K − K̂ = O(1)` from `|K − K̂| ≤ LΔ/|K|`, `ω ≠ 0`. -/
theorem il_isBigO_sub_Kh {M Q e ω L : ℝ} (hω : ω ≠ 0) {Kh : ℝ → ℝ}
    (hKh : ∀ᶠ r in atTop, |radialK e ω r - Kh r| ≤ L * delta M Q r / |radialK e ω r|) :
    (fun r => radialK e ω r - Kh r) =O[atTop] (fun _ => (1 : ℝ)) := by
  have hlim : Tendsto (fun r => L * delta M Q r / |radialK e ω r|) atTop
      (𝓝 (L * 1 / |ω|)) := by
    have h := ((il_tendsto_delta_div_sq M Q).const_mul L).div
      ((Infinity.tendsto_radialK_div_sq e ω).abs) (abs_pos.2 hω).ne'
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    simp only [Pi.div_apply]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < r ^ 2)]
    field_simp
  refine (IsBigO.of_bound' ?_).trans (hlim.isBigO_one ℝ)
  filter_upwards [hKh] with r hr
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact hr.trans (le_abs_self _)

/-- `r² R̃' = O(1)` from `R̃' = O(r⁻²)`. -/
theorem il_isBigO_sq_mul_deriv {F : ℝ → ℂ}
    (hF' : deriv F =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    (fun r : ℝ => (r : ℂ) ^ 2 * deriv F r) =O[atTop] (fun _ => (1 : ℝ)) := by
  have h := (isBigO_of_le atTop (fun r : ℝ =>
    (le_of_eq (by rw [norm_pow, Complex.norm_real, norm_pow]) :
      ‖(r : ℂ) ^ 2‖ ≤ ‖r ^ 2‖))).mul hF'
  refine h.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  field_simp

/-- Reciprocal normalization: the bracket `T(r − gΔ) + (gΔ/r)(r²T') + i rg(K − K̂)T` times
`(1/(rg))²` and the amplitude `|T|/(rg)` are bounded, given `rg → 1`, `r − gΔ → M`,
`|K − K̂| ≤ LΔ/|K|`, `T → B` and `T' = O(r⁻²)`. -/
theorem il_reciprocal_isBigO {M Q e ω L : ℝ} (hω : ω ≠ 0) {g Kh : ℝ → ℝ}
    (hrg : Tendsto (fun r => r * g r) atTop (𝓝 1))
    (hgΔ : Tendsto (fun r => r - g r * delta M Q r) atTop (𝓝 M))
    (hKh : ∀ᶠ r in atTop, |radialK e ω r - Kh r| ≤ L * delta M Q r / |radialK e ω r|)
    {F : ℝ → ℂ} {B : ℂ} (hF : Tendsto F atTop (𝓝 B))
    (hF' : deriv F =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    (fun r : ℝ => ‖F r * ((r - g r * delta M Q r : ℝ) : ℂ) +
        ((g r * delta M Q r / r : ℝ) : ℂ) * ((r : ℂ) ^ 2 * deriv F r) +
        I * ((r * g r * (radialK e ω r - Kh r) : ℝ) : ℂ) * F r‖ * (1 / (r * g r)) ^ 2)
      =O[atTop] (fun _ => (1 : ℝ)) ∧
    (fun r : ℝ => ‖F r‖ * (1 / (r * g r))) =O[atTop] (fun _ => (1 : ℝ)) := by
  have hF0 : F =O[atTop] (fun _ => (1 : ℝ)) := hF.isBigO_one ℝ
  have hirg := (il_tendsto_one_div_mul hrg).isBigO_one ℝ
  have hgΔr : Tendsto (fun r => g r * delta M Q r / r) atTop (𝓝 1) := by
    have h := hrg.mul (il_tendsto_delta_div_sq M Q)
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    field_simp
  have h1 : (fun r => F r * ((r - g r * delta M Q r : ℝ) : ℂ)) =O[atTop]
      (fun _ => (1 : ℝ)) := by
    simpa only [mul_one] using hF0.mul (hgΔ.ofReal.isBigO_one ℝ)
  have h2 : (fun r => ((g r * delta M Q r / r : ℝ) : ℂ) * ((r : ℂ) ^ 2 * deriv F r)) =O[atTop]
      (fun _ => (1 : ℝ)) := by
    simpa only [mul_one] using (hgΔr.ofReal.isBigO_one ℝ).mul (il_isBigO_sq_mul_deriv hF')
  have h4 : (fun r : ℝ => ((r * g r * (radialK e ω r - Kh r) : ℝ) : ℂ)) =O[atTop]
      (fun _ => (1 : ℝ)) := by
    refine isBigO_ofReal_left.2 ?_
    simpa only [mul_one] using (hrg.isBigO_one ℝ).mul (il_isBigO_sub_Kh hω hKh)
  have h3 : (fun r => I * ((r * g r * (radialK e ω r - Kh r) : ℝ) : ℂ) * F r) =O[atTop]
      (fun _ => (1 : ℝ)) := by
    simpa only [mul_one] using ((isBigO_const_one ℝ I atTop).mul h4).mul hF0
  constructor
  · simpa only [one_pow, mul_one] using ((h1.add h2).add h3).norm_left.mul (hirg.pow 2)
  · simpa only [mul_one] using hF0.norm_left.mul hirg

/-- Constant normalization: the bracket `−(Δ/r²)(rT') + (Δ/r²)T − i((K − K̂)/r)T` is bounded and
`|T|/r → 0`, given `|K − K̂| ≤ LΔ/|K|`, `T → B` and `T' = O(r⁻²)`. -/
theorem il_constant_isBigO {M Q e ω L : ℝ} (hω : ω ≠ 0) {Kh : ℝ → ℝ}
    (hKh : ∀ᶠ r in atTop, |radialK e ω r - Kh r| ≤ L * delta M Q r / |radialK e ω r|)
    {F : ℝ → ℂ} {B : ℂ} (hF : Tendsto F atTop (𝓝 B))
    (hF' : deriv F =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    (fun r : ℝ => ‖-(((delta M Q r / r ^ 2 : ℝ) : ℂ) * ((r : ℂ) * deriv F r)) +
        ((delta M Q r / r ^ 2 : ℝ) : ℂ) * F r -
        I * (((radialK e ω r - Kh r) / r : ℝ) : ℂ) * F r‖) =O[atTop] (fun _ => (1 : ℝ)) ∧
    Tendsto (fun r : ℝ => ‖F r‖ * (1 / r)) atTop (𝓝 0) := by
  have hi : Tendsto (fun r : ℝ => 1 / r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hF0 : F =O[atTop] (fun _ => (1 : ℝ)) := hF.isBigO_one ℝ
  have hΔ := ((il_tendsto_delta_div_sq M Q).ofReal).isBigO_one ℝ
  have hrF : (fun r : ℝ => (r : ℂ) * deriv F r) =O[atTop] (fun _ => (1 : ℝ)) := by
    have hO : (fun r : ℝ => (r : ℂ) * deriv F r) =O[atTop] (fun r : ℝ => r * (r ^ 2)⁻¹) :=
      (isBigO_of_le atTop (fun r => (Complex.norm_real r).le)).mul hF'
    refine (hO.trans_tendsto (tendsto_inv_atTop_zero.congr' ?_)).isBigO_one ℝ
    filter_upwards [eventually_gt_atTop 0] with r hr
    field_simp
  have h1 : (fun r : ℝ => -(((delta M Q r / r ^ 2 : ℝ) : ℂ) * ((r : ℂ) * deriv F r)))
      =O[atTop] (fun _ => (1 : ℝ)) := by
    simpa only [mul_one] using (hΔ.mul hrF).neg_left
  have h2 : (fun r : ℝ => ((delta M Q r / r ^ 2 : ℝ) : ℂ) * F r) =O[atTop] (fun _ => (1 : ℝ)) := by
    simpa only [mul_one] using hΔ.mul hF0
  have h4 : (fun r : ℝ => (((radialK e ω r - Kh r) / r : ℝ) : ℂ)) =O[atTop]
      (fun _ => (1 : ℝ)) := by
    refine isBigO_ofReal_left.2 ?_
    refine (((il_isBigO_sub_Kh hω hKh).mul (hi.isBigO_one ℝ)).congr_left fun r => ?_).trans
      (isBigO_refl _ _ |>.congr_right fun _ => mul_one 1)
    rw [mul_one_div]
  have h3 : (fun r => I * (((radialK e ω r - Kh r) / r : ℝ) : ℂ) * F r) =O[atTop]
      (fun _ => (1 : ℝ)) := by
    simpa only [mul_one] using ((isBigO_const_one ℝ I atTop).mul h4).mul hF0
  refine ⟨((h1.add h2).sub h3).norm_left, ?_⟩
  have h := (hF.norm).mul hi
  rwa [mul_zero] at h

end ModeStability.AllAngular

end
