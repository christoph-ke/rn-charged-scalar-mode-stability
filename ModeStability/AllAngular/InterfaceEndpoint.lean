module

public import ModeStability.Endpoint.Infinity
public import ModeStability.AllAngular.InterfaceEndpointAux

/-!
# The infinity endpoint limit of the dephased current at the interface `r₀ = 2M`

the all-angular research notes in preparation, p. 6, (4.5), for `L = 0`, in the reciprocal
normalization `x = 1/g`, `U(x) = x R(r(x))`, `k = transformedK` of
the spherical research notes in preparation, (2.2)–(2.6): at the interface
`c = 2Mω − e = 0` (corotation radius `r₀ = e/ω = 2M`), for a solution `R` of (1.2) with the
outgoing condition (1.4), the current `J[v_I]` of `v_I = e^{−iϑ} U` tends to `0` as `x → ∞`
(`interface_infinity_current_tendsto`). This complements
`Endpoint.infinity_current_tendsto`, which covers `c ≠ 0`.

Route. As in `ModeStability.Endpoint.Infinity`, `J(x) = Φ(r(x))`
(`Endpoint.dephasedCurrent_eq_infinity`), and at `c = 0` the profile of (1.4) is
`R̃ = r e^{−iωr} R`; `Φ` is rewritten in terms of `R̃` (`iface_current_eq_profile`). At
`c = 0`, `g Δ K' − 2K` no longer grows like `−c r` but tends to `2ω(M² + 2Q²)/3 ≠ 0`
(`iface_tendsto_staticSolution_mul_delta_mul_sub`, the coefficient `2D` of (4.5)), so
`|k/k_x| = O(r³)`. On the other hand the bracket `X` with `|U' − ikU| = |X|/r` is `O(r⁻¹)`
(`iface_isBigO_profile`): `1 − gΔ/r = O(r⁻¹)`, `g Q²ω = O(r⁻¹)`, `(gΔ/r) r R̃' = O(r⁻¹)`.
Hence the first part of `J` is `O(r⁻¹)`, and the part `−Re(U'Ū)` tends to `0` as for `c ≠ 0`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- The derivative of the profile `R̃(r) = r e^{−iωr} R(r)` of (1.4) at `c = 0`:
`R̃' = e^{−iωr} (R (1 − iωr) + r R')`. -/
theorem iface_hasDerivAt_profile (ω : ℝ) {R : ℝ → ℂ} {r : ℝ} (hR : DifferentiableAt ℝ R r) :
    HasDerivAt (fun r : ℝ => (r : ℂ) * exp (-(I * ω * r)) * R r)
      (exp (-(I * ω * r)) * (R r * (1 - I * ω * r) + r * deriv R r)) r := by
  have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := by
    simpa only [id_eq, ofReal_one] using (hasDerivAt_id r).ofReal_comp
  have h2 : HasDerivAt (fun r : ℝ => exp (-(I * ω * r))) (exp (-(I * ω * r)) * (-(I * ω))) r := by
    have : HasDerivAt (fun r : ℝ => -(I * ω * (r : ℂ))) (-(I * ω * 1)) r :=
      (h1.const_mul (I * ω)).neg
    simpa only [mul_neg, mul_one] using this.cexp
  have h4 := (h1.mul h2).mul hR.hasDerivAt
  convert h4 using 1
  simp only [Pi.mul_apply]
  ring

/-- For `r > a` and `c = 2Mω − e = 0`, the right side of `Endpoint.dephasedCurrent_eq_infinity`
in terms of the profile `F = R̃` of (1.4), arranged for the limit `r → ∞`. -/
theorem iface_current_eq_profile {M Q q ω : ℝ} (hQ : |Q| < M) (hc : 2 * M * ω - q * Q = 0)
    {R F : ℝ → ℂ} (hR : IsRadialSolution M Q q ω R)
    (hF : F = fun r : ℝ =>
      (r : ℂ) * exp (-(I * ω * r)) * (r : ℂ) ^ (-(I * (2 * M * ω - q * Q))) * R r)
    {r : ℝ} (hr : outerHorizon M Q < r) :
    -(radialK (q * Q) ω r / (staticSolution M Q r * (staticSolution M Q r * delta M Q r *
          (2 * ω * r - q * Q) - 2 * radialK (q * Q) ω r))) *
        ‖R r + staticSolution M Q r * delta M Q r * deriv R r -
          I * staticSolution M Q r * radialK (q * Q) ω r * R r‖ ^ 2 -
      (‖R r‖ ^ 2 / staticSolution M Q r +
        delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).re) =
    -(radialK (q * Q) ω r / r ^ 2 / (r * staticSolution M Q r *
        ((staticSolution M Q r * delta M Q r * (2 * ω * r - q * Q) -
          2 * radialK (q * Q) ω r) / r))) *
        ‖F r * ((1 - staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) +
          I * F r * ((staticSolution M Q r * (Q ^ 2 * ω) : ℝ) : ℂ) +
          ((staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) * (r * deriv F r)‖ ^ 2 -
      ‖F r‖ ^ 2 / r * (r * staticSolution M Q r)⁻¹ -
      delta M Q r / r ^ 2 * ((deriv F r * (starRingEnd ℂ) (F r)).re - ‖F r‖ ^ 2 / r) := by
  have hr0 : 0 < r := (Infinity.outerHorizon_pos_of_abs_lt hQ).trans hr
  have hg := staticSolution_pos hQ hr
  have hs : -(I * (2 * M * ω - q * Q : ℂ)) = 0 := by
    have : (2 * M * ω - q * Q : ℂ) = ((2 * M * ω - q * Q : ℝ) : ℂ) := by push_cast; ring
    rw [this, hc, ofReal_zero, mul_zero, neg_zero]
  have hF' : F = fun r : ℝ => (r : ℂ) * exp (-(I * ω * r)) * R r := by
    rw [hF, hs]
    funext s
    rw [cpow_zero, mul_one]
  have hp : ‖exp (-(I * ω * r))‖ = 1 := by
    simpa only [ofReal_zero, mul_zero, neg_zero, cpow_zero, mul_one] using
      Endpoint.norm_exp_mul_cpow (ω := ω) hr0 0
  have hT : F r = r * exp (-(I * ω * r)) * R r := by rw [hF']
  have hT' : deriv F r = exp (-(I * ω * r)) *
      (R r * (1 - I * ω * r - I * ((0 : ℝ) : ℂ)) + r * deriv R r) := by
    rw [hF', (iface_hasDerivAt_profile ω (hR r hr).1).deriv, ofReal_zero, mul_zero, sub_zero]
  have hK : radialK (q * Q) ω r = ω * r ^ 2 - q * Q * r := rfl
  rw [Endpoint.norm_eq_norm_div_of_profile hr0 hp (Infinity.delta_eq_poly hQ r) hK hc.symm hT hT',
    Endpoint.re_identity_of_profile hr0 hg hp hT hT']
  have hz : Q ^ 2 * ω - 2 * M * 0 + Q ^ 2 * 0 / r = Q ^ 2 * ω := by ring
  rw [hz]
  have hD : r * staticSolution M Q r * ((staticSolution M Q r * delta M Q r *
      (2 * ω * r - q * Q) - 2 * radialK (q * Q) ω r) / r) =
      staticSolution M Q r * (staticSolution M Q r * delta M Q r *
      (2 * ω * r - q * Q) - 2 * radialK (q * Q) ω r) := by
    field_simp
  rw [hD]
  ring

/-- The bracket of `iface_current_eq_profile` is `O(r⁻¹)`: `r X = O(1)`, given the outgoing
condition (1.4) for the profile `F`: `F − B = O(r⁻¹)`, `F' = O(r⁻²)`. -/
theorem iface_isBigO_profile {M Q ω : ℝ} (hQ : |Q| < M) {F : ℝ → ℂ} {B : ℂ}
    (hT : Tendsto F atTop (𝓝 B)) (hF2 : deriv F =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    (fun r : ℝ => (r : ℂ) * (F r * ((1 - staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) +
        I * F r * ((staticSolution M Q r * (Q ^ 2 * ω) : ℝ) : ℂ) +
        ((staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) * (r * deriv F r)))
      =O[atTop] (fun _ => (1 : ℝ)) := by
  have h1 : Tendsto (fun r => r - staticSolution M Q r * delta M Q r) atTop (𝓝 M) := by
    have h := (Infinity.tendsto_staticSolution_mul_delta_sub hQ).neg
    rw [neg_neg] at h
    exact h.congr fun r => by ring
  have hP1 : Tendsto (fun r : ℝ => F r * ((r - staticSolution M Q r * delta M Q r : ℝ) : ℂ) +
      I * F r * ((r * staticSolution M Q r * (Q ^ 2 * ω) : ℝ) : ℂ)) atTop
      (𝓝 (B * (M : ℂ) + I * B * ((1 * (Q ^ 2 * ω) : ℝ) : ℂ))) :=
    (hT.mul h1.ofReal).add (((tendsto_const_nhds (x := I)).mul hT).mul
      ((Infinity.tendsto_mul_staticSolution hQ).mul_const (Q ^ 2 * ω)).ofReal)
  have hr2 : (fun r : ℝ => (r : ℂ) ^ 2 * deriv F r) =O[atTop] (fun _ => (1 : ℝ)) := by
    have h := (isBigO_of_le atTop (fun r : ℝ =>
      (le_of_eq (by rw [norm_pow, Complex.norm_real, norm_pow]) :
        ‖(r : ℂ) ^ 2‖ ≤ ‖r ^ 2‖))).mul hF2
    refine h.congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    field_simp
  have hP2 : (fun r : ℝ => ((staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) *
      ((r : ℂ) ^ 2 * deriv F r)) =O[atTop] (fun _ => (1 : ℝ)) := by
    have h := ((Infinity.tendsto_staticSolution_mul_delta_div hQ).ofReal.isBigO_one ℝ).mul hr2
    simpa only [mul_one] using h
  refine ((hP1.isBigO_one ℝ).add hP2).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  push_cast
  field_simp

/-- The limit `r → ∞` of the right side of `iface_current_eq_profile` at `c = 0`, `ω ≠ 0`,
given the outgoing condition (1.4) for the profile `F`: `F − B = O(r⁻¹)`, `F' = O(r⁻²)`. -/
theorem iface_tendsto_current_profile {M Q q ω : ℝ} (hQ : |Q| < M) (hω : ω ≠ 0)
    (hc : 2 * M * ω - q * Q = 0) {F : ℝ → ℂ} {B : ℂ}
    (hF1 : (fun r => F r - B) =O[atTop] (fun r : ℝ => r⁻¹))
    (hF2 : deriv F =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    Tendsto (fun r : ℝ =>
      -(radialK (q * Q) ω r / r ^ 2 / (r * staticSolution M Q r *
        ((staticSolution M Q r * delta M Q r * (2 * ω * r - q * Q) -
          2 * radialK (q * Q) ω r) / r))) *
        ‖F r * ((1 - staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) +
          I * F r * ((staticSolution M Q r * (Q ^ 2 * ω) : ℝ) : ℂ) +
          ((staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) * (r * deriv F r)‖ ^ 2 -
      ‖F r‖ ^ 2 / r * (r * staticSolution M Q r)⁻¹ -
      delta M Q r / r ^ 2 * ((deriv F r * (starRingEnd ℂ) (F r)).re - ‖F r‖ ^ 2 / r))
      atTop (𝓝 0) := by
  have hT : Tendsto F atTop (𝓝 B) := by
    have h := (hF1.trans_tendsto tendsto_inv_atTop_zero).add_const B
    simpa only [sub_add_cancel, zero_add] using h
  have hT' : Tendsto (deriv F) atTop (𝓝 0) :=
    hF2.trans_tendsto (tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop
  have hRX := iface_isBigO_profile (ω := ω) hQ hT hF2
  have hsmall : Tendsto (fun r : ℝ => ‖(r : ℂ) * (F r *
      ((1 - staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) +
        I * F r * ((staticSolution M Q r * (Q ^ 2 * ω) : ℝ) : ℂ) +
        ((staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) * (r * deriv F r))‖ ^ 2 * r⁻¹)
      atTop (𝓝 0) := by
    have h := (hRX.norm_left.pow 2).mul (isBigO_refl (fun r : ℝ => r⁻¹) atTop)
    refine h.trans_tendsto ?_
    simpa only [one_pow, one_mul] using tendsto_inv_atTop_zero
  have hN := iface_tendsto_staticSolution_mul_delta_mul_sub hQ hc
  have hN0 : 2 * ω * ((M ^ 2 + 2 * Q ^ 2) / 3) ≠ 0 := by
    have : 0 < (M ^ 2 + 2 * Q ^ 2) / 3 := by
      have : 0 < M := lt_of_le_of_lt (abs_nonneg Q) hQ
      positivity
    exact mul_ne_zero (mul_ne_zero two_ne_zero hω) this.ne'
  have hrg := Infinity.tendsto_mul_staticSolution hQ
  have h1 := (((Infinity.tendsto_radialK_div_sq (q * Q) ω).div hrg one_ne_zero).div hN hN0).neg.mul
    hsmall
  have hA := ((hT.norm.pow 2).div_atTop tendsto_id).mul (hrg.inv₀ one_ne_zero)
  have hRe : Tendsto (fun r => (deriv F r * (starRingEnd ℂ) (F r)).re) atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto _).comp
      (hT'.mul ((Complex.continuous_conj.tendsto B).comp hT))
    convert h using 2
    · simp only [mul_re, conj_re, conj_im, mul_neg, sub_neg_eq_add, Function.comp_apply]
    · simp only [zero_mul, zero_re]
  have hC := (Infinity.tendsto_delta_div_sq hQ).mul
    (hRe.sub ((hT.norm.pow 2).div_atTop tendsto_id))
  have h := ((h1.sub hA).sub hC).mono_right
    (le_of_eq (congrArg 𝓝 (by norm_num : _ = (0 : ℝ))))
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (outerHorizon M Q),
    hN.eventually_ne hN0] with r hr hNr
  have hr0 : 0 < r := (Infinity.outerHorizon_pos_of_abs_lt hQ).trans hr
  have hg := staticSolution_pos hQ hr
  simp only [Pi.div_apply, id]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  field_simp

/-- **The infinity endpoint limit at the interface `r₀ = 2M`** (all-angular paper, (4.5), for
`L = 0`). For a solution `R` of (1.2) satisfying the outgoing condition (1.4) with
`c = 2Mω − e = 0` and `ω ≠ 0`, the current `J[v_I]` of `v_I = e^{−iϑ} U`,
`U(x) = x R(r(x))`, tends to `0` as `x → ∞`. -/
theorem interface_infinity_current_tendsto {M Q q ω : ℝ} (_hM : 0 < M) (hQ : |Q| < M)
    (hω : ω ≠ 0) (hc : 2 * M * ω - q * Q = 0) {x₀ : ℝ} (hx₀ : 0 < x₀)
    {R : ℝ → ℂ} {B : ℂ} (hR : IsRadialSolution M Q q ω R) (hI : InfinityCondition M Q q ω R B) :
    Tendsto (dephasedCurrent (transformedK M Q q ω)
        (dephase (transformedK M Q q ω) x₀ (-1) (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))))
      atTop (𝓝 0) := by
  obtain ⟨hF1, hF2⟩ := hI
  have hlim := (iface_tendsto_current_profile hQ hω hc hF1 hF2).comp
    (Infinity.tendsto_radiusOf_atTop hQ)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Endpoint.dephasedCurrent_eq_infinity hQ hx₀ hR hx rfl,
    iface_current_eq_profile hQ hc hR rfl (outerHorizon_lt_radiusOf hQ hx)]
  rfl

end ModeStability.AllAngular

end
