module

public import ModeStability.Endpoint.Common
public import ModeStability.Endpoint.InfinityAux
public import ModeStability.Exterior.Reduction
public import ModeStability.Frozen.InfinityCondition

/-!
# The infinity endpoint limit of the dephased current

The limit (2.14)–(2.15) of the spherical research notes in preparation: for a solution `R`
of (1.2) satisfying the outgoing condition (1.4) at infinity and `c = 2Mω − e ≠ 0`, the current
`J[v_I]` of `v_I = e^{−iϑ} U`, `U(x) = x R(r(x))`, tends to `0` as `x → ∞`
(`infinity_current_tendsto`).

Route. For `x > 0` and `r = r(x)`, `J(x) = Φ(r)` with
`Φ = −(K/(g(gΔK' − 2K))) |R + gΔR' − igKR|² − (|R|²/g + Δ Re(R'R̄))`
(`dephasedCurrent_eq_infinity`). In terms of the profile `R̃ = r e^{−iωr} r^{−ic} R` of (1.4),
`|R + gΔR' − igKR| = |X|/r` with
`X = R̃(1 − gΔ/r) + i R̃ g(Q²ω − 2Mc + Q²c/r) + (gΔ/r)(r R̃')` (`norm_eq_norm_div_of_profile`),
using the exact cancellation `Δ(ω + c/r) − K = Q²ω − 2Mc + Q²c/r`, and
`|R|²/g + Δ Re(R'R̄) = (|R̃|²/r)(rg)⁻¹ + (Δ/r²)(Re(R̃' R̃̄) − |R̃|²/r)`
(`re_identity_of_profile`). Each term then tends to `0` by the asymptotics of `g` at infinity
(`ModeStability.Endpoint.InfinityAux`).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Endpoint

/-- The derivative of the profile `R̃(r) = r e^{−iωr} r^s R(r)` of (1.4):
`R̃' = e^{−iωr} r^s (R (1 − iωr + s) + r R')`. -/
theorem hasDerivAt_infinityProfile (ω : ℝ) {s : ℂ} (hs : s ≠ 0) {R : ℝ → ℂ} {r : ℝ}
    (hr : 0 < r) (hR : DifferentiableAt ℝ R r) :
    HasDerivAt (fun r : ℝ => (r : ℂ) * exp (-(I * ω * r)) * (r : ℂ) ^ s * R r)
      (exp (-(I * ω * r)) * (r : ℂ) ^ s * (R r * (1 - I * ω * r + s) + r * deriv R r)) r := by
  have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := by
    simpa only [id_eq, ofReal_one] using (hasDerivAt_id r).ofReal_comp
  have h2 : HasDerivAt (fun r : ℝ => exp (-(I * ω * r))) (exp (-(I * ω * r)) * (-(I * ω))) r := by
    have : HasDerivAt (fun r : ℝ => -(I * ω * (r : ℂ))) (-(I * ω * 1)) r :=
      (h1.const_mul (I * ω)).neg
    simpa only [mul_neg, mul_one] using this.cexp
  have h3 := hasDerivAt_ofReal_cpow_const hr.ne' hs
  have h4 := ((h1.mul h2).mul h3).mul hR.hasDerivAt
  convert h4 using 1
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  rw [Complex.cpow_sub _ _ hr', cpow_one]
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- The unimodular factor `e^{−iωr} r^{−ic}` has norm `1` for `r > 0`. -/
theorem norm_exp_mul_cpow {ω r : ℝ} (hr : 0 < r) (c : ℝ) :
    ‖exp (-(I * ω * r)) * (r : ℂ) ^ (-(I * c))‖ = 1 := by
  rw [norm_mul, norm_exp, norm_cpow_eq_rpow_re_of_pos hr]
  simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self, mul_im,
    one_mul, zero_add, neg_zero, Real.exp_zero, Real.rpow_zero, mul_one]

/-- The norm identity `|A + gΔA' − igKA| = |X|/r` behind (2.14), for `T = r p A`,
`T' = p (A (1 − iωr − ic) + r A')`, `|p| = 1`. -/
theorem norm_eq_norm_div_of_profile {r g Δ K M Q ω c e : ℝ} {p A A' T T' : ℂ} (hr : 0 < r)
    (hp : ‖p‖ = 1) (hΔ : Δ = r ^ 2 - 2 * M * r + Q ^ 2) (hK : K = ω * r ^ 2 - e * r)
    (hc : c = 2 * M * ω - e) (hT : T = r * p * A)
    (hT' : T' = p * (A * (1 - I * ω * r - I * c) + r * A')) :
    ‖A + g * Δ * A' - I * g * K * A‖ =
      ‖T * ((1 - g * Δ / r : ℝ) : ℂ) +
          I * T * ((g * (Q ^ 2 * ω - 2 * M * c + Q ^ 2 * c / r) : ℝ) : ℂ) +
          ((g * Δ / r : ℝ) : ℂ) * (r * T')‖ / r := by
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have key : T * ((1 - g * Δ / r : ℝ) : ℂ) +
      I * T * ((g * (Q ^ 2 * ω - 2 * M * c + Q ^ 2 * c / r) : ℝ) : ℂ) +
      ((g * Δ / r : ℝ) : ℂ) * (r * T') = (r : ℂ) * p * (A + g * Δ * A' - I * g * K * A) := by
    subst hΔ hK hc hT hT'
    push_cast
    field_simp
    ring
  rw [key, norm_mul, norm_mul, hp, Complex.norm_of_nonneg hr.le]
  field_simp

/-- The real-part identity `|A|²/g + Δ Re(A'Ā) = (|T|²/r)(rg)⁻¹ + (Δ/r²)(Re(T'T̄) − |T|²/r)`,
for `T = r p A`, `T' = p (A (1 − iωr − ic) + r A')`, `|p| = 1`. -/
theorem re_identity_of_profile {r g Δ ω c : ℝ} {p A A' T T' : ℂ} (hr : 0 < r) (hg : 0 < g)
    (hp : ‖p‖ = 1) (hT : T = r * p * A)
    (hT' : T' = p * (A * (1 - I * ω * r - I * c) + r * A')) :
    ‖A‖ ^ 2 / g + Δ * (A' * (starRingEnd ℂ) A).re =
      ‖T‖ ^ 2 / r * (r * g)⁻¹ + Δ / r ^ 2 * ((T' * (starRingEnd ℂ) T).re - ‖T‖ ^ 2 / r) := by
  have hnT : ‖T‖ = r * ‖A‖ := by
    rw [hT, norm_mul, norm_mul, hp, Complex.norm_of_nonneg hr.le, mul_one]
  have hpp : p * (starRingEnd ℂ) p = 1 := by
    rw [Complex.mul_conj', hp, ofReal_one, one_pow]
  have hprod : T' * (starRingEnd ℂ) T =
      (r : ℂ) * (‖A‖ : ℂ) ^ 2 * (1 - I * ω * r - I * c) +
        (r : ℂ) ^ 2 * (A' * (starRingEnd ℂ) A) := by
    rw [hT, hT', map_mul, map_mul, Complex.conj_ofReal, ← Complex.mul_conj']
    linear_combination ((r : ℂ) * (A * (1 - I * ω * r - I * c) + r * A') * (starRingEnd ℂ) A) * hpp
  have hre : (T' * (starRingEnd ℂ) T).re = r * ‖A‖ ^ 2 + r ^ 2 * (A' * (starRingEnd ℂ) A).re := by
    rw [hprod]
    simp only [← ofReal_pow, add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re,
      one_re, I_re, zero_mul, I_im, sub_self, mul_im, one_mul, zero_add, mul_one, add_zero, sub_im,
      one_im,
      zero_sub, conj_re, conj_im, mul_neg, sub_neg_eq_add]
  rw [hre, hnT]
  field_simp
  ring

/-- For `x > 0` and `r = r(x)`, the current of `v_I = e^{−iϑ} U` in terms of `R` at `r`:
`J(x) = −(K/(g(gΔK' − 2K))) |R + gΔR' − igKR|² − (|R|²/g + Δ Re(R'R̄))`. -/
theorem dephasedCurrent_eq_infinity {M Q q ω : ℝ} (hQ : |Q| < M) {x₀ : ℝ} (hx₀ : 0 < x₀)
    {R : ℝ → ℂ} (hR : IsRadialSolution M Q q ω R) {x r : ℝ} (hx : 0 < x)
    (hr : radiusOf M Q x = r) :
    dephasedCurrent (transformedK M Q q ω)
        (dephase (transformedK M Q q ω) x₀ (-1) (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))) x =
      -(radialK (q * Q) ω r / (staticSolution M Q r * (staticSolution M Q r * delta M Q r *
          (2 * ω * r - q * Q) - 2 * radialK (q * Q) ω r))) *
        ‖R r + staticSolution M Q r * delta M Q r * deriv R r -
          I * staticSolution M Q r * radialK (q * Q) ω r * R r‖ ^ 2 -
      (‖R r‖ ^ 2 / staticSolution M Q r +
        delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).re) := by
  have hU := hasDerivAt_reducedSolution hQ hR hx
  rw [dephasedCurrent_dephase_eq hx₀ (continuousOn_transformedK hQ) (-1) hx hU.differentiableAt,
    hU.deriv, (hasDerivAt_transformedK hQ hx).deriv, transformedK_eq_div hQ hx]
  subst hr
  rw [staticSolution_radiusOf hQ hx]
  set r := radiusOf M Q x
  set Δ := delta M Q r
  set K := radialK (q * Q) ω r
  set A := R r
  set A' := deriv R r
  have hx' : x ≠ 0 := hx.ne'
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx'
  have h1 : K / x ^ 2 / ((2 * ω * r - q * Q) * Δ / x ^ 4 - 2 * K / x ^ 3) =
      K / (1 / x * (1 / x * Δ * (2 * ω * r - q * Q) - 2 * K)) := by
    have e1 : (2 * ω * r - q * Q) * Δ / x ^ 4 - 2 * K / x ^ 3 =
        (Δ * (2 * ω * r - q * Q) - 2 * K * x) / x ^ 4 := by
      field_simp
    have e2 : 1 / x * (1 / x * Δ * (2 * ω * r - q * Q) - 2 * K) =
        (Δ * (2 * ω * r - q * Q) - 2 * K * x) / x ^ 2 := by
      field_simp
    rw [e1, e2, div_div_eq_mul_div, div_div_eq_mul_div]
    congr 1
    field_simp
  have h2 : A + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * A') + ((-1 : ℝ) : ℂ) * ((K / x ^ 2 : ℝ) : ℂ) * I *
      ((x : ℂ) * A) = A + ((1 / x : ℝ) : ℂ) * Δ * A' - I * ((1 / x : ℝ) : ℂ) * K * A := by
    push_cast
    field_simp
    ring
  have h3 : ((A + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * A')) * (starRingEnd ℂ) ((x : ℂ) * A)).re =
      ‖A‖ ^ 2 / (1 / x) + Δ * (A' * (starRingEnd ℂ) A).re := by
    have : (A + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * A')) * (starRingEnd ℂ) ((x : ℂ) * A) =
        (x : ℂ) * (‖A‖ : ℂ) ^ 2 + (Δ : ℂ) * (A' * (starRingEnd ℂ) A) := by
      rw [map_mul, Complex.conj_ofReal, ← Complex.mul_conj']
      push_cast
      field_simp
    rw [this]
    simp only [← ofReal_pow, add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, conj_re,
      conj_im, mul_neg, sub_neg_eq_add, mul_im, zero_mul, one_div, div_inv_eq_mul, add_left_inj]
    ring
  rw [h1, h2, h3]

/-- For `r > a`, the right side of `dephasedCurrent_eq_infinity` in terms of the profile
`F = R̃` of (1.4) (with `c = 2Mω − e`), arranged for the limit `r → ∞`. -/
theorem current_eq_profile {M Q q ω c : ℝ} (hQ : |Q| < M) (hc : c ≠ 0)
    (hcdef : c = 2 * M * ω - q * Q) {R F : ℝ → ℂ} (hR : IsRadialSolution M Q q ω R)
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
          I * F r * ((staticSolution M Q r * (Q ^ 2 * ω - 2 * M * c + Q ^ 2 * c / r) : ℝ) : ℂ) +
          ((staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) * (r * deriv F r)‖ ^ 2 -
      ‖F r‖ ^ 2 / r * (r * staticSolution M Q r)⁻¹ -
      delta M Q r / r ^ 2 * ((deriv F r * (starRingEnd ℂ) (F r)).re - ‖F r‖ ^ 2 / r) := by
  have hr0 : 0 < r := (Infinity.outerHorizon_pos_of_abs_lt hQ).trans hr
  have hg := staticSolution_pos hQ hr
  have hs : -(I * (2 * M * ω - q * Q : ℂ)) = -(I * (c : ℂ)) := by
    rw [hcdef]
    push_cast
    ring
  have hs0 : -(I * (2 * M * ω - q * Q : ℂ)) ≠ 0 := by
    rw [hs, neg_ne_zero]
    exact mul_ne_zero I_ne_zero (ofReal_ne_zero.2 hc)
  have hp := norm_exp_mul_cpow (ω := ω) hr0 c
  have hT : F r = r * (exp (-(I * ω * r)) * (r : ℂ) ^ (-(I * (c : ℂ)))) * R r := by
    rw [hF, ← hs]
    ring
  have hT' : deriv F r = exp (-(I * ω * r)) * (r : ℂ) ^ (-(I * (c : ℂ))) *
      (R r * (1 - I * ω * r - I * c) + r * deriv R r) := by
    rw [hF, (hasDerivAt_infinityProfile ω hs0 hr0 (hR r hr).1).deriv, hs]
    ring
  have hK : radialK (q * Q) ω r = ω * r ^ 2 - q * Q * r := rfl
  rw [norm_eq_norm_div_of_profile hr0 hp (Infinity.delta_eq_poly hQ r) hK hcdef hT hT',
    re_identity_of_profile hr0 hg hp hT hT']
  have hD : r * staticSolution M Q r * ((staticSolution M Q r * delta M Q r *
      (2 * ω * r - q * Q) - 2 * radialK (q * Q) ω r) / r) =
      staticSolution M Q r * (staticSolution M Q r * delta M Q r *
      (2 * ω * r - q * Q) - 2 * radialK (q * Q) ω r) := by
    field_simp
  rw [hD]
  ring

/-- The limit `r → ∞` of the right side of `current_eq_profile`, given the outgoing condition
(1.4) for the profile `F`: `F − B = O(r⁻¹)`, `F' = O(r⁻²)`. -/
theorem tendsto_current_profile {M Q q ω c : ℝ} (hQ : |Q| < M) (hc : c ≠ 0)
    (hcdef : c = 2 * M * ω - q * Q) {F : ℝ → ℂ} {B : ℂ}
    (hF1 : (fun r => F r - B) =O[atTop] (fun r : ℝ => r⁻¹))
    (hF2 : deriv F =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    Tendsto (fun r : ℝ =>
      -(radialK (q * Q) ω r / r ^ 2 / (r * staticSolution M Q r *
        ((staticSolution M Q r * delta M Q r * (2 * ω * r - q * Q) -
          2 * radialK (q * Q) ω r) / r))) *
        ‖F r * ((1 - staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) +
          I * F r * ((staticSolution M Q r * (Q ^ 2 * ω - 2 * M * c + Q ^ 2 * c / r) : ℝ) : ℂ) +
          ((staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) * (r * deriv F r)‖ ^ 2 -
      ‖F r‖ ^ 2 / r * (r * staticSolution M Q r)⁻¹ -
      delta M Q r / r ^ 2 * ((deriv F r * (starRingEnd ℂ) (F r)).re - ‖F r‖ ^ 2 / r))
      atTop (𝓝 0) := by
  have hT : Tendsto F atTop (𝓝 B) := by
    have h := (hF1.trans_tendsto tendsto_inv_atTop_zero).add_const B
    simpa only [sub_add_cancel, zero_add] using h
  have hT' : Tendsto (deriv F) atTop (𝓝 0) :=
    hF2.trans_tendsto (tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop
  have hrT' : Tendsto (fun r : ℝ => (r : ℂ) * deriv F r) atTop (𝓝 0) := by
    have hO : (fun r : ℝ => (r : ℂ) * deriv F r) =O[atTop] (fun r : ℝ => r * (r ^ 2)⁻¹) :=
      (isBigO_of_le atTop (fun r => (Complex.norm_real r).le)).mul hF2
    refine hO.trans_tendsto (tendsto_inv_atTop_zero.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with r hr
    field_simp
  have hgΔ := Infinity.tendsto_staticSolution_mul_delta_div hQ
  have hX : Tendsto (fun r : ℝ => F r * ((1 - staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) +
      I * F r * ((staticSolution M Q r * (Q ^ 2 * ω - 2 * M * c + Q ^ 2 * c / r) : ℝ) : ℂ) +
      ((staticSolution M Q r * delta M Q r / r : ℝ) : ℂ) * (r * deriv F r)) atTop (𝓝 0) := by
    have h1 := (tendsto_const_nhds (x := (1 : ℝ)).sub hgΔ).ofReal
    have h2 := ((Infinity.tendsto_staticSolution hQ).mul ((tendsto_const_nhds
      (x := Q ^ 2 * ω - 2 * M * c)).add (tendsto_const_nhds (x := Q ^ 2 * c).div_atTop
        tendsto_id))).ofReal
    have h3 := hgΔ.ofReal
    have h := ((hT.mul h1).add (((tendsto_const_nhds (x := I)).mul hT).mul h2)).add (h3.mul hrT')
    convert h using 2
    · simp only [ofReal_sub, ofReal_one, ofReal_div, ofReal_mul, ofReal_add, ofReal_pow,
        ofReal_ofNat, id_eq]
    · simp only [sub_self, ofReal_zero, mul_zero, add_zero, zero_mul, ofReal_one]
  have hK := (Infinity.tendsto_radialK_div_sq (q * Q) ω).div
    ((Infinity.tendsto_mul_staticSolution hQ).mul
      (Infinity.tendsto_staticSolution_mul_delta_mul_sub_div hQ (q * Q) ω))
    (by rw [one_mul, neg_ne_zero, ← hcdef]; exact hc)
  have hN := (hX.norm).pow 2
  have hA := ((hT.norm.pow 2).div_atTop tendsto_id).mul
    ((Infinity.tendsto_mul_staticSolution hQ).inv₀ one_ne_zero)
  have hRe : Tendsto (fun r => (deriv F r * (starRingEnd ℂ) (F r)).re) atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto _).comp
      (hT'.mul ((Complex.continuous_conj.tendsto B).comp hT))
    convert h using 2
    · simp only [mul_re, conj_re, conj_im, mul_neg, sub_neg_eq_add, Function.comp_apply]
    · simp only [zero_mul, zero_re]
  have hC := (Infinity.tendsto_delta_div_sq hQ).mul
    (hRe.sub ((hT.norm.pow 2).div_atTop tendsto_id))
  have h := ((hK.neg.mul hN).sub hA).sub hC
  convert h using 2
  · simp only [ofReal_sub, ofReal_one, ofReal_div, ofReal_mul, ofReal_add, ofReal_pow, ofReal_ofNat,
      neg_mul, mul_inv_rev, mul_re, conj_re, conj_im, mul_neg, sub_neg_eq_add, Pi.div_apply, id_eq]
  · simp only [neg_sub, one_mul, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, inv_one, mul_one, sub_self]

/-- **The infinity endpoint limit (2.14)–(2.15).** For a solution `R` of (1.2) satisfying the
outgoing condition (1.4) with `c = 2Mω − e ≠ 0`, the current `J[v_I]` of
`v_I = e^{−iϑ} U`, `U(x) = x R(r(x))`, tends to `0` as `x → ∞`. -/
theorem infinity_current_tendsto {M Q q ω : ℝ} (_hM : 0 < M) (hQ : |Q| < M)
    (hc : 2 * M * ω - q * Q ≠ 0) {x₀ : ℝ} (hx₀ : 0 < x₀)
    {R : ℝ → ℂ} {B : ℂ} (hR : IsRadialSolution M Q q ω R) (hI : InfinityCondition M Q q ω R B) :
    Tendsto (dephasedCurrent (transformedK M Q q ω)
        (dephase (transformedK M Q q ω) x₀ (-1) (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))))
      atTop (𝓝 0) := by
  obtain ⟨hF1, hF2⟩ := hI
  have hlim := (tendsto_current_profile hQ hc rfl hF1 hF2).comp
    (Infinity.tendsto_radiusOf_atTop hQ)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [dephasedCurrent_eq_infinity hQ hx₀ hR hx rfl,
    current_eq_profile hQ hc rfl hR rfl (outerHorizon_lt_radiusOf hQ hx)]
  rfl

end ModeStability.Endpoint

end
