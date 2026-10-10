module

public import ModeStability.AllAngular.ConstantEndpointsAux

/-!
# The endpoint limits of the current in the constant normalization

Source: the all-angular research notes in preparation, p. 5, constant normalization: `a < r₀ <
2M`, the limits (4.4), for `L = 0` on the subextremal exterior `|Q| < M`, with the
frozen boundary conditions `HorizonCondition` (1.3) and `InfinityCondition` (1.4) of the spherical
paper.

Coordinates: `y = h(r) ∈ (0, ∞)` with inverse `r(y) = radiusOf M Q (1/y)`, `U(y) = R(r(y))`,
`f(y) = −K(r(y))`; `y → ∞` is the horizon `r ↓ a` and `y ↓ 0` is infinity `r → ∞`. By
`cn_current_eq`, for `y > 0`,
`J[e^{iσϑ} U] = (K/(ΔK')) |ΔR' + iσKR|² + Re(Δ R' R̄)` at `r = r(y)`.

* Horizon, `σ = +1` (`constant_horizon_current_tendsto`): with the profile `R̃ = (r − a)^{iκ} R`,
  `κ = K(a)/d`, `J = (r − a)(K/((r − b)K'))|(r − b)R̃' + iLR̃|² + Re(ΔR̃' conj R̃) → 0`, using
  `R̃ → B`, `R̃'` bounded and `K'(a) ≠ 0`.
* Infinity, `σ = −1` (`constant_infinity_current_tendsto`): with the profile
  `R̃ = r e^{−iωr} r^{−ic} R`, `c = 2Mω − qQ`,
  `J = (K/r²)/((Δ/r²)(K'/r)) · r⁻¹ · |(Δ/r²)(rR̃') − (Δ/r²)R̃ + iR̃ S/r|²
     + (Δ/r²)(Re(R̃' conj R̃) − |R̃|²/r)` with `S = Q²ω − 2Mc + Q²c/r` (`cn_infinity_algebra`),
  which tends to `0` since `K'/r → 2ω ≠ 0` (`cn_tendsto_infinity_form`). This uses the exact
  cancellation `Δ(ω + c/r) − K = S`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

variable {M Q q ω : ℝ}

/-! ### The infinity end -/

/-- The derivative of the profile `R̃(r) = r e^{−iωr} r^s R(r)` of (1.4), for any exponent `s`:
`R̃' = e^{−iωr} r^s (R (1 − iωr + s) + r R')`, `r > 0`. -/
theorem cn_hasDerivAt_infinityProfile (ω : ℝ) (s : ℂ) {R : ℝ → ℂ} {r : ℝ} (hr : 0 < r)
    (hR : DifferentiableAt ℝ R r) :
    HasDerivAt (fun r : ℝ => (r : ℂ) * exp (-(I * ω * r)) * (r : ℂ) ^ s * R r)
      (exp (-(I * ω * r)) * (r : ℂ) ^ s * (R r * (1 - I * ω * r + s) + r * deriv R r)) r := by
  have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := by
    simpa only [id_eq, ofReal_one] using (hasDerivAt_id r).ofReal_comp
  have h2 : HasDerivAt (fun r : ℝ => exp (-(I * ω * r))) (exp (-(I * ω * r)) * (-(I * ω))) r := by
    have : HasDerivAt (fun r : ℝ => -(I * ω * (r : ℂ))) (-(I * ω * 1)) r :=
      (h1.const_mul (I * ω)).neg
    simpa only [mul_neg, mul_one] using this.cexp
  have h3 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (r : ℂ) ^ (s - 1)) r := by
    have h := ((hasDerivAt_id (r : ℂ)).cpow_const (c := s)
      (Complex.ofReal_mem_slitPlane.2 hr)).comp_ofReal
    simpa only [id_eq, mul_one] using h
  have h4 := ((h1.mul h2).mul h3).mul hR.hasDerivAt
  convert h4 using 1
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  rw [Complex.cpow_sub _ _ hr', cpow_one]
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Infinity algebra: for `r > 0`, `Δ > 0`, with `T = r p A`, `|p| = 1`,
`T' = p(A(1 − iωr − ic) + rA')`, `c = 2Mω − e`,
`(K/(ΔK'))|ΔA' − iKA|² + Re(ΔA'Ā) =
  (K/r²)/((Δ/r²)(K'/r)) · r⁻¹ · |(Δ/r²)(rT') − (Δ/r²)T + iT S/r|² + (Δ/r²)(Re(T'T̄) − |T|²/r)`
with `S = Q²ω − 2Mc + Q²c/r`. -/
theorem cn_infinity_algebra {r Δ K K' M Q ω c e : ℝ} {p A A' T T' : ℂ} (hr : 0 < r)
    (hΔ0 : 0 < Δ) (hp : ‖p‖ = 1) (hΔ : Δ = r ^ 2 - 2 * M * r + Q ^ 2)
    (hK : K = ω * r ^ 2 - e * r) (hc : c = 2 * M * ω - e) (hT : T = r * p * A)
    (hT' : T' = p * (A * (1 - I * ω * r - I * c) + r * A')) :
    K / (Δ * K') * ‖(Δ : ℂ) * A' + ((-1 : ℝ) : ℂ) * (K : ℂ) * I * A‖ ^ 2 +
        ((Δ : ℂ) * A' * (starRingEnd ℂ) A).re =
      K / r ^ 2 / (Δ / r ^ 2 * (K' / r)) * (1 / r) *
          ‖((Δ / r ^ 2 : ℝ) : ℂ) * ((r : ℂ) * T') - ((Δ / r ^ 2 : ℝ) : ℂ) * T +
            I * T * (((Q ^ 2 * ω - 2 * M * c + Q ^ 2 * c / r) / r : ℝ) : ℂ)‖ ^ 2 +
        Δ / r ^ 2 * ((T' * (starRingEnd ℂ) T).re - ‖T‖ ^ 2 / r) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hΔne : Δ ≠ 0 := hΔ0.ne'
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr0
  have key : ((Δ / r ^ 2 : ℝ) : ℂ) * ((r : ℂ) * T') - ((Δ / r ^ 2 : ℝ) : ℂ) * T +
      I * T * (((Q ^ 2 * ω - 2 * M * c + Q ^ 2 * c / r) / r : ℝ) : ℂ) =
      p * ((Δ : ℂ) * A' + ((-1 : ℝ) : ℂ) * (K : ℂ) * I * A) := by
    subst hΔ hK hc hT hT'
    push_cast
    field_simp
    ring
  have hnorm : ‖(Δ : ℂ) * A' + ((-1 : ℝ) : ℂ) * (K : ℂ) * I * A‖ =
      ‖((Δ / r ^ 2 : ℝ) : ℂ) * ((r : ℂ) * T') - ((Δ / r ^ 2 : ℝ) : ℂ) * T +
        I * T * (((Q ^ 2 * ω - 2 * M * c + Q ^ 2 * c / r) / r : ℝ) : ℂ)‖ := by
    rw [key, norm_mul, hp, one_mul]
  have hcoef : K / r ^ 2 / (Δ / r ^ 2 * (K' / r)) * (1 / r) = K / (Δ * K') := by
    rcases eq_or_ne K' 0 with h | h
    · simp [h]
    · field_simp
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
      one_im, zero_sub, conj_re, conj_im, mul_neg, sub_neg_eq_add]
  have hre2 : ((Δ : ℂ) * A' * (starRingEnd ℂ) A).re = Δ * (A' * (starRingEnd ℂ) A).re := by
    rw [mul_assoc, Complex.re_ofReal_mul]
  rw [hnorm, hcoef]
  congr 1
  rw [hre, hnT, hre2]
  field_simp
  ring

/-- The infinity form of `cn_infinity_algebra` tends to `0` as `r → ∞`, given the outgoing
condition (1.4) for the profile `F` (`F − B = O(r⁻¹)`, `F' = O(r⁻²)`) and `ω ≠ 0`. -/
theorem cn_tendsto_infinity_form (hQ : |Q| < M) (hω : ω ≠ 0) (c : ℝ) {F : ℝ → ℂ} {B : ℂ}
    (hF1 : (fun r => F r - B) =O[atTop] (fun r : ℝ => r⁻¹))
    (hF2 : deriv F =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    Tendsto (fun r : ℝ => radialK (q * Q) ω r / r ^ 2 /
          (delta M Q r / r ^ 2 * ((2 * ω * r - q * Q) / r)) * (1 / r) *
          ‖((delta M Q r / r ^ 2 : ℝ) : ℂ) * ((r : ℂ) * deriv F r) -
              ((delta M Q r / r ^ 2 : ℝ) : ℂ) * F r +
            I * F r * (((Q ^ 2 * ω - 2 * M * c + Q ^ 2 * c / r) / r : ℝ) : ℂ)‖ ^ 2 +
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
  have hΔ := Infinity.tendsto_delta_div_sq hQ
  have hK := Infinity.tendsto_radialK_div_sq (q * Q) ω
  have hinv : Tendsto (fun r : ℝ => 1 / r) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hK' : Tendsto (fun r : ℝ => (2 * ω * r - q * Q) / r) atTop (𝓝 (2 * ω)) := by
    have h := (tendsto_const_nhds (x := 2 * ω)).sub (hinv.const_mul (q * Q))
    rw [mul_zero, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    field_simp
  have hS : Tendsto (fun r : ℝ => (Q ^ 2 * ω - 2 * M * c + Q ^ 2 * c / r) / r) atTop (𝓝 0) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).div_atTop tendsto_id
  have hcoef := (hK.div (hΔ.mul hK') (by rw [one_mul]; exact mul_ne_zero two_ne_zero hω)).mul
    hinv
  have hX := ((hΔ.ofReal.mul hrT').sub (hΔ.ofReal.mul hT)).add
    (((tendsto_const_nhds (x := I)).mul hT).mul hS.ofReal)
  have hRe : Tendsto (fun r => (deriv F r * (starRingEnd ℂ) (F r)).re) atTop (𝓝 0) := by
    have h : Tendsto (fun r => (deriv F r * (starRingEnd ℂ) (F r)).re) atTop
        (𝓝 ((0 * (starRingEnd ℂ) B).re)) :=
      (Complex.continuous_re.tendsto _).comp
        (hT'.mul ((Complex.continuous_conj.tendsto B).comp hT))
    rwa [zero_mul, zero_re] at h
  have hsecond := hΔ.mul (hRe.sub ((hT.norm.pow 2).div_atTop tendsto_id))
  have h := (hcoef.mul (hX.norm.pow 2)).add hsecond
  convert h using 2 <;> simp

/-! ### The endpoint limits -/

/-- Horizon end (y → ∞, r ↓ a), plus sign. Needs K(a) ≠ 0 and K'(a) ≠ 0. -/
theorem constant_horizon_current_tendsto {M Q q ω : ℝ} (_hM : 0 < M) (hQ : |Q| < M)
    (hKa : radialK (q * Q) ω (outerHorizon M Q) ≠ 0)
    (hK'a : 2 * ω * outerHorizon M Q - q * Q ≠ 0) {y₀ : ℝ} (hy₀ : 0 < y₀)
    {R : ℝ → ℂ} {B : ℂ} (hR : IsRadialSolution M Q q ω R) (hH : HorizonCondition M Q q ω R B) :
    Tendsto (dephasedCurrent (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y)))
        (dephase (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y))) y₀ 1
          (fun y => R (radiusOf M Q (1 / y))))) atTop (𝓝 0) := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hκ : Endpoint.horizonFreq M Q q ω ≠ 0 := div_ne_zero hKa hd.ne'
  have hy : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝[>] 0) := by
    simpa only [one_div] using tendsto_inv_atTop_nhdsGT_zero
  have hr : Tendsto (fun y => radiusOf M Q (1 / y)) atTop (𝓝[>] (outerHorizon M Q)) :=
    (Endpoint.tendsto_radiusOf_nhdsGT hQ).comp hy
  refine ((cn_tendsto_horizon_form hQ hK'a hH).comp hr).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  have hra := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy)
  rw [cn_current_eq hQ hy₀ 1 hR hy]
  exact (cn_horizon_algebra (sub_pos.2 hra) rfl (Endpoint.norm_horizonPhase hra) rfl
    (Endpoint.hasDerivAt_horizonProfile hκ hR hra).deriv
    (Endpoint.radialK_sub_horizonFreq_mul hQ _)).symm

/-- Infinity end (y ↓ 0, r → ∞), minus sign. Needs ω ≠ 0. -/
theorem constant_infinity_current_tendsto {M Q q ω : ℝ} (_hM : 0 < M) (hQ : |Q| < M)
    (hω : ω ≠ 0) {y₀ : ℝ} (hy₀ : 0 < y₀)
    {R : ℝ → ℂ} {B : ℂ} (hR : IsRadialSolution M Q q ω R) (hI : InfinityCondition M Q q ω R B) :
    Tendsto (dephasedCurrent (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y)))
        (dephase (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y))) y₀ (-1)
          (fun y => R (radiusOf M Q (1 / y))))) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hF1, hF2⟩ := hI
  have hy : Tendsto (fun y : ℝ => 1 / y) (𝓝[>] 0) atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero
  have hr : Tendsto (fun y => radiusOf M Q (1 / y)) (𝓝[>] 0) atTop :=
    (Infinity.tendsto_radiusOf_atTop hQ).comp hy
  refine ((cn_tendsto_infinity_form (q := q) hQ hω (2 * M * ω - q * Q) hF1 hF2).comp hr).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hra := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy)
  have hr0 : 0 < radiusOf M Q (1 / y) := (Infinity.outerHorizon_pos_of_abs_lt hQ).trans hra
  have hs : -(I * (2 * M * ω - q * Q : ℂ)) = -(I * ((2 * M * ω - q * Q : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [cn_current_eq hQ hy₀ (-1) hR hy]
  refine (cn_infinity_algebra hr0 (delta_pos hQ hra)
    (Endpoint.norm_exp_mul_cpow (ω := ω) hr0 (2 * M * ω - q * Q))
    (Infinity.delta_eq_poly hQ _) rfl rfl ?_ ?_).symm
  · rw [hs]
    ring
  · rw [(cn_hasDerivAt_infinityProfile ω _ hr0 (hR _ hra).1).deriv, hs]
    ring

end ModeStability.AllAngular

end
