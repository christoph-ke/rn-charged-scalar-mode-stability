module

public import ModeStability.Endpoint.Horizon
public import ModeStability.Endpoint.Infinity

/-!
# Auxiliary facts for the endpoint currents in the constant normalization

Helpers for constant normalization: `a < r₀ < 2M` of
the all-angular research notes in preparation, p. 5, for `L = 0` on the subextremal exterior.

We use the reflected coordinate `y = h(r) ∈ (0, ∞)`, with inverse `r(y) = radiusOf M Q (1/y)`,
the function `U(y) = R(r(y))` and the coefficient `f(y) = −K(r(y))`, `K = ωr² − qQr`.

* `dr/dy = −Δ(r)` (`cn_hasDerivAt_radius`), hence `U_y = −Δ R'(r)` (`cn_hasDerivAt_U`) and
  `f_y = Δ K'(r)` with `K' = 2ωr − qQ` (`cn_hasDerivAt_f`);
* for `y > 0` the current of `e^{iσϑ} U` is
  `J = (K/(ΔK')) |ΔR' + iσKR|² + Re(Δ R' R̄)` at `r = r(y)` (`cn_current_eq`);
* at the horizon, in terms of the profile `R̃ = (r − a)^{iκ} R` of (1.3),
  `J_+ = (r − a) (K/((r − b)K')) |(r − b) R̃' + i L R̃|² + Re(Δ R̃' conj R̃)` with
  `L = ω(r + a) − qQ − κ` (`cn_horizon_algebra`), and this tends to `0` as `r ↓ a` when
  `K'(a) ≠ 0` (`cn_tendsto_horizon_form`).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

variable {M Q q ω : ℝ}

/-! ### The reflected coordinate `y` -/

/-- `r(y) = radiusOf M Q (1/y)` has `dr/dy = −Δ(r(y))` for `y > 0`. -/
theorem cn_hasDerivAt_radius (hQ : |Q| < M) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => radiusOf M Q (1 / y)) (-delta M Q (radiusOf M Q (1 / y))) y := by
  have h1 : HasDerivAt (fun y : ℝ => 1 / y) (-(y ^ 2)⁻¹) y := by
    simpa only [one_div] using hasDerivAt_inv hy.ne'
  have h := (hasDerivAt_radiusOf hQ (one_div_pos.2 hy)).comp y h1
  refine h.congr_deriv ?_
  field_simp

/-- `f(y) = −K(r(y))` has `f_y = Δ K'` at `r = r(y)`, `K' = 2ωr − qQ`. -/
theorem cn_hasDerivAt_f (hQ : |Q| < M) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y)))
      (delta M Q (radiusOf M Q (1 / y)) * (2 * ω * radiusOf M Q (1 / y) - q * Q)) y := by
  have hr := cn_hasDerivAt_radius hQ hy
  have h := (((hr.pow 2).const_mul ω).sub (hr.const_mul (q * Q))).neg
  unfold radialK
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring

/-- `f(y) = −K(r(y))` is continuous on `y > 0`. -/
theorem cn_continuousOn_f (hQ : |Q| < M) :
    ContinuousOn (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y))) (Ioi 0) :=
  fun _ hy => (cn_hasDerivAt_f hQ hy).continuousAt.continuousWithinAt

/-- `U(y) = R(r(y))` has `U_y = −Δ R'(r)` at `r = r(y)`, `y > 0`. -/
theorem cn_hasDerivAt_U (hQ : |Q| < M) {R : ℝ → ℂ} (hR : IsRadialSolution M Q q ω R) {y : ℝ}
    (hy : 0 < y) :
    HasDerivAt (fun y => R (radiusOf M Q (1 / y)))
      (-((delta M Q (radiusOf M Q (1 / y)) : ℝ) : ℂ) * deriv R (radiusOf M Q (1 / y))) y := by
  have hra := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy)
  have h := ((hR _ hra).1.hasDerivAt).scomp y (cn_hasDerivAt_radius hQ hy)
  refine h.congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  ring

/-- Pointwise algebra: with `f = −K`, `f_y = ΔK'`, `U_y = −ΔR'`, the phase-free current
`−(f/f_y)|U_y + iσfU|² − Re(U_y Ū)` equals `(K/(ΔK'))|ΔR' + iσKR|² + Re(ΔR'R̄)`. -/
theorem cn_current_algebra (σ K K' Δ : ℝ) (R R' : ℂ) :
    -((-K) / (Δ * K')) * ‖-(Δ : ℂ) * R' + (σ : ℂ) * ((-K : ℝ) : ℂ) * I * R‖ ^ 2 -
        (-(Δ : ℂ) * R' * (starRingEnd ℂ) R).re =
      K / (Δ * K') * ‖(Δ : ℂ) * R' + (σ : ℂ) * (K : ℂ) * I * R‖ ^ 2 +
        ((Δ : ℂ) * R' * (starRingEnd ℂ) R).re := by
  have h1 : -(Δ : ℂ) * R' + (σ : ℂ) * ((-K : ℝ) : ℂ) * I * R =
      -((Δ : ℂ) * R' + (σ : ℂ) * (K : ℂ) * I * R) := by
    push_cast
    ring
  have h2 : -(Δ : ℂ) * R' * (starRingEnd ℂ) R = -((Δ : ℂ) * R' * (starRingEnd ℂ) R) := by ring
  rw [h1, norm_neg, h2, Complex.neg_re, neg_div]
  ring

/-- For `y > 0` and `r = r(y)`, the current of `e^{iσϑ} U` in the constant normalization:
`J = (K/(ΔK')) |ΔR' + iσKR|² + Re(Δ R' R̄)`. -/
theorem cn_current_eq (hQ : |Q| < M) {y₀ : ℝ} (hy₀ : 0 < y₀) (σ : ℝ) {R : ℝ → ℂ}
    (hR : IsRadialSolution M Q q ω R) {y : ℝ} (hy : 0 < y) :
    dephasedCurrent (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y)))
        (dephase (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y))) y₀ σ
          (fun y => R (radiusOf M Q (1 / y)))) y =
      radialK (q * Q) ω (radiusOf M Q (1 / y)) /
          (delta M Q (radiusOf M Q (1 / y)) * (2 * ω * radiusOf M Q (1 / y) - q * Q)) *
        ‖((delta M Q (radiusOf M Q (1 / y)) : ℝ) : ℂ) * deriv R (radiusOf M Q (1 / y)) +
          (σ : ℂ) * ((radialK (q * Q) ω (radiusOf M Q (1 / y)) : ℝ) : ℂ) * I *
            R (radiusOf M Q (1 / y))‖ ^ 2 +
      (((delta M Q (radiusOf M Q (1 / y)) : ℝ) : ℂ) * deriv R (radiusOf M Q (1 / y)) *
        (starRingEnd ℂ) (R (radiusOf M Q (1 / y)))).re := by
  have hU := cn_hasDerivAt_U hQ hR hy
  rw [dephasedCurrent_dephase_eq hy₀ (cn_continuousOn_f hQ) σ hy hU.differentiableAt,
    hU.deriv, (cn_hasDerivAt_f hQ hy).deriv]
  exact cn_current_algebra σ _ _ _ _ _

/-! ### The horizon end -/

/-- Horizon algebra: for `r > a`, with `R̃ = pR`, `|p| = 1`, `R̃' = p(R' + iκR/(r − a))` and
`K − κ(r − b) = (r − a)L`,
`(K/(ΔK'))|ΔR' + iKR|² + Re(ΔR'R̄) =
  (r − a)(K/((r − b)K'))|(r − b)R̃' + iLR̃|² + Re(ΔR̃' conj R̃)`. -/
theorem cn_horizon_algebra {a b r K K' Δ κ L : ℝ} {p R R' Rt Rt' : ℂ} (hra : 0 < r - a)
    (hΔ : Δ = (r - a) * (r - b)) (hp : ‖p‖ = 1) (hRt : Rt = p * R)
    (hRt' : Rt' = p * (R' + I * κ * R / ((r - a : ℝ) : ℂ)))
    (hKL : K - κ * (r - b) = (r - a) * L) :
    K / (Δ * K') * ‖(Δ : ℂ) * R' + ((1 : ℝ) : ℂ) * (K : ℂ) * I * R‖ ^ 2 +
        ((Δ : ℂ) * R' * (starRingEnd ℂ) R).re =
      (r - a) * (K / ((r - b) * K') * ‖((r - b : ℝ) : ℂ) * Rt' + I * (L : ℂ) * Rt‖ ^ 2) +
        ((Δ : ℂ) * Rt' * (starRingEnd ℂ) Rt).re := by
  have hra' : ((r : ℂ) - a) ≠ 0 := by exact_mod_cast hra.ne'
  have key : (((r - a : ℝ) : ℂ)) * (((r - b : ℝ) : ℂ) * Rt' + I * (L : ℂ) * Rt) =
      p * ((Δ : ℂ) * R' + ((1 : ℝ) : ℂ) * (K : ℂ) * I * R) := by
    subst hRt hRt' hΔ
    have hKL' : (K : ℂ) - κ * (r - b) = (r - a) * L := by exact_mod_cast hKL
    push_cast
    field_simp
    linear_combination (-(p * R * I)) * hKL'
  have hnorm : ‖(Δ : ℂ) * R' + ((1 : ℝ) : ℂ) * (K : ℂ) * I * R‖ =
      (r - a) * ‖((r - b : ℝ) : ℂ) * Rt' + I * (L : ℂ) * Rt‖ := by
    have h := congrArg norm key
    rw [norm_mul, norm_mul, hp, one_mul, Complex.norm_real, Real.norm_of_nonneg hra.le] at h
    exact h.symm
  have hpp : p * (starRingEnd ℂ) p = 1 := by
    rw [Complex.mul_conj', hp, ofReal_one, one_pow]
  have hRR : R * (starRingEnd ℂ) R = ((‖R‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj']
  have hre : (Δ : ℂ) * Rt' * (starRingEnd ℂ) Rt = (Δ : ℂ) * R' * (starRingEnd ℂ) R +
      I * ((Δ * κ / (r - a) * ‖R‖ ^ 2 : ℝ) : ℂ) := by
    rw [hRt', hRt, map_mul]
    push_cast
    linear_combination ((Δ : ℂ) * (R' + I * κ * R / (r - a)) * (starRingEnd ℂ) R) * hpp +
      (I * Δ * κ / (r - a)) * hRR
  have hre' : ((Δ : ℂ) * Rt' * (starRingEnd ℂ) Rt).re = ((Δ : ℂ) * R' * (starRingEnd ℂ) R).re := by
    rw [hre, Complex.add_re, Complex.I_mul_re, Complex.ofReal_im, neg_zero, add_zero]
  rw [hnorm, hre', hΔ]
  congr 1
  rcases eq_or_ne K' 0 with hK' | hK'
  · simp [hK']
  · rcases eq_or_ne (r - b) 0 with hrb0 | hrb0
    · simp [hrb0]
    · field_simp

/-- The horizon form of `cn_horizon_algebra` tends to `0` as `r ↓ a`, given the horizon
condition (1.3) and `K'(a) ≠ 0`: the first term is `O(r − a)` and `Δ → 0` with `R̃'` bounded. -/
theorem cn_tendsto_horizon_form (hQ : |Q| < M) (hK'a : 2 * ω * outerHorizon M Q - q * Q ≠ 0)
    {R : ℝ → ℂ} {B : ℂ} (hH : HorizonCondition M Q q ω R B) :
    Tendsto (fun r => (r - outerHorizon M Q) *
        (radialK (q * Q) ω r / ((r - innerHorizon M Q) * (2 * ω * r - q * Q)) *
          ‖((r - innerHorizon M Q : ℝ) : ℂ) * deriv (Endpoint.horizonProfile M Q q ω R) r +
            I * ((ω * (r + outerHorizon M Q) - q * Q - Endpoint.horizonFreq M Q q ω : ℝ) : ℂ) *
              Endpoint.horizonProfile M Q q ω R r‖ ^ 2) +
        (((delta M Q r : ℝ) : ℂ) * deriv (Endpoint.horizonProfile M Q q ω R) r *
          (starRingEnd ℂ) (Endpoint.horizonProfile M Q q ω R r)).re)
      (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
  have hd : 0 < outerHorizon M Q - innerHorizon M Q := outerHorizon_sub_innerHorizon_pos hQ
  have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (outerHorizon M Q)) (𝓝 (outerHorizon M Q)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h0 : Tendsto (fun r : ℝ => r - outerHorizon M Q) (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
    simpa only [sub_self] using hid.sub_const (outerHorizon M Q)
  have hRt := Endpoint.tendsto_horizonProfile hH
  have hRt' := Endpoint.isBoundedUnder_deriv_horizonProfile hH
  have hcK : Continuous (radialK (q * Q) ω) := by
    unfold radialK
    fun_prop
  have hcoef : Tendsto (fun r => radialK (q * Q) ω r /
      ((r - innerHorizon M Q) * (2 * ω * r - q * Q))) (𝓝[>] (outerHorizon M Q))
      (𝓝 (radialK (q * Q) ω (outerHorizon M Q) / ((outerHorizon M Q - innerHorizon M Q) *
        (2 * ω * outerHorizon M Q - q * Q)))) :=
    ((hcK.tendsto _).comp hid).div
      ((hid.sub_const _).mul ((hid.const_mul (2 * ω)).sub_const (q * Q)))
      (mul_ne_zero hd.ne' hK'a)
  have h1 : (fun r : ℝ => ((r - innerHorizon M Q : ℝ) : ℂ)) =O[𝓝[>] (outerHorizon M Q)]
      (fun _ => (1 : ℝ)) :=
    (hid.sub_const _).ofReal.isBigO_one ℝ
  have h2 : deriv (Endpoint.horizonProfile M Q q ω R) =O[𝓝[>] (outerHorizon M Q)]
      (fun _ => (1 : ℝ)) :=
    hRt'.isBigO_one ℝ
  have h3 : (fun r => I * ((ω * (r + outerHorizon M Q) - q * Q -
      Endpoint.horizonFreq M Q q ω : ℝ) : ℂ) * Endpoint.horizonProfile M Q q ω R r)
      =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)) :=
    (((tendsto_const_nhds (x := I)).mul ((((hid.add_const _).const_mul ω).sub_const
      (q * Q)).sub_const (Endpoint.horizonFreq M Q q ω)).ofReal).mul hRt).isBigO_one ℝ
  have h12 := h1.mul h2
  simp only [mul_one] at h12
  have hW := h12.add h3
  have hO := (hcoef.isBigO_one ℝ).mul (hW.norm_left.pow 2)
  simp only [one_pow, mul_one] at hO
  have hfirst := h0.zero_mul_isBoundedUnder_le ((isBigO_one_iff ℝ).1 hO)
  have hcΔ : Continuous (delta M Q) := by
    unfold delta
    fun_prop
  have hΔa : delta M Q (outerHorizon M Q) = 0 := by
    unfold delta
    ring
  have hΔ : Tendsto (fun r => ((delta M Q r : ℝ) : ℂ)) (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
    have h := ((hcΔ.tendsto _).comp hid).ofReal
    rw [hΔa, ofReal_zero] at h
    exact h
  have hsecond := (Complex.continuous_re.tendsto _).comp
    ((hΔ.zero_mul_isBoundedUnder_le hRt').mul ((Complex.continuous_conj.tendsto B).comp hRt))
  have h := hfirst.add hsecond
  simp only [zero_mul, zero_re, add_zero] at h
  exact h

end ModeStability.AllAngular

end
