module

public import Mathlib
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Endpoint.InfinityAux

/-!
# Auxiliary facts for the infinity limits of the current with angular term

Helpers for the infinity half of (4.4)–(4.5) of the all-angular research notes in preparation,
Section 4, pp. 5–6, with the angular term `L ≥ 0` and the effective frequency
`k̂ = sgn(K) g² √(K² − LΔ)` of (3.2).

* `il_current_tendsto_of`: the phase-free current
  `J = −(f/f_t)|U_t + iσfU|² − Re(U_t Ū)` tends to `0` along any filter on which
  `(f/f_t)|W|² → 0` and `|W||U| → 0`, `W = U_t + iσfU` (since `Re(U_t Ū) = Re(W Ū)`).
* `il_abs_sub_sign_mul_sqrt_le`: the angular correction of the frequency,
  `|K − sgn(K)√(K² − LΔ)| ≤ LΔ/|K|` (the integrable correction (4.3)).
* `il_hasDerivAt_profile`: the derivative of the Θ-profile `R̃ = r e^{−iΘ} R` of (1.5),
  `R̃' = e^{−iΘ}(R(1 − irΘ') + rR')`.
* `il_reciprocal_algebra`, `il_constant_algebra`: the pointwise identities expressing `|U' −
  ik̂U|`
  through `R̃`, `R̃'` (the term `iΘ'` cancels against `−igK` because `ΔΘ' = K`).
* Real-variable asymptotics at `r → ∞`, valid for all `M, Q`: `Δ/r² → 1`, `(K² − LΔ)/r⁴ → ω²`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-! ### The abstract current limit -/

/-- The phase-free current `J = −(f/f_t)|W|² − Re(U_t Ū)`, `W = U_t + iσfU`, tends to `0` along
`l` if `(f/f_t)|W|² → 0` and `|W||U| → 0`: indeed `Re(U_t Ū) = Re(W Ū)` for real `σ, f`. -/
theorem il_current_tendsto_of {l : Filter ℝ} {k dk : ℝ → ℝ} {U dU : ℝ → ℂ} (σ : ℝ)
    (h1 : Tendsto (fun t => k t / dk t * ‖dU t + σ * k t * I * U t‖ ^ 2) l (𝓝 0))
    (h2 : Tendsto (fun t => ‖dU t + σ * k t * I * U t‖ * ‖U t‖) l (𝓝 0)) :
    Tendsto (fun t => -(k t / dk t) * ‖dU t + σ * k t * I * U t‖ ^ 2 -
      (dU t * (starRingEnd ℂ) (U t)).re) l (𝓝 0) := by
  have hre : ∀ t, (dU t * (starRingEnd ℂ) (U t)).re =
      ((dU t + σ * k t * I * U t) * (starRingEnd ℂ) (U t)).re := by
    intro t
    rw [add_mul, Complex.add_re]
    have : ((σ : ℂ) * k t * I * U t * (starRingEnd ℂ) (U t)).re = 0 := by
      rw [mul_assoc, Complex.mul_conj]
      simp [Complex.mul_re]
    rw [this, add_zero]
  have h3 : Tendsto (fun t => ((dU t + σ * k t * I * U t) * (starRingEnd ℂ) (U t)).re) l
      (𝓝 0) := by
    refine squeeze_zero_norm (fun t => ?_) h2
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have h := h1.neg.sub h3
  rw [neg_zero, sub_zero] at h
  refine h.congr fun t => ?_
  rw [hre, neg_mul]

/-! ### The angular correction of the frequency -/

/-- `|K − sgn(K)√(K² − D)| ≤ D/|K|` for `K ≠ 0` and `0 ≤ D ≤ K²`. -/
theorem il_abs_sub_sign_mul_sqrt_le {K D : ℝ} (hK : K ≠ 0) (hD : 0 ≤ D) (hDK : D ≤ K ^ 2) :
    |K - (SignType.sign K : ℝ) * Real.sqrt (K ^ 2 - D)| ≤ D / |K| := by
  have hP0 := Real.sqrt_nonneg (K ^ 2 - D)
  have hP2 := Real.sq_sqrt (sub_nonneg.2 hDK)
  set P := Real.sqrt (K ^ 2 - D)
  rcases hK.lt_or_gt with h | h
  · rw [sign_neg h, abs_of_neg h]
    have hPK : P ≤ -K := by nlinarith
    have e : K - ((-1 : SignType) : ℝ) * P = K + P := by
      simp only [SignType.coe_neg, SignType.coe_one, neg_one_mul, sub_neg_eq_add]
    rw [e, abs_of_nonpos (by linarith), le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg hP0 (by linarith : (0 : ℝ) ≤ -(K + P))]
  · rw [sign_pos h, abs_of_pos h]
    have hPK : P ≤ K := by nlinarith
    have e : K - ((1 : SignType) : ℝ) * P = K - P := by
      simp only [SignType.coe_one, one_mul]
    rw [e, abs_of_nonneg (by linarith), le_div_iff₀ h]
    nlinarith [mul_nonneg hP0 (by linarith : (0 : ℝ) ≤ K - P)]

/-- `sgn(f)` is locally constant at a point where the continuous function `f` does not vanish. -/
theorem il_sign_eventually {f : ℝ → ℝ} {x : ℝ} (hf : ContinuousAt f x) (h0 : f x ≠ 0) :
    ∀ᶠ t in 𝓝 x, (SignType.sign (f t) : ℝ) = SignType.sign (f x) := by
  rcases h0.lt_or_gt with h | h
  · filter_upwards [hf.eventually (gt_mem_nhds h)] with t ht
    rw [sign_neg h, sign_neg ht]
  · filter_upwards [hf.eventually (lt_mem_nhds h)] with t ht
    rw [sign_pos h, sign_pos ht]

/-- `sgn(K) = ±1` for `K ≠ 0`. -/
theorem il_sign_eq_or {K : ℝ} (hK : K ≠ 0) :
    (SignType.sign K : ℝ) = 1 ∨ (SignType.sign K : ℝ) = -1 := by
  rcases hK.lt_or_gt with h | h
  · right
    rw [sign_neg h]
    simp
  · left
    rw [sign_pos h]
    simp

/-! ### The Θ-profile -/

/-- The derivative of the Θ-profile `R̃(r) = r e^{−iΘ(r)} R(r)` of (1.5):
`R̃' = e^{−iΘ}(R(1 − irΘ') + rR')`. -/
theorem il_hasDerivAt_profile {Θ : ℝ → ℝ} {θ' : ℝ} {R : ℝ → ℂ} {r : ℝ}
    (hΘ : HasDerivAt Θ θ' r) (hR : DifferentiableAt ℝ R r) :
    HasDerivAt (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
      (exp (-(I * (Θ r : ℂ))) * (R r * (1 - I * r * θ') + r * deriv R r)) r := by
  have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := by
    simpa only [id_eq, ofReal_one] using (hasDerivAt_id r).ofReal_comp
  have h2 : HasDerivAt (fun r : ℝ => exp (-(I * (Θ r : ℂ))))
      (exp (-(I * (Θ r : ℂ))) * (-(I * θ'))) r :=
    ((hΘ.ofReal_comp.const_mul I).neg).cexp
  have h4 := (h1.mul h2).mul hR.hasDerivAt
  convert h4 using 1
  simp only [Pi.mul_apply]
  ring

/-- The phase factor `e^{−iΘ}` has modulus one. -/
theorem il_norm_exp_neg_I_mul (θ : ℝ) : ‖exp (-(I * (θ : ℂ)))‖ = 1 := by
  have h : -(I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-! ### Pointwise algebra -/

/-- Reciprocal normalization: for `x, r > 0`, `G = 1/x`, `T = r p A`, `|p| = 1`,
`T' = p(A(1 − irK/Δ) + rA')`, the derivative `U' = A + x(Δ/x²)A'` of `U = xA` and the coefficient
`k = K̂ x⁻²`: `|x²(U' − ikU)| = |T(r − GΔ) + (GΔ/r)(r²T') + i rG(K − K̂)T| (1/(rG))²`, and
`|U| = |T| (1/(rG))`. -/
theorem il_reciprocal_algebra {x r Δ K Kh kx G : ℝ} {p A A' dU T T' : ℂ} (hx : 0 < x)
    (hr : 0 < r) (hΔ : Δ ≠ 0) (hp : ‖p‖ = 1) (hG : G = 1 / x) (hkx : kx = Kh * (1 / x) ^ 2)
    (hdU : dU = A + (x : ℂ) * (((Δ / x ^ 2 : ℝ) : ℂ) * A')) (hT : T = r * p * A)
    (hT' : T' = p * (A * (1 - I * r * ((K / Δ : ℝ) : ℂ)) + r * A')) :
    ‖(x : ℂ) ^ 2 * (dU + ((-1 : ℝ) : ℂ) * (kx : ℂ) * I * ((x : ℂ) * A))‖ =
      ‖T * ((r - G * Δ : ℝ) : ℂ) + ((G * Δ / r : ℝ) : ℂ) * ((r : ℂ) ^ 2 * T') +
          I * ((r * G * (K - Kh) : ℝ) : ℂ) * T‖ * (1 / (r * G)) ^ 2 ∧
    ‖(x : ℂ) * A‖ = ‖T‖ * (1 / (r * G)) := by
  subst hG hkx hdU
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have hΔ' : (Δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  constructor
  · have key : (r : ℂ) ^ 2 * p * ((x : ℂ) ^ 2 * (A + (x : ℂ) * (((Δ / x ^ 2 : ℝ) : ℂ) * A') +
          ((-1 : ℝ) : ℂ) * ((Kh * (1 / x) ^ 2 : ℝ) : ℂ) * I * ((x : ℂ) * A))) =
        (x : ℂ) ^ 2 * (T * ((r - 1 / x * Δ : ℝ) : ℂ) +
          ((1 / x * Δ / r : ℝ) : ℂ) * ((r : ℂ) ^ 2 * T') +
            I * ((r * (1 / x) * (K - Kh) : ℝ) : ℂ) * T) := by
      subst hT hT'
      push_cast
      field_simp
      ring
    have hn := congrArg norm key
    simp only [norm_mul, norm_pow, hp, Complex.norm_of_nonneg hr.le, Complex.norm_of_nonneg hx.le,
      mul_one] at hn
    simp only [norm_mul, norm_pow, Complex.norm_of_nonneg hx.le]
    have h1 : (1 / (r * (1 / x))) ^ 2 = x ^ 2 / r ^ 2 := by field_simp
    rw [h1, mul_div_assoc', eq_div_iff hr2.ne']
    linarith
  · rw [hT, norm_mul, norm_mul, norm_mul, hp, Complex.norm_of_nonneg hr.le,
      Complex.norm_of_nonneg hx.le]
    field_simp

/-- Constant normalization: for `r > 0`, `T = r p A`, `|p| = 1`, `T' = p(A(1 − irK/Δ) + rA')`, the
derivative `U' = −ΔA'` of `U = A` and the coefficient `f = −K̂`:
`|U' − ifU| = |−(Δ/r²)(rT') + (Δ/r²)T − i((K − K̂)/r)T|`, and `|U| = |T| (1/r)`. -/
theorem il_constant_algebra {r Δ K Kh fy : ℝ} {p A A' dU T T' : ℂ} (hr : 0 < r) (hΔ : Δ ≠ 0)
    (hp : ‖p‖ = 1) (hfy : fy = -Kh) (hdU : dU = ((-Δ : ℝ) : ℂ) * A') (hT : T = r * p * A)
    (hT' : T' = p * (A * (1 - I * r * ((K / Δ : ℝ) : ℂ)) + r * A')) :
    ‖dU + ((-1 : ℝ) : ℂ) * (fy : ℂ) * I * A‖ =
      ‖-(((Δ / r ^ 2 : ℝ) : ℂ) * ((r : ℂ) * T')) + ((Δ / r ^ 2 : ℝ) : ℂ) * T -
          I * (((K - Kh) / r : ℝ) : ℂ) * T‖ ∧
    ‖A‖ = ‖T‖ * (1 / r) := by
  subst hfy hdU
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  have hΔ' : (Δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ
  constructor
  · have key : p * (((-Δ : ℝ) : ℂ) * A' + ((-1 : ℝ) : ℂ) * ((-Kh : ℝ) : ℂ) * I * A) =
        -(((Δ / r ^ 2 : ℝ) : ℂ) * ((r : ℂ) * T')) + ((Δ / r ^ 2 : ℝ) : ℂ) * T -
          I * (((K - Kh) / r : ℝ) : ℂ) * T := by
      subst hT hT'
      push_cast
      field_simp
      ring
    rw [← key, norm_mul, hp, one_mul]
  · rw [hT, norm_mul, norm_mul, hp, Complex.norm_of_nonneg hr.le]
    field_simp

/-! ### Asymptotics at infinity, for all `M, Q` -/

/-- `Δ(r) > 0` for `r > a` (no restriction on `M, Q`, since `b ≤ a`). -/
theorem il_delta_pos {M Q r : ℝ} (hr : outerHorizon M Q < r) : 0 < delta M Q r := by
  have hab : innerHorizon M Q ≤ outerHorizon M Q := by
    unfold innerHorizon outerHorizon
    linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
  unfold delta
  have h1 : 0 < r - outerHorizon M Q := sub_pos.2 hr
  have h2 : 0 < r - innerHorizon M Q := by linarith
  positivity

/-- `Δ(r)/r² → 1` as `r → ∞`. -/
theorem il_tendsto_delta_div_sq (M Q : ℝ) :
    Tendsto (fun r => delta M Q r / r ^ 2) atTop (𝓝 1) := by
  have h1 : ∀ c : ℝ, Tendsto (fun r : ℝ => 1 - c / r) atTop (𝓝 1) := fun c => by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := c)).div_atTop tendsto_id)
    rw [sub_zero] at h
    exact h
  have h := (h1 (outerHorizon M Q)).mul (h1 (innerHorizon M Q))
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  unfold delta
  field_simp

/-- `(K² − LΔ)/r⁴ → ω²` as `r → ∞`. -/
theorem il_tendsto_radicand_div (M Q e ω L : ℝ) :
    Tendsto (fun r => (radialK e ω r ^ 2 - L * delta M Q r) / r ^ 4) atTop (𝓝 (ω ^ 2)) := by
  have hi : Tendsto (fun r : ℝ => (r ^ 2)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop
  have h := ((Infinity.tendsto_radialK_div_sq e ω).pow 2).sub
    (((il_tendsto_delta_div_sq M Q).const_mul L).mul hi)
  rw [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  field_simp

/-- `K/r² → ω`, `K'/r → 2ω`, and eventually `K ≠ 0` and `K² − LΔ > 0` (for `ω ≠ 0`). -/
theorem il_eventually_radialK (M Q e ω L : ℝ) (hω : ω ≠ 0) :
    ∀ᶠ r in atTop, radialK e ω r ≠ 0 ∧ 0 < radialK e ω r ^ 2 - L * delta M Q r := by
  have h1 := (Infinity.tendsto_radialK_div_sq e ω).eventually_ne hω
  have h2 := (il_tendsto_radicand_div M Q e ω L).eventually (lt_mem_nhds (pow_pos
    (abs_pos.2 hω) 2 |>.trans_eq (sq_abs ω)))
  filter_upwards [h1, h2, eventually_gt_atTop 0] with r hr1 hr2 hr
  refine ⟨fun h => hr1 (by rw [h, zero_div]), ?_⟩
  have := (lt_div_iff₀ (by positivity : (0 : ℝ) < r ^ 4)).1 hr2
  nlinarith [pow_pos hr 4, sq_nonneg ω]

/-- `K'(r)/r → 2ω` as `r → ∞`, with `K' = 2ωr − e`. -/
theorem il_tendsto_radialK'_div (e ω : ℝ) :
    Tendsto (fun r : ℝ => (2 * ω * r - e) / r) atTop (𝓝 (2 * ω)) := by
  have h := (tendsto_const_nhds (x := 2 * ω)).sub
    ((tendsto_const_nhds (x := e)).div_atTop tendsto_id)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  simp only [id]
  field_simp

end ModeStability.AllAngular

end
