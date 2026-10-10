module

public import ModeStability.AllAngular.InfinityLimitsLAsymp
public import ModeStability.AllAngular.CoefficientIdentities

/-!
# The infinity limits of the current with angular term, for an abstract coordinate

the all-angular research notes in preparation, Section 4, pp. 5–6: the infinity half of (4.4),
`J[v_I] → 0`, with the angular term `L ≥ 0` and `f = k̂ = sgn(K) g² √(K² − LΔ)` of (3.2), stated
for an abstract coordinate map `ρ : x ↦ r` so that the subextremal and the extremal cases share
one
proof. The current is in its phase-free form (`dephasedCurrent_dephase_eq_on`, σ = −1)
`J = −(f/f_x)|U_x − ifU|² − Re(U_x Ū)`, and the infinity condition (1.5) is in Θ-form:
`R̃ = r e^{−iΘ} R`, `R̃ − B = O(r⁻¹)`, `R̃' = O(r⁻²)`, `Θ' = K/Δ`.

* `il_reciprocal_current_tendsto` (reciprocal normalization, `x → ∞`): for `ρ` with
  `ρ' = Δ(ρ)/x²`, `ρ → ∞`, a gauge `g` with `g(ρ(x)) = 1/x`, `rg → 1`, `r − gΔ → M`, and the
  coefficient `gS/N` bounded (`S = K² − LΔ`, `N = ΔKK' − LΔ(r − M) − 2g⁻¹S`): `J → 0` for
  `U(x) = x R(ρ(x))`, `k̂(x) = sgn(K) x⁻² √S` at `r = ρ(x)`. Route: `k̂/k̂_x = x³ · gS/N`,
  `|x²(U' − ik̂U)|` and `|U|` are bounded (`il_reciprocal_algebra`, `il_reciprocal_isBigO`), so
  `(k̂/k̂_x)|U' − ik̂U|² = O(x⁻¹)` and `|U' − ik̂U||U| = O(x⁻²)`.
* `il_constant_current_tendsto` (constant normalization, `y ↓ 0`): for `ρ` with
  `ρ' = −Δ(ρ)` and `ρ → ∞`: `J → 0` for `U(y) = R(ρ(y))`, `f̂(y) = −sgn(K)√S`. Route:
  `f̂/f̂_y = −S/(Δ(KK' − L(r − M))) = O(r⁻¹)`, `|U_y − if̂U|` is bounded and `|U| = |R̃|/r → 0`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-! ### Pointwise coefficient identities -/

/-- Reciprocal normalization: with `k = s x⁻² P`, `P = √S`, `s = ±1` and the chain-rule value of
`k_x` (`r' = Δ/x²`, `S' = 2KK' − 2L(r − M)`), `k/k_x/x³ = GS/N`, `G = 1/x`,
`N = ΔKK' − LΔ(r − M) − 2G⁻¹S`. -/
theorem il_reciprocal_coef_eq {x G s P S K K' L M r Δ : ℝ} (hx : 0 < x) (hs : s = 1 ∨ s = -1)
    (hP : 0 < P) (hPS : P ^ 2 = S) (hG : G = 1 / x) :
    s * (1 / x) ^ 2 * P /
        (s * (-2 / x ^ 3) * P + s * (1 / x) ^ 2 *
          ((2 * K * K' - L * (2 * (r - M))) * (Δ / x ^ 2) / (2 * P))) / x ^ 3 =
      G * S / (Δ * K * K' - L * Δ * (r - M) - 2 * (1 / G) * S) := by
  subst hPS hG
  have hx0 : x ≠ 0 := hx.ne'
  have hP0 : P ≠ 0 := hP.ne'
  have hden : s * (-2 / x ^ 3) * P + s * (1 / x) ^ 2 *
      ((2 * K * K' - L * (2 * (r - M))) * (Δ / x ^ 2) / (2 * P)) =
      s * (Δ * K * K' - L * Δ * (r - M) - 2 * (1 / (1 / x)) * P ^ 2) / (x ^ 4 * P) := by
    field_simp
    ring
  rw [hden]
  rcases eq_or_ne (Δ * K * K' - L * Δ * (r - M) - 2 * (1 / (1 / x)) * P ^ 2) 0 with h | h
  · rw [h]
    simp
  · rcases hs with rfl | rfl <;> field_simp

/-- Constant normalization: with `f = −sP`, `P = √S`, `s = ±1` and the chain-rule value of `f_y`
(`r' = −Δ`), `f/f_y = −S/(Δ(KK' − L(r − M)))`. -/
theorem il_constant_coef_eq {s P S K K' L M r Δ : ℝ} (hs : s = 1 ∨ s = -1) (hP : 0 < P)
    (hPS : P ^ 2 = S) :
    -(s * P) / -(s * ((2 * K * K' - L * (2 * (r - M))) * -Δ / (2 * P))) =
      -S / (Δ * (K * K' - L * (r - M))) := by
  subst hPS
  have hP0 : P ≠ 0 := hP.ne'
  rcases eq_or_ne Δ 0 with h | h
  · simp [h]
  rcases eq_or_ne (K * K' - L * (r - M)) 0 with h' | h'
  · have h'' : 2 * K * K' - L * (2 * (r - M)) = 0 := by linear_combination 2 * h'
    rw [h', h'']
    simp
  · rcases hs with rfl | rfl <;> field_simp

/-! ### Derivatives at a point of the coordinate interval -/

/-- `d/dy (1/y)² = −2/x³` at `x > 0`. -/
theorem il_hasDerivAt_one_div_sq {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (1 / y) ^ 2) (-2 / x ^ 3) x := by
  have h := (hasDerivAt_inv hx.ne').pow 2
  simp only [one_div]
  convert h using 1
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp

/-- The square root `√S(ρ(y))` of the radicand `S = K² − LΔ` along a coordinate map `ρ`. -/
theorem il_hasDerivAt_sqrt_radicand {M Q e ω L : ℝ} {ρ : ℝ → ℝ} {x ρ' : ℝ}
    (hρ : HasDerivAt ρ ρ' x) (hS : 0 < radialK e ω (ρ x) ^ 2 - L * delta M Q (ρ x)) :
    HasDerivAt (fun y => Real.sqrt (radialK e ω (ρ y) ^ 2 - L * delta M Q (ρ y)))
      ((2 * radialK e ω (ρ x) * (2 * ω * ρ x - e) - L * (2 * (ρ x - M))) * ρ' /
        (2 * Real.sqrt (radialK e ω (ρ x) ^ 2 - L * delta M Q (ρ x)))) x :=
  ((CoefficientIdentities.hasDerivAt_radicand M Q e ω L (ρ x)).comp x hρ).sqrt hS.ne'

/-- Near a point where `K(ρ) ≠ 0`, the coefficient `sgn(K(ρ)) c(y) √S(ρ)` equals
`s c(y) √S(ρ)` with the constant sign `s = sgn K(ρ(x))`. -/
theorem il_sign_comp_eventually {e ω : ℝ} {ρ : ℝ → ℝ} {x ρ' : ℝ} (hρ : HasDerivAt ρ ρ' x)
    (hK : radialK e ω (ρ x) ≠ 0) :
    ∀ᶠ y in 𝓝 x, (SignType.sign (radialK e ω (ρ y)) : ℝ) =
      SignType.sign (radialK e ω (ρ x)) :=
  il_sign_eventually ((CoefficientIdentities.hasDerivAt_radialK e ω (ρ x)).continuousAt.comp
    (f := ρ) hρ.continuousAt) hK

/-! ### The reciprocal normalization -/

/-- **Infinity limit, reciprocal normalization, abstract coordinate.** See the module docstring. -/
theorem il_reciprocal_current_tendsto {M Q e ω L : ℝ} (hL : 0 ≤ L) (hω : ω ≠ 0)
    {ρ g : ℝ → ℝ} (hρ : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt ρ (delta M Q (ρ x) / x ^ 2) x)
    (hg : ∀ x ∈ Ioi (0 : ℝ), g (ρ x) = 1 / x) (hρI : Tendsto ρ atTop atTop)
    (hrg : Tendsto (fun r => r * g r) atTop (𝓝 1))
    (hgΔ : Tendsto (fun r => r - g r * delta M Q r) atTop (𝓝 M))
    (hcoef : (fun r => g r * (radialK e ω r ^ 2 - L * delta M Q r) /
        (delta M Q r * radialK e ω r * (2 * ω * r - e) - L * delta M Q r * (r - M) -
          2 * (1 / g r) * (radialK e ω r ^ 2 - L * delta M Q r))) =O[atTop] (fun _ => (1 : ℝ)))
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - B) =O[atTop]
      (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹))
    {k : ℝ → ℝ}
    (hk : ∀ x ∈ Ioi (0 : ℝ), k x = (SignType.sign (radialK e ω (ρ x)) : ℝ) * (1 / x) ^ 2 *
      Real.sqrt (radialK e ω (ρ x) ^ 2 - L * delta M Q (ρ x)))
    {U : ℝ → ℂ} (hU : ∀ x ∈ Ioi (0 : ℝ), U x = (x : ℂ) * R (ρ x)) :
    Tendsto (fun x => -(k x / deriv k x) *
        ‖deriv U x + ((-1 : ℝ) : ℂ) * (k x : ℂ) * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) atTop (𝓝 0) := by
  have hF : Tendsto (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) atTop (𝓝 B) := by
    have h := (hI1.trans_tendsto tendsto_inv_atTop_zero).add_const B
    simpa only [sub_add_cancel, zero_add] using h
  have hevr : ∀ᶠ r in atTop, (outerHorizon M Q < r ∧ 0 < r) ∧
      (radialK e ω r ≠ 0 ∧ 0 < radialK e ω r ^ 2 - L * delta M Q r) :=
    ((eventually_gt_atTop _).and (eventually_gt_atTop 0)).and (il_eventually_radialK M Q e ω L hω)
  have hKh : ∀ᶠ r in atTop, |radialK e ω r - (SignType.sign (radialK e ω r) : ℝ) *
      Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r)| ≤
        L * delta M Q r / |radialK e ω r| := by
    filter_upwards [hevr] with r hr
    exact il_abs_sub_sign_mul_sqrt_le hr.2.1 (mul_nonneg hL (il_delta_pos hr.1.1).le)
      (by linarith [hr.2.2])
  obtain ⟨hΨ, hμ⟩ := il_reciprocal_isBigO hω hrg hgΔ hKh hF hI2
  -- the pointwise identities at `x`, `r = ρ(x)`
  have hpt : ∀ᶠ x in atTop, 0 < x ∧
      k x / deriv k x / x ^ 3 = g (ρ x) * (radialK e ω (ρ x) ^ 2 - L * delta M Q (ρ x)) /
        (delta M Q (ρ x) * radialK e ω (ρ x) * (2 * ω * ρ x - e) -
          L * delta M Q (ρ x) * (ρ x - M) -
          2 * (1 / g (ρ x)) * (radialK e ω (ρ x) ^ 2 - L * delta M Q (ρ x))) ∧
      ‖(x : ℂ) ^ 2 * (deriv U x + ((-1 : ℝ) : ℂ) * (k x : ℂ) * I * U x)‖ =
        ‖(fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) (ρ x) *
            ((ρ x - g (ρ x) * delta M Q (ρ x) : ℝ) : ℂ) +
          ((g (ρ x) * delta M Q (ρ x) / ρ x : ℝ) : ℂ) * ((ρ x : ℂ) ^ 2 *
            deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) (ρ x)) +
          I * ((ρ x * g (ρ x) * (radialK e ω (ρ x) - (SignType.sign (radialK e ω (ρ x)) : ℝ) *
            Real.sqrt (radialK e ω (ρ x) ^ 2 - L * delta M Q (ρ x))) : ℝ) : ℂ) *
            (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) (ρ x)‖ *
          (1 / (ρ x * g (ρ x))) ^ 2 ∧
      ‖U x‖ = ‖(fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) (ρ x)‖ *
        (1 / (ρ x * g (ρ x))) := by
    filter_upwards [eventually_gt_atTop 0, hρI.eventually hevr] with x hx hr
    obtain ⟨⟨hra, hr0⟩, hK0, hS0⟩ := hr
    have hxI : x ∈ Ioi (0 : ℝ) := hx
    -- `U' = R + x (Δ/x²) R'`
    have hUd : HasDerivAt U (R (ρ x) + (x : ℂ) *
        (((delta M Q (ρ x) / x ^ 2 : ℝ) : ℂ) * deriv R (ρ x))) x := by
      have h1 := ((hR _ hra).1.hasDerivAt).scomp x (hρ x hxI)
      have h2 := (hasDerivAt_id' x).ofReal_comp.mul h1
      have hev : U =ᶠ[𝓝 x] fun y => (y : ℂ) * R (ρ y) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy using hU y hy
      refine (h2.congr_of_eventuallyEq hev).congr_deriv ?_
      rw [Complex.real_smul]
      simp only [Function.comp_apply]
      push_cast
      ring
    -- `k_x` by the chain rule, with the locally constant sign
    have hkev : k =ᶠ[𝓝 x] fun y => (SignType.sign (radialK e ω (ρ x)) : ℝ) * (1 / y) ^ 2 *
        Real.sqrt (radialK e ω (ρ y) ^ 2 - L * delta M Q (ρ y)) := by
      filter_upwards [Ioi_mem_nhds hx, il_sign_comp_eventually (hρ x hxI) hK0] with y hy hys
      rw [hk y hy, hys]
    have hkd := (((il_hasDerivAt_one_div_sq hx).const_mul
      (SignType.sign (radialK e ω (ρ x)) : ℝ)).mul
        (il_hasDerivAt_sqrt_radicand (hρ x hxI) hS0)).congr_of_eventuallyEq hkev
    have hFd := il_hasDerivAt_profile (hΘ _ hra) (hR _ hra).1
    obtain ⟨hW, hUn⟩ := il_reciprocal_algebra (G := g (ρ x)) (dU := deriv U x) (kx := k x)
      (Kh := (SignType.sign (radialK e ω (ρ x)) : ℝ) *
        Real.sqrt (radialK e ω (ρ x) ^ 2 - L * delta M Q (ρ x))) hx hr0
      (il_delta_pos hra).ne' (il_norm_exp_neg_I_mul (Θ (ρ x))) (hg x hxI)
      (by rw [hk x hxI]; ring) hUd.deriv rfl hFd.deriv
    refine ⟨hx, ?_, ?_, ?_⟩
    · rw [hkd.deriv, hk x hxI]
      exact il_reciprocal_coef_eq hx (il_sign_eq_or hK0) (Real.sqrt_pos.2 hS0)
        (Real.sq_sqrt hS0.le) (hg x hxI)
    · rw [hU x hxI]
      exact hW
    · rw [hU x hxI]
      exact hUn
  have hφx := hcoef.comp_tendsto hρI
  have hΨx := hΨ.comp_tendsto hρI
  have hμx := hμ.comp_tendsto hρI
  refine il_current_tendsto_of (-1) ?_ ?_
  · have hO := (hφx.mul (hΨx.pow 2)).mul (isBigO_refl (fun x : ℝ => 1 / x) atTop)
    refine (hO.congr' ?_ ?_).trans_tendsto
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_id (α := ℝ)))
    · filter_upwards [hpt] with x hx
      obtain ⟨hx0, h1, h2, -⟩ := hx
      simp only [Function.comp_apply]
      rw [← h1, ← h2, norm_mul, norm_pow, Complex.norm_of_nonneg hx0.le]
      field_simp
    · filter_upwards with x
      simp
  · have hO := (hΨx.mul hμx).mul (isBigO_refl (fun x : ℝ => 1 / x ^ 2) atTop)
    refine (hO.congr' ?_ ?_).trans_tendsto
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_pow_atTop (α := ℝ) two_ne_zero))
    · filter_upwards [hpt] with x hx
      obtain ⟨hx0, -, h2, h3⟩ := hx
      simp only [Function.comp_apply]
      rw [← h2, ← h3, norm_mul, norm_pow, Complex.norm_of_nonneg hx0.le]
      field_simp
    · filter_upwards with x
      simp

/-! ### The constant normalization -/

/-- **Infinity limit, constant normalization, abstract coordinate.** See the module docstring. -/
theorem il_constant_current_tendsto {M Q e ω L : ℝ} (hL : 0 ≤ L) (hω : ω ≠ 0)
    {ρ : ℝ → ℝ} (hρ : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt ρ (-delta M Q (ρ y)) y)
    (hρI : Tendsto ρ (𝓝[>] 0) atTop)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - B) =O[atTop]
      (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹))
    {f : ℝ → ℝ}
    (hf : ∀ y ∈ Ioi (0 : ℝ), f y = -((SignType.sign (radialK e ω (ρ y)) : ℝ) *
      Real.sqrt (radialK e ω (ρ y) ^ 2 - L * delta M Q (ρ y))))
    {U : ℝ → ℂ} (hU : ∀ y ∈ Ioi (0 : ℝ), U y = R (ρ y)) :
    Tendsto (fun y => -(f y / deriv f y) *
        ‖deriv U y + ((-1 : ℝ) : ℂ) * (f y : ℂ) * I * U y‖ ^ 2 -
      (deriv U y * (starRingEnd ℂ) (U y)).re) (𝓝[>] 0) (𝓝 0) := by
  have hF : Tendsto (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) atTop (𝓝 B) := by
    have h := (hI1.trans_tendsto tendsto_inv_atTop_zero).add_const B
    simpa only [sub_add_cancel, zero_add] using h
  have hevr : ∀ᶠ r in atTop, (outerHorizon M Q < r ∧ 0 < r) ∧
      (radialK e ω r ≠ 0 ∧ 0 < radialK e ω r ^ 2 - L * delta M Q r) :=
    ((eventually_gt_atTop _).and (eventually_gt_atTop 0)).and (il_eventually_radialK M Q e ω L hω)
  have hKh : ∀ᶠ r in atTop, |radialK e ω r - (SignType.sign (radialK e ω r) : ℝ) *
      Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r)| ≤
        L * delta M Q r / |radialK e ω r| := by
    filter_upwards [hevr] with r hr
    exact il_abs_sub_sign_mul_sqrt_le hr.2.1 (mul_nonneg hL (il_delta_pos hr.1.1).le)
      (by linarith [hr.2.2])
  obtain ⟨hY, hFr⟩ := il_constant_isBigO hω hKh hF hI2
  have hpt : ∀ᶠ y in 𝓝[>] 0,
      f y / deriv f y = -(radialK e ω (ρ y) ^ 2 - L * delta M Q (ρ y)) /
        (delta M Q (ρ y) * (radialK e ω (ρ y) * (2 * ω * ρ y - e) - L * (ρ y - M))) ∧
      ‖deriv U y + ((-1 : ℝ) : ℂ) * (f y : ℂ) * I * U y‖ =
        ‖-(((delta M Q (ρ y) / ρ y ^ 2 : ℝ) : ℂ) * ((ρ y : ℂ) *
            deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) (ρ y))) +
          ((delta M Q (ρ y) / ρ y ^ 2 : ℝ) : ℂ) *
            (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) (ρ y) -
          I * (((radialK e ω (ρ y) - (SignType.sign (radialK e ω (ρ y)) : ℝ) *
            Real.sqrt (radialK e ω (ρ y) ^ 2 - L * delta M Q (ρ y))) / ρ y : ℝ) : ℂ) *
            (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) (ρ y)‖ ∧
      ‖U y‖ = ‖(fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) (ρ y)‖ * (1 / ρ y) := by
    filter_upwards [self_mem_nhdsWithin, hρI.eventually hevr] with y hy hr
    obtain ⟨⟨hra, hr0⟩, hK0, hS0⟩ := hr
    have hyI : y ∈ Ioi (0 : ℝ) := hy
    have hUd : HasDerivAt U (((-delta M Q (ρ y) : ℝ) : ℂ) * deriv R (ρ y)) y := by
      have h1 := ((hR _ hra).1.hasDerivAt).scomp y (hρ y hyI)
      have hev : U =ᶠ[𝓝 y] fun t => R (ρ t) := by
        filter_upwards [Ioi_mem_nhds hy] with t ht using hU t ht
      refine (h1.congr_of_eventuallyEq hev).congr_deriv ?_
      rw [Complex.real_smul]
    have hfev : f =ᶠ[𝓝 y] fun t => -((SignType.sign (radialK e ω (ρ y)) : ℝ) *
        Real.sqrt (radialK e ω (ρ t) ^ 2 - L * delta M Q (ρ t))) := by
      filter_upwards [Ioi_mem_nhds hy, il_sign_comp_eventually (hρ y hyI) hK0] with t ht hts
      rw [hf t ht, hts]
    have hfd := (((il_hasDerivAt_sqrt_radicand (hρ y hyI) hS0).const_mul
      (SignType.sign (radialK e ω (ρ y)) : ℝ)).neg).congr_of_eventuallyEq hfev
    have hFd := il_hasDerivAt_profile (hΘ _ hra) (hR _ hra).1
    obtain ⟨hW, hUn⟩ := il_constant_algebra (fy := f y) (dU := deriv U y)
      (Kh := (SignType.sign (radialK e ω (ρ y)) : ℝ) *
        Real.sqrt (radialK e ω (ρ y) ^ 2 - L * delta M Q (ρ y))) hr0
      (il_delta_pos hra).ne' (il_norm_exp_neg_I_mul (Θ (ρ y))) (hf y hyI) hUd.deriv rfl
      hFd.deriv
    refine ⟨?_, ?_, ?_⟩
    · rw [hfd.deriv, hf y hyI]
      exact il_constant_coef_eq (il_sign_eq_or hK0) (Real.sqrt_pos.2 hS0) (Real.sq_sqrt hS0.le)
    · rw [hU y hyI]
      exact hW
    · rw [hU y hyI]
      exact hUn
  have hφy := (il_constant_coef_tendsto (M := M) (Q := Q) (e := e) (L := L) hω).comp hρI
  have hYy := hY.comp_tendsto hρI
  have hFy := hFr.comp hρI
  refine il_current_tendsto_of (-1) ?_ ?_
  · have h := hφy.zero_mul_isBoundedUnder_le ((isBigO_one_iff ℝ).1
      ((hYy.pow 2).trans (isBigO_of_le _ fun _ => by simp)))
    refine h.congr' ?_
    filter_upwards [hpt] with y hy
    obtain ⟨h1, h2, -⟩ := hy
    simp only [Function.comp_apply]
    rw [h1, h2]
  · have h := hFy.zero_mul_isBoundedUnder_le ((isBigO_one_iff ℝ).1 hYy)
    refine h.congr' ?_
    filter_upwards [hpt] with y hy
    obtain ⟨-, h2, h3⟩ := hy
    simp only [Function.comp_apply]
    rw [h2, h3, mul_comm]

end ModeStability.AllAngular

end
