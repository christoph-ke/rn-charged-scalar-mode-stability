module

public import Mathlib
public import ModeStability.AllAngular.HorizonLimitsLAux

/-!
# The subextremal horizon limits of the current with angular term

Source: the all-angular research notes in preparation, Section 4, p. 5, the horizon half of
(4.4), constant normalization: `a < r₀ < 2M` and reciprocal normalization: `r₀ ≥ 2M`,
on the subextremal exterior `|Q| < M`, for real `L` and `K(a) ≠ 0`, in the phase-free form
`J = −(k̂/k̂_x)|U_x + ik̂U|² − Re(U_x Ū)` (plus sign at the horizon), with the Θ-form horizon
condition (1.4): `R̃ = e^{iΘ}R`, `Θ' = K/Δ`, `R̃ − B = O(r − a)`, `R̃' = O(1)`.

* Reciprocal normalization (`reciprocal_horizon_current_tendsto_L`): `x → 0⁺`,
  `U(x) = xR(r(x))`, `k̂ = sgn K · x⁻² √(K² − LΔ)`. With `P = √(K² − LΔ)`, `s = sgn K(a)`,
  `F = (sP − K)/Δ`, `D = Δ/x`, near the horizon
  `J = −x(P/(P'D − 2P))|R̃ + DR̃' + iDF R̃|² − x|R̃|² − Re(ΔR̃' conj R̃)`
  (`hl_reciprocal_algebra`), and `D → 0` by (2.11), `P → |K(a)| ≠ 0`, `F` converges, so `J → 0`
  (`Endpoint.tendsto_current_form`). This is the paper's `k̂/k̂_x = −(x/2)(1 + o(1))`,
  `v_H = Bx + o(x)`, `(v_H)_x = B + o(1)`.
* Constant normalization (`constant_horizon_current_tendsto_L`): `y → ∞` (`r ↓ a`),
  `U(y) = R(r(1/y))`, `f̂ = −sgn K · √(K² − LΔ)`. Near the horizon
  `J = Δ(P/P')|R̃' + iF R̃|² + Re(ΔR̃' conj R̃)` (`hl_constant_algebra`), where
  `P'(a) = s λ_H`, `λ_H = K'(a) − L(a − b)/(2K(a))`; for `λ_H ≠ 0` this tends to `0`
  (`hl_tendsto_constant_form`). This is the paper's `k̂ = K(a) + λ_H t + O(t²)`,
  `v_H = B + O(t)`, `(v_H)_x = O(Δ)`, `k̂/k̂_x = O(Δ⁻¹)`.

The sign `L ≥ 0` is not used by these limits.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- `Δ(r(x)) → 0` as `x → 0⁺`. -/
theorem hl_tendsto_delta_radiusOf {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (fun x => delta M Q (radiusOf M Q x)) (𝓝[>] 0) (𝓝 0) := by
  have hr' : Tendsto (radiusOf M Q) (𝓝[>] 0) (𝓝 (outerHorizon M Q)) :=
    (Endpoint.tendsto_radiusOf_nhdsGT hQ).mono_right nhdsWithin_le_nhds
  have hcΔ : Continuous (delta M Q) := by
    unfold delta
    fun_prop
  have hΔa : delta M Q (outerHorizon M Q) = 0 := by
    unfold delta
    ring
  have h := (hcΔ.tendsto (outerHorizon M Q)).comp hr'
  rw [hΔa] at h
  exact h

/-- `Δ(r(x))/x → 0` as `x → 0⁺`, from (2.11). -/
theorem hl_tendsto_delta_radiusOf_div {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (fun x => delta M Q (radiusOf M Q x) / x) (𝓝[>] 0) (𝓝 0) := by
  have hr' : Tendsto (radiusOf M Q) (𝓝[>] 0) (𝓝 (outerHorizon M Q)) :=
    (Endpoint.tendsto_radiusOf_nhdsGT hQ).mono_right nhdsWithin_le_nhds
  have h := (Endpoint.tendsto_radiusOf_sub_div hQ).mul (hr'.sub_const (innerHorizon M Q))
  rw [zero_mul] at h
  refine h.congr fun x => ?_
  unfold delta
  ring

/-- The subextremal horizon limit (4.4) in the reciprocal normalization, with angular term:
for `|Q| < M`, `K(a) ≠ 0`, a solution `R` of `(ΔR')' + (K²/Δ − L)R = 0` on `r > a` satisfying the
Θ-form horizon condition (1.4), the phase-free current
`J = −(k̂/k̂_x)|U_x + ik̂U|² − Re(U_x Ū)` of `U(x) = xR(r(x))`,
`k̂(x) = sgn K(r(x)) · (1/x)² · √(K² − LΔ)(r(x))`, tends to `0` as `x → 0⁺`. -/
theorem reciprocal_horizon_current_tendsto_L {M Q e ω L : ℝ} (hQ : |Q| < M) (_hL : 0 ≤ L)
    (hKa : radialK e ω (outerHorizon M Q) ≠ 0)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hH1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - B) =O[𝓝[>] (outerHorizon M Q)]
      (fun r => r - outerHorizon M Q))
    (hH2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) =O[𝓝[>] (outerHorizon M Q)]
      (fun _ => (1 : ℝ))) :
    Tendsto (fun x : ℝ =>
        -(((SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) * (1 / x) ^ 2 *
              Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x))) /
            deriv (fun y : ℝ => (SignType.sign (radialK e ω (radiusOf M Q y)) : ℝ) *
              (1 / y) ^ 2 *
              Real.sqrt (radialK e ω (radiusOf M Q y) ^ 2 - L * delta M Q (radiusOf M Q y))) x) *
          ‖deriv (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x +
            ((1 : ℝ) : ℂ) * (((SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) * (1 / x) ^ 2 *
              Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)) :
                ℝ) : ℂ) * I *
              ((x : ℂ) * R (radiusOf M Q x))‖ ^ 2 -
        (deriv (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x *
          (starRingEnd ℂ) ((x : ℂ) * R (radiusOf M Q x))).re)
      (𝓝[>] 0) (𝓝 0) := by
  set s : ℝ := (SignType.sign (radialK e ω (outerHorizon M Q)) : ℝ) with hs
  have hs0 : s ≠ 0 := by
    intro h
    have h1 : s * radialK e ω (outerHorizon M Q) = |radialK e ω (outerHorizon M Q)| :=
      sign_mul_self _
    rw [h, zero_mul] at h1
    exact (abs_pos.2 hKa).ne h1
  have hr := Endpoint.tendsto_radiusOf_nhdsGT hQ
  have hr' : Tendsto (radiusOf M Q) (𝓝[>] 0) (𝓝 (outerHorizon M Q)) :=
    hr.mono_right nhdsWithin_le_nhds
  -- the limits of the coefficients along `x → 0⁺`
  have hP : Tendsto (fun x => Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 -
      L * delta M Q (radiusOf M Q x))) (𝓝[>] 0) (𝓝 |radialK e ω (outerHorizon M Q)|) :=
    (hl_tendsto_sqrt L).comp hr'
  have hP' : Tendsto (fun x => (2 * radialK e ω (radiusOf M Q x) * (2 * ω * radiusOf M Q x - e) -
        L * (2 * (radiusOf M Q x - M))) /
      (2 * Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x))))
      (𝓝[>] 0) (𝓝 ((2 * radialK e ω (outerHorizon M Q) * (2 * ω * outerHorizon M Q - e) -
          L * (2 * (outerHorizon M Q - M))) / (2 * |radialK e ω (outerHorizon M Q)|))) :=
    (hl_tendsto_sqrt_deriv L hKa).comp hr'
  have hF : Tendsto (fun x => (s * Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 -
        L * delta M Q (radiusOf M Q x)) - radialK e ω (radiusOf M Q x)) /
      delta M Q (radiusOf M Q x)) (𝓝[>] 0)
      (𝓝 (-(s * L) / (|radialK e ω (outerHorizon M Q)| + s * radialK e ω (outerHorizon M Q)))) :=
    (hl_tendsto_phaseCorrection hQ L hKa).comp hr
  have hD := hl_tendsto_delta_radiusOf_div hQ
  have hE : Tendsto (fun x => delta M Q (radiusOf M Q x) / x *
      ((s * Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)) -
        radialK e ω (radiusOf M Q x)) / delta M Q (radiusOf M Q x))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using hD.mul hF
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hRt : Tendsto (fun x => exp (I * (Θ (radiusOf M Q x) : ℂ)) * R (radiusOf M Q x))
      (𝓝[>] 0) (𝓝 B) :=
    (hl_tendsto_profile hH1).comp hr
  have hRt' : IsBoundedUnder (· ≤ ·) (𝓝[>] 0)
      (fun x => ‖deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) (radiusOf M Q x)‖) :=
    hr.isBoundedUnder_comp (hl_isBoundedUnder_deriv_profile hH2)
  have hlim := Endpoint.tendsto_current_form (abs_pos.2 hKa).ne' hx hP hP' hD hE
    (hl_tendsto_delta_radiusOf hQ) hRt hRt'
  refine hlim.congr' ?_
  -- the pointwise identity near the horizon
  have hgood := (hl_eventually_good L hKa).eventually_nhds
  filter_upwards [self_mem_nhdsWithin, hr'.eventually hgood] with x hx hgx
  have hra := outerHorizon_lt_radiusOf hQ hx
  have hsev : ∀ᶠ y in 𝓝 x, (SignType.sign (radialK e ω (radiusOf M Q y)) : ℝ) = s :=
    ((hasDerivAt_radiusOf hQ hx).continuousAt.eventually hgx).mono fun y hy =>
      hl_sign_eq_of_mul_pos hy.1
  have hsx : (SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) = s := hsev.self_of_nhds
  rw [(hl_hasDerivAt_reciprocal_khat hQ hx hsev hgx.self_of_nhds.2).deriv,
    (hasDerivAt_reciprocal_reduced_L hQ hR hx).deriv, staticSolution_radiusOf hQ hx]
  exact (hl_reciprocal_algebra hx (delta_pos hQ hra).ne' hs0 (hl_norm_exp_I_mul _) rfl
    (hl_hasDerivAt_profile hΘ hra (hR _ hra).1).deriv (by rw [hsx]) rfl).symm

/-- The subextremal horizon limit (4.4) in the constant normalization, with angular term:
for `|Q| < M`, `K(a) ≠ 0` and `λ_H = K'(a) − L(a − b)/(2K(a)) ≠ 0` (`K' = 2ωr − e`), a solution
`R` of `(ΔR')' + (K²/Δ − L)R = 0` on `r > a` satisfying the Θ-form horizon condition (1.4), the
phase-free current `J = −(f̂/f̂_y)|U_y + if̂U|² − Re(U_y Ū)` of `U(y) = R(r(1/y))`,
`f̂(y) = −sgn K(r(1/y)) · √(K² − LΔ)(r(1/y))`, tends to `0` as `y → ∞`. -/
theorem constant_horizon_current_tendsto_L {M Q e ω L : ℝ} (hQ : |Q| < M) (_hL : 0 ≤ L)
    (hKa : radialK e ω (outerHorizon M Q) ≠ 0)
    (hlH : 2 * ω * outerHorizon M Q - e -
      L * (outerHorizon M Q - innerHorizon M Q) / (2 * radialK e ω (outerHorizon M Q)) ≠ 0)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hH1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - B) =O[𝓝[>] (outerHorizon M Q)]
      (fun r => r - outerHorizon M Q))
    (hH2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) =O[𝓝[>] (outerHorizon M Q)]
      (fun _ => (1 : ℝ))) :
    Tendsto (fun y : ℝ =>
        -((-((SignType.sign (radialK e ω (radiusOf M Q (1 / y))) : ℝ) *
              Real.sqrt (radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
                L * delta M Q (radiusOf M Q (1 / y))))) /
            deriv (fun t : ℝ => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
              Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
                L * delta M Q (radiusOf M Q (1 / t))))) y) *
          ‖deriv (fun t : ℝ => R (radiusOf M Q (1 / t))) y +
            ((1 : ℝ) : ℂ) * ((-((SignType.sign (radialK e ω (radiusOf M Q (1 / y))) : ℝ) *
              Real.sqrt (radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
                L * delta M Q (radiusOf M Q (1 / y)))) : ℝ) : ℂ) * I *
              R (radiusOf M Q (1 / y))‖ ^ 2 -
        (deriv (fun t : ℝ => R (radiusOf M Q (1 / t))) y *
          (starRingEnd ℂ) (R (radiusOf M Q (1 / y)))).re)
      atTop (𝓝 0) := by
  set s : ℝ := (SignType.sign (radialK e ω (outerHorizon M Q)) : ℝ) with hs
  have hsKa : s * radialK e ω (outerHorizon M Q) = |radialK e ω (outerHorizon M Q)| :=
    sign_mul_self _
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsKa
    exact (abs_pos.2 hKa).ne hsKa
  -- `P'(a) = s λ_H ≠ 0`
  have hP'a : (2 * radialK e ω (outerHorizon M Q) * (2 * ω * outerHorizon M Q - e) -
      L * (2 * (outerHorizon M Q - M))) / (2 * |radialK e ω (outerHorizon M Q)|) ≠ 0 := by
    have h2 : 2 * (outerHorizon M Q - M) = outerHorizon M Q - innerHorizon M Q := by
      unfold outerHorizon innerHorizon
      ring
    have hnum : 2 * radialK e ω (outerHorizon M Q) * (2 * ω * outerHorizon M Q - e) -
        L * (2 * (outerHorizon M Q - M)) = 2 * radialK e ω (outerHorizon M Q) *
          (2 * ω * outerHorizon M Q - e -
            L * (outerHorizon M Q - innerHorizon M Q) / (2 * radialK e ω (outerHorizon M Q))) := by
      rw [h2]
      field_simp
    rw [hnum]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hKa) hlH)
      (mul_ne_zero two_ne_zero (abs_pos.2 hKa).ne')
  have hy : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝[>] 0) := by
    simpa only [one_div] using tendsto_inv_atTop_nhdsGT_zero
  have hr : Tendsto (fun y => radiusOf M Q (1 / y)) atTop (𝓝[>] (outerHorizon M Q)) :=
    (Endpoint.tendsto_radiusOf_nhdsGT hQ).comp hy
  have hr' : Tendsto (fun y => radiusOf M Q (1 / y)) atTop (𝓝 (outerHorizon M Q)) :=
    hr.mono_right nhdsWithin_le_nhds
  -- the limit in `r`
  have hcΔ : Continuous (delta M Q) := by
    unfold delta
    fun_prop
  have hΔa : delta M Q (outerHorizon M Q) = 0 := by
    unfold delta
    ring
  have hΔ : Tendsto (delta M Q) (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
    have h := hcΔ.tendsto (outerHorizon M Q)
    rw [hΔa] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hform := hl_tendsto_constant_form hP'a hΔ
    ((hl_tendsto_sqrt (e := e) (ω := ω) (M := M) (Q := Q) L).mono_left nhdsWithin_le_nhds)
    ((hl_tendsto_sqrt_deriv L hKa).mono_left nhdsWithin_le_nhds)
    (hl_tendsto_phaseCorrection hQ L hKa) (hl_tendsto_profile hH1)
    (hl_isBoundedUnder_deriv_profile hH2)
  refine (hform.comp hr).congr' ?_
  -- the pointwise identity near the horizon
  have hgood := (hl_eventually_good L hKa).eventually_nhds
  filter_upwards [eventually_gt_atTop 0, hr'.eventually hgood] with y hy hgy
  have hra := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy)
  have hsev : ∀ᶠ t in 𝓝 y, (SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) = s :=
    ((hasDerivAt_radiusOf_one_div hQ hy).continuousAt.eventually hgy).mono fun t ht =>
      hl_sign_eq_of_mul_pos ht.1
  have hsy : (SignType.sign (radialK e ω (radiusOf M Q (1 / y))) : ℝ) = s := hsev.self_of_nhds
  rw [(hl_hasDerivAt_constant_fhat hQ hy hsev hgy.self_of_nhds.2).deriv,
    (hasDerivAt_constant_reduced_L hQ hR hy).deriv]
  exact (hl_constant_algebra (delta_pos hQ hra).ne' hs0 (hl_norm_exp_I_mul _) rfl
    (hl_hasDerivAt_profile hΘ hra (hR _ hra).1).deriv (by rw [hsy]) rfl).symm

end ModeStability.AllAngular

end
