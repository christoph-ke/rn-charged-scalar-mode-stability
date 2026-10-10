module

public import Mathlib
public import ModeStability.AllAngular.AngularReduction
public import ModeStability.AllAngular.CoefficientIdentities
public import ModeStability.Endpoint.HorizonAux

/-!
# Auxiliary facts for the subextremal horizon limits with angular term

Helpers for the horizon limits (4.4) of the all-angular research notes in preparation, Section 4,
p. 5, constant normalization and reciprocal normalization, on the subextremal exterior
`|Q| < M`, for any real `L`, with `a = outerHorizon M Q`, `K = radialK e ω`, `Δ = delta M Q`,
`P = √(K² − LΔ)`, `P' = (2KK' − L·2(r − M))/(2P)` (the `r`-derivative of `P`) and `s = sgn K(a)`.

* Signs and the neighbourhood of `a` where `K(r)K(a) > 0` and `K² − LΔ > 0`
  (`hl_eventually_good`); there `sgn K(r) = s` and `k̂ = s g² P`.
* The Θ-form profile `R̃ = e^{iΘ}R` of the horizon condition (1.4):
  `R̃' = e^{iΘ}(R' + i(K/Δ)R)` (`hl_hasDerivAt_profile`), `R̃ → B`, `R̃'` bounded.
* `P → |K(a)|`, `P' → P'(a)`, and the phase correction
  `F = (sP − K)/Δ = −sL/(P + sK) → −sL/(|K(a)| + sK(a))` (`hl_tendsto_phaseCorrection`): this is
  the integrable correction (4.3) between `k̂` and `k` in the `r` variable.
* The derivatives of `k̂(x) = sgn K · (1/x)² · P` (reciprocal, `r = r(x)`) and of
  `f̂(y) = −sgn K · P` (constant, `r = r(1/y)`) near the horizon.
* The pointwise algebra: the phase-free current written through `R̃` and `R̃'`
  (`hl_reciprocal_algebra`, `hl_constant_algebra`), using `ΔΘ' = K` exactly.
* The limit of the constant-normalization form (`hl_tendsto_constant_form`).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

variable {M Q e ω L : ℝ}

/-! ### Signs -/

/-- Two reals with positive product have the same sign. -/
theorem hl_sign_eq_of_mul_pos {t c : ℝ} (h : 0 < t * c) :
    (SignType.sign t : ℝ) = SignType.sign c := by
  rcases mul_pos_iff.1 h with ⟨ht, hc⟩ | ⟨ht, hc⟩
  · rw [sign_pos ht, sign_pos hc]
  · rw [sign_neg ht, sign_neg hc]

/-- `sgn(c)² = 1` for `c ≠ 0`. -/
theorem hl_sign_mul_sign {c : ℝ} (hc : c ≠ 0) :
    (SignType.sign c : ℝ) * SignType.sign c = 1 := by
  rcases hc.lt_or_gt with h | h
  · rw [sign_neg h]
    norm_num
  · rw [sign_pos h]
    norm_num

/-- Near `a`, `K(r)` has the sign of `K(a) ≠ 0` and `K(r)² − LΔ(r) > 0`. -/
theorem hl_eventually_good (L : ℝ) (hKa : radialK e ω (outerHorizon M Q) ≠ 0) :
    ∀ᶠ r in 𝓝 (outerHorizon M Q), 0 < radialK e ω r * radialK e ω (outerHorizon M Q) ∧
      0 < radialK e ω r ^ 2 - L * delta M Q r := by
  have hcK : Continuous (radialK e ω) := by
    unfold radialK
    fun_prop
  have hcΔ : Continuous (delta M Q) := by
    unfold delta
    fun_prop
  have hΔa : delta M Q (outerHorizon M Q) = 0 := by
    unfold delta
    ring
  have h1 : 0 < radialK e ω (outerHorizon M Q) * radialK e ω (outerHorizon M Q) :=
    mul_self_pos.2 hKa
  have h2 : 0 < radialK e ω (outerHorizon M Q) ^ 2 - L * delta M Q (outerHorizon M Q) := by
    rw [hΔa, mul_zero, sub_zero]
    positivity
  exact ((hcK.mul continuous_const).continuousAt.eventually (lt_mem_nhds h1)).and
    (((hcK.pow 2).sub (continuous_const.mul hcΔ)).continuousAt.eventually (lt_mem_nhds h2))

/-! ### The Θ-form profile `R̃ = e^{iΘ} R` -/

/-- `|e^{iθ}| = 1`. -/
theorem hl_norm_exp_I_mul (θ : ℝ) : ‖exp (I * (θ : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I θ

/-- `R̃' = e^{iΘ}(R' + i(K/Δ)R)` for `R̃ = e^{iΘ}R`, `Θ' = K/Δ`, at `r > a`. -/
theorem hl_hasDerivAt_profile {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ} {r : ℝ} (hr : outerHorizon M Q < r) (hRd : DifferentiableAt ℝ R r) :
    HasDerivAt (fun s => exp (I * (Θ s : ℂ)) * R s)
      (exp (I * (Θ r : ℂ)) *
        (deriv R r + I * ((radialK e ω r / delta M Q r : ℝ) : ℂ) * R r)) r := by
  have h1 : HasDerivAt (fun s => I * (Θ s : ℂ)) (I * ((radialK e ω r / delta M Q r : ℝ) : ℂ)) r :=
    ((hΘ r hr).ofReal_comp).const_mul I
  refine (h1.cexp.mul hRd.hasDerivAt).congr_deriv ?_
  ring

/-- `R̃ → B` as `r → a⁺`, from the first half of the horizon condition (1.4). -/
theorem hl_tendsto_profile {Θ : ℝ → ℝ} {R : ℝ → ℂ} {B : ℂ}
    (hH1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - B) =O[𝓝[>] (outerHorizon M Q)]
      (fun r => r - outerHorizon M Q)) :
    Tendsto (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) (𝓝[>] (outerHorizon M Q)) (𝓝 B) := by
  have h0 : Tendsto (fun r : ℝ => r - outerHorizon M Q) (𝓝[>] (outerHorizon M Q)) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.2 (tendsto_id.mono_left nhdsWithin_le_nhds)
  exact tendsto_sub_nhds_zero_iff.1 (hH1.trans_tendsto h0)

/-- `R̃'` is bounded as `r → a⁺`, from the second half of the horizon condition (1.4). -/
theorem hl_isBoundedUnder_deriv_profile {Θ : ℝ → ℝ} {R : ℝ → ℂ}
    (hH2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) =O[𝓝[>] (outerHorizon M Q)]
      (fun _ => (1 : ℝ))) :
    IsBoundedUnder (· ≤ ·) (𝓝[>] (outerHorizon M Q))
      (fun r => ‖deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) r‖) :=
  (isBigO_one_iff ℝ).1 hH2

/-! ### The coefficient `P = √(K² − LΔ)` near `a` -/

/-- `P(r) = √(K² − LΔ) → |K(a)|` as `r → a`. -/
theorem hl_tendsto_sqrt (L : ℝ) :
    Tendsto (fun r => Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r)) (𝓝 (outerHorizon M Q))
      (𝓝 |radialK e ω (outerHorizon M Q)|) := by
  have hc : Continuous (fun r => Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r)) := by
    unfold radialK delta
    fun_prop
  have hΔa : delta M Q (outerHorizon M Q) = 0 := by
    unfold delta
    ring
  have h := hc.tendsto (outerHorizon M Q)
  rwa [hΔa, mul_zero, sub_zero, Real.sqrt_sq_eq_abs] at h

/-- `P'(r) = (2KK' − L·2(r − M))/(2P) → P'(a)` as `r → a`, for `K(a) ≠ 0`. -/
theorem hl_tendsto_sqrt_deriv (L : ℝ) (hKa : radialK e ω (outerHorizon M Q) ≠ 0) :
    Tendsto (fun r => (2 * radialK e ω r * (2 * ω * r - e) - L * (2 * (r - M))) /
        (2 * Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r))) (𝓝 (outerHorizon M Q))
      (𝓝 ((2 * radialK e ω (outerHorizon M Q) * (2 * ω * outerHorizon M Q - e) -
          L * (2 * (outerHorizon M Q - M))) / (2 * |radialK e ω (outerHorizon M Q)|))) := by
  have hnum : Continuous (fun r => 2 * radialK e ω r * (2 * ω * r - e) - L * (2 * (r - M))) := by
    unfold radialK
    fun_prop
  exact (hnum.tendsto _).div ((hl_tendsto_sqrt L).const_mul 2)
    (mul_ne_zero two_ne_zero (abs_pos.2 hKa).ne')

/-- The phase correction `F = (sP − K)/Δ`, `s = sgn K(a)`, equals `−sL/(P + sK)` near `a` and
tends to `−sL/(|K(a)| + sK(a))` as `r → a⁺`. -/
theorem hl_tendsto_phaseCorrection (hQ : |Q| < M) (L : ℝ)
    (hKa : radialK e ω (outerHorizon M Q) ≠ 0) :
    Tendsto (fun r => ((SignType.sign (radialK e ω (outerHorizon M Q)) : ℝ) *
          Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r) - radialK e ω r) / delta M Q r)
      (𝓝[>] (outerHorizon M Q))
      (𝓝 (-((SignType.sign (radialK e ω (outerHorizon M Q)) : ℝ) * L) /
        (|radialK e ω (outerHorizon M Q)| +
          (SignType.sign (radialK e ω (outerHorizon M Q)) : ℝ) *
            radialK e ω (outerHorizon M Q)))) := by
  set s : ℝ := (SignType.sign (radialK e ω (outerHorizon M Q)) : ℝ) with hs
  have hss : s * s = 1 := hl_sign_mul_sign hKa
  have hsKa : s * radialK e ω (outerHorizon M Q) = |radialK e ω (outerHorizon M Q)| :=
    sign_mul_self _
  have hKa' : 0 < |radialK e ω (outerHorizon M Q)| := abs_pos.2 hKa
  have hcK : Continuous (radialK e ω) := by
    unfold radialK
    fun_prop
  have hlim : Tendsto (fun r => -(s * L) /
      (Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r) + s * radialK e ω r))
      (𝓝 (outerHorizon M Q))
      (𝓝 (-(s * L) / (|radialK e ω (outerHorizon M Q)| + s * radialK e ω (outerHorizon M Q)))) :=
    tendsto_const_nhds.div ((hl_tendsto_sqrt L).add ((hcK.tendsto _).const_mul s))
      (by rw [hsKa]; positivity)
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hl_eventually_good L hKa)]
    with r hr hg
  obtain ⟨h1, h2⟩ := hg
  have hΔ : delta M Q r ≠ 0 := (delta_pos hQ hr).ne'
  have hsr : s * radialK e ω r = |radialK e ω r| := by
    rw [hs, ← hl_sign_eq_of_mul_pos h1]
    exact sign_mul_self _
  have hKr : radialK e ω r ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact lt_irrefl _ h1
  have hpos : 0 < Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r) + s * radialK e ω r := by
    rw [hsr]
    have := abs_pos.2 hKr
    positivity
  have hsq : Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r) ^ 2 =
      radialK e ω r ^ 2 - L * delta M Q r := Real.sq_sqrt h2.le
  field_simp
  linear_combination (-s) * hsq - Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r) *
    radialK e ω r * hss

/-! ### The derivatives of the coefficients near the horizon -/

/-- Reciprocal normalization: where `sgn K(r(y)) = s` near `x` and `K² − LΔ > 0` at `r(x)`,
`k̂(y) = sgn K · (1/y)² · P(r(y))` has `k̂'(x) = s(P'Δ/x⁴ − 2P/x³)` at `r = r(x)`. -/
theorem hl_hasDerivAt_reciprocal_khat (hQ : |Q| < M) {x s : ℝ} (hx : 0 < x)
    (hs : ∀ᶠ y in 𝓝 x, (SignType.sign (radialK e ω (radiusOf M Q y)) : ℝ) = s)
    (hP : 0 < radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)) :
    HasDerivAt (fun y : ℝ => (SignType.sign (radialK e ω (radiusOf M Q y)) : ℝ) * (1 / y) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q y) ^ 2 - L * delta M Q (radiusOf M Q y)))
      (s * ((2 * radialK e ω (radiusOf M Q x) * (2 * ω * radiusOf M Q x - e) -
            L * (2 * (radiusOf M Q x - M))) /
          (2 * Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x))) *
          delta M Q (radiusOf M Q x) / x ^ 4 -
        2 * Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)) /
          x ^ 3)) x := by
  have hev : (fun y : ℝ => (SignType.sign (radialK e ω (radiusOf M Q y)) : ℝ) * (1 / y) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q y) ^ 2 - L * delta M Q (radiusOf M Q y))) =ᶠ[𝓝 x]
      fun y : ℝ => s * (1 / y) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q y) ^ 2 - L * delta M Q (radiusOf M Q y)) := by
    filter_upwards [hs] with y hy
    rw [hy]
  have hsq : HasDerivAt
      (fun y => Real.sqrt (radialK e ω (radiusOf M Q y) ^ 2 - L * delta M Q (radiusOf M Q y)))
      ((2 * radialK e ω (radiusOf M Q x) * (2 * ω * radiusOf M Q x - e) -
            L * (2 * (radiusOf M Q x - M))) /
          (2 * Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x))) *
        (delta M Q (radiusOf M Q x) / x ^ 2)) x :=
    ((CoefficientIdentities.hasDerivAt_radicand M Q e ω L (radiusOf M Q x)).sqrt hP.ne').comp x
      (hasDerivAt_radiusOf hQ hx)
  have hinv : HasDerivAt (fun y : ℝ => (1 / y) ^ 2) (-2 / x ^ 3) x := by
    simp only [one_div]
    refine ((hasDerivAt_inv hx.ne').fun_pow 2).congr_deriv ?_
    have hx0 : x ≠ 0 := hx.ne'
    norm_num
    field_simp
  refine (((hinv.const_mul s).mul hsq).congr_of_eventuallyEq hev).congr_deriv ?_
  ring

/-- Constant normalization: where `sgn K(r(1/t)) = s` near `y` and `K² − LΔ > 0` at `r(1/y)`,
`f̂(t) = −sgn K · P(r(1/t))` has `f̂'(y) = s Δ P'` at `r = r(1/y)` (since `dr/dy = −Δ`). -/
theorem hl_hasDerivAt_constant_fhat (hQ : |Q| < M) {y s : ℝ} (hy : 0 < y)
    (hs : ∀ᶠ t in 𝓝 y, (SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) = s)
    (hP : 0 < radialK e ω (radiusOf M Q (1 / y)) ^ 2 - L * delta M Q (radiusOf M Q (1 / y))) :
    HasDerivAt (fun t : ℝ => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
        Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / t)))))
      (s * (delta M Q (radiusOf M Q (1 / y)) *
        ((2 * radialK e ω (radiusOf M Q (1 / y)) * (2 * ω * radiusOf M Q (1 / y) - e) -
            L * (2 * (radiusOf M Q (1 / y) - M))) /
          (2 * Real.sqrt (radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
            L * delta M Q (radiusOf M Q (1 / y))))))) y := by
  have hev : (fun t : ℝ => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
        Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / t))))) =ᶠ[𝓝 y]
      fun t : ℝ => -(s * Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / t)))) := by
    filter_upwards [hs] with t ht
    rw [ht]
  have hsq := ((CoefficientIdentities.hasDerivAt_radicand M Q e ω L
    (radiusOf M Q (1 / y))).sqrt hP.ne').comp y (hasDerivAt_radiusOf_one_div hQ hy)
  refine ((hsq.const_mul s).neg.congr_of_eventuallyEq hev).congr_deriv ?_
  ring

/-! ### Pointwise algebra -/

/-- Reciprocal normalization: with `kh = s(1/x)²P`, `kh' = s(P'Δ/x⁴ − 2P/x³)`, `s ≠ 0`,
`U' = R + (1/x)ΔR'`, `U = xR`, `R̃ = pR`, `|p| = 1`, `R̃' = p(R' + i(K/Δ)R)`, the phase-free
current `−(kh/kh')|U' + i kh U|² − Re(U'Ū)` equals
`−x(P/(P'D − 2P))|R̃ + DR̃' + iDF R̃|² − x|R̃|² − Re(ΔR̃' conj R̃)` with `D = Δ/x`,
`F = (sP − K)/Δ`. -/
theorem hl_reciprocal_algebra {x Δ K P P' s kh kh' : ℝ} {p R R' Rt Rt' : ℂ} (hx : 0 < x)
    (hΔ : Δ ≠ 0) (hs : s ≠ 0) (hp : ‖p‖ = 1) (hRt : Rt = p * R)
    (hRt' : Rt' = p * (R' + I * ((K / Δ : ℝ) : ℂ) * R))
    (hkh : kh = s * (1 / x) ^ 2 * P) (hkh' : kh' = s * (P' * Δ / x ^ 4 - 2 * P / x ^ 3)) :
    -(kh / kh') * ‖R + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * R') +
          ((1 : ℝ) : ℂ) * (kh : ℂ) * I * ((x : ℂ) * R)‖ ^ 2 -
        ((R + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * R')) * (starRingEnd ℂ) ((x : ℂ) * R)).re =
      -(x * (P / (P' * (Δ / x) - 2 * P))) *
          ‖Rt + ((Δ / x : ℝ) : ℂ) * Rt' + I * ((Δ / x * ((s * P - K) / Δ) : ℝ) : ℂ) * Rt‖ ^ 2 -
        x * ‖Rt‖ ^ 2 - ((Δ : ℂ) * Rt' * (starRingEnd ℂ) Rt).re := by
  have hx0 : x ≠ 0 := hx.ne'
  have hratio : kh / kh' = x * (P / (P' * (Δ / x) - 2 * P)) := by
    have h1 : s * (1 / x) ^ 2 * P = s * (P / x ^ 2) := by ring
    rw [hkh, hkh', h1, mul_div_mul_left _ _ hs]
    exact Endpoint.ratio_eq hx0
  have key : Rt + ((Δ / x : ℝ) : ℂ) * Rt' + I * ((Δ / x * ((s * P - K) / Δ) : ℝ) : ℂ) * Rt =
      p * (R + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * R') +
        ((1 : ℝ) : ℂ) * (kh : ℂ) * I * ((x : ℂ) * R)) := by
    subst hRt hRt' hkh
    have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx0
    have hΔ' : (Δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ
    push_cast
    field_simp
    ring
  have hnorm : ‖R + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * R') +
      ((1 : ℝ) : ℂ) * (kh : ℂ) * I * ((x : ℂ) * R)‖ =
      ‖Rt + ((Δ / x : ℝ) : ℂ) * Rt' + I * ((Δ / x * ((s * P - K) / Δ) : ℝ) : ℂ) * Rt‖ := by
    rw [key, norm_mul, hp, one_mul]
  have hRt'' : Rt' = p * (R' + I * K * R / ((Δ - 0 : ℝ) : ℂ)) := by
    rw [hRt', sub_zero]
    push_cast
    ring
  rw [hratio, hnorm, Endpoint.re_combination hx0 hp hRt hRt'']
  ring

/-- Constant normalization: with `fh = −sP`, `fh' = s(ΔP')`, `s ≠ 0`, `U_y = −ΔR'`, `U = R`,
`R̃ = pR`, `|p| = 1`, `R̃' = p(R' + i(K/Δ)R)`, the phase-free current
`−(fh/fh')|U_y + i fh U|² − Re(U_yŪ)` equals `Δ(P/P')|R̃' + iF R̃|² + Re(ΔR̃' conj R̃)` with
`F = (sP − K)/Δ`. -/
theorem hl_constant_algebra {Δ K P P' s fh fh' : ℝ} {p R R' Rt Rt' : ℂ} (hΔ : Δ ≠ 0)
    (hs : s ≠ 0) (hp : ‖p‖ = 1) (hRt : Rt = p * R)
    (hRt' : Rt' = p * (R' + I * ((K / Δ : ℝ) : ℂ) * R))
    (hfh : fh = -(s * P)) (hfh' : fh' = s * (Δ * P')) :
    -(fh / fh') * ‖-(Δ : ℂ) * R' + ((1 : ℝ) : ℂ) * (fh : ℂ) * I * R‖ ^ 2 -
        (-(Δ : ℂ) * R' * (starRingEnd ℂ) R).re =
      Δ * (P / P') * ‖Rt' + I * (((s * P - K) / Δ : ℝ) : ℂ) * Rt‖ ^ 2 +
        ((Δ : ℂ) * Rt' * (starRingEnd ℂ) Rt).re := by
  have hratio : -(fh / fh') = P / (Δ * P') := by
    rw [hfh, hfh', neg_div, neg_neg, mul_div_mul_left _ _ hs]
  have key : (Δ : ℂ) * (Rt' + I * (((s * P - K) / Δ : ℝ) : ℂ) * Rt) =
      -p * (-(Δ : ℂ) * R' + ((1 : ℝ) : ℂ) * (fh : ℂ) * I * R) := by
    subst hRt hRt' hfh
    have hΔ' : (Δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ
    push_cast
    field_simp
    ring
  have hnorm : ‖-(Δ : ℂ) * R' + ((1 : ℝ) : ℂ) * (fh : ℂ) * I * R‖ =
      |Δ| * ‖Rt' + I * (((s * P - K) / Δ : ℝ) : ℂ) * Rt‖ := by
    have h := congrArg norm key
    rw [norm_mul, norm_mul, norm_neg, hp, one_mul, Complex.norm_real, Real.norm_eq_abs] at h
    exact h.symm
  have hpp : p * (starRingEnd ℂ) p = 1 := by
    rw [Complex.mul_conj', hp, ofReal_one, one_pow]
  have hRR : R * (starRingEnd ℂ) R = ((‖R‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj']
  have hre : (Δ : ℂ) * Rt' * (starRingEnd ℂ) Rt = (Δ : ℂ) * R' * (starRingEnd ℂ) R +
      I * ((K * ‖R‖ ^ 2 : ℝ) : ℂ) := by
    rw [hRt', hRt, map_mul]
    have hΔ' : (Δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ
    push_cast
    field_simp
    linear_combination ((Δ : ℂ) * R' * (starRingEnd ℂ) R + I * K * R * (starRingEnd ℂ) R) * hpp +
      (I * K) * hRR
  have hre' : ((Δ : ℂ) * Rt' * (starRingEnd ℂ) Rt).re =
      -(-(Δ : ℂ) * R' * (starRingEnd ℂ) R).re := by
    rw [hre, Complex.add_re, Complex.I_mul_re, Complex.ofReal_im, neg_zero, add_zero, neg_mul,
      neg_mul, Complex.neg_re, neg_neg]
  rw [hratio, hnorm, hre', mul_pow, sq_abs]
  rcases eq_or_ne P' 0 with h | h
  · simp [h]
  · field_simp
    ring

/-! ### The limit of the constant-normalization form -/

/-- If `Δ → 0`, `P` and `F` converge, `P' → P'(a) ≠ 0`, `R̃ → B` and `R̃'` stays bounded, then
`Δ(P/P')|R̃' + iF R̃|² + Re(ΔR̃' conj R̃) → 0`. -/
theorem hl_tendsto_constant_form {α : Type*} {l : Filter α} {Δ P P' F : α → ℝ}
    {Rt Rt' : α → ℂ} {Pa P'a Fa : ℝ} {B : ℂ} (hP'a : P'a ≠ 0) (hΔ : Tendsto Δ l (𝓝 0))
    (hP : Tendsto P l (𝓝 Pa)) (hP' : Tendsto P' l (𝓝 P'a)) (hF : Tendsto F l (𝓝 Fa))
    (hRt : Tendsto Rt l (𝓝 B)) (hRt' : IsBoundedUnder (· ≤ ·) l (fun t => ‖Rt' t‖)) :
    Tendsto (fun t => Δ t * (P t / P' t) * ‖Rt' t + I * ((F t : ℝ) : ℂ) * Rt t‖ ^ 2 +
      (((Δ t : ℝ) : ℂ) * Rt' t * (starRingEnd ℂ) (Rt t)).re) l (𝓝 0) := by
  have h1 : Tendsto (fun t => Δ t * (P t / P' t)) l (𝓝 0) := by
    simpa only [zero_mul, Pi.div_apply] using hΔ.mul (hP.div hP' hP'a)
  have hW : (fun t => Rt' t + I * ((F t : ℝ) : ℂ) * Rt t) =O[l] (fun _ => (1 : ℝ)) :=
    (hRt'.isBigO_one ℝ).add
      (((tendsto_const_nhds (x := I)).mul hF.ofReal |>.mul hRt).isBigO_one ℝ)
  have hW2 := hW.norm_left.pow 2
  simp only [one_pow] at hW2
  have hfirst := h1.zero_mul_isBoundedUnder_le ((isBigO_one_iff ℝ).1 hW2)
  have hΔc : Tendsto (fun t => ((Δ t : ℝ) : ℂ)) l (𝓝 0) := by
    simpa using hΔ.ofReal
  have hsecond := (Complex.continuous_re.tendsto _).comp
    ((hΔc.zero_mul_isBoundedUnder_le hRt').mul ((Complex.continuous_conj.tendsto B).comp hRt))
  have h := hfirst.add hsecond
  simp only [zero_mul, zero_re, add_zero] at h
  exact h

end ModeStability.AllAngular

end
