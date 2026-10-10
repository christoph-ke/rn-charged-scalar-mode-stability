module

public import Mathlib
public import ModeStability.AllAngular.ExtremalHorizonLimitsAux

/-!
# The extremal horizon limits of the current with angular term

Source: the all-angular research notes in preparation, Section 4, pp. 5–6, the horizon half of
(4.4) at an extremal
horizon, `|Q| = M` (so `a = b = M`, `Δ = (r − M)²`), for a real `L ≥ 0`:

* constant normalization (p. 5).;
* reciprocal normalization (pp. 5–6).

The current is used in its phase-free form
`J = −(f̂/f̂_t)|U_t + σ f̂ i U|² − Re(U_t Ū)` with `σ = 1` at the horizon, and the horizon
condition (1.4) in its Θ-form: `R̃ = e^{iΘ}R` with `Θ' = K/Δ` has `R̃ − B = O(r − M)` and
`R̃' = O(1)` as `r ↓ M`. Write `R̃' = e^{iΘ}(iΘ'R + R')`.

* Reciprocal (`extremal_reciprocal_horizon_current_tendsto_L`): `x = r − M ↓ 0`,
  `U(x) = xR(M + x)`, `k̂(x) = sgn K · x⁻² √(K² − Lx²)`. Since `xΘ' = K/x`,
  `e^{iΘ}(U_x + ik̂U) = R̃ + xR̃' + ix(k̂ − K/x²)R̃ → B` (`ex_recip_alg`,
  `ex_tendsto_recip_correction`) and `Re(U_xŪ) = Re((R̃ + xR̃') conj(xR̃)) → 0`, while
  `k̂/k̂_x → 0` (`ex_tendsto_recip_ratio`). Needs only `K(M) ≠ 0`.
* Constant (`extremal_constant_horizon_current_tendsto_L`): `y = 1/(r − M) → ∞`,
  `U(y) = R(M + 1/y)`, `f̂(y) = −sgn K · √(K² − L/y²)`, `U_y = −ΔR'`. Since `ΔΘ' = K`,
  `e^{iΘ}(U_y + if̂U) = Δ(−R̃' + iΔ⁻¹(K + f̂)R̃)` with `Δ⁻¹(K + f̂)` bounded
  (`ex_const_alg`, `ex_tendsto_const_correction`) and `Re(U_yŪ) = −Re(ΔR̃' conj R̃)`, while
  `(f̂/f̂_y)Δ` converges when `K'(M) = 2ωM − e ≠ 0` (`ex_tendsto_const_ratio`). So
  `J = −((f̂/f̂_y)Δ)·Δ|−R̃' + …|² + Re(ΔR̃' conj R̃) → 0`.

The hypothesis `0 ≤ L` of the source is kept in the statements, but it is not used: near the
horizon both coefficients are governed by `K(M) ≠ 0` alone.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-! ### Pointwise algebra -/

/-- Reciprocal algebra at `r = M + x`: with `R̃ = pR`, `|p| = 1`, `R̃' = p(iθR + R')` and
`U' = R + xR'`, `|U' + ik(xR)| = |R̃ + xR̃' + ix(k − θ)R̃|` and
`Re(U' conj(xR)) = Re((R̃ + xR̃') conj(xR̃))`. -/
theorem ex_recip_alg {x θ k : ℝ} {p R R' U' Rt Rt' : ℂ} (hp : ‖p‖ = 1)
    (hU' : U' = R + x * R') (hRt : Rt = p * R) (hRt' : Rt' = p * (I * θ * R + R')) :
    ‖U' + ((1 : ℝ) : ℂ) * (k : ℂ) * I * ((x : ℂ) * R)‖ =
        ‖Rt + x * Rt' + I * ((x * (k - θ) : ℝ) : ℂ) * Rt‖ ∧
      (U' * (starRingEnd ℂ) ((x : ℂ) * R)).re =
        ((Rt + x * Rt') * (starRingEnd ℂ) ((x : ℂ) * Rt)).re := by
  have hpp : p * (starRingEnd ℂ) p = 1 := by
    rw [Complex.mul_conj', hp, ofReal_one, one_pow]
  have hRR : R * (starRingEnd ℂ) R = ((‖R‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj']
  subst hU' hRt hRt'
  constructor
  · have key : p * R + x * (p * (I * θ * R + R')) + I * ((x * (k - θ) : ℝ) : ℂ) * (p * R) =
        p * (R + x * R' + ((1 : ℝ) : ℂ) * (k : ℂ) * I * ((x : ℂ) * R)) := by
      push_cast
      ring
    rw [key, norm_mul, hp, one_mul]
  · have key : (p * R + x * (p * (I * θ * R + R'))) * (starRingEnd ℂ) ((x : ℂ) * (p * R)) =
        (R + x * R') * (starRingEnd ℂ) ((x : ℂ) * R) + I * ((x ^ 2 * θ * ‖R‖ ^ 2 : ℝ) : ℂ) := by
      simp only [map_mul, Complex.conj_ofReal]
      push_cast
      linear_combination ((x : ℂ) * (R + x * I * θ * R + x * R') * (starRingEnd ℂ) R) * hpp +
        ((x : ℂ) ^ 2 * I * θ) * hRR
    rw [key, Complex.add_re, Complex.I_mul_re, Complex.ofReal_im, neg_zero, add_zero]

/-- Constant algebra at `r = M + 1/y`: with `R̃ = pR`, `|p| = 1`, `R̃' = p(iθR + R')`,
`θ y⁻² = K` and `U_y = −R'/y²`, `|U_y + ifR| = y⁻² |−R̃' + i y²(K + f) R̃|` and
`Re(U_y R̄) = −Re((y⁻² R̃') conj R̃)`. -/
theorem ex_const_alg {y θ f K : ℝ} {p R R' Uy Rt Rt' : ℂ} (hy : y ≠ 0) (hp : ‖p‖ = 1)
    (hUy : Uy = -R' / (y : ℂ) ^ 2) (hRt : Rt = p * R) (hRt' : Rt' = p * (I * θ * R + R'))
    (hθ : θ * (1 / y) ^ 2 = K) :
    ‖Uy + ((1 : ℝ) : ℂ) * (f : ℂ) * I * R‖ =
        (1 / y) ^ 2 * ‖-Rt' + I * ((y ^ 2 * (K + f) : ℝ) : ℂ) * Rt‖ ∧
      (Uy * (starRingEnd ℂ) R).re = -((((1 / y) ^ 2 : ℝ) : ℂ) * Rt' * (starRingEnd ℂ) Rt).re := by
  have hpp : p * (starRingEnd ℂ) p = 1 := by
    rw [Complex.mul_conj', hp, ofReal_one, one_pow]
  have hRR : R * (starRingEnd ℂ) R = ((‖R‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj']
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy
  subst hUy hRt hRt' hθ
  constructor
  · have key : (((1 / y) ^ 2 : ℝ) : ℂ) * (-(p * (I * θ * R + R')) +
          I * ((y ^ 2 * (θ * (1 / y) ^ 2 + f) : ℝ) : ℂ) * (p * R)) =
        p * (-R' / (y : ℂ) ^ 2 + ((1 : ℝ) : ℂ) * (f : ℂ) * I * R) := by
      push_cast
      field_simp
      ring
    have h := congrArg norm key
    rw [norm_mul, norm_mul, hp, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)] at h
    exact h.symm
  · have key : (((1 / y) ^ 2 : ℝ) : ℂ) * (p * (I * θ * R + R')) * (starRingEnd ℂ) (p * R) =
        -(-R' / (y : ℂ) ^ 2 * (starRingEnd ℂ) R) + I * (((1 / y) ^ 2 * θ * ‖R‖ ^ 2 : ℝ) : ℂ) := by
      simp only [map_mul]
      push_cast
      field_simp
      linear_combination ((I * θ * R + R') * (starRingEnd ℂ) R) * hpp + (I * θ) * hRR
    rw [key, Complex.add_re, Complex.I_mul_re, Complex.ofReal_im, neg_zero, add_zero,
      Complex.neg_re, neg_neg]

/-! ### The extremal horizon limits -/

/-- **Reciprocal normalization, extremal horizon** (p. 6): for `|Q| = M`, `K(M) ≠ 0`, with
`x = r − M`, `U(x) = xR(M + x)` and `k̂(x) = sgn K(M + x) · x⁻² √(K(M + x)² − Lx²)`, the
phase-free current `J = −(k̂/k̂_x)|U_x + ik̂U|² − Re(U_xŪ)` (σ = 1) tends to `0` as `x ↓ 0`. -/
theorem extremal_reciprocal_horizon_current_tendsto_L {M Q e ω L : ℝ} (hQ : |Q| = M)
    (_hL : 0 ≤ L) (hK : radialK e ω M ≠ 0)
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
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
        -((SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
              Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) /
            deriv (fun t : ℝ => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
              Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x) *
          ‖deriv (fun t : ℝ => (t : ℂ) * R (M + t)) x +
              ((1 : ℝ) : ℂ) * (((SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
                Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) : ℝ) : ℂ) * I *
              ((x : ℂ) * R (M + x))‖ ^ 2 -
        (deriv (fun t : ℝ => (t : ℂ) * R (M + t)) x *
          (starRingEnd ℂ) ((x : ℂ) * R (M + x))).re)
      (𝓝[>] 0) (𝓝 0) := by
  rw [outerHorizon_of_abs_eq hQ] at hH1 hH2
  have hx := ex_tendsto_add_nhdsGT M
  have hT : Tendsto (fun x : ℝ => exp (I * (Θ (M + x) : ℂ)) * R (M + x)) (𝓝[>] 0) (𝓝 B) :=
    (ex_tendsto_of_isBigO_sub hH1).comp hx
  have hT' : (fun x : ℝ => deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) (M + x))
      =O[𝓝[>] 0] (fun _ => (1 : ℝ)) :=
    hH2.comp_tendsto hx
  have hid : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto' 0 0 ofReal_zero).mono_left nhdsWithin_le_nhds
  have hxT' := hid.zero_mul_isBoundedUnder_le ((isBigO_one_iff ℝ).1 hT')
  have hc := (ex_tendsto_recip_correction (L := L) hK).ofReal
  have hW := ((hT.add hxT').add (((tendsto_const_nhds (x := I)).mul hc).mul hT)).norm
  have hRe := (Complex.continuous_re.tendsto _).comp
    ((hT.add hxT').mul ((Complex.continuous_conj.tendsto _).comp (hid.mul hT)))
  have h := ((ex_tendsto_recip_ratio (L := L) hK).neg.mul (hW.pow 2)).sub hRe
  refine (h.congr' ?_).mono_right (by simp)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  have hra : M + x ∈ Ioi (outerHorizon M Q) := by
    rw [mem_Ioi, outerHorizon_of_abs_eq hQ]
    linarith
  have hP := (ex_hasDerivAt_profile (hΘ _ hra) (hR _ hra).1).deriv
  rw [delta_of_abs_eq hQ, add_sub_cancel_left] at hP
  obtain ⟨h1, h2⟩ := ex_recip_alg (k := (SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
      Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2)) (ex_norm_exp_I_mul (Θ (M + x)))
    (hasDerivAt_extremal_reciprocal_reduced_L hQ hR hx0).deriv rfl hP
  rw [h1, h2]
  rfl

/-- **Constant normalization, extremal horizon** (p. 5): for `|Q| = M`, `K(M) ≠ 0` and
`K'(M) = 2ωM − e ≠ 0`, with `y = 1/(r − M)`, `U(y) = R(M + 1/y)` and
`f̂(y) = −sgn K(M + 1/y) · √(K(M + 1/y)² − L/y²)`, the phase-free current
`J = −(f̂/f̂_y)|U_y + if̂U|² − Re(U_yŪ)` (σ = 1) tends to `0` as `y → ∞`. -/
theorem extremal_constant_horizon_current_tendsto_L {M Q e ω L : ℝ} (hQ : |Q| = M)
    (_hL : 0 ≤ L) (hK : radialK e ω M ≠ 0) (hK' : 2 * ω * M - e ≠ 0)
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
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
        -(-((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) *
              Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2)) /
            deriv (fun t : ℝ => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
              Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y) *
          ‖deriv (fun t : ℝ => R (M + 1 / t)) y +
              ((1 : ℝ) : ℂ) * ((-((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) *
                Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2)) : ℝ) : ℂ) * I *
              R (M + 1 / y)‖ ^ 2 -
        (deriv (fun t : ℝ => R (M + 1 / t)) y * (starRingEnd ℂ) (R (M + 1 / y))).re)
      atTop (𝓝 0) := by
  rw [outerHorizon_of_abs_eq hQ] at hH1 hH2
  have hr := ex_tendsto_add_one_div_atTop M
  have hT : Tendsto (fun y : ℝ => exp (I * (Θ (M + 1 / y) : ℂ)) * R (M + 1 / y)) atTop (𝓝 B) :=
    (ex_tendsto_of_isBigO_sub hH1).comp hr
  have hT' : (fun y : ℝ => deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) (M + 1 / y))
      =O[atTop] (fun _ => (1 : ℝ)) :=
    hH2.comp_tendsto hr
  have hε : Tendsto (fun y : ℝ => (1 / y) ^ 2) atTop (𝓝 0) := by
    simpa using ex_tendsto_one_div_atTop.pow 2
  have hc := (ex_tendsto_const_correction (L := L) hK).ofReal
  have hV : (fun y : ℝ => -deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) (M + 1 / y) +
      I * ((y ^ 2 * (radialK e ω (M + 1 / y) + -((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2))) : ℝ) : ℂ) *
          (exp (I * (Θ (M + 1 / y) : ℂ)) * R (M + 1 / y))) =O[atTop] (fun _ => (1 : ℝ)) :=
    hT'.neg_left.add ((((tendsto_const_nhds (x := I)).mul hc).mul hT).isBigO_one ℝ)
  have hV2 := hV.norm_left.pow 2
  simp only [one_pow] at hV2
  have hfirst := (ex_tendsto_const_ratio (L := L) hK hK').neg.mul
    (hε.zero_mul_isBoundedUnder_le ((isBigO_one_iff ℝ).1 hV2))
  have hsecond := (Complex.continuous_re.tendsto _).comp
    ((hε.ofReal.zero_mul_isBoundedUnder_le ((isBigO_one_iff ℝ).1 hT')).mul
      ((Complex.continuous_conj.tendsto _).comp hT))
  have h := hfirst.sub hsecond.neg
  refine (h.congr' ?_).mono_right (by simp)
  filter_upwards [eventually_gt_atTop 0] with y hy
  have hra : M + 1 / y ∈ Ioi (outerHorizon M Q) := by
    rw [mem_Ioi, outerHorizon_of_abs_eq hQ]
    have := one_div_pos.2 hy
    linarith
  have hP := (ex_hasDerivAt_profile (hΘ _ hra) (hR _ hra).1).deriv
  have hθ : radialK e ω (M + 1 / y) / delta M Q (M + 1 / y) * (1 / y) ^ 2 =
      radialK e ω (M + 1 / y) := by
    rw [delta_of_abs_eq hQ, add_sub_cancel_left]
    field_simp
  obtain ⟨h1, h2⟩ := ex_const_alg (f := -((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) *
      Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2))) hy.ne'
    (ex_norm_exp_I_mul (Θ (M + 1 / y))) (hasDerivAt_extremal_constant_reduced_L hQ hR hy).deriv
    rfl hP hθ
  rw [h1, h2]
  simp only [Function.comp_apply]
  ring

end ModeStability.AllAngular

end
