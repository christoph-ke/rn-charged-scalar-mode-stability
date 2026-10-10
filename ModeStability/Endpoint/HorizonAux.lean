module

public import ModeStability.Endpoint.Common
public import ModeStability.Exterior.Reduction
public import ModeStability.Frozen.HorizonCondition

/-!
# Auxiliary facts for the horizon endpoint current

Helpers for the horizon limit (2.11)–(2.13) of the spherical research notes in preparation.
With `a`, `b`, `d = a − b`, `K(r) = ωr² − qQr` and `κ = K(a)/d`:

* the de-oscillated profile `R̃(r) = (r − a)^{iκ} R(r)` of the horizon condition (1.3)
  (`horizonProfile`), with `|(r − a)^{iκ}| = 1` and
  `R̃' = (r − a)^{iκ} (R' + iκ R/(r − a))` for `r > a`;
* the factorization `K(r) − κ(r − b) = (r − a)(ω(r + a) − qQ − κ)`;
* `r(x) → a⁺` and `(r(x) − a)/x → 0` as `x → 0⁺`, from (2.11);
* the pointwise algebra turning the phase-free current into an expression in `R̃`, `R̃'`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Endpoint

variable {M Q q ω : ℝ}

/-- The horizon frequency `κ = K(a)/d` of (1.3). -/
@[expose] noncomputable def horizonFreq (M Q q ω : ℝ) : ℝ :=
  radialK (q * Q) ω (outerHorizon M Q) / (outerHorizon M Q - innerHorizon M Q)

/-- The horizon phase factor `(r − a)^{iκ}`. -/
@[expose] noncomputable def horizonPhase (M Q q ω r : ℝ) : ℂ :=
  ((r - outerHorizon M Q : ℝ) : ℂ) ^ (I * (horizonFreq M Q q ω : ℂ))

/-- The de-oscillated horizon profile `R̃(r) = (r − a)^{iκ} R(r)` of (1.3). -/
@[expose] noncomputable def horizonProfile (M Q q ω : ℝ) (R : ℝ → ℂ) (r : ℝ) : ℂ :=
  horizonPhase M Q q ω r * R r

/-- `|(r − a)^{iκ}| = 1` for `r > a`. -/
theorem norm_horizonPhase {r : ℝ} (hr : outerHorizon M Q < r) :
    ‖horizonPhase M Q q ω r‖ = 1 := by
  unfold horizonPhase
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.2 hr)]
  simp

/-- `((r − a)^{iκ})' = iκ (r − a)^{iκ} / (r − a)` for `r > a`, `κ ≠ 0`. -/
theorem hasDerivAt_horizonPhase (hκ : horizonFreq M Q q ω ≠ 0) {r : ℝ}
    (hr : outerHorizon M Q < r) :
    HasDerivAt (horizonPhase M Q q ω)
      (I * horizonFreq M Q q ω * horizonPhase M Q q ω r / ((r - outerHorizon M Q : ℝ) : ℂ)) r := by
  have hra : r - outerHorizon M Q ≠ 0 := (sub_pos.2 hr).ne'
  have hc : I * (horizonFreq M Q q ω : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.2 hκ)
  have h := (hasDerivAt_ofReal_cpow_const hra hc).comp_sub_const r (outerHorizon M Q)
  refine h.congr_deriv ?_
  rw [Complex.cpow_sub _ _ (ofReal_ne_zero.2 hra), cpow_one]
  unfold horizonPhase
  ring

/-- `R̃' = (r − a)^{iκ} (R' + iκ R/(r − a))` for `r > a`. -/
theorem hasDerivAt_horizonProfile (hκ : horizonFreq M Q q ω ≠ 0) {R : ℝ → ℂ}
    (hR : IsRadialSolution M Q q ω R) {r : ℝ} (hr : outerHorizon M Q < r) :
    HasDerivAt (horizonProfile M Q q ω R)
      (horizonPhase M Q q ω r *
        (deriv R r + I * horizonFreq M Q q ω * R r / ((r - outerHorizon M Q : ℝ) : ℂ))) r := by
  have h := (hasDerivAt_horizonPhase hκ hr).mul (hR r hr).1.hasDerivAt
  refine h.congr_deriv ?_
  ring

/-- `K(r) − κ(r − b) = (r − a)(ω(r + a) − qQ − κ)`. -/
theorem radialK_sub_horizonFreq_mul (hQ : |Q| < M) (r : ℝ) :
    radialK (q * Q) ω r - horizonFreq M Q q ω * (r - innerHorizon M Q) =
      (r - outerHorizon M Q) *
        (ω * (r + outerHorizon M Q) - q * Q - horizonFreq M Q q ω) := by
  have hd := (outerHorizon_sub_innerHorizon_pos hQ).ne'
  unfold horizonFreq radialK
  field_simp
  ring

/-! ### Pointwise algebra -/

/-- `(K/x²)/(K'Δ/x⁴ − 2K/x³) = x · K/(K'(Δ/x) − 2K)`. -/
theorem ratio_eq {x K K' Δ : ℝ} (hx : x ≠ 0) :
    (K / x ^ 2) / (K' * Δ / x ^ 4 - 2 * K / x ^ 3) = x * (K / (K' * (Δ / x) - 2 * K)) := by
  have h : K' * Δ / x ^ 4 - 2 * K / x ^ 3 = (K' * (Δ / x) - 2 * K) / x ^ 3 := by
    field_simp
  rw [h, div_div_eq_mul_div, mul_div_assoc']
  field_simp

/-- After removing the phase, `U' + ikU` becomes `R̃ + (Δ/x) R̃' + i((r − a)/x) L R̃`. -/
theorem norm_combination {x a b r K Δ κ L : ℝ} {p R R' Rt Rt' : ℂ} (hx : x ≠ 0)
    (hra : r - a ≠ 0) (hΔ : Δ = (r - a) * (r - b)) (hp : ‖p‖ = 1) (hRt : Rt = p * R)
    (hRt' : Rt' = p * (R' + I * κ * R / ((r - a : ℝ) : ℂ)))
    (hKL : K - κ * (r - b) = (r - a) * L) :
    ‖R + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * R') +
        ((1 : ℝ) : ℂ) * ((K / x ^ 2 : ℝ) : ℂ) * I * ((x : ℂ) * R)‖ =
      ‖Rt + ((Δ / x : ℝ) : ℂ) * Rt' + I * (((r - a) / x * L : ℝ) : ℂ) * Rt‖ := by
  have key : Rt + ((Δ / x : ℝ) : ℂ) * Rt' + I * (((r - a) / x * L : ℝ) : ℂ) * Rt =
      p * (R + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * R') +
        ((1 : ℝ) : ℂ) * ((K / x ^ 2 : ℝ) : ℂ) * I * ((x : ℂ) * R)) := by
    subst hRt hRt' hΔ
    have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
    have hra' : ((r : ℂ) - a) ≠ 0 := by exact_mod_cast hra
    have hKL' : (K : ℂ) - κ * (r - b) = (r - a) * L := by exact_mod_cast hKL
    push_cast
    field_simp
    linear_combination (-(p * R * I)) * hKL'
  rw [key, norm_mul, hp, one_mul]

/-- The phase drops out of `Re(U' Ū)`: it equals `x |R̃|² + Re(Δ R̃' conj R̃)`. -/
theorem re_combination {x a r Δ κ : ℝ} {p R R' Rt Rt' : ℂ} (hx : x ≠ 0) (hp : ‖p‖ = 1)
    (hRt : Rt = p * R) (hRt' : Rt' = p * (R' + I * κ * R / ((r - a : ℝ) : ℂ))) :
    ((R + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * R')) * (starRingEnd ℂ) ((x : ℂ) * R)).re =
      x * ‖Rt‖ ^ 2 + ((Δ : ℂ) * Rt' * (starRingEnd ℂ) Rt).re := by
  have hpp : p * (starRingEnd ℂ) p = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]
    norm_num
  have hRR : R * (starRingEnd ℂ) R = ((‖R‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow]
  have hnorm : ‖Rt‖ = ‖R‖ := by rw [hRt, norm_mul, hp, one_mul]
  have hx1 : (x : ℂ)⁻¹ * x = 1 := inv_mul_cancel₀ (ofReal_ne_zero.2 hx)
  have h1 : (R + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * R')) * (starRingEnd ℂ) ((x : ℂ) * R) =
      ((x * ‖R‖ ^ 2 : ℝ) : ℂ) + (Δ : ℂ) * (R' * (starRingEnd ℂ) R) := by
    rw [map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination (x : ℂ) * hRR + ((Δ : ℂ) * R' * (starRingEnd ℂ) R) * hx1
  have h2 : (Δ : ℂ) * Rt' * (starRingEnd ℂ) Rt = (Δ : ℂ) * (R' * (starRingEnd ℂ) R) +
      I * ((Δ * κ / (r - a) * ‖R‖ ^ 2 : ℝ) : ℂ) := by
    rw [hRt', hRt, map_mul]
    push_cast
    linear_combination ((Δ : ℂ) * (R' + I * κ * R / (r - a)) * (starRingEnd ℂ) R) * hpp +
      (I * Δ * κ / (r - a)) * hRR
  rw [h1, h2, hnorm, Complex.add_re, Complex.add_re, Complex.ofReal_re, Complex.I_mul_re,
    Complex.ofReal_im, neg_zero, add_zero]

/-- The phase-free current `−(k/k_x)|U' + ikU|² − Re(U'Ū)` written through `R̃` and `R̃'`. -/
theorem current_algebra {x a b r K K' Δ κ L : ℝ} {p R R' Rt Rt' : ℂ} (hx : 0 < x)
    (hra : 0 < r - a) (hΔ : Δ = (r - a) * (r - b)) (hp : ‖p‖ = 1) (hRt : Rt = p * R)
    (hRt' : Rt' = p * (R' + I * κ * R / ((r - a : ℝ) : ℂ)))
    (hKL : K - κ * (r - b) = (r - a) * L) :
    -((K / x ^ 2) / (K' * Δ / x ^ 4 - 2 * K / x ^ 3)) *
        ‖R + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * R') +
          ((1 : ℝ) : ℂ) * ((K / x ^ 2 : ℝ) : ℂ) * I * ((x : ℂ) * R)‖ ^ 2 -
      ((R + ((1 / x : ℝ) : ℂ) * ((Δ : ℂ) * R')) * (starRingEnd ℂ) ((x : ℂ) * R)).re =
    -(x * (K / (K' * (Δ / x) - 2 * K))) *
        ‖Rt + ((Δ / x : ℝ) : ℂ) * Rt' + I * (((r - a) / x * L : ℝ) : ℂ) * Rt‖ ^ 2 -
      x * ‖Rt‖ ^ 2 - ((Δ : ℂ) * Rt' * (starRingEnd ℂ) Rt).re := by
  rw [ratio_eq hx.ne', norm_combination hx.ne' hra.ne' hΔ hp hRt hRt' hKL,
    re_combination hx.ne' hp hRt hRt']
  ring

/-! ### Limits from the horizon form (2.11) of `r(x)` -/

/-- `t/(eᵗ − 1) → 0` as `t → ∞`. -/
theorem tendsto_div_exp_sub_one_atTop :
    Tendsto (fun t : ℝ => t / (Real.exp t - 1)) atTop (𝓝 0) := by
  have hnum : Tendsto (fun t : ℝ => t * Real.exp (-t)) atTop (𝓝 0) := by
    simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hden : Tendsto (fun t : ℝ => 1 - Real.exp (-t)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
  have h := hnum.div hden (by norm_num)
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hE : 1 < Real.exp t := Real.one_lt_exp_iff.2 ht
  have hE0 : Real.exp t - 1 ≠ 0 := (sub_pos.2 hE).ne'
  have hE1 : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  simp only [Pi.div_apply, Real.exp_neg]
  field_simp

/-- `d/x → ∞` as `x → 0⁺`. -/
theorem tendsto_const_div_nhdsGT_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (fun x : ℝ => d / x) (𝓝[>] 0) atTop := by
  simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hd

/-- `r(x) → a⁺` as `x → 0⁺`, from (2.11). -/
theorem tendsto_radiusOf_nhdsGT (hQ : |Q| < M) :
    Tendsto (radiusOf M Q) (𝓝[>] 0) (𝓝[>] (outerHorizon M Q)) := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have h1 := tendsto_const_div_nhdsGT_zero hd
  have h2 : Tendsto (fun x : ℝ => Real.exp ((outerHorizon M Q - innerHorizon M Q) / x) - 1)
      (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_right _ (-1) (Real.tendsto_exp_atTop.comp h1)
  have h3 := (tendsto_const_nhds (x := outerHorizon M Q - innerHorizon M Q)).div_atTop h2
  have h4 := h3.const_add (outerHorizon M Q)
  rw [add_zero] at h4
  refine tendsto_nhdsWithin_iff.2 ⟨h4, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx using outerHorizon_lt_radiusOf hQ hx

/-- `(r(x) − a)/x → 0` as `x → 0⁺`: by (2.11), `(r − a)/x = t/(eᵗ − 1)` with `t = d/x`. -/
theorem tendsto_radiusOf_sub_div (hQ : |Q| < M) :
    Tendsto (fun x => (radiusOf M Q x - outerHorizon M Q) / x) (𝓝[>] 0) (𝓝 0) := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  refine (tendsto_div_exp_sub_one_atTop.comp (tendsto_const_div_nhdsGT_zero hd)).congr ?_
  intro x
  simp only [Function.comp_apply]
  unfold radiusOf
  ring

/-! ### Assembly of the limit -/

/-- If `x, D, E, Δ → 0`, `K → K_a ≠ 0`, `K'` converges, `R̃ → B` and `R̃'` stays bounded, then
`−(xK/(K'D − 2K)) |R̃ + D R̃' + iE R̃|² − x|R̃|² − Re(Δ R̃' conj R̃) → 0`. -/
theorem tendsto_current_form {α : Type*} {l : Filter α} {x K K' D E Δ : α → ℝ}
    {Rt Rt' : α → ℂ} {Ka K'a : ℝ} {B : ℂ} (hKa : Ka ≠ 0) (hx : Tendsto x l (𝓝 0))
    (hK : Tendsto K l (𝓝 Ka)) (hK' : Tendsto K' l (𝓝 K'a)) (hD : Tendsto D l (𝓝 0))
    (hE : Tendsto E l (𝓝 0)) (hΔ : Tendsto Δ l (𝓝 0)) (hRt : Tendsto Rt l (𝓝 B))
    (hRt' : IsBoundedUnder (· ≤ ·) l (fun t => ‖Rt' t‖)) :
    Tendsto (fun t => -(x t * (K t / (K' t * D t - 2 * K t))) *
        ‖Rt t + ((D t : ℝ) : ℂ) * Rt' t + I * ((E t : ℝ) : ℂ) * Rt t‖ ^ 2 -
      x t * ‖Rt t‖ ^ 2 - (((Δ t : ℝ) : ℂ) * Rt' t * (starRingEnd ℂ) (Rt t)).re) l (𝓝 0) := by
  have hden : Tendsto (fun t => K' t * D t - 2 * K t) l (𝓝 (K'a * 0 - 2 * Ka)) :=
    (hK'.mul hD).sub (hK.const_mul 2)
  have hden0 : K'a * 0 - 2 * Ka ≠ 0 := by
    rw [mul_zero, zero_sub, neg_ne_zero]
    exact mul_ne_zero two_ne_zero hKa
  have h1 := hx.mul (hK.div hden hden0)
  have hDc : Tendsto (fun t => ((D t : ℝ) : ℂ)) l (𝓝 0) := by
    simpa using hD.ofReal
  have hEc : Tendsto (fun t => ((E t : ℝ) : ℂ)) l (𝓝 0) := by
    simpa using hE.ofReal
  have hΔc : Tendsto (fun t => ((Δ t : ℝ) : ℂ)) l (𝓝 0) := by
    simpa using hΔ.ofReal
  have hDR := hDc.zero_mul_isBoundedUnder_le hRt'
  have hΔR := hΔc.zero_mul_isBoundedUnder_le hRt'
  have hW := (hRt.add hDR).add ((tendsto_const_nhds (x := I)).mul hEc |>.mul hRt)
  have h2 := hx.mul (hRt.norm.pow 2)
  have h3 : Tendsto (fun t => (((Δ t : ℝ) : ℂ) * Rt' t * (starRingEnd ℂ) (Rt t)).re) l
      (𝓝 ((0 * (starRingEnd ℂ) B).re)) :=
    (Complex.continuous_re.tendsto _).comp
      (hΔR.mul ((Complex.continuous_conj.tendsto B).comp hRt))
  have h := ((h1.neg.mul (hW.norm.pow 2)).sub h2).sub h3
  simpa using h

end ModeStability.Endpoint

end
