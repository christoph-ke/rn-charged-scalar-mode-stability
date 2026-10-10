module

public import Mathlib
public import ModeStability.AllAngular.AngularReduction
public import ModeStability.AllAngular.CoefficientIdentities

/-!
# Auxiliary facts for the extremal horizon limits of the current with angular term

Helpers for `ModeStability.AllAngular.ExtremalHorizonLimits`, after
the all-angular research notes in preparation, Section 4, pp. 5–6: at an extremal horizon
(`|Q| = M`, `a = b = M`, `Δ = (r − M)²`) with `K(M) ≠ 0`.

* Signs and square roots: `sgn ∘ F` is locally constant where `F` is continuous and nonzero
  (`ex_eventually_sign_eq`, `ex_hasDerivAt_sign_comp`), and
  `sgn K · √(K² − V) − K = −sgn K · V/(|K| + √(K² − V))` (`ex_sign_mul_sqrt_sub`).
* The profile `R̃ = e^{iΘ}R` has `R̃' = e^{iΘ}(iΘ'R + R')` (`ex_hasDerivAt_profile`); the
  Θ-form horizon condition gives `R̃ → B` (`ex_tendsto_of_isBigO_sub`).
* Reciprocal normalization, `x = r − M ↓ 0`, `k̂(x) = sgn K · x⁻² · √(K² − Lx²)` at `r = M + x`:
  `k̂/k̂_x → 0` (`ex_tendsto_recip_ratio`; `k̂/k̂_x = xP/(−2P + xP_x)`, `P = √(K² − Lx²)`), and
  `x(k̂ − K/x²) → 0` (`ex_tendsto_recip_correction`; the angular correction `k̂ − k` is `O(1)`).
* Constant normalization, `y = 1/(r − M) → ∞`, `f̂(y) = −sgn K · √(K² − L/y²)` at
  `r = M + 1/y`: `(f̂/f̂_y) · y⁻² → −K(M)²/(K(M)K'(M))` when `K'(M) = 2ωM − e ≠ 0`
  (`ex_tendsto_const_ratio`; `(f̂/f̂_y) y⁻² = −(K² − L/y²)/(KK' − L/y)`), and `y²(K + f̂)`
  converges
  (`ex_tendsto_const_correction`; `K + f̂ = O(Δ)`).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-! ### Signs and square roots -/

/-- Near a point where `F` is continuous and nonzero, `sgn ∘ F` is constant. -/
theorem ex_eventually_sign_eq {F : ℝ → ℝ} {x : ℝ} (hF : ContinuousAt F x) (hx : F x ≠ 0) :
    ∀ᶠ t in 𝓝 x, SignType.sign (F t) = SignType.sign (F x) := by
  rcases hx.lt_or_gt with h | h
  · filter_upwards [hF.eventually (gt_mem_nhds h)] with t ht
    rw [sign_neg h, sign_neg ht]
  · filter_upwards [hF.eventually (lt_mem_nhds h)] with t ht
    rw [sign_pos h, sign_pos ht]

/-- `sgn ∘ F` has derivative `0` at a point where `F` is continuous and nonzero. -/
theorem ex_hasDerivAt_sign_comp {F : ℝ → ℝ} {x : ℝ} (hF : ContinuousAt F x) (hx : F x ≠ 0) :
    HasDerivAt (fun t => (SignType.sign (F t) : ℝ)) 0 x := by
  refine (hasDerivAt_const x (SignType.sign (F x) : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [ex_eventually_sign_eq hF hx] with t ht
  rw [ht]

/-- `sgn K ≠ 0` for `K ≠ 0`. -/
theorem ex_sign_coe_ne_zero {K : ℝ} (hK : K ≠ 0) : (SignType.sign K : ℝ) ≠ 0 := by
  rcases hK.lt_or_gt with h | h
  · rw [sign_neg h, SignType.coe_neg_one]
    norm_num
  · rw [sign_pos h, SignType.coe_one]
    norm_num

/-- `sgn K · √(K² − V) − K = −sgn K · V/(|K| + √(K² − V))` for `K ≠ 0` and `V ≤ K²`. -/
theorem ex_sign_mul_sqrt_sub {K V : ℝ} (hK : K ≠ 0) (hV : V ≤ K ^ 2) :
    (SignType.sign K : ℝ) * Real.sqrt (K ^ 2 - V) - K =
      -((SignType.sign K : ℝ) * V / (|K| + Real.sqrt (K ^ 2 - V))) := by
  have hP := Real.sq_sqrt (sub_nonneg.2 hV)
  have hP0 := Real.sqrt_nonneg (K ^ 2 - V)
  rcases hK.lt_or_gt with h | h
  · rw [sign_neg h, SignType.coe_neg_one, abs_of_neg h]
    have hd : -K + Real.sqrt (K ^ 2 - V) ≠ 0 := by linarith
    field_simp
    linear_combination -hP
  · rw [sign_pos h, SignType.coe_one, abs_of_pos h]
    have hd : K + Real.sqrt (K ^ 2 - V) ≠ 0 := by linarith
    field_simp
    linear_combination hP

/-! ### The profile `R̃ = e^{iΘ}R` -/

/-- `‖e^{iθ}‖ = 1`. -/
theorem ex_norm_exp_I_mul (θ : ℝ) : ‖exp (I * (θ : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I θ

/-- `R̃ = e^{iΘ}R` has derivative `e^{iΘ}(iΘ'R + R')`. -/
theorem ex_hasDerivAt_profile {Θ : ℝ → ℝ} {R : ℝ → ℂ} {r θ : ℝ} (hΘ : HasDerivAt Θ θ r)
    (hR : DifferentiableAt ℝ R r) :
    HasDerivAt (fun s : ℝ => exp (I * (Θ s : ℂ)) * R s)
      (exp (I * (Θ r : ℂ)) * (I * θ * R r + deriv R r)) r := by
  have h1 : HasDerivAt (fun s : ℝ => I * (Θ s : ℂ)) (I * θ) r := hΘ.ofReal_comp.const_mul I
  convert h1.cexp.mul hR.hasDerivAt using 1
  ring

/-- `F − B = O(r − a)` as `r ↓ a` gives `F → B`. -/
theorem ex_tendsto_of_isBigO_sub {F : ℝ → ℂ} {B : ℂ} {a : ℝ}
    (h : (fun r => F r - B) =O[𝓝[>] a] (fun r => r - a)) : Tendsto F (𝓝[>] a) (𝓝 B) := by
  have h0 : Tendsto (fun r : ℝ => r - a) (𝓝[>] a) (𝓝 0) :=
    ((continuous_sub_right a).tendsto' a 0 (sub_self a)).mono_left nhdsWithin_le_nhds
  simpa using (h.trans_tendsto h0).add_const B

/-- `x ↦ M + x` maps `x ↓ 0` to `r ↓ M`. -/
theorem ex_tendsto_add_nhdsGT (M : ℝ) : Tendsto (fun x : ℝ => M + x) (𝓝[>] 0) (𝓝[>] M) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous (fun x : ℝ => M + x) := by fun_prop
    exact (hc.tendsto' 0 M (add_zero M)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact lt_add_of_pos_right M hx

/-- `y ↦ M + 1/y` maps `y → ∞` to `r ↓ M`. -/
theorem ex_tendsto_add_one_div_atTop (M : ℝ) :
    Tendsto (fun y : ℝ => M + 1 / y) atTop (𝓝[>] M) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_inv_atTop_zero
    simpa using h.const_add M
  · filter_upwards [eventually_gt_atTop 0] with y hy
    exact lt_add_of_pos_right M (one_div_pos.2 hy)

/-! ### Continuity of the coefficients in `z = r − M` -/

/-- `z ↦ K(M + z)` is continuous. -/
theorem ex_continuous_K (e ω M : ℝ) : Continuous (fun z : ℝ => radialK e ω (M + z)) := by
  unfold radialK
  fun_prop

/-- `z ↦ K(M + z)² − Lz²` is continuous. -/
theorem ex_continuous_radicand (e ω L M : ℝ) :
    Continuous (fun z : ℝ => radialK e ω (M + z) ^ 2 - L * z ^ 2) := by
  unfold radialK
  fun_prop

/-- `z ↦ √(K(M + z)² − Lz²)` is continuous. -/
theorem ex_continuous_P (e ω L M : ℝ) :
    Continuous (fun z : ℝ => Real.sqrt (radialK e ω (M + z) ^ 2 - L * z ^ 2)) :=
  (ex_continuous_radicand e ω L M).sqrt

/-- `√(K(M + 0)² − L · 0²) = |K(M)|`. -/
theorem ex_P_zero (e ω L M : ℝ) :
    Real.sqrt (radialK e ω (M + 0) ^ 2 - L * 0 ^ 2) = |radialK e ω M| := by
  rw [add_zero]
  simp [Real.sqrt_sq_eq_abs]

/-- Near `z = 0`: `K(M + z) ≠ 0`, `K(M + z)² − Lz² > 0` and `sgn K(M + z) = sgn K(M)`. -/
theorem ex_eventually_good {e ω L M : ℝ} (hK : radialK e ω M ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : ℝ), radialK e ω (M + z) ≠ 0 ∧ 0 < radialK e ω (M + z) ^ 2 - L * z ^ 2 ∧
      SignType.sign (radialK e ω (M + z)) = SignType.sign (radialK e ω M) := by
  have hK0 : radialK e ω (M + 0) ≠ 0 := by rwa [add_zero]
  have hρ0 : 0 < radialK e ω (M + 0) ^ 2 - L * 0 ^ 2 := by
    rw [add_zero]
    simpa using pow_pos (abs_pos.2 hK) 2
  have h3 := ex_eventually_sign_eq (ex_continuous_K e ω M).continuousAt hK0
  filter_upwards [(ex_continuous_K e ω M).continuousAt.eventually_ne hK0,
    ((ex_continuous_radicand e ω L M).tendsto 0).eventually (lt_mem_nhds hρ0), h3] with z h1 h2 h3
  refine ⟨h1, h2, ?_⟩
  rw [h3, add_zero]

/-! ### Reciprocal normalization: `x = r − M ↓ 0` -/

/-- The derivative of `k̂(t) = sgn K(M + t) · (1/t)² · √(K(M + t)² − Lt²)` at `x ≠ 0` with
`K(M + x) ≠ 0` and positive radicand. -/
theorem ex_hasDerivAt_recip_khat {e ω L M x : ℝ} (hx : x ≠ 0) (hK : radialK e ω (M + x) ≠ 0)
    (hρ : 0 < radialK e ω (M + x) ^ 2 - L * x ^ 2) :
    HasDerivAt (fun t : ℝ => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2))
      ((SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 3 *
        (-2 * Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) +
          x * ((2 * radialK e ω (M + x) * (2 * ω * (M + x) - e) - L * (2 * x)) /
            (2 * Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2))))) x := by
  have hF : HasDerivAt (fun t => radialK e ω (M + t)) (2 * ω * (M + x) - e) x :=
    (CoefficientIdentities.hasDerivAt_radialK e ω (M + x)).comp_const_add M x
  have hs := ex_hasDerivAt_sign_comp hF.continuousAt hK
  have hinv : HasDerivAt (fun t : ℝ => (1 / t) ^ 2) (-2 / x ^ 3) x := by
    have h := (hasDerivAt_inv hx).fun_pow 2
    simp only [one_div]
    convert h using 1
    norm_num
    field_simp
  have hρd : HasDerivAt (fun t => radialK e ω (M + t) ^ 2 - L * t ^ 2)
      (2 * radialK e ω (M + x) * (2 * ω * (M + x) - e) - L * (2 * x)) x := by
    convert (hF.fun_pow 2).sub ((hasDerivAt_pow 2 x).const_mul L) using 1
    push_cast
    ring
  have h := (hs.mul hinv).mul (hρd.sqrt hρ.ne')
  convert h using 1
  simp only [Pi.mul_apply]
  have hP : 0 < Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) := Real.sqrt_pos.2 hρ
  field_simp
  ring

/-- Reciprocal normalization at the extremal horizon: `k̂/k̂_x → 0` as `x ↓ 0`. -/
theorem ex_tendsto_recip_ratio {e ω L M : ℝ} (hK : radialK e ω M ≠ 0) :
    Tendsto (fun x : ℝ =>
        (SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
            Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) /
          deriv (fun t : ℝ => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
            Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x)
      (𝓝[>] 0) (𝓝 0) := by
  have hA : 0 < |radialK e ω M| := abs_pos.2 hK
  have hP := (ex_continuous_P e ω L M).tendsto' 0 _ (ex_P_zero e ω L M)
  have hDc : Continuous (fun t : ℝ =>
      2 * radialK e ω (M + t) * (2 * ω * (M + t) - e) - L * (2 * t)) := by
    unfold radialK
    fun_prop
  have hD := hDc.tendsto 0
  have hQ := hD.div (hP.const_mul 2) (by positivity)
  have hden := (hP.const_mul (-2)).add ((tendsto_id (x := 𝓝 (0 : ℝ))).mul hQ)
  have hlim := ((tendsto_id (x := 𝓝 (0 : ℝ))).mul hP).div hden (by simp [hK])
  simp only [id, zero_mul, zero_div] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ex_eventually_good (L := L) hK)]
    with x hx hg
  have hx0 : 0 < x := hx
  rw [(ex_hasDerivAt_recip_khat hx0.ne' hg.1 hg.2.1).deriv]
  have hs := ex_sign_coe_ne_zero hg.1
  have hc : (SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 3 ≠ 0 :=
    mul_ne_zero hs (by positivity)
  rw [show (SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
      Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) =
      (SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 3 *
        (x * Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2)) by field_simp,
    mul_div_mul_left _ _ hc]
  rfl

/-- Reciprocal normalization at the extremal horizon: the angular correction `k̂ − k`,
`k = K/x²`, is `O(1)`, so `x(k̂ − k) → 0` as `x ↓ 0`. -/
theorem ex_tendsto_recip_correction {e ω L M : ℝ} (hK : radialK e ω M ≠ 0) :
    Tendsto (fun x : ℝ => x * ((SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
        Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) - radialK e ω (M + x) / x ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  have hA : 0 < |radialK e ω M| := abs_pos.2 hK
  have hP := (ex_continuous_P e ω L M).tendsto' 0 _ (ex_P_zero e ω L M)
  have hF := (ex_continuous_K e ω M).abs.tendsto' 0 |radialK e ω M| (by simp only [add_zero])
  have hlim := ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul
    ((SignType.sign (radialK e ω M) : ℝ) * L)).div (hF.add hP) (by positivity)
  simp only [id, mul_zero, zero_div] at hlim
  have hlim' := hlim.neg
  rw [neg_zero] at hlim'
  refine (hlim'.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ex_eventually_good (L := L) hK)]
    with x hx hg
  have hx0 : 0 < x := hx
  have key := ex_sign_mul_sqrt_sub hg.1 (V := L * x ^ 2) (by linarith [hg.2.1])
  rw [hg.2.2] at key
  have hd : 0 < |radialK e ω (M + x)| + Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) :=
    add_pos_of_pos_of_nonneg (abs_pos.2 hg.1) (Real.sqrt_nonneg _)
  rw [hg.2.2]
  have h2 : x * ((SignType.sign (radialK e ω M) : ℝ) * (1 / x) ^ 2 *
        Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) - radialK e ω (M + x) / x ^ 2) =
      (1 / x) * ((SignType.sign (radialK e ω M) : ℝ) *
        Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) - radialK e ω (M + x)) := by
    field_simp
  rw [h2, key]
  simp only [Pi.div_apply]
  field_simp

/-! ### Constant normalization: `y = 1/(r − M) → ∞` -/

/-- `z = 1/y ↓ 0` as `y → ∞`. -/
theorem ex_tendsto_one_div_atTop : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
  simpa only [one_div] using tendsto_inv_atTop_zero

/-- `L/y² = L(1/y)²`. -/
theorem ex_div_sq (L y : ℝ) : L / y ^ 2 = L * (1 / y) ^ 2 := by
  rw [one_div_pow, mul_one_div]

/-- The derivative of `f̂(t) = −sgn K(M + 1/t) · √(K(M + 1/t)² − L/t²)` at `y ≠ 0` with
`K(M + 1/y) ≠ 0` and positive radicand: `f̂_y = sgn K · y⁻² (KK' − L/y)/√(K² − L/y²)`. -/
theorem ex_hasDerivAt_const_fhat {e ω L M y : ℝ} (hy : y ≠ 0) (hK : radialK e ω (M + 1 / y) ≠ 0)
    (hρ : 0 < radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2) :
    HasDerivAt (fun t : ℝ => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2)))
      ((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) * (1 / y) ^ 2 *
        ((radialK e ω (M + 1 / y) * (2 * ω * (M + 1 / y) - e) - L * (1 / y)) /
          Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2))) y := by
  have hr : HasDerivAt (fun t : ℝ => M + 1 / t) (-(y ^ 2)⁻¹) y := by
    simpa only [one_div] using (hasDerivAt_inv hy).const_add M
  have h1 : HasDerivAt (fun t => radialK e ω t) (2 * ω * (M + 1 / y) - e)
      ((fun t : ℝ => M + 1 / t) y) :=
    CoefficientIdentities.hasDerivAt_radialK e ω (M + 1 / y)
  have hF : HasDerivAt (fun t => radialK e ω (M + 1 / t))
      ((2 * ω * (M + 1 / y) - e) * -(y ^ 2)⁻¹) y :=
    (h1.comp y hr :)
  have hs := ex_hasDerivAt_sign_comp hF.continuousAt hK
  have hρd := (hF.fun_pow 2).sub
    ((hasDerivAt_const y L).div (hasDerivAt_pow 2 y) (pow_ne_zero 2 hy))
  have h := (hs.mul (hρd.sqrt hρ.ne')).neg
  convert h using 1
  simp only [Pi.sub_apply, Pi.div_apply]
  have hP : 0 < Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2) := Real.sqrt_pos.2 hρ
  generalize Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2) = P at hP ⊢
  generalize (SignType.sign (radialK e ω (M + 1 / y)) : ℝ) = s
  generalize radialK e ω (M + 1 / y) = K
  generalize 2 * ω * (M + 1 / y) - e = K1
  field_simp
  ring

/-- The algebra of `ex_tendsto_const_ratio`: with `P² = K² − Lz²`,
`−(sP)/(s z² (KK₁ − Lz)/P) · z² = −(K² − Lz²)/(KK₁ − Lz)`. -/
theorem ex_const_ratio_alg {s P K K1 L z : ℝ} (hs : s ≠ 0) (hP : P ≠ 0) (hz : z ≠ 0)
    (hP2 : P ^ 2 = K ^ 2 - L * z ^ 2) :
    -(s * P) / (s * z ^ 2 * ((K * K1 - L * z) / P)) * z ^ 2 =
      -(K ^ 2 - L * z ^ 2) / (K * K1 - L * z) := by
  rw [← hP2]
  field_simp

/-- Constant normalization at the extremal horizon, `K'(M) = 2ωM − e ≠ 0`:
`(f̂/f̂_y) · y⁻² → −K(M)²/(K(M)K'(M))` as `y → ∞`; so `f̂/f̂_y = O(Δ⁻¹)`, `Δ = y⁻²`. -/
theorem ex_tendsto_const_ratio {e ω L M : ℝ} (hK : radialK e ω M ≠ 0)
    (hK' : 2 * ω * M - e ≠ 0) :
    Tendsto (fun y : ℝ =>
        -((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) *
            Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2)) /
          deriv (fun t : ℝ => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
            Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y * (1 / y) ^ 2)
      atTop (𝓝 (-(radialK e ω M ^ 2) / (radialK e ω M * (2 * ω * M - e)))) := by
  have hN := (ex_continuous_radicand e ω L M).tendsto' 0 (radialK e ω M ^ 2) (by simp)
  have hDc : Continuous (fun z : ℝ => radialK e ω (M + z) * (2 * ω * (M + z) - e) - L * z) := by
    unfold radialK
    fun_prop
  have hD := hDc.tendsto' 0 (radialK e ω M * (2 * ω * M - e)) (by simp)
  have hlim := (hN.neg.div hD (mul_ne_zero hK hK')).comp ex_tendsto_one_div_atTop
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0,
    ex_tendsto_one_div_atTop.eventually (ex_eventually_good (L := L) hK)] with y hy hg
  have hρ : 0 < radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2 := by
    rw [ex_div_sq]
    exact hg.2.1
  rw [(ex_hasDerivAt_const_fhat hy.ne' hg.1 hρ).deriv]
  have hs := ex_sign_coe_ne_zero hg.1
  have hP : 0 < Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2) := Real.sqrt_pos.2 hρ
  have hP2 := Real.sq_sqrt hρ.le
  simp only [Function.comp_apply, Pi.div_apply]
  rw [ex_div_sq] at hP2 hP ⊢
  exact (ex_const_ratio_alg hs hP.ne' (one_div_ne_zero hy.ne') hP2).symm

/-- Constant normalization at the extremal horizon: `K + f̂ = O(Δ)`, `Δ = y⁻²`; precisely
`y²(K + f̂) → sgn K(M) · L/(2|K(M)|)` as `y → ∞`. -/
theorem ex_tendsto_const_correction {e ω L M : ℝ} (hK : radialK e ω M ≠ 0) :
    Tendsto (fun y : ℝ => y ^ 2 * (radialK e ω (M + 1 / y) +
        -((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) *
          Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2))))
      atTop (𝓝 ((SignType.sign (radialK e ω M) : ℝ) * L /
        (|radialK e ω M| + |radialK e ω M|))) := by
  have hA : 0 < |radialK e ω M| := abs_pos.2 hK
  have hP := (ex_continuous_P e ω L M).tendsto' 0 _ (ex_P_zero e ω L M)
  have hF := (ex_continuous_K e ω M).abs.tendsto' 0 |radialK e ω M| (by simp only [add_zero])
  have hlim := ((tendsto_const_nhds (x := (SignType.sign (radialK e ω M) : ℝ) * L)).div
    (hF.add hP) (by positivity)).comp ex_tendsto_one_div_atTop
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0,
    ex_tendsto_one_div_atTop.eventually (ex_eventually_good (L := L) hK)] with y hy hg
  have key := ex_sign_mul_sqrt_sub hg.1 (V := L * (1 / y) ^ 2) (by linarith [hg.2.1])
  have hd : 0 < |radialK e ω (M + 1 / y)| +
      Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L * (1 / y) ^ 2) :=
    add_pos_of_pos_of_nonneg (abs_pos.2 hg.1) (Real.sqrt_nonneg _)
  rw [hg.2.2] at key ⊢
  simp only [Function.comp, Pi.div_apply]
  rw [ex_div_sq]
  rw [show radialK e ω (M + 1 / y) + -((SignType.sign (radialK e ω M) : ℝ) *
      Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L * (1 / y) ^ 2)) =
      -((SignType.sign (radialK e ω M) : ℝ) *
      Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L * (1 / y) ^ 2) - radialK e ω (M + 1 / y)) by ring,
    key]
  field_simp

end ModeStability.AllAngular

end
