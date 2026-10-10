module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
import ModeStability.Flux.Basic

/-!
# The conserved flux (1.6) with the angular term

Source: the all-angular research notes in preparation, p. 2, (1.6) and the paragraph after
(1.7). The radial equation is
`(ΔR')' + (K²/Δ − L)R = 0` on `(a, ∞)`, the phase `Θ` has `Θ' = K/Δ`, the horizon condition (1.4)
in Θ-form is `e^{iΘ}R − B = O(r − a)`, `(e^{iΘ}R)' = O(1)`, and the infinity condition (1.5) is
`r e^{−iΘ}R − B = O(r⁻¹)`, `(r e^{−iΘ}R)' = O(r⁻²)`. Write `F = Δ Im(R' R̄)`.

* `flux_const_L`: `F` is constant on `(a, ∞)` (the angular term `L` is real and drops out).
* `tendsto_flux_horizon_L`: `F → −K(a)‖B‖²` as `r ↓ a`. With `R̃ = e^{iΘ}R` and `ΔΘ' = K`,
  `F = Δ Im(R̃' conj R̃) − K‖R̃‖²`; this works for subextremal and extremal horizons alike.
* `tendsto_flux_infinity_L`: `F → ω‖B‖²` as `r → ∞`. With `R̃ = r e^{−iΘ}R`,
  `F = (Δ/r²) Im(R̃' conj R̃) + (K/r²)‖R̃‖²`.
* `flux_identity_L`: (1.6), `−K(a)‖B_H‖² = ω‖B_I‖²`, and `F` equals this value.
* `tendsto_flux_sync_of_bounded`, `tendsto_flux_extremal_sync_of_bounded`: at an extremal
  synchronized horizon (`a = b`, `K(a) = 0`) a mode that is bounded near `a` has `F → 0`. This is
  the claim bounded solutions have vanishing horizon flux after (1.7), proved here without
  Frobenius theory: `K²/Δ = (ω(r + a) − e)²` is bounded,
  so `P = ΔR'` has bounded derivative `‖P'‖ ≤ D`; in the coordinate `u = 1/(r − a)` the function
  `R(a + 1/u) + uP(s)` has derivative `P(s) − P(a + 1/u)` of size at most `D(s − a)`, and
  boundedness of `R` then forces `‖P(s)‖ ≤ D(s − a)` (`fl_norm_le_of_bounded`). Hence
  `F = Im(P R̄) → 0`.
* `flux_identity_sync_L`, `flux_identity_extremal_sync_L`: in that case `ω‖B_I‖² = 0`, `F ≡ 0`.

No hypothesis on `M, Q` is needed: the proofs only use `Δ = (r − a)(r − b)` with `b ≤ a`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-! ### Elementary facts -/

/-- `b ≤ a`. -/
theorem fl_innerHorizon_le (M Q : ℝ) : innerHorizon M Q ≤ outerHorizon M Q := by
  unfold innerHorizon outerHorizon
  have := Real.sqrt_nonneg (M ^ 2 - Q ^ 2)
  linarith

/-- `Δ(r) > 0` for `r > a`. -/
theorem fl_delta_pos {M Q r : ℝ} (hr : outerHorizon M Q < r) : 0 < delta M Q r := by
  have hab := fl_innerHorizon_le M Q
  unfold delta
  have h1 : 0 < r - outerHorizon M Q := sub_pos.2 hr
  have h2 : 0 < r - innerHorizon M Q := by linarith
  positivity

/-- `Δ` is continuous. -/
theorem fl_continuous_delta (M Q : ℝ) : Continuous (delta M Q) := by
  unfold delta
  fun_prop

/-- For `|Q| = M`: `a = M`. -/
theorem fl_outerHorizon_of_abs_eq {M Q : ℝ} (hQ : |Q| = M) : outerHorizon M Q = M := by
  have h : M ^ 2 - Q ^ 2 = 0 := by rw [← sq_abs Q, hQ, sub_self]
  unfold outerHorizon
  rw [h, Real.sqrt_zero, add_zero]

/-- For `|Q| = M`: `b = M`. -/
theorem fl_innerHorizon_of_abs_eq {M Q : ℝ} (hQ : |Q| = M) : innerHorizon M Q = M := by
  have h : M ^ 2 - Q ^ 2 = 0 := by rw [← sq_abs Q, hQ, sub_self]
  unfold innerHorizon
  rw [h, Real.sqrt_zero, sub_zero]

/-! ### Conservation of the flux -/

/-- The flux `Δ Im(R' R̄)` of a solution of `(ΔR')' + (K²/Δ − L)R = 0` has derivative `0`. -/
theorem fl_hasDerivAt_flux {M Q e ω L : ℝ} {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {r : ℝ} (hr : r ∈ Ioi (outerHorizon M Q)) :
    HasDerivAt (fun s => delta M Q s * (deriv R s * (starRingEnd ℂ) (R s)).im) 0 r := by
  obtain ⟨hd, hP⟩ := hR r hr
  have hc : HasDerivAt (fun s => (starRingEnd ℂ) (R s)) ((starRingEnd ℂ) (deriv R r)) r :=
    hd.hasDerivAt.star
  have hG := hP.fun_mul hc
  have hIm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r hG
  have hfun : (fun s => delta M Q s * (deriv R s * (starRingEnd ℂ) (R s)).im) =
      Complex.imCLM ∘ fun s => (delta M Q s : ℂ) * deriv R s * (starRingEnd ℂ) (R s) := by
    funext s
    simp [mul_assoc]
  rw [hfun]
  refine hIm.congr_deriv ?_
  rw [Complex.imCLM_apply]
  exact ModeStability.Flux.im_flux_derivative _ _ _ _

/-- Conservation: `F = Δ Im(R' R̄)` is constant on the exterior `(a, ∞)`, for every real `L`. -/
theorem flux_const_L {M Q e ω L : ℝ} {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    ∃ C : ℝ, ∀ r ∈ Ioi (outerHorizon M Q),
      delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im = C := by
  refine isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun r hr => (fl_hasDerivAt_flux hR hr).differentiableAt.differentiableWithinAt) ?_
  intro r hr
  exact (fl_hasDerivAt_flux hR hr).deriv

/-! ### The flux at the horizon -/

/-- Flux formula at the horizon: for `R̃ = e^{iΘ}R` with `Θ' = K/Δ`,
`Δ Im(R' R̄) = Δ Im(R̃' conj R̃) − K‖R̃‖²`. -/
theorem fl_horizon_form {M Q e ω : ℝ} {Θ : ℝ → ℝ} {R : ℝ → ℂ} {r : ℝ}
    (hr : outerHorizon M Q < r) (hΘ : HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : DifferentiableAt ℝ R r) :
    delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im =
      delta M Q r * (deriv (fun s : ℝ => exp (I * (Θ s : ℂ)) * R s) r *
          (starRingEnd ℂ) (exp (I * (Θ r : ℂ)) * R r)).im -
        radialK e ω r * ‖exp (I * (Θ r : ℂ)) * R r‖ ^ 2 := by
  have hc : HasDerivAt (fun s : ℝ => exp (I * (Θ s : ℂ)))
      (exp (I * (Θ r : ℂ)) * (I * ((radialK e ω r / delta M Q r : ℝ) : ℂ))) r :=
    (hΘ.ofReal_comp.const_mul I).cexp
  have h := ModeStability.Flux.im_flux_twist hc hR
  have hn : ‖exp (I * (Θ r : ℂ))‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have him : (I * ((radialK e ω r / delta M Q r : ℝ) : ℂ)).im = radialK e ω r / delta M Q r := by
    simp
  rw [hn, him] at h
  have hΔ : delta M Q r ≠ 0 := (fl_delta_pos hr).ne'
  rw [h]
  field_simp
  ring

/-- Limit of the flux at the horizon (1.6): `Δ Im(R' R̄) → −K(a)‖B‖²` as `r ↓ a`, for the
Θ-form horizon condition (1.4) with leading coefficient `B`. -/
theorem tendsto_flux_horizon_L {M Q e ω L : ℝ}
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hH1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - B)
      =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q))
    (hH2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r)
      =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))) :
    Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im)
      (𝓝[>] (outerHorizon M Q)) (𝓝 (-radialK e ω (outerHorizon M Q) * ‖B‖ ^ 2)) := by
  set a := outerHorizon M Q with ha
  set Rt : ℝ → ℂ := fun r : ℝ => exp (I * (Θ r : ℂ)) * R r with hRt
  have hsub : Tendsto (fun r : ℝ => r - a) (𝓝[>] a) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => r - a) := by fun_prop
    have := (hc.tendsto a).mono_left (nhdsWithin_le_nhds (s := Ioi a))
    simpa using this
  have hRt' : Tendsto Rt (𝓝[>] a) (𝓝 B) :=
    tendsto_sub_nhds_zero_iff.1 (hH1.trans_tendsto hsub)
  have hΔ : Tendsto (delta M Q) (𝓝[>] a) (𝓝 0) := by
    have := ((fl_continuous_delta M Q).tendsto a).mono_left (nhdsWithin_le_nhds (s := Ioi a))
    simpa [delta, ha] using this
  have hX : (fun r => (deriv Rt r * (starRingEnd ℂ) (Rt r)).im) =O[𝓝[>] a]
      (fun _ => (1 : ℝ)) := by
    have h1 : (fun r => (starRingEnd ℂ) (Rt r)) =O[𝓝[>] a] (fun _ => (1 : ℝ)) :=
      (((Complex.continuous_conj).tendsto B).comp hRt').isBigO_one ℝ
    have h2 := (hH2 : deriv Rt =O[𝓝[>] a] (fun _ => (1 : ℝ))).mul h1
    simp only [mul_one] at h2
    refine IsBigO.trans (g := fun r => ‖deriv Rt r * (starRingEnd ℂ) (Rt r)‖) ?_ h2.norm_left
    exact IsBigO.of_bound 1 (Eventually.of_forall fun r => by
      simpa using Complex.abs_im_le_norm (deriv Rt r * (starRingEnd ℂ) (Rt r)))
  have hprod : Tendsto (fun r => delta M Q r * (deriv Rt r * (starRingEnd ℂ) (Rt r)).im)
      (𝓝[>] a) (𝓝 0) := by
    have h := (isBigO_refl (delta M Q) (𝓝[>] a)).mul hX
    simp only [mul_one] at h
    exact h.trans_tendsto hΔ
  have hK : Tendsto (fun r => radialK e ω r) (𝓝[>] a) (𝓝 (radialK e ω a)) := by
    have hc : Continuous (fun r => radialK e ω r) := by
      unfold radialK
      fun_prop
    exact (hc.tendsto a).mono_left nhdsWithin_le_nhds
  have hnorm : Tendsto (fun r => ‖Rt r‖ ^ 2) (𝓝[>] a) (𝓝 (‖B‖ ^ 2)) := hRt'.norm.pow 2
  have hlim := hprod.sub (hK.mul hnorm)
  rw [zero_sub, ← neg_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (fl_horizon_form hr (hΘ r hr) (hR r hr).1).symm

/-! ### The flux at infinity -/

/-- Flux formula at infinity: for `R̃ = r e^{−iΘ}R` with `Θ' = K/Δ`,
`Δ Im(R' R̄) = (Δ/r²) Im(R̃' conj R̃) + (K/r²)‖R̃‖²`. -/
theorem fl_infinity_form {M Q e ω : ℝ} {Θ : ℝ → ℝ} {R : ℝ → ℂ} {r : ℝ} (hr0 : 0 < r)
    (hr : outerHorizon M Q < r) (hΘ : HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : DifferentiableAt ℝ R r) :
    delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im =
      delta M Q r / r ^ 2 *
          (deriv (fun s : ℝ => (s : ℂ) * exp (-(I * (Θ s : ℂ))) * R s) r *
            (starRingEnd ℂ) ((r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)).im +
        radialK e ω r / r ^ 2 * ‖(r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r‖ ^ 2 := by
  set κ : ℝ := radialK e ω r / delta M Q r with hκ
  have hr0' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 r := (hasDerivAt_id r).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => exp (-(I * (Θ s : ℂ))))
      (exp (-(I * (Θ r : ℂ))) * -(I * (κ : ℂ))) r :=
    (hΘ.ofReal_comp.const_mul I).neg.cexp
  have hc : HasDerivAt (fun s : ℝ => (s : ℂ) * exp (-(I * (Θ s : ℂ))))
      ((r : ℂ) * exp (-(I * (Θ r : ℂ))) * (((1 / r : ℝ) : ℂ) - I * (κ : ℂ))) r := by
    refine (h1.fun_mul h2).congr_deriv ?_
    push_cast
    field_simp
    ring
  have h := ModeStability.Flux.im_flux_twist hc hR
  have hn : ‖(r : ℂ) * exp (-(I * (Θ r : ℂ)))‖ = r := by
    rw [norm_mul, Complex.norm_exp]
    simp [abs_of_pos hr0]
  have him : (((1 / r : ℝ) : ℂ) - I * (κ : ℂ)).im = -κ := by
    simp
  rw [hn, him] at h
  have hΔ : delta M Q r ≠ 0 := (fl_delta_pos hr).ne'
  rw [h, hκ]
  field_simp
  ring

/-- Limit of the flux at infinity (1.6): `Δ Im(R' R̄) → ω‖B‖²` as `r → ∞`, for the Θ-form
infinity condition (1.5) with leading coefficient `B`. -/
theorem tendsto_flux_infinity_L {M Q e ω L : ℝ}
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - B)
      =O[atTop] (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im) atTop
      (𝓝 (ω * ‖B‖ ^ 2)) := by
  set a := outerHorizon M Q with ha
  set b := innerHorizon M Q with hb
  set Rt : ℝ → ℂ := fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r with hRt
  have hRt' : Tendsto Rt atTop (𝓝 B) :=
    tendsto_sub_nhds_zero_iff.1 (hI1.trans_tendsto tendsto_inv_atTop_zero)
  have ht : Tendsto (deriv Rt) atTop (𝓝 0) :=
    hI2.trans_tendsto (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero))
  have hIm : Tendsto (fun r => (deriv Rt r * (starRingEnd ℂ) (Rt r)).im) atTop (𝓝 0) := by
    have h1 := ht.mul ((Complex.continuous_conj.tendsto B).comp hRt')
    have h2 := (Complex.continuous_im.tendsto _).comp h1
    rw [zero_mul, Complex.zero_im] at h2
    exact h2
  have hΔ : Tendsto (fun r => delta M Q r / r ^ 2) atTop (𝓝 1) := by
    have h1 : Tendsto (fun r : ℝ => (1 - a / r) * (1 - b / r)) atTop
        (𝓝 ((1 - 0) * (1 - 0))) :=
      (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)).mul
        (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id))
    rw [sub_zero, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    unfold delta
    rw [← ha, ← hb]
    field_simp
  have hK : Tendsto (fun r => radialK e ω r / r ^ 2) atTop (𝓝 ω) := by
    have h1 : Tendsto (fun r : ℝ => ω - e / r) atTop (𝓝 (ω - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    unfold radialK
    field_simp
  have hlim := (hΔ.mul hIm).add (hK.mul (hRt'.norm.pow 2))
  rw [mul_zero, zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 a)] with r hr
  have hr0 : 0 < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hra : a < r := lt_of_le_of_lt (le_max_right _ _) hr
  exact (fl_infinity_form hr0 hra (hΘ r hra) (hR r hra).1).symm

/-! ### The flux identity -/

/-- The flux identity (1.6): for a solution with the Θ-form horizon condition (leading
coefficient `BH`) and infinity condition (leading coefficient `BI`),
`−K(a)‖B_H‖² = ω‖B_I‖²`, and `Δ Im(R' R̄)` equals this value on the whole exterior. -/
theorem flux_identity_L {M Q e ω L : ℝ}
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {BH BI : ℂ}
    (hH1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - BH)
      =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q))
    (hH2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r)
      =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - BI)
      =O[atTop] (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    -radialK e ω (outerHorizon M Q) * ‖BH‖ ^ 2 = ω * ‖BI‖ ^ 2 ∧
      ∀ r ∈ Ioi (outerHorizon M Q),
        delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im = ω * ‖BI‖ ^ 2 := by
  obtain ⟨C, hC⟩ := flux_const_L hR
  have hH := tendsto_flux_horizon_L hΘ hR hH1 hH2
  have hI := tendsto_flux_infinity_L hΘ hR hI1 hI2
  have hCH : Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im)
      (𝓝[>] (outerHorizon M Q)) (𝓝 C) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hC r hr).symm
  have hCI : Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im)
      atTop (𝓝 C) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
    exact (hC r hr).symm
  have e1 := tendsto_nhds_unique hH hCH
  have e2 := tendsto_nhds_unique hI hCI
  exact ⟨e1.trans e2.symm, fun r hr => (hC r hr).trans e2.symm⟩

/-! ### The extremal synchronized horizon -/

/-- Core estimate at an extremal synchronized horizon: if `R' = P/(t − c)²`, `‖R‖ ≤ C` and
`‖P'‖ ≤ D` on `(c, ρ)`, then `‖P(s)‖ ≤ D(s − c)` on `(c, ρ)`. -/
theorem fl_norm_le_of_bounded {c ρ C D : ℝ} {R P P' : ℝ → ℂ}
    (hRd : ∀ t ∈ Ioo c ρ, HasDerivAt R (P t / ((t - c : ℝ) : ℂ) ^ 2) t)
    (hPd : ∀ t ∈ Ioo c ρ, HasDerivAt P (P' t) t)
    (hRb : ∀ t ∈ Ioo c ρ, ‖R t‖ ≤ C) (hPb : ∀ t ∈ Ioo c ρ, ‖P' t‖ ≤ D) :
    ∀ s ∈ Ioo c ρ, ‖P s‖ ≤ D * (s - c) := by
  intro s hs
  have hsc : 0 < s - c := sub_pos.2 hs.1
  have hD : 0 ≤ D := (norm_nonneg _).trans (hPb s hs)
  have hC : 0 ≤ C := (norm_nonneg _).trans (hRb s hs)
  -- `P` is `D`-Lipschitz on `(c, ρ)`
  have hLip : ∀ t ∈ Ioo c ρ, ‖P s - P t‖ ≤ D * |s - t| := by
    intro t ht
    have := (convex_Ioo c ρ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hPd x hx).hasDerivWithinAt) hPb ht hs
    simpa [Real.norm_eq_abs] using this
  -- the coordinate `u = 1/(t − c)`, starting at `u₀ = 1/(s − c)`
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ℝ, u₀ = (s - c)⁻¹ := ⟨_, rfl⟩
  have hu₀pos : 0 < u₀ := hu₀ ▸ inv_pos.2 hsc
  have hs' : c + u₀⁻¹ = s := by
    rw [hu₀, inv_inv]
    ring
  have hmem : ∀ u ∈ Ici u₀, c + u⁻¹ ∈ Ioo c ρ ∧ c + u⁻¹ ≤ s := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hu₀pos hu
    have h1 : u⁻¹ ≤ s - c := by
      have h := inv_anti₀ hu₀pos (show u₀ ≤ u from hu)
      rwa [hu₀, inv_inv] at h
    have h2 : 0 < u⁻¹ := inv_pos.2 hu0
    exact ⟨⟨by linarith, by linarith [hs.2]⟩, by linarith⟩
  -- `η(u) = R(c + 1/u) + u P(s)` has derivative `P(s) − P(c + 1/u)`
  obtain ⟨η, hη⟩ : ∃ η : ℝ → ℂ, η = fun u => R (c + u⁻¹) + (u : ℂ) * P s := ⟨_, rfl⟩
  have hηd : ∀ u ∈ Ici u₀, HasDerivWithinAt η (P s - P (c + u⁻¹)) (Ici u₀) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hu₀pos hu
    obtain ⟨ht, -⟩ := hmem u hu
    have hin : HasDerivAt (fun v : ℝ => c + v⁻¹) (-(u ^ 2)⁻¹) u :=
      (hasDerivAt_inv hu0.ne').const_add c
    have h1 := (hRd _ ht).scomp u hin
    have h2 : HasDerivAt (fun v : ℝ => (v : ℂ) * P s) (1 * P s) u :=
      ((hasDerivAt_id u).ofReal_comp).mul_const (P s)
    rw [hη]
    refine ((h1.add h2).congr_deriv ?_).hasDerivWithinAt
    have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu0.ne'
    simp only [add_sub_cancel_left, Complex.real_smul]
    push_cast
    field_simp
    ring
  have hbound : ∀ u ∈ Ici u₀, ‖P s - P (c + u⁻¹)‖ ≤ D * (s - c) := by
    intro u hu
    obtain ⟨ht, hts⟩ := hmem u hu
    refine (hLip _ ht).trans (mul_le_mul_of_nonneg_left ?_ hD)
    rw [abs_of_nonneg (by linarith)]
    linarith [ht.1]
  -- the mean value inequality on `[u₀, v]`
  have key : ∀ v, u₀ ≤ v → (v - u₀) * ‖P s‖ ≤ D * (s - c) * (v - u₀) + 2 * C := by
    intro v hv
    have hMV := (convex_Ici u₀).norm_image_sub_le_of_norm_hasDerivWithin_le hηd hbound
      self_mem_Ici (show v ∈ Ici u₀ from hv)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hv)] at hMV
    have hid : ((v : ℂ) - (u₀ : ℂ)) * P s = (η v - η u₀) - R (c + v⁻¹) + R s := by
      rw [hη]
      simp only [hs']
      ring
    have hn : ‖((v : ℂ) - (u₀ : ℂ)) * P s‖ = (v - u₀) * ‖P s‖ := by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2 hv)]
    have hRv := hRb _ (hmem v hv).1
    have hRs := hRb s hs
    have h3 := norm_add_le (η v - η u₀ - R (c + v⁻¹)) (R s)
    have h4 := norm_sub_le (η v - η u₀) (R (c + v⁻¹))
    rw [← hid, hn] at h3
    linarith
  -- conclusion
  by_contra hcon
  have hδ : 0 < ‖P s‖ - D * (s - c) := sub_pos.2 (not_le.1 hcon)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (2 * C + 1) / (‖P s‖ - D * (s - c)) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := hT ▸ div_nonneg (by linarith) hδ.le
  have hTδ : T * (‖P s‖ - D * (s - c)) = 2 * C + 1 := by
    rw [hT]
    exact div_mul_cancel₀ _ hδ.ne'
  have hk := key (u₀ + T) (by linarith)
  rw [add_sub_cancel_left] at hk
  linarith

/-- At an extremal synchronized horizon (`b = a`, `K(a) = 0`), the flux of a mode that is
bounded near `a` tends to `0` (paragraph after (1.7), p. 2). -/
theorem tendsto_flux_sync_of_bounded {M Q e ω L : ℝ}
    (hab : innerHorizon M Q = outerHorizon M Q) (hK : radialK e ω (outerHorizon M Q) = 0)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hbdd : (fun r => R r) =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))) :
    Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im)
      (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
  have hΔ : ∀ r, delta M Q r = (r - outerHorizon M Q) ^ 2 := by
    intro r
    unfold delta
    rw [hab]
    ring
  set a := outerHorizon M Q with ha
  -- `K²/Δ − L = (ω(r + a) − e)² − L`
  have hV : ∀ r, a < r →
      radialK e ω r ^ 2 / delta M Q r - L = (ω * (r + a) - e) ^ 2 - L := by
    intro r hr
    have hra : r - a ≠ 0 := (sub_pos.2 hr).ne'
    have hKr : radialK e ω r = (r - a) * (ω * (r + a) - e) := by
      have h : radialK e ω r = radialK e ω r - radialK e ω a := by rw [hK, sub_zero]
      rw [h]
      unfold radialK
      ring
    rw [hKr, hΔ r, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 hra)]
  -- bounds on `(a, ρ)`
  obtain ⟨C, hC⟩ := hbdd.bound
  obtain ⟨ρ, hρ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hC
  have hRb : ∀ t ∈ Ioo a ρ, ‖R t‖ ≤ C := by
    intro t ht
    have h := hsub ht
    simpa using h
  obtain ⟨D₀, hD₀⟩ := (isCompact_Icc (a := a) (b := ρ)).exists_bound_of_continuousOn
    (f := fun t : ℝ => (ω * (t + a) - e) ^ 2 - L)
    (by fun_prop : Continuous fun t : ℝ => (ω * (t + a) - e) ^ 2 - L).continuousOn
  set P : ℝ → ℂ := fun t => (delta M Q t : ℂ) * deriv R t with hP
  have hRd : ∀ t ∈ Ioo a ρ, HasDerivAt R (P t / ((t - a : ℝ) : ℂ) ^ 2) t := by
    intro t ht
    refine ((hR t ht.1).1.hasDerivAt).congr_deriv ?_
    have hta : (t : ℂ) - (a : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.2 (sub_pos.2 ht.1).ne'
    rw [hP]
    simp only [hΔ t]
    push_cast
    field_simp
  have hPd : ∀ t ∈ Ioo a ρ, HasDerivAt P
      (-(((radialK e ω t) ^ 2 / delta M Q t - L : ℝ) : ℂ) * R t) t :=
    fun t ht => (hR t ht.1).2
  have hPb : ∀ t ∈ Ioo a ρ,
      ‖-(((radialK e ω t) ^ 2 / delta M Q t - L : ℝ) : ℂ) * R t‖ ≤ D₀ * C := by
    intro t ht
    have h1 : |radialK e ω t ^ 2 / delta M Q t - L| ≤ D₀ := by
      rw [hV t ht.1, ← Real.norm_eq_abs]
      exact hD₀ t (Ioo_subset_Icc_self ht)
    have hD0 : 0 ≤ D₀ := (abs_nonneg _).trans h1
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul h1 (hRb t ht) (norm_nonneg _) hD0
  have hPs := fl_norm_le_of_bounded hRd hPd hRb hPb
  -- `F = Im(P R̄)`, `|F| ≤ ‖P‖‖R‖ ≤ D₀ C² (r − a)`
  have hsub0 : Tendsto (fun r : ℝ => r - a) (𝓝[>] a) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => r - a) := by fun_prop
    have := (hc.tendsto a).mono_left (nhdsWithin_le_nhds (s := Ioi a))
    simpa using this
  have hlin : Tendsto (fun r : ℝ => D₀ * C * (r - a) * C) (𝓝[>] a) (𝓝 0) := by
    have := (hsub0.const_mul (D₀ * C)).mul_const C
    simpa using this
  refine squeeze_zero_norm' ?_ hlin
  filter_upwards [mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨ρ, hρ, subset_rfl⟩] with t ht
  have hF : delta M Q t * (deriv R t * (starRingEnd ℂ) (R t)).im =
      (P t * (starRingEnd ℂ) (R t)).im := by
    rw [hP, mul_assoc, Complex.im_ofReal_mul]
  rw [hF, Real.norm_eq_abs]
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hPs t ht) (hRb t ht) (norm_nonneg _)
    (mul_nonneg ((norm_nonneg _).trans (hPb t ht)) (sub_pos.2 ht.1).le)

/-- At an extremal synchronized horizon (`|Q| = M`, `K(M) = 0`), the flux of a mode that is
bounded near `M` tends to `0` (paragraph after (1.7), p. 2). -/
theorem tendsto_flux_extremal_sync_of_bounded {M Q e ω L : ℝ} (hQ : |Q| = M)
    (hK : radialK e ω M = 0) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hbdd : (fun r => R r) =O[𝓝[>] M] (fun _ => (1 : ℝ))) :
    Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im)
      (𝓝[>] M) (𝓝 0) := by
  have ha := fl_outerHorizon_of_abs_eq hQ
  have hb := fl_innerHorizon_of_abs_eq hQ
  have h := tendsto_flux_sync_of_bounded (hb.trans ha.symm) (by rw [ha]; exact hK) hR
    (by rw [ha]; exact hbdd)
  rwa [ha] at h

/-- Flux identity at an extremal synchronized horizon (`b = a`, `K(a) = 0`): for a mode bounded
near `a` with the Θ-form infinity condition (leading coefficient `BI`), `ω‖B_I‖² = 0`, and
`Δ Im(R' R̄) ≡ 0` on the exterior. -/
theorem flux_identity_sync_L {M Q e ω L : ℝ}
    (hab : innerHorizon M Q = outerHorizon M Q) (hK : radialK e ω (outerHorizon M Q) = 0)
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hbdd : (fun r => R r) =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))
    {BI : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - BI)
      =O[atTop] (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    ω * ‖BI‖ ^ 2 = 0 ∧
      ∀ r ∈ Ioi (outerHorizon M Q), delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im = 0 := by
  obtain ⟨C, hC⟩ := flux_const_L hR
  have hH := tendsto_flux_sync_of_bounded hab hK hR hbdd
  have hI := tendsto_flux_infinity_L hΘ hR hI1 hI2
  have hCH : Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im)
      (𝓝[>] (outerHorizon M Q)) (𝓝 C) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hC r hr).symm
  have hCI : Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im)
      atTop (𝓝 C) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
    exact (hC r hr).symm
  have e1 := tendsto_nhds_unique hH hCH
  have e2 := tendsto_nhds_unique hI hCI
  exact ⟨e2.trans e1.symm, fun r hr => (hC r hr).trans e1.symm⟩

/-- Flux identity at an extremal synchronized horizon, `|Q| = M` and `K(M) = 0`: for a mode
bounded near `M` with the Θ-form infinity condition, `ω‖B_I‖² = 0` and `Δ Im(R' R̄) ≡ 0`. -/
theorem flux_identity_extremal_sync_L {M Q e ω L : ℝ} (hQ : |Q| = M) (hK : radialK e ω M = 0)
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hbdd : (fun r => R r) =O[𝓝[>] M] (fun _ => (1 : ℝ)))
    {BI : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - BI)
      =O[atTop] (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    ω * ‖BI‖ ^ 2 = 0 ∧
      ∀ r ∈ Ioi M, delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im = 0 := by
  have ha := fl_outerHorizon_of_abs_eq hQ
  have hb := fl_innerHorizon_of_abs_eq hQ
  have h := flux_identity_sync_L (hb.trans ha.symm) (by rw [ha]; exact hK) hΘ hR
    (by rw [ha]; exact hbdd) hI1 hI2
  rwa [ha] at h

end ModeStability.AllAngular

end
