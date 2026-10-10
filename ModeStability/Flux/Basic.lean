module

public import Mathlib
public import ModeStability.Exterior.Calculus
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition

/-!
# Flux helpers

Pointwise and derivative identities used to prove the conserved flux (1.5).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Flux

/-- Pointwise algebra for the twisted flux: with `R̃ = c R`, `R̃' = c μ R + c R'`. -/
theorem im_mul_conj_twist (c μ z w : ℂ) :
    ((c * μ * z + c * w) * (starRingEnd ℂ) (c * z)).im =
      ‖c‖ ^ 2 * (μ.im * ‖z‖ ^ 2 + (w * (starRingEnd ℂ) z).im) := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, map_mul,
    Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Twisted flux: if `c' = c μ` then
`Im(R̃' conj R̃) = Im μ · ‖R̃‖² + ‖c‖² Im(R' conj R)` for `R̃ = c R`. -/
theorem im_flux_twist {c : ℝ → ℂ} {μ : ℂ} {R : ℝ → ℂ} {r : ℝ}
    (hc : HasDerivAt c (c r * μ) r) (hR : DifferentiableAt ℝ R r) :
    (deriv (fun s => c s * R s) r * (starRingEnd ℂ) (c r * R r)).im =
      μ.im * ‖c r * R r‖ ^ 2 + ‖c r‖ ^ 2 * (deriv R r * (starRingEnd ℂ) (R r)).im := by
  rw [(hc.fun_mul hR.hasDerivAt).deriv, im_mul_conj_twist, norm_mul]
  ring

/-- `d/dr (r : ℂ)^ν = ν r^ν / r` for `r > 0`. -/
theorem hasDerivAt_ofReal_cpow {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ ν) ((x : ℂ) ^ ν * (ν / x)) x := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  have h := ((hasDerivAt_id (x : ℂ)).cpow_const (c := ν) (by simp [hx])).comp_ofReal
  refine h.congr_deriv ?_
  simp only [id, mul_one]
  rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
  field_simp

/-- Derivative of the horizon phase `(r − a)^ν`. -/
theorem hasDerivAt_horizonPhase {a r : ℝ} (hr : a < r) (ν : ℂ) :
    HasDerivAt (fun s : ℝ => ((s - a : ℝ) : ℂ) ^ ν)
      (((r - a : ℝ) : ℂ) ^ ν * (ν / ((r - a : ℝ) : ℂ))) r := by
  have h := (hasDerivAt_ofReal_cpow (sub_pos.2 hr) ν).scomp r ((hasDerivAt_id r).sub_const a)
  refine h.congr_deriv ?_
  simp

/-- Flux formula at the horizon: for `R̃ = (r − a)^ν R` with `Re ν = 0`,
`Im(R' R̄) = Im(R̃' conj R̃) − (Im ν / (r − a)) ‖R̃‖²`. -/
theorem horizon_im_flux {a r : ℝ} {ν : ℂ} {R : ℝ → ℂ} (hr : a < r) (hν : ν.re = 0)
    (hR : DifferentiableAt ℝ R r) :
    (deriv R r * (starRingEnd ℂ) (R r)).im =
      (deriv (fun s : ℝ => ((s - a : ℝ) : ℂ) ^ ν * R s) r *
          (starRingEnd ℂ) (((r - a : ℝ) : ℂ) ^ ν * R r)).im -
        ν.im / (r - a) * ‖((r - a : ℝ) : ℂ) ^ ν * R r‖ ^ 2 := by
  have h := im_flux_twist (hasDerivAt_horizonPhase hr ν) hR
  have hn : ‖((r - a : ℝ) : ℂ) ^ ν‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.2 hr), hν, Real.rpow_zero]
  rw [hn] at h
  rw [h, Complex.div_ofReal_im]
  ring

/-- Derivative of the outgoing phase factor `c(r) = r e^{−iωr} r^ν`. -/
theorem hasDerivAt_infinityPhase {r : ℝ} (hr : 0 < r) (ω : ℝ) (ν : ℂ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * exp (-(I * ω * s)) * (s : ℂ) ^ ν)
      ((r : ℂ) * exp (-(I * ω * r)) * (r : ℂ) ^ ν *
        (1 / (r : ℂ) - I * ω + ν / (r : ℂ))) r := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 r := (hasDerivAt_id r).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => exp (-(I * ω * s)))
      (exp (-(I * ω * r)) * -(I * ω * 1)) r := by
    have := ((hasDerivAt_id r).ofReal_comp.const_mul (I * (ω : ℂ))).neg.cexp
    simpa using this
  have h3 := hasDerivAt_ofReal_cpow hr ν
  refine ((h1.fun_mul h2).fun_mul h3).congr_deriv ?_
  field_simp
  ring

/-- Flux formula at infinity: for `R̃ = r e^{−iωr} r^ν R` with `Re ν = 0`,
`r² Im(R' R̄) = Im(R̃' conj R̃) + (ω − Im ν / r) ‖R̃‖²`. -/
theorem infinity_im_flux {r ω : ℝ} {ν : ℂ} {R : ℝ → ℂ} (hr : 0 < r) (hν : ν.re = 0)
    (hR : DifferentiableAt ℝ R r) :
    r ^ 2 * (deriv R r * (starRingEnd ℂ) (R r)).im =
      (deriv (fun s : ℝ => (s : ℂ) * exp (-(I * ω * s)) * (s : ℂ) ^ ν * R s) r *
          (starRingEnd ℂ) ((r : ℂ) * exp (-(I * ω * r)) * (r : ℂ) ^ ν * R r)).im +
        (ω - ν.im / r) * ‖(r : ℂ) * exp (-(I * ω * r)) * (r : ℂ) ^ ν * R r‖ ^ 2 := by
  have h := im_flux_twist (hasDerivAt_infinityPhase hr ω ν) hR
  have hn : ‖(r : ℂ) * exp (-(I * ω * r)) * (r : ℂ) ^ ν‖ = r := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr, hν, Real.rpow_zero,
      Complex.norm_exp]
    simp [abs_of_pos hr]
  rw [hn] at h
  rw [h]
  simp [Complex.div_ofReal_im]
  ring

/-- The derivative of the flux integrand is real. -/
theorem im_flux_derivative (k D : ℝ) (z w : ℂ) :
    (-(k : ℂ) * z * (starRingEnd ℂ) z + (D : ℂ) * w * (starRingEnd ℂ) w).im = 0 := by
  have h : -(k : ℂ) * z * (starRingEnd ℂ) z + (D : ℂ) * w * (starRingEnd ℂ) w =
      ((-k * Complex.normSq z + D * Complex.normSq w : ℝ) : ℂ) := by
    push_cast
    rw [mul_assoc, Complex.mul_conj, mul_assoc, Complex.mul_conj]
  rw [h, Complex.ofReal_im]

/-- The flux `Δ Im(R' R̄)` of a radial solution has derivative `0` on the exterior. -/
theorem hasDerivAt_flux {M Q q ω : ℝ} {R : ℝ → ℂ} (hR : IsRadialSolution M Q q ω R) {r : ℝ}
    (hr : r ∈ Ioi (outerHorizon M Q)) :
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
  exact im_flux_derivative _ _ _ _

/-- Conservation: the flux `Δ Im(R' R̄)` of a radial solution is constant on the exterior. -/
theorem flux_const {M Q q ω : ℝ} {R : ℝ → ℂ} (hR : IsRadialSolution M Q q ω R) :
    ∃ C : ℝ, ∀ r ∈ Ioi (outerHorizon M Q),
      delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im = C := by
  refine isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun r hr => (hasDerivAt_flux hR hr).differentiableAt.differentiableWithinAt) ?_
  intro r hr
  exact (hasDerivAt_flux hR hr).deriv

section Horizon

variable {M Q q ω : ℝ} {R : ℝ → ℂ}

/-- Limit of the flux at the horizon: `Δ Im(R' R̄) → −K(a) ‖B_H‖²`. -/
theorem tendsto_flux_horizon (hQ : |Q| < M) (hR : IsRadialSolution M Q q ω R) {BH : ℂ}
    (hH : HorizonCondition M Q q ω R BH) :
    Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im) (𝓝[>] outerHorizon M Q)
      (𝓝 (-radialK (q * Q) ω (outerHorizon M Q) * ‖BH‖ ^ 2)) := by
  set a := outerHorizon M Q with ha
  set b := innerHorizon M Q with hb
  have hd : 0 < a - b := outerHorizon_sub_innerHorizon_pos hQ
  set κ : ℝ := radialK (q * Q) ω a / (a - b) with hκ
  set Rt : ℝ → ℂ := fun r : ℝ => ((r - a : ℝ) : ℂ) ^ (I * (κ : ℂ)) * R r with hRt
  have hν : (I * (κ : ℂ)).re = 0 := by simp
  have hνi : (I * (κ : ℂ)).im = κ := by simp
  -- the algebraic identity for the flux
  have hform : ∀ r ∈ Ioi a, delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im =
      delta M Q r * (deriv Rt r * (starRingEnd ℂ) (Rt r)).im - κ * (r - b) * ‖Rt r‖ ^ 2 := by
    intro r hr
    have hra : r - a ≠ 0 := (sub_pos.2 hr).ne'
    have h : (deriv R r * (starRingEnd ℂ) (R r)).im =
        (deriv Rt r * (starRingEnd ℂ) (Rt r)).im - (I * (κ : ℂ)).im / (r - a) * ‖Rt r‖ ^ 2 :=
      horizon_im_flux hr hν (hR r hr).1
    rw [h, hνi]
    unfold delta
    rw [← ha, ← hb]
    field_simp
  -- limits
  have hsub : Tendsto (fun r : ℝ => r - a) (𝓝[>] a) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => r - a) := by fun_prop
    have := (hc.tendsto a).mono_left (nhdsWithin_le_nhds (s := Ioi a))
    simpa using this
  have hRt : Tendsto Rt (𝓝[>] a) (𝓝 BH) := by
    have h1 : (fun r => Rt r - BH) =O[𝓝[>] a] (fun r : ℝ => r - a) := hH.1
    exact tendsto_sub_nhds_zero_iff.1 (h1.trans_tendsto hsub)
  have hΔ : Tendsto (delta M Q) (𝓝[>] a) (𝓝 0) := by
    have hc : Continuous (delta M Q) := by unfold delta; fun_prop
    have := (hc.tendsto a).mono_left (nhdsWithin_le_nhds (s := Ioi a))
    simpa [delta, ha] using this
  have hX : (fun r => (deriv Rt r * (starRingEnd ℂ) (Rt r)).im) =O[𝓝[>] a] (fun _ => (1 : ℝ)) := by
    have h1 : (fun r => (starRingEnd ℂ) (Rt r)) =O[𝓝[>] a] (fun _ => (1 : ℝ)) :=
      (((Complex.continuous_conj).tendsto BH).comp hRt).isBigO_one ℝ
    have h2 := (hH.2 : deriv Rt =O[𝓝[>] a] (fun _ => (1 : ℝ))).mul h1
    simp only [mul_one] at h2
    refine IsBigO.trans (g := fun r => ‖deriv Rt r * (starRingEnd ℂ) (Rt r)‖) ?_ h2.norm_left
    exact IsBigO.of_bound 1 (Eventually.of_forall fun r => by
      simpa using Complex.abs_im_le_norm (deriv Rt r * (starRingEnd ℂ) (Rt r)))
  have hprod : Tendsto (fun r => delta M Q r * (deriv Rt r * (starRingEnd ℂ) (Rt r)).im)
      (𝓝[>] a) (𝓝 0) := by
    have h := (isBigO_refl (delta M Q) (𝓝[>] a)).mul hX
    simp only [mul_one] at h
    exact h.trans_tendsto hΔ
  have hb' : Tendsto (fun r : ℝ => r - b) (𝓝[>] a) (𝓝 (a - b)) := by
    have hc : Continuous (fun r : ℝ => r - b) := by fun_prop
    exact (hc.tendsto a).mono_left (nhdsWithin_le_nhds (s := Ioi a))
  have hnorm : Tendsto (fun r => ‖Rt r‖ ^ 2) (𝓝[>] a) (𝓝 (‖BH‖ ^ 2)) := hRt.norm.pow 2
  have hlim := hprod.sub ((tendsto_const_nhds (x := κ)).mul hb' |>.mul hnorm)
  have hval : (0 - κ * (a - b) * ‖BH‖ ^ 2) = -radialK (q * Q) ω a * ‖BH‖ ^ 2 := by
    rw [hκ, div_mul_cancel₀ _ hd.ne']
    ring
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hform r hr).symm

end Horizon

section Infinity

variable {M Q q ω : ℝ} {R : ℝ → ℂ}

/-- Limit of the flux at infinity: `Δ Im(R' R̄) → ω ‖B_I‖²`. -/
theorem tendsto_flux_infinity (hM : 0 < M) (hR : IsRadialSolution M Q q ω R) {BI : ℂ}
    (hI : InfinityCondition M Q q ω R BI) :
    Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im) atTop
      (𝓝 (ω * ‖BI‖ ^ 2)) := by
  set a := outerHorizon M Q with ha
  set b := innerHorizon M Q with hb
  have ha0 : 0 < a := by
    have := Real.sqrt_nonneg (M ^ 2 - Q ^ 2)
    rw [ha]
    unfold outerHorizon
    linarith
  set γ : ℝ := 2 * M * ω - q * Q with hγ
  set ν : ℂ := -(I * (2 * (M : ℂ) * ω - q * Q)) with hνdef
  set Rt : ℝ → ℂ := fun r : ℝ => (r : ℂ) * exp (-(I * ω * r)) * (r : ℂ) ^ ν * R r with hRt
  have hν : ν.re = 0 := by simp [hνdef]
  have hνi : ν.im = -γ := by simp [hνdef, hγ]
  have hform : ∀ r ∈ Ioi a, delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im =
      delta M Q r / r ^ 2 *
        ((ω + γ / r) * ‖Rt r‖ ^ 2 + (deriv Rt r * (starRingEnd ℂ) (Rt r)).im) := by
    intro r hr
    have hr0 : 0 < r := ha0.trans hr
    have h : r ^ 2 * (deriv R r * (starRingEnd ℂ) (R r)).im =
        (deriv Rt r * (starRingEnd ℂ) (Rt r)).im + (ω - ν.im / r) * ‖Rt r‖ ^ 2 :=
      infinity_im_flux hr0 hν (hR r hr).1
    rw [hνi] at h
    have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr0.ne'
    calc delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im
        = delta M Q r / r ^ 2 * (r ^ 2 * (deriv R r * (starRingEnd ℂ) (R r)).im) := by
          field_simp
      _ = _ := by rw [h]; ring
  have hRt' : Tendsto Rt atTop (𝓝 BI) := by
    have h1 : (fun r => Rt r - BI) =O[atTop] (fun r : ℝ => r⁻¹) := hI.1
    exact tendsto_sub_nhds_zero_iff.1 (h1.trans_tendsto tendsto_inv_atTop_zero)
  have ht : Tendsto (deriv Rt) atTop (𝓝 0) := by
    have h1 : deriv Rt =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹) := hI.2
    exact h1.trans_tendsto (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero))
  have hIm : Tendsto (fun r => (deriv Rt r * (starRingEnd ℂ) (Rt r)).im) atTop (𝓝 0) := by
    have h1 := ht.mul ((Complex.continuous_conj.tendsto BI).comp hRt')
    have h2 := (Complex.continuous_im.tendsto _).comp h1
    rw [zero_mul, Complex.zero_im] at h2
    exact h2
  have hγ' : Tendsto (fun r : ℝ => ω + γ / r) atTop (𝓝 (ω + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  have hΔ : Tendsto (fun r => delta M Q r / r ^ 2) atTop (𝓝 1) := by
    have h1 : Tendsto (fun r : ℝ => (1 - a / r) * (1 - b / r)) atTop (𝓝 ((1 - 0) * (1 - 0))) :=
      (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)).mul
        (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id))
    rw [sub_zero, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    unfold delta
    rw [← ha, ← hb]
    field_simp
  have hlim := hΔ.mul ((hγ'.mul (hRt'.norm.pow 2)).add hIm)
  have hval : (1 : ℝ) * ((ω + 0) * ‖BI‖ ^ 2 + 0) = ω * ‖BI‖ ^ 2 := by ring
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop a] with r hr
  exact (hform r hr).symm

end Infinity

end ModeStability.Flux

end
