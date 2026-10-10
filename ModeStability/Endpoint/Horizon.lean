module

public import ModeStability.Endpoint.HorizonAux

/-!
# The horizon endpoint current (2.11)–(2.13)

Source: the spherical research notes in preparation, p. 3, (2.11)–(2.13).

For a solution `R` of (1.2) satisfying the horizon condition (1.3) with `K(a) ≠ 0`, put
`U(x) = x R(r(x))` and `v_H = e^{iϑ} U` as in (2.9). Then `J[v_H](x) → 0` as `x → 0⁺`
(`horizon_current_tendsto`).

Route. For `x > 0`, `r = r(x)`, the current is phase-free (`dephasedCurrent_dephase_eq`), and
removing the horizon oscillation `R = (r − a)^{−iκ} R̃`, `κ = K(a)/d`, gives
(`horizon_current_eq`)

`J[v_H](x) = −(x K/(K'(Δ/x) − 2K)) |R̃ + (Δ/x) R̃' + i((r − a)/x) L R̃|²`
`            − x|R̃|² − Re(Δ R̃' conj R̃)`

with `L(r) = ω(r + a) − qQ − κ`. By (2.11), `r → a⁺` and `(r − a)/x → 0`; by (1.3), `R̃ → B` and
`R̃'` is bounded; hence every term tends to `0` (`tendsto_current_form`).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Endpoint

variable {M Q q ω : ℝ}

/-- `R̃(r) → B` as `r → a⁺`, from (1.3). -/
theorem tendsto_horizonProfile {R : ℝ → ℂ} {B : ℂ} (hH : HorizonCondition M Q q ω R B) :
    Tendsto (horizonProfile M Q q ω R) (𝓝[>] (outerHorizon M Q)) (𝓝 B) := by
  have h0 : Tendsto (fun r : ℝ => r - outerHorizon M Q) (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
    exact tendsto_sub_nhds_zero_iff.2 (tendsto_id.mono_left nhdsWithin_le_nhds)
  have h : (fun r => horizonProfile M Q q ω R r - B) =O[𝓝[>] (outerHorizon M Q)]
      (fun r => r - outerHorizon M Q) := hH.1
  exact tendsto_sub_nhds_zero_iff.1 (h.trans_tendsto h0)

/-- `R̃'(r)` is bounded as `r → a⁺`, from (1.3). -/
theorem isBoundedUnder_deriv_horizonProfile {R : ℝ → ℂ} {B : ℂ}
    (hH : HorizonCondition M Q q ω R B) :
    IsBoundedUnder (· ≤ ·) (𝓝[>] (outerHorizon M Q))
      (fun r => ‖deriv (horizonProfile M Q q ω R) r‖) := by
  have h : deriv (horizonProfile M Q q ω R) =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)) :=
    hH.2
  exact (isBigO_one_iff ℝ).1 h

/-- The horizon current written through the de-oscillated profile `R̃`, for `x > 0`. -/
theorem horizon_current_eq (hQ : |Q| < M) (hκ : horizonFreq M Q q ω ≠ 0) {x₀ : ℝ}
    (hx₀ : 0 < x₀) {R : ℝ → ℂ} (hR : IsRadialSolution M Q q ω R) {x : ℝ} (hx : 0 < x) :
    dephasedCurrent (transformedK M Q q ω)
        (dephase (transformedK M Q q ω) x₀ 1 (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))) x =
      -(x * (radialK (q * Q) ω (radiusOf M Q x) /
          ((2 * ω * radiusOf M Q x - q * Q) * (delta M Q (radiusOf M Q x) / x) -
            2 * radialK (q * Q) ω (radiusOf M Q x)))) *
          ‖horizonProfile M Q q ω R (radiusOf M Q x) +
            ((delta M Q (radiusOf M Q x) / x : ℝ) : ℂ) *
              deriv (horizonProfile M Q q ω R) (radiusOf M Q x) +
            I * (((radiusOf M Q x - outerHorizon M Q) / x *
              (ω * (radiusOf M Q x + outerHorizon M Q) - q * Q - horizonFreq M Q q ω) : ℝ) : ℂ) *
              horizonProfile M Q q ω R (radiusOf M Q x)‖ ^ 2 -
        x * ‖horizonProfile M Q q ω R (radiusOf M Q x)‖ ^ 2 -
        (((delta M Q (radiusOf M Q x) : ℝ) : ℂ) *
            deriv (horizonProfile M Q q ω R) (radiusOf M Q x) *
          (starRingEnd ℂ) (horizonProfile M Q q ω R (radiusOf M Q x))).re := by
  have hr := outerHorizon_lt_radiusOf hQ hx
  have hU := hasDerivAt_reducedSolution hQ hR hx
  rw [dephasedCurrent_dephase_eq hx₀ (continuousOn_transformedK hQ) 1 hx hU.differentiableAt,
    (hasDerivAt_transformedK hQ hx).deriv, hU.deriv, transformedK_eq_div hQ hx,
    staticSolution_radiusOf hQ hx]
  exact current_algebra (a := outerHorizon M Q) (b := innerHorizon M Q) hx (sub_pos.2 hr) rfl
    (norm_horizonPhase hr) rfl (hasDerivAt_horizonProfile hκ hR hr).deriv
    (radialK_sub_horizonFreq_mul hQ _)

/-- The horizon endpoint limit (2.13): `J[v_H](x) → 0` as `x → 0⁺`, where `v_H = e^{iϑ} U`,
`U(x) = x R(r(x))`, for a solution `R` of (1.2) satisfying the horizon condition (1.3) with
`K(a) ≠ 0`. -/
theorem horizon_current_tendsto {M Q q ω : ℝ} (_hM : 0 < M) (hQ : |Q| < M)
    (hKa : radialK (q * Q) ω (outerHorizon M Q) ≠ 0) {x₀ : ℝ} (hx₀ : 0 < x₀)
    {R : ℝ → ℂ} {B : ℂ} (hR : IsRadialSolution M Q q ω R) (hH : HorizonCondition M Q q ω R B) :
    Tendsto (dephasedCurrent (transformedK M Q q ω)
        (dephase (transformedK M Q q ω) x₀ 1 (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))))
      (𝓝[>] 0) (𝓝 0) := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hκ : horizonFreq M Q q ω ≠ 0 := div_ne_zero hKa hd.ne'
  have hr := tendsto_radiusOf_nhdsGT hQ
  have hr' : Tendsto (radiusOf M Q) (𝓝[>] 0) (𝓝 (outerHorizon M Q)) :=
    hr.mono_right nhdsWithin_le_nhds
  have hcK : Continuous (radialK (q * Q) ω) := by
    unfold radialK
    fun_prop
  have hcΔ : Continuous (delta M Q) := by
    unfold delta
    fun_prop
  have hΔa : delta M Q (outerHorizon M Q) = 0 := by
    unfold delta
    ring
  have hra := tendsto_radiusOf_sub_div hQ
  have hΔ : Tendsto (fun x => delta M Q (radiusOf M Q x)) (𝓝[>] 0) (𝓝 0) := by
    have h := (hcΔ.tendsto (outerHorizon M Q)).comp hr'
    rw [hΔa] at h
    exact h
  have hD : Tendsto (fun x => delta M Q (radiusOf M Q x) / x) (𝓝[>] 0) (𝓝 0) := by
    have h := hra.mul (hr'.sub_const (innerHorizon M Q))
    rw [zero_mul] at h
    refine h.congr fun x => ?_
    unfold delta
    ring
  have hE : Tendsto (fun x => (radiusOf M Q x - outerHorizon M Q) / x *
      (ω * (radiusOf M Q x + outerHorizon M Q) - q * Q - horizonFreq M Q q ω))
      (𝓝[>] 0) (𝓝 0) := by
    have hL : Tendsto (fun x => ω * (radiusOf M Q x + outerHorizon M Q) - q * Q -
        horizonFreq M Q q ω) (𝓝[>] 0)
        (𝓝 (ω * (outerHorizon M Q + outerHorizon M Q) - q * Q - horizonFreq M Q q ω)) :=
      ((hr'.add_const _).const_mul ω |>.sub_const _).sub_const _
    have h := hra.mul hL
    rw [zero_mul] at h
    exact h
  have hK' : Tendsto (fun x => 2 * ω * radiusOf M Q x - q * Q) (𝓝[>] 0)
      (𝓝 (2 * ω * outerHorizon M Q - q * Q)) :=
    (hr'.const_mul _).sub_const _
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hlim := tendsto_current_form hKa hx ((hcK.tendsto _).comp hr') hK' hD hE hΔ
    ((tendsto_horizonProfile hH).comp hr)
    (hr.isBoundedUnder_comp (isBoundedUnder_deriv_horizonProfile hH))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (horizon_current_eq hQ hκ hx₀ hR hx).symm

end ModeStability.Endpoint

end
