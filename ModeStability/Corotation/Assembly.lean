module

public import Mathlib
public import ModeStability.Corotation.Basic
public import ModeStability.Corotation.Monotone
public import ModeStability.Exterior.Reduction
public import ModeStability.Endpoint.Common
public import ModeStability.ODE.Uniqueness
public import ModeStability.Frozen.ExactReduction
public import ModeStability.Frozen.CoefficientInequalities
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition

/-!
# Proposition 2.3 (separation at corotation), conditionally on the endpoint limits

Assembly of Proposition 2.3 of the spherical research notes in preparation (p. 3, (2.16)) in band
(1.6), from the abstract current facts of `ModeStability.Corotation.Monotone`, the exact reduction
(Lemma 2.1) and interior ODE uniqueness. The two endpoint limits `J[v_H] → 0` at `x ↓ 0` and
`J[v_I] → 0` at `x → ∞` (2.11)-(2.15) are hypotheses of `separation_at_corotation_of_limits`;
they are proved separately.

* `eqOn_zero_of_reduced_eventuallyEq_zero`: `U = x R(r(x)) ≡ 0` near a point forces `R ≡ 0`;
* `reduced_at_corotation`: (2.19), `U(x₀) = R(r₀)/g(r₀)`, `U_x(x₀) = R(r₀) + g(r₀)Δ(r₀)R'(r₀)`;
* `ne_zero_and_lt_of_re_pos`, `ne_zero_and_gt_of_re_neg`: (2.19) turns the sign of
  `Re (U_x Ū)(x₀)` into (2.16);
* `separation_at_corotation_of_limits`: the conditional form of Proposition 2.3.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Corotation

/-- If `U(y) = y R(r(y))` vanishes near some `x₁ > 0`, then the solution `R` of (1.2) vanishes on
the whole exterior: `R(r₁) = R'(r₁) = 0` at `r₁ = r(x₁)`, then interior uniqueness. -/
theorem eqOn_zero_of_reduced_eventuallyEq_zero {M Q q ω : ℝ} (hQ : |Q| < M) {R : ℝ → ℂ}
    (hR : IsRadialSolution M Q q ω R) {x₁ : ℝ} (hx₁ : 0 < x₁)
    (h : (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) =ᶠ[𝓝 x₁] 0) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  have hra : outerHorizon M Q < radiusOf M Q x₁ := outerHorizon_lt_radiusOf hQ hx₁
  have hx₁c : (x₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx₁.ne'
  have h0 : R (radiusOf M Q x₁) = 0 := by
    have := h.self_of_nhds
    simp only [Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hx₁c
  have hD := hasDerivAt_reducedSolution hQ hR hx₁
  have hD0 : HasDerivAt (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) 0 x₁ :=
    (hasDerivAt_const x₁ (0 : ℂ)).congr_of_eventuallyEq h
  have h1 := hD.unique hD0
  rw [h0, zero_add] at h1
  have hg : ((staticSolution M Q (radiusOf M Q x₁) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (staticSolution_pos hQ hra).ne'
  have hΔ : ((delta M Q (radiusOf M Q x₁) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (delta_pos hQ hra).ne'
  have h2 : deriv R (radiusOf M Q x₁) = 0 :=
    ((mul_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hg)).resolve_left hΔ)
  have hΔc : ContinuousOn (delta M Q) (Ioi (outerHorizon M Q)) := by
    unfold delta
    fun_prop
  have hΔ0 : ∀ r ∈ Ioi (outerHorizon M Q), 0 < delta M Q r := fun r hr => delta_pos hQ hr
  have hK : ContinuousOn (fun r => radialK (q * Q) ω r ^ 2 / delta M Q r)
      (Ioi (outerHorizon M Q)) := by
    refine ContinuousOn.div ?_ hΔc fun r hr => (hΔ0 r hr).ne'
    unfold radialK
    fun_prop
  exact ODE.eqOn_zero_of_linear_ode hΔc hΔ0 hK hR hra h0 h2

/-- (2.19): `U(x₀) = R(r₀)/g(r₀)` and `U_x(x₀) = R(r₀) + g(r₀)Δ(r₀)R'(r₀)` for `U(y) = y R(r(y))`
at `x₀ = 1/g(r₀)`, `r₀ > a`. -/
theorem reduced_at_corotation {M Q q ω : ℝ} (hQ : |Q| < M) {R : ℝ → ℂ}
    (hR : IsRadialSolution M Q q ω R) {r₀ : ℝ} (hr₀ : outerHorizon M Q < r₀) (U : ℝ → ℂ)
    (hU : U = fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) :
    U (1 / staticSolution M Q r₀) = ((1 / staticSolution M Q r₀ : ℝ) : ℂ) * R r₀ ∧
      deriv U (1 / staticSolution M Q r₀) = R r₀ + (staticSolution M Q r₀ : ℂ) *
        ((delta M Q r₀ : ℂ) * deriv R r₀) := by
  subst hU
  have hrad := radiusOf_one_div_staticSolution hQ hr₀
  have hx₀ : 0 < 1 / staticSolution M Q r₀ := one_div_pos.2 (staticSolution_pos hQ hr₀)
  refine ⟨by simp only [hrad], ?_⟩
  have := (hasDerivAt_reducedSolution hQ hR hx₀).deriv
  rw [hrad] at this
  exact this

/-- Real-part algebra for (2.19): with `U = R/g` and `U_x = R + gΔR'`,
`Re (U_x Ū) = (|R|² + gΔ Re (R' R̄))/g`. -/
theorem re_reduced (g Δ : ℝ) (hg : 0 < g) (R R' : ℂ) :
    ((R + (g : ℂ) * ((Δ : ℂ) * R')) * (starRingEnd ℂ) (((1 / g : ℝ) : ℂ) * R)).re =
      (Complex.normSq R + g * Δ * (R' * (starRingEnd ℂ) R).re) / g := by
  have hg' : g ≠ 0 := hg.ne'
  simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  field_simp
  ring

/-- `Re (R'/R) = Re (R' R̄) / |R|²`. -/
theorem div_re_eq (R R' : ℂ) :
    (R' / R).re = (R' * (starRingEnd ℂ) R).re / Complex.normSq R := by
  rw [Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- (2.19) turns `Re (U_x Ū)(x₀) > 0` into `R ≠ 0` and `Re R'/R > -1/(Δ g)`. -/
theorem ne_zero_and_lt_of_re_pos {g Δ : ℝ} (hg : 0 < g) (hΔ : 0 < Δ) {R R' : ℂ}
    (h : 0 < ((R + (g : ℂ) * ((Δ : ℂ) * R')) *
      (starRingEnd ℂ) (((1 / g : ℝ) : ℂ) * R)).re) :
    R ≠ 0 ∧ -1 / (Δ * g) < (R' / R).re := by
  rw [re_reduced g Δ hg] at h
  have h1 : 0 < Complex.normSq R + g * Δ * (R' * (starRingEnd ℂ) R).re :=
    (div_pos_iff_of_pos_right hg).1 h
  have hR : R ≠ 0 := by
    rintro rfl
    simp at h1
  have hn : 0 < Complex.normSq R := Complex.normSq_pos.2 hR
  refine ⟨hR, ?_⟩
  rw [div_re_eq, div_lt_div_iff₀ (mul_pos hΔ hg) hn]
  nlinarith

/-- (2.19) turns `Re (U_x Ū)(x₀) < 0` into `R ≠ 0` and `Re R'/R < -1/(Δ g)`. -/
theorem ne_zero_and_gt_of_re_neg {g Δ : ℝ} (hg : 0 < g) (hΔ : 0 < Δ) {R R' : ℂ}
    (h : ((R + (g : ℂ) * ((Δ : ℂ) * R')) *
      (starRingEnd ℂ) (((1 / g : ℝ) : ℂ) * R)).re < 0) :
    R ≠ 0 ∧ (R' / R).re < -1 / (Δ * g) := by
  rw [re_reduced g Δ hg] at h
  have h1 : Complex.normSq R + g * Δ * (R' * (starRingEnd ℂ) R).re < 0 :=
    by have := (div_lt_iff₀ hg).1 h; linarith
  have hR : R ≠ 0 := by
    rintro rfl
    simp at h1
  have hn : 0 < Complex.normSq R := Complex.normSq_pos.2 hR
  refine ⟨hR, ?_⟩
  rw [div_re_eq, div_lt_div_iff₀ hn (mul_pos hΔ hg)]
  nlinarith

/-- If the real parts of the logarithmic derivatives differ, the Wronskian does not vanish. -/
theorem mul_wronskian_ne_zero {Δ : ℝ} (hΔ : 0 < Δ) {RH RH' RI RI' : ℂ} (hH : RH ≠ 0)
    (hI : RI ≠ 0) (h : (RI' / RI).re < (RH' / RH).re) :
    (Δ : ℂ) * (RH * RI' - RH' * RI) ≠ 0 := by
  refine mul_ne_zero (Complex.ofReal_ne_zero.2 hΔ.ne') fun hw => ?_
  have hw' : RI' / RI = RH' / RH := by
    rw [div_eq_div_iff hI hH]
    linear_combination hw
  rw [hw'] at h
  exact lt_irrefl _ h

/-- The horizon side of Proposition 2.3: from `J[v_H] → 0` at `0⁺`, a nonzero solution satisfies
`R(r₀) ≠ 0` and `Re R'/R(r₀) > -1/(Δ g)(r₀)`. -/
theorem horizon_side {M Q q ω r₀ : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (hr₀ : r₀ = q * Q / ω) (hband : 2 * M < r₀) {R : ℝ → ℂ} (hR : IsRadialSolution M Q q ω R)
    (hR0 : ¬ EqOn R 0 (Ioi (outerHorizon M Q)))
    (hlim : Tendsto (dephasedCurrent (transformedK M Q q ω)
      (dephase (transformedK M Q q ω) (1 / staticSolution M Q r₀) 1
        (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)))) (𝓝[>] 0) (𝓝 0)) :
    R r₀ ≠ 0 ∧ -1 / (delta M Q r₀ * staticSolution M Q r₀) < (deriv R r₀ / R r₀).re := by
  have har : outerHorizon M Q < r₀ := outerHorizon_lt_of_band hM hband
  obtain ⟨hx₀, -, hk₀⟩ := corotation_point hM hQ hω hr₀ hband
  obtain ⟨hk, hkE⟩ := coefficient_inequalities M Q q ω hM hQ hω r₀ hr₀ hband
  have hg : 0 < staticSolution M Q r₀ := staticSolution_pos hQ har
  have hΔ : 0 < delta M Q r₀ := delta_pos hQ har
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ → ℂ, U = fun y : ℝ => (y : ℂ) * R (radiusOf M Q y) := ⟨_, rfl⟩
  rw [← hUdef] at hlim
  have hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((transformedK M Q q ω x ^ 2 : ℝ) : ℂ) * U x) x := by
    subst hUdef
    exact exact_reduction M Q q ω hM hQ R hR
  obtain ⟨hU0, hU1⟩ := reduced_at_corotation hQ hR har U hUdef
  rcases horizon_alternative hx₀ hk (fun x hx => (hkE x hx).1) (fun x hx => (hkE x hx).2) hU hk₀
      (Or.inl rfl) hlim with h | h
  · refine ne_zero_and_lt_of_re_pos hg hΔ ?_
    rw [hU0, hU1] at h
    exact h
  · exfalso
    subst hUdef
    refine hR0 (eqOn_zero_of_reduced_eventuallyEq_zero hQ hR (half_pos hx₀) ?_)
    filter_upwards [Ioo_mem_nhds (half_pos hx₀) (half_lt_self hx₀)] with y hy
    exact h y hy

/-- The infinity side of Proposition 2.3: from `J[v_I] → 0` at `∞`, a nonzero solution satisfies
`R(r₀) ≠ 0` and `Re R'/R(r₀) < -1/(Δ g)(r₀)`. -/
theorem infinity_side {M Q q ω r₀ : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (hr₀ : r₀ = q * Q / ω) (hband : 2 * M < r₀) {R : ℝ → ℂ} (hR : IsRadialSolution M Q q ω R)
    (hR0 : ¬ EqOn R 0 (Ioi (outerHorizon M Q)))
    (hlim : Tendsto (dephasedCurrent (transformedK M Q q ω)
      (dephase (transformedK M Q q ω) (1 / staticSolution M Q r₀) (-1)
        (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)))) atTop (𝓝 0)) :
    R r₀ ≠ 0 ∧ (deriv R r₀ / R r₀).re < -1 / (delta M Q r₀ * staticSolution M Q r₀) := by
  have har : outerHorizon M Q < r₀ := outerHorizon_lt_of_band hM hband
  obtain ⟨hx₀, -, hk₀⟩ := corotation_point hM hQ hω hr₀ hband
  obtain ⟨hk, hkE⟩ := coefficient_inequalities M Q q ω hM hQ hω r₀ hr₀ hband
  have hg : 0 < staticSolution M Q r₀ := staticSolution_pos hQ har
  have hΔ : 0 < delta M Q r₀ := delta_pos hQ har
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ → ℂ, U = fun y : ℝ => (y : ℂ) * R (radiusOf M Q y) := ⟨_, rfl⟩
  rw [← hUdef] at hlim
  have hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((transformedK M Q q ω x ^ 2 : ℝ) : ℂ) * U x) x := by
    subst hUdef
    exact exact_reduction M Q q ω hM hQ R hR
  obtain ⟨hU0, hU1⟩ := reduced_at_corotation hQ hR har U hUdef
  rcases infinity_alternative hx₀ hk (fun x hx => (hkE x hx).1) (fun x hx => (hkE x hx).2) hU hk₀
      (Or.inr rfl) hlim with h | h
  · refine ne_zero_and_gt_of_re_neg hg hΔ ?_
    rw [hU0, hU1] at h
    exact h
  · exfalso
    subst hUdef
    refine hR0 (eqOn_zero_of_reduced_eventuallyEq_zero hQ hR (x₁ := 1 / staticSolution M Q r₀ + 1)
      (by linarith) ?_)
    filter_upwards [Ioi_mem_nhds (show 1 / staticSolution M Q r₀ < 1 / staticSolution M Q r₀ + 1
      by linarith)] with y hy
    exact h y hy

/-- **Proposition 2.3** (separation at corotation) in band (1.6), conditionally on the two
endpoint limits `J[v_H] → 0` as `x ↓ 0` and `J[v_I] → 0` as `x → ∞`. Internal helper, not the
source theorem. -/
theorem separation_at_corotation_of_limits :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → 0 < ω →
      ∀ (r₀ : ℝ), r₀ = q * Q / ω → 2 * M < r₀ →
        ∀ (RH RI : ℝ → ℂ) (BH BI : ℂ),
          IsRadialSolution M Q q ω RH → HorizonCondition M Q q ω RH BH →
          ¬ EqOn RH 0 (Ioi (outerHorizon M Q)) →
          IsRadialSolution M Q q ω RI → InfinityCondition M Q q ω RI BI →
          ¬ EqOn RI 0 (Ioi (outerHorizon M Q)) →
          Tendsto (dephasedCurrent (transformedK M Q q ω)
              (dephase (transformedK M Q q ω) (1 / staticSolution M Q r₀) 1
                (fun y : ℝ => (y : ℂ) * RH (radiusOf M Q y)))) (𝓝[>] 0) (𝓝 0) →
          Tendsto (dephasedCurrent (transformedK M Q q ω)
              (dephase (transformedK M Q q ω) (1 / staticSolution M Q r₀) (-1)
                (fun y : ℝ => (y : ℂ) * RI (radiusOf M Q y)))) atTop (𝓝 0) →
            RH r₀ ≠ 0 ∧ RI r₀ ≠ 0 ∧
              -1 / (delta M Q r₀ * staticSolution M Q r₀) < (deriv RH r₀ / RH r₀).re ∧
              (deriv RI r₀ / RI r₀).re < -1 / (delta M Q r₀ * staticSolution M Q r₀) ∧
              delta M Q r₀ * (RH r₀ * deriv RI r₀ - deriv RH r₀ * RI r₀) ≠ 0 := by
  intro M Q q ω hM hQ hω r₀ hr₀ hband RH RI _ _ hRH _ hRH0 hRI _ hRI0 hlimH hlimI
  have har : outerHorizon M Q < r₀ := outerHorizon_lt_of_band hM hband
  have hΔ : 0 < delta M Q r₀ := delta_pos hQ har
  obtain ⟨hH, hHlt⟩ := horizon_side hM hQ hω hr₀ hband hRH hRH0 hlimH
  obtain ⟨hI, hIgt⟩ := infinity_side hM hQ hω hr₀ hband hRI hRI0 hlimI
  refine ⟨hH, hI, hHlt, hIgt, ?_⟩
  exact mul_wronskian_ne_zero hΔ hH hI (hIgt.trans hHlt)

end ModeStability.Corotation

end
