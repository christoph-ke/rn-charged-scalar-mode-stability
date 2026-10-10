module

public import Mathlib
public import ModeStability.Frozen.ComplementaryBandExclusion
public import ModeStability.Frozen.DephasedCurrentLemma
public import ModeStability.Frozen.ExactReduction
public import ModeStability.Corotation.Basic
public import ModeStability.Corotation.Monotone
public import ModeStability.Corotation.Assembly
public import ModeStability.Endpoint.Horizon
public import ModeStability.ODE.Uniqueness
public import ModeStability.AllAngular.ConstantNormalization
public import ModeStability.AllAngular.BandExclusionCoeff
public import ModeStability.AllAngular.BandExclusionFlux

/-!
# The complementary-band exclusion by the all-angular method, conditionally on four parts

Source: the all-angular research notes in preparation, pp. 1–6 (the flux reduction (1.6)–(1.7),
the two static normalizations (2.2), Lemma 2.2, the current (4.2) and the endpoint limits (4.4)),
specialized to `L = 0`, applied to the band `ω > 0`, `2Mω − e ≥ 0` of the trust boundary
`ModeStability.ComplementaryBandExclusion` (the spherical research notes in preparation,
Appendix A).

Fix a solution `R` with (1.3), (1.4), `ω > 0`, `0 ≤ 2Mω − e` (`e = qQ`, `r₀ = e/ω`).

* `K(a) ≥ 0`: the flux identity forces `B_I = 0`, and uniqueness at infinity gives `R ≡ 0`
  (`cbe_flux_band`).
* `K(a) < 0`: then `a < r₀ ≤ 2M`.
  * `r₀ < 2M`, constant normalization (`y = h(r)`, `U = R ∘ r`, `f = −K ∘ r`): the current
    alternatives of `Corotation.Monotone` at `y₀ = h(r₀)` with the endpoint limits at `y ↓ 0`
    (infinity) and `y → ∞` (horizon) give `Re (U_y Ū)(y₀) > 0` and `< 0` unless `U` vanishes on
    an interval, which forces `R ≡ 0` (`cbe_constant_case`).
  * `r₀ = 2M`, reciprocal normalization (`x = 1/h`, `U = xR ∘ r`, `k = transformedK`): the same
    argument with the landed horizon limit, the interface limit at infinity, and the coefficient
    inequalities for `ν = 0` (`cbe_interface_case`).

`complementaryBandExclusion_of_parts` takes the four parts still being proved (uniqueness at
infinity, the two constant-normalization endpoint limits, and the interface endpoint limit) as
hypotheses, in their universally closed form. It is an internal conditional helper, not the
source theorem.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- If `U(y) = R(r(y))`, `r(y) = radiusOf M Q (1/y)`, vanishes on an open interval
`(c, d) ⊆ (0, ∞)`, then `R` vanishes on the exterior: `R(r₁) = 0` and `−Δ R'(r₁) = U_y(y₁) = 0`
at `y₁ = (c + d)/2`, `r₁ = r(y₁)`, then interior uniqueness. -/
theorem cbe_eqOn_zero_of_constant_vanish {M Q q ω : ℝ} (hQ : |Q| < M) {R : ℝ → ℂ}
    (hR : IsRadialSolution M Q q ω R) {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d)
    (h : ∀ y ∈ Ioo c d, R (radiusOf M Q (1 / y)) = 0) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  have hy₁ : (c + d) / 2 ∈ Ioo c d := ⟨by linarith, by linarith⟩
  have hy₁0 : 0 < (c + d) / 2 := by linarith
  have hra := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy₁0)
  have h0 : R (radiusOf M Q (1 / ((c + d) / 2))) = 0 := h _ hy₁
  have hev : (fun t : ℝ => R (radiusOf M Q (1 / t))) =ᶠ[𝓝 ((c + d) / 2)] fun _ => (0 : ℂ) :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds hy₁.1 hy₁.2) h
  have hD := hasDerivAt_constant_reduced hQ hR hy₁0
  have hD0 : HasDerivAt (fun t : ℝ => R (radiusOf M Q (1 / t))) 0 ((c + d) / 2) :=
    (hasDerivAt_const ((c + d) / 2) (0 : ℂ)).congr_of_eventuallyEq hev
  have h1 := hD.unique hD0
  have hΔ : ((delta M Q (radiusOf M Q (1 / ((c + d) / 2))) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (delta_pos hQ hra).ne'
  have h2 : deriv R (radiusOf M Q (1 / ((c + d) / 2))) = 0 := by
    have h3 : ((delta M Q (radiusOf M Q (1 / ((c + d) / 2))) : ℝ) : ℂ) *
        deriv R (radiusOf M Q (1 / ((c + d) / 2))) = 0 := by
      rw [neg_mul] at h1
      exact neg_eq_zero.1 h1
    exact (mul_eq_zero.1 h3).resolve_left hΔ
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

/-- **The case `a < r₀ < 2M`** (constant normalization), conditionally on the two endpoint
limits of the constant normalization. -/
theorem cbe_constant_case
    (hcH : ∀ {M Q q ω : ℝ}, 0 < M → |Q| < M → radialK (q * Q) ω (outerHorizon M Q) ≠ 0 →
      2 * ω * outerHorizon M Q - q * Q ≠ 0 → ∀ {y₀ : ℝ}, 0 < y₀ → ∀ {R : ℝ → ℂ} {B : ℂ},
      IsRadialSolution M Q q ω R → HorizonCondition M Q q ω R B →
      Tendsto (dephasedCurrent (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y)))
          (dephase (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y))) y₀ 1
            (fun y => R (radiusOf M Q (1 / y))))) atTop (𝓝 0))
    (hcI : ∀ {M Q q ω : ℝ}, 0 < M → |Q| < M → ω ≠ 0 → ∀ {y₀ : ℝ}, 0 < y₀ →
      ∀ {R : ℝ → ℂ} {B : ℂ}, IsRadialSolution M Q q ω R → InfinityCondition M Q q ω R B →
      Tendsto (dephasedCurrent (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y)))
          (dephase (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y))) y₀ (-1)
            (fun y => R (radiusOf M Q (1 / y))))) (𝓝[>] 0) (𝓝 0))
    {M Q q ω : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (hKa : radialK (q * Q) ω (outerHorizon M Q) < 0)
    (h₀ : outerHorizon M Q < q * Q / ω) (h2M : q * Q / ω < 2 * M)
    {R : ℝ → ℂ} {BH BI : ℂ} (hR : IsRadialSolution M Q q ω R)
    (hH : HorizonCondition M Q q ω R BH) (hI : InfinityCondition M Q q ω R BI) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  have hy₀ : 0 < staticSolution M Q (q * Q / ω) := staticSolution_pos hQ h₀
  have hrad : radiusOf M Q (1 / staticSolution M Q (q * Q / ω)) = q * Q / ω :=
    radiusOf_one_div_staticSolution hQ h₀
  have hk₀ : (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y)))
      (staticSolution M Q (q * Q / ω)) = 0 := by
    simp only
    rw [hrad, radialK_corotation hω.ne' rfl, neg_zero]
  -- `K'(a) = 2ωa − e > 0`, since `a ≥ M` and `e < 2Mω`
  have hK'a : 2 * ω * outerHorizon M Q - q * Q ≠ 0 := by
    have haM : M ≤ outerHorizon M Q := by
      unfold outerHorizon
      linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
    have he : q * Q < 2 * M * ω := (div_lt_iff₀ hω).1 h2M
    have : 2 * ω * M ≤ 2 * ω * outerHorizon M Q :=
      mul_le_mul_of_nonneg_left haM (by linarith)
    exact (show 0 < 2 * ω * outerHorizon M Q - q * Q by linarith).ne'
  have hU := constant_reduction hM hQ hR
  have hk := (constant_coefficient (q := q) (ω := ω) hQ).1
  have hkE := constant_coefficient_inequalities hM hQ hω h₀ h2M
  have hCI := hcI hM hQ hω.ne' hy₀ hR hI
  have hCH := hcH hM hQ hKa.ne hK'a hy₀ hR hH
  rcases Corotation.horizon_alternative hy₀ hk (fun y hy => (hkE y hy).1)
      (fun y hy => (hkE y hy).2) hU hk₀ (Or.inr rfl) hCI with h1 | h1
  · rcases Corotation.infinity_alternative hy₀ hk (fun y hy => (hkE y hy).1)
        (fun y hy => (hkE y hy).2) hU hk₀ (Or.inl rfl) hCH with h2 | h2
    · exact absurd (h1.trans h2) (lt_irrefl _)
    · exact cbe_eqOn_zero_of_constant_vanish hQ hR hy₀.le (lt_add_one _)
        fun y hy => h2 y hy.1
  · exact cbe_eqOn_zero_of_constant_vanish hQ hR le_rfl hy₀ h1

/-- **The interface `r₀ = 2M`** (reciprocal normalization), conditionally on the interface
endpoint limit at infinity. -/
theorem cbe_interface_case
    (hiface : ∀ {M Q q ω : ℝ}, 0 < M → |Q| < M → ω ≠ 0 → 2 * M * ω - q * Q = 0 →
      ∀ {x₀ : ℝ}, 0 < x₀ → ∀ {R : ℝ → ℂ} {B : ℂ}, IsRadialSolution M Q q ω R →
      InfinityCondition M Q q ω R B →
      Tendsto (dephasedCurrent (transformedK M Q q ω)
          (dephase (transformedK M Q q ω) x₀ (-1) (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))))
        atTop (𝓝 0))
    {M Q q ω : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (hKa : radialK (q * Q) ω (outerHorizon M Q) < 0)
    (h₀ : outerHorizon M Q < q * Q / ω) (h2M : q * Q / ω = 2 * M)
    {R : ℝ → ℂ} {BH BI : ℂ} (hR : IsRadialSolution M Q q ω R)
    (hH : HorizonCondition M Q q ω R BH) (hI : InfinityCondition M Q q ω R BI) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  have hg : 0 < staticSolution M Q (q * Q / ω) := staticSolution_pos hQ h₀
  have hx₀ : 0 < 1 / staticSolution M Q (q * Q / ω) := one_div_pos.2 hg
  have hrad : radiusOf M Q (1 / staticSolution M Q (q * Q / ω)) = q * Q / ω :=
    radiusOf_one_div_staticSolution hQ h₀
  have hk₀ : transformedK M Q q ω (1 / staticSolution M Q (q * Q / ω)) = 0 := by
    unfold transformedK
    rw [hrad, radialK_corotation hω.ne' rfl, mul_zero]
  have hc : 2 * M * ω - q * Q = 0 := by
    have : q * Q = 2 * M * ω := by
      rw [div_eq_iff hω.ne'] at h2M
      exact h2M
    linarith
  obtain ⟨hk, hkE⟩ := cbe_coefficient_inequalities hM hQ hω (r₀ := q * Q / ω) rfl h2M.ge
  have hU : ∀ x ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x ∧
        HasDerivAt (deriv fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))
          (-((transformedK M Q q ω x ^ 2 : ℝ) : ℂ) * ((x : ℂ) * R (radiusOf M Q x))) x :=
    exact_reduction M Q q ω hM hQ R hR
  have hlimH := Endpoint.horizon_current_tendsto hM hQ hKa.ne hx₀ hR hH
  have hlimI := hiface hM hQ hω.ne' hc hx₀ hR hI
  rcases Corotation.horizon_alternative hx₀ hk (fun x hx => (hkE x hx).1)
      (fun x hx => (hkE x hx).2) hU hk₀ (Or.inl rfl) hlimH with h1 | h1
  · rcases Corotation.infinity_alternative hx₀ hk (fun x hx => (hkE x hx).1)
        (fun x hx => (hkE x hx).2) hU hk₀ (Or.inr rfl) hlimI with h2 | h2
    · exact absurd (h1.trans h2) (lt_irrefl _)
    · refine Corotation.eqOn_zero_of_reduced_eventuallyEq_zero hQ hR
        (x₁ := 1 / staticSolution M Q (q * Q / ω) + 1) (by linarith) ?_
      filter_upwards [Ioi_mem_nhds (show 1 / staticSolution M Q (q * Q / ω) <
        1 / staticSolution M Q (q * Q / ω) + 1 by linarith)] with y hy
      exact h2 y hy
  · refine Corotation.eqOn_zero_of_reduced_eventuallyEq_zero hQ hR (half_pos hx₀) ?_
    filter_upwards [Ioo_mem_nhds (half_pos hx₀) (half_lt_self hx₀)] with y hy
    exact h1 y hy

/-- **The complementary-band exclusion** (`ModeStability.ComplementaryBandExclusion`) by the
method of the all-angular paper, conditionally on its four remaining parts: uniqueness at
infinity (`huniq`), the horizon and infinity limits of the current in the constant
normalization (`hcH`, `hcI`), and the infinity limit of the current at the interface
`r₀ = 2M` in the reciprocal normalization (`hiface`). Internal conditional helper. -/
theorem complementaryBandExclusion_of_parts
    (huniq : ∀ {M Q e ω L : ℝ}, 0 < M → |Q| ≤ M → ω ≠ 0 → ∀ {Θ : ℝ → ℝ},
      (∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r) →
      ∀ {R : ℝ → ℂ},
      (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
        HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
          (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) →
      (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) =O[atTop] (fun r : ℝ => r⁻¹) →
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) =O[atTop]
        (fun r : ℝ => (r ^ 2)⁻¹) →
      EqOn R 0 (Ioi (outerHorizon M Q)))
    (hcH : ∀ {M Q q ω : ℝ}, 0 < M → |Q| < M → radialK (q * Q) ω (outerHorizon M Q) ≠ 0 →
      2 * ω * outerHorizon M Q - q * Q ≠ 0 → ∀ {y₀ : ℝ}, 0 < y₀ → ∀ {R : ℝ → ℂ} {B : ℂ},
      IsRadialSolution M Q q ω R → HorizonCondition M Q q ω R B →
      Tendsto (dephasedCurrent (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y)))
          (dephase (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y))) y₀ 1
            (fun y => R (radiusOf M Q (1 / y))))) atTop (𝓝 0))
    (hcI : ∀ {M Q q ω : ℝ}, 0 < M → |Q| < M → ω ≠ 0 → ∀ {y₀ : ℝ}, 0 < y₀ →
      ∀ {R : ℝ → ℂ} {B : ℂ}, IsRadialSolution M Q q ω R → InfinityCondition M Q q ω R B →
      Tendsto (dephasedCurrent (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y)))
          (dephase (fun y => -radialK (q * Q) ω (radiusOf M Q (1 / y))) y₀ (-1)
            (fun y => R (radiusOf M Q (1 / y))))) (𝓝[>] 0) (𝓝 0))
    (hiface : ∀ {M Q q ω : ℝ}, 0 < M → |Q| < M → ω ≠ 0 → 2 * M * ω - q * Q = 0 →
      ∀ {x₀ : ℝ}, 0 < x₀ → ∀ {R : ℝ → ℂ} {B : ℂ}, IsRadialSolution M Q q ω R →
      InfinityCondition M Q q ω R B →
      Tendsto (dephasedCurrent (transformedK M Q q ω)
          (dephase (transformedK M Q q ω) x₀ (-1) (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))))
        atTop (𝓝 0)) :
    ModeStability.ComplementaryBandExclusion := by
  unfold ComplementaryBandExclusion
  intro M Q q ω hM hQ hω hband R BH BI hR hH hI
  rcases le_or_gt 0 (radialK (q * Q) ω (outerHorizon M Q)) with hK | hK
  · exact cbe_flux_band huniq hM hQ hω hK hR hH hI
  · -- `K(a) < 0` gives `a < r₀`, and the band gives `r₀ ≤ 2M`
    have ha : 0 < outerHorizon M Q := outerHorizon_pos hM
    have h₀ : outerHorizon M Q < q * Q / ω := by
      rw [lt_div_iff₀ hω]
      have h : outerHorizon M Q * (outerHorizon M Q * ω - q * Q) < 0 := by
        unfold radialK at hK
        linarith
      have h' : outerHorizon M Q * ω - q * Q < 0 := neg_of_mul_neg_right h ha.le
      linarith
    have h2M : q * Q / ω ≤ 2 * M := by
      rw [div_le_iff₀ hω]
      linarith
    rcases h2M.lt_or_eq with hlt | heq
    · exact cbe_constant_case hcH hcI hM hQ hω hK h₀ hlt hR hH hI
    · exact cbe_interface_case hiface hM hQ hω hK h₀ heq hR hH hI

end ModeStability.AllAngular

end
