module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.RadiusOf
public import ModeStability.AllAngular.AngularReduction
public import ModeStability.AllAngular.CoordinateCoefficients
public import ModeStability.AllAngular.CoordinateIntervals
public import ModeStability.AllAngular.HorizonLimitsL
public import ModeStability.AllAngular.InfinityLimitsL
public import ModeStability.AllAngular.GlobalIdentity
public import ModeStability.AllAngular.TurningPointGeometry

/-!
# The superradiant band in the subextremal constant normalization

Source: the all-angular research notes in preparation, Sections 2–5: the transformed equation
(2.4) in the constant
normalization `g = 1` (`a < r₀ = e/ω < 2M`), Lemma 2.2 and Proposition 3.1 for
`f̂ = −sgn(K)√(K² − LΔ)`, the turning points (3.1), the endpoint limits (4.4), and the global
identity (5.1)–(5.3) showing that vanishing follows from the interior bulk term for positive
angular momentum and from current rigidity in the spherical case.

The coordinate is the reflected `y = h ∈ (0, ∞)` with `r(y) = radiusOf M Q (1/y)` (decreasing),
`U(y) = R(r(y))`, `U'' = −F U` with `F = K² − LΔ` at `r = r(y)` (`constant_reduction_L`). The
infinity side is `y → 0⁺` (σ = −1), the horizon side is `y → ∞` (σ = 1).

* `s2_lambdaH_pos`: in the superradiant band `K(a) < 0` with `e < 2Mω`, the horizon constant
  `λ_H = 2ωa − e − L(a − b)/(2K(a))` of (4.4) is positive.
* `superradiant_sub_constant`: the superradiant case of Theorem 1.1 (Θ-form) for `|Q| < M`,
  `e/ω < 2M`, both `L > 0` (`eqOn_zero_of_global_current_L`, turning points `x₁ := y₂`,
  `x₂ := y₁`) and `L = 0` (`eqOn_zero_of_global_current_L0`, corotation point `y₀ = h(e/ω)`).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- In the superradiant band `K(a) < 0`, with `L ≥ 0` and `e/ω < 2M`, the horizon constant
`λ_H = 2ωa − e − L(a − b)/(2K(a))` of (4.4) is positive: `2ωa − e ≥ 2ωM − e > 0`, and
`L(a − b)/(2K(a)) ≤ 0`. -/
private theorem s2_lambdaH_pos {M Q e ω L : ℝ} (hL : 0 ≤ L) (hω : 0 < ω)
    (hKa : radialK e ω (outerHorizon M Q) < 0) (hN : e / ω < 2 * M) :
    0 < 2 * ω * outerHorizon M Q - e -
      L * (outerHorizon M Q - innerHorizon M Q) / (2 * radialK e ω (outerHorizon M Q)) := by
  have hsq := Real.sqrt_nonneg (M ^ 2 - Q ^ 2)
  have hab : 0 ≤ outerHorizon M Q - innerHorizon M Q := by
    unfold outerHorizon innerHorizon
    linarith
  have hMa : M ≤ outerHorizon M Q := by
    unfold outerHorizon
    linarith
  have he : e < 2 * M * ω := (div_lt_iff₀ hω).1 hN
  have hωa : 2 * ω * M ≤ 2 * ω * outerHorizon M Q :=
    mul_le_mul_of_nonneg_left hMa (by positivity)
  have hq : L * (outerHorizon M Q - innerHorizon M Q) / (2 * radialK e ω (outerHorizon M Q)) ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (mul_nonneg hL hab) (by linarith)
  linarith

/-- Proposition 3.1 in the subextremal constant coordinate, in the form consumed by the global
identity: where `F = K² − LΔ > 0`, `f̂' ≠ 0` and `(2f̂'² − f̂f̂'')/f̂'² ≥ 0`. -/
private theorem s2_fhat_props {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (hL : 0 ≤ L) (hr₀ : outerHorizon M Q < e / ω) (hN : e / ω < 2 * M) {y : ℝ} (hy : 0 < y)
    (hF : 0 < radialK e ω (radiusOf M Q (1 / y)) ^ 2 - L * delta M Q (radiusOf M Q (1 / y))) :
    deriv (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
        Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / t))))) y ≠ 0 ∧
      0 ≤ (2 * deriv (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
          Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
            L * delta M Q (radiusOf M Q (1 / t))))) y ^ 2 -
        -((SignType.sign (radialK e ω (radiusOf M Q (1 / y))) : ℝ) *
            Real.sqrt (radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
              L * delta M Q (radiusOf M Q (1 / y)))) *
          deriv (deriv fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
            Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
              L * delta M Q (radiusOf M Q (1 / t))))) y) /
        deriv (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
          Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
            L * delta M Q (radiusOf M Q (1 / t))))) y ^ 2 := by
  obtain ⟨-, h1, h2⟩ := constant_fhat_props hM hQ hω hL hr₀ hN hy (sub_pos.1 hF)
  exact ⟨h1.ne', div_nonneg h2.le (sq_nonneg _)⟩

/-- **The superradiant case of Theorem 1.1, subextremal constant normalization.** For `M > 0`,
`|Q| < M`, `L ≥ 0`, `ω > 0`, `K(a) < 0` and `e/ω < 2M`, a solution `R` of
`(ΔR')' + (K²/Δ − L)R = 0` on `r > a` with `Θ' = K/Δ`, the Θ-form horizon condition (1.4) and the
Θ-form outgoing condition (1.5) vanishes on `(a, ∞)`. In the reflected coordinate `y = h`,
`U(y) = R(r(y))` solves `U'' = −(K² − LΔ)U`, the phase-free currents of
`f̂ = −sgn(K)√(K² − LΔ)` vanish at both ends ((4.4)), and the global identity (5.3) forces
`U = 0`. -/
theorem superradiant_sub_constant {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| < M)
    (hL : 0 ≤ L) (hω : 0 < ω) (hKa : radialK e ω (outerHorizon M Q) < 0)
    (hN : e / ω < 2 * M)
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ} {BH BI : ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hH1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - BH)
      =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q))
    (hH2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r)
      =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - BI)
      =O[atTop] (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  have hr₀ : outerHorizon M Q < e / ω := outerHorizon_lt_corotation hM hω hKa
  -- the endpoint limits (4.4): horizon `y → ∞` (σ = 1), infinity `y → 0⁺` (σ = −1)
  have hJH := constant_horizon_current_tendsto_L hQ hL hKa.ne
    (s2_lambdaH_pos hL hω hKa hN).ne' hΘ hR hH1 hH2
  have hJI := constant_infinity_current_tendsto_L hQ hL hω.ne' hΘ hR hI1 hI2
    (f := fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
      Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
        L * delta M Q (radiusOf M Q (1 / t)))))
    (fun _ _ => rfl) (U := fun t => R (radiusOf M Q (1 / t))) (fun _ _ => rfl)
  -- the reduced equation (2.4)
  have hU := constant_reduction_L (L := L) hQ hR
  refine constant_transfer_zero hQ ?_
  rcases hL.lt_or_eq with hL0 | hL0
  · -- `L > 0`: turning points `0 < y₂ < y₁`, allowed intervals `(0, y₂)` (`K > 0`) and
    -- `(y₁, ∞)` (`K < 0`)
    obtain ⟨y₁, y₂, hy₂, hy₂₁, -, -, -, hS₂, hSm, hS₁, -, -, hd₂, hd₁⟩ :=
      constant_turning_points hQ hω hL0 hKa
    refine eqOn_zero_of_global_current_L (x₁ := y₂) (x₂ := y₁) (s₁ := -1) (s₂ := 1) hy₂ hy₂₁
      (constant_coefficient_contDiffOn hQ e ω L) (fun y hy => (hS₂ y hy).1) hSm
      (fun y hy => (hS₁ y hy).1) hd₂.ne hd₁.ne' hU (Or.inr rfl) (Or.inl rfl)
      (fun y hy => constant_fhat_eq_sign_sqrt (s := 1) (S := Ioo 0 y₂)
        (fun t ht => by rw [sign_pos (hS₂ t ht).2, SignType.coe_one]) hy)
      (fun y hy => (constant_fhat_eq_sign_sqrt (s := -1) (S := Ioi y₁)
        (fun t ht => by rw [sign_neg (hS₁ t ht).2, SignType.coe_neg_one]) hy).trans
          (by rw [neg_neg]))
      (fun y hy => (s2_fhat_props hM hQ hω hL hr₀ hN hy.1 (hS₂ y hy).1).1)
      (fun y hy => (s2_fhat_props hM hQ hω hL hr₀ hN (hy₂.trans (hy₂₁.trans hy))
        (hS₁ y hy).1).1)
      (fun y hy => (s2_fhat_props hM hQ hω hL hr₀ hN hy.1 (hS₂ y hy).1).2)
      (fun y hy => (s2_fhat_props hM hQ hω hL hr₀ hN (hy₂.trans (hy₂₁.trans hy))
        (hS₁ y hy).1).2)
      (Or.inr rfl) (Or.inl rfl) hJI hJH
  · -- `L = 0`: `f̂ = −K` through its simple zero at the corotation point `y₀ = h(e/ω)`
    obtain ⟨y₀, hy₀, hρ₀, -, -⟩ := constant_corotation_sign hQ hω hr₀
    obtain ⟨heq, hprops⟩ := constant_fhat_L0 hM hQ hω hL0.symm hr₀ hN
    refine eqOn_zero_of_global_current_L0 (x₀ := y₀) (σ₁ := -1) (σ₂ := 1) hy₀
      (fun y hy => (hprops y hy).1.contDiffWithinAt) ?_ (fun y hy => (hprops y hy).2.1.ne')
      (fun y hy => div_pos (hprops y hy).2.2 (pow_pos (hprops y hy).2.1 2))
      (Or.inr rfl) (Or.inl rfl) ?_ hJI hJH
    · refine (congrFun heq y₀).trans ?_
      simp only [hρ₀, radialK_corotation_eq_zero e hω.ne', neg_zero]
    · intro y hy
      have hsq := constant_fhat_sq (e := e) (ω := ω) hQ hL hy
        (by rw [← hL0, zero_mul, sub_zero]; exact sq_nonneg _)
      refine ⟨(hU y hy).1, ?_⟩
      rw [hsq]
      exact (hU y hy).2

end ModeStability.AllAngular

end
