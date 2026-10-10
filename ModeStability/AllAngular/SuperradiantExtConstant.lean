module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
import ModeStability.AllAngular.AngularReduction
import ModeStability.AllAngular.CoordinateCoefficientsExtremal
import ModeStability.AllAngular.CoordinateIntervalsExtremal
import ModeStability.AllAngular.ExtremalHorizonLimits
import ModeStability.AllAngular.InfinityLimitsL
import ModeStability.AllAngular.GlobalIdentity

/-!
# The superradiant band in the extremal constant coordinate

Source: the all-angular research notes in preparation, Sections 2–5, in particular the global
identity
(5.1)–(5.3) and its conclusion..

Here `|Q| = M` (so `a = b = M`, `Δ = (r − M)²`) and `a < r₀ = e/ω < 2M`, the constant
normalization `g = 1` with the reflected coordinate `y = h = 1/(r − M) ∈ (0, ∞)`:
`r = M + 1/y` is decreasing, `U(y) = R(M + 1/y)` solves `U_yy = −F U` with
`F(y) = K² − L/y²` at `r = M + 1/y` (`extremal_constant_reduction_L`), and the coefficient is
`f̂(y) = −sgn(K) √F`. Infinity is `y ↓ 0` (σ = −1), the horizon is `y → ∞` (σ = 1).

* `superradiant_ext_constant`: for `ω > 0`, `K(a) < 0` and `e/ω < 2M`, a solution of the radial
  equation with the Θ-form horizon condition (1.4) and infinity condition (1.5) vanishes on the
  exterior. For `L > 0` it is `eqOn_zero_of_global_current_L` with the turning points
  `x₁ = y₂ < x₂ = y₁` of `extremal_constant_turning_points` (`f̂ = −√F` on `(0, y₂)`, where
  `K > 0`, and `f̂ = √F` on `(y₁, ∞)`, where `K < 0`); for `L = 0` it is
  `eqOn_zero_of_global_current_L0` with `f̂ = −K` vanishing at the corotation point `y₀`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-! ### Frequency bookkeeping -/

/-- `K(a) < 0` gives `a < r₀ = e/ω` in the extremal case (`a = M > 0`). -/
private theorem s4_outerHorizon_lt {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω)
    (hKa : radialK e ω (outerHorizon M Q) < 0) : outerHorizon M Q < e / ω := by
  rw [outerHorizon_of_abs_eq hQ, radialK] at hKa
  rw [outerHorizon_of_abs_eq hQ, lt_div_iff₀ hω]
  by_contra h
  have h' : 0 ≤ M * (M * ω - e) := mul_nonneg hM.le (sub_nonneg.2 (not_lt.1 h))
  linarith

/-- `e/ω < 2M` gives `K'(M) = 2ωM − e ≠ 0`. -/
private theorem s4_two_mul_sub_ne {M e ω : ℝ} (hω : 0 < ω) (hN : e / ω < 2 * M) :
    2 * ω * M - e ≠ 0 := by
  rw [div_lt_iff₀ hω] at hN
  linarith

/-! ### The coefficient on the allowed intervals -/

/-- From `f' > 0` and `2f'² − f f'' > 0`: `f' ≠ 0` and `(2f'² − f f'')/f'² > 0`. -/
private theorem s4_ratio {f : ℝ → ℝ} {y : ℝ} (h1 : 0 < deriv f y)
    (h2 : 0 < 2 * deriv f y ^ 2 - f y * deriv (deriv f) y) :
    deriv f y ≠ 0 ∧ 0 < (2 * deriv f y ^ 2 - f y * deriv (deriv f) y) / deriv f y ^ 2 :=
  ⟨h1.ne', div_pos h2 (pow_pos h1 2)⟩

/-- Where `F = K² − L/y² > 0`, the coefficient `f̂ = −sgn(K)√F` has `f̂' ≠ 0` and
`(2f̂'² − f̂f̂'')/f̂'² ≥ 0` (Proposition 3.1, `extremal_constant_fhat_props`). -/
private theorem s4_fhat_outer {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω)
    (hL : 0 ≤ L) (hr₀ : outerHorizon M Q < e / ω) (hN : e / ω < 2 * M) {y : ℝ} (hy : 0 < y)
    (hF : 0 < radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2) :
    deriv (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y ≠ 0 ∧
      0 ≤ (2 * deriv (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
          Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y ^ 2 -
        -((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) *
            Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2)) *
          deriv (deriv fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
            Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y) /
        deriv (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
          Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y ^ 2 := by
  obtain ⟨-, h1, h2⟩ := extremal_constant_fhat_props hM hQ hω hL hr₀ hN hy (sub_pos.1 hF)
  have h := s4_ratio h1 h2
  exact ⟨h.1, h.2.le⟩

/-! ### The superradiant band -/

/-- **The superradiant band, extremal constant coordinate** (Sections 2–5, the global identity
(5.1)–(5.3)). Let `M > 0`, `|Q| = M`, `L ≥ 0`, `ω > 0`, `K(a) < 0` and `e/ω < 2M`. A solution
`R` of `(ΔR')' + (K²/Δ − L)R = 0` on `(a, ∞)` with `Θ' = K/Δ`, the Θ-form horizon condition
(1.4) and the Θ-form infinity condition (1.5) vanishes on `(a, ∞)`. -/
theorem superradiant_ext_constant {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| = M)
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
  have hK0 : radialK e ω M ≠ 0 := by
    rw [outerHorizon_of_abs_eq hQ] at hKa
    exact hKa.ne
  have hr₀ := s4_outerHorizon_lt hM hQ hω hKa
  -- the endpoint limits: infinity `y ↓ 0` (σ = −1), horizon `y → ∞` (σ = 1)
  have hJI := extremal_constant_infinity_current_tendsto_L hQ hL hω.ne' hΘ hR hI1 hI2
    (f := fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
      Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) (fun _ _ => rfl)
    (U := fun t => R (M + 1 / t)) (fun _ _ => rfl)
  have hJH := extremal_constant_horizon_current_tendsto_L hQ hL hK0
    (s4_two_mul_sub_ne hω hN) hΘ hR hH1 hH2
  have hU := extremal_constant_reduction_L hQ hR
  refine extremal_constant_transfer_zero hQ ?_
  rcases hL.lt_or_eq with hL0 | hL0
  · -- `L > 0`: the forbidden interval `(y₂, y₁)`
    obtain ⟨y₁, y₂, hy₂, h₂₁, -, -, -, hF₁, hFm, hF₂, -, -, hd₂, hd₁⟩ :=
      extremal_constant_turning_points hM hQ hω hL0 hKa
    have hs₁ := extremal_constant_fhat_eq_sign_sqrt (L := L) (S := Ioo 0 y₂) (s := 1)
      fun y hy => by rw [sign_pos (hF₁ y hy).2, SignType.coe_one]
    have hs₂ := extremal_constant_fhat_eq_sign_sqrt (L := L) (S := Ioi y₁) (s := -1)
      fun y hy => by rw [sign_neg (hF₂ y hy).2, SignType.coe_neg_one]
    exact eqOn_zero_of_global_current_L (x₁ := y₂) (x₂ := y₁) (s₁ := -1) (s₂ := 1)
      (σ₁ := -1) (σ₂ := 1) (F := fun y => radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2)
      (f₁ := fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2)))
      (f₂ := fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2)))
      (U := fun t => R (M + 1 / t)) hy₂ h₂₁ (extremal_constant_coefficient_contDiffOn M e ω L)
      (fun y hy => (hF₁ y hy).1) hFm (fun y hy => (hF₂ y hy).1) hd₂.ne hd₁.ne' hU
      (Or.inr rfl) (Or.inl rfl) (fun y hy => hs₁ hy)
      (fun y hy => (hs₂ hy).trans (by rw [neg_neg]))
      (fun y hy => (s4_fhat_outer hM hQ hω hL hr₀ hN hy.1 (hF₁ y hy).1).1)
      (fun y hy => (s4_fhat_outer hM hQ hω hL hr₀ hN (hy₂.trans (h₂₁.trans hy))
        (hF₂ y hy).1).1)
      (fun y hy => (s4_fhat_outer hM hQ hω hL hr₀ hN hy.1 (hF₁ y hy).1).2)
      (fun y hy => (s4_fhat_outer hM hQ hω hL hr₀ hN (hy₂.trans (h₂₁.trans hy))
        (hF₂ y hy).1).2)
      (Or.inr rfl) (Or.inl rfl) hJI hJH
  · -- `L = 0`: `f̂ = −K` vanishes at the corotation point `y₀`
    obtain ⟨heq, hP⟩ := extremal_constant_fhat_L0 hM hQ hω hL0.symm hr₀ hN
    obtain ⟨y₀, hy₀, hρ₀, -, -⟩ := extremal_constant_corotation_sign hQ hω hr₀
    have h0 : -radialK e ω (M + 1 / y₀) = 0 := by
      rw [hρ₀, radialK]
      field_simp
      ring
    refine eqOn_zero_of_global_current_L0 (σ₁ := -1) (σ₂ := 1)
      (f := fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2)))
      (U := fun t => R (M + 1 / t)) hy₀ (fun y hy => (hP y hy).1.contDiffWithinAt)
      ((congrFun heq y₀).trans h0) (fun y hy => (s4_ratio (hP y hy).2.1 (hP y hy).2.2).1)
      (fun y hy => (s4_ratio (hP y hy).2.1 (hP y hy).2.2).2) (Or.inr rfl) (Or.inl rfl)
      (fun y hy => ?_) hJI hJH
    have hF : 0 ≤ radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2 := by
      rw [← hL0, zero_div, sub_zero]
      exact sq_nonneg _
    refine ⟨(hU y hy).1, ?_⟩
    rw [extremal_constant_fhat_sq hL hF]
    exact (hU y hy).2

end ModeStability.AllAngular

end
