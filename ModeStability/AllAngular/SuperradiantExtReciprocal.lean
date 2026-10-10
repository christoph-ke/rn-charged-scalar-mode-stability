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
import ModeStability.AllAngular.TurningPointGeometry

/-!
# The superradiant band at an extremal horizon, reciprocal normalization

Source: the all-angular research notes in preparation, Sections 2–5, pp. 2–7, in particular the
global identity (5.1)–(5.3)
and its conclusion.

This file treats the superradiant case `ω > 0`, `K(a) < 0` of Theorem 1.1 at an extremal horizon
(`|Q| = M`, so `a = b = M` and `Δ = (r − M)²`) with corotation radius `r₀ = e/ω ≥ 2M`, where the
reciprocal normalization `g = h = 1/(r − M)` is used. The coordinate is `x = r − M ∈ (0, ∞)`
(horizon `x ↓ 0`, infinity `x → ∞`), the amplitude is `U(x) = x R(M + x)`
(`extremal_reciprocal_reduction_L`: `U_xx = −F U` with `F = (K/x²)² − L/x²`), and the effective
phase is `k̂(x) = sgn K(M + x) · x⁻² √(K(M + x)² − Lx²)` (Proposition 3.1,
`extremal_reciprocal_fhat_props`).

* `L > 0`: the turning points `0 < x₁ < x₂` (`extremal_reciprocal_turning_points`), `k̂ = −√F` on
  the horizon side `(0, x₁)` and `k̂ = √F` on the infinity side `(x₂, ∞)`, the endpoint limits of
  the phase-free current (`σ = 1` at the horizon, `σ = −1` at infinity), and
  `eqOn_zero_of_global_current_L`.
* `L = 0`: `k̂ = K/x²` (`extremal_reciprocal_fhat_L0`) vanishes at the corotation point
  `x₀ = e/ω − M`, and `eqOn_zero_of_global_current_L0` applies.

In both cases `U = 0` on `(0, ∞)`, hence `R = 0` on `(a, ∞)`
(`extremal_reciprocal_transfer_zero`).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-! ### Pointwise helpers -/

/-- `L x² < K²` where `F = (K/x²)² − L/x² > 0`, `x > 0`. -/
private theorem s3_lt_of_F_pos {K L x : ℝ} (hx : 0 < x)
    (hF : 0 < (K / x ^ 2) ^ 2 - L / x ^ 2) : L * x ^ 2 < K ^ 2 := by
  have hx0 : x ≠ 0 := hx.ne'
  have h : (K / x ^ 2) ^ 2 - L / x ^ 2 = (K ^ 2 - L * x ^ 2) / x ^ 4 := by
    field_simp
  rw [h] at hF
  have := (div_pos_iff_of_pos_right (pow_pos hx 4)).1 hF
  linarith

/-- `sgn K(M + x) = −1` where `K(M + x) < 0`. -/
private theorem s3_sign_neg {M e ω : ℝ} {S : Set ℝ} (h : ∀ x ∈ S, radialK e ω (M + x) < 0) :
    ∀ x ∈ S, (SignType.sign (radialK e ω (M + x)) : ℝ) = -1 := fun x hx => by
  rw [sign_neg (h x hx), SignType.coe_neg_one]

/-- `sgn K(M + x) = 1` where `K(M + x) > 0`. -/
private theorem s3_sign_pos {M e ω : ℝ} {S : Set ℝ} (h : ∀ x ∈ S, 0 < radialK e ω (M + x)) :
    ∀ x ∈ S, (SignType.sign (radialK e ω (M + x)) : ℝ) = 1 := fun x hx => by
  rw [sign_pos (h x hx), SignType.coe_one]

/-- Proposition 3.1 in the ratio form used by the global identity: where `F > 0`, `k̂_x ≠ 0` and
`(2k̂_x² − k̂k̂_xx)/k̂_x² ≥ 0`. -/
private theorem s3_props {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω)
    (hL : 0 ≤ L) (hr₀ : outerHorizon M Q < e / ω) (hN : 2 * M ≤ e / ω) {x : ℝ} (hx : 0 < x)
    (hF : 0 < (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2) :
    deriv (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x ≠ 0 ∧
      0 ≤ (2 * deriv (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
          Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x ^ 2 -
        (SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
            Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) *
          deriv (deriv fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
            Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x) /
        deriv (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
          Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x ^ 2 := by
  obtain ⟨-, hd, hE⟩ := extremal_reciprocal_fhat_props hM hQ hω hL hr₀ hN hx
    (s3_lt_of_F_pos hx hF)
  exact ⟨hd.ne', div_nonneg hE.le (sq_nonneg _)⟩

/-! ### The superradiant band -/

/-- **The superradiant band at an extremal horizon, reciprocal normalization** (all-angular paper,
Sections 2–5, conclusion after (5.3)): for `M > 0`, `|Q| = M`, `L ≥ 0`, `ω > 0`, `K(a) < 0` and
`2M ≤ e/ω`, a solution of the radial equation `(ΔR')' + (K²/Δ − L)R = 0` with `Θ' = K/Δ`, the
Θ-form horizon condition (1.4) and the Θ-form infinity condition (1.5) vanishes on `(a, ∞)`. -/
theorem superradiant_ext_reciprocal {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| = M)
    (hL : 0 ≤ L) (hω : 0 < ω) (hKa : radialK e ω (outerHorizon M Q) < 0)
    (hN : 2 * M ≤ e / ω)
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
  have hKM : radialK e ω M ≠ 0 := by
    have h := hKa
    rw [outerHorizon_of_abs_eq hQ] at h
    exact h.ne
  have hr₀ : outerHorizon M Q < e / ω := by
    rw [outerHorizon_of_abs_eq hQ]
    linarith
  -- the reduced equation `U_xx = −F U` for `U(x) = x R(M + x)`
  have hU := extremal_reciprocal_reduction_L (e := e) (ω := ω) (L := L) hQ hR
  -- the endpoint limits of the phase-free current (`σ = 1` at `0⁺`, `σ = −1` at `+∞`)
  have hJH := extremal_reciprocal_horizon_current_tendsto_L hQ hL hKM hΘ hR hH1 hH2
  have hJI := extremal_reciprocal_infinity_current_tendsto_L hM hQ hL hω.ne' hΘ hR hI1 hI2
    (k := fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
      Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2))
    (U := fun t : ℝ => (t : ℂ) * R (M + t)) (fun _ _ => rfl) (fun _ _ => rfl)
  refine extremal_reciprocal_transfer_zero hQ ?_
  rcases hL.lt_or_eq with hLpos | hL0
  · -- `L > 0`: the turning points and the middle term of (5.3)
    obtain ⟨x₁, x₂, hx₁, hx₁₂, -, -, -, hS₁, hSm, hS₂, -, -, hd₁, hd₂⟩ :=
      extremal_reciprocal_turning_points hM hQ hω hLpos hKa
    have hf₁ := extremal_reciprocal_fhat_eq_sign_sqrt (L := L) (S := Ioo 0 x₁)
      (s3_sign_neg fun x hx => (hS₁ x hx).2)
    have hf₂ := extremal_reciprocal_fhat_eq_sign_sqrt (L := L) (S := Ioi x₂)
      (s3_sign_pos fun x hx => (hS₂ x hx).2)
    exact eqOn_zero_of_global_current_L (s₁ := -1) (s₂ := 1) (σ₁ := 1) (σ₂ := -1)
      (U := fun t : ℝ => (t : ℂ) * R (M + t))
      (F := fun x => (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2) hx₁ hx₁₂
      (extremal_reciprocal_coefficient_contDiffOn M e ω L) (fun x hx => (hS₁ x hx).1) hSm
      (fun x hx => (hS₂ x hx).1) hd₁.ne hd₂.ne' hU (Or.inr rfl) (Or.inl rfl)
      (fun x hx => hf₁ hx) (fun x hx => hf₂ hx)
      (fun x hx => (s3_props hM hQ hω hL hr₀ hN hx.1 (hS₁ x hx).1).1)
      (fun x hx => (s3_props hM hQ hω hL hr₀ hN (hx₁.trans (hx₁₂.trans hx)) (hS₂ x hx).1).1)
      (fun x hx => (s3_props hM hQ hω hL hr₀ hN hx.1 (hS₁ x hx).1).2)
      (fun x hx => (s3_props hM hQ hω hL hr₀ hN (hx₁.trans (hx₁₂.trans hx)) (hS₂ x hx).1).2)
      (Or.inl rfl) (Or.inr rfl) hJH hJI
  · -- `L = 0`: `k̂ = K/x²` with its simple zero at corotation, and the outer terms of (5.3)
    obtain ⟨heq, hP⟩ := extremal_reciprocal_fhat_L0 hM hQ hω hL0.symm hr₀ hN
    obtain ⟨x₀, hx₀, hρ₀, -, -⟩ := extremal_reciprocal_corotation_sign hQ hω hr₀
    have hf0 : (SignType.sign (radialK e ω (M + x₀)) : ℝ) * (1 / x₀) ^ 2 *
        Real.sqrt (radialK e ω (M + x₀) ^ 2 - L * x₀ ^ 2) = 0 := by
      have h := congrFun heq x₀
      rw [h, hρ₀, radialK_corotation_eq_zero e hω.ne', zero_div]
    have hU0 : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) * R (M + t)) x ∧
        HasDerivAt (deriv fun t : ℝ => (t : ℂ) * R (M + t))
          (-((((SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
              Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2)) ^ 2 : ℝ) : ℂ) *
            ((x : ℂ) * R (M + x))) x := by
      intro x hx
      have hFnn : 0 ≤ (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2 := by
        rw [← hL0, zero_div, sub_zero]
        exact sq_nonneg _
      rw [extremal_reciprocal_fhat_sq hL hFnn]
      exact hU x hx
    exact eqOn_zero_of_global_current_L0 (σ₁ := 1) (σ₂ := -1)
      (f := fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2))
      (U := fun t : ℝ => (t : ℂ) * R (M + t)) hx₀
      (fun x hx => (hP x hx).1.contDiffWithinAt) hf0 (fun x hx => (hP x hx).2.1.ne')
      (fun x hx => div_pos (hP x hx).2.2 (pow_pos (hP x hx).2.1 2)) (Or.inl rfl) (Or.inr rfl)
      hU0 hJH hJI

end ModeStability.AllAngular

end
