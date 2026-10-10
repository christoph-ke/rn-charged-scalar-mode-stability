module

public import Mathlib
public import ModeStability.AllAngular.AngularReduction
public import ModeStability.AllAngular.CoordinateCoefficients
public import ModeStability.AllAngular.CoordinateIntervals
public import ModeStability.AllAngular.GlobalIdentity
public import ModeStability.AllAngular.HorizonLimitsL
public import ModeStability.AllAngular.InfinityLimitsL

/-!
# The superradiant band in the subextremal reciprocal normalization

Source: the all-angular research notes in preparation, Sections 2–5: the transformed equation
(2.4), the signed
effective frequency (3.2) and Proposition 3.1, the endpoint limits (4.4)–(4.5), and the global
identity (5.1)–(5.3) showing that vanishing follows from the interior bulk term for positive
angular momentum and from current rigidity in the spherical case.

Here the case `|Q| < M`, `ω > 0`, `K(a) < 0` and `r₀ = e/ω ≥ 2M` (the reciprocal normalization
`g = h`, `x = 1/h ∈ (0, ∞)`) is assembled. The coordinate is `r(x) = radiusOf M Q x`
(increasing; the horizon is `x → 0⁺`, infinity is `x → ∞`), the amplitude is
`U(x) = x R(r(x))` (`reciprocal_reduction_L`: `U'' = −F U`, `F = (K/x²)² − LΔ/x⁴`), and the
coefficient is `k̂ = sgn(K) x⁻² √(K² − LΔ)`.

* `L > 0`: the turning points `0 < x₁ < x₂` (`reciprocal_turning_points`), `k̂ = −√F` on
  `(0, x₁)` and `k̂ = √F` on `(x₂, ∞)` (`reciprocal_fhat_eq_sign_sqrt`), Proposition 3.1 there
  (`reciprocal_fhat_props`), the horizon limit (`reciprocal_horizon_current_tendsto_L`, σ = 1) and
  the infinity limit (`reciprocal_infinity_current_tendsto_L` for `2Mω − e ≠ 0`,
  `reciprocal_interface_current_tendsto_L` at the interface `2Mω − e = 0`, σ = −1) feed
  `eqOn_zero_of_global_current_L`.
* `L = 0`: `k̂ = K/x²` vanishes at the corotation point `x₀ = x(r₀)`
  (`reciprocal_corotation_sign`), `k̂² = F` (`reciprocal_fhat_sq`), Lemma 2.2 at every point
  (`reciprocal_fhat_L0`), and the same limits feed `eqOn_zero_of_global_current_L0`.

In both cases `U = 0` on `(0, ∞)`, hence `R = 0` on `(a, ∞)` (`reciprocal_transfer_zero`).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-! ### Helpers -/

/-- `K(a) < 0` with `ω > 0` puts the horizon below corotation: `a < e/ω`. -/
private theorem s1_lt_corotation {M Q e ω : ℝ} (hQ : |Q| < M) (hω : 0 < ω)
    (hKa : radialK e ω (outerHorizon M Q) < 0) : outerHorizon M Q < e / ω := by
  have ha0 := outerHorizon_nonneg_of_abs_le hQ.le
  have hK : radialK e ω (outerHorizon M Q) = outerHorizon M Q * (ω * outerHorizon M Q - e) := by
    unfold radialK
    ring
  have h1 : ω * outerHorizon M Q - e < 0 := by
    refine lt_of_not_ge fun h => ?_
    have h2 := mul_nonneg ha0 h
    linarith
  rw [lt_div_iff₀ hω]
  linarith

/-- `(K/x²)² − LD/x⁴ > 0` with `x > 0` gives `LD < K²`. -/
private theorem s1_radicand_pos {K D L x : ℝ} (hx : 0 < x)
    (hF : 0 < (K / x ^ 2) ^ 2 - L * D / x ^ 4) : L * D < K ^ 2 := by
  have h : (K / x ^ 2) ^ 2 - L * D / x ^ 4 = (K ^ 2 - L * D) / x ^ 4 := by
    field_simp
  rw [h] at hF
  have h2 := (div_pos_iff_of_pos_right (pow_pos hx 4)).1 hF
  linarith

/-- From `f' > 0` and `2f'² − ff'' > 0`: `f' ≠ 0` and the ratio form `E_f/f'² > 0`. -/
private theorem s1_ratio {f : ℝ → ℝ} {x : ℝ}
    (h : 0 < deriv f x ∧ 0 < 2 * deriv f x ^ 2 - f x * deriv (deriv f) x) :
    deriv f x ≠ 0 ∧ 0 < (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 :=
  ⟨h.1.ne', div_pos h.2 (pow_pos h.1 2)⟩

/-- The infinity limit of the phase-free current (σ = −1) in the reciprocal normalization, for
both `2Mω − e ≠ 0` and the interface `2Mω − e = 0`. -/
private theorem s1_infinity_current {M Q e ω L : ℝ} (hQ : |Q| < M) (hL : 0 ≤ L) (hω : 0 < ω)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - B) =O[atTop]
      (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹))
    {k : ℝ → ℝ}
    (hk : ∀ x ∈ Ioi (0 : ℝ), k x = (SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) *
      (1 / x) ^ 2 * Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)))
    {U : ℝ → ℂ} (hU : ∀ x ∈ Ioi (0 : ℝ), U x = (x : ℂ) * R (radiusOf M Q x)) :
    Tendsto (fun x => -(k x / deriv k x) *
        ‖deriv U x + ((-1 : ℝ) : ℂ) * (k x : ℂ) * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) atTop (𝓝 0) := by
  by_cases hc : 2 * M * ω - e = 0
  · exact reciprocal_interface_current_tendsto_L hQ hL hω.ne' hc hΘ hR hI1 hI2 hk hU
  · exact reciprocal_infinity_current_tendsto_L hQ hL hω.ne' hc hΘ hR hI1 hI2 hk hU

/-! ### The superradiant band, subextremal reciprocal normalization -/

/-- **The superradiant band in the subextremal reciprocal normalization** (all-angular paper,
Sections 2–5, conclusion after (5.3)). For `M > 0`, `|Q| < M`, `L ≥ 0`, `ω > 0`, `K(a) < 0` and
`2M ≤ e/ω`, a solution `R` of `(ΔR')' + (K²/Δ − L)R = 0` on `r > a` with `Θ' = K/Δ`, the Θ-form
horizon condition (1.4) and the Θ-form outgoing condition (1.5) vanishes on `(a, ∞)`. -/
theorem superradiant_sub_reciprocal {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| < M)
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
  have hr₀ := s1_lt_corotation hQ hω hKa
  have hU := reciprocal_reduction_L (L := L) hQ hR
  have hJ₁ := reciprocal_horizon_current_tendsto_L hQ hL hKa.ne hΘ hR hH1 hH2
  have hJ₂ := s1_infinity_current hQ hL hω hΘ hR hI1 hI2
    (k := fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
      Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t)))
    (U := fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) (fun _ _ => rfl) (fun _ _ => rfl)
  refine reciprocal_transfer_zero hQ ?_
  rcases hL.lt_or_eq with hLp | hL0
  · -- `L > 0`: the forbidden interval `(x₁, x₂)`
    obtain ⟨x₁, x₂, hx₁, hx₁₂, -, -, -, hS₁, hSm, hS₂, -, -, hd₁, hd₂⟩ :=
      reciprocal_turning_points hQ hω hLp hKa
    have hP : ∀ x, 0 < x → 0 < (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
        L * delta M Q (radiusOf M Q x) / x ^ 4 →
        deriv (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
            Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) x ≠ 0 ∧
          0 < (2 * deriv (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) *
              (1 / t) ^ 2 *
              Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) x ^ 2 -
            (SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) * (1 / x) ^ 2 *
                Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)) *
              deriv (deriv fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) *
                (1 / t) ^ 2 *
                Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 -
                  L * delta M Q (radiusOf M Q t))) x) /
            deriv (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
              Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 -
                L * delta M Q (radiusOf M Q t))) x ^ 2 := fun x hx hF =>
      s1_ratio (reciprocal_fhat_props hM hQ hω hL hr₀ hN hx (s1_radicand_pos hx hF)).2
    refine eqOn_zero_of_global_current_L (s₁ := -1) (s₂ := 1) (σ₁ := 1) (σ₂ := -1)
      (f₁ := fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t)))
      (f₂ := fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t)))
      hx₁ hx₁₂ (reciprocal_coefficient_contDiffOn hQ e ω L) (fun x hx => (hS₁ x hx).1) hSm
      (fun x hx => (hS₂ x hx).1) hd₁.ne hd₂.ne' hU (Or.inr rfl) (Or.inl rfl)
      (fun x hx => reciprocal_fhat_eq_sign_sqrt (L := L) (S := Ioo 0 x₁)
        (fun y hy => by rw [sign_neg (hS₁ y hy).2, SignType.coe_neg_one]) hx)
      (fun x hx => reciprocal_fhat_eq_sign_sqrt (L := L) (S := Ioi x₂)
        (fun y hy => by rw [sign_pos (hS₂ y hy).2, SignType.coe_one]) hx)
      (fun x hx => (hP x hx.1 (hS₁ x hx).1).1)
      (fun x hx => (hP x (hx₁.trans (hx₁₂.trans hx)) (hS₂ x hx).1).1)
      (fun x hx => (hP x hx.1 (hS₁ x hx).1).2.le)
      (fun x hx => (hP x (hx₁.trans (hx₁₂.trans hx)) (hS₂ x hx).1).2.le)
      (Or.inl rfl) (Or.inr rfl) hJ₁ hJ₂
  · -- `L = 0`: the corotation point `x₀`
    obtain ⟨heq, hprops⟩ := reciprocal_fhat_L0 hM hQ hω hL0.symm hr₀ hN
    obtain ⟨x₀, hx₀, hρ₀, -, -⟩ := reciprocal_corotation_sign hQ hω hr₀
    have hf0 : (SignType.sign (radialK e ω (radiusOf M Q x₀)) : ℝ) * (1 / x₀) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q x₀) ^ 2 - L * delta M Q (radiusOf M Q x₀)) = 0 := by
      rw [hρ₀, radialK_corotation_eq_zero e hω.ne', sign_zero, SignType.coe_zero, zero_mul,
        zero_mul]
    have hU0 : ∀ x ∈ Ioi (0 : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x ∧
          HasDerivAt (deriv fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))
            (-((((SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) * (1 / x) ^ 2 *
                Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 -
                  L * delta M Q (radiusOf M Q x))) ^ 2 : ℝ) : ℂ) *
              ((x : ℂ) * R (radiusOf M Q x))) x := by
      intro x hx
      have hx0 : (0 : ℝ) < x := hx
      have hFnn : 0 ≤ (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x) / x ^ 4 := by
        rw [← hL0, zero_mul, zero_div, sub_zero]
        positivity
      rw [reciprocal_fhat_sq hQ hL hx0 hFnn]
      exact hU x hx
    exact eqOn_zero_of_global_current_L0 (σ₁ := 1) (σ₂ := -1)
      (f := fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t)))
      hx₀ (fun x hx => (hprops x hx).1.contDiffWithinAt) hf0
      (fun x hx => (s1_ratio (hprops x hx).2).1) (fun x hx => (s1_ratio (hprops x hx).2).2)
      (Or.inl rfl) (Or.inr rfl) hU0 hJ₁ hJ₂

end ModeStability.AllAngular

end
