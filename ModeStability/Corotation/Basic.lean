module

public import ModeStability.Exterior.Basic
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.TransformedK

/-!
# The corotation radius in band (1.6)

Elementary facts for Proposition 2.3 of the spherical research notes in preparation: in band (1.6)
(`ω > 0`, `r₀ = e/ω > 2M`, `e = qQ`) the corotation radius lies in the exterior, `x₀ = 1/g(r₀)`
is a
zero of `k`, `K(a) < 0` and `2Mω − e < 0`.
-/

public section

open Set

namespace ModeStability

/-- `a ≤ 2M`. -/
theorem outerHorizon_le_two_mul {M Q : ℝ} (hM : 0 < M) : outerHorizon M Q ≤ 2 * M := by
  have : Real.sqrt (M ^ 2 - Q ^ 2) ≤ M :=
    Real.sqrt_le_iff.2 ⟨hM.le, by nlinarith [sq_nonneg Q]⟩
  unfold outerHorizon
  linarith

/-- `a > 0`. -/
theorem outerHorizon_pos {M Q : ℝ} (hM : 0 < M) : 0 < outerHorizon M Q := by
  unfold outerHorizon
  have := Real.sqrt_nonneg (M ^ 2 - Q ^ 2)
  linarith

/-- In band (1.6) the corotation radius lies outside the horizon: `a < r₀`. -/
theorem outerHorizon_lt_of_band {M Q r₀ : ℝ} (hM : 0 < M) (hband : 2 * M < r₀) :
    outerHorizon M Q < r₀ :=
  lt_of_le_of_lt (outerHorizon_le_two_mul hM) hband

/-- `K(r₀) = 0` at the corotation radius `r₀ = qQ/ω`. -/
theorem radialK_corotation {q Q ω r₀ : ℝ} (hω : ω ≠ 0) (hr₀ : r₀ = q * Q / ω) :
    radialK (q * Q) ω r₀ = 0 := by
  unfold radialK
  rw [hr₀]
  field_simp
  ring

/-- In band (1.6), `K(a) < 0`. -/
theorem radialK_outerHorizon_neg {M Q q ω r₀ : ℝ} (hM : 0 < M) (hω : 0 < ω)
    (hr₀ : r₀ = q * Q / ω) (hband : 2 * M < r₀) :
    radialK (q * Q) ω (outerHorizon M Q) < 0 := by
  have ha := outerHorizon_pos (Q := Q) hM
  have har := outerHorizon_lt_of_band (Q := Q) hM hband
  have hqQ : q * Q = ω * r₀ := by rw [hr₀]; field_simp
  unfold radialK
  rw [hqQ]
  have : ω * outerHorizon M Q ^ 2 - ω * r₀ * outerHorizon M Q =
      ω * outerHorizon M Q * (outerHorizon M Q - r₀) := by ring
  rw [this]
  have h1 : 0 < ω * outerHorizon M Q := mul_pos hω ha
  nlinarith

/-- In band (1.6), `2Mω − e < 0`. -/
theorem two_mul_sub_neg_of_band {M q Q ω r₀ : ℝ} (hω : 0 < ω) (hr₀ : r₀ = q * Q / ω)
    (hband : 2 * M < r₀) : 2 * M * ω - q * Q < 0 := by
  have hqQ : q * Q = ω * r₀ := by rw [hr₀]; field_simp
  rw [hqQ]
  nlinarith

/-- `x₀ = 1/g(r₀)` is positive, `r(x₀) = r₀`, and `k(x₀) = 0`. -/
theorem corotation_point {M Q q ω r₀ : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (hr₀ : r₀ = q * Q / ω) (hband : 2 * M < r₀) :
    0 < 1 / staticSolution M Q r₀ ∧ radiusOf M Q (1 / staticSolution M Q r₀) = r₀ ∧
      transformedK M Q q ω (1 / staticSolution M Q r₀) = 0 := by
  have har := outerHorizon_lt_of_band (Q := Q) hM hband
  have hrad := radiusOf_one_div_staticSolution hQ har
  refine ⟨one_div_pos.2 (staticSolution_pos hQ har), hrad, ?_⟩
  unfold transformedK
  rw [hrad, radialK_corotation hω.ne' hr₀, mul_zero]

end ModeStability

end
