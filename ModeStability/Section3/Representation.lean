module

public import Mathlib
public import ModeStability.Exterior.Basic
public import ModeStability.Frozen.TransformedK
public import ModeStability.Section3.Expansion

/-!
# Section 3: the representation (3.2) of `k`

For `x > 0` the transformed coefficient `k(x) = g(r(x))² K(r(x))` of (2.2) is
`ω (δ/x)² f(δ/x)` with `f(t) = csch² t − ν(1 + coth t) − χ` (`sec3f`), where
`δ = √(M² − Q²) = d/2`, `ν = (r₀ − 2M)/δ`, `χ = (μ − 1)(μ + 1 + ν)` and `μ = M/δ`
(the spherical research notes in preparation, (3.1)–(3.2)).
-/

public section

namespace ModeStability.Section3

open ModeStability

/-- `δ = √(M² − Q²) > 0` in the subextremal case. -/
theorem sqrt_pos_of_abs_lt {M Q : ℝ} (hQ : |Q| < M) : 0 < Real.sqrt (M ^ 2 - Q ^ 2) := by
  have h : 0 < M ^ 2 - Q ^ 2 := by
    have := sq_lt_sq' (abs_lt.1 hQ).1 (abs_lt.1 hQ).2
    linarith
  exact Real.sqrt_pos.2 h

/-- `δ ≤ M`, equivalently `μ = M/δ ≥ 1`. -/
theorem sqrt_le_of_abs_lt {M Q : ℝ} (hM : 0 < M) : Real.sqrt (M ^ 2 - Q ^ 2) ≤ M :=
  Real.sqrt_le_iff.2 ⟨hM.le, by nlinarith [sq_nonneg Q]⟩

/-- The representation (3.2): `k(x) = ω (δ/x)² f(δ/x)` for `x > 0`. -/
theorem transformedK_eq {M Q q ω r₀ δ ν χ : ℝ} (hQ : |Q| < M) (hω : 0 < ω)
    (hr₀ : r₀ = q * Q / ω) (hδ : δ = Real.sqrt (M ^ 2 - Q ^ 2))
    (hν : ν = (r₀ - 2 * M) / δ) (hχ : χ = (M / δ - 1) * (M / δ + 1 + ν))
    {x : ℝ} (hx : 0 < x) :
    transformedK M Q q ω x = ω * ((δ / x) ^ 2 * sec3f ν χ (δ / x)) := by
  have hδpos : 0 < δ := hδ ▸ sqrt_pos_of_abs_lt hQ
  have ha : outerHorizon M Q = M + δ := by rw [hδ]; rfl
  have hb : innerHorizon M Q = M - δ := by rw [hδ]; rfl
  have hd : outerHorizon M Q - innerHorizon M Q = 2 * δ := by rw [ha, hb]; ring
  have hqQ : q * Q = ω * r₀ := by rw [hr₀]; field_simp
  have hr₀' : r₀ = 2 * M + ν * δ := by rw [hν]; field_simp; ring
  have hMμ : M = (M / δ) * δ := by field_simp
  have hd2 : 2 * δ / x = 2 * (δ / x) := by ring
  have ht : 0 < δ / x := div_pos hδpos hx
  have hu1 : Real.exp (2 * (δ / x)) - 1 ≠ 0 := exp_two_mul_sub_one_ne_zero ht
  unfold transformedK radialK
  rw [staticSolution_radiusOf hQ hx]
  unfold radiusOf
  rw [hd, ha, hd2, hqQ]
  unfold sec3f
  generalize Real.exp (2 * (δ / x)) = u at hu1 ⊢
  generalize M / δ = μ at hMμ hχ
  rw [hr₀', hMμ, hχ]
  field_simp
  ring

end ModeStability.Section3

end
