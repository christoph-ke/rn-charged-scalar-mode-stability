module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.StaticSolution
public import ModeStability.Exterior.Basic
public import ModeStability.Section3.Numerators

/-!
# Lemma 2.1 (common geometry) of the all-angular paper

Source: the all-angular research notes in preparation, p. 3, Lemma 2.1, with the notation (1.1)
(`a`, `b`, `Δ`, `δ = √(M² − Q²)`), `K = ωr² − er`, `e = ωr₀`, and `T = ΔK' − zK`, `z = r − M`,
`K' = ω(2r − r₀)`, as in (2.1)–(2.5).

* `T_sub_mul_K_eq`, `T_add_mul_K_eq`: the exact factorizations (2.9) and (2.10).
* `mul_abs_K_lt_T`: the first claim `T > δ|K|` for `r₀ > a`, `r > a`.
* `chi_bounds`: the bounds (2.8) in the subextremal case `δ > 0`, with `χ = 1/g(r)` and
  `ε = z − χ`: `0 < ε < δ`, `ε(δ + χ) < δ²`, `0 < χ < z`.

For `δ > 0` write `t = δ g(r) > 0`; then `e^{2t} = (r − b)/(r − a)`, `z = δ coth t`, `χ = δ/t`.
The inequality `ε > 0` is `t coth t > 1`, and `ε(δ + χ) < δ²` is equivalent to
`e^{2t} > 1 + 2t + 2t²`. Both are landed in `ModeStability.Section3`.
-/

public section

open Set

namespace ModeStability.AllAngular

/-! ### Elementary facts on `δ = √(M² − Q²)` -/

/-- `(√(M² − Q²))² = M² − Q²` for `|Q| ≤ M`. -/
theorem sq_sqrt_sub_sq {M Q : ℝ} (hQ : |Q| ≤ M) :
    Real.sqrt (M ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - Q ^ 2 := by
  have h := sq_le_sq' (abs_le.1 hQ).1 (abs_le.1 hQ).2
  exact Real.sq_sqrt (by linarith)

/-- The inner horizon is nonnegative: `0 ≤ b = M − √(M² − Q²)`. -/
theorem innerHorizon_nonneg {M Q : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) :
    0 ≤ innerHorizon M Q := by
  unfold innerHorizon
  have hsq := sq_sqrt_sub_sq hQ
  have : Real.sqrt (M ^ 2 - Q ^ 2) ≤ M := by
    nlinarith [sq_nonneg Q, Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
  linarith

/-! ### The exact factorizations (2.9), (2.10) -/

/-- (2.9): `T − δK = ω(r − b)[(r − a)² + a(r₀ − a)]` with `T = ΔK' − zK`, `K = ωr² − er`,
`e = ωr₀`. -/
theorem T_sub_mul_K_eq (M Q ω r₀ r : ℝ) :
    delta M Q r * (2 * ω * r - ω * r₀) - (r - M) * radialK (ω * r₀) ω r -
        Real.sqrt (M ^ 2 - Q ^ 2) * radialK (ω * r₀) ω r =
      ω * (r - innerHorizon M Q) * ((r - outerHorizon M Q) ^ 2 +
        outerHorizon M Q * (r₀ - outerHorizon M Q)) := by
  unfold delta radialK outerHorizon innerHorizon
  ring

/-- (2.10): `T + δK = ω(r − a)[(r − b)² + b(r₀ − b)]`. -/
theorem T_add_mul_K_eq (M Q ω r₀ r : ℝ) :
    delta M Q r * (2 * ω * r - ω * r₀) - (r - M) * radialK (ω * r₀) ω r +
        Real.sqrt (M ^ 2 - Q ^ 2) * radialK (ω * r₀) ω r =
      ω * (r - outerHorizon M Q) * ((r - innerHorizon M Q) ^ 2 +
        innerHorizon M Q * (r₀ - innerHorizon M Q)) := by
  unfold delta radialK outerHorizon innerHorizon
  ring

/-- Lemma 2.1, first claim: `T > δ|K|` for `r₀ > a`, `r > a`, `ω > 0`. -/
theorem mul_abs_K_lt_T {M Q ω r₀ : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (hr₀ : outerHorizon M Q < r₀) {r : ℝ} (hr : outerHorizon M Q < r) :
    Real.sqrt (M ^ 2 - Q ^ 2) * |radialK (ω * r₀) ω r| <
      delta M Q r * (2 * ω * r - ω * r₀) - (r - M) * radialK (ω * r₀) ω r := by
  have hδ0 : 0 ≤ Real.sqrt (M ^ 2 - Q ^ 2) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ innerHorizon M Q := innerHorizon_nonneg hM hQ
  have hab : innerHorizon M Q ≤ outerHorizon M Q := by
    unfold innerHorizon outerHorizon
    linarith
  have ha0 : 0 < outerHorizon M Q := by
    unfold outerHorizon
    linarith
  have hra : 0 < r - outerHorizon M Q := sub_pos.2 hr
  have hrb : 0 < r - innerHorizon M Q := by linarith
  have p1 : 0 < ω * (r - innerHorizon M Q) * ((r - outerHorizon M Q) ^ 2 +
      outerHorizon M Q * (r₀ - outerHorizon M Q)) :=
    mul_pos (mul_pos hω hrb) (add_pos (pow_pos hra 2) (mul_pos ha0 (sub_pos.2 hr₀)))
  have p2 : 0 < ω * (r - outerHorizon M Q) * ((r - innerHorizon M Q) ^ 2 +
      innerHorizon M Q * (r₀ - innerHorizon M Q)) :=
    mul_pos (mul_pos hω hra) (add_pos_of_pos_of_nonneg (pow_pos hrb 2)
      (mul_nonneg hb0 (by linarith)))
  have h1 := T_sub_mul_K_eq M Q ω r₀ r
  have h2 := T_add_mul_K_eq M Q ω r₀ r
  rcases abs_cases (radialK (ω * r₀) ω r) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    linarith
  · rw [h]
    linarith

/-! ### The bounds (2.8) -/

/-- The core of (2.8) in the variables `δ`, `t = δ/χ`, `u = e^{2t}`, `z = δ coth t`:
with `χ = δ/t` one has `0 < z − χ < δ`, `(z − χ)(δ + χ) < δ²`, `0 < χ < z`. -/
theorem chi_aux {δ t u z : ℝ} (hδ : 0 < δ) (ht : 0 < t) (hu : u = Real.exp (2 * t))
    (hz : z = δ * (u + 1) / (u - 1)) :
    0 < z - δ / t ∧ z - δ / t < δ ∧ (z - δ / t) * (δ + δ / t) < δ ^ 2 ∧
      0 < δ / t ∧ δ / t < z := by
  subst hz
  have hu1 : 1 < u := hu ▸ Section3.one_lt_exp_two_mul ht
  have hu1' : 0 < u - 1 := sub_pos.2 hu1
  have hB : u - 1 < t * (u + 1) := hu ▸ Section3.exp_two_mul_sub_one_lt ht
  have hA : 0 < u - 1 - 2 * t - 2 * t ^ 2 := by
    have := Section3.numA_pos ht
    unfold Section3.numA at this
    rwa [← hu] at this
  have ht' : 0 < (u - 1) * t := mul_pos hu1' ht
  have hε : 0 < δ * (u + 1) / (u - 1) - δ / t := by
    have e : δ * (u + 1) / (u - 1) - δ / t = δ * (t * (u + 1) - (u - 1)) / ((u - 1) * t) := by
      field_simp
    rw [e]
    exact div_pos (mul_pos hδ (sub_pos.2 hB)) ht'
  refine ⟨hε, ?_, ?_, div_pos hδ ht, by linarith⟩
  · have e : δ * (u + 1) / (u - 1) - δ / t - δ = -(δ * (u - 1 - 2 * t)) / ((u - 1) * t) := by
      field_simp
      ring
    have : δ * (u + 1) / (u - 1) - δ / t - δ < 0 := by
      rw [e]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hδ (by nlinarith))) ht'
    linarith
  · have e : δ ^ 2 - (δ * (u + 1) / (u - 1) - δ / t) * (δ + δ / t) =
        δ ^ 2 * (u - 1 - 2 * t - 2 * t ^ 2) / ((u - 1) * t ^ 2) := by
      field_simp
      ring
    have : 0 < δ ^ 2 - (δ * (u + 1) / (u - 1) - δ / t) * (δ + δ / t) := by
      rw [e]
      exact div_pos (mul_pos (pow_pos hδ 2) hA) (mul_pos hu1' (pow_pos ht 2))
    linarith

/-- The core of (2.8) in terms of `g = h` and `z`: with `z = δ coth(δ g)`, `ε = z − 1/g`,
`χ = 1/g`. -/
theorem chi_bounds_core {δ g z : ℝ} (hδ : 0 < δ) (hg : 0 < g)
    (hz : z = δ * (Real.exp (2 * (δ * g)) + 1) / (Real.exp (2 * (δ * g)) - 1)) :
    0 < z - 1 / g ∧ z - 1 / g < δ ∧ (z - 1 / g) * (δ + 1 / g) < δ ^ 2 ∧
      0 < 1 / g ∧ 1 / g < z := by
  have hdiv : δ / (δ * g) = 1 / g := by
    field_simp
  have h := chi_aux hδ (mul_pos hδ hg) rfl hz
  rwa [hdiv] at h

/-- Lemma 2.1, (2.8), subextremal case: with `χ = 1/h(r)` (`h = staticSolution`, which is
`(2δ)⁻¹ log((r − b)/(r − a))` since `a − b = 2δ`) and `ε = z − χ`, `z = r − M`:
`0 < ε < δ`, `ε(δ + χ) < δ²`, `0 < χ < z`. -/
theorem chi_bounds {M Q : ℝ} (hQ : |Q| < M) {r : ℝ} (hr : outerHorizon M Q < r) :
    0 < (r - M) - 1 / staticSolution M Q r ∧
      (r - M) - 1 / staticSolution M Q r < Real.sqrt (M ^ 2 - Q ^ 2) ∧
      ((r - M) - 1 / staticSolution M Q r) *
          (Real.sqrt (M ^ 2 - Q ^ 2) + 1 / staticSolution M Q r) < M ^ 2 - Q ^ 2 ∧
      0 < 1 / staticSolution M Q r ∧ 1 / staticSolution M Q r < r - M := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hd2 : outerHorizon M Q - innerHorizon M Q = 2 * Real.sqrt (M ^ 2 - Q ^ 2) := by
    unfold outerHorizon innerHorizon
    ring
  have hδ : 0 < Real.sqrt (M ^ 2 - Q ^ 2) := by linarith
  have hg := staticSolution_pos hQ hr
  have hra : 0 < r - outerHorizon M Q := sub_pos.2 hr
  have hrb : 0 < r - innerHorizon M Q := by
    have : innerHorizon M Q < outerHorizon M Q := by linarith
    linarith
  have hexp : Real.exp (2 * (Real.sqrt (M ^ 2 - Q ^ 2) * staticSolution M Q r)) =
      (r - innerHorizon M Q) / (r - outerHorizon M Q) := by
    have h2 : 2 * (Real.sqrt (M ^ 2 - Q ^ 2) * staticSolution M Q r) =
        Real.log ((r - innerHorizon M Q) / (r - outerHorizon M Q)) := by
      unfold staticSolution
      rw [hd2]
      field_simp
    rw [h2, Real.exp_log (div_pos hrb hra)]
  have hz : r - M = Real.sqrt (M ^ 2 - Q ^ 2) *
      (Real.exp (2 * (Real.sqrt (M ^ 2 - Q ^ 2) * staticSolution M Q r)) + 1) /
      (Real.exp (2 * (Real.sqrt (M ^ 2 - Q ^ 2) * staticSolution M Q r)) - 1) := by
    rw [hexp]
    have h1 : r - innerHorizon M Q = (r - outerHorizon M Q) + 2 * Real.sqrt (M ^ 2 - Q ^ 2) := by
      linarith
    have h2 : r - M = (r - outerHorizon M Q) + Real.sqrt (M ^ 2 - Q ^ 2) := by
      unfold outerHorizon
      ring
    rw [h1, h2]
    field_simp
    ring
  obtain ⟨h1, h2, h3, h4, h5⟩ := chi_bounds_core hδ hg hz
  exact ⟨h1, h2, lt_of_lt_of_eq h3 (sq_sqrt_sub_sq hQ.le), h4, h5⟩

end ModeStability.AllAngular

end
