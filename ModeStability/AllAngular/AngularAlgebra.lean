module

public import Mathlib

/-!
# Proposition 3.1: the pure-algebra part

Real-number algebra behind Proposition 3.1 of
the all-angular research notes in preparation, Section 3. All variables are abstract reals, so
that
the statements apply to both normalizations of the gauge function `g`.

* `mixed_coefficient_eq`: the two forms (3.7) and (3.8) of the mixed coefficient `B` agree,
  where `D = Δ`, `K1 = K'`, `K2 = K''`, `T = ΔK' − zK`, `Δ = z² − δ²`.
* `mixed_coefficient_gt`: (3.9), `B > A₀ + 2T²` when `T² > δ²K²` and `0 ≤ χ ≤ z`.
* `angular_ratio_eq`: the identity relating (3.6)/(3.5)² to the displayed formula for `a_k̂`.
* `angular_ratio_ge_min`: the final step (3.4), `a_k̂ ≥ min{a_k, 2}`.
* `angular_numerator_pos`, `angular_slope_pos`: positivity of the brackets of (3.6) and (3.5).
-/

public section

namespace ModeStability.AllAngular

/-- (3.7) = (3.8): the two forms of the mixed coefficient `B` agree (verified with sympy). Here
`D` is `Δ`, `K1 = K'`, `K2 = K''`, `T = ΔK' − zK`, `A₀ = 2Δ²K'² − 2Δ(χ + z)KK' − Δ²KK'' + 2χ²K²`,
and `Δ = z² − δ²`. -/
theorem mixed_coefficient_eq (D z δ χ K K1 K2 : ℝ) (hD : D = z ^ 2 - δ ^ 2) :
    (2 * D ^ 2 * K1 ^ 2 - 2 * D * (χ + z) * K * K1 - D ^ 2 * K * K2 + 2 * χ ^ 2 * K ^ 2) +
        3 * (D * K1 - z * K) ^ 2 + (2 * χ * (z - χ) - δ ^ 2) * K ^ 2 =
      5 * D ^ 2 * K1 ^ 2 - 2 * D * (χ + 4 * z) * K * K1 - D ^ 2 * K * K2 +
        (D + 2 * χ * z + 2 * z ^ 2) * K ^ 2 := by
  subst hD
  ring

/-- (3.9): `B > A₀ + 2T²` when `T² > δ²K²` and `0 ≤ χ ≤ z`, with
`B = A₀ + 3T² + [2χ(z − χ) − δ²]K²`. -/
theorem mixed_coefficient_gt {A₀ T δ χ z K : ℝ} (hT : δ ^ 2 * K ^ 2 < T ^ 2) (hχ0 : 0 ≤ χ)
    (hχz : χ ≤ z) :
    A₀ + 2 * T ^ 2 < A₀ + 3 * T ^ 2 + (2 * χ * (z - χ) - δ ^ 2) * K ^ 2 := by
  have h : 0 ≤ 2 * χ * (z - χ) * K ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg two_pos.le hχ0) (sub_nonneg.2 hχz)) (sq_nonneg K)
  linarith only [hT, h]

/-- `(uH + vT)² ≤ uH² + vT²` for `u + v = 1`, `u, v ≥ 0` (convexity of the square). -/
theorem sq_convex_comb_le {H T u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    (u * H + v * T) ^ 2 ≤ u * H ^ 2 + v * T ^ 2 := by
  have hu' : u = 1 - v := by linarith only [huv]
  have h : 0 ≤ u * v * (H - T) ^ 2 := mul_nonneg (mul_nonneg hu hv) (sq_nonneg _)
  subst hu'
  nlinarith only [h]

/-- The final step of Proposition 3.1, (3.4): for `u + v = 1`, `u > 0`, `v ≥ 0`,
`(A₀u² + Buv + 3T²v²)/(uH + vT)² ≥ min(A₀/H², 2)` when `A₀, H, T > 0` and `B ≥ A₀ + 2T²`.
(Numerator ≥ A₀u + T²v(2 + v) ≥ min(A₀/H², 2)(H²u + T²v) and (uH + vT)² ≤ uH² + vT².) -/
theorem angular_ratio_ge_min {A₀ B H T u v : ℝ} (hA₀ : 0 < A₀) (hH : 0 < H) (hT : 0 < T)
    (hB : A₀ + 2 * T ^ 2 ≤ B) (hu : 0 < u) (hv : 0 ≤ v) (huv : u + v = 1) :
    min (A₀ / H ^ 2) 2 ≤
      (A₀ * u ^ 2 + B * u * v + 3 * T ^ 2 * v ^ 2) / (u * H + v * T) ^ 2 := by
  set m : ℝ := min (A₀ / H ^ 2) 2 with hm
  have hH2 : 0 < H ^ 2 := pow_pos hH 2
  have hm0 : 0 ≤ m := le_min (div_nonneg hA₀.le hH2.le) zero_le_two
  have hm1 : m * H ^ 2 ≤ A₀ := by
    have : m ≤ A₀ / H ^ 2 := min_le_left _ _
    rwa [le_div_iff₀ hH2] at this
  have hm2 : m ≤ 2 := min_le_right _ _
  have hden : 0 < u * H + v * T := by positivity
  have huvnn : 0 ≤ u * v := mul_nonneg hu.le hv
  -- numerator ≥ `A₀ u + T² v (2 + v)`
  have hnum : A₀ * u + T ^ 2 * (v * (2 + v)) ≤ A₀ * u ^ 2 + B * u * v + 3 * T ^ 2 * v ^ 2 := by
    have h1 : (A₀ + 2 * T ^ 2) * (u * v) ≤ B * (u * v) := mul_le_mul_of_nonneg_right hB huvnn
    have hv' : v = 1 - u := by linarith only [huv]
    subst hv'
    nlinarith only [h1]
  -- `A₀ u + T² v (2 + v) ≥ m (H² u + T² v)`
  have hmid : m * (H ^ 2 * u + T ^ 2 * v) ≤ A₀ * u + T ^ 2 * (v * (2 + v)) := by
    have h1 : m * H ^ 2 * u ≤ A₀ * u := mul_le_mul_of_nonneg_right hm1 hu.le
    have h2 : m * (T ^ 2 * v) ≤ T ^ 2 * (v * (2 + v)) := by
      have h3 : m * v ≤ (2 + v) * v := mul_le_mul_of_nonneg_right (by linarith only [hm2, hv]) hv
      have h4 : T ^ 2 * (m * v) ≤ T ^ 2 * ((2 + v) * v) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg T)
      linarith only [h4]
    linarith only [h1, h2]
  have hconv : (u * H + v * T) ^ 2 ≤ u * H ^ 2 + v * T ^ 2 := sq_convex_comb_le hu.le hv huv
  rw [le_div_iff₀ (pow_pos hden 2)]
  calc m * (u * H + v * T) ^ 2 ≤ m * (u * H ^ 2 + v * T ^ 2) :=
        mul_le_mul_of_nonneg_left hconv hm0
    _ = m * (H ^ 2 * u + T ^ 2 * v) := by ring
    _ ≤ A₀ * u + T ^ 2 * (v * (2 + v)) := hmid
    _ ≤ A₀ * u ^ 2 + B * u * v + 3 * T ^ 2 * v ^ 2 := hnum

/-- Positivity of the numerator of (3.6): `(1 − τ)A₀ + τB + 3T²τ²/(1 − τ) > 0` for `τ ∈ [0, 1)`. -/
theorem angular_numerator_pos {A₀ B T τ : ℝ} (hA₀ : 0 < A₀) (hB : 0 < B) (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) : 0 < (1 - τ) * A₀ + τ * B + 3 * T ^ 2 * τ ^ 2 / (1 - τ) := by
  have h1 : 0 < 1 - τ := sub_pos.2 hτ1
  have h2 : 0 < (1 - τ) * A₀ := mul_pos h1 hA₀
  have h3 : 0 ≤ τ * B := mul_nonneg hτ0 hB.le
  have h4 : 0 ≤ 3 * T ^ 2 * τ ^ 2 / (1 - τ) := by positivity
  linarith only [h2, h3, h4]

/-- Positivity of the bracket of (3.5): `(1 − τ)H + τT > 0` for `τ ∈ [0, 1)`, `H, T > 0`. -/
theorem angular_slope_pos {H T τ : ℝ} (hH : 0 < H) (hT : 0 < T) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    0 < (1 - τ) * H + τ * T := by
  have h1 : 0 < 1 - τ := sub_pos.2 hτ1
  have h2 : 0 < (1 - τ) * H := mul_pos h1 hH
  have h3 : 0 ≤ τ * T := mul_nonneg hτ0 hT.le
  linarith only [h2, h3]

/-- The identity behind the last display of Proposition 3.1: with `u = 1 − τ` and `v = τ`,
`E/k_x² = [(1 − τ)A₀ + τB + 3T²τ²/(1 − τ)] (1 − τ)/[(1 − τ)H + τT]²
  = (A₀u² + Buv + 3T²v²)/(uH + vT)²`
(the factors `g⁸` and `g⁴/√(1 − τ)` of (3.6) and (3.5) cancel to give the factor `1 − τ`). -/
theorem angular_ratio_eq {A₀ B H T τ : ℝ} (hτ : τ ≠ 1) :
    ((1 - τ) * A₀ + τ * B + 3 * T ^ 2 * τ ^ 2 / (1 - τ)) / ((1 - τ) * H + τ * T) ^ 2 * (1 - τ) =
      (A₀ * (1 - τ) ^ 2 + B * (1 - τ) * τ + 3 * T ^ 2 * τ ^ 2) / ((1 - τ) * H + τ * T) ^ 2 := by
  have h1 : (1 - τ) ≠ 0 := sub_ne_zero.2 (Ne.symm hτ)
  field_simp

end ModeStability.AllAngular
