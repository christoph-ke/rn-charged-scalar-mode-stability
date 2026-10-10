module

public import Mathlib

/-!
# Coordinate-free estimates for the large angular parameter

Source: the all-angular research notes in preparation (all-angular paper,
p. 8, proof of Proposition 6.1). Cauchy–Schwarz and the scalar coercivity argument.
-/

public section

open MeasureTheory Complex
open scoped ComplexConjugate

namespace ModeStability.AllAngular

/-- Cauchy–Schwarz for the real part of the source pairing, on any measure space.
Use the restricted measure to obtain the integral over the source interval. -/
theorem largeL_source_cauchy_schwarz {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F U : α → ℂ} (hF : MemLp F 2 μ) (hU : MemLp U 2 μ) :
    -(∫ x, F x * conj (U x) ∂μ).re ≤
      Real.sqrt (∫ x, ‖F x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ‖U x‖ ^ 2 ∂μ) := by
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hF) (by simpa using hU)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
  calc
    -(∫ x, F x * conj (U x) ∂μ).re ≤ ‖∫ x, F x * conj (U x) ∂μ‖ :=
      (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    _ ≤ ∫ x, ‖F x * conj (U x)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖F x‖ * ‖U x‖ ∂μ := by simp only [norm_mul, Complex.norm_conj]
    _ ≤ _ := hh

/-- Scalar form of the large-`L` estimate, with explicit constant
`C(c) = 4 (1 + 1/c)²`. No coordinates or differential equation enter here. -/
theorem largeL_scalar_estimate {B Ux2 U2 F2 c L L₀ : ℝ}
    (hUx : 0 ≤ Ux2) (hU : 0 ≤ U2) (hF : 0 ≤ F2)
    (hc : 0 < c) (hL₀ : 1 ≤ L₀) (hL : L₀ ≤ L)
    (hcoerc : Ux2 + c * L * U2 ≤ B)
    (hcs : B ≤ Real.sqrt F2 * Real.sqrt U2) :
    B + Ux2 + (1 + L) * U2 ≤ (4 * (1 + 1 / c) ^ 2 / (1 + L)) * F2 := by
  have hL1 : 1 ≤ L := hL₀.trans hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hcL : 0 < c * L := mul_pos hc hLp
  have hB : 0 ≤ B := (add_nonneg hUx (mul_nonneg hcL.le hU)).trans hcoerc
  have hUB : c * L * U2 ≤ B := (le_add_of_nonneg_left hUx).trans hcoerc
  have hXB : Ux2 ≤ B :=
    (le_add_of_nonneg_right (mul_nonneg hcL.le hU)).trans hcoerc
  have hsq : B ^ 2 ≤ F2 * U2 := by
    have hs := mul_self_le_mul_self hB hcs
    calc
      B ^ 2 ≤ (Real.sqrt F2 * Real.sqrt U2) ^ 2 := by simpa only [pow_two] using hs
      _ = F2 * U2 := by rw [mul_pow, Real.sq_sqrt hF, Real.sq_sqrt hU]
  have hBF : c * L * B ≤ F2 := by
    by_cases hz : B = 0
    · simp [hz, hF]
    · have hp : 0 < B := lt_of_le_of_ne hB (Ne.symm hz)
      have h₁ := mul_le_mul_of_nonneg_left hsq hcL.le
      have h₂ := mul_le_mul_of_nonneg_left hUB hF
      apply (mul_le_mul_iff_left₀ hp).mp
      calc
        (c * L * B) * B = c * L * B ^ 2 := by ring
        _ ≤ c * L * (F2 * U2) := h₁
        _ = F2 * (c * L * U2) := by ring
        _ ≤ F2 * B := h₂
  have hd : 0 < 1 / c := one_div_pos.mpr hc
  have hBL : L * B ≤ (1 / c) * F2 := by
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hBF
  have hXL : L * Ux2 ≤ (1 / c) * F2 :=
    (mul_le_mul_of_nonneg_left hXB hLp.le).trans hBL
  have hUL : L * U2 ≤ (1 / c) * B := by
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hUB
  have hUL2 : L ^ 2 * U2 ≤ (1 / c) ^ 2 * F2 := by
    have h₁ := mul_le_mul_of_nonneg_left hUL hLp.le
    have h₂ := mul_le_mul_of_nonneg_left hBL hd.le
    nlinarith only [h₁, h₂]
  have ht : 0 ≤ 1 + L := by linarith
  have h₁ : (1 + L) * B ≤ 2 * ((1 / c) * F2) := by
    nlinarith only [hBL, mul_le_mul_of_nonneg_right hL1 hB]
  have h₂ : (1 + L) * Ux2 ≤ 2 * ((1 / c) * F2) := by
    nlinarith only [hXL, mul_le_mul_of_nonneg_right hL1 hUx]
  have h₃ : (1 + L) ^ 2 * U2 ≤ 4 * ((1 / c) ^ 2 * F2) := by
    have hh : (1 + L) ^ 2 ≤ 4 * L ^ 2 := by nlinarith only [hL1]
    have := mul_le_mul_of_nonneg_right hh hU
    nlinarith only [this, hUL2]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1 + L)).mpr
  have hh : 0 ≤ (1 + 1 / c) ^ 2 * F2 := mul_nonneg (sq_nonneg _) hF
  nlinarith only [h₁, h₂, h₃, mul_nonneg hd.le hF, hF]

end ModeStability.AllAngular

end
