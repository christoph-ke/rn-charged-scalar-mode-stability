module

public import Mathlib
public import ModeStability.Frozen.TransformedK
public import ModeStability.Section3.Representation
public import ModeStability.Section3.Inequalities

/-!
# The coefficient inequalities of the reciprocal normalization up to the interface `r₀ = 2M`

Source: the all-angular research notes in preparation, p. 3, Lemma 2.2 (case `r₀ ≥ 2M`, with
`g = h`, `x = h⁻¹`), and the spherical research notes in preparation, Section 3 (the
representation (3.2) and the expansion (3.4)).

The landed Section 3 inequalities (`Section3.sec3F1_neg`, `Section3.sec3E_pos`) are stated for
`ν = (r₀ − 2M)/δ > 0`. Their proofs only need `ν ≥ 0`: in (3.5) and (3.4) the `ν`- and
`χ`-free terms are strictly signed, and every other term is a nonnegative multiple of `ν`, `ν²`,
`νχ`, `χ` or `χ²`. We record the `ν ≥ 0` versions and conclude the coefficient inequalities
`k_x > 0`, `2k_x² − k k_xx > 0` for the transformed coefficient `k = transformedK` on `x > 0`
whenever `ω > 0` and `r₀ = qQ/ω ≥ 2M` (in particular at the interface `r₀ = 2M`).
-/

public section

open Set

namespace ModeStability.AllAngular

open Section3

/-- `F'(t) = (t² f)' < 0` for `ν ≥ 0`, `χ ≥ 0`, `t > 0` (the sign form (3.5)). -/
theorem cbe_sec3F1_neg {ν χ t : ℝ} (hν : 0 ≤ ν) (hχ : 0 ≤ χ) (ht : 0 < t) :
    sec3F1 ν χ t < 0 := by
  have hu := one_lt_exp_two_mul ht
  have h1 := exp_two_mul_sub_one_lt ht
  have h2 := exp_two_mul_sub_one_sub_pos ht
  have hu1 : 0 < Real.exp (2 * t) - 1 := sub_pos.2 hu
  have hA : 8 * t * Real.exp (2 * t) * ((Real.exp (2 * t) - 1) - t * (Real.exp (2 * t) + 1)) /
      (Real.exp (2 * t) - 1) ^ 3 < 0 := by
    refine div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (by linarith)) ?_
    positivity
  have hB : 0 ≤ ν * (4 * t * Real.exp (2 * t) * ((Real.exp (2 * t) - 1) - t) /
      (Real.exp (2 * t) - 1) ^ 2) := by
    have : 0 ≤ 4 * t * Real.exp (2 * t) * ((Real.exp (2 * t) - 1) - t) /
        (Real.exp (2 * t) - 1) ^ 2 := by
      have : 0 < (Real.exp (2 * t) - 1) - t := h2
      positivity
    exact mul_nonneg hν this
  have hC : 0 ≤ 2 * χ * t := by positivity
  unfold sec3F1
  rw [two_mul_sec3f_add_eq ν χ ht]
  linarith

/-- `𝓔(t) > 0` for `ν ≥ 0`, `χ ≥ 0`, `t > 0` (the expansion (3.4)). -/
theorem cbe_sec3E_pos {ν χ t : ℝ} (hν : 0 ≤ ν) (hχ : 0 ≤ χ) (ht : 0 < t) :
    0 < sec3E ν χ t := by
  have hu := one_lt_exp_two_mul ht
  have hu1 : 0 < Real.exp (2 * t) - 1 := sub_pos.2 hu
  have hA : 0 < Real.exp (2 * t) - 1 - 2 * t - 2 * t ^ 2 := numA_pos ht
  have hB : 0 < (Real.exp (2 * t) - 1) ^ 2 - t * (Real.exp (2 * t) - 1) -
      t ^ 2 * (Real.exp (2 * t) + 1) := numB_pos ht
  have hC : 0 < (t ^ 2 + t - 1) * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1 := numC_pos ht
  have hD : 0 < (t ^ 2 + t - 1) * Real.exp (2 * t) ^ 2 +
      (4 * t ^ 2 + 2) * Real.exp (2 * t) + t ^ 2 - t - 1 := numD_pos ht
  have hH : 0 < (2 * t ^ 2 - 2 * t + 1) * Real.exp (2 * t) ^ 2 -
      2 * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1 := numH_pos ht
  rw [sec3E_eq ν χ ht]
  have t1 : 0 ≤ 8 * Real.exp (2 * t) ^ 2 * (Real.exp (2 * t) - 1 - 2 * t - 2 * t ^ 2) /
      (Real.exp (2 * t) - 1) ^ 3 * ν ^ 2 := by positivity
  have t2 : 0 ≤ 8 * Real.exp (2 * t) * ((Real.exp (2 * t) - 1) ^ 2 - t * (Real.exp (2 * t) - 1) -
      t ^ 2 * (Real.exp (2 * t) + 1)) / (Real.exp (2 * t) - 1) ^ 3 * (ν * χ) := by
    have : 0 ≤ ν * χ := mul_nonneg hν hχ
    positivity
  have t3 : 0 ≤ 32 * Real.exp (2 * t) ^ 2 *
      ((t ^ 2 + t - 1) * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1) /
        (Real.exp (2 * t) - 1) ^ 4 * ν := by
    have : 0 ≤ 32 * Real.exp (2 * t) ^ 2 *
        ((t ^ 2 + t - 1) * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1) /
          (Real.exp (2 * t) - 1) ^ 4 := by positivity
    exact mul_nonneg this hν
  have t4 : 0 ≤ 2 * χ ^ 2 := by positivity
  have t5 : 0 ≤ 16 * Real.exp (2 * t) * ((t ^ 2 + t - 1) * Real.exp (2 * t) ^ 2 +
      (4 * t ^ 2 + 2) * Real.exp (2 * t) + t ^ 2 - t - 1) / (Real.exp (2 * t) - 1) ^ 4 * χ := by
    positivity
  have t6 : 0 < 32 * Real.exp (2 * t) ^ 2 * ((2 * t ^ 2 - 2 * t + 1) * Real.exp (2 * t) ^ 2 -
      2 * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1) / (Real.exp (2 * t) - 1) ^ 6 := by
    positivity
  linarith

/-- `G' > 0` on `x > 0` for `ω, δ > 0`, `ν, χ ≥ 0`. -/
theorem cbe_sec3G1_pos {ω δ ν χ x : ℝ} (hω : 0 < ω) (hδ : 0 < δ) (hν : 0 ≤ ν) (hχ : 0 ≤ χ)
    (hx : 0 < x) : 0 < sec3G1 ω δ ν χ x := by
  have ht : 0 < δ / x := div_pos hδ hx
  have hF := cbe_sec3F1_neg hν hχ ht
  unfold sec3G1
  have : 0 < -(sec3F1 ν χ (δ / x)) := neg_pos.2 hF
  have h2 : 0 < ω / δ * (-(sec3F1 ν χ (δ / x)) * (δ / x) ^ 2) := by positivity
  linarith

/-- `2G'² − G G'' > 0` on `x > 0` for `ω, δ > 0`, `ν, χ ≥ 0`. -/
theorem cbe_sec3G_two_mul_sq_sub_pos {ω δ ν χ x : ℝ} (hω : 0 < ω) (hδ : 0 < δ) (hν : 0 ≤ ν)
    (hχ : 0 ≤ χ) (hx : 0 < x) :
    0 < 2 * sec3G1 ω δ ν χ x ^ 2 - sec3G ω δ ν χ x * sec3G2 ω δ ν χ x := by
  have ht : 0 < δ / x := div_pos hδ hx
  have hE := cbe_sec3E_pos hν hχ ht
  have hid := sec3_chain_identity (sec3f ν χ (δ / x)) (sec3f1 ν (δ / x)) (sec3f2 ν (δ / x))
    (δ / x)
  have key : 2 * sec3G1 ω δ ν χ x ^ 2 - sec3G ω δ ν χ x * sec3G2 ω δ ν χ x =
      ω ^ 2 / δ ^ 2 * (δ / x) ^ 3 * ((δ / x) ^ 3 * sec3E ν χ (δ / x)) := by
    rw [← sec3E] at hid
    rw [← hid]
    unfold sec3G1 sec3G sec3G2 sec3F1 sec3F2
    field_simp
    ring
  rw [key]
  positivity

/-- The coefficient inequalities for any `k` agreeing with `G` on `x > 0`, for `ν, χ ≥ 0`. -/
theorem cbe_coefficient_inequalities_of_eqOn {k : ℝ → ℝ} {ω δ ν χ : ℝ} (hω : 0 < ω)
    (hδ : 0 < δ) (hν : 0 ≤ ν) (hχ : 0 ≤ χ) (hk : EqOn k (sec3G ω δ ν χ) (Ioi 0)) :
    ContDiffOn ℝ 2 k (Ioi 0) ∧
      ∀ x ∈ Ioi (0 : ℝ), 0 < deriv k x ∧ 0 < 2 * deriv k x ^ 2 - k x * deriv (deriv k) x := by
  refine ⟨(contDiffOn_sec3G ω δ ν χ hδ).congr hk, fun x hx => ?_⟩
  have hx' : 0 < x := hx
  obtain ⟨h1, h2⟩ := deriv_eq_of_eqOn hδ hk hx'
  rw [h1, h2, hk hx]
  exact ⟨cbe_sec3G1_pos hω hδ hν hχ hx', cbe_sec3G_two_mul_sq_sub_pos hω hδ hν hχ hx'⟩

/-- **Coefficient inequalities for `r₀ ≥ 2M`** (reciprocal normalization, including the interface
`r₀ = 2M`): for `ω > 0` and `r₀ = qQ/ω ≥ 2M`, the transformed coefficient `k` is `C²` on
`x > 0` with `k_x > 0` and `2k_x² − k k_xx > 0` there. -/
theorem cbe_coefficient_inequalities {M Q q ω : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    {r₀ : ℝ} (hr₀ : r₀ = q * Q / ω) (h2M : 2 * M ≤ r₀) :
    ContDiffOn ℝ 2 (transformedK M Q q ω) (Ioi 0) ∧
      ∀ x ∈ Ioi (0 : ℝ), 0 < deriv (transformedK M Q q ω) x ∧
        0 < 2 * deriv (transformedK M Q q ω) x ^ 2 -
          transformedK M Q q ω x * deriv (deriv (transformedK M Q q ω)) x := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = Real.sqrt (M ^ 2 - Q ^ 2) := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = (r₀ - 2 * M) / δ := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ, χ = (M / δ - 1) * (M / δ + 1 + ν) := ⟨_, rfl⟩
  have hδpos : 0 < δ := hδ ▸ sqrt_pos_of_abs_lt hQ
  have hνnn : 0 ≤ ν := hν ▸ div_nonneg (sub_nonneg.2 h2M) hδpos.le
  have hμ : 1 ≤ M / δ := (one_le_div hδpos).2 (hδ ▸ sqrt_le_of_abs_lt hM)
  have hχnn : 0 ≤ χ := by
    rw [hχ]
    have h1 : 0 ≤ M / δ - 1 := sub_nonneg.2 hμ
    have h2 : 0 ≤ M / δ + 1 + ν := by linarith
    positivity
  exact cbe_coefficient_inequalities_of_eqOn hω hδpos hνnn hχnn
    (fun x hx => transformedK_eq hQ hω hr₀ hδ hν hχ hx)

end ModeStability.AllAngular

end
