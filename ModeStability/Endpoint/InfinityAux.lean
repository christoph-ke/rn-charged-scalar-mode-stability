module

public import ModeStability.Exterior.Calculus
public import ModeStability.Frozen.RadialK

/-!
# Asymptotics of the static solution at infinity

Real-variable asymptotics used for the infinity endpoint limit (2.14)–(2.15) of
the spherical research notes in preparation. As `r → ∞` on the subextremal exterior:

* `g(r) Δ(r) − r → −M` (`tendsto_staticSolution_mul_delta_sub`), the second-order expansion
  `g = r⁻¹ + M r⁻² + O(r⁻³)` of p. 3, derived from the bound
  `|log(1 + y) − y + y²/2| ≤ y³/(1 − y)` (`abs_log_mul_sub_le`);
* `g Δ / r → 1`, `Δ / r² → 1`, `r g → 1`, `g → 0`;
* `(g Δ K' − 2K) / r → −(2Mω − e)` (`tendsto_staticSolution_mul_delta_mul_sub_div`);

and `r(x) → ∞` as `x → ∞` (`tendsto_radiusOf_atTop`).
-/

public section

open Set Filter Topology

namespace ModeStability

namespace Infinity

/-- `Δ(r) = r² − 2Mr + Q²`. -/
theorem delta_eq_poly {M Q : ℝ} (hQ : |Q| < M) (r : ℝ) :
    delta M Q r = r ^ 2 - 2 * M * r + Q ^ 2 := by
  have h : 0 ≤ M ^ 2 - Q ^ 2 := by
    have := sq_lt_sq' (abs_lt.1 hQ).1 (abs_lt.1 hQ).2
    linarith
  unfold delta outerHorizon innerHorizon
  have hs := Real.sq_sqrt h
  linear_combination (-1 : ℝ) * hs

/-- `a > 0` for subextremal parameters. -/
theorem outerHorizon_pos_of_abs_lt {M Q : ℝ} (hQ : |Q| < M) : 0 < outerHorizon M Q := by
  have hM : 0 < M := lt_of_le_of_lt (abs_nonneg Q) hQ
  unfold outerHorizon
  have := Real.sqrt_nonneg (M ^ 2 - Q ^ 2)
  linarith

/-- Second-order Taylor bound for the logarithm, in the form used for `g Δ`:
for `0 < d` and `2d ≤ s`, `|log((s + d)/s) · s(s + d)/d − s − d/2| ≤ 4 d²/s`. -/
theorem abs_log_mul_sub_le {s d : ℝ} (hd : 0 < d) (hs : 2 * d ≤ s) :
    |Real.log ((s + d) / s) * (s * (s + d)) / d - s - d / 2| ≤ 4 * d ^ 2 / s := by
  have hs0 : 0 < s := by linarith
  set y := d / s with hy
  have hy0 : 0 < y := div_pos hd hs0
  have hy1 : y ≤ 1 / 2 := by rw [hy, div_le_iff₀ hs0]; linarith
  have habs : |(-y)| < 1 := by rw [abs_neg, abs_of_pos hy0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_pos hy0] at h
  have hratio : (s + d) / s = 1 - -y := by rw [hy]; field_simp; ring
  rw [hratio]
  set L := Real.log (1 - -y)
  set W := s * (s + d) / d with hW
  have hW0 : 0 < W := by positivity
  have hε : |L - (y - y ^ 2 / 2)| ≤ 2 * y ^ 3 := by
    have h1 : |L - (y - y ^ 2 / 2)| ≤ y ^ 3 / (1 - y) := by
      convert h using 2
      norm_num
      ring
    have h2 : y ^ 3 / (1 - y) ≤ 2 * y ^ 3 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [pow_pos hy0 3]
    exact h1.trans h2
  have hid : L * (s * (s + d)) / d - s - d / 2 = (L - (y - y ^ 2 / 2)) * W - d ^ 2 / (2 * s) := by
    rw [hW, hy]
    field_simp
    ring
  have hyW : 2 * y ^ 3 * W ≤ 3 * d ^ 2 / s := by
    have : 2 * y ^ 3 * W = 2 * d ^ 2 * (s + d) / s ^ 2 := by
      rw [hW, hy]
      field_simp
    rw [this, div_le_div_iff₀ (by positivity) hs0]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg d) hs0.le) (sub_nonneg.2 hs)]
  have hεW : |(L - (y - y ^ 2 / 2)) * W| ≤ 3 * d ^ 2 / s := by
    rw [abs_mul, abs_of_pos hW0]
    calc |L - (y - y ^ 2 / 2)| * W ≤ 2 * y ^ 3 * W := by gcongr
      _ ≤ 3 * d ^ 2 / s := hyW
  have hq0 : 0 ≤ d ^ 2 / (2 * s) := by positivity
  have hq1 : d ^ 2 / (2 * s) ≤ d ^ 2 / s := by
    gcongr
    linarith
  have hsplit : 4 * d ^ 2 / s = 3 * d ^ 2 / s + d ^ 2 / s := by ring
  rw [hid, hsplit]
  calc |(L - (y - y ^ 2 / 2)) * W - d ^ 2 / (2 * s)|
      ≤ |(L - (y - y ^ 2 / 2)) * W| + |d ^ 2 / (2 * s)| := abs_sub _ _
    _ ≤ 3 * d ^ 2 / s + d ^ 2 / s := by
      rw [abs_of_nonneg hq0]
      linarith

/-- `|g(r) Δ(r) − r + M| ≤ 4d²/(r − a)` for `r ≥ a + 2d`. -/
theorem abs_staticSolution_mul_delta_sub_le {M Q : ℝ} (hQ : |Q| < M) {r : ℝ}
    (hr : outerHorizon M Q + 2 * (outerHorizon M Q - innerHorizon M Q) ≤ r) :
    |staticSolution M Q r * delta M Q r - r + M| ≤
      4 * (outerHorizon M Q - innerHorizon M Q) ^ 2 / (r - outerHorizon M Q) := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hM : M = outerHorizon M Q - (outerHorizon M Q - innerHorizon M Q) / 2 := by
    unfold outerHorizon innerHorizon; ring
  unfold staticSolution delta
  set a := outerHorizon M Q
  set b := innerHorizon M Q
  have h := abs_log_mul_sub_le (s := r - a) hd (by linarith)
  have hrb : r - a + (a - b) = r - b := by ring
  rw [hrb] at h
  convert h using 2
  rw [hM]
  field_simp
  ring

/-- The second-order expansion of `g` at infinity: `g(r) Δ(r) − r → −M`. -/
theorem tendsto_staticSolution_mul_delta_sub {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (fun r => staticSolution M Q r * delta M Q r - r) atTop (𝓝 (-M)) := by
  have h0 : Tendsto (fun r => staticSolution M Q r * delta M Q r - r + M) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun r => 4 * (outerHorizon M Q - innerHorizon M Q) ^ 2 /
      (r - outerHorizon M Q)) ?_ ?_
    · filter_upwards [eventually_ge_atTop
        (outerHorizon M Q + 2 * (outerHorizon M Q - innerHorizon M Q))] with r hr
      rw [Real.norm_eq_abs]
      exact abs_staticSolution_mul_delta_sub_le hQ hr
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop (-outerHorizon M Q) fun _ h => h)
  have h1 := h0.sub_const M
  simp only [zero_sub, add_sub_cancel_right] at h1
  exact h1

/-- `g(r) Δ(r) / r → 1`. -/
theorem tendsto_staticSolution_mul_delta_div {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (fun r => staticSolution M Q r * delta M Q r / r) atTop (𝓝 1) := by
  have h := ((tendsto_staticSolution_mul_delta_sub hQ).div_atTop tendsto_id).add_const 1
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  simp only [id]
  field_simp
  ring

/-- `Δ(r) / r² → 1`. -/
theorem tendsto_delta_div_sq {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (fun r => delta M Q r / r ^ 2) atTop (𝓝 1) := by
  have hi := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hi.const_mul (2 * M))).add
    ((hi.pow 2).const_mul (Q ^ 2))
  simp only [mul_zero, sub_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [delta_eq_poly hQ]
  field_simp

/-- `r g(r) → 1`. -/
theorem tendsto_mul_staticSolution {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (fun r => r * staticSolution M Q r) atTop (𝓝 1) := by
  have h := (tendsto_staticSolution_mul_delta_div hQ).div (tendsto_delta_div_sq hQ) one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
  have hr0 : 0 < r := (outerHorizon_pos_of_abs_lt hQ).trans hr
  have hΔ := delta_pos hQ hr
  simp only [Pi.div_apply]
  field_simp

/-- `g(r) → 0`. -/
theorem tendsto_staticSolution {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (staticSolution M Q) atTop (𝓝 0) := by
  refine ((tendsto_mul_staticSolution hQ).div_atTop tendsto_id).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  simp only [id]
  field_simp

/-- `K(r) / r² → ω`. -/
theorem tendsto_radialK_div_sq (e ω : ℝ) :
    Tendsto (fun r => radialK e ω r / r ^ 2) atTop (𝓝 ω) := by
  have h := (tendsto_const_nhds (x := ω)).sub ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul e)
  rw [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  unfold radialK
  field_simp

/-- `(g Δ K' − 2K) / r → −(2Mω − e)`, with `K'(r) = 2ωr − e`. -/
theorem tendsto_staticSolution_mul_delta_mul_sub_div {M Q : ℝ} (hQ : |Q| < M) (e ω : ℝ) :
    Tendsto (fun r => (staticSolution M Q r * delta M Q r * (2 * ω * r - e) -
      2 * radialK e ω r) / r) atTop (𝓝 (-(2 * M * ω - e))) := by
  have h := (((tendsto_staticSolution_mul_delta_sub hQ).const_mul (2 * ω)).sub
    ((tendsto_staticSolution_mul_delta_div hQ).const_mul e)).add_const (2 * e)
  have hlim : 2 * ω * -M - e * 1 + 2 * e = -(2 * M * ω - e) := by ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  unfold radialK
  field_simp
  ring

/-- `r(x) → ∞` as `x → ∞`. -/
theorem tendsto_radiusOf_atTop {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (radiusOf M Q) atTop atTop := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  set d := outerHorizon M Q - innerHorizon M Q
  have h1 : Tendsto (fun x : ℝ => d / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun x : ℝ => Real.exp (d / x) - 1) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((Real.continuous_exp.tendsto 0).comp h1).sub_const 1
      simpa only [Function.comp_apply, Real.exp_zero, sub_self] using this
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact sub_pos.2 (Real.one_lt_exp_iff.2 (div_pos hd hx))
  have h3 := (tendsto_inv_nhdsGT_zero.comp h2).const_mul_atTop hd
  refine (tendsto_atTop_add_const_left atTop (outerHorizon M Q) h3).congr fun x => ?_
  simp only [Function.comp_apply, radiusOf, div_eq_mul_inv]
  rfl

end Infinity

end ModeStability

end
