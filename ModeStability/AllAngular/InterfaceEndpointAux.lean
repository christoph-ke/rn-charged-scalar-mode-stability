module

public import ModeStability.Endpoint.InfinityAux

/-!
# Third-order asymptotics of the static solution at the interface `r₀ = 2M`

Real-variable asymptotics for the interface case of the infinity endpoint limit:
the all-angular research notes in preparation, p. 6, (4.5), in the reciprocal normalization
`x = 1/g` of the spherical research notes in preparation, (2.2). At `c = 2Mω − e = 0` the
leading term `−c r` of `g Δ K' − 2K` vanishes (compare
`Infinity.tendsto_staticSolution_mul_delta_mul_sub_div`), and the limit of `g Δ K' − 2K` is
governed by the third-order term of `g` at infinity. With `d = a − b`, as `r → ∞`:

* `|g Δ − r + M + d²/(6(r − a))| ≤ 4d³/(r − a)²` for `r ≥ a + 2d`
  (`iface_abs_staticSolution_mul_delta_sub_le`), from the third-order bound
  `|log(1 + y) − y + y²/2 − y³/3| ≤ y⁴/(1 − y)` (`iface_abs_log_mul_sub_le`);
* `(r − M)(g Δ − r + M) → −d²/6` (`iface_tendsto_mul_staticSolution_mul_delta_sub`);
* for `e = 2Mω`: `g Δ K' − 2K → 2ω(M² + 2Q²)/3`
  (`iface_tendsto_staticSolution_mul_delta_mul_sub`),
  the coefficient `2D`, `D = ω(M² + 2Q²)/3`, of (4.5) for `L = 0`.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

/-- Third-order Taylor bound for the logarithm, in the form used for `g Δ`:
for `0 < d` and `2d ≤ s`, `|log((s + d)/s) · s(s + d)/d − s − d/2 + d²/(6s)| ≤ 4 d³/s²`. -/
theorem iface_abs_log_mul_sub_le {s d : ℝ} (hd : 0 < d) (hs : 2 * d ≤ s) :
    |Real.log ((s + d) / s) * (s * (s + d)) / d - s - d / 2 + d ^ 2 / (6 * s)| ≤
      4 * d ^ 3 / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  set y := d / s with hy
  have hy0 : 0 < y := div_pos hd hs0
  have hy1 : y ≤ 1 / 2 := by rw [hy, div_le_iff₀ hs0]; linarith
  have habs : |(-y)| < 1 := by rw [abs_neg, abs_of_pos hy0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_pos hy0] at h
  have hratio : (s + d) / s = 1 - -y := by rw [hy]; field_simp; ring
  rw [hratio]
  set L := Real.log (1 - -y)
  set W := s * (s + d) / d with hW
  have hW0 : 0 < W := by positivity
  have hε : |L - (y - y ^ 2 / 2 + y ^ 3 / 3)| ≤ 2 * y ^ 4 := by
    have h1 : |L - (y - y ^ 2 / 2 + y ^ 3 / 3)| ≤ y ^ 4 / (1 - y) := by
      convert h using 2
      norm_num
      ring
    have h2 : y ^ 4 / (1 - y) ≤ 2 * y ^ 4 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [pow_pos hy0 4]
    exact h1.trans h2
  have hid : L * (s * (s + d)) / d - s - d / 2 + d ^ 2 / (6 * s) =
      (L - (y - y ^ 2 / 2 + y ^ 3 / 3)) * W + d ^ 3 / (3 * s ^ 2) := by
    rw [hW, hy]
    field_simp
    ring
  have hyW : 2 * y ^ 4 * W ≤ 3 * d ^ 3 / s ^ 2 := by
    have : 2 * y ^ 4 * W = 2 * d ^ 3 * (s + d) / s ^ 3 := by
      rw [hW, hy]
      field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (pow_pos hd 3).le (sq_nonneg s)) (sub_nonneg.2 hs)]
  have hεW : |(L - (y - y ^ 2 / 2 + y ^ 3 / 3)) * W| ≤ 3 * d ^ 3 / s ^ 2 := by
    rw [abs_mul, abs_of_pos hW0]
    calc |L - (y - y ^ 2 / 2 + y ^ 3 / 3)| * W ≤ 2 * y ^ 4 * W := by gcongr
      _ ≤ 3 * d ^ 3 / s ^ 2 := hyW
  have hq0 : 0 ≤ d ^ 3 / (3 * s ^ 2) := by positivity
  have hq1 : d ^ 3 / (3 * s ^ 2) ≤ d ^ 3 / s ^ 2 := by
    gcongr
    linarith [sq_nonneg s]
  have hsplit : 4 * d ^ 3 / s ^ 2 = 3 * d ^ 3 / s ^ 2 + d ^ 3 / s ^ 2 := by ring
  rw [hid, hsplit]
  calc |(L - (y - y ^ 2 / 2 + y ^ 3 / 3)) * W + d ^ 3 / (3 * s ^ 2)|
      ≤ |(L - (y - y ^ 2 / 2 + y ^ 3 / 3)) * W| + |d ^ 3 / (3 * s ^ 2)| := abs_add_le _ _
    _ ≤ 3 * d ^ 3 / s ^ 2 + d ^ 3 / s ^ 2 := by
      rw [abs_of_nonneg hq0]
      linarith

/-- The third-order expansion of `g Δ` at infinity:
`|g(r) Δ(r) − r + M + d²/(6(r − a))| ≤ 4d³/(r − a)²` for `r ≥ a + 2d`, `d = a − b`. -/
theorem iface_abs_staticSolution_mul_delta_sub_le {M Q : ℝ} (hQ : |Q| < M) {r : ℝ}
    (hr : outerHorizon M Q + 2 * (outerHorizon M Q - innerHorizon M Q) ≤ r) :
    |staticSolution M Q r * delta M Q r - r + M +
        (outerHorizon M Q - innerHorizon M Q) ^ 2 / (6 * (r - outerHorizon M Q))| ≤
      4 * (outerHorizon M Q - innerHorizon M Q) ^ 3 / (r - outerHorizon M Q) ^ 2 := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hM : M = outerHorizon M Q - (outerHorizon M Q - innerHorizon M Q) / 2 := by
    unfold outerHorizon innerHorizon; ring
  unfold staticSolution delta
  set a := outerHorizon M Q
  set b := innerHorizon M Q
  have hra : 0 < r - a := by linarith
  have h := iface_abs_log_mul_sub_le (s := r - a) hd (by linarith)
  have hrb : r - a + (a - b) = r - b := by ring
  rw [hrb] at h
  convert h using 2
  rw [hM]
  field_simp
  ring

/-- `(r − M)(g(r) Δ(r) − r + M) → −d²/6` as `r → ∞`, `d = a − b`. -/
theorem iface_tendsto_mul_staticSolution_mul_delta_sub {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (fun r => (r - M) * (staticSolution M Q r * delta M Q r - r + M)) atTop
      (𝓝 (-((outerHorizon M Q - innerHorizon M Q) ^ 2 / 6))) := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hs : Tendsto (fun r : ℝ => r - outerHorizon M Q) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-outerHorizon M Q) fun _ h => h
  have hE : Tendsto (fun r => (r - outerHorizon M Q) * (staticSolution M Q r * delta M Q r - r + M +
      (outerHorizon M Q - innerHorizon M Q) ^ 2 / (6 * (r - outerHorizon M Q)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun r => 4 * (outerHorizon M Q - innerHorizon M Q) ^ 3 /
      (r - outerHorizon M Q)) ?_ (tendsto_const_nhds.div_atTop hs)
    filter_upwards [eventually_ge_atTop
      (outerHorizon M Q + 2 * (outerHorizon M Q - innerHorizon M Q))] with r hr
    have hra : 0 < r - outerHorizon M Q := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hra]
    calc (r - outerHorizon M Q) * |staticSolution M Q r * delta M Q r - r + M +
          (outerHorizon M Q - innerHorizon M Q) ^ 2 / (6 * (r - outerHorizon M Q))|
        ≤ (r - outerHorizon M Q) * (4 * (outerHorizon M Q - innerHorizon M Q) ^ 3 /
          (r - outerHorizon M Q) ^ 2) := by
          gcongr
          exact iface_abs_staticSolution_mul_delta_sub_le hQ hr
      _ = 4 * (outerHorizon M Q - innerHorizon M Q) ^ 3 / (r - outerHorizon M Q) := by
          field_simp
  have hq : Tendsto (fun r => (r - M) / (r - outerHorizon M Q)) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := outerHorizon M Q - M)).div_atTop hs).const_add 1
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
    have hra : r - outerHorizon M Q ≠ 0 := (sub_pos.2 hr).ne'
    field_simp
    ring
  have h := hq.mul (hE.sub_const ((outerHorizon M Q - innerHorizon M Q) ^ 2 / 6))
  rw [one_mul, zero_sub] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
  have hra : r - outerHorizon M Q ≠ 0 := (sub_pos.2 hr).ne'
  field_simp
  ring

/-- At the interface `2Mω = e` (`r₀ = 2M`): `g Δ K' − 2K → 2ω(M² + 2Q²)/3` as `r → ∞`,
with `K'(r) = 2ωr − e`. -/
theorem iface_tendsto_staticSolution_mul_delta_mul_sub {M Q : ℝ} (hQ : |Q| < M) {e ω : ℝ}
    (he : 2 * M * ω - e = 0) :
    Tendsto (fun r => staticSolution M Q r * delta M Q r * (2 * ω * r - e) - 2 * radialK e ω r)
      atTop (𝓝 (2 * ω * ((M ^ 2 + 2 * Q ^ 2) / 3))) := by
  have h := ((iface_tendsto_mul_staticSolution_mul_delta_sub hQ).add_const (M ^ 2)).const_mul
    (2 * ω)
  have hlim : -((outerHorizon M Q - innerHorizon M Q) ^ 2 / 6) + M ^ 2 =
      (M ^ 2 + 2 * Q ^ 2) / 3 := by
    have h0 : 0 ≤ M ^ 2 - Q ^ 2 := by
      have := sq_lt_sq' (abs_lt.1 hQ).1 (abs_lt.1 hQ).2
      linarith
    have hs := Real.sq_sqrt h0
    unfold outerHorizon innerHorizon
    linear_combination (-2 / 3 : ℝ) * hs
  rw [hlim] at h
  have he' : e = 2 * M * ω := by linarith
  subst he'
  refine h.congr fun r => ?_
  unfold radialK
  ring

end ModeStability.AllAngular

end
