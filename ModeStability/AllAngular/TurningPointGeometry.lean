module

public import Mathlib
public import ModeStability.AllAngular.Geometry

/-!
# The turning-point geometry (3.1) of the all-angular paper

Source: the all-angular research notes in preparation, p. 4, Section 3, (3.1) and the sentence
after it.

Setting: `M > 0`, `|Q| ≤ M` (subextremal and extremal), `ω > 0`, `e` real, `L > 0`, and the
superradiant condition `K(a) < 0`, which is `a < r₀ = e/ω`. Notation: `a = outerHorizon M Q`,
`Δ = delta M Q`, `K = radialK e ω`, `T = ΔK' − (r − M)K` with `K' = 2ωr − e` (the quantity of
Lemma 2.1, written as in `ModeStability.AllAngular.Geometry` with `ω r₀ = e`), and
`P = K² − LΔ`, so that `P = Δ((K/√Δ)² − L)` on `r > a`. `Δ^{3/2}` is written `Δ √Δ`.

* `T_pos_of_superradiant`: `T > 0` on `r > a` (from `mul_abs_K_lt_T`).
* `hasDerivAt_K_div_sqrt_delta`: (3.1), `(K/√Δ)' = T/(Δ √Δ)` on `r > a`;
  `strictMonoOn_K_div_sqrt_delta`: `K/√Δ` is strictly increasing on `(a, ∞)`.
* `tendsto_K_div_sqrt_delta_nhdsGT`, `tendsto_K_div_sqrt_delta_atTop`: `K/√Δ → −∞` as `r → a⁺`
  and `K/√Δ → +∞` as `r → ∞`.
* `K_div_sqrt_delta_corotation`: `(K/√Δ)(r₀) = 0`, so `r₀` lies strictly between the turning
  points.
* `hasDerivAt_turningPoly`: `P' = 2KK' − 2L(r − M)`; `turningPoly_deriv_eq_of_eq_zero`: at a
  zero `r > a` of `P`, `P'(r) = 2(K/√Δ)(r) T(r)/√Δ(r)`.
* `exists_turning_points`: the two turning points `a < r₁ < r₀ < r₂`, their uniqueness, the sign
  of `P` and `K` on `(a, r₁)`, `(r₁, r₂)`, `(r₂, ∞)`, and the simple-zero facts
  `P'(r₁) = −2√L T(r₁)/√Δ(r₁) < 0`, `P'(r₂) = 2√L T(r₂)/√Δ(r₂) > 0`.
* `hasDerivAt_mul_comp_at_zero`: for a coordinate change `r = ρ(x)` and a factor `c(x)`, the
  function `c(x) P(ρ(x))` has derivative `c(x_j) P'(r_j) ρ'(x_j)` at a point with `P(ρ(x_j)) = 0`.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

/-! ### Elementary facts -/

private theorem tpg_outerHorizon_pos {M Q : ℝ} (hM : 0 < M) : 0 < outerHorizon M Q := by
  unfold outerHorizon
  exact add_pos_of_pos_of_nonneg hM (Real.sqrt_nonneg _)

private theorem tpg_inner_le_outer (M Q : ℝ) : innerHorizon M Q ≤ outerHorizon M Q := by
  unfold innerHorizon outerHorizon
  linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]

private theorem tpg_delta_pos {M Q r : ℝ} (hr : outerHorizon M Q < r) : 0 < delta M Q r := by
  unfold delta
  exact mul_pos (sub_pos.2 hr) (by linarith [tpg_inner_le_outer M Q])

private theorem tpg_sqrt_delta_pos {M Q r : ℝ} (hr : outerHorizon M Q < r) :
    0 < Real.sqrt (delta M Q r) :=
  Real.sqrt_pos.2 (tpg_delta_pos hr)

private theorem tpg_hasDerivAt_delta (M Q r : ℝ) :
    HasDerivAt (fun s => delta M Q s) (2 * (r - M)) r := by
  have h : HasDerivAt (fun s => (s - outerHorizon M Q) * (s - innerHorizon M Q))
      (1 * (r - innerHorizon M Q) + (r - outerHorizon M Q) * 1) r :=
    ((hasDerivAt_id' r).sub_const (outerHorizon M Q)).mul
      ((hasDerivAt_id' r).sub_const (innerHorizon M Q))
  change HasDerivAt (fun s => (s - outerHorizon M Q) * (s - innerHorizon M Q)) _ r
  convert h using 1
  unfold outerHorizon innerHorizon
  ring

private theorem tpg_hasDerivAt_K (e ω r : ℝ) :
    HasDerivAt (fun s => radialK e ω s) (2 * ω * r - e) r := by
  have h : HasDerivAt (fun s => ω * s ^ 2 - e * s) (ω * (2 * r) - e * 1) r := by
    have h2 : HasDerivAt (fun s => s ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    exact (h2.const_mul ω).sub ((hasDerivAt_id' r).const_mul e)
  change HasDerivAt (fun s => ω * s ^ 2 - e * s) _ r
  convert h using 1
  ring

/-- The superradiant condition `K(a) < 0` places the horizon below corotation: `a < e/ω`. -/
theorem outerHorizon_lt_corotation {M Q e ω : ℝ} (hM : 0 < M) (hω : 0 < ω)
    (hK : radialK e ω (outerHorizon M Q) < 0) : outerHorizon M Q < e / ω := by
  have ha := tpg_outerHorizon_pos (Q := Q) hM
  have h : outerHorizon M Q * (ω * outerHorizon M Q - e) < 0 := by
    unfold radialK at hK
    linarith
  have h2 : ω * outerHorizon M Q - e < 0 := by
    by_contra hc
    exact absurd h (not_lt.2 (mul_nonneg ha.le (not_lt.1 hc)))
  rw [lt_div_iff₀ hω]
  linarith

/-- `K(r₀) = 0` at corotation `r₀ = e/ω`. -/
theorem radialK_corotation_eq_zero (e : ℝ) {ω : ℝ} (hω : ω ≠ 0) : radialK e ω (e / ω) = 0 := by
  unfold radialK
  field_simp
  ring

/-- `(K/√Δ)(r₀) = 0` at corotation `r₀ = e/ω`. -/
theorem K_div_sqrt_delta_corotation (M Q e : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    radialK e ω (e / ω) / Real.sqrt (delta M Q (e / ω)) = 0 := by
  rw [radialK_corotation_eq_zero e hω, zero_div]

/-- Lemma 2.1 in the superradiant setting: `T = ΔK' − (r − M)K > 0` on `r > a`. -/
theorem T_pos_of_superradiant {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (hK : radialK e ω (outerHorizon M Q) < 0) {r : ℝ} (hr : outerHorizon M Q < r) :
    0 < delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r := by
  have h := mul_abs_K_lt_T hM hQ hω (outerHorizon_lt_corotation hM hω hK) hr
  have he : ω * (e / ω) = e := by
    field_simp
  rw [he] at h
  have h0 : 0 ≤ Real.sqrt (M ^ 2 - Q ^ 2) * |radialK e ω r| :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  linarith

/-! ### The derivative (3.1) and monotonicity -/

/-- (3.1): `(K/√Δ)' = T/Δ^{3/2}` on `r > a`, with `T = ΔK' − (r − M)K`, `Δ^{3/2} = Δ √Δ`. -/
theorem hasDerivAt_K_div_sqrt_delta {M Q e ω r : ℝ} (hr : outerHorizon M Q < r) :
    HasDerivAt (fun s => radialK e ω s / Real.sqrt (delta M Q s))
      ((delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r) /
        (delta M Q r * Real.sqrt (delta M Q r))) r := by
  have hΔ := tpg_delta_pos hr
  have hs := tpg_sqrt_delta_pos hr
  have h := (tpg_hasDerivAt_K e ω r).div ((tpg_hasDerivAt_delta M Q r).sqrt hΔ.ne') hs.ne'
  convert h using 1
  have hsq : Real.sqrt (delta M Q r) ^ 2 = delta M Q r := Real.sq_sqrt hΔ.le
  set s := Real.sqrt (delta M Q r)
  rw [← hsq]
  field_simp

private theorem tpg_continuousOn {M Q e ω : ℝ} :
    ContinuousOn (fun s => radialK e ω s / Real.sqrt (delta M Q s)) (Ioi (outerHorizon M Q)) :=
  fun _ hr => (hasDerivAt_K_div_sqrt_delta hr).continuousAt.continuousWithinAt

/-- (3.1): `K/√Δ` is strictly increasing on `(a, ∞)`. -/
theorem strictMonoOn_K_div_sqrt_delta {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (hK : radialK e ω (outerHorizon M Q) < 0) :
    StrictMonoOn (fun s => radialK e ω s / Real.sqrt (delta M Q s)) (Ioi (outerHorizon M Q)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi _) tpg_continuousOn fun r hr => ?_
  rw [interior_Ioi] at hr
  rw [(hasDerivAt_K_div_sqrt_delta hr).deriv]
  exact div_pos (T_pos_of_superradiant hM hQ hω hK hr)
    (mul_pos (tpg_delta_pos hr) (tpg_sqrt_delta_pos hr))

/-! ### The endpoint limits -/

/-- `K/√Δ → −∞` as `r → a⁺` when `K(a) < 0` (subextremal or extremal). -/
theorem tendsto_K_div_sqrt_delta_nhdsGT {M Q e ω : ℝ}
    (hK : radialK e ω (outerHorizon M Q) < 0) :
    Tendsto (fun s => radialK e ω s / Real.sqrt (delta M Q s)) (𝓝[>] outerHorizon M Q) atBot := by
  have hKc : Tendsto (fun s => radialK e ω s) (𝓝[>] outerHorizon M Q)
      (𝓝 (radialK e ω (outerHorizon M Q))) :=
    (tpg_hasDerivAt_K e ω _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun s => Real.sqrt (delta M Q s)) (𝓝[>] outerHorizon M Q) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun s => Real.sqrt (delta M Q s)) (outerHorizon M Q) :=
        (tpg_hasDerivAt_delta M Q _).continuousAt.sqrt
      have h0 : Real.sqrt (delta M Q (outerHorizon M Q)) = 0 := by
        simp [delta]
      rw [← h0]
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact tpg_sqrt_delta_pos hr
  have h := hKc.neg_mul_atTop hK (tendsto_inv_nhdsGT_zero.comp hsq)
  simpa only [div_eq_mul_inv, Function.comp_def] using h

/-- `K/√Δ → +∞` as `r → ∞` when `ω > 0`. -/
theorem tendsto_K_div_sqrt_delta_atTop {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω) :
    Tendsto (fun s => radialK e ω s / Real.sqrt (delta M Q s)) atTop atTop := by
  have hlin : Tendsto (fun r => ω * r + -e) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hω)
  refine tendsto_atTop_mono' _ ?_ hlin
  filter_upwards [eventually_gt_atTop (outerHorizon M Q), eventually_gt_atTop (e / ω)]
    with r hra hre
  have ha := tpg_outerHorizon_pos (Q := Q) hM
  have hb := innerHorizon_nonneg hM hQ
  have hab := tpg_inner_le_outer M Q
  have hs := tpg_sqrt_delta_pos hra
  have hlin0 : 0 ≤ ω * r - e := by
    rw [div_lt_iff₀ hω] at hre
    linarith
  have hΔle : delta M Q r ≤ r ^ 2 := by
    unfold delta
    nlinarith
  have hsle : Real.sqrt (delta M Q r) ≤ r := by
    calc Real.sqrt (delta M Q r) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt hΔle
      _ = r := Real.sqrt_sq (by linarith)
  rw [le_div_iff₀ hs]
  have hKr : radialK e ω r = r * (ω * r - e) := by
    unfold radialK
    ring
  rw [hKr]
  nlinarith

/-! ### The turning polynomial `P = K² − LΔ` -/

/-- `P = K² − LΔ` has derivative `P' = 2KK' − 2L(r − M)`. -/
theorem hasDerivAt_turningPoly (M Q e ω L r : ℝ) :
    HasDerivAt (fun s => radialK e ω s ^ 2 - L * delta M Q s)
      (2 * radialK e ω r * (2 * ω * r - e) - L * (2 * (r - M))) r := by
  have h := ((tpg_hasDerivAt_K e ω r).pow 2).sub ((tpg_hasDerivAt_delta M Q r).const_mul L)
  convert h using 1
  simp only [Nat.cast_ofNat]
  ring

/-- `P = Δ((K/√Δ)² − L)` on `r > a`. -/
theorem turningPoly_eq_delta_mul {M Q e ω L r : ℝ} (hr : outerHorizon M Q < r) :
    radialK e ω r ^ 2 - L * delta M Q r =
      delta M Q r * ((radialK e ω r / Real.sqrt (delta M Q r)) ^ 2 - L) := by
  have hΔ := tpg_delta_pos hr
  rw [div_pow, Real.sq_sqrt hΔ.le]
  field_simp

/-- At a zero of `P`: `P'(r) Δ(r) = 2K(r) T(r)`. -/
theorem turningPoly_deriv_mul_delta_of_eq_zero {M Q e ω L r : ℝ}
    (h0 : radialK e ω r ^ 2 - L * delta M Q r = 0) :
    (2 * radialK e ω r * (2 * ω * r - e) - L * (2 * (r - M))) * delta M Q r =
      2 * radialK e ω r * (delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r) := by
  linear_combination (2 * (r - M)) * h0

/-- At a zero `r > a` of `P`: `P'(r) = 2(K/√Δ)(r) T(r)/√Δ(r)`. -/
theorem turningPoly_deriv_eq_of_eq_zero {M Q e ω L r : ℝ} (hr : outerHorizon M Q < r)
    (h0 : radialK e ω r ^ 2 - L * delta M Q r = 0) :
    2 * radialK e ω r * (2 * ω * r - e) - L * (2 * (r - M)) =
      2 * (radialK e ω r / Real.sqrt (delta M Q r)) *
        (delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r) / Real.sqrt (delta M Q r) := by
  have hΔ := tpg_delta_pos hr
  have hs := tpg_sqrt_delta_pos hr
  have h := turningPoly_deriv_mul_delta_of_eq_zero h0
  have hsq : Real.sqrt (delta M Q r) * Real.sqrt (delta M Q r) = delta M Q r :=
    Real.mul_self_sqrt hΔ.le
  have e1 : 2 * (radialK e ω r / Real.sqrt (delta M Q r)) *
      (delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r) =
      2 * radialK e ω r * (delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r) /
        Real.sqrt (delta M Q r) := by
    ring
  rw [eq_div_iff hs.ne', e1, eq_div_iff hs.ne', mul_assoc, hsq]
  exact h

/-! ### The two turning points -/

/-- (3.1) and the sentence after it: for `L > 0` and `K(a) < 0` there are exactly two turning
points `a < r₁ < r₀ = e/ω < r₂`, `K(r₁)/√Δ(r₁) = −√L`, `K(r₂)/√Δ(r₂) = √L`. With
`P = K² − LΔ`: `P > 0` and `K < 0` on `(a, r₁)`, `P < 0` on `(r₁, r₂)`, `P > 0` and `K > 0` on
`(r₂, ∞)`, `P(r₁) = P(r₂) = 0`, and the zeros are simple:
`P'(r₁) = −2√L T(r₁)/√Δ(r₁) < 0`, `P'(r₂) = 2√L T(r₂)/√Δ(r₂) > 0`, where
`P' = 2KK' − 2L(r − M)` is the derivative of `P` (`hasDerivAt_turningPoly`). -/
theorem exists_turning_points {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (hL : 0 < L) (hK : radialK e ω (outerHorizon M Q) < 0) :
    ∃ r₁ r₂ : ℝ, outerHorizon M Q < r₁ ∧ r₁ < e / ω ∧ e / ω < r₂ ∧
      radialK e ω r₁ / Real.sqrt (delta M Q r₁) = -Real.sqrt L ∧
      radialK e ω r₂ / Real.sqrt (delta M Q r₂) = Real.sqrt L ∧
      (∀ s, outerHorizon M Q < s →
        radialK e ω s / Real.sqrt (delta M Q s) = -Real.sqrt L → s = r₁) ∧
      (∀ s, outerHorizon M Q < s →
        radialK e ω s / Real.sqrt (delta M Q s) = Real.sqrt L → s = r₂) ∧
      (∀ r ∈ Ioo (outerHorizon M Q) r₁,
        0 < radialK e ω r ^ 2 - L * delta M Q r ∧ radialK e ω r < 0) ∧
      (∀ r ∈ Ioo r₁ r₂, radialK e ω r ^ 2 - L * delta M Q r < 0) ∧
      (∀ r ∈ Ioi r₂, 0 < radialK e ω r ^ 2 - L * delta M Q r ∧ 0 < radialK e ω r) ∧
      radialK e ω r₁ ^ 2 - L * delta M Q r₁ = 0 ∧
      radialK e ω r₂ ^ 2 - L * delta M Q r₂ = 0 ∧
      radialK e ω r₁ < 0 ∧ 0 < radialK e ω r₂ ∧
      2 * radialK e ω r₁ * (2 * ω * r₁ - e) - L * (2 * (r₁ - M)) =
        -(2 * Real.sqrt L * (delta M Q r₁ * (2 * ω * r₁ - e) - (r₁ - M) * radialK e ω r₁) /
          Real.sqrt (delta M Q r₁)) ∧
      2 * radialK e ω r₂ * (2 * ω * r₂ - e) - L * (2 * (r₂ - M)) =
        2 * Real.sqrt L * (delta M Q r₂ * (2 * ω * r₂ - e) - (r₂ - M) * radialK e ω r₂) /
          Real.sqrt (delta M Q r₂) ∧
      2 * radialK e ω r₁ * (2 * ω * r₁ - e) - L * (2 * (r₁ - M)) < 0 ∧
      0 < 2 * radialK e ω r₂ * (2 * ω * r₂ - e) - L * (2 * (r₂ - M)) := by
  set a := outerHorizon M Q
  set f : ℝ → ℝ := fun s => radialK e ω s / Real.sqrt (delta M Q s)
  have hmono : StrictMonoOn f (Ioi a) := strictMonoOn_K_div_sqrt_delta hM hQ hω hK
  have hcont : ContinuousOn f (Ioi a) := tpg_continuousOn
  have hr₀ : a < e / ω := outerHorizon_lt_corotation hM hω hK
  have hf0 : f (e / ω) = 0 := K_div_sqrt_delta_corotation M Q e hω.ne'
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsL2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
  -- a point `lo ∈ (a, r₀)` with `f lo < −√L`
  obtain ⟨lo, hlo_f, hlo_a, hlo_r⟩ : ∃ lo, f lo < -Real.sqrt L ∧ a < lo ∧ lo < e / ω :=
    (((tendsto_K_div_sqrt_delta_nhdsGT hK).eventually (eventually_lt_atBot (-Real.sqrt L))).and
      ((eventually_mem_nhdsWithin (s := Ioi a)).and
        (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hr₀)))).exists
  -- a point `hi > r₀` with `f hi > √L`
  obtain ⟨hi, hhi_f, hhi_r⟩ : ∃ hi, Real.sqrt L < f hi ∧ e / ω < hi :=
    (((tendsto_K_div_sqrt_delta_atTop hM hQ hω).eventually
      (eventually_gt_atTop (Real.sqrt L))).and (eventually_gt_atTop (e / ω))).exists
  obtain ⟨r₁, ⟨hr₁lo, hr₁r⟩, hr₁f⟩ : ∃ r₁ ∈ Ioo lo (e / ω), f r₁ = -Real.sqrt L :=
    intermediate_value_Ioo hlo_r.le (hcont.mono fun r hr => lt_of_lt_of_le hlo_a hr.1)
      ⟨hlo_f, by rw [hf0]; linarith⟩
  obtain ⟨r₂, ⟨hr₂r, hr₂hi⟩, hr₂f⟩ : ∃ r₂ ∈ Ioo (e / ω) hi, f r₂ = Real.sqrt L :=
    intermediate_value_Ioo hhi_r.le (hcont.mono fun r hr => lt_of_lt_of_le hr₀ hr.1)
      ⟨by rw [hf0]; exact hsL, hhi_f⟩
  have hr₁a : a < r₁ := hlo_a.trans hr₁lo
  have hr₂a : a < r₂ := hr₀.trans hr₂r
  have hr₁₂ : r₁ < r₂ := hr₁r.trans hr₂r
  -- `K = f √Δ`
  have hKf : ∀ r, a < r → radialK e ω r = f r * Real.sqrt (delta M Q r) := fun r hr =>
    (div_mul_cancel₀ _ (tpg_sqrt_delta_pos hr).ne').symm
  have hP : ∀ r, a < r → radialK e ω r ^ 2 - L * delta M Q r = delta M Q r * (f r ^ 2 - L) :=
    fun r hr => turningPoly_eq_delta_mul hr
  have hP₁ : radialK e ω r₁ ^ 2 - L * delta M Q r₁ = 0 := by
    rw [hP r₁ hr₁a, hr₁f, neg_sq, hsL2, sub_self, mul_zero]
  have hP₂ : radialK e ω r₂ ^ 2 - L * delta M Q r₂ = 0 := by
    rw [hP r₂ hr₂a, hr₂f, hsL2, sub_self, mul_zero]
  have hK₁ : radialK e ω r₁ < 0 := by
    rw [hKf r₁ hr₁a, hr₁f]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hsL) (tpg_sqrt_delta_pos hr₁a)
  have hK₂ : 0 < radialK e ω r₂ := by
    rw [hKf r₂ hr₂a, hr₂f]
    exact mul_pos hsL (tpg_sqrt_delta_pos hr₂a)
  have hT₁ := T_pos_of_superradiant hM hQ hω hK hr₁a
  have hT₂ := T_pos_of_superradiant hM hQ hω hK hr₂a
  have hd₁ := turningPoly_deriv_eq_of_eq_zero hr₁a hP₁
  have hd₂ := turningPoly_deriv_eq_of_eq_zero hr₂a hP₂
  have hf₁ : radialK e ω r₁ / Real.sqrt (delta M Q r₁) = -Real.sqrt L := hr₁f
  have hf₂ : radialK e ω r₂ / Real.sqrt (delta M Q r₂) = Real.sqrt L := hr₂f
  rw [hf₁] at hd₁
  rw [hf₂] at hd₂
  have hd₁' : 2 * radialK e ω r₁ * (2 * ω * r₁ - e) - L * (2 * (r₁ - M)) =
      -(2 * Real.sqrt L * (delta M Q r₁ * (2 * ω * r₁ - e) - (r₁ - M) * radialK e ω r₁) /
        Real.sqrt (delta M Q r₁)) := by
    rw [hd₁]
    ring
  refine ⟨r₁, r₂, hr₁a, hr₁r, hr₂r, hf₁, hf₂, ?_, ?_, ?_, ?_, ?_, hP₁, hP₂, hK₁, hK₂, hd₁', hd₂,
    ?_, ?_⟩
  · exact fun s hs hfs => hmono.injOn hs hr₁a (hfs.trans hr₁f.symm)
  · exact fun s hs hfs => hmono.injOn hs hr₂a (hfs.trans hr₂f.symm)
  · rintro r ⟨hra, hr₁⟩
    have hlt : f r < -Real.sqrt L := hr₁f ▸ hmono hra hr₁a hr₁
    have hsq : L < f r ^ 2 := by
      have h2 := pow_lt_pow_left₀ (lt_neg_of_lt_neg hlt) hsL.le two_ne_zero
      rwa [hsL2, neg_sq] at h2
    refine ⟨?_, ?_⟩
    · rw [hP r hra]
      exact mul_pos (tpg_delta_pos hra) (sub_pos.2 hsq)
    · rw [hKf r hra]
      exact mul_neg_of_neg_of_pos (by linarith) (tpg_sqrt_delta_pos hra)
  · rintro r ⟨hr₁, hr₂⟩
    have hra : a < r := hr₁a.trans hr₁
    have hlt₁ : -Real.sqrt L < f r := hr₁f ▸ hmono hr₁a hra hr₁
    have hlt₂ : f r < Real.sqrt L := hr₂f ▸ hmono hra hr₂a hr₂
    have hsq : f r ^ 2 < L := by
      have h2 := sq_lt_sq' hlt₁ hlt₂
      rwa [hsL2] at h2
    rw [hP r hra]
    exact mul_neg_of_pos_of_neg (tpg_delta_pos hra) (sub_neg.2 hsq)
  · intro r hr₂
    have hra : a < r := hr₂a.trans hr₂
    have hlt : Real.sqrt L < f r := hr₂f ▸ hmono hr₂a hra hr₂
    have hsq : L < f r ^ 2 := by
      have h2 := pow_lt_pow_left₀ hlt hsL.le two_ne_zero
      rwa [hsL2] at h2
    refine ⟨?_, ?_⟩
    · rw [hP r hra]
      exact mul_pos (tpg_delta_pos hra) (sub_pos.2 hsq)
    · rw [hKf r hra]
      exact mul_pos (by linarith) (tpg_sqrt_delta_pos hra)
  · rw [hd₁']
    exact neg_neg_of_pos (div_pos (mul_pos (mul_pos two_pos hsL) hT₁)
      (tpg_sqrt_delta_pos hr₁a))
  · rw [hd₂]
    exact div_pos (mul_pos (mul_pos two_pos hsL) hT₂) (tpg_sqrt_delta_pos hr₂a)

/-! ### Transport through a coordinate change -/

/-- For a coordinate change `r = ρ(x)` and a factor `c(x)`, `F(x) = c(x) P(ρ(x))` has
derivative `c(x_j) P'(ρ(x_j)) ρ'(x_j)` at a point `x_j` with `P(ρ(x_j)) = 0`. -/
theorem hasDerivAt_mul_comp_at_zero {c ρ P : ℝ → ℝ} {x c' ρ' p : ℝ} (hc : HasDerivAt c c' x)
    (hρ : HasDerivAt ρ ρ' x) (hP : HasDerivAt P p (ρ x)) (h0 : P (ρ x) = 0) :
    HasDerivAt (fun y => c y * P (ρ y)) (c x * (p * ρ')) x := by
  have h := hc.mul (hP.comp x hρ)
  simp only [Function.comp_def, h0, mul_zero, zero_add] at h
  exact h

/-- Sign transport: if `c(x_j) > 0` and `P'(r_j) ρ'(x_j) > 0`, then `F'(x_j) > 0`. -/
theorem deriv_mul_comp_pos_at_zero {c ρ P : ℝ → ℝ} {x c' ρ' p : ℝ} (hc : HasDerivAt c c' x)
    (hρ : HasDerivAt ρ ρ' x) (hP : HasDerivAt P p (ρ x)) (h0 : P (ρ x) = 0) (hcx : 0 < c x)
    (hpρ : 0 < p * ρ') : 0 < deriv (fun y => c y * P (ρ y)) x := by
  rw [(hasDerivAt_mul_comp_at_zero hc hρ hP h0).deriv]
  exact mul_pos hcx hpρ

/-- Sign transport: if `c(x_j) > 0` and `P'(r_j) ρ'(x_j) < 0`, then `F'(x_j) < 0`. -/
theorem deriv_mul_comp_neg_at_zero {c ρ P : ℝ → ℝ} {x c' ρ' p : ℝ} (hc : HasDerivAt c c' x)
    (hρ : HasDerivAt ρ ρ' x) (hP : HasDerivAt P p (ρ x)) (h0 : P (ρ x) = 0) (hcx : 0 < c x)
    (hpρ : p * ρ' < 0) : deriv (fun y => c y * P (ρ y)) x < 0 := by
  rw [(hasDerivAt_mul_comp_at_zero hc hρ hP h0).deriv]
  exact mul_neg_of_pos_of_neg hcx hpρ

end ModeStability.AllAngular

end
