module

public import Mathlib

/-!
# The turning points (4.6) of the all-angular paper

Section 4 of the all-angular research notes in preparation (p. 6, turning-point geometry): at a
simple angular turning point `x_j`, the angular frequency `k̂` of (3.2) satisfies
`k̂/k̂_x = 2(x − x_j) + O((x − x_j)²)`, and, since `U` and `U_x` extend smoothly through `x_j`,
the
current (4.2) tends from the allowed side to `−Re(U_x Ū)(x_j)`.

The statements are abstract. In the paper `k̂² = F := k² − V = g⁴(K² − LΔ)` and `x_j` is a simple
zero of `F`. Here `F : ℝ → ℝ` is any function that is `C²` near `x_j` with `F(x_j) = 0` and
`F'(x_j) ≠ 0`, and on the allowed side (where `F > 0`) `k̂ = s√F` with a fixed sign `s = ±1`.
Then `k̂_x = sF'/(2√F)`, so `k̂/k̂_x = 2F/F' → 0`.

* `tendsto_khat_div_deriv_right`, `tendsto_khat_div_deriv_left`: `k̂/k̂_x → 0` from the allowed
  side
  (the right side when `F'(x_j) > 0`, the left side when `F'(x_j) < 0`).
* `tendsto_current_at_turning_point_right`, `tendsto_current_at_turning_point_left`: for `U` that
  is `C¹` near `x_j` and any real `σ` (in the paper `σ = ±1`),
  `−(k̂/k̂_x)|U_x + iσk̂U|² − Re(U_x Ū) → −Re(U_x Ū)(x_j)` from the allowed side.
* `khat_div_deriv_sub_isBigO_right`, `khat_div_deriv_sub_isBigO_left`: the sharper first claim of
  (4.6), `k̂/k̂_x − 2(x − x_j) = O((x − x_j)²)` from the allowed side.
* `tendsto_khat_E_div_sq_right`, `tendsto_khat_E_div_sq_left`: the second claim of (4.6),
  `E_k̂/k̂_x² → 3` with `E_k̂ = 2k̂_x² − k̂k̂_xx`; pointwise `E_k̂/k̂_x² = 3 − 2FF''/F'²`
  (`khat_E_div_sq_eq`).

The filters `𝓝[>] x_j` and `𝓝[<] x_j` do not presuppose positivity of `F`: from `F(x_j) = 0` and
the sign of `F'(x_j)`, `F > 0` just on the allowed side (`eventually_pos_right_of_deriv_pos`,
`eventually_pos_left_of_deriv_neg`). Only `C¹` regularity of `F` is used for the two limits
`k̂/k̂_x → 0` and the current limit; `C²` enters the `O`-form and `E_k̂/k̂_x² → 3`.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

/-- Near a point where `F` is `C¹`, `F` has derivative `deriv F x` at every nearby `x`. -/
private theorem tp_eventually_hasDerivAt {F : ℝ → ℝ} {xj : ℝ} (hF : ContDiffAt ℝ 1 F xj) :
    ∀ᶠ x in 𝓝 xj, HasDerivAt F (deriv F x) x :=
  (hF.eventually (by simp)).mono fun _ hy => hy.differentiableAt_one.hasDerivAt

/-- If `F` is `C¹` at `x_j`, then `F'` is continuous at `x_j`. -/
private theorem tp_continuousAt_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ → E} {xj : ℝ} (hG : ContDiffAt ℝ 1 G xj) : ContinuousAt (deriv G) xj :=
  (hG.derivWithin (m := 0) (by simp)).continuousAt

/-- Right of a simple zero with `F'(x_j) > 0`, the function `F` is positive. -/
theorem eventually_pos_right_of_deriv_pos {F : ℝ → ℝ} {xj F' : ℝ} (hd : HasDerivAt F F' xj)
    (hF0 : F xj = 0) (hF1 : 0 < F') : ∀ᶠ x in 𝓝[>] xj, 0 < F x := by
  have h := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono xj fun y (hy : xj < y) => ne_of_gt hy)
  filter_upwards [h.eventually (lt_mem_nhds hF1), self_mem_nhdsWithin] with x hx hxj
  rw [slope_def_field, hF0, sub_zero] at hx
  exact (div_pos_iff_of_pos_right (sub_pos.mpr hxj)).mp hx

/-- Left of a simple zero with `F'(x_j) < 0`, the function `F` is positive. -/
theorem eventually_pos_left_of_deriv_neg {F : ℝ → ℝ} {xj F' : ℝ} (hd : HasDerivAt F F' xj)
    (hF0 : F xj = 0) (hF1 : F' < 0) : ∀ᶠ x in 𝓝[<] xj, 0 < F x := by
  have h := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono xj fun y (hy : y < xj) => ne_of_lt hy)
  filter_upwards [h.eventually (gt_mem_nhds hF1), self_mem_nhdsWithin] with x hx hxj
  rw [slope_def_field, hF0, sub_zero] at hx
  have hne : x - xj ≠ 0 := sub_ne_zero.mpr (ne_of_lt hxj)
  have h2 : F x = F x / (x - xj) * (x - xj) := (div_mul_cancel₀ (F x) hne).symm
  rw [h2]
  exact mul_pos_of_neg_of_neg hx (sub_neg.mpr hxj)

/-- Where `F > 0` and `F` is differentiable, `k̂/k̂_x = 2F/F'` for `k̂ = s√F`, `s ≠ 0`. -/
theorem khat_div_deriv_eq {F : ℝ → ℝ} {s x : ℝ} (hs : s ≠ 0) (hd : HasDerivAt F (deriv F x) x)
    (hx : 0 < F x) :
    (s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x = 2 * F x / deriv F x := by
  rw [((hd.sqrt hx.ne').const_mul s).deriv]
  have hsq : 0 < Real.sqrt (F x) := Real.sqrt_pos.mpr hx
  have hsq2 : Real.sqrt (F x) ^ 2 = F x := Real.sq_sqrt hx.le
  by_cases hd0 : deriv F x = 0
  · simp [hd0]
  · field_simp
    exact hsq2

/-- The limit `k̂/k̂_x → 0` along any filter `l ≤ 𝓝 x_j` on which `F > 0` eventually. -/
private theorem tendsto_khat_div_deriv_of {F : ℝ → ℝ} {xj s : ℝ} {l : Filter ℝ} (hl : l ≤ 𝓝 xj)
    (hs : s ≠ 0) (hF : ContDiffAt ℝ 1 F xj) (hF0 : F xj = 0) (hF1 : deriv F xj ≠ 0)
    (hpos : ∀ᶠ x in l, 0 < F x) :
    Tendsto (fun x => (s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x) l (𝓝 0) := by
  have hFt : Tendsto F l (𝓝 0) := hF0 ▸ hF.continuousAt.tendsto.mono_left hl
  have hdt : Tendsto (deriv F) l (𝓝 (deriv F xj)) :=
    (tp_continuousAt_deriv hF).tendsto.mono_left hl
  have hlim : Tendsto (fun x => 2 * F x / deriv F x) l (𝓝 0) := by
    have h := (hFt.const_mul 2).div hdt hF1
    rw [mul_zero, zero_div] at h
    exact h
  refine hlim.congr' ?_
  filter_upwards [hpos, hl (tp_eventually_hasDerivAt hF)] with x hx hd
  exact (khat_div_deriv_eq hs hd hx).symm

/-- The current limit along any filter `l ≤ 𝓝 x_j` on which `F > 0` eventually. -/
private theorem tendsto_current_of {F : ℝ → ℝ} {xj s σ : ℝ} {l : Filter ℝ} (hl : l ≤ 𝓝 xj)
    (hs : s ≠ 0) (hF : ContDiffAt ℝ 1 F xj) (hF0 : F xj = 0) (hF1 : deriv F xj ≠ 0)
    (hpos : ∀ᶠ x in l, 0 < F x) {U : ℝ → ℂ} (hU : ContDiffAt ℝ 1 U xj) :
    Tendsto (fun x => -((s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x) *
          ‖deriv U x + σ * (s * Real.sqrt (F x)) * I * U x‖ ^ 2 -
            (deriv U x * (starRingEnd ℂ) (U x)).re)
      l (𝓝 (-(deriv U xj * (starRingEnd ℂ) (U xj)).re)) := by
  have hUt : Tendsto U l (𝓝 (U xj)) := hU.continuousAt.tendsto.mono_left hl
  have hU't : Tendsto (deriv U) l (𝓝 (deriv U xj)) :=
    (tp_continuousAt_deriv hU).tendsto.mono_left hl
  have hFt : Tendsto (fun x => Real.sqrt (F x)) l (𝓝 (Real.sqrt (F xj))) :=
    ((Real.continuous_sqrt.tendsto _).comp hF.continuousAt.tendsto).mono_left hl
  have hG : Continuous fun p : ℂ × ℝ × ℂ => ‖p.1 + σ * (s * p.2.1) * I * p.2.2‖ ^ 2 := by
    fun_prop
  have hH : Continuous fun p : ℂ × ℂ => (p.1 * (starRingEnd ℂ) p.2).re := by
    fun_prop
  have hnorm := (hG.tendsto _).comp (hU't.prodMk_nhds (hFt.prodMk_nhds hUt))
  have hre := (hH.tendsto _).comp (hU't.prodMk_nhds hUt)
  have hk := tendsto_khat_div_deriv_of hl hs hF hF0 hF1 hpos
  have h := (hk.neg.mul hnorm).sub hre
  rw [neg_zero, zero_mul, zero_sub] at h
  exact h

private theorem tp_ne_zero {s : ℝ} (hs : s = 1 ∨ s = -1) : s ≠ 0 := by
  rcases hs with rfl | rfl <;> norm_num

/-- (4.6), first claim, weak form: `k̂/k̂_x → 0` at a simple turning point from the allowed side,
here the right side (`F'(x_j) > 0`, so `F > 0` on `(x_j, x_j + ε)`). On that side
`k̂_x = sF'/(2√F)`, so `k̂/k̂_x = 2F/F'`. -/
theorem tendsto_khat_div_deriv_right {F : ℝ → ℝ} {xj s : ℝ} (hs : s = 1 ∨ s = -1)
    (hF : ContDiffAt ℝ 2 F xj) (hF0 : F xj = 0) (hF1 : 0 < deriv F xj) :
    Tendsto (fun x => (s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x)
      (𝓝[>] xj) (𝓝 0) :=
  have hF' : ContDiffAt ℝ 1 F xj := hF.of_le (by norm_num)
  tendsto_khat_div_deriv_of nhdsWithin_le_nhds (tp_ne_zero hs) hF' hF0 hF1.ne'
    (eventually_pos_right_of_deriv_pos hF'.differentiableAt_one.hasDerivAt hF0 hF1)

/-- (4.6), first claim, weak form, mirror version: `k̂/k̂_x → 0` from the left side when
`F'(x_j) < 0` (so `F > 0` on `(x_j − ε, x_j)`). -/
theorem tendsto_khat_div_deriv_left {F : ℝ → ℝ} {xj s : ℝ} (hs : s = 1 ∨ s = -1)
    (hF : ContDiffAt ℝ 2 F xj) (hF0 : F xj = 0) (hF1 : deriv F xj < 0) :
    Tendsto (fun x => (s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x)
      (𝓝[<] xj) (𝓝 0) :=
  have hF' : ContDiffAt ℝ 1 F xj := hF.of_le (by norm_num)
  tendsto_khat_div_deriv_of nhdsWithin_le_nhds (tp_ne_zero hs) hF' hF0 hF1.ne
    (eventually_pos_left_of_deriv_neg hF'.differentiableAt_one.hasDerivAt hF0 hF1)

/-- The current (4.2), `−(k̂/k̂_x)|U_x + iσk̂U|² − Re(U_x Ū)`, tends to `−Re(U_x Ū)(x_j)` at a
simple turning point from the allowed (right) side, for `U` that is `C¹` near `x_j`. -/
theorem tendsto_current_at_turning_point_right {F : ℝ → ℝ} {xj s σ : ℝ} (hs : s = 1 ∨ s = -1)
    (hF : ContDiffAt ℝ 2 F xj) (hF0 : F xj = 0) (hF1 : 0 < deriv F xj)
    {U : ℝ → ℂ} (hU : ContDiffAt ℝ 1 U xj) :
    Tendsto (fun x => -((s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x) *
          ‖deriv U x + σ * (s * Real.sqrt (F x)) * I * U x‖ ^ 2 -
            (deriv U x * (starRingEnd ℂ) (U x)).re)
      (𝓝[>] xj) (𝓝 (-(deriv U xj * (starRingEnd ℂ) (U xj)).re)) :=
  have hF' : ContDiffAt ℝ 1 F xj := hF.of_le (by norm_num)
  tendsto_current_of nhdsWithin_le_nhds (tp_ne_zero hs) hF' hF0 hF1.ne'
    (eventually_pos_right_of_deriv_pos hF'.differentiableAt_one.hasDerivAt hF0 hF1) hU

/-- Mirror version of `tendsto_current_at_turning_point_right`: the current tends to
`−Re(U_x Ū)(x_j)` from the allowed (left) side when `F'(x_j) < 0`. -/
theorem tendsto_current_at_turning_point_left {F : ℝ → ℝ} {xj s σ : ℝ} (hs : s = 1 ∨ s = -1)
    (hF : ContDiffAt ℝ 2 F xj) (hF0 : F xj = 0) (hF1 : deriv F xj < 0)
    {U : ℝ → ℂ} (hU : ContDiffAt ℝ 1 U xj) :
    Tendsto (fun x => -((s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x) *
          ‖deriv U x + σ * (s * Real.sqrt (F x)) * I * U x‖ ^ 2 -
            (deriv U x * (starRingEnd ℂ) (U x)).re)
      (𝓝[<] xj) (𝓝 (-(deriv U xj * (starRingEnd ℂ) (U xj)).re)) :=
  have hF' : ContDiffAt ℝ 1 F xj := hF.of_le (by norm_num)
  tendsto_current_of nhdsWithin_le_nhds (tp_ne_zero hs) hF' hF0 hF1.ne
    (eventually_pos_left_of_deriv_neg hF'.differentiableAt_one.hasDerivAt hF0 hF1) hU

/-! ### The sharper form of (4.6) and the limit `E_k̂/k̂_x² → 3` -/

/-- Taylor bound at a point where `F` is `C²`:
`F(x) − F(x_j) − F'(x_j)(x − x_j) = O((x − x_j)²)`. -/
private theorem tp_taylor_isBigO {F : ℝ → ℝ} {xj : ℝ} (hF : ContDiffAt ℝ 2 F xj) :
    (fun x => F x - F xj - deriv F xj * (x - xj)) =O[𝓝 xj] fun x => (x - xj) ^ 2 := by
  have hd1 := tp_eventually_hasDerivAt (hF.of_le (by norm_num))
  have hF2 : ContDiffAt ℝ 1 (deriv F) xj := hF.derivWithin (m := 1) (by norm_num)
  obtain ⟨C, hCpos, hC⟩ := hF2.differentiableAt_one.hasDerivAt.isBigO_sub.exists_pos
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hd1.and hC.bound)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Metric.ball_mem_nhds xj hδ] with x hx
  have hsub : uIcc xj x ⊆ Metric.ball xj δ :=
    (convex_ball xj δ).ordConnected.uIcc_subset (Metric.mem_ball_self hδ) hx
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y => F y - deriv F xj * (y - xj)) (f' := fun y => deriv F y - deriv F xj)
    (C := C * |x - xj|) (s := uIcc xj x) (x := xj) (y := x) ?_ ?_ (convex_uIcc xj x)
    left_mem_uIcc right_mem_uIcc
  · have he : F x - deriv F xj * (x - xj) - (F xj - deriv F xj * (xj - xj)) =
        F x - F xj - deriv F xj * (x - xj) := by ring
    rw [he] at key
    calc ‖F x - F xj - deriv F xj * (x - xj)‖ ≤ C * |x - xj| * ‖x - xj‖ := key
      _ = C * ‖(x - xj) ^ 2‖ := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]; ring
  · intro y hy
    have h := (hball y (hsub hy)).1.sub (((hasDerivAt_id' y).sub_const xj).const_mul (deriv F xj))
    convert h.hasDerivWithinAt using 1
    ring
  · intro y hy
    calc ‖deriv F y - deriv F xj‖ ≤ C * ‖y - xj‖ := (hball y (hsub hy)).2
      _ ≤ C * |x - xj| := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hy) hCpos.le

/-- The sharper form `k̂/k̂_x = 2(x − x_j) + O((x − x_j)²)` along any filter `l ≤ 𝓝 x_j` on which
`F > 0` eventually. -/
private theorem khat_div_deriv_sub_isBigO_of {F : ℝ → ℝ} {xj s : ℝ} {l : Filter ℝ}
    (hl : l ≤ 𝓝 xj) (hs : s ≠ 0) (hF : ContDiffAt ℝ 2 F xj) (hF0 : F xj = 0)
    (hF1 : deriv F xj ≠ 0) (hpos : ∀ᶠ x in l, 0 < F x) :
    (fun x => (s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x - 2 * (x - xj))
      =O[l] fun x => (x - xj) ^ 2 := by
  have hF' : ContDiffAt ℝ 1 F xj := hF.of_le (by norm_num)
  have hF2 : ContDiffAt ℝ 1 (deriv F) xj := hF.derivWithin (m := 1) (by norm_num)
  have h1 := tp_taylor_isBigO hF
  have h2 : (fun x => (x - xj) * (deriv F x - deriv F xj)) =O[𝓝 xj] fun x => (x - xj) ^ 2 := by
    have h := (Asymptotics.isBigO_refl (fun x => x - xj) (𝓝 xj)).mul
      hF2.differentiableAt_one.hasDerivAt.isBigO_sub
    simpa only [sq] using h
  have h3 : (fun x => (deriv F x)⁻¹) =O[𝓝 xj] fun _ => (1 : ℝ) :=
    ((tp_continuousAt_deriv hF').tendsto.inv₀ hF1).isBigO_one ℝ
  have h4 := ((h1.sub h2).const_mul_left 2).mul h3
  refine (h4.mono hl).congr' ?_ (Eventually.of_forall fun x => mul_one _)
  filter_upwards [hpos, hl (tp_eventually_hasDerivAt hF'),
    hl ((tp_continuousAt_deriv hF').eventually_ne hF1)] with x hx hd hne
  rw [khat_div_deriv_eq hs hd hx, hF0]
  field_simp
  ring

/-- Where `F > 0` and `F` is differentiable near `x`, and `F'` is differentiable at `x` with
`F'(x) ≠ 0`: `E_k̂/k̂_x² = 3 − 2FF''/F'²` for `k̂ = s√F`, `s ≠ 0`. -/
theorem khat_E_div_sq_eq {F : ℝ → ℝ} {s x : ℝ} (hs : s ≠ 0)
    (hev : ∀ᶠ y in 𝓝 x, 0 < F y ∧ HasDerivAt F (deriv F y) y)
    (hd2 : HasDerivAt (deriv F) (deriv (deriv F) x) x) (hne : deriv F x ≠ 0) :
    (2 * deriv (fun y => s * Real.sqrt (F y)) x ^ 2 -
        s * Real.sqrt (F x) * deriv (deriv (fun y => s * Real.sqrt (F y))) x) /
        deriv (fun y => s * Real.sqrt (F y)) x ^ 2 =
      3 - 2 * F x * deriv (deriv F) x / deriv F x ^ 2 := by
  obtain ⟨hx, hd⟩ := hev.self_of_nhds
  have heq : deriv (fun y => s * Real.sqrt (F y)) =ᶠ[𝓝 x]
      fun y => s * (deriv F y / (2 * Real.sqrt (F y))) := by
    filter_upwards [hev] with y hy
    exact ((hy.2.sqrt hy.1.ne').const_mul s).deriv
  have hsq : 0 < Real.sqrt (F x) := Real.sqrt_pos.mpr hx
  have hsq2 : Real.sqrt (F x) ^ 2 = F x := Real.sq_sqrt hx.le
  have hD : HasDerivAt (fun y => s * (deriv F y / (2 * Real.sqrt (F y))))
      (s * ((deriv (deriv F) x * (2 * Real.sqrt (F x)) -
        deriv F x * (2 * (deriv F x / (2 * Real.sqrt (F x))))) / (2 * Real.sqrt (F x)) ^ 2)) x :=
    (hd2.div ((hd.sqrt hx.ne').const_mul 2) (by positivity)).const_mul s
  rw [heq.deriv_eq, hD.deriv, ((hd.sqrt hx.ne').const_mul s).deriv]
  generalize Real.sqrt (F x) = r at hsq hsq2 ⊢
  rw [← hsq2]
  field_simp
  ring

/-- The limit `E_k̂/k̂_x² → 3` along any filter `l ≤ 𝓝 x_j` on which `F > 0` eventually. -/
private theorem tendsto_khat_E_div_sq_of {F : ℝ → ℝ} {xj s : ℝ} {l : Filter ℝ} (hl : l ≤ 𝓝 xj)
    (hs : s ≠ 0) (hF : ContDiffAt ℝ 2 F xj) (hF0 : F xj = 0) (hF1 : deriv F xj ≠ 0)
    (hpos : ∀ᶠ x in l, 0 < F x) :
    Tendsto (fun x => (2 * deriv (fun y => s * Real.sqrt (F y)) x ^ 2 -
        s * Real.sqrt (F x) * deriv (deriv (fun y => s * Real.sqrt (F y))) x) /
        deriv (fun y => s * Real.sqrt (F y)) x ^ 2) l (𝓝 3) := by
  have hF' : ContDiffAt ℝ 1 F xj := hF.of_le (by norm_num)
  have hF2 : ContDiffAt ℝ 1 (deriv F) xj := hF.derivWithin (m := 1) (by norm_num)
  have hboth : ∀ᶠ y in 𝓝 xj,
      HasDerivAt F (deriv F y) y ∧ HasDerivAt (deriv F) (deriv (deriv F) y) y :=
    (tp_eventually_hasDerivAt hF').and (tp_eventually_hasDerivAt hF2)
  have hFt : Tendsto F l (𝓝 0) := hF0 ▸ hF.continuousAt.tendsto.mono_left hl
  have hdt := (tp_continuousAt_deriv hF').tendsto.mono_left hl
  have hd2t := (tp_continuousAt_deriv hF2).tendsto.mono_left hl
  have hlim : Tendsto (fun x => 3 - 2 * F x * deriv (deriv F) x / deriv F x ^ 2) l (𝓝 3) := by
    have h := (tendsto_const_nhds (x := (3 : ℝ))).sub
      (((hFt.const_mul 2).mul hd2t).div (hdt.pow 2) (pow_ne_zero 2 hF1))
    rw [mul_zero, zero_mul, zero_div, sub_zero] at h
    exact h
  refine hlim.congr' ?_
  filter_upwards [hpos, hl hboth.eventually_nhds,
    hl ((tp_continuousAt_deriv hF').eventually_ne hF1)] with x hx hev hne
  refine (khat_E_div_sq_eq hs ?_ hev.self_of_nhds.2 hne).symm
  filter_upwards [hev, hev.self_of_nhds.1.continuousAt.eventually (lt_mem_nhds hx)] with y hy hy'
  exact ⟨hy', hy.1⟩

/-- (4.6), first claim: `k̂/k̂_x = 2(x − x_j) + O((x − x_j)²)` at a simple turning point from the
allowed (right) side, `F'(x_j) > 0`. -/
theorem khat_div_deriv_sub_isBigO_right {F : ℝ → ℝ} {xj s : ℝ} (hs : s = 1 ∨ s = -1)
    (hF : ContDiffAt ℝ 2 F xj) (hF0 : F xj = 0) (hF1 : 0 < deriv F xj) :
    (fun x => (s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x - 2 * (x - xj))
      =O[𝓝[>] xj] fun x => (x - xj) ^ 2 :=
  khat_div_deriv_sub_isBigO_of nhdsWithin_le_nhds (tp_ne_zero hs) hF hF0 hF1.ne'
    (eventually_pos_right_of_deriv_pos (hF.differentiableAt (by simp)).hasDerivAt hF0 hF1)

/-- (4.6), first claim, mirror version: from the allowed (left) side, `F'(x_j) < 0`. -/
theorem khat_div_deriv_sub_isBigO_left {F : ℝ → ℝ} {xj s : ℝ} (hs : s = 1 ∨ s = -1)
    (hF : ContDiffAt ℝ 2 F xj) (hF0 : F xj = 0) (hF1 : deriv F xj < 0) :
    (fun x => (s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x - 2 * (x - xj))
      =O[𝓝[<] xj] fun x => (x - xj) ^ 2 :=
  khat_div_deriv_sub_isBigO_of nhdsWithin_le_nhds (tp_ne_zero hs) hF hF0 hF1.ne
    (eventually_pos_left_of_deriv_neg (hF.differentiableAt (by simp)).hasDerivAt hF0 hF1)

/-- (4.6), second claim: `E_k̂/k̂_x² → 3` at a simple turning point from the allowed (right) side,
where `E_k̂ = 2k̂_x² − k̂k̂_xx`. -/
theorem tendsto_khat_E_div_sq_right {F : ℝ → ℝ} {xj s : ℝ} (hs : s = 1 ∨ s = -1)
    (hF : ContDiffAt ℝ 2 F xj) (hF0 : F xj = 0) (hF1 : 0 < deriv F xj) :
    Tendsto (fun x => (2 * deriv (fun y => s * Real.sqrt (F y)) x ^ 2 -
        s * Real.sqrt (F x) * deriv (deriv (fun y => s * Real.sqrt (F y))) x) /
        deriv (fun y => s * Real.sqrt (F y)) x ^ 2) (𝓝[>] xj) (𝓝 3) :=
  tendsto_khat_E_div_sq_of nhdsWithin_le_nhds (tp_ne_zero hs) hF hF0 hF1.ne'
    (eventually_pos_right_of_deriv_pos (hF.differentiableAt (by simp)).hasDerivAt hF0 hF1)

/-- (4.6), second claim, mirror version: from the allowed (left) side, `F'(x_j) < 0`. -/
theorem tendsto_khat_E_div_sq_left {F : ℝ → ℝ} {xj s : ℝ} (hs : s = 1 ∨ s = -1)
    (hF : ContDiffAt ℝ 2 F xj) (hF0 : F xj = 0) (hF1 : deriv F xj < 0) :
    Tendsto (fun x => (2 * deriv (fun y => s * Real.sqrt (F y)) x ^ 2 -
        s * Real.sqrt (F x) * deriv (deriv (fun y => s * Real.sqrt (F y))) x) /
        deriv (fun y => s * Real.sqrt (F y)) x ^ 2) (𝓝[<] xj) (𝓝 3) :=
  tendsto_khat_E_div_sq_of nhdsWithin_le_nhds (tp_ne_zero hs) hF hF0 hF1.ne
    (eventually_pos_left_of_deriv_neg (hF.differentiableAt (by simp)).hasDerivAt hF0 hF1)

end ModeStability.AllAngular
