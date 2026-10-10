module

public import Mathlib
public import ModeStability.AllAngular.AngularReduction
public import ModeStability.AllAngular.CoordinateIntervalsAux

/-!
# Coordinate bookkeeping for the turning-point geometry, extremal case

Source: the all-angular research notes in preparation, Section 3, p. 4), and Section 5, pp. 6–7,
(5.1)–(5.3).

The extremal half (`|Q| = M`, so `a = b = M`, `Δ = (r − M)²`) of
`ModeStability.AllAngular.CoordinateIntervals`; see there for the overview. The two coordinate
maps `ρ : (0, ∞) → (a, ∞)` are

* extremal reciprocal (`extremal_reciprocal_*`): `ρ(x) = M + x`, increasing, inverse `r ↦ r − M`,
  amplitude `U(x) = x R(M + x)`, coefficient `F(x) = (K/x²)² − L/x² = P(ρ(x))/x⁴` of
  `extremal_reciprocal_reduction_L`;
* extremal constant (`extremal_constant_*`): `ρ(y) = M + 1/y`, decreasing, inverse
  `r ↦ 1/(r − M)`, amplitude `U(y) = R(M + 1/y)`, coefficient `F(y) = K² − L/y² = P(ρ(y))` of
  `extremal_constant_reduction_L`,

where `P = K² − LΔ`. For each: `*_transfer_zero`, `*_bijective`, `*_interval_preimage`,
`*_corotation_point`, `*_corotation_sign`, `*_sign_pattern`, `*_coefficient_contDiffOn`,
`*_turning_points`, with the same shapes as in the subextremal case.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

/-- `K` is smooth. -/
private theorem cx_contDiff_radialK (e ω : ℝ) : ContDiff ℝ ⊤ (radialK e ω) := by
  unfold radialK
  fun_prop

/-! ### Extremal, reciprocal normalization: `ρ(x) = M + x` -/

/-- `ρ(x) = M + x > a` for `x > 0`. -/
theorem extremal_reciprocal_mapsTo {M Q : ℝ} (hQ : |Q| = M) {x : ℝ} (hx : 0 < x) :
    outerHorizon M Q < M + x := by
  rw [outerHorizon_of_abs_eq hQ]
  linarith

/-- `ρ(x) = M + x` is strictly increasing. -/
theorem extremal_reciprocal_strictMonoOn (M : ℝ) :
    StrictMonoOn (fun x : ℝ => M + x) (Ioi 0) :=
  fun _ _ _ _ hab => (add_lt_add_iff_left M).2 hab

/-- `ρ(x) = M + x` is smooth. -/
theorem extremal_reciprocal_contDiffOn (M : ℝ) :
    ContDiffOn ℝ ⊤ (fun x : ℝ => M + x) (Ioi 0) :=
  contDiffOn_const.add contDiffOn_id

/-- The inverse of `ρ(x) = M + x` is `r ↦ r − M`: for `r > a`, `r − M > 0` and
`ρ(r − M) = r`. -/
theorem extremal_reciprocal_inverse {M Q : ℝ} (hQ : |Q| = M) {r : ℝ}
    (hr : outerHorizon M Q < r) : 0 < r - M ∧ M + (r - M) = r := by
  rw [outerHorizon_of_abs_eq hQ] at hr
  exact ⟨sub_pos.2 hr, by ring⟩

/-- **The extremal reciprocal coordinate.** `ρ(x) = M + x` is a strictly increasing bijection
`(0, ∞) → (a, ∞)` with inverse `r ↦ r − M`, continuous and `C²` (in fact smooth), with
`ρ' = 1 > 0`. -/
theorem extremal_reciprocal_bijective {M Q : ℝ} (hQ : |Q| = M) :
    StrictMonoOn (fun x : ℝ => M + x) (Ioi 0) ∧
      BijOn (fun x : ℝ => M + x) (Ioi 0) (Ioi (outerHorizon M Q)) ∧
      (∀ r ∈ Ioi (outerHorizon M Q), 0 < r - M ∧ M + (r - M) = r) ∧
      (∀ x ∈ Ioi (0 : ℝ), M + x - M = x) ∧
      ContinuousOn (fun x : ℝ => M + x) (Ioi 0) ∧
      ContDiffOn ℝ 2 (fun x : ℝ => M + x) (Ioi 0) ∧
      ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => M + t) 1 x ∧ (0 : ℝ) < 1 := by
  have hmono := extremal_reciprocal_strictMonoOn M
  have hcd := extremal_reciprocal_contDiffOn M
  refine ⟨hmono, ⟨fun x hx => extremal_reciprocal_mapsTo hQ hx, hmono.injOn, fun r hr => ?_⟩,
    fun r hr => extremal_reciprocal_inverse hQ hr, fun x _ => add_sub_cancel_left M x,
    hcd.continuousOn, hcd.of_le le_top, fun x _ => ⟨(hasDerivAt_id' x).const_add M, one_pos⟩⟩
  obtain ⟨h0, h1⟩ := extremal_reciprocal_inverse hQ hr
  exact ⟨_, h0, h1⟩

/-- **Vanishing transfers back (extremal reciprocal).** If `U(x) = x R(M + x)` vanishes on
`(0, ∞)`, then `R = 0` on `(a, ∞)`. -/
theorem extremal_reciprocal_transfer_zero {M Q : ℝ} (hQ : |Q| = M) {R : ℝ → ℂ}
    (hU : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) * R (M + x) = 0) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  intro r hr
  obtain ⟨h0, h1⟩ := extremal_reciprocal_inverse hQ hr
  have h := hU _ h0
  rw [h1] at h
  exact (mul_eq_zero.1 h).resolve_left (Complex.ofReal_ne_zero.2 h0.ne')

/-- **The corotation point (extremal reciprocal, `L = 0`).** For `r₀ > a` and `x₀ = r₀ − M`:
`x₀ > 0`, `ρ(x₀) = r₀`, and `ρ` maps `(0, x₀)` into `(a, r₀)` and `(x₀, ∞)` into `(r₀, ∞)`. -/
theorem extremal_reciprocal_corotation_point {M Q r₀ : ℝ} (hQ : |Q| = M)
    (hr₀ : outerHorizon M Q < r₀) :
    ∃ x₀ : ℝ, x₀ = r₀ - M ∧ 0 < x₀ ∧ M + x₀ = r₀ ∧
      (∀ x ∈ Ioo 0 x₀, M + x ∈ Ioo (outerHorizon M Q) r₀) ∧ ∀ x ∈ Ioi x₀, M + x ∈ Ioi r₀ := by
  obtain ⟨hx₀, hρ₀⟩ := extremal_reciprocal_inverse hQ hr₀
  obtain ⟨h₁, h₂⟩ := coordinate_point_of_strictMonoOn (ρ := fun x : ℝ => M + x)
    (extremal_reciprocal_strictMonoOn M) (fun x hx => extremal_reciprocal_mapsTo hQ hx) hx₀ hρ₀
  exact ⟨_, rfl, hx₀, hρ₀, h₁, h₂⟩

/-- **The sign of `K` around corotation (extremal reciprocal).** For `ω > 0` and `a < r₀ = e/ω`,
with `x₀ = ρ⁻¹(r₀)`: `K(M + x) < 0` on `(0, x₀)` and `K(M + x) > 0` on `(x₀, ∞)`. -/
theorem extremal_reciprocal_corotation_sign {M Q e ω : ℝ} (hQ : |Q| = M) (hω : 0 < ω)
    (hr₀ : outerHorizon M Q < e / ω) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ M + x₀ = e / ω ∧ (∀ x ∈ Ioo 0 x₀, radialK e ω (M + x) < 0) ∧
      ∀ x ∈ Ioi x₀, 0 < radialK e ω (M + x) := by
  obtain ⟨hx₀, hρ₀⟩ := extremal_reciprocal_inverse hQ hr₀
  exact ⟨_, hx₀, hρ₀, corotation_sign_of_strictMonoOn (ρ := fun x : ℝ => M + x)
    (outerHorizon_nonneg_of_abs_le hQ.le) hω (extremal_reciprocal_strictMonoOn M)
    (fun x hx => extremal_reciprocal_mapsTo hQ hx) hx₀ hρ₀⟩

/-- The coefficient `F(x) = (K/x²)² − L/x²` (at `r = M + x`) of `extremal_reciprocal_reduction_L`
is `C²` on `(0, ∞)`. -/
theorem extremal_reciprocal_coefficient_contDiffOn (M e ω L : ℝ) :
    ContDiffOn ℝ 2 (fun x => (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2) (Ioi 0) := by
  have hK := (cx_contDiff_radialK e ω).comp_contDiffOn (extremal_reciprocal_contDiffOn M)
  exact (((hK.div (contDiffOn_id.pow 2) fun x hx => pow_ne_zero 2 (ne_of_gt hx)).pow 2).sub
    (contDiffOn_const.div (contDiffOn_id.pow 2)
      fun x hx => pow_ne_zero 2 (ne_of_gt hx))).of_le le_top

/-- `F(x) = (K/x²)² − L/x² = x⁻⁴ P(M + x)` for `x > 0`. -/
private theorem cx_extremal_reciprocal_F_eq {M Q : ℝ} (hQ : |Q| = M) (e ω L : ℝ) {x : ℝ}
    (hx : 0 < x) :
    (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2 =
      (x ^ 4)⁻¹ * (radialK e ω (M + x) ^ 2 - L * delta M Q (M + x)) := by
  have hx0 : x ≠ 0 := hx.ne'
  rw [delta_of_abs_eq hQ, add_sub_cancel_left]
  field_simp

/-- **The turning points in the extremal reciprocal coordinate.** For `M > 0`, `ω > 0`, `L > 0`
and `K(a) < 0` there are `0 < x₁ < x₂` with `a < M + x₁ < e/ω < M + x₂`, `M + x_j = r_j` the
turning points of `exists_turning_points`, such that `F(x) = (K/x²)² − L/x²` (at `r = M + x`) is
positive with `K < 0` on `(0, x₁)`, negative on `(x₁, x₂)`, positive with `K > 0` on `(x₂, ∞)`,
vanishes at `x₁`, `x₂`, and has `F'(x₁) < 0 < F'(x₂)`. -/
theorem extremal_reciprocal_turning_points {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| = M)
    (hω : 0 < ω) (hL : 0 < L) (hK : radialK e ω (outerHorizon M Q) < 0) :
    ∃ x₁ x₂ : ℝ, 0 < x₁ ∧ x₁ < x₂ ∧ outerHorizon M Q < M + x₁ ∧ M + x₁ < e / ω ∧
      e / ω < M + x₂ ∧
      (∀ x ∈ Ioo 0 x₁, 0 < (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2 ∧
        radialK e ω (M + x) < 0) ∧
      (∀ x ∈ Ioo x₁ x₂, (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2 < 0) ∧
      (∀ x ∈ Ioi x₂, 0 < (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2 ∧
        0 < radialK e ω (M + x)) ∧
      (radialK e ω (M + x₁) / x₁ ^ 2) ^ 2 - L / x₁ ^ 2 = 0 ∧
      (radialK e ω (M + x₂) / x₂ ^ 2) ^ 2 - L / x₂ ^ 2 = 0 ∧
      deriv (fun x => (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2) x₁ < 0 ∧
      0 < deriv (fun x => (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2) x₂ := by
  obtain ⟨r₁, r₂, hr₁, hr₁₀, hr₀₂, -, -, -, -, hP₁, hPm, hP₂, hP0₁, hP0₂, -, -, -, -, hd₁, hd₂⟩ :=
    exists_turning_points hM hQ.le hω hL hK
  have hr₁₂ : r₁ < r₂ := hr₁₀.trans hr₀₂
  obtain ⟨x₁, hx₁, hρ₁⟩ : ∃ x₁, 0 < x₁ ∧ M + x₁ = r₁ := ⟨_, extremal_reciprocal_inverse hQ hr₁⟩
  obtain ⟨x₂, hx₂, hρ₂⟩ : ∃ x₂, 0 < x₂ ∧ M + x₂ = r₂ :=
    ⟨_, extremal_reciprocal_inverse hQ (hr₁.trans hr₁₂)⟩
  obtain ⟨h₁₂, hS₁, hSm, hS₂⟩ := coordinate_signs_of_strictMonoOn (ρ := fun x : ℝ => M + x)
    (F := fun x => (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2)
    (c := fun x => (x ^ 4)⁻¹) (P := fun r => radialK e ω r ^ 2 - L * delta M Q r)
    (K := radialK e ω) (extremal_reciprocal_strictMonoOn M)
    (fun x hx => extremal_reciprocal_mapsTo hQ hx) hx₁ hx₂ hρ₁ hρ₂ hr₁₂
    (fun x hx => cx_extremal_reciprocal_F_eq hQ e ω L hx) (fun x hx => inv_pos.2 (pow_pos hx 4))
    hP₁ hPm hP₂
  have hD : ∀ {x r : ℝ}, 0 < x → M + x = r → radialK e ω r ^ 2 - L * delta M Q r = 0 →
      HasDerivAt (fun x => (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2)
        ((x ^ 4)⁻¹ * ((2 * radialK e ω r * (2 * ω * r - e) - L * (2 * (r - M))) * 1)) x :=
    fun hx hρ h0 =>
      hasDerivAt_coefficient_at_turning_point (c := fun x => (x ^ 4)⁻¹)
        (ρ := fun x : ℝ => M + x) (P := fun r => radialK e ω r ^ 2 - L * delta M Q r) hx
        (fun x hx => cx_extremal_reciprocal_F_eq hQ e ω L hx)
        ((hasDerivAt_pow 4 _).inv (pow_ne_zero 4 hx.ne')) ((hasDerivAt_id' _).const_add M) hρ
        (hasDerivAt_turningPoly M Q e ω L _) h0
  refine ⟨x₁, x₂, hx₁, h₁₂, hρ₁ ▸ hr₁, hρ₁ ▸ hr₁₀, hρ₂ ▸ hr₀₂, hS₁, hSm, hS₂, ?_, ?_, ?_, ?_⟩
  · rw [cx_extremal_reciprocal_F_eq hQ e ω L hx₁, hρ₁, hP0₁, mul_zero]
  · rw [cx_extremal_reciprocal_F_eq hQ e ω L hx₂, hρ₂, hP0₂, mul_zero]
  · rw [(hD hx₁ hρ₁ hP0₁).deriv, mul_one]
    exact mul_neg_of_pos_of_neg (inv_pos.2 (pow_pos hx₁ 4)) hd₁
  · rw [(hD hx₂ hρ₂ hP0₂).deriv, mul_one]
    exact mul_pos (inv_pos.2 (pow_pos hx₂ 4)) hd₂

/-! ### Extremal, constant normalization: `ρ(y) = M + 1/y` -/

/-- `ρ(y) = M + 1/y > a` for `y > 0`. -/
theorem extremal_constant_mapsTo {M Q : ℝ} (hQ : |Q| = M) {y : ℝ} (hy : 0 < y) :
    outerHorizon M Q < M + 1 / y := by
  rw [outerHorizon_of_abs_eq hQ]
  have := one_div_pos.2 hy
  linarith

/-- `ρ(y) = M + 1/y` is strictly decreasing on `(0, ∞)`. -/
theorem extremal_constant_strictAntiOn (M : ℝ) :
    StrictAntiOn (fun y : ℝ => M + 1 / y) (Ioi 0) :=
  fun _ ha _ _ hab => (add_lt_add_iff_left M).2 (one_div_lt_one_div_of_lt ha hab)

/-- `ρ(y) = M + 1/y` is smooth on `(0, ∞)`. -/
theorem extremal_constant_contDiffOn (M : ℝ) :
    ContDiffOn ℝ ⊤ (fun y : ℝ => M + 1 / y) (Ioi 0) :=
  contDiffOn_const.add (contDiffOn_const.div contDiffOn_id fun _ ht => (mem_Ioi.1 ht).ne')

/-- `ρ'(y) = −1/y²` for `y > 0`. -/
theorem extremal_constant_hasDerivAt (M : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => M + 1 / t) (-(y ^ 2)⁻¹) y := by
  simpa only [one_div] using (hasDerivAt_inv hy.ne').const_add M

/-- The inverse of `ρ(y) = M + 1/y` is `r ↦ 1/(r − M)`: for `r > a`, `1/(r − M) > 0` and
`ρ(1/(r − M)) = r`. -/
theorem extremal_constant_inverse {M Q : ℝ} (hQ : |Q| = M) {r : ℝ}
    (hr : outerHorizon M Q < r) : 0 < 1 / (r - M) ∧ M + 1 / (1 / (r - M)) = r := by
  rw [outerHorizon_of_abs_eq hQ] at hr
  refine ⟨one_div_pos.2 (sub_pos.2 hr), ?_⟩
  rw [one_div_one_div]
  ring

/-- **The extremal constant coordinate.** `ρ(y) = M + 1/y` is a strictly decreasing bijection
`(0, ∞) → (a, ∞)` with inverse `r ↦ 1/(r − M)`, continuous and `C²` (in fact smooth), with
`ρ'(y) = −1/y² < 0`. -/
theorem extremal_constant_bijective {M Q : ℝ} (hQ : |Q| = M) :
    StrictAntiOn (fun y : ℝ => M + 1 / y) (Ioi 0) ∧
      BijOn (fun y : ℝ => M + 1 / y) (Ioi 0) (Ioi (outerHorizon M Q)) ∧
      (∀ r ∈ Ioi (outerHorizon M Q), 0 < 1 / (r - M) ∧ M + 1 / (1 / (r - M)) = r) ∧
      (∀ y ∈ Ioi (0 : ℝ), 1 / (M + 1 / y - M) = y) ∧
      ContinuousOn (fun y : ℝ => M + 1 / y) (Ioi 0) ∧
      ContDiffOn ℝ 2 (fun y : ℝ => M + 1 / y) (Ioi 0) ∧
      ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => M + 1 / t) (-(y ^ 2)⁻¹) y ∧ -(y ^ 2)⁻¹ < 0 := by
  have hanti := extremal_constant_strictAntiOn M
  have hcd := extremal_constant_contDiffOn M
  refine ⟨hanti, ⟨fun y hy => extremal_constant_mapsTo hQ hy, hanti.injOn, fun r hr => ?_⟩,
    fun r hr => extremal_constant_inverse hQ hr, fun y _ => ?_, hcd.continuousOn,
    hcd.of_le le_top, fun y hy => ⟨extremal_constant_hasDerivAt M hy,
      neg_neg_of_pos (inv_pos.2 (pow_pos hy 2))⟩⟩
  · obtain ⟨h0, h1⟩ := extremal_constant_inverse hQ hr
    exact ⟨_, h0, h1⟩
  · rw [add_sub_cancel_left, one_div_one_div]

/-- **Vanishing transfers back (extremal constant).** If `U(y) = R(M + 1/y)` vanishes on
`(0, ∞)`, then `R = 0` on `(a, ∞)`. -/
theorem extremal_constant_transfer_zero {M Q : ℝ} (hQ : |Q| = M) {R : ℝ → ℂ}
    (hU : ∀ y ∈ Ioi (0 : ℝ), R (M + 1 / y) = 0) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  intro r hr
  obtain ⟨h0, h1⟩ := extremal_constant_inverse hQ hr
  have h := hU _ h0
  rw [h1] at h
  exact h

/-- **The corotation point (extremal constant, `L = 0`).** For `r₀ > a` and `y₀ = 1/(r₀ − M)`:
`y₀ > 0`, `ρ(y₀) = r₀`, and `ρ` maps `(0, y₀)` into `(r₀, ∞)` and `(y₀, ∞)` into `(a, r₀)`. -/
theorem extremal_constant_corotation_point {M Q r₀ : ℝ} (hQ : |Q| = M)
    (hr₀ : outerHorizon M Q < r₀) :
    ∃ y₀ : ℝ, y₀ = 1 / (r₀ - M) ∧ 0 < y₀ ∧ M + 1 / y₀ = r₀ ∧
      (∀ y ∈ Ioo 0 y₀, M + 1 / y ∈ Ioi r₀) ∧
      ∀ y ∈ Ioi y₀, M + 1 / y ∈ Ioo (outerHorizon M Q) r₀ := by
  obtain ⟨hy₀, hρ₀⟩ := extremal_constant_inverse hQ hr₀
  obtain ⟨h₁, h₂⟩ := coordinate_point_of_strictAntiOn (ρ := fun y : ℝ => M + 1 / y)
    (extremal_constant_strictAntiOn M) (fun y hy => extremal_constant_mapsTo hQ hy) hy₀ hρ₀
  exact ⟨_, rfl, hy₀, hρ₀, h₁, h₂⟩

/-- **The sign of `K` around corotation (extremal constant).** For `ω > 0` and `a < r₀ = e/ω`,
with `y₀ = ρ⁻¹(r₀)`: `K(M + 1/y) > 0` on `(0, y₀)` and `K(M + 1/y) < 0` on `(y₀, ∞)`. -/
theorem extremal_constant_corotation_sign {M Q e ω : ℝ} (hQ : |Q| = M) (hω : 0 < ω)
    (hr₀ : outerHorizon M Q < e / ω) :
    ∃ y₀ : ℝ, 0 < y₀ ∧ M + 1 / y₀ = e / ω ∧ (∀ y ∈ Ioo 0 y₀, 0 < radialK e ω (M + 1 / y)) ∧
      ∀ y ∈ Ioi y₀, radialK e ω (M + 1 / y) < 0 := by
  obtain ⟨hy₀, hρ₀⟩ := extremal_constant_inverse hQ hr₀
  exact ⟨_, hy₀, hρ₀, corotation_sign_of_strictAntiOn (ρ := fun y : ℝ => M + 1 / y)
    (outerHorizon_nonneg_of_abs_le hQ.le) hω (extremal_constant_strictAntiOn M)
    (fun y hy => extremal_constant_mapsTo hQ hy) hy₀ hρ₀⟩

/-- The coefficient `F(y) = K² − L/y²` (at `r = M + 1/y`) of `extremal_constant_reduction_L` is
`C²` on `(0, ∞)`. -/
theorem extremal_constant_coefficient_contDiffOn (M e ω L : ℝ) :
    ContDiffOn ℝ 2 (fun y => radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2) (Ioi 0) := by
  have hK := (cx_contDiff_radialK e ω).comp_contDiffOn (extremal_constant_contDiffOn M)
  exact ((hK.pow 2).sub (contDiffOn_const.div (contDiffOn_id.pow 2)
      fun x hx => pow_ne_zero 2 (ne_of_gt hx))).of_le le_top

/-- `F(y) = K² − L/y² = P(M + 1/y)` (all `y`). -/
private theorem cx_extremal_constant_F_eq {M Q : ℝ} (hQ : |Q| = M) (e ω L y : ℝ) :
    radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2 =
      1 * (radialK e ω (M + 1 / y) ^ 2 - L * delta M Q (M + 1 / y)) := by
  rw [delta_of_abs_eq hQ, add_sub_cancel_left]
  ring

/-- **The turning points in the extremal constant coordinate.** For `M > 0`, `ω > 0`, `L > 0` and
`K(a) < 0` there are `0 < y₂ < y₁` with `a < M + 1/y₁ < e/ω < M + 1/y₂`, `M + 1/y_j = r_j` the
turning points of `exists_turning_points`, such that `F(y) = K² − L/y²` (at `r = M + 1/y`) is
positive with `K > 0` on `(0, y₂)`, negative on `(y₂, y₁)`, positive with `K < 0` on `(y₁, ∞)`,
vanishes at `y₁`, `y₂`, and has `F'(y₂) < 0 < F'(y₁)`. For `eqOn_zero_of_global_current_L` take
`x₁ := y₂`, `x₂ := y₁`. -/
theorem extremal_constant_turning_points {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| = M)
    (hω : 0 < ω) (hL : 0 < L) (hK : radialK e ω (outerHorizon M Q) < 0) :
    ∃ y₁ y₂ : ℝ, 0 < y₂ ∧ y₂ < y₁ ∧ outerHorizon M Q < M + 1 / y₁ ∧ M + 1 / y₁ < e / ω ∧
      e / ω < M + 1 / y₂ ∧
      (∀ y ∈ Ioo 0 y₂, 0 < radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2 ∧
        0 < radialK e ω (M + 1 / y)) ∧
      (∀ y ∈ Ioo y₂ y₁, radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2 < 0) ∧
      (∀ y ∈ Ioi y₁, 0 < radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2 ∧
        radialK e ω (M + 1 / y) < 0) ∧
      radialK e ω (M + 1 / y₁) ^ 2 - L / y₁ ^ 2 = 0 ∧
      radialK e ω (M + 1 / y₂) ^ 2 - L / y₂ ^ 2 = 0 ∧
      deriv (fun y => radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2) y₂ < 0 ∧
      0 < deriv (fun y => radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2) y₁ := by
  obtain ⟨r₁, r₂, hr₁, hr₁₀, hr₀₂, -, -, -, -, hP₁, hPm, hP₂, hP0₁, hP0₂, -, -, -, -, hd₁, hd₂⟩ :=
    exists_turning_points hM hQ.le hω hL hK
  have hr₁₂ : r₁ < r₂ := hr₁₀.trans hr₀₂
  obtain ⟨y₁, hy₁, hρ₁⟩ : ∃ y₁, 0 < y₁ ∧ M + 1 / y₁ = r₁ :=
    ⟨_, extremal_constant_inverse hQ hr₁⟩
  obtain ⟨y₂, hy₂, hρ₂⟩ : ∃ y₂, 0 < y₂ ∧ M + 1 / y₂ = r₂ :=
    ⟨_, extremal_constant_inverse hQ (hr₁.trans hr₁₂)⟩
  obtain ⟨h₂₁, hS₂, hSm, hS₁⟩ := coordinate_signs_of_strictAntiOn
    (ρ := fun y : ℝ => M + 1 / y) (F := fun y => radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2)
    (c := fun _ => 1) (P := fun r => radialK e ω r ^ 2 - L * delta M Q r) (K := radialK e ω)
    (extremal_constant_strictAntiOn M) (fun y hy => extremal_constant_mapsTo hQ hy)
    hy₁ hy₂ hρ₁ hρ₂ hr₁₂ (fun y _ => cx_extremal_constant_F_eq hQ e ω L y)
    (fun _ _ => one_pos) hP₁ hPm hP₂
  have hD : ∀ {y r : ℝ}, 0 < y → M + 1 / y = r → radialK e ω r ^ 2 - L * delta M Q r = 0 →
      HasDerivAt (fun y => radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2)
        (1 * ((2 * radialK e ω r * (2 * ω * r - e) - L * (2 * (r - M))) * -(y ^ 2)⁻¹)) y :=
    fun hy hρ h0 =>
      hasDerivAt_coefficient_at_turning_point (c := fun _ => 1) (ρ := fun y : ℝ => M + 1 / y)
        (P := fun r => radialK e ω r ^ 2 - L * delta M Q r) hy
        (fun y _ => cx_extremal_constant_F_eq hQ e ω L y) (hasDerivAt_const _ _)
        (extremal_constant_hasDerivAt M hy) hρ (hasDerivAt_turningPoly M Q e ω L _) h0
  refine ⟨y₁, y₂, hy₂, h₂₁, hρ₁ ▸ hr₁, hρ₁ ▸ hr₁₀, hρ₂ ▸ hr₀₂, hS₂, hSm, hS₁, ?_, ?_, ?_, ?_⟩
  · rw [cx_extremal_constant_F_eq hQ e ω L, hρ₁, hP0₁, mul_zero]
  · rw [cx_extremal_constant_F_eq hQ e ω L, hρ₂, hP0₂, mul_zero]
  · rw [(hD hy₂ hρ₂ hP0₂).deriv, one_mul]
    exact mul_neg_of_pos_of_neg hd₂ (neg_neg_of_pos (inv_pos.2 (pow_pos hy₂ 2)))
  · rw [(hD hy₁ hρ₁ hP0₁).deriv, one_mul]
    exact mul_pos_of_neg_of_neg hd₁ (neg_neg_of_pos (inv_pos.2 (pow_pos hy₁ 2)))

end ModeStability.AllAngular

end
