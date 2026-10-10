module

public import Mathlib
public import ModeStability.AllAngular.AngularReduction
public import ModeStability.AllAngular.CoordinateIntervalsAux
public import ModeStability.AllAngular.CoordinateIntervalsExtremal

/-!
# Coordinate bookkeeping for the turning-point geometry

Source: the all-angular research notes in preparation, Section 3, p. 4, and Section 5, pp. 6–7,
(5.1)–(5.3) with the closing sentence ODE uniqueness propagates vanishing across the exterior

The radial turning-point geometry of (3.1) (`exists_turning_points`: `a < r₁ < r₀ = e/ω < r₂`,
`P = K² − LΔ` positive on `(a, r₁)` and `(r₂, ∞)`, negative on `(r₁, r₂)`) lives on `r > a`; the
global identity (5.3) (`eqOn_zero_of_global_current_L`) is stated on the coordinate interval
`(0, ∞)`. This file and `ModeStability.AllAngular.CoordinateIntervalsExtremal` (imported here,
with the generic transport lemmas of `ModeStability.AllAngular.CoordinateIntervalsAux`) transport
the geometry to the four coordinate systems of the reductions in
`ModeStability.AllAngular.AngularReduction` and transport vanishing back. Each system has a
coordinate map `ρ : (0, ∞) → (a, ∞)`; the two subextremal systems are treated here, the two
extremal ones in `CoordinateIntervalsExtremal`:

* subextremal reciprocal (`reciprocal_*`): `ρ(x) = radiusOf M Q x`, increasing, inverse
  `r ↦ 1/h(r)`, amplitude `U(x) = x R(ρ(x))`, `F(x) = (K/x²)² − LΔ/x⁴ = P(ρ(x))/x⁴`;
* subextremal constant (`constant_*`): `ρ(y) = radiusOf M Q (1/y)`, decreasing, inverse
  `r ↦ h(r)`, amplitude `U(y) = R(ρ(y))`, `F(y) = K² − LΔ = P(ρ(y))`;
* extremal reciprocal (`extremal_reciprocal_*`, `|Q| = M`, `a = M`): `ρ(x) = M + x`, increasing,
  inverse `r ↦ r − M`, `U(x) = x R(M + x)`, `F(x) = (K/x²)² − L/x² = P(ρ(x))/x⁴`;
* extremal constant (`extremal_constant_*`): `ρ(y) = M + 1/y`, decreasing, inverse
  `r ↦ 1/(r − M)`, `U(y) = R(M + 1/y)`, `F(y) = K² − L/y² = P(ρ(y))`.

Here `h = staticSolution M Q` and `F` is the coefficient of the reduced equation `U'' = −F U` in
the exact form of `reciprocal_reduction_L`, `constant_reduction_L`,
`extremal_reciprocal_reduction_L`, `extremal_constant_reduction_L`.

For each system:

* `*_transfer_zero`: `U = 0` on `(0, ∞)` implies `R = 0` on `(a, ∞)`.
* `*_bijective`: `ρ` is a strictly monotone bijection `(0, ∞) → (a, ∞)` with explicit inverse,
  continuous and `C²` (in fact smooth: `*_contDiffOn`), with `ρ' ≠ 0` of known sign.
* `*_interval_preimage`: for `a < r₁ < r₂`, the points `x_j = ρ⁻¹(r_j)` and the images of the
  three coordinate intervals (for decreasing systems the order is reversed: `y₂ < y₁`).
* `*_corotation_point`, `*_corotation_sign`: the case `L = 0`, one point `x₀ = ρ⁻¹(r₀)`, and the
  sign of `K(ρ(x))` on both sides of `x₀ = ρ⁻¹(e/ω)`.
* `*_sign_pattern`: from the radial sign pattern of `P` and `K`, the sign pattern of `F` and `K
  ∘ ρ`
  on the coordinate intervals.
* `*_coefficient_contDiffOn`: `F` is `C²` on `(0, ∞)`.
* `*_turning_points`: the same, packaged from the source premises (`ω > 0`, `L > 0`, `K(a) < 0`)
  through `exists_turning_points`, together with `F(x_j) = 0` and the signs of `F'(x_j)`, which is
  the input shape of `eqOn_zero_of_global_current_L` (`x₁ < x₂`, `F > 0` on `(0, x₁)`, `F < 0` on
  `(x₁, x₂)`, `F > 0` on `(x₂, ∞)`, `F'(x_j) ≠ 0`). For the decreasing systems the consumer's
  first point is `y₂ = ρ⁻¹(r₂)` and its second `y₁ = ρ⁻¹(r₁)`.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular


/-- `K` is smooth. -/
private theorem cx_contDiff_radialK (e ω : ℝ) : ContDiff ℝ ⊤ (radialK e ω) := by
  unfold radialK
  fun_prop

/-- `Δ` is smooth. -/
private theorem cx_contDiff_delta (M Q : ℝ) : ContDiff ℝ ⊤ (delta M Q) := by
  unfold delta
  fun_prop

/-! ### Subextremal, reciprocal normalization: `ρ(x) = radiusOf M Q x` -/

/-- `ρ'(x) = Δ(ρ(x))/x² > 0` for `x > 0`. -/
theorem reciprocal_deriv_pos {M Q : ℝ} (hQ : |Q| < M) {x : ℝ} (hx : 0 < x) :
    0 < delta M Q (radiusOf M Q x) / x ^ 2 :=
  div_pos (delta_pos hQ (outerHorizon_lt_radiusOf hQ hx)) (pow_pos hx 2)

/-- `ρ = radiusOf M Q` is strictly increasing on `(0, ∞)`. -/
theorem reciprocal_strictMonoOn {M Q : ℝ} (hQ : |Q| < M) :
    StrictMonoOn (radiusOf M Q) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun x hx => (hasDerivAt_radiusOf hQ hx).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_radiusOf hQ hx).deriv]
  exact reciprocal_deriv_pos hQ hx

/-- `ρ = radiusOf M Q` is smooth on `(0, ∞)`. -/
theorem reciprocal_contDiffOn {M Q : ℝ} (hQ : |Q| < M) :
    ContDiffOn ℝ ⊤ (radiusOf M Q) (Ioi 0) := by
  have hinv : ContDiffOn ℝ ⊤ (fun t : ℝ => 1 / t) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id fun t ht => (mem_Ioi.1 ht).ne'
  refine ((contDiffOn_radiusOf_one_div hQ).comp hinv fun t ht => one_div_pos.2 ht).congr
    fun x _ => ?_
  simp only [Function.comp_apply, one_div_one_div]

/-- The inverse of `ρ = radiusOf M Q` is `r ↦ 1/h(r)`: for `r > a`, `1/h(r) > 0` and
`ρ(1/h(r)) = r`. -/
theorem reciprocal_inverse {M Q : ℝ} (hQ : |Q| < M) {r : ℝ} (hr : outerHorizon M Q < r) :
    0 < 1 / staticSolution M Q r ∧ radiusOf M Q (1 / staticSolution M Q r) = r :=
  ⟨one_div_pos.2 (staticSolution_pos hQ hr), radiusOf_one_div_staticSolution hQ hr⟩

/-- **The subextremal reciprocal coordinate.** `ρ = radiusOf M Q` is a strictly increasing
bijection `(0, ∞) → (a, ∞)` with inverse `r ↦ 1/h(r)`, continuous and `C²` on `(0, ∞)`, with
`ρ'(x) = Δ(ρ(x))/x² > 0`. -/
theorem reciprocal_bijective {M Q : ℝ} (hQ : |Q| < M) :
    StrictMonoOn (radiusOf M Q) (Ioi 0) ∧
      BijOn (radiusOf M Q) (Ioi 0) (Ioi (outerHorizon M Q)) ∧
      (∀ r ∈ Ioi (outerHorizon M Q), 0 < 1 / staticSolution M Q r ∧
        radiusOf M Q (1 / staticSolution M Q r) = r) ∧
      (∀ x ∈ Ioi (0 : ℝ), 1 / staticSolution M Q (radiusOf M Q x) = x) ∧
      ContinuousOn (radiusOf M Q) (Ioi 0) ∧ ContDiffOn ℝ 2 (radiusOf M Q) (Ioi 0) ∧
      ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (radiusOf M Q) (delta M Q (radiusOf M Q x) / x ^ 2) x ∧
        0 < delta M Q (radiusOf M Q x) / x ^ 2 := by
  have hmono := reciprocal_strictMonoOn hQ
  have hcd := reciprocal_contDiffOn hQ
  refine ⟨hmono, ⟨fun x hx => outerHorizon_lt_radiusOf hQ hx, hmono.injOn, fun r hr => ?_⟩,
    fun r hr => reciprocal_inverse hQ hr, fun x hx => ?_, hcd.continuousOn, hcd.of_le le_top,
    fun x hx => ⟨hasDerivAt_radiusOf hQ hx, reciprocal_deriv_pos hQ hx⟩⟩
  · obtain ⟨h0, h1⟩ := reciprocal_inverse hQ hr
    exact ⟨_, h0, h1⟩
  · rw [staticSolution_radiusOf hQ hx, one_div_one_div]

/-- **Vanishing transfers back (subextremal reciprocal).** If `U(x) = x R(ρ(x))` vanishes on
`(0, ∞)`, then `R = 0` on `(a, ∞)`. -/
theorem reciprocal_transfer_zero {M Q : ℝ} (hQ : |Q| < M) {R : ℝ → ℂ}
    (hU : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) * R (radiusOf M Q x) = 0) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  intro r hr
  obtain ⟨h0, h1⟩ := reciprocal_inverse hQ hr
  have h := hU _ h0
  rw [h1] at h
  exact (mul_eq_zero.1 h).resolve_left (Complex.ofReal_ne_zero.2 h0.ne')

/-- **The coordinate intervals (subextremal reciprocal).** For `a < r₁ < r₂` and
`x_j = 1/h(r_j)`: `0 < x₁ < x₂`, `ρ(x_j) = r_j`, and `ρ` maps `(0, x₁)`, `(x₁, x₂)`, `(x₂, ∞)`
into `(a, r₁)`, `(r₁, r₂)`, `(r₂, ∞)`. -/
theorem reciprocal_interval_preimage {M Q r₁ r₂ : ℝ} (hQ : |Q| < M)
    (hr₁ : outerHorizon M Q < r₁) (hr₁₂ : r₁ < r₂) :
    ∃ x₁ x₂ : ℝ, x₁ = 1 / staticSolution M Q r₁ ∧ x₂ = 1 / staticSolution M Q r₂ ∧
      0 < x₁ ∧ x₁ < x₂ ∧ radiusOf M Q x₁ = r₁ ∧ radiusOf M Q x₂ = r₂ ∧
      (∀ x ∈ Ioo 0 x₁, radiusOf M Q x ∈ Ioo (outerHorizon M Q) r₁) ∧
      (∀ x ∈ Ioo x₁ x₂, radiusOf M Q x ∈ Ioo r₁ r₂) ∧
      ∀ x ∈ Ioi x₂, radiusOf M Q x ∈ Ioi r₂ := by
  obtain ⟨hx₁, hρ₁⟩ := reciprocal_inverse hQ hr₁
  obtain ⟨hx₂, hρ₂⟩ := reciprocal_inverse hQ (hr₁.trans hr₁₂)
  obtain ⟨h₁₂, hI₁, hIm, hI₂⟩ := coordinate_intervals_of_strictMonoOn (reciprocal_strictMonoOn hQ)
    (fun x hx => outerHorizon_lt_radiusOf hQ hx) hx₁ hx₂ hρ₁ hρ₂ hr₁₂
  exact ⟨_, _, rfl, rfl, hx₁, h₁₂, hρ₁, hρ₂, hI₁, hIm, hI₂⟩

/-- **The corotation point (subextremal reciprocal, `L = 0`).** For `r₀ > a` and `x₀ = 1/h(r₀)`:
`x₀ > 0`, `ρ(x₀) = r₀`, and `ρ` maps `(0, x₀)` into `(a, r₀)` and `(x₀, ∞)` into `(r₀, ∞)`. -/
theorem reciprocal_corotation_point {M Q r₀ : ℝ} (hQ : |Q| < M) (hr₀ : outerHorizon M Q < r₀) :
    ∃ x₀ : ℝ, x₀ = 1 / staticSolution M Q r₀ ∧ 0 < x₀ ∧ radiusOf M Q x₀ = r₀ ∧
      (∀ x ∈ Ioo 0 x₀, radiusOf M Q x ∈ Ioo (outerHorizon M Q) r₀) ∧
      ∀ x ∈ Ioi x₀, radiusOf M Q x ∈ Ioi r₀ := by
  obtain ⟨hx₀, hρ₀⟩ := reciprocal_inverse hQ hr₀
  obtain ⟨h₁, h₂⟩ := coordinate_point_of_strictMonoOn (reciprocal_strictMonoOn hQ)
    (fun x hx => outerHorizon_lt_radiusOf hQ hx) hx₀ hρ₀
  exact ⟨_, rfl, hx₀, hρ₀, h₁, h₂⟩

/-- **The sign of `K` around corotation (subextremal reciprocal).** For `ω > 0` and
`a < r₀ = e/ω`, with `x₀ = ρ⁻¹(r₀)`: `K(ρ(x)) < 0` on `(0, x₀)` and `K(ρ(x)) > 0` on
`(x₀, ∞)`. -/
theorem reciprocal_corotation_sign {M Q e ω : ℝ} (hQ : |Q| < M) (hω : 0 < ω)
    (hr₀ : outerHorizon M Q < e / ω) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ radiusOf M Q x₀ = e / ω ∧
      (∀ x ∈ Ioo 0 x₀, radialK e ω (radiusOf M Q x) < 0) ∧
      ∀ x ∈ Ioi x₀, 0 < radialK e ω (radiusOf M Q x) := by
  obtain ⟨hx₀, hρ₀⟩ := reciprocal_inverse hQ hr₀
  exact ⟨_, hx₀, hρ₀, corotation_sign_of_strictMonoOn (outerHorizon_nonneg_of_abs_le hQ.le) hω
    (reciprocal_strictMonoOn hQ) (fun x hx => outerHorizon_lt_radiusOf hQ hx) hx₀ hρ₀⟩

/-- The coefficient `F(x) = (K/x²)² − LΔ/x⁴` (at `r = ρ(x)`) of `reciprocal_reduction_L` is `C²`
on `(0, ∞)`. -/
theorem reciprocal_coefficient_contDiffOn {M Q : ℝ} (hQ : |Q| < M) (e ω L : ℝ) :
    ContDiffOn ℝ 2 (fun x => (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
      L * delta M Q (radiusOf M Q x) / x ^ 4) (Ioi 0) := by
  have hρ := reciprocal_contDiffOn hQ
  have hK := (cx_contDiff_radialK e ω).comp_contDiffOn hρ
  have hD := (cx_contDiff_delta M Q).comp_contDiffOn hρ
  exact (((hK.div (contDiffOn_id.pow 2) fun x hx => pow_ne_zero 2 (ne_of_gt hx)).pow 2).sub
    ((contDiffOn_const.mul hD).div (contDiffOn_id.pow 4)
      fun x hx => pow_ne_zero 4 (ne_of_gt hx))).of_le le_top

/-- `F(x) = (K/x²)² − LΔ/x⁴ = x⁻⁴ P(ρ(x))` (all `x`). -/
private theorem cx_reciprocal_F_eq (M Q e ω L x : ℝ) :
    (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 - L * delta M Q (radiusOf M Q x) / x ^ 4 =
      (x ^ 4)⁻¹ * (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)) := by
  ring

/-- **The sign pattern (subextremal reciprocal).** If `a < r₁ < r₂`, `P = K² − LΔ > 0` and
`K < 0` on `(a, r₁)`, `P < 0` on `(r₁, r₂)`, `P > 0` and `K > 0` on `(r₂, ∞)`, then with
`x_j = ρ⁻¹(r_j)` the coefficient `F(x) = (K/x²)² − LΔ/x⁴` of `reciprocal_reduction_L` is positive
on `(0, x₁)` and `(x₂, ∞)` and negative on `(x₁, x₂)`, and `K(ρ(x))` is negative on `(0, x₁)` and
positive on `(x₂, ∞)`. -/
theorem reciprocal_sign_pattern {M Q e ω L r₁ r₂ : ℝ} (hQ : |Q| < M)
    (hr₁ : outerHorizon M Q < r₁) (hr₁₂ : r₁ < r₂)
    (hP₁ : ∀ r ∈ Ioo (outerHorizon M Q) r₁,
      0 < radialK e ω r ^ 2 - L * delta M Q r ∧ radialK e ω r < 0)
    (hPm : ∀ r ∈ Ioo r₁ r₂, radialK e ω r ^ 2 - L * delta M Q r < 0)
    (hP₂ : ∀ r ∈ Ioi r₂, 0 < radialK e ω r ^ 2 - L * delta M Q r ∧ 0 < radialK e ω r) :
    ∃ x₁ x₂ : ℝ, 0 < x₁ ∧ x₁ < x₂ ∧ radiusOf M Q x₁ = r₁ ∧ radiusOf M Q x₂ = r₂ ∧
      (∀ x ∈ Ioo 0 x₁, 0 < (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x) / x ^ 4 ∧ radialK e ω (radiusOf M Q x) < 0) ∧
      (∀ x ∈ Ioo x₁ x₂, (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x) / x ^ 4 < 0) ∧
      ∀ x ∈ Ioi x₂, 0 < (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x) / x ^ 4 ∧ 0 < radialK e ω (radiusOf M Q x) := by
  obtain ⟨hx₁, hρ₁⟩ := reciprocal_inverse hQ hr₁
  obtain ⟨hx₂, hρ₂⟩ := reciprocal_inverse hQ (hr₁.trans hr₁₂)
  obtain ⟨h₁₂, hS₁, hSm, hS₂⟩ := coordinate_signs_of_strictMonoOn
    (F := fun x => (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
      L * delta M Q (radiusOf M Q x) / x ^ 4)
    (c := fun x => (x ^ 4)⁻¹) (P := fun r => radialK e ω r ^ 2 - L * delta M Q r)
    (K := radialK e ω) (reciprocal_strictMonoOn hQ)
    (fun x hx => outerHorizon_lt_radiusOf hQ hx) hx₁ hx₂ hρ₁ hρ₂ hr₁₂
    (fun x _ => cx_reciprocal_F_eq M Q e ω L x) (fun x hx => inv_pos.2 (pow_pos hx 4))
    hP₁ hPm hP₂
  exact ⟨_, _, hx₁, h₁₂, hρ₁, hρ₂, hS₁, hSm, hS₂⟩

/-- **The turning points in the subextremal reciprocal coordinate.** For `ω > 0`, `L > 0` and
`K(a) < 0` there are `0 < x₁ < x₂` with `a < ρ(x₁) < e/ω < ρ(x₂)`, `ρ(x_j) = r_j` the turning
points of `exists_turning_points`, such that `F(x) = (K/x²)² − LΔ/x⁴` (at `r = ρ(x)`) is positive
with `K < 0` on `(0, x₁)`, negative on `(x₁, x₂)`, positive with `K > 0` on `(x₂, ∞)`, vanishes
at `x₁`, `x₂`, and has `F'(x₁) < 0 < F'(x₂)`. -/
theorem reciprocal_turning_points {M Q e ω L : ℝ} (hQ : |Q| < M) (hω : 0 < ω) (hL : 0 < L)
    (hK : radialK e ω (outerHorizon M Q) < 0) :
    ∃ x₁ x₂ : ℝ, 0 < x₁ ∧ x₁ < x₂ ∧ outerHorizon M Q < radiusOf M Q x₁ ∧
      radiusOf M Q x₁ < e / ω ∧ e / ω < radiusOf M Q x₂ ∧
      (∀ x ∈ Ioo 0 x₁, 0 < (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x) / x ^ 4 ∧ radialK e ω (radiusOf M Q x) < 0) ∧
      (∀ x ∈ Ioo x₁ x₂, (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x) / x ^ 4 < 0) ∧
      (∀ x ∈ Ioi x₂, 0 < (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x) / x ^ 4 ∧ 0 < radialK e ω (radiusOf M Q x)) ∧
      (radialK e ω (radiusOf M Q x₁) / x₁ ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x₁) / x₁ ^ 4 = 0 ∧
      (radialK e ω (radiusOf M Q x₂) / x₂ ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x₂) / x₂ ^ 4 = 0 ∧
      deriv (fun x => (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x) / x ^ 4) x₁ < 0 ∧
      0 < deriv (fun x => (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x) / x ^ 4) x₂ := by
  have hM : 0 < M := lt_of_le_of_lt (abs_nonneg Q) hQ
  obtain ⟨r₁, r₂, hr₁, hr₁₀, hr₀₂, -, -, -, -, hP₁, hPm, hP₂, hP0₁, hP0₂, -, -, -, -, hd₁, hd₂⟩ :=
    exists_turning_points hM hQ.le hω hL hK
  have hr₁₂ : r₁ < r₂ := hr₁₀.trans hr₀₂
  obtain ⟨x₁, hx₁, hρ₁⟩ : ∃ x₁, 0 < x₁ ∧ radiusOf M Q x₁ = r₁ := ⟨_, reciprocal_inverse hQ hr₁⟩
  obtain ⟨x₂, hx₂, hρ₂⟩ : ∃ x₂, 0 < x₂ ∧ radiusOf M Q x₂ = r₂ :=
    ⟨_, reciprocal_inverse hQ (hr₁.trans hr₁₂)⟩
  obtain ⟨h₁₂, hS₁, hSm, hS₂⟩ := coordinate_signs_of_strictMonoOn
    (F := fun x => (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
      L * delta M Q (radiusOf M Q x) / x ^ 4)
    (c := fun x => (x ^ 4)⁻¹) (P := fun r => radialK e ω r ^ 2 - L * delta M Q r)
    (K := radialK e ω) (reciprocal_strictMonoOn hQ)
    (fun x hx => outerHorizon_lt_radiusOf hQ hx) hx₁ hx₂ hρ₁ hρ₂ hr₁₂
    (fun x _ => cx_reciprocal_F_eq M Q e ω L x) (fun x hx => inv_pos.2 (pow_pos hx 4))
    hP₁ hPm hP₂
  have hD : ∀ {x r : ℝ}, 0 < x → radiusOf M Q x = r → radialK e ω r ^ 2 - L * delta M Q r = 0 →
      HasDerivAt (fun x => (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x) / x ^ 4)
        ((x ^ 4)⁻¹ * ((2 * radialK e ω r * (2 * ω * r - e) - L * (2 * (r - M))) *
          (delta M Q (radiusOf M Q x) / x ^ 2))) x := fun hx hρ h0 =>
    hasDerivAt_coefficient_at_turning_point (c := fun x => (x ^ 4)⁻¹)
      (P := fun r => radialK e ω r ^ 2 - L * delta M Q r)
      hx (fun x _ => cx_reciprocal_F_eq M Q e ω L x)
      ((hasDerivAt_pow 4 _).inv (pow_ne_zero 4 hx.ne')) (hasDerivAt_radiusOf hQ hx) hρ
      (hasDerivAt_turningPoly M Q e ω L _) h0
  refine ⟨x₁, x₂, hx₁, h₁₂, hρ₁ ▸ hr₁, hρ₁ ▸ hr₁₀, hρ₂ ▸ hr₀₂, hS₁, hSm, hS₂, ?_, ?_, ?_, ?_⟩
  · rw [cx_reciprocal_F_eq, hρ₁, hP0₁, mul_zero]
  · rw [cx_reciprocal_F_eq, hρ₂, hP0₂, mul_zero]
  · rw [(hD hx₁ hρ₁ hP0₁).deriv]
    exact mul_neg_of_pos_of_neg (inv_pos.2 (pow_pos hx₁ 4))
      (mul_neg_of_neg_of_pos hd₁ (reciprocal_deriv_pos hQ hx₁))
  · rw [(hD hx₂ hρ₂ hP0₂).deriv]
    exact mul_pos (inv_pos.2 (pow_pos hx₂ 4)) (mul_pos hd₂ (reciprocal_deriv_pos hQ hx₂))

/-! ### Subextremal, constant normalization: `ρ(y) = radiusOf M Q (1/y)` -/

/-- `ρ'(y) = −Δ(ρ(y)) < 0` for `y > 0`. -/
theorem constant_deriv_neg {M Q : ℝ} (hQ : |Q| < M) {y : ℝ} (hy : 0 < y) :
    -delta M Q (radiusOf M Q (1 / y)) < 0 :=
  neg_neg_of_pos (delta_pos hQ (outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy)))

/-- `ρ(y) = radiusOf M Q (1/y)` is strictly decreasing on `(0, ∞)`. -/
theorem constant_strictAntiOn {M Q : ℝ} (hQ : |Q| < M) :
    StrictAntiOn (fun y : ℝ => radiusOf M Q (1 / y)) (Ioi 0) := fun _ ha _ _ hab =>
  reciprocal_strictMonoOn hQ (one_div_pos.2 (ha.trans hab)) (one_div_pos.2 ha)
    (one_div_lt_one_div_of_lt ha hab)

/-- The inverse of `ρ(y) = radiusOf M Q (1/y)` is `h`: for `r > a`, `h(r) > 0` and
`ρ(h(r)) = r`. -/
theorem constant_inverse {M Q : ℝ} (hQ : |Q| < M) {r : ℝ} (hr : outerHorizon M Q < r) :
    0 < staticSolution M Q r ∧ radiusOf M Q (1 / staticSolution M Q r) = r :=
  ⟨staticSolution_pos hQ hr, radiusOf_one_div_staticSolution hQ hr⟩

/-- **The subextremal constant coordinate.** `ρ(y) = radiusOf M Q (1/y)` is a strictly decreasing
bijection `(0, ∞) → (a, ∞)` with inverse `h`, continuous and `C²` on `(0, ∞)` (in fact smooth,
`contDiffOn_radiusOf_one_div`), with `ρ'(y) = −Δ(ρ(y)) < 0`. -/
theorem constant_bijective {M Q : ℝ} (hQ : |Q| < M) :
    StrictAntiOn (fun y : ℝ => radiusOf M Q (1 / y)) (Ioi 0) ∧
      BijOn (fun y : ℝ => radiusOf M Q (1 / y)) (Ioi 0) (Ioi (outerHorizon M Q)) ∧
      (∀ r ∈ Ioi (outerHorizon M Q), 0 < staticSolution M Q r ∧
        radiusOf M Q (1 / staticSolution M Q r) = r) ∧
      (∀ y ∈ Ioi (0 : ℝ), staticSolution M Q (radiusOf M Q (1 / y)) = y) ∧
      ContinuousOn (fun y : ℝ => radiusOf M Q (1 / y)) (Ioi 0) ∧
      ContDiffOn ℝ 2 (fun y : ℝ => radiusOf M Q (1 / y)) (Ioi 0) ∧
      ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => radiusOf M Q (1 / t))
        (-delta M Q (radiusOf M Q (1 / y))) y ∧ -delta M Q (radiusOf M Q (1 / y)) < 0 := by
  have hanti := constant_strictAntiOn hQ
  have hcd := contDiffOn_radiusOf_one_div hQ
  refine ⟨hanti, ⟨fun y hy => outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy), hanti.injOn,
    fun r hr => ?_⟩, fun r hr => constant_inverse hQ hr, fun y hy => ?_, hcd.continuousOn,
    hcd.of_le le_top, fun y hy => ⟨hasDerivAt_radiusOf_one_div hQ hy, constant_deriv_neg hQ hy⟩⟩
  · obtain ⟨h0, h1⟩ := constant_inverse hQ hr
    exact ⟨_, h0, h1⟩
  · rw [staticSolution_radiusOf hQ (one_div_pos.2 hy), one_div_one_div]

/-- **Vanishing transfers back (subextremal constant).** If `U(y) = R(ρ(y))` vanishes on
`(0, ∞)`, then `R = 0` on `(a, ∞)`. -/
theorem constant_transfer_zero {M Q : ℝ} (hQ : |Q| < M) {R : ℝ → ℂ}
    (hU : ∀ y ∈ Ioi (0 : ℝ), R (radiusOf M Q (1 / y)) = 0) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  intro r hr
  obtain ⟨h0, h1⟩ := constant_inverse hQ hr
  have h := hU _ h0
  rw [h1] at h
  exact h

/-- **The coordinate intervals (subextremal constant).** For `a < r₁ < r₂` and `y_j = h(r_j)`:
`0 < y₂ < y₁`, `ρ(y_j) = r_j`, and `ρ` maps `(0, y₂)`, `(y₂, y₁)`, `(y₁, ∞)` into `(r₂, ∞)`,
`(r₁, r₂)`, `(a, r₁)`. -/
theorem constant_interval_preimage {M Q r₁ r₂ : ℝ} (hQ : |Q| < M)
    (hr₁ : outerHorizon M Q < r₁) (hr₁₂ : r₁ < r₂) :
    ∃ y₁ y₂ : ℝ, y₁ = staticSolution M Q r₁ ∧ y₂ = staticSolution M Q r₂ ∧
      0 < y₂ ∧ y₂ < y₁ ∧ radiusOf M Q (1 / y₁) = r₁ ∧ radiusOf M Q (1 / y₂) = r₂ ∧
      (∀ y ∈ Ioo 0 y₂, radiusOf M Q (1 / y) ∈ Ioi r₂) ∧
      (∀ y ∈ Ioo y₂ y₁, radiusOf M Q (1 / y) ∈ Ioo r₁ r₂) ∧
      ∀ y ∈ Ioi y₁, radiusOf M Q (1 / y) ∈ Ioo (outerHorizon M Q) r₁ := by
  obtain ⟨hy₁, hρ₁⟩ := constant_inverse hQ hr₁
  obtain ⟨hy₂, hρ₂⟩ := constant_inverse hQ (hr₁.trans hr₁₂)
  obtain ⟨h₂₁, hI₂, hIm, hI₁⟩ := coordinate_intervals_of_strictAntiOn
    (ρ := fun y : ℝ => radiusOf M Q (1 / y))
    (constant_strictAntiOn hQ) (fun y hy => outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy))
    hy₁ hy₂ hρ₁ hρ₂ hr₁₂
  exact ⟨_, _, rfl, rfl, hy₂, h₂₁, hρ₁, hρ₂, hI₂, hIm, hI₁⟩

/-- **The corotation point (subextremal constant, `L = 0`).** For `r₀ > a` and `y₀ = h(r₀)`:
`y₀ > 0`, `ρ(y₀) = r₀`, and `ρ` maps `(0, y₀)` into `(r₀, ∞)` and `(y₀, ∞)` into `(a, r₀)`. -/
theorem constant_corotation_point {M Q r₀ : ℝ} (hQ : |Q| < M) (hr₀ : outerHorizon M Q < r₀) :
    ∃ y₀ : ℝ, y₀ = staticSolution M Q r₀ ∧ 0 < y₀ ∧ radiusOf M Q (1 / y₀) = r₀ ∧
      (∀ y ∈ Ioo 0 y₀, radiusOf M Q (1 / y) ∈ Ioi r₀) ∧
      ∀ y ∈ Ioi y₀, radiusOf M Q (1 / y) ∈ Ioo (outerHorizon M Q) r₀ := by
  obtain ⟨hy₀, hρ₀⟩ := constant_inverse hQ hr₀
  obtain ⟨h₁, h₂⟩ := coordinate_point_of_strictAntiOn (ρ := fun y : ℝ => radiusOf M Q (1 / y))
    (constant_strictAntiOn hQ) (fun y hy => outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy))
    hy₀ hρ₀
  exact ⟨_, rfl, hy₀, hρ₀, h₁, h₂⟩

/-- **The sign of `K` around corotation (subextremal constant).** For `ω > 0` and `a < r₀ = e/ω`,
with `y₀ = ρ⁻¹(r₀)`: `K(ρ(y)) > 0` on `(0, y₀)` and `K(ρ(y)) < 0` on `(y₀, ∞)`. -/
theorem constant_corotation_sign {M Q e ω : ℝ} (hQ : |Q| < M) (hω : 0 < ω)
    (hr₀ : outerHorizon M Q < e / ω) :
    ∃ y₀ : ℝ, 0 < y₀ ∧ radiusOf M Q (1 / y₀) = e / ω ∧
      (∀ y ∈ Ioo 0 y₀, 0 < radialK e ω (radiusOf M Q (1 / y))) ∧
      ∀ y ∈ Ioi y₀, radialK e ω (radiusOf M Q (1 / y)) < 0 := by
  obtain ⟨hy₀, hρ₀⟩ := constant_inverse hQ hr₀
  exact ⟨_, hy₀, hρ₀, corotation_sign_of_strictAntiOn (ρ := fun y : ℝ => radiusOf M Q (1 / y))
    (outerHorizon_nonneg_of_abs_le hQ.le) hω (constant_strictAntiOn hQ)
    (fun y hy => outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy)) hy₀ hρ₀⟩

/-- The coefficient `F(y) = K² − LΔ` (at `r = ρ(y)`) of `constant_reduction_L` is `C²` on
`(0, ∞)`. -/
theorem constant_coefficient_contDiffOn {M Q : ℝ} (hQ : |Q| < M) (e ω L : ℝ) :
    ContDiffOn ℝ 2 (fun y => radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
      L * delta M Q (radiusOf M Q (1 / y))) (Ioi 0) := by
  have hρ := contDiffOn_radiusOf_one_div hQ
  have hK := (cx_contDiff_radialK e ω).comp_contDiffOn hρ
  have hD := (cx_contDiff_delta M Q).comp_contDiffOn hρ
  exact ((hK.pow 2).sub (contDiffOn_const.mul hD)).of_le le_top

/-- **The sign pattern (subextremal constant).** If `a < r₁ < r₂`, `P = K² − LΔ > 0` and `K < 0`
on `(a, r₁)`, `P < 0` on `(r₁, r₂)`, `P > 0` and `K > 0` on `(r₂, ∞)`, then with `y_j = ρ⁻¹(r_j)`
(so `y₂ < y₁`) the coefficient `F(y) = K² − LΔ` (at `r = ρ(y)`) of `constant_reduction_L` is
positive with `K > 0` on `(0, y₂)`, negative on `(y₂, y₁)`, positive with `K < 0` on
`(y₁, ∞)`. -/
theorem constant_sign_pattern {M Q e ω L r₁ r₂ : ℝ} (hQ : |Q| < M)
    (hr₁ : outerHorizon M Q < r₁) (hr₁₂ : r₁ < r₂)
    (hP₁ : ∀ r ∈ Ioo (outerHorizon M Q) r₁,
      0 < radialK e ω r ^ 2 - L * delta M Q r ∧ radialK e ω r < 0)
    (hPm : ∀ r ∈ Ioo r₁ r₂, radialK e ω r ^ 2 - L * delta M Q r < 0)
    (hP₂ : ∀ r ∈ Ioi r₂, 0 < radialK e ω r ^ 2 - L * delta M Q r ∧ 0 < radialK e ω r) :
    ∃ y₁ y₂ : ℝ, 0 < y₂ ∧ y₂ < y₁ ∧ radiusOf M Q (1 / y₁) = r₁ ∧ radiusOf M Q (1 / y₂) = r₂ ∧
      (∀ y ∈ Ioo 0 y₂, 0 < radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / y)) ∧ 0 < radialK e ω (radiusOf M Q (1 / y))) ∧
      (∀ y ∈ Ioo y₂ y₁, radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / y)) < 0) ∧
      ∀ y ∈ Ioi y₁, 0 < radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / y)) ∧ radialK e ω (radiusOf M Q (1 / y)) < 0 := by
  obtain ⟨hy₁, hρ₁⟩ := constant_inverse hQ hr₁
  obtain ⟨hy₂, hρ₂⟩ := constant_inverse hQ (hr₁.trans hr₁₂)
  obtain ⟨h₂₁, hS₂, hSm, hS₁⟩ := coordinate_signs_of_strictAntiOn
    (ρ := fun y : ℝ => radiusOf M Q (1 / y))
    (F := fun y => radialK e ω (radiusOf M Q (1 / y)) ^ 2 - L * delta M Q (radiusOf M Q (1 / y)))
    (c := fun _ => 1) (P := fun r => radialK e ω r ^ 2 - L * delta M Q r) (K := radialK e ω)
    (constant_strictAntiOn hQ) (fun y hy => outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy))
    hy₁ hy₂ hρ₁ hρ₂ hr₁₂ (fun y _ => (one_mul _).symm) (fun _ _ => one_pos) hP₁ hPm hP₂
  exact ⟨_, _, hy₂, h₂₁, hρ₁, hρ₂, hS₂, hSm, hS₁⟩

/-- **The turning points in the subextremal constant coordinate.** For `ω > 0`, `L > 0` and
`K(a) < 0` there are `0 < y₂ < y₁` with `a < ρ(y₁) < e/ω < ρ(y₂)`, `ρ(y_j) = r_j` the turning
points of `exists_turning_points`, such that `F(y) = K² − LΔ` (at `r = ρ(y)`) is positive with
`K > 0` on `(0, y₂)`, negative on `(y₂, y₁)`, positive with `K < 0` on `(y₁, ∞)`, vanishes at
`y₁`, `y₂`, and has `F'(y₂) < 0 < F'(y₁)`. For `eqOn_zero_of_global_current_L` take
`x₁ := y₂`, `x₂ := y₁`. -/
theorem constant_turning_points {M Q e ω L : ℝ} (hQ : |Q| < M) (hω : 0 < ω) (hL : 0 < L)
    (hK : radialK e ω (outerHorizon M Q) < 0) :
    ∃ y₁ y₂ : ℝ, 0 < y₂ ∧ y₂ < y₁ ∧ outerHorizon M Q < radiusOf M Q (1 / y₁) ∧
      radiusOf M Q (1 / y₁) < e / ω ∧ e / ω < radiusOf M Q (1 / y₂) ∧
      (∀ y ∈ Ioo 0 y₂, 0 < radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / y)) ∧ 0 < radialK e ω (radiusOf M Q (1 / y))) ∧
      (∀ y ∈ Ioo y₂ y₁, radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / y)) < 0) ∧
      (∀ y ∈ Ioi y₁, 0 < radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / y)) ∧ radialK e ω (radiusOf M Q (1 / y)) < 0) ∧
      radialK e ω (radiusOf M Q (1 / y₁)) ^ 2 - L * delta M Q (radiusOf M Q (1 / y₁)) = 0 ∧
      radialK e ω (radiusOf M Q (1 / y₂)) ^ 2 - L * delta M Q (radiusOf M Q (1 / y₂)) = 0 ∧
      deriv (fun y => radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / y))) y₂ < 0 ∧
      0 < deriv (fun y => radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / y))) y₁ := by
  have hM : 0 < M := lt_of_le_of_lt (abs_nonneg Q) hQ
  obtain ⟨r₁, r₂, hr₁, hr₁₀, hr₀₂, -, -, -, -, hP₁, hPm, hP₂, hP0₁, hP0₂, -, -, -, -, hd₁, hd₂⟩ :=
    exists_turning_points hM hQ.le hω hL hK
  have hr₁₂ : r₁ < r₂ := hr₁₀.trans hr₀₂
  obtain ⟨y₁, hy₁, hρ₁⟩ : ∃ y₁, 0 < y₁ ∧ radiusOf M Q (1 / y₁) = r₁ :=
    ⟨_, constant_inverse hQ hr₁⟩
  obtain ⟨y₂, hy₂, hρ₂⟩ : ∃ y₂, 0 < y₂ ∧ radiusOf M Q (1 / y₂) = r₂ :=
    ⟨_, constant_inverse hQ (hr₁.trans hr₁₂)⟩
  obtain ⟨h₂₁, hS₂, hSm, hS₁⟩ := coordinate_signs_of_strictAntiOn
    (ρ := fun y : ℝ => radiusOf M Q (1 / y))
    (F := fun y => radialK e ω (radiusOf M Q (1 / y)) ^ 2 - L * delta M Q (radiusOf M Q (1 / y)))
    (c := fun _ => 1) (P := fun r => radialK e ω r ^ 2 - L * delta M Q r) (K := radialK e ω)
    (constant_strictAntiOn hQ) (fun y hy => outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy))
    hy₁ hy₂ hρ₁ hρ₂ hr₁₂ (fun y _ => (one_mul _).symm) (fun _ _ => one_pos) hP₁ hPm hP₂
  have hD : ∀ {y r : ℝ}, 0 < y → radiusOf M Q (1 / y) = r →
      radialK e ω r ^ 2 - L * delta M Q r = 0 →
      HasDerivAt (fun y => radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / y)))
        (1 * ((2 * radialK e ω r * (2 * ω * r - e) - L * (2 * (r - M))) *
          -delta M Q (radiusOf M Q (1 / y)))) y := fun hy hρ h0 =>
    hasDerivAt_coefficient_at_turning_point (c := fun _ => 1)
      (P := fun r => radialK e ω r ^ 2 - L * delta M Q r)
      hy (fun y _ => (one_mul _).symm) (hasDerivAt_const _ _) (hasDerivAt_radiusOf_one_div hQ hy)
      hρ (hasDerivAt_turningPoly M Q e ω L _) h0
  refine ⟨y₁, y₂, hy₂, h₂₁, hρ₁ ▸ hr₁, hρ₁ ▸ hr₁₀, hρ₂ ▸ hr₀₂, hS₂, hSm, hS₁, ?_, ?_, ?_, ?_⟩
  · rw [hρ₁, hP0₁]
  · rw [hρ₂, hP0₂]
  · rw [(hD hy₂ hρ₂ hP0₂).deriv, one_mul]
    exact mul_neg_of_pos_of_neg hd₂ (constant_deriv_neg hQ hy₂)
  · rw [(hD hy₁ hρ₁ hP0₁).deriv, one_mul]
    exact mul_pos_of_neg_of_neg hd₁ (constant_deriv_neg hQ hy₁)

end ModeStability.AllAngular

end
