module

public import Mathlib
public import ModeStability.AllAngular.AngularReduction
public import ModeStability.AllAngular.CoordinateCoefficientsAux

/-!
# Lemma 2.2 and Proposition 3.1 in the two extremal coordinate systems

Source: the all-angular research notes in preparation, pp. 2–4: (2.1)–(2.7) with `δ = 0`,
Lemma 2.2, (3.2) and Proposition 3.1. In the
extremal case `|Q| = M` one has `a = b = M`, `Δ = (r − M)²` and `h = 1/(r − M)` (2.1). The
reductions (2.4) are `ModeStability.AllAngular.extremal_reciprocal_reduction_L` and
`extremal_constant_reduction_L`; the subextremal systems are in
`ModeStability.AllAngular.CoordinateCoefficients`, which states the five items in detail.

* extremal reciprocal (`g = h`, `x = r − M ∈ (0, ∞)`, `r = M + x`, `r' = Δg² = 1`):
  `F = (K/x²)² − L/x²`, `f̂ = sgn(K) (1/x)² √(K² − Lx²)`;
* extremal constant (`g = 1`, reflected `y = h = 1/(r − M)`, `r = M + 1/y`, `r' = −Δ = −1/y²`):
  `F = K² − L/y²`, `f̂ = −sgn(K) √(K² − L/y²)`.

Here `χ = −Δg'/g` is `z = r − M` (so `ε = 0`) resp. `0`, and the bounds (2.8) needed by
Lemma 2.2 hold trivially.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

open CoefficientIdentities CoordinateCoefficients

/-! ### Helpers -/

/-- `ω · (e/ω) = e`. -/
private theorem cc_mul_div {e ω : ℝ} (hω : 0 < ω) : ω * (e / ω) = e :=
  mul_div_cancel₀ e hω.ne'

/-- Extremal `h = 1/(r − M)`: `h' = −1/Δ` with `Δ = (r − M)²`, near `r > M`. -/
private theorem cc_ext_hg {M Q : ℝ} (hQ : |Q| = M) {r : ℝ} (hr : M < r) :
    ∀ᶠ s in 𝓝 r, HasDerivAt (fun t : ℝ => 1 / (t - M)) (-1 / delta M Q s) s := by
  filter_upwards [lt_mem_nhds hr] with s hs
  have hne : s - M ≠ 0 := (sub_pos.2 hs).ne'
  rw [delta_of_abs_eq hQ]
  refine ((hasDerivAt_const s (1 : ℝ)).div ((hasDerivAt_id' s).sub_const M) hne).congr_deriv ?_
  ring

/-- `a = M < M + x` for `x > 0` in the extremal case. -/
private theorem cc_ext_lt {M Q : ℝ} (hQ : |Q| = M) {x : ℝ} (hx : 0 < x) :
    outerHorizon M Q < M + x := by
  rw [outerHorizon_of_abs_eq hQ]
  linarith

/-- `M² − Q² = 0` in the extremal case. -/
private theorem cc_ext_sq {M Q : ℝ} (hQ : |Q| = M) : M ^ 2 - Q ^ 2 = 0 := by
  rw [← sq_abs Q, hQ, sub_self]

/-! ### Extremal, reciprocal normalization -/

/-- `ρ' = 1 = Δ h²` along `r = M + x`, near `x > 0`. -/
private theorem cc_er_hρ {M Q : ℝ} (hQ : |Q| = M) {x : ℝ} (hx : 0 < x) :
    ∀ᶠ y in 𝓝 x, HasDerivAt (fun t => M + t)
      (1 * (delta M Q (M + y) * (1 / (M + y - M)) ^ 2)) y := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  refine ((hasDerivAt_id' y).const_add M).congr_deriv ?_
  rw [delta_of_abs_eq hQ, add_sub_cancel_left]
  have : y ≠ 0 := (show (0 : ℝ) < y from hy).ne'
  field_simp

/-- `(K/x²)² − L/x² = x⁻⁴ (K² − Lx²)` (for `x = 0` both sides vanish). -/
private theorem cc_er_F (K L x : ℝ) :
    (K / x ^ 2) ^ 2 - L / x ^ 2 = ((1 / x) ^ 2) ^ 2 * (K ^ 2 - L * x ^ 2) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · field_simp

/-- Pointwise form of (3.2) in the extremal reciprocal coordinate: `f̂ = sgn(K) √F`. -/
private theorem cc_er_eq (M e ω L x : ℝ) :
    (SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
        Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) =
      (SignType.sign (radialK e ω (M + x)) : ℝ) *
        Real.sqrt ((radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2) := by
  rw [cc_er_F, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

/-- (3.2), extremal reciprocal: `f̂² = F` wherever `F ≥ 0`. -/
theorem extremal_reciprocal_fhat_sq {M e ω L : ℝ} (hL : 0 ≤ L) {x : ℝ}
    (hF : 0 ≤ (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2) :
    ((SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
        Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2)) ^ 2 =
      (radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2 := by
  rw [cc_er_eq]
  refine sq_sign_mul_sqrt hF fun hK => le_antisymm ?_ hF
  rw [hK]
  have : 0 ≤ L / x ^ 2 := div_nonneg hL (sq_nonneg x)
  linarith [show ((0 : ℝ) / x ^ 2) ^ 2 = 0 by simp]

/-- Proposition 3.1, extremal reciprocal normalization (`r₀ ≥ 2M`, `g = h = 1/(r − M)`,
`x = r − M`): at `x > 0` with `Lx² < K²` at `r = M + x`, `f̂ = sgn(K)(1/x)²√(K² − Lx²)` is `C²`,
`f̂' > 0` and `2f̂'² − f̂f̂'' > 0`. -/
theorem extremal_reciprocal_fhat_props {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| = M)
    (hω : 0 < ω) (hL : 0 ≤ L) (hr₀ : outerHorizon M Q < e / ω) (h2M : 2 * M ≤ e / ω) {x : ℝ}
    (hx : 0 < x) (hK : L * x ^ 2 < radialK e ω (M + x) ^ 2) :
    ContDiffAt ℝ 2 (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x ∧
      0 < deriv (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x ∧
      0 < 2 * deriv (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
          Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x ^ 2 -
        (SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
            Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) *
          deriv (deriv fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
            Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x := by
  have hr := cc_ext_lt hQ hx
  have hK' : L * delta M Q (M + x) < radialK e ω (M + x) ^ 2 := by
    rw [delta_of_abs_eq hQ, add_sub_cancel_left]
    exact hK
  have hε : M + x - M - x = 0 := by ring
  obtain ⟨hH, hA⟩ := scalar_positivity_reciprocal hM hQ.le hω hr₀ h2M hr hx (by rw [hε])
    (by rw [hε]; exact Real.sqrt_nonneg _) (by rw [hε, zero_mul, cc_ext_sq hQ])
  rw [cc_mul_div hω] at hH hA
  have hf : (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) =ᶠ[𝓝 x]
      fun y => 1 * effectiveKAux M Q e ω L (fun r => 1 / (r - M)) (M + y) :=
    Eventually.of_forall fun y => by
      simp only [effectiveKAux]
      rw [delta_of_abs_eq hQ, add_sub_cancel_left, one_mul]
  have hg0 : 0 < 1 / (M + x - M) := by
    rw [add_sub_cancel_left]
    exact one_div_pos.2 hx
  have hgC : ContDiffAt ℝ 2 (fun r : ℝ => 1 / (r - M)) (M + x) :=
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (by simp [hx.ne'])
  exact coordinate_khat_props (g := fun r => 1 / (r - M)) (ρ := fun t => M + t) (one_mul 1) hM
    hQ.le hω hL hr₀ hr hg0 hK' (cc_ext_hg hQ (by linarith)) hgC (cc_er_hρ hQ hx)
    (contDiffAt_const.add contDiffAt_id) hf
    (by rw [neg_neg, add_sub_cancel_left, one_div_one_div]) hx.le (by linarith) hH hA

/-- Lemma 2.2, extremal reciprocal normalization, at `L = 0`: `f̂ = K/x²`, and `f̂` is `C²`,
`f̂' > 0`, `2f̂'² − f̂f̂'' > 0` at every `x > 0` (including the corotation point). -/
theorem extremal_reciprocal_fhat_L0 {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω)
    (hL0 : L = 0) (hr₀ : outerHorizon M Q < e / ω) (h2M : 2 * M ≤ e / ω) :
    (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) =
      (fun t => radialK e ω (M + t) / t ^ 2) ∧
    ∀ x ∈ Ioi (0 : ℝ),
      ContDiffAt ℝ 2 (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
          Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x ∧
        0 < deriv (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
          Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x ∧
        0 < 2 * deriv (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
            Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x ^ 2 -
          (SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
              Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2) *
            deriv (deriv fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
              Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) x := by
  have heq : (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2)) =
      (fun t => radialK e ω (M + t) / t ^ 2) := by
    funext t
    rw [hL0, mul_right_comm, sign_mul_sqrt_L0]
    ring
  refine ⟨heq, fun x hx => ?_⟩
  have hx0 : 0 < x := hx
  suffices h : ∀ f : ℝ → ℝ, f = (fun t => radialK e ω (M + t) / t ^ 2) →
      ContDiffAt ℝ 2 f x ∧ 0 < deriv f x ∧ 0 < 2 * deriv f x ^ 2 - f x * deriv (deriv f) x from
    h _ heq
  rintro f rfl
  have hr := cc_ext_lt hQ hx0
  have hε : M + x - M - x = 0 := by ring
  obtain ⟨hH, hA⟩ := scalar_positivity_reciprocal hM hQ.le hω hr₀ h2M hr hx0 (by rw [hε])
    (by rw [hε]; exact Real.sqrt_nonneg _) (by rw [hε, zero_mul, cc_ext_sq hQ])
  rw [cc_mul_div hω] at hH hA
  have hf : (fun t => radialK e ω (M + t) / t ^ 2) =ᶠ[𝓝 x]
      fun y => 1 * ((1 / (M + y - M)) ^ 2 * radialK e ω (M + y)) :=
    Eventually.of_forall fun y => by
      beta_reduce
      rw [add_sub_cancel_left]
      ring
  have hg0 : 0 < 1 / (M + x - M) := by
    rw [add_sub_cancel_left]
    exact one_div_pos.2 hx0
  have hgC : ContDiffAt ℝ 2 (fun r : ℝ => 1 / (r - M)) (M + x) :=
    contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (by simp [hx0.ne'])
  exact coordinate_k_props (g := fun r => 1 / (r - M)) (ρ := fun t => M + t) (one_mul 1) hr hg0
    (cc_ext_hg hQ (by linarith)) hgC (cc_er_hρ hQ hx0) (contDiffAt_const.add contDiffAt_id) hf
    (by rw [neg_neg, add_sub_cancel_left, one_div_one_div]) hH hA

/-- Item 5, extremal reciprocal: on a set where `sgn K(M + ·) = s`, `f̂ = s√F`. -/
theorem extremal_reciprocal_fhat_eq_sign_sqrt {M e ω L s : ℝ} {S : Set ℝ}
    (hs : ∀ x ∈ S, (SignType.sign (radialK e ω (M + x)) : ℝ) = s) :
    EqOn (fun t => (SignType.sign (radialK e ω (M + t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (M + t) ^ 2 - L * t ^ 2))
      (fun t => s * Real.sqrt ((radialK e ω (M + t) / t ^ 2) ^ 2 - L / t ^ 2)) S := by
  intro x hx
  simp only
  rw [cc_er_eq, hs x hx]

/-! ### Extremal, constant normalization -/

/-- `ρ' = −1/y² = −Δ` along `r = M + 1/y`. -/
private theorem cc_ec_hρ' (M : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => M + 1 / t) (-(y ^ 2)⁻¹) y := by
  simpa only [one_div] using (hasDerivAt_inv hy.ne').const_add M

/-- `ρ' = −Δ · 1²` along `r = M + 1/y`, near `y > 0`. -/
private theorem cc_ec_hρ {M Q : ℝ} (hQ : |Q| = M) {x : ℝ} (hx : 0 < x) :
    ∀ᶠ y in 𝓝 x, HasDerivAt (fun t : ℝ => M + 1 / t) (-1 * (delta M Q (M + 1 / y) * 1 ^ 2)) y := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  refine (cc_ec_hρ' M hy).congr_deriv ?_
  rw [delta_of_abs_eq hQ, add_sub_cancel_left]
  ring

/-- `L/y² = LΔ(M + 1/y)` in the extremal case. -/
private theorem cc_ec_delta {M Q : ℝ} (hQ : |Q| = M) (L y : ℝ) :
    L * delta M Q (M + 1 / y) = L / y ^ 2 := by
  rw [delta_of_abs_eq hQ, add_sub_cancel_left]
  ring

/-- (3.2), extremal constant: `f̂² = F` wherever `F ≥ 0`. -/
theorem extremal_constant_fhat_sq {M e ω L : ℝ} (hL : 0 ≤ L) {y : ℝ}
    (hF : 0 ≤ radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2) :
    (-((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2))) ^ 2 =
      radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2 := by
  rw [neg_sq]
  refine sq_sign_mul_sqrt hF fun hK => le_antisymm ?_ hF
  rw [hK]
  have : 0 ≤ L / y ^ 2 := div_nonneg hL (sq_nonneg y)
  linarith [show (0 : ℝ) ^ 2 = 0 by simp]

/-- Proposition 3.1, extremal constant normalization (`a < r₀ < 2M`, `g = 1`, reflected
`y = 1/(r − M)`): at `y > 0` with `L/y² < K²` at `r = M + 1/y`, `f̂ = −sgn(K)√(K² − L/y²)` is
`C²`, `f̂' > 0` and `2f̂'² − f̂f̂'' > 0`. -/
theorem extremal_constant_fhat_props {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω)
    (hL : 0 ≤ L) (hr₀ : outerHorizon M Q < e / ω) (h2M : e / ω < 2 * M) {y : ℝ} (hy : 0 < y)
    (hK : L / y ^ 2 < radialK e ω (M + 1 / y) ^ 2) :
    ContDiffAt ℝ 2 (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y ∧
      0 < deriv (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y ∧
      0 < 2 * deriv (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
          Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y ^ 2 -
        -((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) *
            Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2)) *
          deriv (deriv fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
            Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y := by
  have hr := cc_ext_lt hQ (one_div_pos.2 hy)
  have hK' : L * delta M Q (M + 1 / y) < radialK e ω (M + 1 / y) ^ 2 := by
    rw [cc_ec_delta hQ]
    exact hK
  obtain ⟨hH, hA⟩ := scalar_positivity_constant hM hQ.le hω hr₀ h2M hr
  rw [cc_mul_div hω] at hH hA
  have hH' : 0 < delta M Q (M + 1 / y) * (2 * ω * (M + 1 / y) - e) -
      2 * 0 * radialK e ω (M + 1 / y) := by linarith
  have hA' : 0 < 2 * delta M Q (M + 1 / y) ^ 2 * (2 * ω * (M + 1 / y) - e) ^ 2 -
      2 * delta M Q (M + 1 / y) * (0 + (M + 1 / y - M)) * radialK e ω (M + 1 / y) *
        (2 * ω * (M + 1 / y) - e) -
      delta M Q (M + 1 / y) ^ 2 * radialK e ω (M + 1 / y) * (2 * ω) +
      2 * 0 ^ 2 * radialK e ω (M + 1 / y) ^ 2 := by linarith
  have hf : (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) =ᶠ[𝓝 y]
      fun t => -1 * effectiveKAux M Q e ω L (fun _ => 1) (M + 1 / t) :=
    Eventually.of_forall fun t => by
      simp only [effectiveKAux]
      rw [cc_ec_delta hQ]
      ring
  exact coordinate_khat_props (g := fun _ => 1) (ρ := fun t => M + 1 / t) (by norm_num) hM hQ.le
    hω hL hr₀ hr one_pos hK' (eventually_hasDerivAt_one M Q _) contDiffAt_const (cc_ec_hρ hQ hy)
    (contDiffAt_const.add (contDiffAt_const.div contDiffAt_id hy.ne')) hf
    (by rw [neg_zero, zero_div]) le_rfl (sub_pos_of_outerHorizon_lt hr).le hH' hA'

/-- Lemma 2.2, extremal constant normalization, at `L = 0`: `f̂ = −K`, and `f̂` is `C²`,
`f̂' > 0`, `2f̂'² − f̂f̂'' > 0` at every `y > 0`. -/
theorem extremal_constant_fhat_L0 {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω)
    (hL0 : L = 0) (hr₀ : outerHorizon M Q < e / ω) (h2M : e / ω < 2 * M) :
    (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) =
      (fun t => -radialK e ω (M + 1 / t)) ∧
    ∀ y ∈ Ioi (0 : ℝ),
      ContDiffAt ℝ 2 (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
          Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y ∧
        0 < deriv (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
          Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y ∧
        0 < 2 * deriv (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
            Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y ^ 2 -
          -((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) *
              Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2)) *
            deriv (deriv fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
              Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) y := by
  have heq : (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2))) =
      (fun t => -radialK e ω (M + 1 / t)) := by
    funext t
    rw [hL0, zero_div, sub_zero, Real.sqrt_sq_eq_abs, sign_mul_abs]
  refine ⟨heq, fun y hy => ?_⟩
  have hy0 : 0 < y := hy
  suffices h : ∀ f : ℝ → ℝ, f = (fun t => -radialK e ω (M + 1 / t)) →
      ContDiffAt ℝ 2 f y ∧ 0 < deriv f y ∧ 0 < 2 * deriv f y ^ 2 - f y * deriv (deriv f) y from
    h _ heq
  rintro f rfl
  have hr := cc_ext_lt hQ (one_div_pos.2 hy0)
  obtain ⟨hH, hA⟩ := scalar_positivity_constant hM hQ.le hω hr₀ h2M hr
  rw [cc_mul_div hω] at hH hA
  have hH' : 0 < delta M Q (M + 1 / y) * (2 * ω * (M + 1 / y) - e) -
      2 * 0 * radialK e ω (M + 1 / y) := by linarith
  have hA' : 0 < 2 * delta M Q (M + 1 / y) ^ 2 * (2 * ω * (M + 1 / y) - e) ^ 2 -
      2 * delta M Q (M + 1 / y) * (0 + (M + 1 / y - M)) * radialK e ω (M + 1 / y) *
        (2 * ω * (M + 1 / y) - e) -
      delta M Q (M + 1 / y) ^ 2 * radialK e ω (M + 1 / y) * (2 * ω) +
      2 * 0 ^ 2 * radialK e ω (M + 1 / y) ^ 2 := by linarith
  have hf : (fun t => -radialK e ω (M + 1 / t)) =ᶠ[𝓝 y]
      fun t => -1 * ((1 : ℝ) ^ 2 * radialK e ω (M + 1 / t)) :=
    Eventually.of_forall fun t => by ring
  exact coordinate_k_props (g := fun _ => 1) (ρ := fun t => M + 1 / t) (by norm_num) hr one_pos
    (eventually_hasDerivAt_one M Q _) contDiffAt_const (cc_ec_hρ hQ hy0)
    (contDiffAt_const.add (contDiffAt_const.div contDiffAt_id hy0.ne')) hf
    (by rw [neg_zero, zero_div]) hH' hA'

/-- Item 5, extremal constant: on a set where `sgn K(M + 1/·) = s`, `f̂ = −s√F`. -/
theorem extremal_constant_fhat_eq_sign_sqrt {M e ω L s : ℝ} {S : Set ℝ}
    (hs : ∀ y ∈ S, (SignType.sign (radialK e ω (M + 1 / y)) : ℝ) = s) :
    EqOn (fun t => -((SignType.sign (radialK e ω (M + 1 / t)) : ℝ) *
        Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2)))
      (fun t => -s * Real.sqrt (radialK e ω (M + 1 / t) ^ 2 - L / t ^ 2)) S := by
  intro y hy
  simp only
  rw [hs y hy, neg_mul]

end ModeStability.AllAngular

end
