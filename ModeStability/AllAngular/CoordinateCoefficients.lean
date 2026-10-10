module

public import Mathlib
public import ModeStability.AllAngular.AngularReduction
public import ModeStability.AllAngular.CoordinateCoefficientsAux
public import ModeStability.AllAngular.CoordinateCoefficientsExtremal

/-!
# Lemma 2.2 and Proposition 3.1 in the four coordinate systems

Source: the all-angular research notes in preparation, pp. 2–4: (2.2)–(2.7), Lemma 2.2,
(3.2) and Proposition 3.1. The paper proves
`k̂_x > 0` and `E_k̂ = 2k̂_x² − k̂k̂_xx > 0` in `r`-form, with `∂ₓ = Δg²∂ᵣ`; here they are
transported into the four concrete coordinate systems of the main assembly (the reductions (2.4)
are
`ModeStability.AllAngular.reciprocal_reduction_L`, `constant_reduction_L`,
`extremal_reciprocal_reduction_L`, `extremal_constant_reduction_L`). In each system `F` is the
coefficient of the reduced equation `U'' + F U = 0` and `f̂` is the signed effective frequency
(3.2) in that coordinate:

* subextremal reciprocal (`g = h`, `x = 1/h`, `r = radiusOf M Q x`):
  `F = (K/x²)² − LΔ/x⁴`, `f̂ = sgn(K) (1/x)² √(K² − LΔ)`;
* subextremal constant (`g = 1`, `y = h`, `r = radiusOf M Q (1/y)`):
  `F = K² − LΔ`, `f̂ = −sgn(K) √(K² − LΔ)`;
* extremal reciprocal (`|Q| = M`, `x = r − M`): `F = (K/x²)² − L/x²`,
  `f̂ = sgn(K) (1/x)² √(K² − Lx²)`;
* extremal constant (`|Q| = M`, `y = 1/(r − M)`): `F = K² − L/y²`, `f̂ = −sgn(K) √(K² − L/y²)`.

For each system (`*` one of `reciprocal`, `constant`, `extremal_reciprocal`,
`extremal_constant`):

1. `*_fhat_sq`: `f̂² = F` wherever `F ≥ 0`.
2. `*_fhat_props`: Proposition 3.1, (3.3): where `LΔ < K²` (`F > 0`), `f̂` is `C²`, `f̂' > 0`
   and `2f̂'² − f̂f̂'' > 0`.
3. `*_fhat_L0`: at `L = 0`, `f̂` is the spherical coefficient (`K/x²` resp. `−K`), and
   Lemma 2.2 (`H > 0`, `A₀ > 0`) gives the three conclusions of 2 at every point, including the
   corotation point `x(r₀)`.
4. `*_F_props`: `F` is `C²` on `(0, ∞)`, `F = c · P ∘ ρ` with `P = K² − LΔ` and `c = 1/x⁴`
   (reciprocal) resp. `c = 1` (constant), and `F' = c · P'(ρ) · ρ'` at a zero of `P ∘ ρ`
   (everywhere in the constant systems), with `P' = 2KK' − LΔ'`.
5. `*_fhat_eq_sign_sqrt`: on a set where `sgn K(ρ ·)` is a constant `s`, `f̂ = s√F`
   (reciprocal) resp. `f̂ = −s√F` (constant); no positivity of `F` is needed.

The standing parameters are `M > 0`, `ω > 0`, `L ≥ 0`, `r₀ = e/ω > a`, with `r₀ ≥ 2M` for the
reciprocal and `r₀ < 2M` for the constant normalization, as in (2.2). The subextremal systems are
proved here; the extremal ones are in `ModeStability.AllAngular.CoordinateCoefficientsExtremal`
(imported), and the abstract transport is in `ModeStability.AllAngular.CoordinateCoefficientsAux`.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

open CoefficientIdentities CoordinateCoefficients

/-! ### Helpers -/

/-- `ω · (e/ω) = e`. -/
private theorem cc_mul_div {e ω : ℝ} (hω : 0 < ω) : ω * (e / ω) = e :=
  mul_div_cancel₀ e hω.ne'

/-- `h' = −1/Δ` near an exterior point (subextremal). -/
private theorem cc_static_hg {M Q : ℝ} (hQ : |Q| < M) {r : ℝ} (hr : outerHorizon M Q < r) :
    ∀ᶠ s in 𝓝 r, HasDerivAt (staticSolution M Q) (-1 / delta M Q s) s := by
  filter_upwards [lt_mem_nhds hr] with s hs using hasDerivAt_staticSolution hQ hs

/-! ### Subextremal, reciprocal normalization -/

/-- `ρ' = Δ h²` along `r = radiusOf M Q x`, near `x > 0`. -/
private theorem cc_rec_hρ {M Q : ℝ} (hQ : |Q| < M) {x : ℝ} (hx : 0 < x) :
    ∀ᶠ y in 𝓝 x, HasDerivAt (radiusOf M Q)
      (1 * (delta M Q (radiusOf M Q y) * staticSolution M Q (radiusOf M Q y) ^ 2)) y := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [one_mul]
  exact hasDerivAt_radiusOf_eq_mul_sq hQ hy

/-- Pointwise form of (3.2) in the reciprocal coordinate: `f̂ = sgn(K) √F`. -/
private theorem cc_rec_eq (M Q e ω L x : ℝ) :
    (SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) * (1 / x) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)) =
      (SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) *
        Real.sqrt ((radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
          L * delta M Q (radiusOf M Q x) / x ^ 4) := by
  have hF : (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 - L * delta M Q (radiusOf M Q x) / x ^ 4 =
      ((1 / x) ^ 2) ^ 2 * (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)) := by
    ring
  rw [hF, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

/-- (3.2), subextremal reciprocal: `f̂² = F` wherever `F ≥ 0`. -/
theorem reciprocal_fhat_sq {M Q e ω L : ℝ} (hQ : |Q| < M) (hL : 0 ≤ L) {x : ℝ} (hx : 0 < x)
    (hF : 0 ≤ (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
      L * delta M Q (radiusOf M Q x) / x ^ 4) :
    ((SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) * (1 / x) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x))) ^ 2 =
      (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 - L * delta M Q (radiusOf M Q x) / x ^ 4 := by
  rw [cc_rec_eq]
  refine sq_sign_mul_sqrt hF fun hK => le_antisymm ?_ hF
  have hΔ := delta_pos hQ (outerHorizon_lt_radiusOf hQ hx)
  rw [hK]
  have : 0 ≤ L * delta M Q (radiusOf M Q x) / x ^ 4 := by positivity
  linarith [show ((0 : ℝ) / x ^ 2) ^ 2 = 0 by simp]

/-- Proposition 3.1, subextremal reciprocal normalization (`r₀ ≥ 2M`, `g = h`, `x = 1/h`): at
`x > 0` with `LΔ < K²` at `r = r(x)`, `f̂ = sgn(K)(1/x)²√(K² − LΔ)` is `C²`, `f̂' > 0` and
`2f̂'² − f̂f̂'' > 0`. -/
theorem reciprocal_fhat_props {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (hL : 0 ≤ L) (hr₀ : outerHorizon M Q < e / ω) (h2M : 2 * M ≤ e / ω) {x : ℝ} (hx : 0 < x)
    (hK : L * delta M Q (radiusOf M Q x) < radialK e ω (radiusOf M Q x) ^ 2) :
    ContDiffAt ℝ 2 (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) x ∧
      0 < deriv (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) x ∧
      0 < 2 * deriv (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
          Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) x ^ 2 -
        (SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) * (1 / x) ^ 2 *
            Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)) *
          deriv (deriv fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
            Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) x := by
  have hr := outerHorizon_lt_radiusOf hQ hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := chi_bounds hQ hr
  obtain ⟨hH, hA⟩ := scalar_positivity_reciprocal hM hQ.le hω hr₀ h2M hr h4 h1.le h2.le h3.le
  rw [cc_mul_div hω] at hH hA
  have hf : (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) =ᶠ[𝓝 x]
      fun y => 1 * effectiveKAux M Q e ω L (staticSolution M Q) (radiusOf M Q y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [effectiveKAux, staticSolution_radiusOf hQ hy, one_mul]
  exact coordinate_khat_props (one_mul 1) hM hQ.le hω hL hr₀ hr (staticSolution_pos hQ hr) hK
    (cc_static_hg hQ hr) (contDiffAt_staticSolution hQ hr) (cc_rec_hρ hQ hx)
    (contDiffAt_radiusOf hQ hx) hf (by rw [neg_neg]) h4.le h5.le hH hA

/-- Lemma 2.2, subextremal reciprocal normalization, at `L = 0`: `f̂ = K/x²`, and `f̂` is `C²`,
`f̂' > 0`, `2f̂'² − f̂f̂'' > 0` at every `x > 0` (including the corotation point `x(r₀)`). -/
theorem reciprocal_fhat_L0 {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (hL0 : L = 0) (hr₀ : outerHorizon M Q < e / ω) (h2M : 2 * M ≤ e / ω) :
    (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) =
      (fun t => radialK e ω (radiusOf M Q t) / t ^ 2) ∧
    ∀ x ∈ Ioi (0 : ℝ),
      ContDiffAt ℝ 2 (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
          Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) x ∧
        0 < deriv (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
          Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) x ∧
        0 < 2 * deriv (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) *
            (1 / t) ^ 2 *
            Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) x ^ 2 -
          (SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) * (1 / x) ^ 2 *
              Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)) *
            deriv (deriv fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) *
              (1 / t) ^ 2 *
              Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) x := by
  have heq : (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t))) =
      (fun t => radialK e ω (radiusOf M Q t) / t ^ 2) := by
    funext t
    rw [hL0, mul_right_comm, sign_mul_sqrt_L0]
    ring
  refine ⟨heq, fun x hx => ?_⟩
  have hx0 : 0 < x := hx
  suffices h : ∀ f : ℝ → ℝ, f = (fun t => radialK e ω (radiusOf M Q t) / t ^ 2) →
      ContDiffAt ℝ 2 f x ∧ 0 < deriv f x ∧ 0 < 2 * deriv f x ^ 2 - f x * deriv (deriv f) x from
    h _ heq
  rintro f rfl
  have hr := outerHorizon_lt_radiusOf hQ hx0
  obtain ⟨h1, h2, h3, h4, -⟩ := chi_bounds hQ hr
  obtain ⟨hH, hA⟩ := scalar_positivity_reciprocal hM hQ.le hω hr₀ h2M hr h4 h1.le h2.le h3.le
  rw [cc_mul_div hω] at hH hA
  have hf : (fun t => radialK e ω (radiusOf M Q t) / t ^ 2) =ᶠ[𝓝 x]
      fun y => 1 * (staticSolution M Q (radiusOf M Q y) ^ 2 * radialK e ω (radiusOf M Q y)) := by
    filter_upwards [Ioi_mem_nhds hx0] with y hy
    rw [staticSolution_radiusOf hQ hy]
    ring
  exact coordinate_k_props (one_mul 1) hr (staticSolution_pos hQ hr) (cc_static_hg hQ hr)
    (contDiffAt_staticSolution hQ hr) (cc_rec_hρ hQ hx0) (contDiffAt_radiusOf hQ hx0) hf
    (by rw [neg_neg]) hH hA

/-- Item 4, subextremal reciprocal: `F = (K/x²)² − LΔ/x⁴` is `C²` on `(0, ∞)`, `F = x⁻⁴ P(r)`
with `P = K² − LΔ`, and at a zero of `P(r(x))`, `F' = x⁻⁴ P'(r) r'` with
`P' = 2KK' − LΔ'`, `r' = Δ/x²`. -/
theorem reciprocal_F_props {M Q e ω L : ℝ} (hQ : |Q| < M) :
    ContDiffOn ℝ 2 (fun t => (radialK e ω (radiusOf M Q t) / t ^ 2) ^ 2 -
        L * delta M Q (radiusOf M Q t) / t ^ 4) (Ioi 0) ∧
      ∀ x ∈ Ioi (0 : ℝ), 0 < 1 / x ^ 4 ∧
        (radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 - L * delta M Q (radiusOf M Q x) / x ^ 4 =
          1 / x ^ 4 * (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)) ∧
        (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x) = 0 →
          HasDerivAt (fun t => (radialK e ω (radiusOf M Q t) / t ^ 2) ^ 2 -
              L * delta M Q (radiusOf M Q t) / t ^ 4)
            (1 / x ^ 4 * (2 * radialK e ω (radiusOf M Q x) * (2 * ω * radiusOf M Q x - e) -
                L * (2 * (radiusOf M Q x - M))) * (delta M Q (radiusOf M Q x) / x ^ 2)) x) := by
  refine ⟨fun x hx => ?_, fun x hx => ⟨by have : (0 : ℝ) < x := hx; positivity, by ring, ?_⟩⟩
  · have hx0 : (0 : ℝ) < x := hx
    have hρ := contDiffAt_radiusOf hQ hx0
    have hK := (contDiff_radialK e ω).contDiffAt.comp x hρ
    have hD := (contDiff_delta M Q).contDiffAt.comp x hρ
    exact (((hK.div (contDiffAt_id.pow 2) (pow_ne_zero 2 hx0.ne')).pow 2).sub
      ((contDiffAt_const.mul hD).div (contDiffAt_id.pow 4)
        (pow_ne_zero 4 hx0.ne'))).contDiffWithinAt
  · intro hP0
    have hx0 : (0 : ℝ) < x := hx
    have h1 : HasDerivAt (fun t : ℝ => 1 / t ^ 4) (deriv (fun t : ℝ => 1 / t ^ 4) x) x :=
      ((differentiableAt_const (1 : ℝ)).div (differentiableAt_pow 4)
        (pow_ne_zero 4 hx0.ne')).hasDerivAt
    have h2 := (hasDerivAt_radicand M Q e ω L (radiusOf M Q x)).comp x (hasDerivAt_radiusOf hQ hx0)
    refine ((h1.fun_mul h2).congr_deriv ?_).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    · simp only [Function.comp_apply, hP0]
      ring
    · simp only [Function.comp_apply]
      ring

/-- Item 5, subextremal reciprocal: on a set where `sgn K(r(·)) = s`, `f̂ = s√F`. -/
theorem reciprocal_fhat_eq_sign_sqrt {M Q e ω L s : ℝ} {S : Set ℝ}
    (hs : ∀ x ∈ S, (SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) = s) :
    EqOn (fun t => (SignType.sign (radialK e ω (radiusOf M Q t)) : ℝ) * (1 / t) ^ 2 *
        Real.sqrt (radialK e ω (radiusOf M Q t) ^ 2 - L * delta M Q (radiusOf M Q t)))
      (fun t => s * Real.sqrt ((radialK e ω (radiusOf M Q t) / t ^ 2) ^ 2 -
        L * delta M Q (radiusOf M Q t) / t ^ 4)) S := by
  intro x hx
  simp only
  rw [cc_rec_eq, hs x hx]

/-! ### Subextremal, constant normalization -/

/-- `ρ' = −Δ` along `r = radiusOf M Q (1/y)`. -/
private theorem cc_con_hρ {M Q : ℝ} (hQ : |Q| < M) {x : ℝ} (hx : 0 < x) :
    ∀ᶠ y in 𝓝 x, HasDerivAt (fun t => radiusOf M Q (1 / t))
      (-1 * (delta M Q (radiusOf M Q (1 / y)) * 1 ^ 2)) y := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  refine (hasDerivAt_radiusOf_one_div hQ hy).congr_deriv ?_
  ring

/-- `r = radiusOf M Q (1/y)` is `C²` at `y > 0`. -/
private theorem cc_con_hρC {M Q : ℝ} (hQ : |Q| < M) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ 2 (fun t => radiusOf M Q (1 / t)) x :=
  ((contDiffOn_radiusOf_one_div hQ).contDiffAt (Ioi_mem_nhds hx)).of_le le_top

/-- (3.2), subextremal constant: `f̂² = F` wherever `F ≥ 0`. -/
theorem constant_fhat_sq {M Q e ω L : ℝ} (hQ : |Q| < M) (hL : 0 ≤ L) {y : ℝ} (hy : 0 < y)
    (hF : 0 ≤ radialK e ω (radiusOf M Q (1 / y)) ^ 2 - L * delta M Q (radiusOf M Q (1 / y))) :
    (-((SignType.sign (radialK e ω (radiusOf M Q (1 / y))) : ℝ) *
        Real.sqrt (radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / y))))) ^ 2 =
      radialK e ω (radiusOf M Q (1 / y)) ^ 2 - L * delta M Q (radiusOf M Q (1 / y)) := by
  rw [neg_sq]
  refine sq_sign_mul_sqrt hF fun hK => le_antisymm ?_ hF
  have hΔ := delta_pos hQ (outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy))
  rw [hK]
  nlinarith [mul_nonneg hL hΔ.le]

/-- Proposition 3.1, subextremal constant normalization (`a < r₀ < 2M`, `g = 1`, reflected
`y = h`): at `y > 0` with `LΔ < K²` at `r = r(y)`, `f̂ = −sgn(K)√(K² − LΔ)` is `C²`, `f̂' > 0` and
`2f̂'² − f̂f̂'' > 0`. -/
theorem constant_fhat_props {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (hL : 0 ≤ L) (hr₀ : outerHorizon M Q < e / ω) (h2M : e / ω < 2 * M) {y : ℝ} (hy : 0 < y)
    (hK : L * delta M Q (radiusOf M Q (1 / y)) < radialK e ω (radiusOf M Q (1 / y)) ^ 2) :
    ContDiffAt ℝ 2 (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
        Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / t))))) y ∧
      0 < deriv (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
        Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / t))))) y ∧
      0 < 2 * deriv (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
          Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
            L * delta M Q (radiusOf M Q (1 / t))))) y ^ 2 -
        -((SignType.sign (radialK e ω (radiusOf M Q (1 / y))) : ℝ) *
            Real.sqrt (radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
              L * delta M Q (radiusOf M Q (1 / y)))) *
          deriv (deriv fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
            Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
              L * delta M Q (radiusOf M Q (1 / t))))) y := by
  have hr := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy)
  obtain ⟨hH, hA⟩ := scalar_positivity_constant hM hQ.le hω hr₀ h2M hr
  rw [cc_mul_div hω] at hH hA
  have hH' : 0 < delta M Q (radiusOf M Q (1 / y)) * (2 * ω * radiusOf M Q (1 / y) - e) -
      2 * 0 * radialK e ω (radiusOf M Q (1 / y)) := by linarith
  have hA' : 0 < 2 * delta M Q (radiusOf M Q (1 / y)) ^ 2 * (2 * ω * radiusOf M Q (1 / y) - e) ^ 2 -
      2 * delta M Q (radiusOf M Q (1 / y)) * (0 + (radiusOf M Q (1 / y) - M)) *
        radialK e ω (radiusOf M Q (1 / y)) * (2 * ω * radiusOf M Q (1 / y) - e) -
      delta M Q (radiusOf M Q (1 / y)) ^ 2 * radialK e ω (radiusOf M Q (1 / y)) * (2 * ω) +
      2 * 0 ^ 2 * radialK e ω (radiusOf M Q (1 / y)) ^ 2 := by linarith
  have hf : (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
        Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / t))))) =ᶠ[𝓝 y]
      fun t => -1 * effectiveKAux M Q e ω L (fun _ => 1) (radiusOf M Q (1 / t)) :=
    Eventually.of_forall fun t => by
      simp only [effectiveKAux]
      ring
  exact coordinate_khat_props (by norm_num) hM hQ.le hω hL hr₀ hr one_pos hK
    (eventually_hasDerivAt_one M Q _) contDiffAt_const (cc_con_hρ hQ hy) (cc_con_hρC hQ hy) hf
    (by rw [neg_zero, zero_div]) le_rfl (sub_pos_of_outerHorizon_lt hr).le hH' hA'

/-- Lemma 2.2, subextremal constant normalization, at `L = 0`: `f̂ = −K`, and `f̂` is `C²`,
`f̂' > 0`, `2f̂'² − f̂f̂'' > 0` at every `y > 0`. -/
theorem constant_fhat_L0 {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (hL0 : L = 0) (hr₀ : outerHorizon M Q < e / ω) (h2M : e / ω < 2 * M) :
    (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
        Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / t))))) =
      (fun t => -radialK e ω (radiusOf M Q (1 / t))) ∧
    ∀ y ∈ Ioi (0 : ℝ),
      ContDiffAt ℝ 2 (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
          Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
            L * delta M Q (radiusOf M Q (1 / t))))) y ∧
        0 < deriv (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
          Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
            L * delta M Q (radiusOf M Q (1 / t))))) y ∧
        0 < 2 * deriv (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
            Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
              L * delta M Q (radiusOf M Q (1 / t))))) y ^ 2 -
          -((SignType.sign (radialK e ω (radiusOf M Q (1 / y))) : ℝ) *
              Real.sqrt (radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
                L * delta M Q (radiusOf M Q (1 / y)))) *
            deriv (deriv fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
              Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
                L * delta M Q (radiusOf M Q (1 / t))))) y := by
  have heq : (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
        Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / t))))) =
      (fun t => -radialK e ω (radiusOf M Q (1 / t))) := by
    funext t
    rw [hL0, sign_mul_sqrt_L0]
  refine ⟨heq, fun y hy => ?_⟩
  have hy0 : 0 < y := hy
  suffices h : ∀ f : ℝ → ℝ, f = (fun t => -radialK e ω (radiusOf M Q (1 / t))) →
      ContDiffAt ℝ 2 f y ∧ 0 < deriv f y ∧ 0 < 2 * deriv f y ^ 2 - f y * deriv (deriv f) y from
    h _ heq
  rintro f rfl
  have hr := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy0)
  obtain ⟨hH, hA⟩ := scalar_positivity_constant hM hQ.le hω hr₀ h2M hr
  rw [cc_mul_div hω] at hH hA
  have hH' : 0 < delta M Q (radiusOf M Q (1 / y)) * (2 * ω * radiusOf M Q (1 / y) - e) -
      2 * 0 * radialK e ω (radiusOf M Q (1 / y)) := by linarith
  have hA' : 0 < 2 * delta M Q (radiusOf M Q (1 / y)) ^ 2 * (2 * ω * radiusOf M Q (1 / y) - e) ^ 2 -
      2 * delta M Q (radiusOf M Q (1 / y)) * (0 + (radiusOf M Q (1 / y) - M)) *
        radialK e ω (radiusOf M Q (1 / y)) * (2 * ω * radiusOf M Q (1 / y) - e) -
      delta M Q (radiusOf M Q (1 / y)) ^ 2 * radialK e ω (radiusOf M Q (1 / y)) * (2 * ω) +
      2 * 0 ^ 2 * radialK e ω (radiusOf M Q (1 / y)) ^ 2 := by linarith
  have hf : (fun t => -radialK e ω (radiusOf M Q (1 / t))) =ᶠ[𝓝 y]
      fun t => -1 * ((1 : ℝ) ^ 2 * radialK e ω (radiusOf M Q (1 / t))) :=
    Eventually.of_forall fun t => by ring
  exact coordinate_k_props (g := fun _ => 1) (by norm_num) hr one_pos
    (eventually_hasDerivAt_one M Q _) contDiffAt_const (cc_con_hρ hQ hy0) (cc_con_hρC hQ hy0) hf
    (by rw [neg_zero, zero_div]) hH' hA'

/-- Item 4, subextremal constant: `F = K² − LΔ = P(r(y))` is `C²` on `(0, ∞)`, and
`F' = P'(r) r'` with `P' = 2KK' − LΔ'`, `r' = −Δ`, at every `y > 0`. -/
theorem constant_F_props {M Q e ω L : ℝ} (hQ : |Q| < M) :
    ContDiffOn ℝ 2 (fun t => radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
        L * delta M Q (radiusOf M Q (1 / t))) (Ioi 0) ∧
      ∀ y ∈ Ioi (0 : ℝ),
        HasDerivAt (fun t => radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
            L * delta M Q (radiusOf M Q (1 / t)))
          ((2 * radialK e ω (radiusOf M Q (1 / y)) * (2 * ω * radiusOf M Q (1 / y) - e) -
              L * (2 * (radiusOf M Q (1 / y) - M))) * -delta M Q (radiusOf M Q (1 / y))) y := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have hρ := cc_con_hρC hQ (show (0 : ℝ) < y from hy)
    exact ((((contDiff_radialK e ω).contDiffAt.comp y hρ).pow 2).sub
      (contDiffAt_const.mul ((contDiff_delta M Q).contDiffAt.comp y hρ))).contDiffWithinAt
  · exact (hasDerivAt_radicand M Q e ω L _).comp y
      (hasDerivAt_radiusOf_one_div hQ (show (0 : ℝ) < y from hy))

/-- Item 5, subextremal constant: on a set where `sgn K(r(·)) = s`, `f̂ = −s√F`. -/
theorem constant_fhat_eq_sign_sqrt {M Q e ω L s : ℝ} {S : Set ℝ}
    (hs : ∀ y ∈ S, (SignType.sign (radialK e ω (radiusOf M Q (1 / y))) : ℝ) = s) :
    EqOn (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
        Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
          L * delta M Q (radiusOf M Q (1 / t)))))
      (fun t => -s * Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
        L * delta M Q (radiusOf M Q (1 / t)))) S := by
  intro y hy
  simp only
  rw [hs y hy, neg_mul]

end ModeStability.AllAngular

end
