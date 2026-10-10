module

public import Mathlib
public import ModeStability.Exterior.Reduction
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.RadiusOf
public import ModeStability.Frozen.RadialK
public import ModeStability.AllAngular.ScalarPositivity

/-!
# The constant normalization (`g = 1`, `x = −h`) of the all-angular paper

Source: the all-angular research notes in preparation, pp. 2 and 5, the constant normalization
`g = 1`, `U = R`, `x = −h`, for `a < r₀ < 2M`; the coordinate `x` is that of Lemma 2.1 of
the spherical research notes in preparation.

We use the reflected coordinate `y = h(r) = −x ∈ (0, ∞)`. In the subextremal case `h` is the
static solution `g` of the spherical paper (`a − b = 2δ`), so `r(y) = radiusOf M Q (1 / y)`
is the inverse of `h`, and `dr/dy = −Δ(r(y))`. Reflection keeps `U_yy = U_xx`. With
`f(y) = −K(r(y))` one has `f² = k²`, `f_y = k_x = ΔK'` and `2 f_y² − f f_yy = E_k = A₀ (χ = 0)`,
so the frozen Lemma 2.2 (`ModeStability.dephased_current`, stated on `(0, ∞)`) applies verbatim.

* `constant_reduction`: `U(y) = R(r(y))` solves `U_yy + f² U = 0`, `f = −K ∘ r`, on `y > 0`.
* `hasDerivAt_constant_reduced`: `U_y = −Δ R'` at `r = r(y)`.
* `constant_coefficient`: `f` is `C²` on `(0, ∞)` with `f_y = ΔK'` and
  `f_yy = −Δ(2zK' + ΔK'')` at `r = r(y)` (`z = r − M`, `K' = 2ωr − qQ`, `K'' = 2ω`).
* `constant_coefficient_inequalities`: for `ω > 0`, `a < r₀ = qQ/ω < 2M` one has `f_y > 0` and
  `E_f = 2 f_y² − f f_yy > 0` on `(0, ∞)` (Lemma 2.2 of the all-angular paper, `A₀ > 0`, `H > 0`).
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

/-- `d/dy [r(y)] = −Δ(r(y))` for `r(y) = radiusOf M Q (1/y)`, `y > 0`: the chain rule through
`x = 1/y` and `r'(x) = Δ(r(x)) / x²`. -/
theorem hasDerivAt_radiusOf_one_div {M Q : ℝ} (hQ : |Q| < M) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => radiusOf M Q (1 / t))
      (-delta M Q (radiusOf M Q (1 / y))) y := by
  have hx : 0 < 1 / y := one_div_pos.2 hy
  have h1 : HasDerivAt (fun t : ℝ => 1 / t) (-(y ^ 2)⁻¹) y := by
    simpa only [one_div] using hasDerivAt_inv hy.ne'
  have h2 := (hasDerivAt_radiusOf hQ hx).comp y h1
  refine h2.congr_deriv ?_
  field_simp

/-- `U_y = −Δ R'` at `r = r(y)` for `U(y) = R(r(y))`, `y > 0`. -/
theorem hasDerivAt_constant_reduced {M Q q ω : ℝ} (hQ : |Q| < M) {R : ℝ → ℂ}
    (hR : IsRadialSolution M Q q ω R) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => R (radiusOf M Q (1 / t)))
      (-((delta M Q (radiusOf M Q (1 / y)) : ℝ) : ℂ) * deriv R (radiusOf M Q (1 / y))) y := by
  have hra := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy)
  have h := ((hR _ hra).1.hasDerivAt).scomp y (hasDerivAt_radiusOf_one_div hQ hy)
  refine h.congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  ring

/-- `U(y) = R(r(y))` solves `U_yy + f² U = 0`, `f(y) = −K(r(y))`, on `y > 0`. -/
theorem constant_reduction {M Q q ω : ℝ} (hM : 0 < M) (hQ : |Q| < M) {R : ℝ → ℂ}
    (hR : IsRadialSolution M Q q ω R) :
    ∀ y ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun t : ℝ => R (radiusOf M Q (1 / t))) y ∧
        HasDerivAt (deriv fun t : ℝ => R (radiusOf M Q (1 / t)))
          (-(((-radialK (q * Q) ω (radiusOf M Q (1 / y))) ^ 2 : ℝ) : ℂ) *
            R (radiusOf M Q (1 / y))) y := by
  intro y hy
  have hy0 : 0 < y := hy
  have _ := hM -- source premise `M > 0` (implied by `|Q| < M`), kept in the statement
  refine ⟨(hasDerivAt_constant_reduced hQ hR hy0).differentiableAt, ?_⟩
  have hra := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy0)
  have hD : 0 < delta M Q (radiusOf M Q (1 / y)) := delta_pos hQ hra
  have hev : (deriv fun t : ℝ => R (radiusOf M Q (1 / t))) =ᶠ[𝓝 y]
      fun t : ℝ => -(((delta M Q (radiusOf M Q (1 / t)) : ℝ) : ℂ) *
        deriv R (radiusOf M Q (1 / t))) := by
    filter_upwards [Ioi_mem_nhds hy0] with t ht
    have h := (hasDerivAt_constant_reduced hQ hR ht).deriv
    rw [h]
    ring
  have hG := ((hR _ hra).2).scomp y (hasDerivAt_radiusOf_one_div hQ hy0)
  refine (hG.neg.congr_deriv ?_).congr_of_eventuallyEq hev
  have hDc : ((delta M Q (radiusOf M Q (1 / y)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hD.ne'
  rw [Complex.real_smul]
  push_cast
  field_simp

/-- `r(y) = radiusOf M Q (1/y)` is smooth on `y > 0`. -/
theorem contDiffOn_radiusOf_one_div {M Q : ℝ} (hQ : |Q| < M) :
    ContDiffOn ℝ ⊤ (fun t : ℝ => radiusOf M Q (1 / t)) (Ioi 0) := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hinv : ContDiffOn ℝ ⊤ (fun t : ℝ => 1 / t) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun t ht => (Set.mem_Ioi.1 ht).ne')
  have hdiv : ContDiffOn ℝ ⊤ (fun t : ℝ => (outerHorizon M Q - innerHorizon M Q) / t) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun t ht => (Set.mem_Ioi.1 ht).ne')
  have hexp : ContDiffOn ℝ ⊤
      (fun t : ℝ => Real.exp ((outerHorizon M Q - innerHorizon M Q) / t) - 1) (Ioi 0) :=
    (ContDiffOn.exp hdiv).sub contDiffOn_const
  have hr : ContDiffOn ℝ ⊤ (radiusOf M Q) (Ioi 0) := by
    unfold radiusOf
    refine contDiffOn_const.add (contDiffOn_const.div hexp ?_)
    intro t ht
    have hE : 1 < Real.exp ((outerHorizon M Q - innerHorizon M Q) / t) :=
      Real.one_lt_exp_iff.2 (div_pos hd ht)
    exact (sub_pos.2 hE).ne'
  refine hr.comp hinv ?_
  intro t ht
  exact one_div_pos.2 ht

/-- The coefficient `f(y) = −K(r(y))`: `C²` on `(0, ∞)`, `f_y = ΔK'`,
`f_yy = −Δ(2zK' + ΔK'')` (`z = r − M`, `K' = 2ωr − qQ`, `K'' = 2ω`), at `r = r(y)`. -/
theorem constant_coefficient {M Q q ω : ℝ} (hQ : |Q| < M) :
    ContDiffOn ℝ 2 (fun y : ℝ => -radialK (q * Q) ω (radiusOf M Q (1 / y))) (Ioi 0) ∧
      ∀ y ∈ Ioi (0 : ℝ),
        deriv (fun t : ℝ => -radialK (q * Q) ω (radiusOf M Q (1 / t))) y =
            delta M Q (radiusOf M Q (1 / y)) * (2 * ω * radiusOf M Q (1 / y) - q * Q) ∧
          deriv (deriv fun t : ℝ => -radialK (q * Q) ω (radiusOf M Q (1 / t))) y =
            -(delta M Q (radiusOf M Q (1 / y)) *
              (2 * (radiusOf M Q (1 / y) - M) * (2 * ω * radiusOf M Q (1 / y) - q * Q) +
                delta M Q (radiusOf M Q (1 / y)) * (2 * ω))) := by
  refine ⟨?_, ?_⟩
  · have hr := (contDiffOn_radiusOf_one_div (M := M) (Q := Q) hQ).of_le
      (show ((2 : ℕ∞) : WithTop ℕ∞) ≤ ⊤ from le_top)
    unfold radialK
    exact (((contDiffOn_const.mul (hr.pow 2)).sub (contDiffOn_const.mul hr)).neg)
  · intro y hy
    have hy0 : 0 < y := hy
    have hrd := hasDerivAt_radiusOf_one_div hQ hy0
    -- `f_y = ΔK'` on `y > 0`
    have hf : ∀ t ∈ Ioi (0 : ℝ),
        HasDerivAt (fun t : ℝ => -radialK (q * Q) ω (radiusOf M Q (1 / t)))
          (delta M Q (radiusOf M Q (1 / t)) * (2 * ω * radiusOf M Q (1 / t) - q * Q)) t := by
      intro t ht
      have hrt := hasDerivAt_radiusOf_one_div hQ ht
      have h1 : HasDerivAt (fun s : ℝ => -radialK (q * Q) ω s) (-(2 * ω * radiusOf M Q (1 / t) -
          q * Q)) (radiusOf M Q (1 / t)) := by
        unfold radialK
        have := (((hasDerivAt_id (radiusOf M Q (1 / t))).pow 2).const_mul ω).sub
          ((hasDerivAt_id (radiusOf M Q (1 / t))).const_mul (q * Q))
        refine this.neg.congr_deriv ?_
        simp
        ring
      refine (h1.comp t hrt).congr_deriv ?_
      ring
    refine ⟨(hf y hy).deriv, ?_⟩
    -- `f_yy`: differentiate `ΔK'` along `r(y)`
    have hP : HasDerivAt (fun s : ℝ => delta M Q s * (2 * ω * s - q * Q))
        (2 * (radiusOf M Q (1 / y) - M) * (2 * ω * radiusOf M Q (1 / y) - q * Q) +
          delta M Q (radiusOf M Q (1 / y)) * (2 * ω)) (radiusOf M Q (1 / y)) := by
      have hΔ : HasDerivAt (delta M Q) (2 * (radiusOf M Q (1 / y) - M))
          (radiusOf M Q (1 / y)) := by
        have := ((hasDerivAt_id (radiusOf M Q (1 / y))).sub_const (outerHorizon M Q)).mul
          ((hasDerivAt_id (radiusOf M Q (1 / y))).sub_const (innerHorizon M Q))
        have hfun : delta M Q = fun s => (id s - outerHorizon M Q) * (id s - innerHorizon M Q) :=
          rfl
        rw [hfun]
        refine this.congr_deriv ?_
        unfold outerHorizon innerHorizon
        simp
        ring
      have hK : HasDerivAt (fun s : ℝ => 2 * ω * s - q * Q) (2 * ω) (radiusOf M Q (1 / y)) := by
        simpa using ((hasDerivAt_id (radiusOf M Q (1 / y))).const_mul (2 * ω)).sub_const (q * Q)
      exact hΔ.mul hK
    have hev : (deriv fun t : ℝ => -radialK (q * Q) ω (radiusOf M Q (1 / t))) =ᶠ[𝓝 y]
        fun t : ℝ => delta M Q (radiusOf M Q (1 / t)) *
          (2 * ω * radiusOf M Q (1 / t) - q * Q) := by
      filter_upwards [Ioi_mem_nhds hy0] with t ht using (hf t ht).deriv
    refine (((hP.comp y hrd).congr_of_eventuallyEq hev).deriv).trans ?_
    ring

/-- For `ω > 0` and `a < r₀ = qQ/ω < 2M`, the coefficient `f(y) = −K(r(y))` satisfies `f_y > 0`
and `E_f = 2 f_y² − f f_yy > 0` on `y > 0`: these are `H = ΔK' > 0` and `A₀ > 0` of Lemma 2.2
(constant normalization) of the all-angular paper at `r = r(y)`. -/
theorem constant_coefficient_inequalities {M Q q ω : ℝ} (hM : 0 < M) (hQ : |Q| < M)
    (hω : 0 < ω) (h₀ : outerHorizon M Q < q * Q / ω) (h2M : q * Q / ω < 2 * M) :
    ∀ y ∈ Ioi (0 : ℝ),
      0 < deriv (fun t : ℝ => -radialK (q * Q) ω (radiusOf M Q (1 / t))) y ∧
        0 < 2 * deriv (fun t : ℝ => -radialK (q * Q) ω (radiusOf M Q (1 / t))) y ^ 2 -
          (-radialK (q * Q) ω (radiusOf M Q (1 / y))) *
            deriv (deriv fun t : ℝ => -radialK (q * Q) ω (radiusOf M Q (1 / t))) y := by
  intro y hy
  have hy0 : 0 < y := hy
  obtain ⟨h1, h2⟩ := (constant_coefficient (M := M) (Q := Q) (q := q) (ω := ω) hQ).2 y hy
  have hra := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy0)
  have he : ω * (q * Q / ω) = q * Q := mul_div_cancel₀ _ hω.ne'
  obtain ⟨hH, hA⟩ := scalar_positivity_constant hM hQ.le hω h₀ h2M hra
  rw [he] at hH hA
  rw [h1, h2]
  refine ⟨hH, ?_⟩
  unfold radialK at hA ⊢
  linarith only [hA]

end ModeStability.AllAngular

end
