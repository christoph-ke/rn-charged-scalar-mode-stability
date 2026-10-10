module

public import Mathlib
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.RadiusOf
public import ModeStability.Frozen.StaticSolution
public import ModeStability.Exterior.Calculus
public import ModeStability.AllAngular.ConstantNormalization

/-!
# The transformed equation (2.4) with angular term

Source: the all-angular research notes in preparation, p. 2, (2.1)–(2.4). For a solution of the
radial equation with angular term, `(ΔR')' + (K²/Δ − L)R = 0` on `r > a`, with
`K(r) = ωr² − er` (`radialK e ω`, `e` an independent real coefficient), the function
`U = R/g` solves `U_xx + (k² − V)U = 0` with `k = g²K` and `V = LΔg⁴`, in each of the four
coordinate systems below (`h` is the static solution (2.1), `h' = −1/Δ`).

* Subextremal (`|Q| < M`), reciprocal normalization `g = h`, `x = 1/h ∈ (0, ∞)`:
  `U(x) = x R(r(x))`, `r(x) = radiusOf M Q x`, and since `g(r(x)) = 1/x`,
  `k² − V = (K(r)/x²)² − LΔ(r)/x⁴` (`reciprocal_reduction_L`).
* Subextremal, constant normalization `g = 1`, reflected coordinate `y = h = −x ∈ (0, ∞)`:
  `U(y) = R(r(y))`, `r(y) = radiusOf M Q (1/y)`, `k² − V = K(r)² − LΔ(r)`
  (`constant_reduction_L`).
* Extremal (`|Q| = M`, so `a = b = M`, `Δ = (r − M)²`, `h = 1/(r − M)`), reciprocal
  normalization `x = r − M ∈ (0, ∞)`: `U(x) = x R(M + x)`, `k² − V = (K(M + x)/x²)² − L/x²`
  (`extremal_reciprocal_reduction_L`).
* Extremal, constant normalization, reflected `y = h = 1/(r − M) ∈ (0, ∞)`:
  `U(y) = R(M + 1/y)`, `k² − V = K(M + 1/y)² − L/y²` (`extremal_constant_reduction_L`).

The first derivatives are recorded separately: `U' = R + gΔR'` (reciprocal), `U_y = −ΔR'`
(constant), `U' = R + xR'(M + x)` (extremal reciprocal), `U_y = −R'(M + 1/y)/y²` (extremal
constant).
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

/-! ### The extremal exterior -/

/-- `a = M` in the extremal case `|Q| = M`. -/
theorem outerHorizon_of_abs_eq {M Q : ℝ} (hQ : |Q| = M) : outerHorizon M Q = M := by
  have h : M ^ 2 - Q ^ 2 = 0 := by rw [← hQ, sq_abs, sub_self]
  rw [outerHorizon, h, Real.sqrt_zero, add_zero]

/-- `b = M` in the extremal case `|Q| = M`. -/
theorem innerHorizon_of_abs_eq {M Q : ℝ} (hQ : |Q| = M) : innerHorizon M Q = M := by
  have h : M ^ 2 - Q ^ 2 = 0 := by rw [← hQ, sq_abs, sub_self]
  rw [innerHorizon, h, Real.sqrt_zero, sub_zero]

/-- `Δ(r) = (r − M)²` in the extremal case `|Q| = M`. -/
theorem delta_of_abs_eq {M Q : ℝ} (hQ : |Q| = M) (r : ℝ) : delta M Q r = (r - M) ^ 2 := by
  rw [delta, outerHorizon_of_abs_eq hQ, innerHorizon_of_abs_eq hQ, sq]

/-! ### Subextremal, reciprocal normalization -/

/-- `U' = R(r) + g(r) · (ΔR')(r)` at `r = r(x)` for `U(x) = x R(r(x))`, `x > 0`. -/
theorem hasDerivAt_reciprocal_reduced_L {M Q e ω L : ℝ} (hQ : |Q| < M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))
      (R (radiusOf M Q x) + ((staticSolution M Q (radiusOf M Q x) : ℝ) : ℂ) *
        (((delta M Q (radiusOf M Q x) : ℝ) : ℂ) * deriv R (radiusOf M Q x))) x := by
  have hra := outerHorizon_lt_radiusOf hQ hx
  have h1 : HasDerivAt (fun y : ℝ => R (radiusOf M Q y))
      ((delta M Q (radiusOf M Q x) * staticSolution M Q (radiusOf M Q x) ^ 2 : ℝ) •
        deriv R (radiusOf M Q x)) x :=
    ((hR _ hra).1.hasDerivAt).scomp x (hasDerivAt_radiusOf_eq_mul_sq hQ hx)
  have h2 := (hasDerivAt_id' x).ofReal_comp.mul h1
  refine h2.congr_deriv ?_
  rw [Complex.real_smul, staticSolution_radiusOf hQ hx]
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  push_cast
  field_simp

/-- (2.4), subextremal, reciprocal normalization `g = h`, `x = 1/h`: `U(x) = x R(r(x))` solves
`U_xx + (k² − V)U = 0` on `x > 0`, with `k = K/x²`, `V = LΔ/x⁴` at `r = r(x)`. -/
theorem reciprocal_reduction_L {M Q e ω L : ℝ} (hQ : |Q| < M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    ∀ x ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x ∧
        HasDerivAt (deriv fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))
          (-(((radialK e ω (radiusOf M Q x) / x ^ 2) ^ 2 -
              L * delta M Q (radiusOf M Q x) / x ^ 4 : ℝ) : ℂ) *
            ((x : ℂ) * R (radiusOf M Q x))) x := by
  intro x hx
  have hx0 : 0 < x := hx
  refine ⟨(hasDerivAt_reciprocal_reduced_L hQ hR hx0).differentiableAt, ?_⟩
  have hra := outerHorizon_lt_radiusOf hQ hx0
  have hD : 0 < delta M Q (radiusOf M Q x) := delta_pos hQ hra
  have h1 : HasDerivAt (fun y : ℝ => R (radiusOf M Q y))
      ((delta M Q (radiusOf M Q x) * staticSolution M Q (radiusOf M Q x) ^ 2 : ℝ) •
        deriv R (radiusOf M Q x)) x :=
    ((hR _ hra).1.hasDerivAt).scomp x (hasDerivAt_radiusOf_eq_mul_sq hQ hx0)
  have hG := ((hasDerivAt_staticSolution hQ hra).ofReal_comp).mul (hR _ hra).2
  have h2 := h1.add (hG.scomp x (hasDerivAt_radiusOf_eq_mul_sq hQ hx0))
  have hev : (deriv fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) =ᶠ[𝓝 x]
      fun y : ℝ => R (radiusOf M Q y) + ((staticSolution M Q (radiusOf M Q y) : ℝ) : ℂ) *
        (((delta M Q (radiusOf M Q y) : ℝ) : ℂ) * deriv R (radiusOf M Q y)) := by
    filter_upwards [Ioi_mem_nhds hx0] with y hy using
      (hasDerivAt_reciprocal_reduced_L hQ hR hy).deriv
  refine (h2.congr_deriv ?_).congr_of_eventuallyEq hev
  have hDc : ((delta M Q (radiusOf M Q x) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hD.ne'
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0.ne'
  simp only [Complex.real_smul, staticSolution_radiusOf hQ hx0]
  push_cast
  field_simp
  ring

/-! ### Subextremal, constant normalization -/

/-- `U_y = −ΔR'` at `r = r(y)` for `U(y) = R(r(y))`, `r(y) = radiusOf M Q (1/y)`, `y > 0`. -/
theorem hasDerivAt_constant_reduced_L {M Q e ω L : ℝ} (hQ : |Q| < M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => R (radiusOf M Q (1 / t)))
      (-((delta M Q (radiusOf M Q (1 / y)) : ℝ) : ℂ) * deriv R (radiusOf M Q (1 / y))) y := by
  have hra := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy)
  have h := ((hR _ hra).1.hasDerivAt).scomp y (hasDerivAt_radiusOf_one_div hQ hy)
  refine h.congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  ring

/-- (2.4), subextremal, constant normalization `g = 1`, reflected coordinate `y = h = −x`:
`U(y) = R(r(y))` solves `U_yy + (k² − V)U = 0` on `y > 0`, with `k = K`, `V = LΔ` at
`r = r(y)`. -/
theorem constant_reduction_L {M Q e ω L : ℝ} (hQ : |Q| < M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    ∀ y ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun t : ℝ => R (radiusOf M Q (1 / t))) y ∧
        HasDerivAt (deriv fun t : ℝ => R (radiusOf M Q (1 / t)))
          (-((radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
              L * delta M Q (radiusOf M Q (1 / y)) : ℝ) : ℂ) *
            R (radiusOf M Q (1 / y))) y := by
  intro y hy
  have hy0 : 0 < y := hy
  refine ⟨(hasDerivAt_constant_reduced_L hQ hR hy0).differentiableAt, ?_⟩
  have hra := outerHorizon_lt_radiusOf hQ (one_div_pos.2 hy0)
  have hD : 0 < delta M Q (radiusOf M Q (1 / y)) := delta_pos hQ hra
  have hev : (deriv fun t : ℝ => R (radiusOf M Q (1 / t))) =ᶠ[𝓝 y]
      fun t : ℝ => -(((delta M Q (radiusOf M Q (1 / t)) : ℝ) : ℂ) *
        deriv R (radiusOf M Q (1 / t))) := by
    filter_upwards [Ioi_mem_nhds hy0] with t ht
    rw [(hasDerivAt_constant_reduced_L hQ hR ht).deriv]
    ring
  have hG := ((hR _ hra).2).scomp y (hasDerivAt_radiusOf_one_div hQ hy0)
  refine (hG.neg.congr_deriv ?_).congr_of_eventuallyEq hev
  have hDc : ((delta M Q (radiusOf M Q (1 / y)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hD.ne'
  rw [Complex.real_smul]
  push_cast
  field_simp

/-! ### Extremal, reciprocal normalization -/

/-- `U' = R(M + x) + x R'(M + x)` for `U(x) = x R(M + x)`, `x > 0`, in the extremal case
(`= R + gΔR'` with `g = 1/x`, `Δ = x²`). -/
theorem hasDerivAt_extremal_reciprocal_reduced_L {M Q e ω L : ℝ} (hQ : |Q| = M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (t : ℂ) * R (M + t))
      (R (M + x) + (x : ℂ) * deriv R (M + x)) x := by
  have hra : M + x ∈ Ioi (outerHorizon M Q) := by
    rw [mem_Ioi, outerHorizon_of_abs_eq hQ]
    linarith
  have h1 := ((hR _ hra).1.hasDerivAt).comp_const_add M x
  refine ((hasDerivAt_id' x).ofReal_comp.mul h1).congr_deriv ?_
  push_cast
  ring

/-- (2.4), extremal, reciprocal normalization `g = h = 1/(r − M)`, `x = r − M`:
`U(x) = x R(M + x)` solves `U_xx + (k² − V)U = 0` on `x > 0`, with `k = K/x²`, `V = L/x²`. -/
theorem extremal_reciprocal_reduction_L {M Q e ω L : ℝ} (hQ : |Q| = M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    ∀ x ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun t : ℝ => (t : ℂ) * R (M + t)) x ∧
        HasDerivAt (deriv fun t : ℝ => (t : ℂ) * R (M + t))
          (-(((radialK e ω (M + x) / x ^ 2) ^ 2 - L / x ^ 2 : ℝ) : ℂ) *
            ((x : ℂ) * R (M + x))) x := by
  intro x hx
  have hx0 : 0 < x := hx
  refine ⟨(hasDerivAt_extremal_reciprocal_reduced_L hQ hR hx0).differentiableAt, ?_⟩
  have hra : M + x ∈ Ioi (outerHorizon M Q) := by
    rw [mem_Ioi, outerHorizon_of_abs_eq hQ]
    linarith
  -- on `t > 0`, `U'(t) = R(M + t) + t⁻¹ · (ΔR')(M + t)` since `Δ(M + t) = t²`
  have hev : (deriv fun t : ℝ => (t : ℂ) * R (M + t)) =ᶠ[𝓝 x]
      fun t : ℝ => R (M + t) + ((t⁻¹ : ℝ) : ℂ) *
        (((delta M Q (M + t) : ℝ) : ℂ) * deriv R (M + t)) := by
    filter_upwards [Ioi_mem_nhds hx0] with t ht
    rw [(hasDerivAt_extremal_reciprocal_reduced_L hQ hR ht).deriv, delta_of_abs_eq hQ,
      add_sub_cancel_left]
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ht)
    push_cast
    field_simp
  have h1 := ((hR _ hra).1.hasDerivAt).comp_const_add M x
  have h2 := ((hasDerivAt_inv hx0.ne').ofReal_comp).mul ((hR _ hra).2.comp_const_add M x)
  refine ((h1.add h2).congr_deriv ?_).congr_of_eventuallyEq hev
  rw [delta_of_abs_eq hQ, add_sub_cancel_left]
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0.ne'
  push_cast
  field_simp
  ring

/-! ### Extremal, constant normalization -/

/-- `U_y = −R'(M + 1/y)/y²` for `U(y) = R(M + 1/y)`, `y > 0`, in the extremal case
(`= −ΔR'` with `Δ = 1/y²`). -/
theorem hasDerivAt_extremal_constant_reduced_L {M Q e ω L : ℝ} (hQ : |Q| = M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => R (M + 1 / t)) (-deriv R (M + 1 / y) / (y : ℂ) ^ 2) y := by
  have hra : M + 1 / y ∈ Ioi (outerHorizon M Q) := by
    rw [mem_Ioi, outerHorizon_of_abs_eq hQ]
    have := one_div_pos.2 hy
    linarith
  have hr : HasDerivAt (fun t : ℝ => M + 1 / t) (-(y ^ 2)⁻¹) y := by
    simpa only [one_div] using (hasDerivAt_inv hy.ne').const_add M
  refine (((hR _ hra).1.hasDerivAt).scomp y hr).congr_deriv ?_
  rw [Complex.real_smul]
  push_cast
  ring

/-- (2.4), extremal, constant normalization `g = 1`, reflected coordinate `y = h = 1/(r − M)`:
`U(y) = R(M + 1/y)` solves `U_yy + (k² − V)U = 0` on `y > 0`, with `k = K`, `V = L/y²` at
`r = M + 1/y`. -/
theorem extremal_constant_reduction_L {M Q e ω L : ℝ} (hQ : |Q| = M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    ∀ y ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun t : ℝ => R (M + 1 / t)) y ∧
        HasDerivAt (deriv fun t : ℝ => R (M + 1 / t))
          (-((radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2 : ℝ) : ℂ) * R (M + 1 / y)) y := by
  intro y hy
  have hy0 : 0 < y := hy
  refine ⟨(hasDerivAt_extremal_constant_reduced_L hQ hR hy0).differentiableAt, ?_⟩
  have hra : M + 1 / y ∈ Ioi (outerHorizon M Q) := by
    rw [mem_Ioi, outerHorizon_of_abs_eq hQ]
    have := one_div_pos.2 hy0
    linarith
  -- on `t > 0`, `U_t = −(ΔR')(M + 1/t)` since `Δ(M + 1/t) = 1/t²`
  have hev : (deriv fun t : ℝ => R (M + 1 / t)) =ᶠ[𝓝 y]
      fun t : ℝ => -(((delta M Q (M + 1 / t) : ℝ) : ℂ) * deriv R (M + 1 / t)) := by
    filter_upwards [Ioi_mem_nhds hy0] with t ht
    rw [(hasDerivAt_extremal_constant_reduced_L hQ hR ht).deriv, delta_of_abs_eq hQ,
      add_sub_cancel_left]
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ht)
    push_cast
    field_simp
  have hr : HasDerivAt (fun t : ℝ => M + 1 / t) (-(y ^ 2)⁻¹) y := by
    simpa only [one_div] using (hasDerivAt_inv hy0.ne').const_add M
  have hG := ((hR _ hra).2).scomp y hr
  refine (hG.neg.congr_deriv ?_).congr_of_eventuallyEq hev
  rw [Complex.real_smul, delta_of_abs_eq hQ, add_sub_cancel_left]
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy0.ne'
  push_cast
  field_simp

end ModeStability.AllAngular

end
