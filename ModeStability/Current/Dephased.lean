module

public import Mathlib

/-!
# Lemma 2.2: the dephased current

Source: the spherical research notes in preparation, Lemma 2.2 (equations (2.5)-(2.8)).

For a real `C²` function `k` with `k_x > 0` on `(0, ∞)` and a solution `U` of `U_xx + k² U = 0`,
put `ϑ(x) = ∫_{x₀}^x k`, `v = e^{iσϑ} U` with `σ = ±1`, and
`J[v] = -(k / k_x) |v_x|² - Re (v_x v̄)`.  Then `J[v]' = -((2 k_x² - k k_xx) / k_x²) |v_x|²`, and
`J[v](x₀) = -Re (U_x(x₀) Ū(x₀))` when `k(x₀) = 0`.

The file is organised as reusable lemmas:

* `hasDerivAt_phase`: `ϑ' = k` (fundamental theorem of calculus);
* `hasDerivAt_dephased`, `deriv_dephased`: the formula for `v_x`;
* `hasDerivAt_deriv_dephased`: the conjugated equation `v_xx = iσ (2 k v_x + k_x v)`;
* `hasDerivAt_current`: the derivative of `J` for any `v` solving the conjugated equation;
* `dephased_current_aux`: Lemma 2.2.
-/

public section

open Complex Set

namespace ModeStability.Current

/-- `ϑ(x) = ∫_{x₀}^x k` has derivative `k(x)` at every `x > 0` (fundamental theorem of calculus),
provided `k` is continuous on `(0, ∞)` and `x₀ > 0`. -/
theorem hasDerivAt_phase {k : ℝ → ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀) (hk : ContinuousOn k (Ioi 0))
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => ∫ ξ in x₀..y, k ξ) (k x) x := by
  refine intervalIntegral.integral_hasDerivAt_right ?_
    (hk.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hk.continuousAt (Ioi_mem_nhds hx))
  exact (hk.mono (Set.ordConnected_Ioi.uIcc_subset hx₀ hx)).intervalIntegrable

/-- A `C²` function on `(0, ∞)` is differentiable at every `x > 0`. -/
theorem differentiableAt_of_contDiffOn {k : ℝ → ℝ} (hk : ContDiffOn ℝ 2 k (Ioi 0)) {x : ℝ}
    (hx : 0 < x) : DifferentiableAt ℝ k x :=
  (hk.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hx)

/-- The derivative of a `C²` function on `(0, ∞)` is differentiable at every `x > 0`. -/
theorem differentiableAt_deriv_of_contDiffOn {k : ℝ → ℝ} (hk : ContDiffOn ℝ 2 k (Ioi 0)) {x : ℝ}
    (hx : 0 < x) : DifferentiableAt ℝ (deriv k) x :=
  ((hk.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).differentiableOn
    (by norm_num)).differentiableAt (Ioi_mem_nhds hx)

/-- The dephased function `v = e^{iσϑ} U` has the derivative `e^{iσϑ} (U_x + iσ k U)`. -/
theorem hasDerivAt_dephased {k : ℝ → ℝ} {U : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hk : ContinuousOn k (Ioi 0)) (σ : ℝ) {x : ℝ} (hx : 0 < x) (hU : DifferentiableAt ℝ U x) :
    HasDerivAt (fun y => exp (σ * (∫ ξ in x₀..y, k ξ) * I) * U y)
      (exp (σ * (∫ ξ in x₀..x, k ξ) * I) * (deriv U x + σ * k x * I * U x)) x := by
  have hphase := ((hasDerivAt_phase hx₀ hk hx).ofReal_comp.const_mul (σ : ℂ)).mul_const I
  have h := hphase.cexp.mul hU.hasDerivAt
  convert h using 1
  ring

/-- Formula for the derivative of the dephased function. -/
theorem deriv_dephased {k : ℝ → ℝ} {U : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hk : ContinuousOn k (Ioi 0)) (σ : ℝ) {x : ℝ} (hx : 0 < x) (hU : DifferentiableAt ℝ U x) :
    deriv (fun y => exp (σ * (∫ ξ in x₀..y, k ξ) * I) * U y) x =
      exp (σ * (∫ ξ in x₀..x, k ξ) * I) * (deriv U x + σ * k x * I * U x) :=
  (hasDerivAt_dephased hx₀ hk σ hx hU).deriv

/-- The conjugated equation: `v = e^{iσϑ} U` with `U_xx = -k² U` and `σ = ±1` satisfies
`v_xx = iσ (2 k v_x + k_x v)`. -/
theorem hasDerivAt_deriv_dephased {k : ℝ → ℝ} {U : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hk : ContDiffOn ℝ 2 k (Ioi 0)) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv fun y => exp (σ * (∫ ξ in x₀..y, k ξ) * I) * U y)
      (σ * I * (2 * k x * deriv (fun y => exp (σ * (∫ ξ in x₀..y, k ξ) * I) * U y) x +
        deriv k x * (exp (σ * (∫ ξ in x₀..x, k ξ) * I) * U x))) x := by
  have hσ2 : (σ : ℂ) ^ 2 = 1 := by
    rcases hσ with rfl | rfl <;> simp
  have hkc : ContinuousOn k (Ioi 0) := hk.continuousOn
  have hkd := (differentiableAt_of_contDiffOn hk hx).hasDerivAt
  -- the derivative of `v` agrees with an explicit formula near `x`
  have heq : (deriv fun y => exp (σ * (∫ ξ in x₀..y, k ξ) * I) * U y) =ᶠ[nhds x]
      fun y => exp (σ * (∫ ξ in x₀..y, k ξ) * I) * (deriv U y + σ * k y * I * U y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact deriv_dephased hx₀ hkc σ hy (hU y hy).1
  have hphase := ((hasDerivAt_phase hx₀ hkc hx).ofReal_comp.const_mul (σ : ℂ)).mul_const I
  have hE := hphase.cexp
  have hF := (hU x hx).2.add (((hkd.ofReal_comp.const_mul (σ : ℂ)).mul_const I).mul
    (hU x hx).1.hasDerivAt)
  have h := (hE.mul hF).congr_of_eventuallyEq heq
  rw [deriv_dephased hx₀ hkc σ hx (hU x hx).1]
  simp only [Pi.add_apply, Pi.mul_apply] at h
  convert h using 1
  push_cast
  linear_combination (exp (σ * (∫ ξ in x₀..x, k ξ) * I) * (k x : ℂ) ^ 2 * U x * I ^ 2) * hσ2 +
    (exp (σ * (∫ ξ in x₀..x, k ξ) * I) * (k x : ℂ) ^ 2 * U x) * Complex.I_sq

/-- The derivative of the real part of a complex-valued function of a real variable. -/
theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

/-- The current `J[v] = -(k / k_x) |v_x|² - Re (v_x v̄)` of any `v` satisfying the conjugated
equation `v_xx = iσ (2 k v_x + k_x v)` has derivative `-((2 k_x² - k k_xx) / k_x²) |v_x|²`. -/
theorem hasDerivAt_current {k : ℝ → ℝ} {v : ℝ → ℂ} {σ : ℝ} {x : ℝ}
    (hk : DifferentiableAt ℝ k x) (hk' : DifferentiableAt ℝ (deriv k) x) (hkx : deriv k x ≠ 0)
    (hv : DifferentiableAt ℝ v x)
    (hv' : HasDerivAt (deriv v) (σ * I * (2 * k x * deriv v x + deriv k x * v x)) x) :
    HasDerivAt
      (fun y => -(k y / deriv k y) * ‖deriv v y‖ ^ 2 -
        (deriv v y * (starRingEnd ℂ) (v y)).re)
      (-((2 * deriv k x ^ 2 - k x * deriv (deriv k) x) / deriv k x ^ 2) * ‖deriv v x‖ ^ 2) x := by
  have hq := (hk.hasDerivAt.div hk'.hasDerivAt hkx).neg
  have hN := hv'.norm_sq
  have hP := hasDerivAt_re (hv'.mul hv.hasDerivAt.star)
  have h := (hq.mul hN).sub hP
  convert h using 1
  · rfl
  have hqx : (-(k / deriv k)) x = -(k x / deriv k x) := rfl
  rw [hqx]
  generalize deriv v x = w at *
  generalize v x = u at *
  generalize deriv k x = K' at *
  generalize k x = K at *
  generalize deriv (deriv k) x = K'' at *
  simp only [Complex.inner, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.re_ofNat,
    Complex.im_ofNat]
  field_simp
  ring

/-- **Lemma 2.2 (dephased current).** Let `k` be real and `C²` on `(0, ∞)` with `k_x > 0`, let
`U_xx + k² U = 0`, `k(x₀) = 0`, and `v = e^{iσϑ} U` with `ϑ(x) = ∫_{x₀}^x k` and `σ = ±1`.
Then the current `J[v] = -(k / k_x) |v_x|² - Re (v_x v̄)` satisfies
`J' = -((2 k_x² - k k_xx) / k_x²) |v_x|²` on `(0, ∞)`, and `J(x₀) = -Re (U_x(x₀) Ū(x₀))`. -/
theorem dephased_current_aux (k : ℝ → ℝ) (U : ℝ → ℂ) (x₀ : ℝ) (hx₀ : 0 < x₀)
    (hk : ContDiffOn ℝ 2 k (Ioi 0)) (hkx : ∀ x ∈ Ioi (0 : ℝ), 0 < deriv k x)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x)
    (hk₀ : k x₀ = 0) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    let v : ℝ → ℂ := fun x => exp (σ * (∫ ξ in x₀..x, k ξ) * I) * U x
    let J : ℝ → ℝ := fun x => -(k x / deriv k x) * ‖deriv v x‖ ^ 2 -
      (deriv v x * (starRingEnd ℂ) (v x)).re
    (∀ x ∈ Ioi (0 : ℝ), HasDerivAt J
        (-((2 * deriv k x ^ 2 - k x * deriv (deriv k) x) / deriv k x ^ 2) * ‖deriv v x‖ ^ 2) x) ∧
      J x₀ = -(deriv U x₀ * (starRingEnd ℂ) (U x₀)).re := by
  intro v J
  have hkc : ContinuousOn k (Ioi 0) := hk.continuousOn
  refine ⟨fun x hx => ?_, ?_⟩
  · have hx' : 0 < x := hx
    have hv : DifferentiableAt ℝ v x :=
      (hasDerivAt_dephased hx₀ hkc σ hx' (hU x hx).1).differentiableAt
    exact hasDerivAt_current (differentiableAt_of_contDiffOn hk hx')
      (differentiableAt_deriv_of_contDiffOn hk hx') (hkx x hx).ne' hv
      (hasDerivAt_deriv_dephased hx₀ hk hσ hU hx')
  · have hdv : deriv v x₀ = deriv U x₀ := by
      rw [show deriv v x₀ = _ from deriv_dephased hx₀ hkc σ hx₀ (hU x₀ hx₀).1]
      simp [hk₀]
    have hv : v x₀ = U x₀ := by simp [v]
    simp only [J, hdv, hv, hk₀]
    simp

end ModeStability.Current

end
