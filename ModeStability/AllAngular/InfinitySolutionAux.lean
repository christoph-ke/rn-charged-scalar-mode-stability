module

public import Mathlib
public import ModeStability.AllAngular.InfinityUniqueness

/-!
# The outgoing solution at infinity: coefficients of the amplitude system

Auxiliary material for `ModeStability.AllAngular.InfinitySolution`, which constructs the
solution `R_I` of the radial equation normalized by the outgoing condition (1.5) of
the all-angular research notes in preparation with leading coefficient `1` (used in Sections 6
and 8 of the paper).

With `u = rR`, `Θ' = K/Δ` and the amplitudes `A = e^{−iΘ}(u' + iΘ'u)`,
`B = e^{iΘ}(u' − iΘ'u)` of `ModeStability.AllAngular.InfinityUniqueness`, the radial equation
becomes the linear system

`A' = (ρ₊ + iσ)A + e^{−2iΘ}(ρ₋ − iσ)B`,  `B' = e^{2iΘ}(ρ₋ + iσ)A + (ρ₊ − iσ)B`,

with the real coefficients `ρ± = −α/2 ± Θ''/(2Θ')` and `σ = γ/(2Θ')`. This file defines the
entries (`ampCoeffAA`, `ampCoeffAB`, `ampCoeffBA`, `ampCoeffBB`), bounds them by the error
coefficient `errCoeff = O(r⁻²)`, and proves the rates needed for the outgoing asymptotics:

* `isBigO_phaseRate_sub`: `Θ' − ω = O(r⁻¹)`;
* `isBigO_ampRhoM_sub`, `isBigO_ampSigma_sub`: `r²ρ₋ + (e/(2ω²))Θ' = O(r⁻¹)` and
  `r²σ + (L/(2ω²))Θ' = O(r⁻¹)` (from the closed forms `ρ₋ = −e/(2r(ωr − e))`,
  `σ = −(Lr² + 2Mr − 2Q²)/(2r³(ωr − e))`), so that the coefficient of `e^{2iΘ}A` in `B'` is
  `2iκΘ'/r² + O(r⁻³)`, `κ = −(e + iL)/(4iω²)`;
* `norm_le_of_tendsto_zero_of_norm_deriv_le_cube`: the tail estimate `‖c(s)‖ ≤ D/(2s²)` for
  `c → 0` with `‖c'(t)‖ ≤ D/t³`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

namespace InfinitySolution

open InfinityUniqueness

/-! ### The coefficients -/

/-- `ρ₊ = −α/2 + Θ''/(2Θ')`. -/
@[expose] noncomputable def ampRhoP (M Q e ω r : ℝ) : ℝ :=
  -dampCoeff M Q r / 2 + phaseAccel M Q e ω r / (2 * phaseRate M Q e ω r)

/-- `ρ₋ = −α/2 − Θ''/(2Θ')`. -/
@[expose] noncomputable def ampRhoM (M Q e ω r : ℝ) : ℝ :=
  -dampCoeff M Q r / 2 - phaseAccel M Q e ω r / (2 * phaseRate M Q e ω r)

/-- `σ = γ/(2Θ')`. -/
@[expose] noncomputable def ampSigma (M Q e ω L r : ℝ) : ℝ :=
  potCoeff M Q L r / (2 * phaseRate M Q e ω r)

/-- The coefficient of `A` in `A'`: `ρ₊ + iσ`. -/
@[expose] noncomputable def ampCoeffAA (M Q e ω L r : ℝ) : ℂ :=
  ampRhoP M Q e ω r + I * ampSigma M Q e ω L r

/-- The coefficient of `B` in `A'`: `e^{−2iΘ}(ρ₋ − iσ)`. -/
@[expose] noncomputable def ampCoeffAB (M Q e ω L : ℝ) (Θ : ℝ → ℝ) (r : ℝ) : ℂ :=
  exp (-(I * Θ r)) ^ 2 * (ampRhoM M Q e ω r - I * ampSigma M Q e ω L r)

/-- The coefficient of `A` in `B'`: `e^{2iΘ}(ρ₋ + iσ)`. -/
@[expose] noncomputable def ampCoeffBA (M Q e ω L : ℝ) (Θ : ℝ → ℝ) (r : ℝ) : ℂ :=
  exp (I * Θ r) ^ 2 * (ampRhoM M Q e ω r + I * ampSigma M Q e ω L r)

/-- The coefficient of `B` in `B'`: `ρ₊ − iσ`. -/
@[expose] noncomputable def ampCoeffBB (M Q e ω L r : ℝ) : ℂ :=
  ampRhoP M Q e ω r - I * ampSigma M Q e ω L r

/-! ### Bounds by the error coefficient -/

/-- `|ρ±| + |σ| ≤ |α|/2 + (|γ| + |Θ''|)/(2|Θ'|)`. -/
theorem abs_ampRho_add_abs_ampSigma_le (M Q e ω L r : ℝ) :
    |ampRhoP M Q e ω r| + |ampSigma M Q e ω L r| ≤ errCoeff M Q e ω L r ∧
      |ampRhoM M Q e ω r| + |ampSigma M Q e ω L r| ≤ errCoeff M Q e ω L r := by
  have e1 : |phaseAccel M Q e ω r / (2 * phaseRate M Q e ω r)| =
      |phaseAccel M Q e ω r| / (2 * |phaseRate M Q e ω r|) := by
    rw [abs_div, abs_mul, abs_two]
  have e2 : |ampSigma M Q e ω L r| = |potCoeff M Q L r| / (2 * |phaseRate M Q e ω r|) := by
    unfold ampSigma
    rw [abs_div, abs_mul, abs_two]
  have e3 : |-dampCoeff M Q r / 2| = |dampCoeff M Q r| / 2 := by
    rw [abs_div, abs_neg, abs_two]
  have e4 : errCoeff M Q e ω L r = |dampCoeff M Q r| / 2 +
      |potCoeff M Q L r| / (2 * |phaseRate M Q e ω r|) +
        |phaseAccel M Q e ω r| / (2 * |phaseRate M Q e ω r|) := by
    unfold errCoeff
    rw [add_div]
    ring
  constructor
  · have h := abs_add_le (-dampCoeff M Q r / 2) (phaseAccel M Q e ω r / (2 * phaseRate M Q e ω r))
    unfold ampRhoP
    linarith
  · have h := abs_sub (-dampCoeff M Q r / 2) (phaseAccel M Q e ω r / (2 * phaseRate M Q e ω r))
    unfold ampRhoM
    linarith

/-- `‖ρ + iσ‖ ≤ |ρ| + |σ|`. -/
theorem norm_ofReal_add_I_mul_le (ρ σ : ℝ) : ‖(ρ : ℂ) + I * σ‖ ≤ |ρ| + |σ| := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

/-- `‖ρ − iσ‖ ≤ |ρ| + |σ|`. -/
theorem norm_ofReal_sub_I_mul_le (ρ σ : ℝ) : ‖(ρ : ℂ) - I * σ‖ ≤ |ρ| + |σ| := by
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]

theorem norm_ampCoeffAA_le (M Q e ω L r : ℝ) :
    ‖ampCoeffAA M Q e ω L r‖ ≤ errCoeff M Q e ω L r :=
  (norm_ofReal_add_I_mul_le _ _).trans (abs_ampRho_add_abs_ampSigma_le M Q e ω L r).1

theorem norm_ampCoeffBB_le (M Q e ω L r : ℝ) :
    ‖ampCoeffBB M Q e ω L r‖ ≤ errCoeff M Q e ω L r :=
  (norm_ofReal_sub_I_mul_le _ _).trans (abs_ampRho_add_abs_ampSigma_le M Q e ω L r).1

theorem norm_ampCoeffAB_le (M Q e ω L : ℝ) (Θ : ℝ → ℝ) (r : ℝ) :
    ‖ampCoeffAB M Q e ω L Θ r‖ ≤ errCoeff M Q e ω L r := by
  unfold ampCoeffAB
  rw [norm_mul, norm_pow, norm_exp_neg_I_mul, one_pow, one_mul]
  exact (norm_ofReal_sub_I_mul_le _ _).trans (abs_ampRho_add_abs_ampSigma_le M Q e ω L r).2

theorem norm_ampCoeffBA_le (M Q e ω L : ℝ) (Θ : ℝ → ℝ) (r : ℝ) :
    ‖ampCoeffBA M Q e ω L Θ r‖ ≤ errCoeff M Q e ω L r := by
  unfold ampCoeffBA
  rw [norm_mul, norm_pow, norm_exp_I_mul, one_pow, one_mul]
  exact (norm_ofReal_add_I_mul_le _ _).trans (abs_ampRho_add_abs_ampSigma_le M Q e ω L r).2

/-! ### Closed forms -/

/-- `K = r(ωr − e)`. -/
theorem radialK_eq_mul (e ω r : ℝ) : radialK e ω r = r * (ω * r - e) := by
  unfold radialK
  ring

/-- `ρ₋ = −e/(2r(ωr − e))`. -/
theorem ampRhoM_eq {M Q e ω r : ℝ} (hQ : |Q| ≤ M) (hr : r ≠ 0) (hΔ : delta M Q r ≠ 0)
    (hK : ω * r - e ≠ 0) : ampRhoM M Q e ω r = -e / (2 * r * (ω * r - e)) := by
  have hD := delta_eq hQ r
  unfold ampRhoM dampCoeff phaseAccel phaseRate
  rw [radialK_eq_mul]
  generalize hx : ω * r - e = x at hK ⊢
  generalize delta M Q r = D at hΔ hD ⊢
  field_simp
  subst hx hD
  ring

/-- `σ = −(Lr² + 2Mr − 2Q²)/(2r³(ωr − e))`. -/
theorem ampSigma_eq {M Q e ω L r : ℝ} (hr : r ≠ 0) (hΔ : delta M Q r ≠ 0)
    (hK : ω * r - e ≠ 0) :
    ampSigma M Q e ω L r = -(L * r ^ 2 + 2 * M * r - 2 * Q ^ 2) / (2 * r ^ 3 * (ω * r - e)) := by
  unfold ampSigma potCoeff phaseRate
  rw [radialK_eq_mul]
  generalize ω * r - e = x at hK ⊢
  generalize delta M Q r = D at hΔ ⊢
  field_simp
  ring

/-- `Θ' = (ω − e r⁻¹)/(1 − 2M r⁻¹ + Q² r⁻²)`. -/
theorem phaseRate_eq_inv {M Q e ω r : ℝ} (hQ : |Q| ≤ M) (hr : r ≠ 0)
    (hD : 1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2 ≠ 0) :
    phaseRate M Q e ω r = (ω - e * r⁻¹) / (1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2) := by
  unfold phaseRate radialK
  rw [delta_eq_sq_mul hQ hr]
  generalize 1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2 = D at hD ⊢
  field_simp

/-! ### Rates at infinity -/

/-- A function that is eventually `F(1/r)` with `F` differentiable at `0` differs from `F(0)` by
`O(r⁻¹)`. -/
theorem isBigO_sub_of_eventuallyEq_comp_inv {f F : ℝ → ℝ} {c : ℝ} (hF : DifferentiableAt ℝ F 0)
    (hc : F 0 = c) (hfF : ∀ᶠ r in atTop, f r = F r⁻¹) :
    (fun r => f r - c) =O[atTop] (fun r => r⁻¹) := by
  have h := hF.hasDerivAt.isBigO_sub.comp_tendsto tendsto_inv_atTop_zero
  simp only [Function.comp_def, sub_zero, hc] at h
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hfF] with r hr
  rw [hr]

/-- Eventually `r > 0`, `r > a`, `Δ > 0`, `Δ/r² ≠ 0` and `ω − e r⁻¹ ≠ 0` (for `ω ≠ 0`). -/
theorem eventually_good_inv {M Q e ω : ℝ} (hQ : |Q| ≤ M) (hω : ω ≠ 0) :
    ∀ᶠ r : ℝ in atTop, 0 < r ∧ outerHorizon M Q < r ∧ 0 < delta M Q r ∧
      (1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2) ≠ 0 ∧ ω - e * r⁻¹ ≠ 0 ∧ ω * r - e ≠ 0 := by
  have hlim : Tendsto (fun r : ℝ => ω - e * r⁻¹) atTop (𝓝 ω) := by
    simpa using (tendsto_const_nhds (x := ω)).sub (tendsto_inv_atTop_zero.const_mul e)
  filter_upwards [eventually_good hQ, eventually_gt_atTop (outerHorizon M Q),
    hlim.eventually_ne hω] with r ⟨hr0, hΔ, hD⟩ hra hne
  refine ⟨hr0, hra, hΔ, hD, hne, ?_⟩
  have : ω * r - e = r * (ω - e * r⁻¹) := by field_simp
  rw [this]
  exact mul_ne_zero hr0.ne' hne

theorem differentiableAt_phaseRate_inv (M Q e ω : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => (ω - e * y) / (1 - 2 * M * y + Q ^ 2 * y ^ 2)) 0 :=
  DifferentiableAt.div (by fun_prop) (by fun_prop) (by norm_num)

/-- `Θ' − ω = O(r⁻¹)` at infinity. -/
theorem isBigO_phaseRate_sub {M Q : ℝ} (hQ : |Q| ≤ M) (e : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    (fun r => phaseRate M Q e ω r - ω) =O[atTop] (fun r => r⁻¹) := by
  refine isBigO_sub_of_eventuallyEq_comp_inv (differentiableAt_phaseRate_inv M Q e ω)
    (by norm_num) ?_
  filter_upwards [eventually_good_inv (e := e) hQ hω] with r ⟨hr0, _, _, hD, _, _⟩
  exact phaseRate_eq_inv hQ hr0.ne' hD

/-- `r²ρ₋ + (e/(2ω²))Θ' = O(r⁻¹)` at infinity. -/
theorem isBigO_ampRhoM_sub {M Q : ℝ} (hQ : |Q| ≤ M) (e : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    (fun r => r ^ 2 * ampRhoM M Q e ω r - (-e / (2 * ω ^ 2)) * phaseRate M Q e ω r)
      =O[atTop] (fun r => r⁻¹) := by
  have hF : DifferentiableAt ℝ (fun y : ℝ => -e / (2 * (ω - e * y)) -
      (-e / (2 * ω ^ 2)) * ((ω - e * y) / (1 - 2 * M * y + Q ^ 2 * y ^ 2))) 0 := by
    refine DifferentiableAt.sub (DifferentiableAt.div (by fun_prop) (by fun_prop) ?_)
      ((differentiableAt_phaseRate_inv M Q e ω).const_mul _)
    simpa using hω
  have h := isBigO_sub_of_eventuallyEq_comp_inv (c := 0) (f := fun r =>
    r ^ 2 * ampRhoM M Q e ω r - (-e / (2 * ω ^ 2)) * phaseRate M Q e ω r) hF
    (by field_simp; ring) ?_
  · simpa using h
  filter_upwards [eventually_good_inv (e := e) hQ hω] with r ⟨hr0, _, hΔ, hD, hne, hK⟩
  rw [ampRhoM_eq hQ hr0.ne' hΔ.ne' hK, phaseRate_eq_inv hQ hr0.ne' hD]
  congr 1
  have hr := hr0.ne'
  field_simp

/-- `r²σ + (L/(2ω²))Θ' = O(r⁻¹)` at infinity. -/
theorem isBigO_ampSigma_sub {M Q : ℝ} (hQ : |Q| ≤ M) (e L : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    (fun r => r ^ 2 * ampSigma M Q e ω L r - (-L / (2 * ω ^ 2)) * phaseRate M Q e ω r)
      =O[atTop] (fun r => r⁻¹) := by
  have hF : DifferentiableAt ℝ (fun y : ℝ => -(L + 2 * M * y - 2 * Q ^ 2 * y ^ 2) /
      (2 * (ω - e * y)) -
      (-L / (2 * ω ^ 2)) * ((ω - e * y) / (1 - 2 * M * y + Q ^ 2 * y ^ 2))) 0 := by
    refine DifferentiableAt.sub (DifferentiableAt.div (by fun_prop) (by fun_prop) ?_)
      ((differentiableAt_phaseRate_inv M Q e ω).const_mul _)
    simpa using hω
  have h := isBigO_sub_of_eventuallyEq_comp_inv (c := 0) (f := fun r =>
    r ^ 2 * ampSigma M Q e ω L r - (-L / (2 * ω ^ 2)) * phaseRate M Q e ω r) hF
    (by field_simp; ring) ?_
  · simpa using h
  filter_upwards [eventually_good_inv (e := e) hQ hω] with r ⟨hr0, _, hΔ, hD, hne, hK⟩
  rw [ampSigma_eq hr0.ne' hΔ.ne' hK, phaseRate_eq_inv hQ hr0.ne' hD]
  congr 1
  have hr := hr0.ne'
  field_simp

/-! ### The cubic tail estimate -/

/-- If `c → 0` at `+∞` and `‖c'(t)‖ ≤ D/t³` on `[s, ∞)` with `s > 0`, then
`‖c(s)‖ ≤ D/(2s²)`. -/
theorem norm_le_of_tendsto_zero_of_norm_deriv_le_cube {c c' : ℝ → ℂ} {s D : ℝ} (hs : 0 < s)
    (hc : ∀ t, s ≤ t → HasDerivAt c (c' t) t) (hb : ∀ t, s ≤ t → ‖c' t‖ ≤ D / t ^ 3)
    (hlim : Tendsto c atTop (𝓝 0)) : ‖c s‖ ≤ D / (2 * s ^ 2) := by
  have hD : 0 ≤ D := by
    have h := (norm_nonneg _).trans (hb s le_rfl)
    have hs3 : 0 < s ^ 3 := by positivity
    by_contra hneg
    have : D / s ^ 3 < 0 := div_neg_of_neg_of_pos (not_le.1 hneg) hs3
    linarith
  have key : ∀ t, s ≤ t → ‖c t - c s‖ ≤ D / (2 * s ^ 2) - D / (2 * t ^ 2) := by
    intro t hst
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := fun x => c x - c s)
      (f' := c') (B := fun x => D / (2 * s ^ 2) - D / (2 * x ^ 2)) (B' := fun x => D / x ^ 3)
      ?_ ?_ ?_ ?_ ?_ ?_ (right_mem_Icc.2 hst)
    · intro x hx
      exact ((hc x hx.1).continuousAt.sub continuousAt_const).continuousWithinAt
    · intro x hx
      exact ((hc x hx.1).sub_const (c s)).hasDerivWithinAt
    · simp
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
      have h2 : (2 * x ^ 2) ≠ 0 := by positivity
      exact (continuousAt_const.sub (continuousAt_const.div
        (continuousAt_const.mul (continuousAt_id.pow 2)) h2)).continuousWithinAt
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
      have h2 : (2 * x ^ 2) ≠ 0 := by positivity
      have h := ((hasDerivAt_const x D).div ((hasDerivAt_pow 2 x).const_mul 2) h2).const_sub
        (D / (2 * s ^ 2))
      refine HasDerivAt.hasDerivWithinAt ?_
      convert h using 1
      field_simp
      ring
    · intro x hx
      exact hb x hx.1
  have hT : Tendsto (fun t => ‖c t - c s‖) atTop (𝓝 ‖0 - c s‖) := (hlim.sub_const (c s)).norm
  rw [zero_sub, norm_neg] at hT
  refine le_of_tendsto hT (eventually_atTop.2 ⟨s, fun t hst => ?_⟩)
  have : 0 ≤ D / (2 * t ^ 2) := div_nonneg hD (by positivity)
  linarith [key t hst]

end InfinitySolution

end ModeStability.AllAngular

end
