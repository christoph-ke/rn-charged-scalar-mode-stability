module

public import Mathlib
public import ModeStability.ODE.LinearVolterra
public import ModeStability.AllAngular.InfinityUniqueness
public import ModeStability.AllAngular.InfinitySolutionExtend

/-!
# The outgoing solution at infinity

Source: the all-angular research notes in preparation, (1.5), and Sections 6 and 8, which use
the outgoing solution with unit leading coefficient in (1.5). For `M > 0`, `|Q| ≤ M`,
real `e, L`, `ω ≠ 0` and a phase `Θ` with `Θ' = K/Δ` on `r > a`:

* `exists_infinity_solution`: there is a solution `R_I` of the radial equation
  `(ΔR')' + (K²/Δ − L)R = 0` on `r > a` with `r e^{−iΘ}R_I − 1 = O(r⁻¹)` and
  `(r e^{−iΘ}R_I)' = O(r⁻²)`, i.e. satisfying (1.5) with leading coefficient `B_I = 1`;
* `infinity_solution_unique`: two solutions of the radial equation on `r > a` satisfying the
  outgoing condition (1.5) with the same leading coefficient agree on `r > a` (from
  `ModeStability.AllAngular.eqOn_zero_of_outgoing_coefficient_zero`).

## Proof of existence

For large `r₁` (where `Θ' ≠ 0` and the coefficients are `O(r⁻²)`), the amplitude system of
`ModeStability.AllAngular.InfinitySolutionAux` has an integrable coefficient on `(r₁, ∞)`, so
`ModeStability.ODE.linear_exists_atTop` gives a solution `(A, B) → (2iω, 0)`. Then `R = u/r`
(`ModeStability.AllAngular.InfinitySolutionSystem`) solves the radial equation on `(r₁, ∞)` with
the outgoing asymptotics (`ModeStability.AllAngular.InfinitySolution.outgoing_ampSol`). It is
continued to `r > a` by solving the first-order system `R' = P/Δ`, `P' = −(K²/Δ − L)R`
(`ModeStability.ODE.linear_exists_Ioi`) with the same data at `r₁ + 1` and matching by interior
uniqueness (`ModeStability.AllAngular.InfinitySolution.exists_outgoing_of_amp`).
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

open InfinityUniqueness in
/-- **Uniqueness of the outgoing solution.** Two solutions of the radial equation
`(ΔR')' + (K²/Δ − L)R = 0` on `r > a` (`|Q| ≤ M`, `ω ≠ 0`, `Θ' = K/Δ`) satisfying the outgoing
condition (1.5), `r e^{−iΘ}R − B = O(r⁻¹)` and `(r e^{−iΘ}R)' = O(r⁻²)`, with the same leading
coefficient `B` agree on `r > a`. -/
theorem infinity_solution_unique {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : ω ≠ 0)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R₁ R₂ : ℝ → ℂ} {B : ℂ}
    (hR₁ : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R₁ r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R₁ s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R₁ r) r)
    (hR₂ : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R₂ r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R₂ s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R₂ r) r)
    (h₁₁ : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R₁ r - B) =O[atTop]
      (fun r : ℝ => r⁻¹))
    (h₁₂ : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R₁ r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹))
    (h₂₁ : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R₂ r - B) =O[atTop]
      (fun r : ℝ => r⁻¹))
    (h₂₂ : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R₂ r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹)) :
    EqOn R₁ R₂ (Ioi (outerHorizon M Q)) := by
  have hR := InfinitySolution.radial_sub isOpen_Ioi hR₁ hR₂
  have hP : ∀ (R : ℝ → ℂ), (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r) →
      ∀ r ∈ Ioi (outerHorizon M Q),
        DifferentiableAt ℝ (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) r :=
    fun R hd r hr => (hasDerivAt_profile (M := M) (Q := Q) (hΘ r hr) (hd r hr)).differentiableAt
  have h1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * (R₁ r - R₂ r)) =O[atTop]
      (fun r : ℝ => r⁻¹) := by
    refine (h₁₁.sub h₂₁).congr (fun r => ?_) (fun _ => rfl)
    ring
  have h2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * (R₁ r - R₂ r)) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹) := by
    refine (h₁₂.sub h₂₂).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
    have h := deriv_fun_sub (hP R₁ (fun s hs => (hR₁ s hs).1) r hr)
      (hP R₂ (fun s hs => (hR₂ s hs).1) r hr)
    rw [← h]
    congr 1
    funext s
    ring
  intro r hr
  have h := eqOn_zero_of_outgoing_coefficient_zero hM hQ hω hΘ hR h1 h2 hr
  exact sub_eq_zero.1 h

open InfinityUniqueness InfinitySolution in
/-- **Existence of the outgoing solution `R_I`.** For `M > 0`, `|Q| ≤ M`, real `e, L`, `ω ≠ 0`
and `Θ' = K/Δ` on `r > a`, there is a solution of the radial equation `(ΔR')' + (K²/Δ − L)R = 0`
on `r > a` satisfying the outgoing condition (1.5) with leading coefficient `1`:
`r e^{−iΘ}R − 1 = O(r⁻¹)` and `(r e^{−iΘ}R)' = O(r⁻²)`. -/
theorem exists_infinity_solution {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : ω ≠ 0)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r) :
    ∃ R : ℝ → ℂ, (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) ∧
      (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - 1) =O[atTop] (fun r : ℝ => r⁻¹) ∧
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) =O[atTop]
        (fun r : ℝ => (r ^ 2)⁻¹) := by
  have ha0 : 0 < outerHorizon M Q := outerHorizon_pos hM
  obtain ⟨C, -, hCev⟩ := exists_errCoeff_le hQ e L hω
  obtain ⟨r₁, hr₁⟩ := eventually_atTop.1 (hCev.and (eventually_good_inv (e := e) hQ hω))
  have ha : outerHorizon M Q ≤ r₁ := (hr₁ r₁ le_rfl).2.2.1.le
  have h0 : 0 < r₁ := (hr₁ r₁ le_rfl).2.1
  have hgood : ∀ t ∈ Ioi r₁, t ≠ 0 ∧ delta M Q t ≠ 0 ∧ phaseRate M Q e ω t ≠ 0 := by
    intro t ht
    obtain ⟨-, ht0, -, hΔ, -, -, hK⟩ := hr₁ t (le_of_lt ht)
    refine ⟨ht0.ne', hΔ.ne', div_ne_zero ?_ hΔ.ne'⟩
    rw [radialK_eq_mul]
    exact mul_ne_zero ht0.ne' hK
  have hθ : ∀ t ∈ Ioi r₁, phaseRate M Q e ω t ≠ 0 := fun t ht => (hgood t ht).2.2
  -- the amplitude system and its solution with `(A, B) → (2iω, 0)`
  set Mx : ℝ → ℂ × ℂ →L[ℂ] ℂ × ℂ := fun t => ODE.mat2 (ampCoeffAA M Q e ω L t)
    (ampCoeffAB M Q e ω L Θ t) (ampCoeffBA M Q e ω L Θ t) (ampCoeffBB M Q e ω L t) with hMx
  have hcoef : ∀ t ∈ Ioi r₁, ContinuousAt (ampCoeffAA M Q e ω L) t ∧
      ContinuousAt (ampCoeffAB M Q e ω L Θ) t ∧ ContinuousAt (ampCoeffBA M Q e ω L Θ) t ∧
        ContinuousAt (ampCoeffBB M Q e ω L) t := fun t ht =>
    continuousAt_ampCoeffs (hgood t ht).1 (hgood t ht).2.1 (hgood t ht).2.2
      (hΘ t (ha.trans_lt ht)).continuousAt
  have hMc : ContinuousOn Mx (Ioi r₁) :=
    ODE.continuousOn_mat2 (fun t ht => (hcoef t ht).1.continuousWithinAt)
      (fun t ht => (hcoef t ht).2.1.continuousWithinAt)
      (fun t ht => (hcoef t ht).2.2.1.continuousWithinAt)
      (fun t ht => (hcoef t ht).2.2.2.continuousWithinAt)
  have hMi : IntegrableOn (fun t => ‖Mx t‖) (Ioi (r₁ + 1)) := by
    refine integrableOn_Ioi_of_abs_le_div_sq (C := 4 * C) (by linarith)
      (hMc.mono fun t ht => lt_of_lt_of_le (lt_add_one r₁) ht).norm fun t ht => ?_
    have hE := (hr₁ t (by linarith)).1
    rw [abs_norm]
    refine (ODE.norm_mat2_le _ _ _ _).trans ?_
    have := norm_ampCoeffAA_le M Q e ω L t
    have := norm_ampCoeffAB_le M Q e ω L Θ t
    have := norm_ampCoeffBA_le M Q e ω L Θ t
    have := norm_ampCoeffBB_le M Q e ω L t
    have h4 : 4 * C / t ^ 2 = 4 * (C / t ^ 2) := by ring
    linarith
  obtain ⟨v, hv, hvl, -⟩ := ODE.linear_exists_atTop hMc (lt_add_one r₁) hMi
    ((2 * I * ω, 0) : ℂ × ℂ)
  have hA : ∀ t ∈ Ioi r₁, HasDerivAt (fun s => (v s).1)
      (ampCoeffAA M Q e ω L t * (v t).1 + ampCoeffAB M Q e ω L Θ t * (v t).2) t := by
    intro t ht
    have h := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t (hv t ht)
    rw [ContinuousLinearMap.coe_fst', hMx, ODE.mat2_apply_fst] at h
    exact h
  have hB : ∀ t ∈ Ioi r₁, HasDerivAt (fun s => (v s).2)
      (ampCoeffBA M Q e ω L Θ t * (v t).1 + ampCoeffBB M Q e ω L t * (v t).2) t := by
    intro t ht
    have h := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t (hv t ht)
    rw [ContinuousLinearMap.coe_snd', hMx, ODE.mat2_apply_snd] at h
    exact h
  have hlA : Tendsto (fun s => (v s).1) atTop (𝓝 (2 * I * ω)) :=
    (continuous_fst.tendsto _).comp hvl
  have hlB : Tendsto (fun s => (v s).2) atTop (𝓝 0) := (continuous_snd.tendsto _).comp hvl
  -- interior existence for the first-order form of the radial equation
  have hext : ∀ x y : ℂ, ∃ R P : ℝ → ℂ,
      (∀ t ∈ Ioi (outerHorizon M Q), HasDerivAt R (P t / (delta M Q t : ℂ)) t) ∧
      (∀ t ∈ Ioi (outerHorizon M Q),
        HasDerivAt P (-(((radialK e ω t) ^ 2 / delta M Q t - L : ℝ) : ℂ) * R t) t) ∧
      R (r₁ + 1) = x ∧ P (r₁ + 1) = y := by
    intro x y
    have hΔ : ∀ t ∈ Ioi (outerHorizon M Q), (delta M Q t : ℂ) ≠ 0 := fun t ht =>
      ofReal_ne_zero.2 (delta_pos_of_lt ht).ne'
    have hd : Continuous (fun t => (delta M Q t : ℂ)) :=
      continuous_ofReal.comp (continuous_delta M Q)
    have hK : Continuous (fun t => (radialK e ω t : ℂ)) := by
      unfold radialK
      fun_prop
    have hc₁₂ : ContinuousOn (fun t => 1 / (delta M Q t : ℂ)) (Ioi (outerHorizon M Q)) :=
      continuousOn_const.div hd.continuousOn hΔ
    have hc₂₁ : ContinuousOn (fun t => -(((radialK e ω t) ^ 2 / delta M Q t - L : ℝ) : ℂ))
        (Ioi (outerHorizon M Q)) := by
      have h : ContinuousOn (fun t => -((radialK e ω t : ℂ) ^ 2 / (delta M Q t : ℂ) - L))
          (Ioi (outerHorizon M Q)) :=
        (((hK.pow 2).continuousOn.div hd.continuousOn hΔ).sub continuousOn_const).neg
      refine h.congr fun t _ => ?_
      push_cast
      rfl
    have hM₀ := ODE.continuousOn_mat2 (continuousOn_const (c := (0 : ℂ))) hc₁₂ hc₂₁
      (continuousOn_const (c := (0 : ℂ)))
    obtain ⟨w, hw0, hw⟩ := ODE.linear_exists_Ioi hM₀ (ha.trans_lt (lt_add_one r₁)) (x, y)
    refine ⟨fun s => (w s).1, fun s => (w s).2, fun t ht => ?_, fun t ht => ?_, ?_, ?_⟩
    · have h := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t (hw t ht)
      rw [ContinuousLinearMap.coe_fst', ODE.mat2_apply_fst] at h
      refine h.congr_deriv ?_
      ring
    · have h := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t (hw t ht)
      rw [ContinuousLinearMap.coe_snd', ODE.mat2_apply_snd] at h
      refine h.congr_deriv ?_
      ring
    · exact congrArg Prod.fst hw0
    · exact congrArg Prod.snd hw0
  exact exists_outgoing_of_amp hQ hω hΘ ha h0 (lt_add_one r₁) hθ hA hB hlA hlB hext

end ModeStability.AllAngular

end
