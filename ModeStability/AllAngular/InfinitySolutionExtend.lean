module

public import Mathlib
public import ModeStability.ODE.Uniqueness
public import ModeStability.AllAngular.InfinitySolutionAsymp

/-!
# The outgoing solution at infinity: extension to the whole exterior

Part of the construction of the outgoing solution `R_I` of
the all-angular research notes in preparation, (1.5) (Sections 6 and 8). The amplitude system
lives only where `Θ' ≠ 0`; the solution is continued to `r > a` through the first-order form
`R' = P/Δ`, `P' = −(K²/Δ − L)R` of the radial equation and matched by interior uniqueness.

* `radial_of_first_order`: a solution `(R, P)` of the first-order system solves the radial
  equation;
* `radial_sub`, `eqOn_of_radial_of_eq`: solutions of the radial equation on `r > α ≥ a` with the
  same value and derivative at one point agree on `r > α`;
* `outgoing_congr`: the outgoing condition only depends on `R` on a half-line `r > α`;
* continuity of the coefficients of the amplitude system where `r ≠ 0`, `Δ ≠ 0`, `Θ' ≠ 0`, and
  `integrableOn_Ioi_of_abs_le_div_sq` for the integrability of `O(r⁻²)` coefficients.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

namespace InfinitySolution

open InfinityUniqueness

variable {M Q e ω L : ℝ}

/-! ### The radial equation on a half-line -/

/-- A solution `(R, P)` of `R' = P/Δ`, `P' = −(K²/Δ − L)R` on `r > α ≥ a` solves the radial
equation there. -/
theorem radial_of_first_order {α : ℝ} (hα : outerHorizon M Q ≤ α) {R P : ℝ → ℂ}
    (hR : ∀ t ∈ Ioi α, HasDerivAt R (P t / (delta M Q t : ℂ)) t)
    (hP : ∀ t ∈ Ioi α, HasDerivAt P (-(((radialK e ω t) ^ 2 / delta M Q t - L : ℝ) : ℂ) * R t) t) :
    ∀ t ∈ Ioi α, DifferentiableAt ℝ R t ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω t) ^ 2 / delta M Q t - L : ℝ) : ℂ) * R t) t := by
  intro t ht
  refine ⟨(hR t ht).differentiableAt, (hP t ht).congr_of_eventuallyEq ?_⟩
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  have hΔ : (delta M Q s : ℂ) ≠ 0 := ofReal_ne_zero.2 (delta_pos_of_lt (hα.trans_lt hs)).ne'
  rw [(hR s hs).deriv, mul_div_cancel₀ _ hΔ]

/-- The difference of two solutions of the radial equation is a solution. -/
theorem radial_sub {S : Set ℝ} (hS : IsOpen S) {R₁ R₂ : ℝ → ℂ}
    (hR₁ : ∀ r ∈ S, DifferentiableAt ℝ R₁ r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R₁ s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R₁ r) r)
    (hR₂ : ∀ r ∈ S, DifferentiableAt ℝ R₂ r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R₂ s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R₂ r) r) :
    ∀ r ∈ S, DifferentiableAt ℝ (fun s => R₁ s - R₂ s) r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv (fun s => R₁ s - R₂ s) s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * (R₁ r - R₂ r)) r := by
  intro r hr
  refine ⟨(hR₁ r hr).1.sub (hR₂ r hr).1, ?_⟩
  have hev : (fun s => (delta M Q s : ℂ) * deriv (fun s => R₁ s - R₂ s) s) =ᶠ[𝓝 r]
      (fun s => (delta M Q s : ℂ) * deriv R₁ s - (delta M Q s : ℂ) * deriv R₂ s) := by
    filter_upwards [hS.mem_nhds hr] with s hs
    rw [deriv_fun_sub (hR₁ s hs).1 (hR₂ s hs).1, mul_sub]
  refine (((hR₁ r hr).2.sub (hR₂ r hr).2).congr_of_eventuallyEq hev).congr_deriv ?_
  ring

/-- Two solutions of the radial equation on `r > α ≥ a` with the same value and derivative at a
point `r₂ > α` agree on `r > α`. -/
theorem eqOn_of_radial_of_eq {α : ℝ} (hα : outerHorizon M Q ≤ α) {R₁ R₂ : ℝ → ℂ}
    (hR₁ : ∀ r ∈ Ioi α, DifferentiableAt ℝ R₁ r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R₁ s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R₁ r) r)
    (hR₂ : ∀ r ∈ Ioi α, DifferentiableAt ℝ R₂ r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R₂ s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R₂ r) r)
    {r₂ : ℝ} (hr₂ : α < r₂) (h0 : R₁ r₂ = R₂ r₂) (h1 : deriv R₁ r₂ = deriv R₂ r₂) :
    EqOn R₁ R₂ (Ioi α) := by
  have hp0 : ∀ r ∈ Ioi α, 0 < delta M Q r := fun r hr => delta_pos_of_lt (hα.trans_lt hr)
  have hw : ContinuousOn (fun r => radialK e ω r ^ 2 / delta M Q r - L) (Ioi α) := by
    refine ContinuousOn.sub (ContinuousOn.div ?_ (continuous_delta M Q).continuousOn
      (fun r hr => (hp0 r hr).ne')) continuousOn_const
    unfold radialK
    fun_prop
  have hz := ModeStability.ODE.eqOn_zero_of_linear_ode (continuous_delta M Q).continuousOn hp0 hw
    (radial_sub isOpen_Ioi hR₁ hR₂) hr₂ (sub_eq_zero.2 h0)
    (by rw [deriv_fun_sub (hR₁ r₂ hr₂).1 (hR₂ r₂ hr₂).1, h1, sub_self])
  intro r hr
  exact sub_eq_zero.1 (hz hr)

/-- The outgoing condition only depends on `R` on a half-line. -/
theorem outgoing_congr {α : ℝ} {Θ : ℝ → ℝ} {R₁ R₂ : ℝ → ℂ} {B : ℂ} (h : EqOn R₁ R₂ (Ioi α))
    (h₁ : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R₁ r - B) =O[atTop]
      (fun r : ℝ => r⁻¹))
    (h₂ : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R₁ r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹)) :
    (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R₂ r - B) =O[atTop] (fun r : ℝ => r⁻¹) ∧
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R₂ r) =O[atTop]
        (fun r : ℝ => (r ^ 2)⁻¹) := by
  have hev : ∀ r ∈ Ioi α, (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R₁ r) =ᶠ[𝓝 r]
      (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R₂ r) := by
    intro r hr
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    rw [h hs]
  constructor
  · refine h₁.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop α] with r hr
    rw [h hr]
  · refine h₂.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop α] with r hr
    exact (hev r hr).deriv_eq

/-! ### Continuity of the coefficients -/

theorem continuousAt_phaseRate {t : ℝ} (hΔ : delta M Q t ≠ 0) :
    ContinuousAt (phaseRate M Q e ω) t :=
  (hasDerivAt_phaseRate hΔ).continuousAt

theorem continuousAt_phaseAccel {t : ℝ} (hΔ : delta M Q t ≠ 0) :
    ContinuousAt (phaseAccel M Q e ω) t := by
  have hd := (continuous_delta M Q).continuousAt (x := t)
  have hK : Continuous (radialK e ω) := by unfold radialK; fun_prop
  have h : ContinuousAt (fun r => ((2 * ω * r - e) * delta M Q r -
      radialK e ω r * (2 * r - 2 * M)) / delta M Q r ^ 2) t :=
    ContinuousAt.div (by fun_prop) (hd.pow 2) (pow_ne_zero 2 hΔ)
  exact h

theorem continuousAt_dampCoeff {t : ℝ} (ht : t ≠ 0) (hΔ : delta M Q t ≠ 0) :
    ContinuousAt (dampCoeff M Q) t := by
  have hd := (continuous_delta M Q).continuousAt (x := t)
  have h : ContinuousAt (fun r => (2 * M * r - 2 * Q ^ 2) / (r * delta M Q r)) t :=
    ContinuousAt.div (by fun_prop) (continuousAt_id.mul hd) (mul_ne_zero ht hΔ)
  exact h

theorem continuousAt_potCoeff {t : ℝ} (ht : t ≠ 0) (hΔ : delta M Q t ≠ 0) :
    ContinuousAt (potCoeff M Q L) t := by
  have hd := (continuous_delta M Q).continuousAt (x := t)
  have h : ContinuousAt (fun r => (-2 * M * r + 2 * Q ^ 2 - L * r ^ 2) / (r ^ 2 * delta M Q r)) t :=
    ContinuousAt.div (by fun_prop) ((continuousAt_id.pow 2).mul hd)
      (mul_ne_zero (pow_ne_zero 2 ht) hΔ)
  exact h

theorem continuousAt_ampRhoP {t : ℝ} (ht : t ≠ 0) (hΔ : delta M Q t ≠ 0)
    (hθ : phaseRate M Q e ω t ≠ 0) : ContinuousAt (ampRhoP M Q e ω) t := by
  have h : ContinuousAt (fun r => -dampCoeff M Q r / 2 +
      phaseAccel M Q e ω r / (2 * phaseRate M Q e ω r)) t :=
    ((continuousAt_dampCoeff ht hΔ).neg.div_const 2).add ((continuousAt_phaseAccel hΔ).div
      ((continuousAt_phaseRate hΔ).const_mul 2) (mul_ne_zero two_ne_zero hθ))
  exact h

theorem continuousAt_ampRhoM {t : ℝ} (ht : t ≠ 0) (hΔ : delta M Q t ≠ 0)
    (hθ : phaseRate M Q e ω t ≠ 0) : ContinuousAt (ampRhoM M Q e ω) t := by
  have h : ContinuousAt (fun r => -dampCoeff M Q r / 2 -
      phaseAccel M Q e ω r / (2 * phaseRate M Q e ω r)) t :=
    ((continuousAt_dampCoeff ht hΔ).neg.div_const 2).sub ((continuousAt_phaseAccel hΔ).div
      ((continuousAt_phaseRate hΔ).const_mul 2) (mul_ne_zero two_ne_zero hθ))
  exact h

theorem continuousAt_ampSigma {t : ℝ} (ht : t ≠ 0) (hΔ : delta M Q t ≠ 0)
    (hθ : phaseRate M Q e ω t ≠ 0) : ContinuousAt (ampSigma M Q e ω L) t := by
  have h : ContinuousAt (fun r => potCoeff M Q L r / (2 * phaseRate M Q e ω r)) t :=
    (continuousAt_potCoeff ht hΔ).div ((continuousAt_phaseRate hΔ).const_mul 2)
      (mul_ne_zero two_ne_zero hθ)
  exact h

/-- Continuity of the four entries of the amplitude system where `r ≠ 0`, `Δ ≠ 0`, `Θ' ≠ 0`
and `Θ` is continuous. -/
theorem continuousAt_ampCoeffs {Θ : ℝ → ℝ} {t : ℝ} (ht : t ≠ 0) (hΔ : delta M Q t ≠ 0)
    (hθ : phaseRate M Q e ω t ≠ 0) (hΘ : ContinuousAt Θ t) :
    ContinuousAt (ampCoeffAA M Q e ω L) t ∧ ContinuousAt (ampCoeffAB M Q e ω L Θ) t ∧
      ContinuousAt (ampCoeffBA M Q e ω L Θ) t ∧ ContinuousAt (ampCoeffBB M Q e ω L) t := by
  have hp := continuous_ofReal.continuousAt.comp (continuousAt_ampRhoP (e := e) ht hΔ hθ)
  have hm := continuous_ofReal.continuousAt.comp (continuousAt_ampRhoM (e := e) ht hΔ hθ)
  have hs := continuous_ofReal.continuousAt.comp (continuousAt_ampSigma (L := L) ht hΔ hθ)
  have hΘc := continuous_ofReal.continuousAt.comp hΘ
  have hE : ContinuousAt (fun r => exp (I * (Θ r : ℂ))) t :=
    continuous_exp.continuousAt.comp (continuousAt_const.mul hΘc)
  have hEi : ContinuousAt (fun r => exp (-(I * (Θ r : ℂ)))) t :=
    continuous_exp.continuousAt.comp (continuousAt_const.mul hΘc).neg
  refine ⟨hp.add (continuousAt_const.mul hs), (hEi.pow 2).mul (hm.sub (continuousAt_const.mul hs)),
    (hE.pow 2).mul (hm.add (continuousAt_const.mul hs)), hp.sub (continuousAt_const.mul hs)⟩

/-! ### Integrability -/

/-- A function continuous on `[r₀, ∞)` with `|g(t)| ≤ C/t²` there, `r₀ > 0`, is integrable on
`(r₀, ∞)`. -/
theorem integrableOn_Ioi_of_abs_le_div_sq {g : ℝ → ℝ} {r₀ C : ℝ} (hr₀ : 0 < r₀)
    (hg : ContinuousOn g (Ici r₀)) (hb : ∀ t, r₀ ≤ t → |g t| ≤ C / t ^ 2) :
    IntegrableOn g (Ioi r₀) := by
  have hi : IntegrableOn (fun t : ℝ => C * t ^ (-2 : ℝ)) (Ioi r₀) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hr₀).const_mul C
  refine hi.mono' ((hg.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := hr₀.trans ht
  rw [Real.norm_eq_abs, Real.rpow_neg ht0.le, Real.rpow_two, ← div_eq_mul_inv]
  exact hb t (le_of_lt ht)

/-! ### Assembly from the amplitude system and interior existence -/

/-- **Assembly.** Let `(A, B)` solve the amplitude system on `(r₁, ∞)` (`r₁ ≥ a`, `r₁ > 0`,
`Θ' ≠ 0` there) with `A → 2iω`, `B → 0`, and suppose the first-order system
`R' = P/Δ`, `P' = −(K²/Δ − L)R` has, for all data at a point `r₂ > r₁`, a solution on `r > a`.
Then there is a solution of the radial equation on `r > a` with the outgoing asymptotics (1.5)
and leading coefficient `1`. -/
theorem exists_outgoing_of_amp (hQ : |Q| ≤ M) (hω : ω ≠ 0) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {r₁ r₂ : ℝ} (ha : outerHorizon M Q ≤ r₁) (h0 : 0 < r₁) (hr₂ : r₁ < r₂)
    (hθ : ∀ t ∈ Ioi r₁, phaseRate M Q e ω t ≠ 0) {A B : ℝ → ℂ}
    (hA : ∀ t ∈ Ioi r₁,
      HasDerivAt A (ampCoeffAA M Q e ω L t * A t + ampCoeffAB M Q e ω L Θ t * B t) t)
    (hB : ∀ t ∈ Ioi r₁,
      HasDerivAt B (ampCoeffBA M Q e ω L Θ t * A t + ampCoeffBB M Q e ω L t * B t) t)
    (hlA : Tendsto A atTop (𝓝 (2 * I * ω))) (hlB : Tendsto B atTop (𝓝 0))
    (hext : ∀ x y : ℂ, ∃ R P : ℝ → ℂ,
      (∀ t ∈ Ioi (outerHorizon M Q), HasDerivAt R (P t / (delta M Q t : ℂ)) t) ∧
      (∀ t ∈ Ioi (outerHorizon M Q),
        HasDerivAt P (-(((radialK e ω t) ^ 2 / delta M Q t - L : ℝ) : ℂ) * R t) t) ∧
      R r₂ = x ∧ P r₂ = y) :
    ∃ R : ℝ → ℂ, (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) ∧
      (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - 1) =O[atTop] (fun r : ℝ => r⁻¹) ∧
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) =O[atTop]
        (fun r : ℝ => (r ^ 2)⁻¹) := by
  have hΘ₁ : ∀ t ∈ Ioi r₁, HasDerivAt Θ (radialK e ω t / delta M Q t) t :=
    fun t ht => hΘ t (ha.trans_lt ht)
  have hfar := ampSol_radial hQ ha h0 hθ hΘ₁ hA hB
  obtain ⟨h1, h2⟩ := outgoing_ampSol hQ hω ha hθ hΘ₁ hA hB hlA hlB
  obtain ⟨R, P, hRd, hPd, hR0, hP0⟩ := hext (ampSol M Q e ω Θ A B r₂)
    ((delta M Q r₂ : ℂ) * deriv (ampSol M Q e ω Θ A B) r₂)
  have hglob := radial_of_first_order le_rfl hRd hPd
  have hra : r₂ ∈ Ioi (outerHorizon M Q) := (ha.trans_lt hr₂)
  have hd : deriv R r₂ = deriv (ampSol M Q e ω Θ A B) r₂ := by
    have hΔ : (delta M Q r₂ : ℂ) ≠ 0 := ofReal_ne_zero.2 (delta_pos_of_lt hra).ne'
    rw [(hRd r₂ hra).deriv, hP0, mul_div_cancel_left₀ _ hΔ]
  have heq := eqOn_of_radial_of_eq ha (fun t ht => hglob t (ha.trans_lt ht)) hfar hr₂ hR0 hd
  exact ⟨R, hglob, outgoing_congr (fun t ht => (heq ht).symm) h1 h2⟩

end InfinitySolution

end ModeStability.AllAngular

end
