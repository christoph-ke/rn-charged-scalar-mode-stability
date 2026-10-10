module

public import Mathlib
public import ModeStability.Exterior.Calculus
public import ModeStability.Corotation.Basic
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition
public import ModeStability.Frozen.FluxIdentity

/-!
# The flux band `K(a) ≥ 0` of the complementary-band exclusion

Source: the all-angular research notes in preparation, pp. 1–2, the phase (1.3), the outgoing
condition (1.5) and the flux identity (1.6); the spherical research notes in preparation, (1.4)
and (1.5).

For `ω > 0` and `K(a) ≥ 0`, the flux identity `−K(a)|B_H|² = ω|B_I|²` forces `B_I = 0`. The
outgoing condition (1.4) of the spherical paper with `B_I = 0` says that the profile
`R̃ = r e^{−iωr} r^{−ic} R` (`c = 2Mω − e`) is `O(r⁻¹)` with `R̃' = O(r⁻²)`. For any primitive
`Θ` of `K/Δ` on `r > a`, the phase-(1.3) profile is `r e^{−iΘ} R = e^{iψ} R̃` with
`ψ = ωr + c log r − Θ`, and `ψ' = ω + c/r − K/Δ = O(r⁻¹)` by partial fractions, so this profile is
`O(r⁻¹)` with derivative `O(r⁻²)`. Uniqueness at infinity (taken as a hypothesis here) then
gives `R ≡ 0`.

* `cbe_radialK_div_delta`: `K/Δ = ω + K(a)/(a − b) (r − a)⁻¹ − K(b)/(a − b) (r − b)⁻¹`.
* `cbe_hasDerivAt_phase`: an explicit primitive of `K/Δ` on `r > a`.
* `cbe_isBigO_of_phase`: an abstract unimodular-twist lemma for the two `O`-bounds.
* `cbe_phase_profile_isBigO`: the bounds for `r e^{−iΘ} R` from (1.4) with `B_I = 0`.
* `cbe_flux_band`: `K(a) ≥ 0` forces `R ≡ 0`, conditionally on uniqueness at infinity.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- Partial fractions: `K/Δ = ω + K(a)/(a − b) · (r − a)⁻¹ − K(b)/(a − b) · (r − b)⁻¹` on `r > a`
(subextremal, so `a ≠ b`). -/
theorem cbe_radialK_div_delta {M Q : ℝ} (hQ : |Q| < M) (e ω : ℝ) {r : ℝ}
    (hr : outerHorizon M Q < r) :
    radialK e ω r / delta M Q r =
      ω + radialK e ω (outerHorizon M Q) / (outerHorizon M Q - innerHorizon M Q) *
          (r - outerHorizon M Q)⁻¹ -
        radialK e ω (innerHorizon M Q) / (outerHorizon M Q - innerHorizon M Q) *
          (r - innerHorizon M Q)⁻¹ := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hra : 0 < r - outerHorizon M Q := sub_pos.2 hr
  have hrb : 0 < r - innerHorizon M Q := by linarith
  have hd0 : outerHorizon M Q - innerHorizon M Q ≠ 0 := hd.ne'
  have hra0 : r - outerHorizon M Q ≠ 0 := hra.ne'
  have hrb0 : r - innerHorizon M Q ≠ 0 := hrb.ne'
  unfold delta radialK
  field_simp
  ring

/-- An explicit primitive of `K/Δ` on `r > a`: `Θ(r) = ωr + K(a)/(a − b) log(r − a)
− K(b)/(a − b) log(r − b)`, a phase (1.3). -/
theorem cbe_hasDerivAt_phase {M Q : ℝ} (hQ : |Q| < M) (e ω : ℝ) {r : ℝ}
    (hr : outerHorizon M Q < r) :
    HasDerivAt (fun s : ℝ => ω * s + radialK e ω (outerHorizon M Q) /
        (outerHorizon M Q - innerHorizon M Q) * Real.log (s - outerHorizon M Q) -
        radialK e ω (innerHorizon M Q) / (outerHorizon M Q - innerHorizon M Q) *
          Real.log (s - innerHorizon M Q))
      (radialK e ω r / delta M Q r) r := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hra : 0 < r - outerHorizon M Q := sub_pos.2 hr
  have hrb : 0 < r - innerHorizon M Q := by linarith
  have h1 := ((hasDerivAt_id r).sub_const (outerHorizon M Q)).log hra.ne'
  have h2 := ((hasDerivAt_id r).sub_const (innerHorizon M Q)).log hrb.ne'
  have h := (((hasDerivAt_id r).const_mul ω).add
    (h1.const_mul (radialK e ω (outerHorizon M Q) / (outerHorizon M Q - innerHorizon M Q)))).sub
    (h2.const_mul (radialK e ω (innerHorizon M Q) / (outerHorizon M Q - innerHorizon M Q)))
  rw [cbe_radialK_div_delta hQ e ω hr]
  refine h.congr_deriv ?_
  simp only [id_eq, mul_one, one_div]

/-- `(r − a)⁻¹ = O(r⁻¹)` as `r → ∞`. -/
theorem cbe_isBigO_inv_sub (a : ℝ) :
    (fun r : ℝ => (r - a)⁻¹) =O[atTop] (fun r : ℝ => r⁻¹) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (2 * |a| + 1)] with r hr
  have ha := le_abs_self a
  have ha' := abs_nonneg a
  have hr0 : 0 < r := by linarith
  have hra : 0 < r - a := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_inv, abs_of_pos hra, abs_of_pos hr0]
  have h2 : 2 * r⁻¹ = (r / 2)⁻¹ := by
    rw [inv_div, div_eq_mul_inv]
  rw [h2]
  exact inv_anti₀ (by positivity) (by linarith)

/-- A unimodular twist preserves the two `O`-bounds of an outgoing profile: if `G = e^{iψ} F` on
`(r₁, ∞)` with `ψ' = O(r⁻¹)`, `F = O(r⁻¹)` and `F' = O(r⁻²)`, then `G = O(r⁻¹)` and
`G' = O(r⁻²)`. -/
theorem cbe_isBigO_of_phase {F G : ℝ → ℂ} {ψ ψ' : ℝ → ℝ} {r₁ : ℝ}
    (hG : ∀ s ∈ Ioi r₁, G s = exp (I * ψ s) * F s)
    (hψ : ∀ s ∈ Ioi r₁, HasDerivAt ψ (ψ' s) s)
    (hFd : ∀ s ∈ Ioi r₁, DifferentiableAt ℝ F s)
    (hψ' : ψ' =O[atTop] (fun s : ℝ => s⁻¹))
    (hF1 : F =O[atTop] (fun s : ℝ => s⁻¹)) (hF2 : deriv F =O[atTop] (fun s : ℝ => (s ^ 2)⁻¹)) :
    G =O[atTop] (fun s : ℝ => s⁻¹) ∧ deriv G =O[atTop] (fun s : ℝ => (s ^ 2)⁻¹) := by
  have hE : ∀ s : ℝ, ‖exp (I * (ψ s : ℂ))‖ = 1 := fun s => by
    rw [mul_comm]
    exact norm_exp_ofReal_mul_I _
  have hEO : (fun s : ℝ => exp (I * (ψ s : ℂ))) =O[atTop] (fun _ => (1 : ℝ)) :=
    isBigO_of_le _ fun s => by rw [hE, norm_one]
  have hGev : (fun s => exp (I * (ψ s : ℂ)) * F s) =ᶠ[atTop] G := by
    filter_upwards [eventually_gt_atTop r₁] with s hs using (hG s hs).symm
  refine ⟨?_, ?_⟩
  · have h := hEO.mul hF1
    refine h.congr' hGev ?_
    exact Eventually.of_forall fun s => one_mul _
  · -- the derivative of `G` on `(r₁, ∞)`
    have hD : ∀ s ∈ Ioi r₁, deriv G s =
        exp (I * (ψ s : ℂ)) * (I * (ψ' s : ℂ)) * F s + exp (I * (ψ s : ℂ)) * deriv F s := by
      intro s hs
      have hloc : G =ᶠ[𝓝 s] fun t => exp (I * (ψ t : ℂ)) * F t :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds hs) fun t ht => hG t ht
      have h := (((hψ s hs).ofReal_comp.const_mul I).cexp).mul (hFd s hs).hasDerivAt
      exact (h.congr_of_eventuallyEq hloc).deriv
    have hIψ : (fun s : ℝ => I * (ψ' s : ℂ)) =O[atTop] (fun s : ℝ => s⁻¹) := by
      refine (isBigO_of_le _ fun s => ?_).trans hψ'
      rw [norm_mul, norm_I, one_mul, Complex.norm_real]
    have h1 : (fun s : ℝ => exp (I * (ψ s : ℂ)) * (I * (ψ' s : ℂ)) * F s) =O[atTop]
        (fun s : ℝ => (s ^ 2)⁻¹) :=
      ((hEO.mul hIψ).mul hF1).congr_right fun s => by ring
    have h2 : (fun s : ℝ => exp (I * (ψ s : ℂ)) * deriv F s) =O[atTop]
        (fun s : ℝ => (s ^ 2)⁻¹) :=
      (hEO.mul hF2).congr_right fun s => one_mul _
    refine (h1.add h2).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop r₁] with s hs
    exact (hD s hs).symm

/-- From the outgoing condition (1.4) with `B_I = 0`: for any primitive `Θ` of `K/Δ` on `r > a`,
the profile `r e^{−iΘ} R` is `O(r⁻¹)` with derivative `O(r⁻²)`. -/
theorem cbe_phase_profile_isBigO {M Q q ω : ℝ} (hM : 0 < M) (hQ : |Q| < M) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK (q * Q) ω r / delta M Q r) r)
    {R : ℝ → ℂ} (hR : IsRadialSolution M Q q ω R) (hI : InfinityCondition M Q q ω R 0) :
    (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) =O[atTop] (fun r : ℝ => r⁻¹) ∧
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) =O[atTop]
        (fun r : ℝ => (r ^ 2)⁻¹) := by
  have ha : 0 < outerHorizon M Q := outerHorizon_pos hM
  have hF1 : (fun r : ℝ => (r : ℂ) * exp (-(I * ω * r)) *
      (r : ℂ) ^ (-(I * (2 * M * ω - q * Q))) * R r) =O[atTop] (fun r : ℝ => r⁻¹) := by
    simpa only [sub_zero] using hI.1
  refine cbe_isBigO_of_phase (r₁ := outerHorizon M Q)
    (ψ := fun s => ω * s + (2 * M * ω - q * Q) * Real.log s - Θ s)
    (ψ' := fun s => (2 * M * ω - q * Q) * s⁻¹ -
      radialK (q * Q) ω (outerHorizon M Q) / (outerHorizon M Q - innerHorizon M Q) *
        (s - outerHorizon M Q)⁻¹ +
      radialK (q * Q) ω (innerHorizon M Q) / (outerHorizon M Q - innerHorizon M Q) *
        (s - innerHorizon M Q)⁻¹) ?_ ?_ ?_ ?_ hF1 hI.2
  · -- the twist identity `r e^{−iΘ} R = e^{iψ} R̃`
    intro s hs
    have hs0 : 0 < s := ha.trans hs
    have hsc : (s : ℂ) ≠ 0 := ofReal_ne_zero.2 hs0.ne'
    rw [Complex.cpow_def_of_ne_zero hsc, ← Complex.ofReal_log hs0.le]
    have he : exp (I * ((ω * s + (2 * M * ω - q * Q) * Real.log s - Θ s : ℝ) : ℂ)) *
        exp (-(I * ω * s)) * exp (((Real.log s : ℝ) : ℂ) * (-(I * (2 * M * ω - q * Q)))) =
        exp (-(I * Θ s)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← he]
    ring
  · -- `ψ' = ω + c/r − K/Δ`, in partial fractions
    intro s hs
    have hs0 : 0 < s := ha.trans hs
    have h := (((hasDerivAt_id s).const_mul ω).add
      ((Real.hasDerivAt_log hs0.ne').const_mul (2 * M * ω - q * Q))).sub (hΘ s hs)
    rw [cbe_radialK_div_delta hQ (q * Q) ω hs] at h
    refine h.congr_deriv ?_
    simp only [mul_one]
    ring
  · -- differentiability of `R̃`
    intro s hs
    have hs0 : 0 < s := ha.trans hs
    have h1 : DifferentiableAt ℝ (fun r : ℝ => (r : ℂ)) s :=
      (hasDerivAt_id s).ofReal_comp.differentiableAt
    have h2 : DifferentiableAt ℝ (fun r : ℝ => exp (-(I * ω * r))) s :=
      ((h1.const_mul (I * ω)).neg).cexp
    have h3 : DifferentiableAt ℝ (fun r : ℝ => (r : ℂ) ^ (-(I * (2 * M * ω - q * Q)))) s := by
      have h := ((hasDerivAt_id (s : ℂ)).cpow_const (c := -(I * (2 * M * ω - q * Q)))
        (Complex.ofReal_mem_slitPlane.2 hs0)).comp_ofReal
      exact h.differentiableAt
    exact ((h1.mul h2).mul h3).mul (hR s hs).1
  · -- `ψ' = O(r⁻¹)`
    exact (((isBigO_refl (fun s : ℝ => s⁻¹) atTop).const_mul_left _).sub
      ((cbe_isBigO_inv_sub _).const_mul_left _)).add ((cbe_isBigO_inv_sub _).const_mul_left _)

/-- **The flux band.** For `ω > 0` and `K(a) ≥ 0`, a solution of (1.2) with (1.3) and (1.4)
vanishes on the exterior, conditionally on uniqueness at infinity (`huniq`, used with `L = 0` and
the explicit phase `Θ` of `cbe_hasDerivAt_phase`). -/
theorem cbe_flux_band
    (huniq : ∀ {M Q e ω L : ℝ}, 0 < M → |Q| ≤ M → ω ≠ 0 → ∀ {Θ : ℝ → ℝ},
      (∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r) →
      ∀ {R : ℝ → ℂ},
      (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
        HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
          (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) →
      (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) =O[atTop] (fun r : ℝ => r⁻¹) →
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) =O[atTop]
        (fun r : ℝ => (r ^ 2)⁻¹) →
      EqOn R 0 (Ioi (outerHorizon M Q)))
    {M Q q ω : ℝ} (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω)
    (hKa : 0 ≤ radialK (q * Q) ω (outerHorizon M Q)) {R : ℝ → ℂ} {BH BI : ℂ}
    (hR : IsRadialSolution M Q q ω R) (hH : HorizonCondition M Q q ω R BH)
    (hI : InfinityCondition M Q q ω R BI) : EqOn R 0 (Ioi (outerHorizon M Q)) := by
  have hflux := (flux_identity M Q q ω hM hQ R BH BI hR hH hI).2
  have hBI : BI = 0 := by
    have h1 : 0 ≤ radialK (q * Q) ω (outerHorizon M Q) * ‖BH‖ ^ 2 := by positivity
    have h2 : 0 ≤ ω * ‖BI‖ ^ 2 := by positivity
    have h3 : ω * ‖BI‖ ^ 2 = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h hω.ne'
    · exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
  subst hBI
  have hΘ := fun r (hr : r ∈ Ioi (outerHorizon M Q)) => cbe_hasDerivAt_phase hQ (q * Q) ω hr
  obtain ⟨h1, h2⟩ := cbe_phase_profile_isBigO hM hQ hΘ hR hI
  refine @huniq M Q (q * Q) ω 0 hM hQ.le hω.ne' _ hΘ R (fun r hr => ?_) h1 h2
  simp only [sub_zero]
  exact hR r hr

end ModeStability.AllAngular

end
