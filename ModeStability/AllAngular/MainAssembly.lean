module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
import ModeStability.AllAngular.FluxL
import ModeStability.AllAngular.FluxLConj
import ModeStability.AllAngular.InfinityUniqueness

/-!
# Assembly of Theorem 1.1 of the all-angular paper (Θ-form), modulo the superradiant band

Source: the all-angular research notes in preparation, p. 2, Theorem 1.1, (1.6), (1.7) and the
paragraph after (1.7), and the
conclusion of Section 5, after (5.3).

The radial equation is `(ΔR')' + (K²/Δ − L)R = 0` on `(a, ∞)`, the phase `Θ` has `Θ' = K/Δ`, the
horizon condition (1.4) in Θ-form is `e^{iΘ}R − B_H = O(r − a)`, `(e^{iΘ}R)' = O(1)`, replaced by
boundedness of `R` at an extremal synchronized horizon (`a = b`, `K(a) = 0`), and the infinity
condition (1.5) is `r e^{−iΘ}R − B_I = O(r⁻¹)`, `(r e^{−iΘ}R)' = O(r⁻²)`.

The reduction of p. 2 is assembled here:

* `flux_band_exclusion_L`: for `ω > 0` and `K(a) ≥ 0`, the flux identity (1.6),
  `−K(a)‖B_H‖² = ω‖B_I‖²`, forces `B_I = 0`, and uniqueness at infinity gives `R ≡ 0`. This
  contains the subextremal synchronized case `K(a) = 0`.
* `sync_extremal_exclusion_L`: at an extremal synchronized horizon a bounded mode has
  `ω‖B_I‖² = 0` (paragraph after (1.7)), hence `B_I = 0` and `R ≡ 0`.
* `real_mode_exclusion_theta_pos_of_superradiant`: the case `ω > 0`, given the superradiant
  case `K(a) < 0` (the range (1.7), treated in Sections 2–5) as the internal hypothesis
  `SuperradiantExclusionL`.
* `real_mode_exclusion_theta_of_superradiant`: every real `ω ≠ 0`, by conjugation
  `(ω, e) ↦ (−ω, −e)` for `ω < 0` (p. 2.).
* `hasDerivAt_integral_radialK_div_delta`, `real_mode_exclusion_integralPhase_of_superradiant`:
  the same statement with the phase `Θ(r) = ∫_{a+1}^r K/Δ` of (1.3).

`SuperradiantExclusionL` is an internal helper predicate recording exactly the part of the
argument (Sections 2–5) that is not assembled in this file; it is not source-facing and is to be
discharged by a proof of the superradiant band.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- Internal helper predicate, not source-facing: the superradiant case `ω > 0`, `K(a) < 0` (the
range (1.7) of the all-angular research notes in preparation, p. 2) of Theorem 1.1 in Θ-form,
i.e. the content of Sections 2–5 there. It is the single unassembled input of
`real_mode_exclusion_theta_of_superradiant` and is to be proved, not assumed, downstream. -/
def SuperradiantExclusionL : Prop :=
  ∀ M Q e ω L : ℝ, 0 < M → |Q| ≤ M → 0 ≤ L → 0 < ω → radialK e ω (outerHorizon M Q) < 0 →
    ∀ (Θ : ℝ → ℝ),
      (∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r) →
    ∀ (R : ℝ → ℂ) (BH BI : ℂ),
      (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
        HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
          (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) →
      (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - BH)
        =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) →
      deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r)
        =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)) →
      (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - BI)
        =O[atTop] (fun r : ℝ => r⁻¹) →
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
        =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹) →
      EqOn R 0 (Ioi (outerHorizon M Q))

/-! ### Vanishing outgoing coefficient -/

/-- `ω‖B‖² = 0` with `ω ≠ 0` forces `B = 0`. -/
private theorem as_eq_zero_of_mul_norm_sq {ω : ℝ} {B : ℂ} (hω : ω ≠ 0)
    (h : ω * ‖B‖ ^ 2 = 0) : B = 0 := by
  have h2 : ‖B‖ ^ 2 = 0 := (mul_eq_zero.1 h).resolve_left hω
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)

/-- The outgoing condition (1.5) with leading coefficient `0` gives `R ≡ 0`
(`eqOn_zero_of_outgoing_coefficient_zero`). -/
private theorem as_eqOn_zero_of_BI_zero {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hω : ω ≠ 0) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {BI : ℂ} (hBI : BI = 0)
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - BI)
      =O[atTop] (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  subst hBI
  exact eqOn_zero_of_outgoing_coefficient_zero hM hQ hω hΘ hR
    (hI1.congr_left fun r => sub_zero _) hI2

/-! ### The flux band and the extremal synchronized horizon -/

/-- **Flux band** (p. 2, after (1.6)): for `ω > 0` and `K(a) ≥ 0`, a solution of the radial
equation with the Θ-form horizon condition (1.4) and infinity condition (1.5) vanishes. The flux
identity `−K(a)‖B_H‖² = ω‖B_I‖²` forces `B_I = 0`, and uniqueness at infinity gives `R ≡ 0`.
This includes the subextremal synchronized frequency `K(a) = 0`. -/
theorem flux_band_exclusion_L {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (hK : 0 ≤ radialK e ω (outerHorizon M Q))
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {BH BI : ℂ}
    (hH1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - BH)
      =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q))
    (hH2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r)
      =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - BI)
      =O[atTop] (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  have hflux := (flux_identity_L hΘ hR hH1 hH2 hI1 hI2).1
  have h1 : 0 ≤ radialK e ω (outerHorizon M Q) * ‖BH‖ ^ 2 := mul_nonneg hK (sq_nonneg _)
  have h2 : 0 ≤ ω * ‖BI‖ ^ 2 := mul_nonneg hω.le (sq_nonneg _)
  have h0 : ω * ‖BI‖ ^ 2 = 0 := by linarith
  exact as_eqOn_zero_of_BI_zero hM hQ hω.ne' hΘ hR (as_eq_zero_of_mul_norm_sq hω.ne' h0) hI1 hI2

/-- **Extremal synchronized horizon** (p. 2, paragraph after (1.7)): if `b = a` and `K(a) = 0`,
a solution of the radial equation that is bounded near `a` and satisfies the Θ-form infinity
condition (1.5) at a real frequency `ω ≠ 0` vanishes: `ω‖B_I‖² = 0` forces `B_I = 0`. -/
theorem sync_extremal_exclusion_L {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : ω ≠ 0)
    (hab : innerHorizon M Q = outerHorizon M Q) (hK : radialK e ω (outerHorizon M Q) = 0)
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hbdd : (fun r => R r) =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))
    {BI : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - BI)
      =O[atTop] (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  have h0 := (flux_identity_sync_L hab hK hΘ hR hbdd hI1 hI2).1
  exact as_eqOn_zero_of_BI_zero hM hQ hω hΘ hR (as_eq_zero_of_mul_norm_sq hω h0) hI1 hI2

/-! ### Assembly for `ω > 0` -/

/-- Theorem 1.1 in Θ-form for `ω > 0`, given the superradiant case `SuperradiantExclusionL`. The
horizon hypothesis is boundedness at an extremal synchronized horizon (`b = a`, `K(a) = 0`) and
the Θ-form condition (1.4) otherwise. Cases: `K(a) < 0` (superradiant, `hS`), `K(a) ≥ 0` away from
extremal synchronization (`flux_band_exclusion_L`), extremal synchronization
(`sync_extremal_exclusion_L`). -/
theorem real_mode_exclusion_theta_pos_of_superradiant (hS : SuperradiantExclusionL)
    {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hL : 0 ≤ L) (hω : 0 < ω)
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {BH BI : ℂ}
    (hH : if innerHorizon M Q = outerHorizon M Q ∧ radialK e ω (outerHorizon M Q) = 0 then
        (fun r => R r) =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))
      else
        ((fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - BH)
            =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) ∧
          deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r)
            =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))))
    (hI : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - BI)
        =O[atTop] (fun r : ℝ => r⁻¹) ∧
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
        =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  by_cases hs : innerHorizon M Q = outerHorizon M Q ∧ radialK e ω (outerHorizon M Q) = 0
  · rw [ite_eq_left hs] at hH
    exact sync_extremal_exclusion_L hM hQ hω.ne' hs.1 hs.2 hΘ hR hH hI.1 hI.2
  · rw [ite_eq_right hs] at hH
    rcases lt_or_ge (radialK e ω (outerHorizon M Q)) 0 with hK | hK
    · exact hS M Q e ω L hM hQ hL hω hK Θ hΘ R BH BI hR hH.1 hH.2 hI.1 hI.2
    · exact flux_band_exclusion_L hM hQ hω hK hΘ hR hH.1 hH.2 hI.1 hI.2

/-! ### Conjugation and all real frequencies -/

/-- **Theorem 1.1** (real-frequency exclusion) in Θ-form, given the superradiant case
`SuperradiantExclusionL`: for `M > 0`, `|Q| ≤ M`, real `e`, `L ≥ 0` and real `ω ≠ 0`, every
solution of the radial equation with `Θ' = K/Δ`, the future-horizon condition (boundedness at an
extremal synchronized horizon, the Θ-form (1.4) otherwise) and the Θ-form outgoing condition (1.5)
vanishes on the exterior. For `ω < 0` apply the case `ω > 0` to `conj ∘ R`, `(−e, −ω)`, `−Θ`. -/
theorem real_mode_exclusion_theta_of_superradiant (hS : SuperradiantExclusionL) :
    ∀ M Q e ω L : ℝ, 0 < M → |Q| ≤ M → 0 ≤ L → ω ≠ 0 →
      ∀ (Θ : ℝ → ℝ),
        (∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r) →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ),
        (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
          HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
            (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) →
        (if innerHorizon M Q = outerHorizon M Q ∧ radialK e ω (outerHorizon M Q) = 0 then
          (fun r => R r) =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))
        else
          ((fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - BH)
              =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) ∧
            deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r)
              =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))) →
        ((fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - BI)
            =O[atTop] (fun r : ℝ => r⁻¹) ∧
          deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
            =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) →
        EqOn R 0 (Ioi (outerHorizon M Q)) := by
  intro M Q e ω L hM hQ hL hω Θ hΘ R BH BI hR hH hI
  rcases lt_or_gt_of_ne hω with hneg | hpos
  · have hconj := real_mode_exclusion_theta_pos_of_superradiant hS (e := -e) (ω := -ω)
      (Θ := fun s => -Θ s) (R := fun s => (starRingEnd ℂ) (R s))
      (BH := (starRingEnd ℂ) BH) (BI := (starRingEnd ℂ) BI) hM hQ hL (neg_pos.2 hneg)
      (phase_conj_L hΘ) (radialEquation_conj_L hR) ?_ (infinityTheta_conj_L hI.1 hI.2)
    · intro r hr
      have h := hconj hr
      simp only [Pi.zero_apply, map_eq_zero] at h
      exact h
    · by_cases hs : innerHorizon M Q = outerHorizon M Q ∧ radialK e ω (outerHorizon M Q) = 0
      · rw [ite_eq_left hs] at hH
        rw [ite_eq_left ⟨hs.1, (radialK_neg_eq_zero_iff _ _ _).2 hs.2⟩]
        exact bounded_conj_L hH
      · rw [ite_eq_right hs] at hH
        rw [ite_eq_right fun h => hs ⟨h.1, (radialK_neg_eq_zero_iff _ _ _).1 h.2⟩]
        exact horizonTheta_conj_L hH.1 hH.2
  · exact real_mode_exclusion_theta_pos_of_superradiant hS hM hQ hL hpos hΘ hR hH hI

/-! ### The integral phase (1.3) -/

/-- `K/Δ` is continuous on the exterior `r > a`. -/
private theorem as_continuousOn_radialK_div_delta (M Q e ω : ℝ) :
    ContinuousOn (fun ρ => radialK e ω ρ / delta M Q ρ) (Ioi (outerHorizon M Q)) := by
  have hK : Continuous (fun ρ => radialK e ω ρ) := by
    unfold radialK
    fun_prop
  exact hK.continuousOn.div (fl_continuous_delta M Q).continuousOn
    fun ρ hρ => (fl_delta_pos hρ).ne'

/-- The phase `Θ(r) = ∫_{a+1}^r K/Δ` of (1.3) has `Θ' = K/Δ` on the exterior `r > a`. -/
theorem hasDerivAt_integral_radialK_div_delta {M Q e ω r : ℝ} (hr : outerHorizon M Q < r) :
    HasDerivAt (fun r => ∫ ρ in (outerHorizon M Q + 1)..r, radialK e ω ρ / delta M Q ρ)
      (radialK e ω r / delta M Q r) r := by
  have hc := as_continuousOn_radialK_div_delta M Q e ω
  have ha1 : outerHorizon M Q + 1 ∈ Ioi (outerHorizon M Q) := by
    rw [mem_Ioi]
    linarith
  have hsub : uIcc (outerHorizon M Q + 1) r ⊆ Ioi (outerHorizon M Q) :=
    ordConnected_Ioi.uIcc_subset ha1 hr
  exact intervalIntegral.integral_hasDerivAt_right
    ((hc.mono hsub).intervalIntegrable)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi r hr)
    (hc.continuousAt (Ioi_mem_nhds hr))

/-- **Theorem 1.1** (real-frequency exclusion) with the phase `Θ(r) = ∫_{a+1}^r K/Δ` of (1.3),
given the superradiant case `SuperradiantExclusionL`: for `M > 0`, `|Q| ≤ M`, real `e`, `L ≥ 0`
and real `ω ≠ 0`, every solution of (1.2) with the future-horizon condition (boundedness at an
extremal synchronized horizon, (1.4) otherwise) and the outgoing condition (1.5) vanishes. -/
theorem real_mode_exclusion_integralPhase_of_superradiant (hS : SuperradiantExclusionL) :
    ∀ M Q e ω L : ℝ, 0 < M → |Q| ≤ M → 0 ≤ L → ω ≠ 0 →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ),
        (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
          HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
            (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) →
        (if innerHorizon M Q = outerHorizon M Q ∧ radialK e ω (outerHorizon M Q) = 0 then
          (fun r => R r) =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))
        else
          ((fun r : ℝ => exp (I * ((∫ ρ in (outerHorizon M Q + 1)..r,
                  radialK e ω ρ / delta M Q ρ : ℝ) : ℂ)) * R r - BH)
              =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) ∧
            deriv (fun r : ℝ => exp (I * ((∫ ρ in (outerHorizon M Q + 1)..r,
                  radialK e ω ρ / delta M Q ρ : ℝ) : ℂ)) * R r)
              =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))) →
        ((fun r : ℝ => (r : ℂ) * exp (-(I * ((∫ ρ in (outerHorizon M Q + 1)..r,
                radialK e ω ρ / delta M Q ρ : ℝ) : ℂ))) * R r - BI)
            =O[atTop] (fun r : ℝ => r⁻¹) ∧
          deriv (fun r : ℝ => (r : ℂ) * exp (-(I * ((∫ ρ in (outerHorizon M Q + 1)..r,
                radialK e ω ρ / delta M Q ρ : ℝ) : ℂ))) * R r)
            =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) →
        EqOn R 0 (Ioi (outerHorizon M Q)) :=
  fun M Q e ω L hM hQ hL hω R BH BI hR hH hI =>
    real_mode_exclusion_theta_of_superradiant hS M Q e ω L hM hQ hL hω
      (fun r => ∫ ρ in (outerHorizon M Q + 1)..r, radialK e ω ρ / delta M Q ρ)
      (fun _ hr => hasDerivAt_integral_radialK_div_delta hr) R BH BI hR hH hI

end ModeStability.AllAngular

end
