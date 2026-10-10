module

public import Mathlib
public import ModeStability.AllAngular.Prop61Multiplier
public import ModeStability.AllAngular.GreenFormula
public import ModeStability.AllAngular.HorizonSolution
public import ModeStability.AllAngular.InfinitySolution
public import ModeStability.AllAngular.RealModeExclusionL
public import ModeStability.AllAngular.SourceIdentityRSubReciprocalEndpoints

/-!
# Endpoint inputs for the subextremal reciprocal source identity

Source: the all-angular research notes in preparation, pp. 7–8.
The Green formula and uniqueness identify every source solution with homogeneous
endpoint pieces. This supplies the radial current limits needed for (6.3).
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

open P61

/-- The range (1.7) puts corotation outside the horizon and makes `K(a)` negative. -/
theorem ssr_range_geometry {M Q e ω ρ₁ ρ₂ : ℝ} (h : Range17 M Q e ω ρ₁ ρ₂) :
    outerHorizon M Q < e / ω ∧ radialK e ω (outerHorizon M Q) < 0 := by
  have ha : 0 < outerHorizon M Q := by
    unfold outerHorizon
    exact add_pos_of_pos_of_nonneg h.1 (Real.sqrt_nonneg _)
  have he := (lt_div_iff₀ ha).mp h.2.2.2.2.1
  refine ⟨(lt_div_iff₀ h.2.2.2.1).mpr (by linarith), ?_⟩
  have hf : radialK e ω (outerHorizon M Q) =
      outerHorizon M Q * (ω * outerHorizon M Q - e) := by unfold radialK; ring
  rw [hf]
  exact mul_neg_of_pos_of_neg ha (sub_neg.mpr he)

private theorem ssr_solution_const_mul {M Q e ω L : ℝ} {T : ℝ → ℂ}
    (hT : IsRadialSolutionL M Q e ω L T) (c : ℂ) :
    IsRadialSolutionL M Q e ω L (fun r => c * T r) := by
  have ht := solution_lincomb c 0 hT hT
  simpa only [IsRadialSolutionL, zero_mul, sub_zero] using ht

/-- Every source solution has homogeneous pieces outside its compact source interval. -/
theorem ssr_endpoint_pieces {M Q e ω ρ₁ ρ₂ L : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hL : 0 ≤ L)
    {S R : ℝ → ℂ} {BH BI : ℂ} (hP : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) :
    ∃ (TH TI : ℝ → ℂ) (CH CI : ℂ),
      IsRadialSolutionL M Q e ω L TH ∧ IsRadialSolutionL M Q e ω L TI ∧
      HorizonConditionL M Q e ω TH CH ∧ InfinityConditionL M Q e ω TI CI ∧
      EqOn R TH (Ioo (outerHorizon M Q) ρ₁) ∧ EqOn R TI (Ioi ρ₂) := by
  obtain ⟨hM, hQ, he, hω, hωa, hρ₁, hρ⟩ := h
  have hK := (ssr_range_geometry ⟨hM, hQ, he, hω, hωa, hρ₁, hρ⟩).2
  have hΘ : ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
    fun r hr => hasDerivAt_integral_radialK_div_delta hr
  have hSint : Integrable S :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero (hP.2.1.integrable (by norm_num)) hP.1
  have hSi : ∀ x ∈ Ioi (outerHorizon M Q), ∀ y ∈ Ioi (outerHorizon M Q),
      IntervalIntegrable S volume x y := fun _ _ _ _ => hSint.intervalIntegrable
  obtain ⟨u, hu, huH1, huH2⟩ := exists_horizon_solution (L := L) hM hQ hK.ne hΘ
  obtain ⟨v, hv, hvI1, hvI2⟩ := exists_infinity_solution (L := L) hM hQ hω.ne' hΘ
  have huH : HorizonConditionL M Q e ω u 1 := by
    unfold HorizonConditionL
    rw [ite_eq_right fun hc => hK.ne hc.2]
    exact ⟨huH1, huH2⟩
  have hvI : InfinityConditionL M Q e ω v 1 := ⟨hvI1, hvI2⟩
  have hρ₂ : outerHorizon M Q < ρ₂ := hρ₁.trans hρ
  let W := (delta M Q ρ₁ : ℂ) * (u ρ₁ * deriv v ρ₁ - deriv u ρ₁ * v ρ₁)
  have hW : W ≠ 0 := wronskian_ne_zero hM hQ hL hω.ne' hK.ne hu huH hv hvI hρ₁
  let G : ℝ → ℂ := fun r =>
    (v r * (∫ t in ρ₁..r, u t * S t) + u r * ∫ t in r..ρ₂, v t * S t) / W
  obtain ⟨hGd, hGint⟩ := green_solution (p := delta M Q)
    (q := fun r => radialK e ω r ^ 2 / delta M Q r - L)
    (InfinityUniqueness.continuous_delta M Q).continuousOn
    (fun r hr => (InfinityUniqueness.delta_pos_of_lt hr).ne')
    (continuousOn_radialCoeff M Q e ω L) hu hv hρ₁ hW hρ₁ hρ₂ hSi
    (R := G) (fun r => rfl)
  let cH := (∫ t in ρ₁..ρ₂, v t * S t) / W
  let cI := (∫ t in ρ₁..ρ₂, u t * S t) / W
  have hGH : EqOn G (fun r => cH * u r) (Ioo (outerHorizon M Q) ρ₁) := by
    intro r hr
    exact green_eq_left hP.1 hr.2.le
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hv) hSi hr.1 hρ₁)
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hv) hSi hρ₁ hρ₂)
  have hGI : EqOn G (fun r => cI * v r) (Ioi ρ₂) := by
    intro r hr
    exact green_eq_right hP.1 hr.le
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hu) hSi hρ₁ hρ₂)
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hu) hSi hρ₂ (hρ₂.trans hr))
  have hCH := horizonConditionL_const_mul cH huH
  have hCI := infinityConditionL_const_mul cI hvI
  have hG : IsRadialSolutionWithSourceL M Q e ω L G S :=
    ⟨hGd, fun x hx y hy => ⟨hSi x hx y hy, hGint x hx y hy⟩⟩
  have hRG := source_solution_unique hM hQ hL hω.ne' hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2
    hG (horizonConditionL_of_eqOn hρ₁ hGH.symm hCH)
    (infinityConditionL_of_eqOn hGI.symm hCI)
  exact ⟨_, _, cH * 1, cI * 1, ssr_solution_const_mul hu cH,
    ssr_solution_const_mul hv cI, hCH, hCI,
    fun r hr => (hRG hr.1).trans (hGH hr),
    fun r hr => (hRG (hρ₂.trans hr)).trans (hGI hr)⟩

/-- Both physical endpoint limits for the exact interface currents. -/
theorem ssr_endpoint_currents {M Q e ω ρ₁ ρ₂ L : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) (hL : 0 ≤ L)
    {S R : ℝ → ℂ} {BH BI : ℂ} (hP : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) :
    Tendsto (fun r => -(effectiveK M Q e ω L r / khxR M Q e ω L r) *
      ‖uxR M Q e ω R r + (effectiveK M Q e ω L r : ℂ) * I * uR M Q e ω R r‖ ^ 2 -
      (uxR M Q e ω R r * (starRingEnd ℂ) (uR M Q e ω R r)).re)
      (𝓝[>] (outerHorizon M Q)) (𝓝 0) ∧
    Tendsto (fun r => -(effectiveK M Q e ω L r / khxR M Q e ω L r) *
      ‖uxR M Q e ω R r - (effectiveK M Q e ω L r : ℂ) * I * uR M Q e ω R r‖ ^ 2 -
      (uxR M Q e ω R r * (starRingEnd ℂ) (uR M Q e ω R r)).re) atTop (𝓝 0) := by
  obtain ⟨TH, TI, CH, CI, hTH, hTI, hCH, hCI, heH, heI⟩ := ssr_endpoint_pieces h hL hP
  have hK := (ssr_range_geometry h).2
  have hΘ : ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
    fun r hr => hasDerivAt_integral_radialK_div_delta hr
  unfold HorizonConditionL at hCH
  rw [ite_eq_right fun hc => hK.ne hc.2] at hCH
  exact ⟨source_sub_reciprocal_horizon_current h.1 hQ h.2.2.2.1 hL hK hN
    h.2.2.2.2.2.1 hΘ heH hP.2.2.1.1 hTH hCH.1 hCH.2,
    source_sub_reciprocal_infinity_current h.1 hQ h.2.2.2.1 hL hK hN
      hΘ heI hP.2.2.1.1 hTI hCI.1 hCI.2⟩

end ModeStability.AllAngular

end
