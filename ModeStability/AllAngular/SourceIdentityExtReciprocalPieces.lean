module

public import Mathlib
public import ModeStability.AllAngular.MainAssembly
public import ModeStability.AllAngular.GreenFormula
public import ModeStability.AllAngular.HorizonSolution
public import ModeStability.AllAngular.InfinitySolution
public import ModeStability.AllAngular.InfinityUniqueness
public import ModeStability.AllAngular.Prop61Interface

/-!
# Homogeneous pieces of the compactly supported source solution

Source: the all-angular research notes in preparation, pp. 7–8.
The Green formula is a multiple of the ingoing solution below the source
and a multiple of the outgoing solution above it. Uniqueness identifies
an arbitrary source solution with this Green solution on the exterior.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-- The endpoint pieces needed for the extremal reciprocal current limits. -/
theorem ser_endpoint_pieces {M Q e ω ρ₁ ρ₂ L : ℝ}
    (h : P61.Range17 M Q e ω ρ₁ ρ₂) (hL : 0 ≤ L)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) :
    ∃ (T_H T_I : ℝ → ℂ) (B_H B_I : ℂ),
      IsRadialSolutionL M Q e ω L T_H ∧ IsRadialSolutionL M Q e ω L T_I ∧
      HorizonConditionL M Q e ω T_H B_H ∧ InfinityConditionL M Q e ω T_I B_I ∧
      EqOn R T_H (Ioo (outerHorizon M Q) ρ₁) ∧ EqOn R T_I (Ioi ρ₂) := by
  rcases h with ⟨hM, hQ, he, hω, hωa, hρ₁, hρ⟩
  rcases hP with ⟨hS0, hS, hR, hH, hI⟩
  have ha0 : 0 < outerHorizon M Q := InfinityUniqueness.outerHorizon_pos hM
  have hK : radialK e ω (outerHorizon M Q) ≠ 0 := by
    have hka := (lt_div_iff₀ ha0).mp hωa
    have hh : radialK e ω (outerHorizon M Q) =
        outerHorizon M Q * (ω * outerHorizon M Q - e) := by unfold radialK; ring
    rw [hh]
    exact mul_ne_zero ha0.ne' (by linarith)
  have hΘ : ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
    fun r hr => hasDerivAt_integral_radialK_div_delta hr
  have hSint : Integrable S volume :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero (hS.integrable one_le_two) hS0
  have hSi : ∀ x ∈ Ioi (outerHorizon M Q), ∀ y ∈ Ioi (outerHorizon M Q),
      IntervalIntegrable S volume x y := fun _ _ _ _ => hSint.intervalIntegrable
  obtain ⟨u, hu, huH1, huH2⟩ := exists_horizon_solution (L := L) hM hQ hK hΘ
  obtain ⟨w, hw, hwI1, hwI2⟩ := exists_infinity_solution (L := L) hM hQ hω.ne' hΘ
  have huH : HorizonConditionL M Q e ω u 1 := by
    unfold HorizonConditionL
    rw [ite_eq_right fun hh => hK hh.2]
    exact ⟨huH1, huH2⟩
  have hwI : InfinityConditionL M Q e ω w 1 := ⟨hwI1, hwI2⟩
  have hρ₂ : outerHorizon M Q < ρ₂ := hρ₁.trans hρ
  have hW := wronskian_ne_zero hM hQ hL hω.ne' hK hu huH hw hwI hρ₁
  let W := (delta M Q ρ₁ : ℂ) * (u ρ₁ * deriv w ρ₁ - deriv u ρ₁ * w ρ₁)
  let G : ℝ → ℂ := fun r =>
    (w r * (∫ t in ρ₁..r, u t * S t) + u r * ∫ t in r..ρ₂, w t * S t) / W
  obtain ⟨hGd, hGint⟩ := green_solution (p := delta M Q)
    (q := fun r => radialK e ω r ^ 2 / delta M Q r - L)
    (InfinityUniqueness.continuous_delta M Q).continuousOn
    (fun r hr => (InfinityUniqueness.delta_pos_of_lt hr).ne') (continuousOn_radialCoeff M Q e ω L)
    hu hw hρ₁ hW hρ₁ hρ₂ hSi (R := G) (fun r => rfl)
  let cH := (∫ t in ρ₁..ρ₂, w t * S t) / W
  let cI := (∫ t in ρ₁..ρ₂, u t * S t) / W
  have hGH : EqOn G (fun r => cH * u r) (Ioo (outerHorizon M Q) ρ₁) := by
    intro r hr
    exact green_eq_left hS0 hr.2.le
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hw) hSi hr.1 hρ₁)
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hw) hSi hρ₁ hρ₂)
  have hGI : EqOn G (fun r => cI * w r) (Ioi ρ₂) := by
    intro r hr
    exact green_eq_right hS0 hr.le
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hu) hSi hρ₁ hρ₂)
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hu) hSi hρ₂ (hρ₂.trans hr))
  have hTH := horizonConditionL_const_mul cH huH
  have hTI := infinityConditionL_const_mul cI hwI
  have hRG : EqOn R G (Ioi (outerHorizon M Q)) :=
    source_solution_unique hM hQ hL hω.ne' hR hH hI
      ⟨hGd, fun x hx y hy => ⟨hSi x hx y hy, hGint x hx y hy⟩⟩
      (horizonConditionL_of_eqOn hρ₁ hGH.symm hTH)
      (infinityConditionL_of_eqOn hGI.symm hTI)
  have hzero : IsRadialSolutionL M Q e ω L (fun _ => (0 : ℂ)) := by
    intro r hr
    simp only [deriv_const, mul_zero]
    exact ⟨differentiableAt_const _, hasDerivAt_const _ _⟩
  refine ⟨fun r => cH * u r, fun r => cI * w r, cH * 1, cI * 1, ?_, ?_, hTH, hTI, ?_, ?_⟩
  · unfold IsRadialSolutionL
    simpa only [mul_zero, sub_zero] using solution_lincomb cH 0 hu hzero
  · unfold IsRadialSolutionL
    simpa only [mul_zero, sub_zero] using solution_lincomb cI 0 hw hzero
  · intro r hr
    exact (hRG hr.1).trans (hGH hr)
  · intro r hr
    exact (hRG (hρ₂.trans hr)).trans (hGI hr)

end ModeStability.AllAngular

end
