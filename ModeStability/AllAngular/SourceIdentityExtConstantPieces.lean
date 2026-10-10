module

public import Mathlib
public import ModeStability.AllAngular.Prop61Interface
public import ModeStability.AllAngular.GreenFormula
public import ModeStability.AllAngular.MainAssembly
public import ModeStability.AllAngular.HorizonSolution
public import ModeStability.AllAngular.InfinitySolution

/-!
# Homogeneous endpoint pieces of the compact-source solution

Source: the all-angular research notes in preparation (pp. 7–8).
The Green formula is a multiple of the normalized horizon solution below
source support and a multiple of the infinity solution above it. Uniqueness
transfers these endpoint pieces to every solution of the shared source problem.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-- Endpoint pieces of a solution with compactly supported L² source. -/
theorem sec_homogeneous_pieces {M Q e ω L ρ₁ ρ₂ : ℝ}
    (h : P61.Range17 M Q e ω ρ₁ ρ₂) (hL : 0 ≤ L)
    {S T : ℝ → ℂ} {BH BI : ℂ} (hP : P61.SourceProblem M Q e ω L ρ₁ ρ₂ T S BH BI) :
    ∃ (TH : ℝ → ℂ) (CH : ℂ) (TI : ℝ → ℂ) (CI : ℂ),
      (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ TH r ∧
        HasDerivAt (fun s => (delta M Q s : ℂ) * deriv TH s)
          (-((radialK e ω r ^ 2 / delta M Q r - L : ℝ) : ℂ) * TH r) r) ∧
      HorizonConditionL M Q e ω TH CH ∧ EqOn T TH (Ioo (outerHorizon M Q) ρ₁) ∧
      (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ TI r ∧
        HasDerivAt (fun s => (delta M Q s : ℂ) * deriv TI s)
          (-((radialK e ω r ^ 2 / delta M Q r - L : ℝ) : ℂ) * TI r) r) ∧
      InfinityConditionL M Q e ω TI CI ∧ EqOn T TI (Ioi ρ₂) := by
  rcases h with ⟨hM, hQ, he, hω, hωa, hρ₁, hρ⟩
  have hS0 := hP.1
  have hS := hP.2.1
  set a := outerHorizon M Q with ha
  have ha0 : 0 < a := InfinityUniqueness.outerHorizon_pos hM
  have hK : radialK e ω a ≠ 0 := by
    have : ω * a < e := (lt_div_iff₀ ha0).1 hωa
    have h : radialK e ω a = a * (ω * a - e) := by
      unfold radialK
      ring
    rw [h]
    exact mul_ne_zero ha0.ne' (by linarith)
  have hΘ : ∀ r ∈ Ioi a, HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
    fun r hr => hasDerivAt_integral_radialK_div_delta hr
  -- the source is integrable
  have hSint : Integrable S volume :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero (hS.integrable one_le_two) hS0
  have hSi : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a, IntervalIntegrable S volume x y :=
    fun _ _ _ _ => hSint.intervalIntegrable
  -- the normalized solutions `R_H`, `R_I` and their Wronskian
  obtain ⟨u, hu, huH1, huH2⟩ := exists_horizon_solution (L := L) hM hQ hK hΘ
  obtain ⟨w, hw, hwI1, hwI2⟩ := exists_infinity_solution (L := L) hM hQ hω.ne' hΘ
  have huH : HorizonConditionL M Q e ω u 1 := by
    unfold HorizonConditionL
    rw [ite_eq_right fun h => hK h.2]
    exact ⟨huH1, huH2⟩
  have hwI : InfinityConditionL M Q e ω w 1 := ⟨hwI1, hwI2⟩
  have hρ₁' : ρ₁ ∈ Ioi a := hρ₁
  have hρ₂' : ρ₂ ∈ Ioi a := lt_trans hρ₁ hρ
  have hW := wronskian_ne_zero hM hQ hL hω.ne' hK hu huH hw hwI hρ₁'
  set W := (delta M Q ρ₁ : ℂ) * (u ρ₁ * deriv w ρ₁ - deriv u ρ₁ * w ρ₁) with hWdef
  -- the Green formula
  set R : ℝ → ℂ := fun r =>
    (w r * (∫ t in ρ₁..r, u t * S t) + u r * ∫ t in r..ρ₂, w t * S t) / W with hRdef
  obtain ⟨hRd, hRint⟩ := green_solution (p := delta M Q)
    (q := fun r => (radialK e ω r) ^ 2 / delta M Q r - L)
    (InfinityUniqueness.continuous_delta M Q).continuousOn
    (fun r hr => (InfinityUniqueness.delta_pos_of_lt hr).ne') (continuousOn_radialCoeff M Q e ω L)
    hu hw hρ₁' hW hρ₁' hρ₂' hSi (R := R) (fun r => rfl)
  have hcu := gf_continuousOn_sol hu
  have hcw := gf_continuousOn_sol hw
  let cH : ℂ := (∫ t in ρ₁..ρ₂, w t * S t) / W
  let cI : ℂ := (∫ t in ρ₁..ρ₂, u t * S t) / W
  have heH : EqOn R (fun r => cH * u r) (Ioo a ρ₁) := by
    intro r hr
    exact green_eq_left (u := u) (w := w) (W := W) hS0 hr.2.le
      (gf_intervalIntegrable_mul hcw hSi hr.1 hρ₁')
      (gf_intervalIntegrable_mul hcw hSi hρ₁' hρ₂')
  have heI : EqOn R (fun r => cI * w r) (Ioi ρ₂) := by
    intro r hr
    exact green_eq_right (u := u) (w := w) (W := W) hS0 hr.le
      (gf_intervalIntegrable_mul hcu hSi hρ₁' hρ₂')
      (gf_intervalIntegrable_mul hcu hSi hρ₂' (hρ₂'.trans hr))
  have hcH := horizonConditionL_const_mul cH huH
  have hcI := infinityConditionL_const_mul cI hwI
  have hRH := horizonConditionL_of_eqOn hρ₁ heH.symm hcH
  have hRI := infinityConditionL_of_eqOn heI.symm hcI
  have hfull : IsRadialSolutionWithSourceL M Q e ω L R S :=
    ⟨hRd, fun r hr s hs => ⟨hSi r hr s hs, hRint r hr s hs⟩⟩
  have he := source_solution_unique hM hQ hL hω.ne' hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2
    hfull hRH hRI
  have hTH := solution_lincomb (p := delta M Q)
    (q := fun r => radialK e ω r ^ 2 / delta M Q r - L) cH 0 hu hu
  have hTI := solution_lincomb (p := delta M Q)
    (q := fun r => radialK e ω r ^ 2 / delta M Q r - L) cI 0 hw hw
  simp only [zero_mul, sub_zero] at hTH hTI
  refine ⟨(fun r => cH * u r), cH * 1, (fun r => cI * w r), cI * 1,
    hTH, hcH, ?_, hTI, hcI, ?_⟩
  · intro r hr
    exact (he hr.1).trans (heH hr)
  · intro r hr
    exact (he (hρ₂'.trans hr)).trans (heI hr)

end ModeStability.AllAngular

end
