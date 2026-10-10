module

public import Mathlib
public import ModeStability.AllAngular.Prop61Interface
public import ModeStability.AllAngular.GreenFormula
public import ModeStability.AllAngular.HorizonSolution
public import ModeStability.AllAngular.InfinitySolution
public import ModeStability.AllAngular.CoordinateIntervals
public import ModeStability.AllAngular.MainAssembly

/-!
# Homogeneous endpoint pieces of the constant source problem

Source: the all-angular research notes in preparation, pp. 7–8.
The Green formula agrees with scalar multiples of the normalized horizon
and infinity solutions outside the source support. Uniqueness transfers
these equalities to every solution of the shared source problem.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-- The homogeneous radial equation in first-flux form. -/
@[expose] def ssc_homogeneous (M Q e ω L : ℝ) (T : ℝ → ℂ) : Prop :=
  ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ T r ∧
    HasDerivAt (fun s => (delta M Q s : ℂ) * deriv T s)
      (-(((radialK e ω r ^ 2 / delta M Q r - L : ℝ) : ℂ)) * T r) r

/-- Every source solution is homogeneous near both physical endpoints. -/
theorem ssc_green_pieces {M Q e ω L ρ₁ ρ₂ : ℝ}
    (h : P61.Range17 M Q e ω ρ₁ ρ₂) (hL : 0 ≤ L)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) :
    ∃ TH TI : ℝ → ℂ, ∃ CH CI : ℂ,
      ssc_homogeneous M Q e ω L TH ∧ ssc_homogeneous M Q e ω L TI ∧
      EqOn R TH (Ioo (outerHorizon M Q) ρ₁) ∧ EqOn R TI (Ioi ρ₂) ∧
      HorizonConditionL M Q e ω TH CH ∧ InfinityConditionL M Q e ω TI CI := by
  have ha0 : 0 < outerHorizon M Q := InfinityUniqueness.outerHorizon_pos h.1
  have he := (lt_div_iff₀ ha0).mp h.2.2.2.2.1
  have hK : radialK e ω (outerHorizon M Q) ≠ 0 := by
    have hk : radialK e ω (outerHorizon M Q) = outerHorizon M Q *
        (ω * outerHorizon M Q - e) := by unfold radialK; ring
    rw [hk]
    exact mul_ne_zero ha0.ne' (by linarith)
  have hΘ : ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
    fun r hr => hasDerivAt_integral_radialK_div_delta hr
  obtain ⟨u, hu, huH1, huH2⟩ := exists_horizon_solution (L := L) h.1 h.2.1 hK hΘ
  obtain ⟨w, hw, hwI1, hwI2⟩ := exists_infinity_solution (L := L) h.1 h.2.1 h.2.2.2.1.ne' hΘ
  have huH : HorizonConditionL M Q e ω u 1 := by
    unfold HorizonConditionL
    rw [ite_eq_right fun hc => hK hc.2]
    exact ⟨huH1, huH2⟩
  have hwI : InfinityConditionL M Q e ω w 1 := ⟨hwI1, hwI2⟩
  have hρ₁ := h.2.2.2.2.2.1
  have hρ₁₂ := h.2.2.2.2.2.2
  have hρ₂ := hρ₁.trans hρ₁₂
  have hSi := fun b hb c hc => (hP.2.2.1.2 b hb c hc).1
  let W := (delta M Q ρ₁ : ℂ) * (u ρ₁ * deriv w ρ₁ - deriv u ρ₁ * w ρ₁)
  have hW : W ≠ 0 := wronskian_ne_zero h.1 h.2.1 hL h.2.2.2.1.ne' hK hu huH hw hwI hρ₁
  let G : ℝ → ℂ := fun r =>
    (w r * (∫ t in ρ₁..r, u t * S t) + u r * ∫ t in r..ρ₂, w t * S t) / W
  obtain ⟨hGd, hGint⟩ := green_solution (p := delta M Q)
    (q := fun r => radialK e ω r ^ 2 / delta M Q r - L)
    (InfinityUniqueness.continuous_delta M Q).continuousOn
    (fun r hr => (InfinityUniqueness.delta_pos_of_lt hr).ne') (continuousOn_radialCoeff M Q e ω L)
    hu hw hρ₁ hW hρ₁ hρ₂ hSi (R := G) (fun r => rfl)
  let cH := (∫ t in ρ₁..ρ₂, w t * S t) / W
  let cI := (∫ t in ρ₁..ρ₂, u t * S t) / W
  have hleft : EqOn G (fun r => cH * u r) (Ioo (outerHorizon M Q) ρ₁) := by
    intro r hr
    exact green_eq_left (u := u) (w := w) (W := W) hP.1 hr.2.le
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hw) hSi hr.1 hρ₁)
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hw) hSi hρ₁ hρ₂)
  have hright : EqOn G (fun r => cI * w r) (Ioi ρ₂) := by
    intro r hr
    exact green_eq_right (u := u) (w := w) (W := W) hP.1 hr.le
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hu) hSi hρ₁ hρ₂)
      (gf_intervalIntegrable_mul (gf_continuousOn_sol hu) hSi hρ₂ (hρ₂.trans hr))
  have hHH := horizonConditionL_const_mul cH huH
  have hII := infinityConditionL_const_mul cI hwI
  have hGH := horizonConditionL_of_eqOn hρ₁ hleft.symm hHH
  have hGI := infinityConditionL_of_eqOn hright.symm hII
  have hEq := source_solution_unique h.1 h.2.1 hL h.2.2.2.1.ne' hP.2.2.1 hP.2.2.2.1
    hP.2.2.2.2 ⟨hGd, fun b hb c hc => ⟨hSi b hb c hc, hGint b hb c hc⟩⟩ hGH hGI
  refine ⟨fun r => cH * u r, fun r => cI * w r, cH * 1, cI * 1, ?_, ?_, ?_, ?_, hHH, hII⟩
  · unfold ssc_homogeneous
    simpa only [zero_mul, sub_zero] using solution_lincomb cH 0 hu hu
  · unfold ssc_homogeneous
    simpa only [zero_mul, sub_zero] using solution_lincomb cI 0 hw hw
  · intro r hr
    exact (hEq hr.1).trans (hleft hr)
  · intro r hr
    exact (hEq (hρ₂.trans hr)).trans (hright hr)

end ModeStability.AllAngular

end
