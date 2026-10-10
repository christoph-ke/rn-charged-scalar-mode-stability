module

public import Mathlib
public import ModeStability.AllAngular.SolutionContinuityInfinitySystem

/-!
# Recovering the radial system from outgoing amplitudes

Source: the all-angular research notes in preparation, p. 10, Proposition 6.1.
Tail continuity of the amplitudes gives continuous radial Cauchy data. The
interior stability estimate then propagates these data throughout the exterior.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

open InfinityUniqueness InfinitySolution

@[expose] noncomputable def sc_NI (M Q e L ω r : ℝ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  ODE.mat2 0 (1 / (delta M Q r : ℂ))
    (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ)) 0

@[expose] noncomputable def sc_radialPair (M Q : ℝ) (R : ℝ → ℂ) (r : ℝ) : ℂ × ℂ :=
  (R r, (delta M Q r : ℂ) * deriv R r)

theorem sc_hasDerivAt_radialPair {M Q e L ω r : ℝ} {R : ℝ → ℂ}
    (hR : IsRadialSolutionL M Q e ω L R) (hr : outerHorizon M Q < r) :
    HasDerivAt (sc_radialPair M Q R) (sc_NI M Q e L ω r (sc_radialPair M Q R r)) r := by
  have hd : (delta M Q r : ℂ) ≠ 0 := ofReal_ne_zero.2 (delta_pos_of_lt hr).ne'
  refine ((hR r hr).1.hasDerivAt.prodMk (hR r hr).2).congr_deriv ?_
  simp [sc_NI, sc_radialPair, ODE.mat2_apply, hd]

theorem sc_continuousOn_NI (M Q e L : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => sc_NI M Q e L p.1 p.2)
      (univ ×ˢ Ioi (outerHorizon M Q)) := by
  have hd : Continuous (fun p : ℝ × ℝ => delta M Q p.2) :=
    (continuous_delta M Q).comp continuous_snd
  have hn : ∀ (p : ℝ × ℝ), p ∈ univ ×ˢ Ioi (outerHorizon M Q) → delta M Q p.2 ≠ 0 :=
    fun p hp => (delta_pos_of_lt hp.2).ne'
  have h12 := (continuousOn_const (c := (1 : ℂ))).div (continuous_ofReal.comp hd).continuousOn
    (fun p hp => ofReal_ne_zero.2 (hn p hp))
  have hK : Continuous (fun p : ℝ × ℝ => radialK e p.1 p.2) := by unfold radialK; fun_prop
  have h21 : ContinuousOn (fun p : ℝ × ℝ =>
      (-((radialK e p.1 p.2) ^ 2 / delta M Q p.2 - L : ℝ) : ℂ))
      (univ ×ˢ Ioi (outerHorizon M Q)) :=
    (continuous_ofReal.comp_continuousOn
      (((hK.pow 2).continuousOn.div hd.continuousOn hn).sub
        (continuousOn_const (c := L)))).neg
  exact sc_continuousOn_mat2 continuousOn_const h12 h21 continuousOn_const

/-- Continuous amplitudes give continuous radial Cauchy data on a common tail. -/
theorem sc_continuousOn_radialPair_tail {M Q e b : ℝ} {S : Set ℝ}
    {R : ℝ → ℝ → ℂ} (hb : 0 < b)
    (hθ : ∀ ω ∈ S, ∀ r ∈ Ioi b, phaseRate M Q e ω r ≠ 0)
    (hv : ContinuousOn (fun p : ℝ × ℝ =>
      (outAmp M Q e p.1 (radialPhase M Q e p.1) (R p.1) p.2,
        inAmp M Q e p.1 (radialPhase M Q e p.1) (R p.1) p.2)) (S ×ˢ Ioi b))
    (hab : outerHorizon M Q ≤ b) :
    ContinuousOn (fun p : ℝ × ℝ => sc_radialPair M Q (R p.1) p.2) (S ×ˢ Ioi b) := by
  let T := S ×ˢ Ioi b
  have hA := continuous_fst.comp_continuousOn hv
  have hB := continuous_snd.comp_continuousOn hv
  have hΘ : ContinuousOn (fun p : ℝ × ℝ => (radialPhase M Q e p.1 p.2 : ℂ)) T :=
    continuous_ofReal.comp_continuousOn
    ((sc_continuousOn_radialPhase M Q e).mono (fun p hp => ⟨mem_univ _, hab.trans_lt hp.2⟩))
  have hE := ((continuousOn_const (c := I)).mul hΘ).cexp
  have hEi := ((continuousOn_const (c := I)).mul hΘ).neg.cexp
  have hd : Continuous (fun p : ℝ × ℝ => (delta M Q p.2 : ℂ)) :=
    continuous_ofReal.comp ((continuous_delta M Q).comp continuous_snd)
  have hK : Continuous (fun p : ℝ × ℝ => radialK e p.1 p.2) := by unfold radialK; fun_prop
  have hrate : ContinuousOn (fun p : ℝ × ℝ => (phaseRate M Q e p.1 p.2 : ℂ)) T :=
    continuous_ofReal.comp_continuousOn (hK.continuousOn.div
      ((continuous_delta M Q).comp continuous_snd).continuousOn
      (fun p hp => (delta_pos_of_lt (hab.trans_lt hp.2)).ne'))
  have hr : Continuous (fun p : ℝ × ℝ => (p.2 : ℂ)) := continuous_ofReal.comp continuous_snd
  have hden : ∀ p ∈ T, 2 * I * (phaseRate M Q e p.1 p.2 : ℂ) * (p.2 : ℂ) ≠ 0 :=
    fun p hp => mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (ofReal_ne_zero.2 (hθ p.1 hp.1 p.2 hp.2))) (ofReal_ne_zero.2 (hb.trans hp.2).ne')
  have hRc := ((hE.mul hA).sub (hEi.mul hB)).div
    ((continuousOn_const.mul hrate).mul hr.continuousOn) hden
  have hDc := ((((hE.mul hA).add (hEi.mul hB)).div_const 2).sub hRc).div
    hr.continuousOn (fun p hp => ofReal_ne_zero.2 (hb.trans hp.2).ne')
  refine (hRc.prodMk (hd.continuousOn.mul hDc)).congr ?_
  intro p hp
  simp only [Function.comp_def, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply,
    Pi.neg_apply]
  have hE0 : exp (I * (radialPhase M Q e p.1 p.2 : ℂ)) ≠ 0 := exp_ne_zero _
  have ht0 : (phaseRate M Q e p.1 p.2 : ℂ) ≠ 0 := ofReal_ne_zero.2 (hθ p.1 hp.1 p.2 hp.2)
  have hr0 : (p.2 : ℂ) ≠ 0 := ofReal_ne_zero.2 (hb.trans hp.2).ne'
  apply Prod.ext <;> simp only [sc_radialPair, outAmp, inAmp, exp_neg]
  · field_simp
    ring
  · field_simp
    ring

end ModeStability.AllAngular

end
