module

public import Mathlib
public import ModeStability.AllAngular.Prop61Interface
public import ModeStability.AllAngular.BoundedLCoefficients
public import ModeStability.AllAngular.SourceIdentityRAux

/-!
# Radial regularity for the bounded angular estimate

Source: the all-angular research notes in preparation, Proposition 6.1.
The integrated equation gives a continuous first derivative even for an L²
source. Beyond the source support the transformed flux satisfies the classical
homogeneous equation. The argument treats both gauges and extremality together.
-/

public section

open Set Filter Topology MeasureTheory Complex

namespace ModeStability.AllAngular.P61

theorem blr_gauge {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) :
    ∃ c : ℝ, ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt (normalizationG M Q e ω) (c / delta M Q r) r ∧
        0 < normalizationG M Q e ω r := by
  by_cases hn : e / ω < 2 * M
  · refine ⟨0, ?_⟩
    intro r hr
    rw [NormalizationFacts.normalizationG_eq_one hn]
    exact ⟨by simpa using hasDerivAt_const r (1 : ℝ), one_pos⟩
  · refine ⟨-1, ?_⟩
    intro r hr
    rw [NormalizationFacts.normalizationG_eq_static hn]
    exact ⟨NormalizationFacts.hasDerivAt_staticSolutionAA hM hQ hr,
      NormalizationFacts.staticSolutionAA_pos hM hr⟩

theorem blr_weight {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) :
    ContinuousOn (wR M Q e ω) (Ioi (outerHorizon M Q)) ∧
      ∀ r ∈ Ioi (outerHorizon M Q), 0 < wR M Q e ω r := by
  obtain ⟨c, hg⟩ := blr_gauge (e := e) (ω := ω) hM hQ
  have hd : Continuous (delta M Q) := by unfold delta; fun_prop
  have hgc : ContinuousOn (normalizationG M Q e ω) (Ioi (outerHorizon M Q)) :=
    fun r hr => (hg r hr).1.continuousAt.continuousWithinAt
  exact ⟨continuousOn_const.div (hd.continuousOn.mul (hgc.pow 2))
    (fun r hr => (mul_pos (NormalizationFacts.delta_pos_of_outerHorizon_lt hr)
      (pow_pos (hg r hr).2 2)).ne'),
    fun r hr => one_div_pos.mpr (mul_pos
      (NormalizationFacts.delta_pos_of_outerHorizon_lt hr) (pow_pos (hg r hr).2 2))⟩

theorem blr_radial_regular {M Q e ω L : ℝ} {R S : ℝ → ℂ}
    (hM : 0 < M) (hQ : |Q| ≤ M)
    (hsol : IsRadialSolutionWithSourceL M Q e ω L R S) :
    (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ (uR M Q e ω R) r) ∧
      ContinuousOn (deriv (uR M Q e ω R)) (Ioi (outerHorizon M Q)) ∧
      ContinuousOn (uxR M Q e ω R) (Ioi (outerHorizon M Q)) := by
  let a := outerHorizon M Q
  let q : ℝ → ℝ := fun r => radialK e ω r ^ 2 / delta M Q r - L
  have hd : Continuous (delta M Q) := by unfold delta; fun_prop
  have hk : Continuous (radialK e ω) := by unfold radialK; fun_prop
  have hd0 : ∀ r ∈ Ioi a, delta M Q r ≠ 0 :=
    fun r hr => (NormalizationFacts.delta_pos_of_outerHorizon_lt hr).ne'
  have hq : ContinuousOn q (Ioi a) :=
    ((hk.pow 2).continuousOn.div hd.continuousOn hd0).sub continuousOn_const
  have hi := fun b hb c hc => (hsol.2 b hb c hc).1
  have he := fun b hb c hc => (hsol.2 b hb c hc).2
  have hRC := source_solution_contDiffOn_one hd.continuousOn hd0 hq hsol.1 hi he
  have hdR := hRC.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  obtain ⟨c, hg⟩ := blr_gauge (e := e) (ω := ω) hM hQ
  have hgc : ContinuousOn (normalizationG M Q e ω) (Ioi a) :=
    fun r hr => (hg r hr).1.continuousAt.continuousWithinAt
  have hdc : ContinuousOn (fun r => c / delta M Q r) (Ioi a) :=
    continuousOn_const.div hd.continuousOn hd0
  have hRc : ContinuousOn R (Ioi a) :=
    fun r hr => (hsol.1 r hr).continuousAt.continuousWithinAt
  have hU : ∀ r ∈ Ioi a, DifferentiableAt ℝ (uR M Q e ω R) r := by
    intro r hr
    exact (hsol.1 r hr).div (hg r hr).1.ofReal_comp.differentiableAt
      (ofReal_ne_zero.mpr (hg r hr).2.ne')
  have hdU : ContinuousOn (deriv (uR M Q e ω R)) (Ioi a) := by
    have hc := ((hdR.mul (continuous_ofReal.comp_continuousOn hgc)).sub
      (hRc.mul
        (continuous_ofReal.comp_continuousOn hdc))).div
      ((continuous_ofReal.comp_continuousOn hgc).pow 2)
      (fun r hr => pow_ne_zero 2 (ofReal_ne_zero.mpr (hg r hr).2.ne'))
    apply hc.congr
    intro r hr
    exact ((hsol.1 r hr).hasDerivAt.div (hg r hr).1.ofReal_comp
      (ofReal_ne_zero.mpr (hg r hr).2.ne')).deriv
  exact ⟨hU, hdU,
    (continuous_ofReal.comp_continuousOn (hd.continuousOn.mul (hgc.pow 2))).mul hdU⟩

theorem blr_ux_jet {M Q e ω L ρ₁ ρ₂ : ℝ} {R S : ℝ → ℂ} {BH BI : ℂ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hρ : outerHorizon M Q < ρ₂)
    (hprob : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) :
    ∀ r ∈ Ioi ρ₂, HasDerivAt (uxR M Q e ω R)
      (-(wR M Q e ω r : ℂ) *
        ((normalizationG M Q e ω r ^ 4 *
          (radialK e ω r ^ 2 - L * delta M Q r) : ℝ) : ℂ) * uR M Q e ω R r) r := by
  obtain ⟨hsupp, -, hsol, -, -⟩ := hprob
  let q : ℝ → ℝ := fun r => radialK e ω r ^ 2 / delta M Q r - L
  have hq : ContinuousOn q (Ioi ρ₂) := by
    have hk : Continuous (radialK e ω) := by unfold radialK; fun_prop
    have hd : Continuous (delta M Q) := by unfold delta; fun_prop
    exact ((hk.pow 2).continuousOn.div hd.continuousOn
      (fun r hr => (NormalizationFacts.delta_pos_of_outerHorizon_lt (hρ.trans hr)).ne')).sub
        continuousOn_const
  have hint : ∀ b ∈ Ioi ρ₂, ∀ c ∈ Ioi ρ₂,
      (delta M Q c : ℂ) * deriv R c - (delta M Q b : ℂ) * deriv R b =
        -∫ r in b..c, (q r : ℂ) * R r := by
    intro b hb c hc
    rw [(hsol.2 b (hρ.trans hb) c (hρ.trans hc)).2, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr₂ : ρ₂ < r := (lt_min hb hc).trans_le hr.1
    change S r - (q r : ℂ) * R r = -((q r : ℂ) * R r)
    rw [hsupp r (fun hn => (not_le_of_gt hr₂) hn.2), zero_sub]
  obtain ⟨c, hg⟩ := blr_gauge (e := e) (ω := ω) hM hQ
  have hux : ∀ s ∈ Ioi (outerHorizon M Q), uxR M Q e ω R s =
      (normalizationG M Q e ω s : ℂ) * ((delta M Q s : ℂ) * deriv R s) - (c : ℂ) * R s := by
    intro s hs
    have ht := ((hsol.1 s hs).hasDerivAt.div (hg s hs).1.ofReal_comp
      (ofReal_ne_zero.mpr (hg s hs).2.ne')).deriv
    change ((delta M Q s * normalizationG M Q e ω s ^ 2 : ℝ) : ℂ) *
      deriv (R / fun y => (normalizationG M Q e ω y : ℂ)) s = _
    rw [ht]
    push_cast
    field_simp [(NormalizationFacts.delta_pos_of_outerHorizon_lt hs).ne', (hg s hs).2.ne']
  intro r hr
  have har := hρ.trans hr
  have hf := (hasDerivAt_of_integrated hq (fun s hs => hsol.1 s (hρ.trans hs)) hint r hr).2
  have hz : S r = 0 := hsupp r (fun hn => (not_le_of_gt hr) hn.2)
  have hf' : HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
      (S r - (q r : ℂ) * R r) r := by simpa [hz] using hf
  have hv := (source_reduction_at (NormalizationFacts.delta_pos_of_outerHorizon_lt har).ne'
    (hg r har).2.ne' (hg r har).1 (hsol.1 r har) hf').2
  have hc : normalizationG M Q e ω r ^ 4 * delta M Q r * q r =
      normalizationG M Q e ω r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r) := by
    dsimp [q]
    field_simp [(NormalizationFacts.delta_pos_of_outerHorizon_lt har).ne']
  rw [hc, hz] at hv
  simp only [mul_zero, add_zero] at hv
  apply (hv.congr_deriv (by dsimp [wR, uR]; ring)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds har] with s hs
  exact hux s hs

end ModeStability.AllAngular.P61

end
