module

public import Mathlib
public import ModeStability.AllAngular.BoundedLRRegularity
public import ModeStability.AllAngular.BoundedLRCutoff

/-!
# Radial dephasing for Proposition 6.1

Source: the all-angular research notes in preparation. The primitive has
radial derivative `W/(Δg²)`. The phase removes the effective frequency on
the allowed sets and vanishes on the barrier, including turning points.
-/

public section

open Set Filter Topology MeasureTheory Complex

namespace ModeStability.AllAngular.P61

@[expose] noncomputable def blr_phase (M Q e ω L r : ℝ) : ℝ :=
  ∫ s in (outerHorizon M Q + 1)..r, boundedLPhaseFrequency M Q e ω L s * wR M Q e ω s

@[expose] noncomputable def blr_z (M Q e ω L : ℝ) (R : ℝ → ℂ) (r : ℝ) : ℂ :=
  uxR M Q e ω R r - (boundedLPhaseFrequency M Q e ω L r : ℂ) * I * uR M Q e ω R r

@[expose] noncomputable def blr_w (M Q e ω L : ℝ) (R : ℝ → ℂ) : ℝ → ℂ :=
  boundedLDephase (blr_phase M Q e ω L) (uR M Q e ω R)

@[expose] noncomputable def blr_v (M Q e ω L : ℝ) (R : ℝ → ℂ) (r : ℝ) : ℂ :=
  exp (-(blr_phase M Q e ω L r : ℂ) * I) * blr_z M Q e ω L R r

theorem blr_phase_continuous {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) :
    ContinuousOn (boundedLPhaseFrequency M Q e ω L) (Ioi (outerHorizon M Q)) := by
  have hg : ContinuousOn (normalizationG M Q e ω) (Ioi (outerHorizon M Q)) :=
    fun r hr => (boundedL_continuousAt_g hM hQ hr).continuousWithinAt
  have hk : Continuous (radialK e ω) := by unfold radialK; fun_prop
  have hd : Continuous (delta M Q) := by unfold delta; fun_prop
  have hf : Continuous (fun r => max (radialK e ω r ^ 2 - L * delta M Q r) 0) :=
    ((hk.pow 2).sub (hd.const_mul L)).max continuous_const
  exact (hg.pow 2).mul hf.sqrt.continuousOn

theorem blr_phase_jet {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    {r : ℝ} (hr : outerHorizon M Q < r) :
    HasDerivAt (blr_phase M Q e ω L)
      (boundedLPhaseFrequency M Q e ω L r * wR M Q e ω r) r := by
  have hc := (blr_phase_continuous (L := L) (e := e) (ω := ω) hM hQ).mul
    (blr_weight (e := e) (ω := ω) hM hQ).1
  have ha : outerHorizon M Q < outerHorizon M Q + 1 := by linarith
  exact intervalIntegral.integral_hasDerivAt_right
    ((hc.mono (ordConnected_Ioi.uIcc_subset ha hr)).intervalIntegrable)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi r hr)
    (hc.continuousAt (Ioi_mem_nhds hr))

theorem blr_u_jet {M Q e ω : ℝ} {R : ℝ → ℂ} {r : ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hr : outerHorizon M Q < r)
    (hU : DifferentiableAt ℝ (uR M Q e ω R) r) :
    HasDerivAt (uR M Q e ω R) ((wR M Q e ω r : ℂ) * uxR M Q e ω R r) r := by
  apply hU.hasDerivAt.congr_deriv
  obtain ⟨c, hg⟩ := blr_gauge (e := e) (ω := ω) hM hQ
  dsimp [uxR, wR]
  push_cast
  field_simp [(NormalizationFacts.delta_pos_of_outerHorizon_lt hr).ne', (hg r hr).2.ne']

theorem blr_dephase_regular {M Q e ω L : ℝ} {R S : ℝ → ℂ}
    (hM : 0 < M) (hQ : |Q| ≤ M)
    (hsol : IsRadialSolutionWithSourceL M Q e ω L R S) :
    (∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt (blr_w M Q e ω L R)
      (deriv (blr_w M Q e ω L R) r) r) ∧
    ContinuousOn (deriv (blr_w M Q e ω L R)) (Ioi (outerHorizon M Q)) ∧
    (∀ r ∈ Ioi (outerHorizon M Q),
      deriv (blr_w M Q e ω L R) r = (wR M Q e ω r : ℂ) * blr_v M Q e ω L R r) ∧
    (∀ r, ‖blr_w M Q e ω L R r‖ = ‖uR M Q e ω R r‖) ∧
    (∀ r, ‖blr_v M Q e ω L R r‖ = ‖blr_z M Q e ω L R r‖) := by
  obtain ⟨hU, hdU, hUx⟩ := blr_radial_regular hM hQ hsol
  have hUc : ContinuousOn (uR M Q e ω R) (Ioi (outerHorizon M Q)) :=
    fun r hr => (hU r hr).continuousAt.continuousWithinAt
  have hθc : ContinuousOn (blr_phase M Q e ω L) (Ioi (outerHorizon M Q)) :=
    fun r hr => (blr_phase_jet hM hQ hr).continuousAt.continuousWithinAt
  have hzc : ContinuousOn (blr_z M Q e ω L R) (Ioi (outerHorizon M Q)) :=
    hUx.sub (((continuous_ofReal.comp_continuousOn (blr_phase_continuous hM hQ)).mul
      continuousOn_const).mul hUc)
  have hvc : ContinuousOn (blr_v M Q e ω L R) (Ioi (outerHorizon M Q)) :=
    ((continuous_ofReal.comp_continuousOn hθc).neg.mul continuousOn_const).cexp.mul hzc
  have hjet : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt (blr_w M Q e ω L R)
      ((wR M Q e ω r : ℂ) * blr_v M Q e ω L R r) r := by
    intro r hr
    have hθ := blr_phase_jet (L := L) (e := e) (ω := ω) hM hQ hr
    have hUr := blr_u_jet hM hQ hr (hU r hr)
    have ht := ((hθ.ofReal_comp.neg.mul_const I).cexp).mul hUr
    convert ht using 1
    · rfl
    · dsimp [blr_v, blr_z]
      push_cast
      ring
  have he := fun r hr => (hjet r hr).deriv
  refine ⟨fun r hr => (hjet r hr).differentiableAt.hasDerivAt, ?_, he, ?_, ?_⟩
  · exact ((continuous_ofReal.comp_continuousOn
      (blr_weight (e := e) (ω := ω) hM hQ).1).mul hvc).congr he
  · exact fun r => bl_dephase_norm _ _ r
  · intro r
    have hn : ‖exp (-(blr_phase M Q e ω L r : ℂ) * I)‖ = 1 := by
      simpa only [ofReal_neg] using norm_exp_ofReal_mul_I (-blr_phase M Q e ω L r)
    simp only [blr_v, norm_mul, hn, one_mul]

theorem blr_allowed_phase {M Q e ω L r : ℝ}
    (hallow : L * delta M Q r < radialK e ω r ^ 2) (hK : 0 < radialK e ω r) :
    boundedLPhaseFrequency M Q e ω L r = effectiveK M Q e ω L r ∧
      effectiveK M Q e ω L r ^ 2 =
        normalizationG M Q e ω r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r) := by
  constructor
  · simp only [boundedLPhaseFrequency, effectiveK, sign_pos hK, SignType.coe_one,
      one_mul, max_eq_left (sub_pos.mpr hallow).le]
  · simp only [effectiveK, sign_pos hK, SignType.coe_one, one_mul, mul_pow,
      Real.sq_sqrt (sub_pos.mpr hallow).le]
    ring

theorem blr_dephase_ode {M Q e ω L ρ₁ ρ₂ r : ℝ} {R S : ℝ → ℂ} {BH BI : ℂ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hρ : outerHorizon M Q < ρ₂)
    (hprob : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) (hr : ρ₂ < r)
    (hallow : L * delta M Q r < radialK e ω r ^ 2) (hK : 0 < radialK e ω r) :
    HasDerivAt (blr_v M Q e ω L R)
      (-2 * I * (effectiveK M Q e ω L r : ℂ) * deriv (blr_w M Q e ω L R) r -
        I * ((deriv (effectiveK M Q e ω L) r : ℝ) : ℂ) * blr_w M Q e ω L R r) r := by
  have har := hρ.trans hr
  obtain ⟨hU, -, -⟩ := blr_radial_regular hM hQ hprob.2.2.1
  have hUr := blr_u_jet hM hQ har (hU r har)
  have hθ := blr_phase_jet (L := L) (e := e) (ω := ω) hM hQ har
  have hV := blr_ux_jet hM hQ hρ hprob r hr
  obtain ⟨c, hg⟩ := blr_gauge (e := e) (ω := ω) hM hQ
  have hgd := (hg r har).1.differentiableAt
  have hk : DifferentiableAt ℝ (effectiveK M Q e ω L) r := by
    have hs : DifferentiableAt ℝ (fun s => normalizationG M Q e ω s ^ 2 *
        Real.sqrt (radialK e ω s ^ 2 - L * delta M Q s)) r :=
      (hgd.pow 2).mul
        ((((CoefficientIdentities.hasDerivAt_radialK e ω r).differentiableAt.pow 2).sub
        ((CoefficientIdentities.hasDerivAt_delta M Q r).differentiableAt.const_mul L)).sqrt
          (sub_pos.mpr hallow).ne')
    apply hs.congr_of_eventuallyEq
    have hc : ContinuousAt (radialK e ω) r :=
      (CoefficientIdentities.hasDerivAt_radialK e ω r).continuousAt
    filter_upwards [hc.eventually (Ioi_mem_nhds hK)] with s hs
    simp only [effectiveK, sign_pos hs, SignType.coe_one, one_mul]
  have heW : boundedLPhaseFrequency M Q e ω L =ᶠ[𝓝 r] effectiveK M Q e ω L := by
    have hkc : Continuous (radialK e ω) := by unfold radialK; fun_prop
    have hdc : Continuous (delta M Q) := by unfold delta; fun_prop
    have hc : Continuous (fun s => radialK e ω s ^ 2 - L * delta M Q s) :=
      (hkc.pow 2).sub (hdc.const_mul L)
    filter_upwards [hc.continuousAt.eventually (Ioi_mem_nhds (sub_pos.mpr hallow)),
      hkc.continuousAt.eventually (Ioi_mem_nhds hK)] with s hs hKs
    exact (blr_allowed_phase (sub_pos.mp hs) hKs).1
  have hW : HasDerivAt (boundedLPhaseFrequency M Q e ω L)
      (deriv (effectiveK M Q e ω L) r) r := hk.hasDerivAt.congr_of_eventuallyEq heW
  have hz := hV.sub (((hW.ofReal_comp.mul_const I).mul hUr))
  have hv := ((hθ.ofReal_comp.neg.mul_const I).cexp).mul hz
  have hdw := (blr_dephase_regular hM hQ hprob.2.2.1).2.2.1 r har
  have hWval := (blr_allowed_phase hallow hK).1
  have hk2 := (blr_allowed_phase hallow hK).2
  convert hv using 1
  · rfl
  · rw [hdw]
    dsimp [blr_v, blr_z, blr_w, boundedLDephase]
    rw [hWval, ← hk2]
    push_cast
    ring_nf
    simp only [I_sq]
    ring

end ModeStability.AllAngular.P61

end
