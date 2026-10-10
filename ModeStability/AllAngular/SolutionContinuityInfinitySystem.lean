module

public import Mathlib
public import ModeStability.AllAngular.SolutionContinuityInfinityAux
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL

/-!
# Parameter dependent outgoing amplitude system

Source: the all-angular research notes in preparation, p. 10.
The normalized radial solutions give solutions of the outgoing amplitude system;
its coefficients are jointly continuous on any tail where the phase rate is nonzero.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

open InfinityUniqueness InfinitySolution

/-- Matrix continuity with an arbitrary parameter space. -/
theorem sc_continuousOn_mat2 {X : Type*} [TopologicalSpace X] {S : Set X}
    {f g h k : X → ℂ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hh : ContinuousOn h S) (hk : ContinuousOn k S) :
    ContinuousOn (fun x => ODE.mat2 (f x) (g x) (h x) (k x)) S := by
  have heq : ∀ a b c d : ℂ, ODE.mat2 a b c d =
      a • (ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ ℂ ℂ) +
      b • (ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ ℂ) +
      c • (ContinuousLinearMap.inr ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ ℂ ℂ) +
      d • (ContinuousLinearMap.inr ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ ℂ) := by
    intro a b c d
    ext <;> simp [ODE.mat2_apply]
  simp_rw [heq]
  exact (((hf.smul continuousOn_const).add (hg.smul continuousOn_const)).add
    (hh.smul continuousOn_const)).add (hk.smul continuousOn_const)

@[expose] noncomputable def sc_MI (M Q e L ω r : ℝ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  ODE.mat2 (ampCoeffAA M Q e ω L r)
    (ampCoeffAB M Q e ω L (radialPhase M Q e ω) r)
    (ampCoeffBA M Q e ω L (radialPhase M Q e ω) r) (ampCoeffBB M Q e ω L r)

theorem sc_norm_MI_le (M Q e L ω r : ℝ) :
    ‖sc_MI M Q e L ω r‖ ≤ 4 * errCoeff M Q e ω L r := by
  refine (ODE.norm_mat2_le _ _ _ _).trans ?_
  have := norm_ampCoeffAA_le M Q e ω L r
  have := norm_ampCoeffAB_le M Q e ω L (radialPhase M Q e ω) r
  have := norm_ampCoeffBA_le M Q e ω L (radialPhase M Q e ω) r
  have := norm_ampCoeffBB_le M Q e ω L r
  linarith

theorem sc_continuousOn_MI {M Q e L b : ℝ} {S : Set ℝ} (hab : outerHorizon M Q ≤ b)
    (hb : 0 < b) (hθ : ∀ ω ∈ S, ∀ r ∈ Ioi b, phaseRate M Q e ω r ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ => sc_MI M Q e L p.1 p.2) (S ×ˢ Ioi b) := by
  let T := S ×ˢ Ioi b
  have hd : Continuous (fun p : ℝ × ℝ => delta M Q p.2) :=
    (continuous_delta M Q).comp continuous_snd
  have hdn : ∀ p ∈ T, delta M Q p.2 ≠ 0 := fun p hp =>
    (delta_pos_of_lt (hab.trans_lt hp.2)).ne'
  have hrn : ∀ p ∈ T, p.2 ≠ 0 := fun p hp => (hb.trans hp.2).ne'
  have hK : Continuous (fun p : ℝ × ℝ => radialK e p.1 p.2) := by unfold radialK; fun_prop
  have ht : ContinuousOn (fun p : ℝ × ℝ => phaseRate M Q e p.1 p.2) T :=
    hK.continuousOn.div hd.continuousOn hdn
  have ha : ContinuousOn (fun p : ℝ × ℝ => phaseAccel M Q e p.1 p.2) T := by
    unfold phaseAccel
    refine ((Continuous.continuousOn (by fun_prop)).sub
      (hK.continuousOn.mul (Continuous.continuousOn (by fun_prop)))).div
      (hd.continuousOn.pow 2) (fun p hp => pow_ne_zero 2 (hdn p hp))
  have hc : ContinuousOn (fun p : ℝ × ℝ => dampCoeff M Q p.2) T := by
    unfold dampCoeff
    exact (Continuous.continuousOn (by fun_prop)).div
      (continuous_snd.continuousOn.mul hd.continuousOn) fun p hp =>
        mul_ne_zero (hrn p hp) (hdn p hp)
  have hg : ContinuousOn (fun p : ℝ × ℝ => potCoeff M Q L p.2) T := by
    unfold potCoeff
    exact (Continuous.continuousOn (by fun_prop)).div
      ((continuous_snd.continuousOn.pow 2).mul hd.continuousOn) fun p hp =>
        mul_ne_zero (pow_ne_zero 2 (hrn p hp)) (hdn p hp)
  have htn : ∀ p ∈ T, 2 * phaseRate M Q e p.1 p.2 ≠ 0 :=
    fun p hp => mul_ne_zero two_ne_zero (hθ p.1 hp.1 p.2 hp.2)
  have hP := (hc.neg.div_const 2).add (ha.div (continuousOn_const.mul ht) htn)
  have hM := (hc.neg.div_const 2).sub (ha.div (continuousOn_const.mul ht) htn)
  have hs := hg.div (continuousOn_const.mul ht) htn
  have hPc := continuous_ofReal.comp_continuousOn hP
  have hMc := continuous_ofReal.comp_continuousOn hM
  have hsc := (continuousOn_const (c := I)).mul (continuous_ofReal.comp_continuousOn hs)
  have hΘ := continuous_ofReal.comp_continuousOn ((sc_continuousOn_radialPhase M Q e).mono
    (fun p hp => ⟨mem_univ _, hab.trans_lt hp.2⟩) :
      ContinuousOn (fun p : ℝ × ℝ => radialPhase M Q e p.1 p.2) T)
  have hE := ((continuousOn_const (c := I)).mul hΘ).cexp
  have hEi := ((continuousOn_const (c := I)).mul hΘ).neg.cexp
  exact sc_continuousOn_mat2 (hPc.add hsc) ((hEi.pow 2).mul (hMc.sub hsc))
    ((hE.pow 2).mul (hMc.add hsc)) (hPc.sub hsc)


/-- The amplitudes of any radial solution satisfy the tail system. -/
theorem sc_hasDerivAt_amps {M Q e ω L r : ℝ} (hQ : |Q| ≤ M)
    (hr : outerHorizon M Q < r) (hr0 : 0 < r) (hθ : phaseRate M Q e ω r ≠ 0)
    {R : ℝ → ℂ} (hR : IsRadialSolutionL M Q e ω L R) :
    HasDerivAt (fun s => (outAmp M Q e ω (radialPhase M Q e ω) R s,
      inAmp M Q e ω (radialPhase M Q e ω) R s))
      (sc_MI M Q e L ω r (outAmp M Q e ω (radialPhase M Q e ω) R r,
        inAmp M Q e ω (radialPhase M Q e ω) R r)) r := by
  have hΘ := sc_hasDerivAt_radialPhase M Q e ω hr
  have hout := hasDerivAt_outAmp hQ hr hr0 hΘ (hR r hr)
  have hin := hasDerivAt_inAmp hQ hr hr0 hΘ (hR r hr)
  refine (hout.prodMk hin).congr_deriv ?_
  rw [sc_MI, ODE.mat2_apply]
  have hθc : (phaseRate M Q e ω r : ℂ) ≠ 0 := ofReal_ne_zero.2 hθ
  have hE : exp (I * (radialPhase M Q e ω r : ℂ)) ≠ 0 := exp_ne_zero _
  simp only [outAmp, inAmp, ampCoeffAA, ampCoeffAB, ampCoeffBA, ampCoeffBB,
    ampRhoP, ampRhoM, ampSigma]
  push_cast
  rw [exp_neg]
  generalize exp (I * (radialPhase M Q e ω r : ℂ)) = E at hE ⊢
  generalize (phaseRate M Q e ω r : ℂ) = θ at hθc ⊢
  apply Prod.ext <;> dsimp only
  · field_simp
    ring_nf
    simp only [I_sq]
    ring
  · field_simp
    ring_nf
    simp only [I_sq]
    ring

/-- Normalized outgoing solutions have amplitude limit `(2iω, 0)`. -/
theorem sc_tendsto_amps_one {M Q e ω L : ℝ} (hQ : |Q| ≤ M)
    {R : ℝ → ℂ} (hR : IsRadialSolutionL M Q e ω L R)
    (hI : InfinityConditionL M Q e ω R 1) :
    Tendsto (fun r => (outAmp M Q e ω (radialPhase M Q e ω) R r,
      inAmp M Q e ω (radialPhase M Q e ω) R r)) atTop (𝓝 (2 * I * ω, 0)) := by
  let Θ := radialPhase M Q e ω
  have hP : Tendsto (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) atTop (𝓝 1) := by
    have h := (hI.1.trans_tendsto tendsto_inv_atTop_zero).add_const 1
    simpa using h
  have hW : Tendsto (deriv (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r))
      atTop (𝓝 0) :=
    hI.2.trans_tendsto (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero))
  have hd : ∀ r ∈ Ioi (outerHorizon M Q),
      deriv (fun s : ℝ => (s : ℂ) * exp (-(I * Θ s)) * R s) r =
        exp (-(I * Θ r)) * ((R r + r * deriv R r) - I * phaseRate M Q e ω r * (r * R r)) :=
    fun r hr => (hasDerivAt_profile (sc_hasDerivAt_radialPhase M Q e ω hr) (hR r hr).1).deriv
  have hθ : Tendsto (fun r => (phaseRate M Q e ω r : ℂ)) atTop (𝓝 (ω : ℂ)) :=
    (continuous_ofReal.tendsto ω).comp (tendsto_phaseRate hQ e ω)
  have hA : Tendsto (outAmp M Q e ω Θ R) atTop (𝓝 (2 * I * ω)) := by
    have h := hW.add (((tendsto_const_nhds (x := 2 * I)).mul hθ).mul hP)
    simp only [mul_one, zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
    rw [hd r hr]
    simp only [outAmp]
    ring
  have hB : Tendsto (inAmp M Q e ω Θ R) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := hW.norm
    rw [norm_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
    rw [hd r hr]
    simp only [inAmp, norm_mul, norm_exp_neg_I_mul, norm_exp_I_mul]
  exact hA.prodMk_nhds hB

/-- Integrability and dominated parameter convergence on a common tail. -/
theorem sc_tail_stability_data {M Q e L b C : ℝ} {S : Set ℝ}
    (hab : outerHorizon M Q ≤ b) (hb : 0 < b)
    (hbound : ∀ ω ∈ S, ∀ r, b < r →
      phaseRate M Q e ω r ≠ 0 ∧ errCoeff M Q e ω L r ≤ C / r ^ 2) :
    (∀ ω ∈ S, ∀ t ∈ Ioi b, IntegrableOn (fun x => ‖sc_MI M Q e L ω x‖) (Ioi t)) ∧
    (∀ ω₀ ∈ S, ∀ t ∈ Ioi b,
      Tendsto (fun ω => ∫ x in Ioi t, ‖sc_MI M Q e L ω x - sc_MI M Q e L ω₀ x‖)
        (𝓝[S] ω₀) (𝓝 0)) := by
  have hc := sc_continuousOn_MI (L := L) hab hb (fun ω hω r hr => (hbound ω hω r hr).1)
  have hcx : ∀ ω ∈ S, ContinuousOn (sc_MI M Q e L ω) (Ioi b) := fun ω hω =>
    hc.comp (f := fun r : ℝ => (ω, r))
      (continuous_const.prodMk continuous_id).continuousOn (fun r hr => ⟨hω, hr⟩)
  have hbd : ∀ ω ∈ S, ∀ r ∈ Ioi b, ‖sc_MI M Q e L ω r‖ ≤ (4 * C) / r ^ 2 := by
    intro ω hω r hr
    calc ‖sc_MI M Q e L ω r‖ ≤ 4 * errCoeff M Q e ω L r := sc_norm_MI_le _ _ _ _ _ _
      _ ≤ 4 * (C / r ^ 2) := mul_le_mul_of_nonneg_left (hbound ω hω r hr).2 (by norm_num)
      _ = _ := by ring
  have hi : ∀ t ∈ Ioi b, IntegrableOn (fun x : ℝ => (4 * C) / x ^ 2) (Ioi t) := by
    intro t ht
    have ht0 := hb.trans ht
    exact integrableOn_Ioi_of_abs_le_div_sq (C := |4 * C|) ht0
      (continuousOn_const.div (continuousOn_id.pow 2) (fun r hr =>
        pow_ne_zero 2 (ht0.trans_le hr).ne')) (fun r hr => by
          rw [abs_div, abs_of_nonneg (sq_nonneg r)])
  constructor
  · intro ω hω t ht
    have hm : AEStronglyMeasurable (fun x => ‖sc_MI M Q e L ω x‖)
        (volume.restrict (Ioi t)) :=
      (((hcx ω hω).mono (Ioi_subset_Ioi ht.le)).norm).aestronglyMeasurable measurableSet_Ioi
    refine (hi t ht).mono' hm ((ae_restrict_iff' measurableSet_Ioi).2 ?_)
    exact Eventually.of_forall fun x hx => by
      rw [norm_norm]
      exact hbd ω hω x (ht.trans hx)
  · intro ω₀ hω₀ t ht
    refine ODE.tendsto_integral_norm_sub_of_dominated measurableSet_Ioi ?_
      (((hcx ω₀ hω₀).mono (Ioi_subset_Ioi ht.le)).aestronglyMeasurable measurableSet_Ioi)
      ?_ (fun x hx => hbd ω₀ hω₀ x (ht.trans hx)) (hi t ht) ?_
    · filter_upwards [self_mem_nhdsWithin] with ω hω
      exact ((hcx ω hω).mono (Ioi_subset_Ioi ht.le)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [self_mem_nhdsWithin] with ω hω
      exact fun x hx => hbd ω hω x (ht.trans hx)
    · intro x hx
      exact (hc.comp (f := fun ω : ℝ => (ω, x)) (continuous_id.prodMk continuous_const).continuousOn
        (fun ω hω => ⟨hω, ht.trans hx⟩) ω₀ hω₀).tendsto

end ModeStability.AllAngular

end
