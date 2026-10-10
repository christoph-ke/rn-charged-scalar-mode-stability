module

public import Mathlib
public import ModeStability.AllAngular.BoundedLCoefficientsAux

/-!
# Uniform bounded-L coefficients for Proposition 6.1

Source: the all-angular research notes in preparation (p. 8).
These radius-space estimates are independent of the solution and uniform for
`0 ≤ L ≤ L₀`. Coordinate transport is a separate application step.
-/

public section

open Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

private theorem bc_horizon_K_neg {M Q e ω : ℝ} (hM : 0 < M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) : radialK e ω (outerHorizon M Q) < 0 := by
  have hap : 0 < outerHorizon M Q := by
    unfold outerHorizon
    linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
  have he : ω * outerHorizon M Q < e := by simpa only [mul_comm] using (lt_div_iff₀ hω).1 ha
  unfold radialK
  nlinarith [mul_pos hap (sub_pos.2 he)]

/-- Existence of the infinity-side root; at zero angular momentum it is corotation. -/
theorem boundedL_exists_outer_root {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hω : 0 < ω) (ha : outerHorizon M Q < e / ω) (hL : 0 ≤ L) :
    ∃ r, outerHorizon M Q < r ∧ e / ω ≤ r ∧
      radialK e ω r / Real.sqrt (delta M Q r) = Real.sqrt L := by
  rcases hL.eq_or_lt with hzero | hpos
  · refine ⟨e / ω, ha, le_rfl, ?_⟩
    rw [← hzero, Real.sqrt_zero, K_div_sqrt_delta_corotation M Q e hω.ne']
  · obtain ⟨r₁, r₂, hr₁, h₁, h₂, he₁, he₂, rest⟩ :=
      exists_turning_points hM hQ hω hpos (bc_horizon_K_neg hM hω ha)
    exact ⟨r₂, ha.trans h₂, h₂.le, he₂⟩

/-- Monotonicity of the outer roots, expressed by their defining equation.
This also covers `L = 0`, with root `r₀ = e/ω`. -/
theorem boundedL_outer_root_le {M Q e ω L L₀ r₂ r₂₀ : ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) (hLmax : L ≤ L₀)
    (hr : outerHorizon M Q < r₂) (hr₀ : outerHorizon M Q < r₂₀)
    (he : radialK e ω r₂ / Real.sqrt (delta M Q r₂) = Real.sqrt L)
    (he₀ : radialK e ω r₂₀ / Real.sqrt (delta M Q r₂₀) = Real.sqrt L₀) : r₂ ≤ r₂₀ := by
  have hm := strictMonoOn_K_div_sqrt_delta hM hQ hω (bc_horizon_K_neg hM hω ha)
  by_contra hn
  have ht := hm hr₀ hr (lt_of_not_ge hn)
  dsimp only at ht
  rw [he, he₀] at ht
  exact (not_lt_of_ge (Real.sqrt_le_sqrt hLmax)) ht

/-- Every radius beyond the largest outer root is allowed for the entire range. -/
theorem boundedL_allowed_beyond_root {M Q e ω L L₀ r r₂₀ : ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) (hL : 0 ≤ L) (hLmax : L ≤ L₀)
    (hr₀ : outerHorizon M Q < r₂₀)
    (he₀ : radialK e ω r₂₀ / Real.sqrt (delta M Q r₂₀) = Real.sqrt L₀)
    (hr : r₂₀ < r) : outerHorizon M Q < r ∧
      L * delta M Q r < radialK e ω r ^ 2 ∧ 0 < radialK e ω r := by
  have har := hr₀.trans hr
  have hd := NormalizationFacts.delta_pos_of_outerHorizon_lt har
  have hs := Real.sqrt_pos.2 hd
  have hm := strictMonoOn_K_div_sqrt_delta hM hQ hω (bc_horizon_K_neg hM hω ha)
  have ht := hm hr₀ har hr
  dsimp only at ht
  rw [he₀] at ht
  have hf : Real.sqrt L < radialK e ω r / Real.sqrt (delta M Q r) :=
    (Real.sqrt_le_sqrt hLmax).trans_lt ht
  have hf0 : 0 < radialK e ω r / Real.sqrt (delta M Q r) :=
    (Real.sqrt_nonneg L).trans_lt hf
  have hk := (div_pos_iff_of_pos_right hs).1 hf0
  have hmul := (lt_div_iff₀ hs).1 hf
  have hsq := (sq_lt_sq₀ (mul_nonneg (Real.sqrt_nonneg L) hs.le) hk.le).2 hmul
  rw [mul_pow, Real.sq_sqrt hL, Real.sq_sqrt hd.le] at hsq
  exact ⟨har, hsq, hk⟩

/-- A source-free interval beyond every outer root can be fixed independently of L. -/
theorem boundedL_exists_test_interval {M Q e ω L₀ ρ₂ : ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) (hL₀ : 0 ≤ L₀) :
    ∃ r₂₀ j₁ j₂, outerHorizon M Q < r₂₀ ∧
      radialK e ω r₂₀ / Real.sqrt (delta M Q r₂₀) = Real.sqrt L₀ ∧
      max ρ₂ r₂₀ < j₁ ∧ j₁ < j₂ ∧
      ∀ L ∈ Icc 0 L₀, ∀ r ∈ Icc j₁ j₂,
        outerHorizon M Q < r ∧ L * delta M Q r < radialK e ω r ^ 2 ∧
          0 < radialK e ω r := by
  obtain ⟨r₂₀, hr₀, -, he₀⟩ := boundedL_exists_outer_root hM hQ hω ha hL₀
  refine ⟨r₂₀, max ρ₂ r₂₀ + 1, max ρ₂ r₂₀ + 2, hr₀, he₀,
    by linarith, by linarith, ?_⟩
  intro L hL r hr
  exact boundedL_allowed_beyond_root hM hQ hω ha hL.1 hL.2 hr₀ he₀
    (by have := le_max_right ρ₂ r₂₀; linarith [hr.1])

/-- The phase frequency is bounded above by the scalar frequency for every L ≥ 0. -/
theorem boundedL_phase_le {M Q e ω L r : ℝ} (hL : 0 ≤ L)
    (hr : outerHorizon M Q < r) :
    0 ≤ boundedLPhaseFrequency M Q e ω L r ∧
      boundedLPhaseFrequency M Q e ω L r ≤ normalizationG M Q e ω r ^ 2 * |radialK e ω r| := by
  have hd := NormalizationFacts.delta_pos_of_outerHorizon_lt hr
  constructor
  · unfold boundedLPhaseFrequency
    positivity
  · unfold boundedLPhaseFrequency
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    exact max_le (sub_le_self _ (mul_nonneg hL hd.le)) (sq_nonneg _)

/-- The phase frequency vanishes throughout the forbidden region and at its endpoints. -/
theorem boundedL_phase_eq_zero {M Q e ω L r : ℝ}
    (hforbid : radialK e ω r ^ 2 ≤ L * delta M Q r) :
    boundedLPhaseFrequency M Q e ω L r = 0 := by
  simp only [boundedLPhaseFrequency, max_eq_right (sub_nonpos.2 hforbid),
    Real.sqrt_zero, mul_zero]

/-- On the allowed set the phase frequency is exactly the absolute effective frequency. -/
theorem boundedL_phase_eq_abs {M Q e ω L r : ℝ} (hL : 0 ≤ L)
    (hr : outerHorizon M Q < r) (hallow : L * delta M Q r < radialK e ω r ^ 2) :
    boundedLPhaseFrequency M Q e ω L r = |effectiveK M Q e ω L r| := by
  have hks : 0 < radialK e ω r ^ 2 := lt_of_le_of_lt
    (mul_nonneg hL (NormalizationFacts.delta_pos_of_outerHorizon_lt hr).le) hallow
  have hn : radialK e ω r ≠ 0 := by intro hn; simp [hn] at hks
  have hs : |(SignType.sign (radialK e ω r) : ℝ)| = 1 := by
    rcases hn.lt_or_gt with hn | hn <;> simp [sign_neg, sign_pos, hn]
  simp only [boundedLPhaseFrequency, effectiveK, max_eq_left (sub_pos.2 hallow).le,
    abs_mul, hs, one_mul,
    abs_of_nonneg (sq_nonneg (normalizationG M Q e ω r)),
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- A compact radius interval bounds W uniformly, with no upper restriction on L. -/
theorem boundedL_phase_uniform {M Q e ω : ℝ} {s : Set ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hs : IsCompact s)
    (hex : s ⊆ Ioi (outerHorizon M Q)) :
    ∃ K₁, 0 ≤ K₁ ∧ ∀ L, 0 ≤ L → ∀ r ∈ s,
      boundedLPhaseFrequency M Q e ω L r ≤ K₁ := by
  have hc : ContinuousOn (fun r => normalizationG M Q e ω r ^ 2 * |radialK e ω r|) s := by
    intro r hr
    exact (((boundedL_continuousAt_g (e := e) (ω := ω) hM hQ (hex hr)).pow 2).mul
      (CoefficientIdentities.hasDerivAt_radialK e ω r).continuousAt.abs).continuousWithinAt
  by_cases hn : s.Nonempty
  · obtain ⟨r, hr, hmax⟩ := hs.exists_isMaxOn hn hc
    refine ⟨normalizationG M Q e ω r ^ 2 * |radialK e ω r|, by positivity, ?_⟩
    intro L hL t ht
    exact (boundedL_phase_le hL (hex ht)).2.trans (hmax ht)
  · refine ⟨0, le_rfl, ?_⟩
    intro L hL r hr
    exact False.elim (hn ⟨r, hr⟩)

/-- Gamma, extended by zero on the forbidden region, is uniformly bounded on any
compact exterior set, independently of the angular cutoff. -/
theorem boundedL_gamma_uniform {M Q e ω : ℝ} {s : Set ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) (hs : IsCompact s)
    (hex : s ⊆ Ioi (outerHorizon M Q)) :
    ∃ Γ, 0 ≤ Γ ∧ ∀ L, 0 ≤ L → ∀ r ∈ s, |boundedLGamma M Q e ω L r| ≤ Γ := by
  have hc : ContinuousOn (fun r => |radialK e ω r| /
      (normalizationG M Q e ω r ^ 2 * scalarH M Q e ω r)) s := by
    intro r hr
    have hH : 0 < scalarH M Q e ω r :=
      (scalar_positivity M Q e ω hM hQ hω (e / ω) rfl ha r (hex hr)).1
    obtain ⟨c, -, hg, -⟩ := NormalizationFacts.gauge_facts (e := e) (ω := ω) hM hQ (hex hr)
    exact ((CoefficientIdentities.hasDerivAt_radialK e ω r).continuousAt.abs.div
      (((boundedL_continuousAt_g (e := e) (ω := ω) hM hQ (hex hr)).pow 2).mul
        (boundedL_continuousAt_H (e := e) (ω := ω) hM hQ (hex hr)))
      (mul_pos (pow_pos hg 2) hH).ne').continuousWithinAt
  by_cases hn : s.Nonempty
  · obtain ⟨r, hr, hmax⟩ := hs.exists_isMaxOn hn hc
    refine ⟨|radialK e ω r| / (normalizationG M Q e ω r ^ 2 * scalarH M Q e ω r), ?_, ?_⟩
    · have hH : 0 < scalarH M Q e ω r :=
        (scalar_positivity M Q e ω hM hQ hω (e / ω) rfl ha r (hex hr)).1
      positivity
    · intro L hL t ht
      exact (boundedL_gamma_le hM hQ hω ha hL (hex ht)).trans (hmax ht)
  · refine ⟨0, le_rfl, ?_⟩
    intro L hL r hr
    exact False.elim (hn ⟨r, hr⟩)

/-- Joint compactness gives a strictly positive uniform lower bound for k̂_x;
the same interval bounds |k̂| uniformly. -/
theorem boundedL_test_uniform {M Q e ω L₀ j₁ j₂ : ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) (hL₀ : 0 ≤ L₀) (hj : j₁ ≤ j₂)
    (hex : Icc j₁ j₂ ⊆ Ioi (outerHorizon M Q))
    (hallow : ∀ L ∈ Icc 0 L₀, ∀ r ∈ Icc j₁ j₂,
      L * delta M Q r < radialK e ω r ^ 2) :
    ∃ K₀ κ₁, 0 ≤ K₀ ∧ 0 < κ₁ ∧ ∀ L ∈ Icc 0 L₀, ∀ r ∈ Icc j₁ j₂,
      |effectiveK M Q e ω L r| ≤ K₀ ∧
        κ₁ ≤ xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r := by
  obtain ⟨K₀, hK₀, hbound⟩ := boundedL_phase_uniform (e := e) (ω := ω) hM hQ isCompact_Icc hex
  let s := Icc (0 : ℝ) L₀ ×ˢ Icc j₁ j₂
  have hs : IsCompact s := isCompact_Icc.prod isCompact_Icc
  have hn : s.Nonempty := ⟨(0, j₁), ⟨⟨le_rfl, hL₀⟩, ⟨le_rfl, hj⟩⟩⟩
  have hsub : s ⊆ {p : ℝ × ℝ | 0 ≤ p.1 ∧ outerHorizon M Q < p.2 ∧
      p.1 * delta M Q p.2 < radialK e ω p.2 ^ 2} :=
    fun p hp => ⟨hp.1.1, hex hp.2, hallow p.1 hp.1 p.2 hp.2⟩
  obtain ⟨p, hp, hmin⟩ := hs.exists_isMinOn hn
    ((boundedL_joint_continuous_xDeriv (e := e) (ω := ω) hM hQ).mono hsub)
  refine ⟨K₀, xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω p.1) p.2,
    hK₀, ?_, ?_⟩
  · exact (angular_positivity M Q e ω p.1 hM hQ hω hp.1.1 (e / ω) rfl ha
      p.2 (hex hp.2) (hallow p.1 hp.1 p.2 hp.2)).1
  · intro L hL r hr
    constructor
    · rw [← boundedL_phase_eq_abs hL.1 (hex hr) (hallow L hL r hr)]
      exact hbound L hL.1 r hr
    · exact hmin (show (L, r) ∈ s from ⟨hL, hr⟩)

/-- A fixed C¹ cutoff, nonnegative and zero at both endpoints. -/
@[expose] noncomputable def boundedLCutoff (j₁ j₂ r : ℝ) : ℝ :=
  (r - j₁) ^ 2 * (j₂ - r) ^ 2

private theorem bc_cutoff_deriv (j₁ j₂ r : ℝ) :
    HasDerivAt (boundedLCutoff j₁ j₂)
      (2 * (r - j₁) * (j₂ - r) ^ 2 - 2 * (r - j₁) ^ 2 * (j₂ - r)) r := by
  convert (((hasDerivAt_id' r).sub_const j₁).fun_pow 2).mul
    (((hasDerivAt_const r j₂).sub (hasDerivAt_id' r)).fun_pow 2) using 1
  · rfl
  · dsimp
    ring

/-- All cutoff regularity required by `boundedL_estimate`. -/
theorem boundedL_cutoff_spec (j₁ j₂ : ℝ) :
    (∀ r, HasDerivAt (boundedLCutoff j₁ j₂) (deriv (boundedLCutoff j₁ j₂) r) r) ∧
      Continuous (deriv (boundedLCutoff j₁ j₂)) ∧
      boundedLCutoff j₁ j₂ j₁ = 0 ∧ boundedLCutoff j₁ j₂ j₂ = 0 ∧
      ∀ r, 0 ≤ boundedLCutoff j₁ j₂ r := by
  refine ⟨fun r => (bc_cutoff_deriv j₁ j₂ r).differentiableAt.hasDerivAt, ?_,
    by simp [boundedLCutoff], by simp [boundedLCutoff], fun r => by
      unfold boundedLCutoff; positivity⟩
  have he : deriv (boundedLCutoff j₁ j₂) = fun r =>
      2 * (r - j₁) * (j₂ - r) ^ 2 - 2 * (r - j₁) ^ 2 * (j₂ - r) :=
    funext fun r => (bc_cutoff_deriv j₁ j₂ r).deriv
  rw [he]
  fun_prop

/-- The fixed polynomial cutoff has strictly positive mass on a nondegenerate interval. -/
theorem boundedL_cutoff_integral_pos {j₁ j₂ : ℝ} (hj : j₁ < j₂) :
    0 < ∫ r in Icc j₁ j₂, boundedLCutoff j₁ j₂ r := by
  have hc : Continuous (boundedLCutoff j₁ j₂) := by unfold boundedLCutoff; fun_prop
  apply (integral_pos_iff_support_of_nonneg (fun r => (boundedL_cutoff_spec j₁ j₂).2.2.2.2 r)
    hc.continuousOn.integrableOn_Icc).2
  have hsub : Ioo j₁ j₂ ⊆ Function.support (boundedLCutoff j₁ j₂) := by
    intro r hr
    exact (mul_pos (pow_pos (sub_pos.2 hr.1) 2) (pow_pos (sub_pos.2 hr.2) 2)).ne'
  apply lt_of_lt_of_le _ (measure_mono hsub)
  rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Icc_self,
    Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (sub_pos.2 hj)

/-- The positive derivative floor supplies the mass and sign hypotheses of (6.4),
with a cutoff and positive mass constant independent of L. -/
theorem boundedL_test_mass {M Q e ω L₀ j₁ j₂ κ₁ : ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hj : j₁ < j₂) (hκ₁ : 0 < κ₁)
    (hex : Icc j₁ j₂ ⊆ Ioi (outerHorizon M Q))
    (hallow : ∀ L ∈ Icc 0 L₀, ∀ r ∈ Icc j₁ j₂,
      L * delta M Q r < radialK e ω r ^ 2)
    (hlow : ∀ L ∈ Icc 0 L₀, ∀ r ∈ Icc j₁ j₂,
      κ₁ ≤ xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r) :
    ∃ κ, 0 < κ ∧ ∀ L ∈ Icc 0 L₀,
      (∀ r ∈ Icc j₁ j₂, 0 ≤
        xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r * boundedLCutoff j₁ j₂ r) ∧
      κ ≤ ∫ r in Icc j₁ j₂,
        xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r * boundedLCutoff j₁ j₂ r := by
  have hφ : Continuous (boundedLCutoff j₁ j₂) := by unfold boundedLCutoff; fun_prop
  refine ⟨κ₁ * (∫ r in Icc j₁ j₂, boundedLCutoff j₁ j₂ r),
    mul_pos hκ₁ (boundedL_cutoff_integral_pos hj), ?_⟩
  intro L hL
  have hk : ContinuousOn (fun r =>
      xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r) (Icc j₁ j₂) :=
    (boundedL_joint_continuous_xDeriv (e := e) (ω := ω) hM hQ).comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun r hr => ⟨hL.1, hex hr, hallow L hL r hr⟩)
  constructor
  · intro r hr
    exact mul_nonneg (hκ₁.le.trans (hlow L hL r hr))
      ((boundedL_cutoff_spec j₁ j₂).2.2.2.2 r)
  · rw [← integral_const_mul]
    exact setIntegral_mono_on (hφ.continuousOn.integrableOn_Icc.const_mul κ₁)
      (hk.mul hφ.continuousOn).integrableOn_Icc measurableSet_Icc
      (fun r hr => mul_le_mul_of_nonneg_right (hlow L hL r hr)
        ((boundedL_cutoff_spec j₁ j₂).2.2.2.2 r))

/-- Radius regularity on an infinity-side allowed interval. The derivative
continuity follows from (3.5) and `∂ₓ = Δg²∂ᵣ`. -/
theorem boundedL_test_regular {M Q e ω L j₁ j₂ : ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hL : 0 ≤ L)
    (hex : Icc j₁ j₂ ⊆ Ioi (outerHorizon M Q))
    (hallow : ∀ r ∈ Icc j₁ j₂, L * delta M Q r < radialK e ω r ^ 2)
    (hK : ∀ r ∈ Icc j₁ j₂, 0 < radialK e ω r) :
    ContinuousOn (effectiveK M Q e ω L) (Icc j₁ j₂) ∧
      ContinuousOn (deriv (effectiveK M Q e ω L)) (Icc j₁ j₂) := by
  have hg : ContinuousOn (normalizationG M Q e ω) (Icc j₁ j₂) :=
    fun r hr => (boundedL_continuousAt_g hM hQ (hex hr)).continuousWithinAt
  have hD : Continuous (delta M Q) := by unfold delta; fun_prop
  have hRad : Continuous (radialK e ω) := by unfold radialK; fun_prop
  have hkx : ContinuousOn (fun r =>
      xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r) (Icc j₁ j₂) :=
    (boundedL_joint_continuous_xDeriv (e := e) (ω := ω) hM hQ).comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun r hr => ⟨hL, hex hr, hallow r hr⟩)
  constructor
  · apply ((hg.pow 2).mul ((hRad.continuousOn.pow 2).sub
      ((continuousOn_const (c := L)).mul hD.continuousOn)).sqrt).congr
    intro r hr
    simp only [effectiveK, sign_pos (hK r hr), SignType.coe_one, one_mul,
      Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
  · apply (hkx.div (hD.continuousOn.mul (hg.pow 2)) (fun r hr => ?_)).congr
      (fun r hr => ?_)
    · obtain ⟨c, -, hp, -⟩ := NormalizationFacts.gauge_facts (e := e) (ω := ω)
        hM hQ (hex hr)
      exact (mul_pos (NormalizationFacts.delta_pos_of_outerHorizon_lt (hex hr))
        (pow_pos hp 2)).ne'
    · change deriv (effectiveK M Q e ω L) r =
        delta M Q r * normalizationG M Q e ω r ^ 2 * deriv (effectiveK M Q e ω L) r /
          (delta M Q r * normalizationG M Q e ω r ^ 2)
      have hd := (NormalizationFacts.delta_pos_of_outerHorizon_lt (hex hr)).ne'
      obtain ⟨c, -, hp, -⟩ := NormalizationFacts.gauge_facts (e := e) (ω := ω)
        hM hQ (hex hr)
      field_simp [hd, hp.ne']

/-- Complete radius-space coefficient package for the bounded angular part of
Proposition 6.1. The larger compact interval is `[ρ₁,j₂]`; the cutoff is fixed
by the chosen `J`. Every displayed constant is independent of L and U. -/
theorem boundedL_coefficients {M Q e ω L₀ ρ₁ ρ₂ : ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) (hL₀ : 0 ≤ L₀)
    (hρ₁ : outerHorizon M Q < ρ₁) (_hρ : ρ₁ ≤ ρ₂) :
    ∃ r₂₀ j₁ j₂ Γ K₀ K₁ κ₁ κ : ℝ,
      outerHorizon M Q < r₂₀ ∧
      radialK e ω r₂₀ / Real.sqrt (delta M Q r₂₀) = Real.sqrt L₀ ∧
      max ρ₂ r₂₀ < j₁ ∧ j₁ < j₂ ∧
      0 ≤ Γ ∧ 0 ≤ K₀ ∧ 0 ≤ K₁ ∧ 0 < κ₁ ∧ 0 < κ ∧
      ∀ L ∈ Icc 0 L₀,
        (∀ r ∈ Icc j₁ j₂, outerHorizon M Q < r ∧
          L * delta M Q r < radialK e ω r ^ 2 ∧ 0 < radialK e ω r) ∧
        (∀ r ∈ Icc j₁ j₂, |effectiveK M Q e ω L r| ≤ K₀ ∧
          κ₁ ≤ xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r) ∧
        (∀ r ∈ Icc j₁ j₂, 0 ≤
          xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r *
            boundedLCutoff j₁ j₂ r) ∧
        (κ ≤ ∫ r in Icc j₁ j₂,
          xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r *
            boundedLCutoff j₁ j₂ r) ∧
        (∀ r ∈ Icc ρ₁ ρ₂, |boundedLGamma M Q e ω L r| ≤ Γ) ∧
        (∀ r ∈ Icc ρ₁ j₂, boundedLPhaseFrequency M Q e ω L r ≤ K₁ ∧
          min (uniformConstant M Q e ω) 1 ≤ boundedLWeight M Q e ω L r) := by
  obtain ⟨r₂₀, j₁, j₂, hr₂₀, he₂₀, hj₁, hj, hJ⟩ :=
    boundedL_exists_test_interval (ρ₂ := ρ₂) hM hQ hω ha hL₀
  have hexJ : Icc j₁ j₂ ⊆ Ioi (outerHorizon M Q) := fun r hr =>
    (hJ 0 ⟨le_rfl, hL₀⟩ r hr).1
  have hallow : ∀ L ∈ Icc 0 L₀, ∀ r ∈ Icc j₁ j₂,
      L * delta M Q r < radialK e ω r ^ 2 := fun L hL r hr => (hJ L hL r hr).2.1
  obtain ⟨K₀, κ₁, hK₀, hκ₁, htest⟩ :=
    boundedL_test_uniform hM hQ hω ha hL₀ hj.le hexJ hallow
  obtain ⟨κ, hκ, hmass⟩ := boundedL_test_mass hM hQ hj hκ₁ hexJ hallow
    (fun L hL r hr => (htest L hL r hr).2)
  have hexI : Icc ρ₁ ρ₂ ⊆ Ioi (outerHorizon M Q) :=
    fun r hr => hρ₁.trans_le hr.1
  have hexI' : Icc ρ₁ j₂ ⊆ Ioi (outerHorizon M Q) :=
    fun r hr => hρ₁.trans_le hr.1
  obtain ⟨Γ, hΓ, hgamma⟩ := boundedL_gamma_uniform hM hQ hω ha isCompact_Icc hexI
  obtain ⟨K₁, hK₁, hphase⟩ :=
    boundedL_phase_uniform (e := e) (ω := ω) hM hQ isCompact_Icc hexI'
  refine ⟨r₂₀, j₁, j₂, Γ, K₀, K₁, κ₁, κ, hr₂₀, he₂₀, hj₁, hj,
    hΓ, hK₀, hK₁, hκ₁, hκ, ?_⟩
  intro L hL
  exact ⟨hJ L hL, htest L hL, (hmass L hL).1, (hmass L hL).2,
    hgamma L hL.1, fun r hr => ⟨hphase L hL.1 r hr,
      boundedL_weight_ge hM hQ hω ha hL.1 (hexI' hr)⟩⟩

end ModeStability.AllAngular

end
