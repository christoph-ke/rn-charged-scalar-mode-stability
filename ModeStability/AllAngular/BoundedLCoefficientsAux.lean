module

public import Mathlib
public import ModeStability.AllAngular.UniformConstant
public import ModeStability.AllAngular.TurningPointGeometry

/-!
# Coefficient compactness for the bounded angular regime

Source: the all-angular research notes in preparation, Proposition 6.1,
and (3.5) on p. 4. All coefficients here are functions of the exterior radius.
-/

public section

open Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-- The nonnegative phase frequency, extended by zero across the barrier. -/
@[expose] noncomputable def boundedLPhaseFrequency (M Q e ω L r : ℝ) : ℝ :=
  normalizationG M Q e ω r ^ 2 * Real.sqrt (max (radialK e ω r ^ 2 - L * delta M Q r) 0)

/-- The multiplier coefficient, extended by zero off the allowed set. -/
@[expose] noncomputable def boundedLGamma (M Q e ω L r : ℝ) : ℝ :=
  if L * delta M Q r < radialK e ω r ^ 2 then
    effectiveK M Q e ω L r /
      xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r
  else 0

/-- The local bulk weight, with weight one on the barrier and its endpoints. -/
@[expose] noncomputable def boundedLWeight (M Q e ω L r : ℝ) : ℝ :=
  if L * delta M Q r < radialK e ω r ^ 2 then
    (2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2 -
      effectiveK M Q e ω L r * xDeriv M Q (normalizationG M Q e ω)
        (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) r) /
      xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2
  else 1

/-- Continuity of the gauge at every exterior point, including extremality. -/
theorem boundedL_continuousAt_g {M Q e ω r : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hr : outerHorizon M Q < r) : ContinuousAt (normalizationG M Q e ω) r := by
  obtain ⟨c, hd, -, -⟩ := NormalizationFacts.gauge_facts (e := e) (ω := ω) hM hQ hr
  exact hd.self_of_nhds.continuousAt

/-- Continuity of the strictly positive scalar denominator in the gamma bound. -/
theorem boundedL_continuousAt_H {M Q e ω r : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hr : outerHorizon M Q < r) : ContinuousAt (scalarH M Q e ω) r := by
  have hh := (NormalizationFacts.hasDerivAt_staticSolutionAA hM hQ hr).continuousAt
  have hn := (NormalizationFacts.staticSolutionAA_pos hM hr).ne'
  have hc : ContinuousAt (scalarChi M Q e ω) r := by
    unfold scalarChi
    split_ifs
    · exact continuousAt_const
    · exact continuousAt_const.div hh hn
  unfold scalarH
  exact ((CoefficientIdentities.hasDerivAt_delta M Q r).continuousAt.mul
    (by fun_prop)).sub ((continuousAt_const.mul hc).mul
      (CoefficientIdentities.hasDerivAt_radialK e ω r).continuousAt)

/-- Identity (3.5) for the actual normalized coefficient. -/
theorem boundedL_xDeriv_formula {M Q e ω L r : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hL : 0 ≤ L) (hr : outerHorizon M Q < r)
    (hallow : L * delta M Q r < radialK e ω r ^ 2) :
    xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r =
      normalizationG M Q e ω r ^ 4 /
        Real.sqrt (1 - L * delta M Q r / radialK e ω r ^ 2) *
      ((1 - L * delta M Q r / radialK e ω r ^ 2) * scalarH M Q e ω r +
        L * delta M Q r / radialK e ω r ^ 2 *
          (delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r)) := by
  obtain ⟨c, hd, hg, hc⟩ := NormalizationFacts.gauge_facts (e := e) (ω := ω) hM hQ hr
  have ht := (NormalizationFacts.xDeriv_khat hQ hL
    (NormalizationFacts.delta_pos_of_outerHorizon_lt hr) hg hallow hd).1
  simpa only [← NormalizationFacts.effectiveK_eq_effectiveKAux, hc, scalarH, scalarChi] using ht

/-- Joint continuity in angular momentum and radius on the allowed exterior.
In particular it applies on the compact rectangle used in Proposition 6.1. -/
theorem boundedL_joint_continuous_xDeriv {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) :
    ContinuousOn (fun p : ℝ × ℝ =>
      xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω p.1) p.2)
      {p | 0 ≤ p.1 ∧ outerHorizon M Q < p.2 ∧
        p.1 * delta M Q p.2 < radialK e ω p.2 ^ 2} := by
  intro p hp
  have hg := (boundedL_continuousAt_g (e := e) (ω := ω) hM hQ hp.2.1).comp continuousAt_snd
  have hH := (boundedL_continuousAt_H (e := e) (ω := ω) hM hQ hp.2.1).comp continuousAt_snd
  have hK : ContinuousAt (fun p : ℝ × ℝ => radialK e ω p.2) p := by
    unfold radialK
    fun_prop
  have hD : ContinuousAt (fun p : ℝ × ℝ => delta M Q p.2) p := by
    unfold delta
    fun_prop
  have hd := NormalizationFacts.delta_pos_of_outerHorizon_lt hp.2.1
  have hks : 0 < radialK e ω p.2 ^ 2 :=
    lt_of_le_of_lt (mul_nonneg hp.1 hd.le) hp.2.2
  have ht := (continuousAt_fst.mul hD).div (hK.pow 2) hks.ne'
  have hq : 0 < 1 - p.1 * delta M Q p.2 / radialK e ω p.2 ^ 2 :=
    sub_pos.2 ((div_lt_one hks).2 hp.2.2)
  have hz : ContinuousAt (fun p : ℝ × ℝ => p.2 - M) p := by fun_prop
  have hkp : ContinuousAt (fun p : ℝ × ℝ => 2 * ω * p.2 - e) p := by fun_prop
  have hcont : ContinuousAt (fun p : ℝ × ℝ =>
      normalizationG M Q e ω p.2 ^ 4 /
        Real.sqrt (1 - p.1 * delta M Q p.2 / radialK e ω p.2 ^ 2) *
      ((1 - p.1 * delta M Q p.2 / radialK e ω p.2 ^ 2) * scalarH M Q e ω p.2 +
        p.1 * delta M Q p.2 / radialK e ω p.2 ^ 2 *
          (delta M Q p.2 * (2 * ω * p.2 - e) - (p.2 - M) * radialK e ω p.2))) p :=
    ((hg.pow 4).div ((continuousAt_const.sub ht).sqrt) (Real.sqrt_pos.2 hq).ne').mul
      (((continuousAt_const.sub ht).mul hH).add
        (ht.mul ((hD.mul hkp).sub (hz.mul hK))))
  exact hcont.continuousWithinAt.congr
    (fun q hq => (boundedL_xDeriv_formula hM hQ hq.1 hq.2.1 hq.2.2))
    (boundedL_xDeriv_formula hM hQ hp.1 hp.2.1 hp.2.2)

private theorem bc_gamma_alg {G H T τ q A : ℝ} (hG : 0 < G) (hH : 0 < H)
    (hT : 0 ≤ T) (hτ : 0 ≤ τ) (hτ1 : τ < 1) (hq : 0 < q)
    (hq2 : q ^ 2 = 1 - τ) (hA : 0 ≤ A) :
    G ^ 2 * A * q / (G ^ 4 / q * ((1 - τ) * H + τ * T)) ≤ A / (G ^ 2 * H) := by
  have hS : 0 < (1 - τ) * H + τ * T :=
    add_pos_of_pos_of_nonneg (mul_pos (sub_pos.2 hτ1) hH) (mul_nonneg hτ hT)
  apply (div_le_div_iff₀ (mul_pos (div_pos (pow_pos hG 4) hq) hS)
    (mul_pos (pow_pos hG 2) hH)).2
  have he : G ^ 4 / q * ((1 - τ) * H + τ * T) =
      G ^ 4 * ((1 - τ) * H + τ * T) / q := by ring
  rw [he, ← mul_div_assoc]
  apply (le_div_iff₀ hq).2
  calc
    _ = G ^ 4 * A * H * q ^ 2 := by ring
    _ = G ^ 4 * A * H * (1 - τ) := by rw [hq2]
    _ ≤ _ := by
      nlinarith only [mul_nonneg (mul_nonneg hA (pow_nonneg hG.le 4)) (mul_nonneg hτ hT)]

/-- The cancellation in (3.5) controls gamma even arbitrarily near a turning point. -/
theorem boundedL_gamma_le {M Q e ω L r : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hω : 0 < ω) (ha : outerHorizon M Q < e / ω) (hL : 0 ≤ L)
    (hr : outerHorizon M Q < r) :
    |boundedLGamma M Q e ω L r| ≤
      |radialK e ω r| / (normalizationG M Q e ω r ^ 2 * scalarH M Q e ω r) := by
  have hH : 0 < scalarH M Q e ω r :=
    (scalar_positivity M Q e ω hM hQ hω (e / ω) rfl ha r hr).1
  obtain ⟨c, hd, hg, hc⟩ := NormalizationFacts.gauge_facts (e := e) (ω := ω) hM hQ hr
  unfold boundedLGamma
  split_ifs with hallow
  · have hD := NormalizationFacts.delta_pos_of_outerHorizon_lt hr
    have hks : 0 < radialK e ω r ^ 2 := lt_of_le_of_lt (mul_nonneg hL hD.le) hallow
    have hτ0 := div_nonneg (mul_nonneg hL hD.le) hks.le
    have hτ1 := (div_lt_one hks).2 hallow
    have hq := Real.sqrt_pos.2 (sub_pos.2 hτ1)
    have hT : 0 ≤ delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r := by
      have ht := (common_geometry M Q e ω hM hQ hω (e / ω) rfl ha r hr).1
      exact (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)).trans ht.le
    have hkx := (angular_positivity M Q e ω L hM hQ hω hL (e / ω) rfl ha r hr hallow).1
    have hrad : Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r) =
        |radialK e ω r| * Real.sqrt (1 - L * delta M Q r / radialK e ω r ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
      congr 1
      have hn : radialK e ω r ≠ 0 := by intro hn; simp [hn] at hks
      field_simp [hn]
    have habs : |effectiveK M Q e ω L r| = normalizationG M Q e ω r ^ 2 *
        |radialK e ω r| * Real.sqrt (1 - L * delta M Q r / radialK e ω r ^ 2) := by
      have hsign : |(SignType.sign (radialK e ω r) : ℝ)| = 1 := by
        have hn : radialK e ω r ≠ 0 := by intro hn; simp [hn] at hks
        rcases hn.lt_or_gt with hn | hn <;> simp [sign_neg, sign_pos, hn]
      simp only [effectiveK, abs_mul, hsign, one_mul,
        abs_of_nonneg (sq_nonneg (normalizationG M Q e ω r)),
        abs_of_nonneg (Real.sqrt_nonneg _), hrad, abs_abs]
      ring
    rw [abs_div, abs_of_pos hkx, habs, boundedL_xDeriv_formula hM hQ hL hr hallow]
    exact bc_gamma_alg hg hH hT hτ0 hτ1 hq (Real.sq_sqrt (sub_pos.2 hτ1).le) (abs_nonneg _)
  · simp only [abs_zero]
    positivity

/-- The local bulk coefficient has the fixed positive floor (4.7). -/
theorem boundedL_weight_ge {M Q e ω L r : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hω : 0 < ω) (ha : outerHorizon M Q < e / ω) (hL : 0 ≤ L)
    (hr : outerHorizon M Q < r) :
    min (uniformConstant M Q e ω) 1 ≤ boundedLWeight M Q e ω L r := by
  unfold boundedLWeight
  split_ifs with hallow
  · exact (min_le_left _ _).trans ((uniformConstant_spec hM hQ hω ha).2.2.2 L hL r hr hallow)
  · exact min_le_right _ _

end ModeStability.AllAngular

end
