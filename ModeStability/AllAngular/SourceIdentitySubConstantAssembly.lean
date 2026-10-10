module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentitySubConstantCurrent
public import ModeStability.AllAngular.SourceIdentitySubConstantRegions
public import ModeStability.AllAngular.SourceIdentityRGlobal
public import ModeStability.AllAngular.Prop61Multiplier
public import ModeStability.AllAngular.CoordinateIntervals

/-!
# The integrated radial identity in the constant system

Source: the all-angular research notes in preparation, identity (6.3).
The locally absolutely continuous currents are glued at their turning
points. Nonnegativity and their zero endpoint limits imply finite bulk
integrals; finiteness is a conclusion of the proof.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

open CoordinateCoefficients

/-- Allowed current, in the positive coordinate x = −h. -/
@[expose] noncomputable def ssc_J (M Q e ω L : ℝ) (R : ℝ → ℂ) (σ : ℝ) : ℝ → ℝ := fun r =>
  -(effectiveK M Q e ω L r / P61.khxR M Q e ω L r) *
    ‖P61.uxR M Q e ω R r + σ * effectiveK M Q e ω L r * I * P61.uR M Q e ω R r‖ ^ 2 -
    (P61.uxR M Q e ω R r * (starRingEnd ℂ) (P61.uR M Q e ω R r)).re

/-- The nonnegative allowed density, including dx/dr. -/
@[expose] noncomputable def ssc_b (M Q e ω L : ℝ) (R : ℝ → ℂ) (σ : ℝ) : ℝ → ℝ := fun r =>
  P61.akR M Q e ω L r *
    ‖P61.uxR M Q e ω R r + σ * effectiveK M Q e ω L r * I * P61.uR M Q e ω R r‖ ^ 2 *
    P61.wR M Q e ω r

/-- The forbidden density, including dx/dr. -/
@[expose] noncomputable def ssc_bm (M Q e ω L : ℝ) (R : ℝ → ℂ) : ℝ → ℝ := fun r =>
  (‖P61.uxR M Q e ω R r‖ ^ 2 + normalizationG M Q e ω r ^ 4 *
    (L * delta M Q r - radialK e ω r ^ 2) * ‖P61.uR M Q e ω R r‖ ^ 2) * P61.wR M Q e ω r

private theorem ssc_allowed_continuous {M Q e ω L ρ₁ ρ₂ σ : ℝ}
    (h : P61.Range17 M Q e ω ρ₁ ρ₂) (hQ : |Q| < M) (hN : e / ω < 2 * M)
    (hL : 0 ≤ L) (ha : outerHorizon M Q < e / ω)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI)
    {r : ℝ} (hr : outerHorizon M Q < r) (hp : L * delta M Q r < radialK e ω r ^ 2) :
    ContinuousAt (ssc_b M Q e ω L R σ) r := by
  have hk := (ssc_coefficient_props h.1 hQ h.2.2.2.1 hL ha hN hr hp).1
  have hx0 := (ssc_coefficient_props h.1 hQ h.2.2.2.1 hL ha hN hr hp).2.1
  have hd : ContDiffAt ℝ 1 (fun r => delta M Q r * normalizationG M Q e ω r ^ 2) r := by
    rw [NormalizationFacts.normalizationG_eq_one hN]
    simpa using (contDiff_delta M Q).contDiffAt.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hx : ContDiffAt ℝ 1 (P61.khxR M Q e ω L) r :=
    hd.mul (hk.derivWithin (m := 1) (by norm_num))
  have hxx : ContinuousAt (xDeriv M Q (normalizationG M Q e ω) (P61.khxR M Q e ω L)) r :=
    hd.continuousAt.mul (hx.derivWithin (m := 0) (by norm_num)).continuousAt
  have hak : ContinuousAt (P61.akR M Q e ω L) r :=
    ((continuousAt_const.mul (hx.continuousAt.pow 2)).sub
      (hk.continuousAt.mul hxx)).div (hx.continuousAt.pow 2) (pow_ne_zero 2 hx0.ne')
  have hU := (P61.uR_contDiffOn_one h.1 hP.2.2.1).continuousOn.continuousAt (Ioi_mem_nhds hr)
  have hV := (P61.uxR_continuousOn h.1 hP.2.2.1).continuousAt (Ioi_mem_nhds hr)
  have hw := (P61.wR_continuousOn (e := e) (ω := ω) h.1).continuousAt (Ioi_mem_nhds hr)
  have hkC := hk.continuousAt
  unfold ssc_b
  fun_prop

private theorem ssc_multiplier_horizon {M Q e ω L r : ℝ} {R : ℝ → ℂ}
    (hr : r ∈ P61.setAH M Q e ω L) :
    P61.multR M Q e ω L R r = P61.uR M Q e ω R r +
      2 * ((effectiveK M Q e ω L r / P61.khxR M Q e ω L r : ℝ) : ℂ) *
        (P61.uxR M Q e ω R r + (effectiveK M Q e ω L r : ℂ) * I * P61.uR M Q e ω R r) := by
  rw [P61.multR, ite_eq_left hr]

private theorem ssc_multiplier_infinity {M Q e ω L r : ℝ} {R : ℝ → ℂ}
    (hr : r ∈ P61.setAI M Q e ω L) :
    P61.multR M Q e ω L R r = P61.uR M Q e ω R r +
      2 * ((effectiveK M Q e ω L r / P61.khxR M Q e ω L r : ℝ) : ℂ) *
        (P61.uxR M Q e ω R r - (effectiveK M Q e ω L r : ℂ) * I * P61.uR M Q e ω R r) := by
  have hn : r ∉ P61.setAH M Q e ω L := fun hh => (not_lt.mpr hr.1.le) hh.2.1
  rw [P61.multR, ite_eq_right hn, ite_eq_left hr]

private theorem ssc_multiplier_forbidden {M Q e ω L r : ℝ} {R : ℝ → ℂ}
    (hr : r ∈ P61.setFb M Q e ω L) :
    P61.multR M Q e ω L R r = P61.uR M Q e ω R r := by
  have hnH : r ∉ P61.setAH M Q e ω L := fun hh => (not_lt.mpr hr.2) hh.2.2
  have hnI : r ∉ P61.setAI M Q e ω L := fun hh => (not_lt.mpr hr.2) hh.2
  rw [P61.multR, ite_eq_right hnH, ite_eq_right hnI]

/-- Zero physical endpoint limits imply the exact shared source identity. -/
theorem ssc_identity_of_limits {M Q e ω ρ₁ ρ₂ L : ℝ}
    (h : P61.Range17 M Q e ω ρ₁ ρ₂) (hQ : |Q| < M) (hN : e / ω < 2 * M)
    (hL : 0 ≤ L) {R S : ℝ → ℂ} {BH BI : ℂ}
    (hP : P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI)
    (hH : Tendsto (ssc_J M Q e ω L R 1) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (hI : Tendsto (ssc_J M Q e ω L R (-1)) atTop (𝓝 0)) :
    P61.SourceIdentityR M Q e ω L ρ₁ ρ₂ R S := by
  have ha0 : 0 < outerHorizon M Q := by
    unfold outerHorizon
    exact add_pos_of_pos_of_nonneg h.1 (Real.sqrt_nonneg _)
  have he := (lt_div_iff₀ ha0).mp h.2.2.2.2.1
  have hKa : radialK e ω (outerHorizon M Q) < 0 := radialK_neg_of_lt_corotation h.2.2.2.1 ha0
    ((lt_div_iff₀ h.2.2.2.1).mpr (by linarith))
  have ha := outerHorizon_lt_corotation h.1 h.2.2.2.1 hKa
  have hU := (P61.uR_contDiffOn_one h.1 hP.2.2.1).continuousOn
  have hV := P61.uxR_continuousOn h.1 hP.2.2.1
  obtain ⟨r₁, r₂, har₁, hr₁₂, hAH, hFb, hAI, hT₁, hT₂⟩ :=
    ssc_gluing_data h.1 hQ h.2.2.2.1 hL hKa hN hU hV
  let pair : ℝ → ℂ := fun r => P61.srcR M Q e ω S r *
    (starRingEnd ℂ) (P61.multR M Q e ω L R r) * (P61.wR M Q e ω r : ℂ)
  have hpair0 : ∀ r, r ∉ Icc ρ₁ ρ₂ → pair r = 0 := by
    intro r hr
    simp only [pair, P61.srcR, hP.1 r hr, mul_zero, zero_mul]
  have hpairOn : IntegrableOn pair (Icc ρ₁ ρ₂) := P61.integrableOn_src_mul_multR h hL hP
  have hpair : Integrable pair := hpairOn.integrable_of_forall_notMem_eq_zero hpair0
  have hsrc : Integrable (fun r => (pair r).re) := reCLM.integrable_comp hpair
  have hsrc0 : ∀ r ∉ Ioi (outerHorizon M Q), (pair r).re = 0 := by
    intro r hr
    rw [hpair0 r (fun hm => hr (h.2.2.2.2.2.1.trans_le hm.1))]
    rfl
  have hUdef : P61.uR M Q e ω R = fun r => R r / (normalizationG M Q e ω r : ℂ) := rfl
  have hR := hP.2.2.1.1
  have hS := fun b hb c hc => (hP.2.2.1.2 b hb c hc).1
  have hint := fun b hb c hc => (hP.2.2.1.2 b hb c hc).2
  let Jm := fun r => -(P61.uxR M Q e ω R r * (starRingEnd ℂ) (P61.uR M Q e ω R r)).re
  have h₁ : ∀ b c, b ≤ c → Icc b c ⊆ Ioo (outerHorizon M Q) r₁ →
      (∫ r in b..c, -ssc_b M Q e ω L R 1 r - (pair r).re) =
        ssc_J M Q e ω L R 1 c - ssc_J M Q e ω L R 1 b := by
    intro b c hbc hsub
    have hb := (hsub (left_mem_Icc.mpr hbc)).1
    have hc := (hsub (right_mem_Icc.mpr hbc)).1
    have hreg : ∀ r ∈ uIcc b c, r ∈ P61.setAH M Q e ω L := by
      intro r hr
      rw [hAH]
      exact hsub (by rwa [uIcc_of_le hbc] at hr)
    have ht := ssc_allowed_integral (σ := 1) h.1 hQ h.2.2.2.1 hL ha hN hb hc
      (fun r hr => (hreg r hr).2.2) (Or.inl rfl) hR hS hint
    convert ht using 1
    · apply intervalIntegral.integral_congr
      intro r hr
      simp only [ssc_b, pair, ssc_multiplier_horizon (hreg r hr), P61.akR,
        P61.khxR, P61.wR, P61.srcR, P61.uR, P61.uxR, ofReal_one, one_mul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [hUdef]
      simp only [Complex.ofReal_div]
      ring
    · dsimp only [ssc_J, P61.khxR, P61.uxR]
      rw [hUdef]
  have h₂ : ∀ b c, b ≤ c → Icc b c ⊆ Ioi r₂ →
      (∫ r in b..c, -ssc_b M Q e ω L R (-1) r - (pair r).re) =
        ssc_J M Q e ω L R (-1) c - ssc_J M Q e ω L R (-1) b := by
    intro b c hbc hsub
    have hb := (har₁.trans_le hr₁₂).trans (hsub (left_mem_Icc.mpr hbc))
    have hc := (har₁.trans_le hr₁₂).trans (hsub (right_mem_Icc.mpr hbc))
    have hreg : ∀ r ∈ uIcc b c, r ∈ P61.setAI M Q e ω L := by
      intro r hr
      rw [hAI]
      exact hsub (by rwa [uIcc_of_le hbc] at hr)
    have ht := ssc_allowed_integral (σ := -1) h.1 hQ h.2.2.2.1 hL ha hN hb hc
      (fun r hr => (hreg r hr).2) (Or.inr rfl) hR hS hint
    convert ht using 1
    · apply intervalIntegral.integral_congr
      intro r hr
      simp only [ssc_b, pair, ssc_multiplier_infinity (hreg r hr), P61.akR,
        P61.khxR, P61.wR, P61.srcR, P61.uR, P61.uxR, ofReal_neg, ofReal_one,
        neg_mul, one_mul, ← sub_eq_add_neg,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [hUdef]
      simp only [Complex.ofReal_div]
      ring
    · dsimp only [ssc_J, P61.khxR, P61.uxR]
      rw [hUdef]
  have hm : (∫ r in r₁..r₂, -ssc_bm M Q e ω L R r - (pair r).re) = Jm r₂ - Jm r₁ := by
    have ht := ssc_forbidden_integral hQ hN har₁ (har₁.trans_le hr₁₂) hR hS hint
    convert ht using 1
    · apply intervalIntegral.integral_congr
      intro r hr
      have hreg : r ∈ P61.setFb M Q e ω L := by rw [hFb]; rwa [uIcc_of_le hr₁₂] at hr
      simp only [ssc_bm, pair, ssc_multiplier_forbidden hreg, P61.wR, P61.srcR,
        P61.uR, P61.uxR, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      rw [hUdef]
      ring
    · rfl
  have hb₁ : ContinuousOn (ssc_b M Q e ω L R 1) (Ioo (outerHorizon M Q) r₁) := by
    intro r hr
    have hreg : r ∈ P61.setAH M Q e ω L := by rw [hAH]; exact hr
    exact (ssc_allowed_continuous h hQ hN hL ha hP hr.1 hreg.2.2).continuousWithinAt
  have hb₂ : ContinuousOn (ssc_b M Q e ω L R (-1)) (Ioi r₂) := by
    intro r hr
    have hreg : r ∈ P61.setAI M Q e ω L := by rw [hAI]; exact hr
    exact (ssc_allowed_continuous h hQ hN hL ha hP
      ((har₁.trans_le hr₁₂).trans hr) hreg.2).continuousWithinAt
  have hbm : ContinuousOn (ssc_bm M Q e ω L R) (Icc r₁ r₂) := by
    have hsub : Icc r₁ r₂ ⊆ Ioi (outerHorizon M Q) := fun r hr => har₁.trans_le hr.1
    have hu := hU.mono hsub
    have hv := hV.mono hsub
    have hw := (P61.wR_continuousOn (e := e) (ω := ω) h.1).mono hsub
    have hg := (P61.normalizationG_continuousOn (e := e) (ω := ω) h.1).mono hsub
    have hk := (contDiff_radialK e ω).continuous.continuousOn (s := Icc r₁ r₂)
    have hd := (contDiff_delta M Q).continuous.continuousOn (s := Icc r₁ r₂)
    unfold ssc_bm
    fun_prop
  have hwpos : ∀ r ∈ Ioi (outerHorizon M Q), 0 ≤ P61.wR M Q e ω r := by
    intro r hr
    unfold P61.wR
    rw [NormalizationFacts.normalizationG_eq_one hN]
    simpa using (one_div_pos.mpr (delta_pos hQ hr)).le
  have hp₁ : ∀ r ∈ Ioo (outerHorizon M Q) r₁, 0 ≤ ssc_b M Q e ω L R 1 r := by
    intro r hr
    have hreg : r ∈ P61.setAH M Q e ω L := by rw [hAH]; exact hr
    have hc := ssc_coefficient_props h.1 hQ h.2.2.2.1 hL ha hN hr.1 hreg.2.2
    exact mul_nonneg (mul_nonneg (div_nonneg hc.2.2.le (sq_nonneg _)) (sq_nonneg _)) (hwpos r hr.1)
  have hp₂ : ∀ r ∈ Ioi r₂, 0 ≤ ssc_b M Q e ω L R (-1) r := by
    intro r hr
    have hra := (har₁.trans_le hr₁₂).trans hr
    have hreg : r ∈ P61.setAI M Q e ω L := by rw [hAI]; exact hr
    have hc := ssc_coefficient_props h.1 hQ h.2.2.2.1 hL ha hN hra hreg.2
    exact mul_nonneg (mul_nonneg (div_nonneg hc.2.2.le (sq_nonneg _)) (sq_nonneg _)) (hwpos r hra)
  have hpm : ∀ r ∈ Icc r₁ r₂, 0 ≤ ssc_bm M Q e ω L R r := by
    intro r hr
    have hreg : r ∈ P61.setFb M Q e ω L := by rw [hFb]; exact hr
    exact mul_nonneg (add_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hreg.2)) (sq_nonneg _)))
      (hwpos r hreg.1)
  have ht₁ : Tendsto (ssc_J M Q e ω L R 1) (𝓝[<] r₁) (𝓝 (Jm r₁)) := by
    unfold ssc_J
    dsimp only [P61.khxR, Jm]
    simpa only [ofReal_one, one_mul] using hT₁
  have ht₂ : Tendsto (ssc_J M Q e ω L R (-1)) (𝓝[>] r₂) (𝓝 (Jm r₂)) := by
    unfold ssc_J
    dsimp only [P61.khxR, Jm]
    simpa only [ofReal_neg, ofReal_one, neg_one_mul, neg_mul,
      one_mul, ← sub_eq_add_neg] using hT₂
  have ht := source_three_region_identity har₁ hr₁₂ h₁ hm h₂ hb₁ hbm hb₂ hp₁ hpm hp₂
    hsrc hsrc0 hH ht₁ ht₂ hI
  have hreal : (∫ r, (pair r).re) = (∫ r in Icc ρ₁ ρ₂, pair r).re := by
    calc
      _ = (∫ r, pair r).re := reCLM.integral_comp_comm hpair
      _ = _ := congrArg Complex.re (setIntegral_eq_integral_of_forall_compl_eq_zero hpair0).symm
  rw [hreal] at ht
  simpa only [P61.SourceIdentityR, P61.bulkR, hAH, hFb, hAI, ssc_b, ssc_bm,
    ofReal_one, one_mul, ofReal_neg, neg_one_mul, neg_mul, ← sub_eq_add_neg,
    pair] using ht

end ModeStability.AllAngular

end
