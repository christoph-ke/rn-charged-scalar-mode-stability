module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtConstantCurrent
public import ModeStability.AllAngular.SourceIdentityExtConstantRegions
public import ModeStability.AllAngular.SourceIdentityRGlobal
public import ModeStability.AllAngular.Prop61Multiplier

/-!
# Assembly of the three integrated radial currents

Source: the all-angular research notes in preparation, identity (6.3).
The nonnegative densities are exactly those in the shared interface. Local
absolute continuity, turning-point matches and zero endpoint limits prove
both finiteness of the bulk and the source identity.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

noncomputable def sec_current (M Q e ω L σ : ℝ) (R : ℝ → ℂ) (r : ℝ) : ℝ :=
  -(effectiveK M Q e ω L r / P61.khxR M Q e ω L r) *
    ‖P61.uxR M Q e ω R r + (σ : ℂ) * (effectiveK M Q e ω L r : ℂ) * I *
      P61.uR M Q e ω R r‖ ^ 2 -
    (P61.uxR M Q e ω R r * (starRingEnd ℂ) (P61.uR M Q e ω R r)).re

noncomputable def sec_allowedBulk (M Q e ω L σ : ℝ) (R : ℝ → ℂ) (r : ℝ) : ℝ :=
  P61.akR M Q e ω L r *
    ‖P61.uxR M Q e ω R r + (σ : ℂ) * (effectiveK M Q e ω L r : ℂ) * I *
      P61.uR M Q e ω R r‖ ^ 2 * P61.wR M Q e ω r

noncomputable def sec_middleCurrent (M Q e ω : ℝ) (R : ℝ → ℂ) (r : ℝ) : ℝ :=
  -(P61.uxR M Q e ω R r * (starRingEnd ℂ) (P61.uR M Q e ω R r)).re

noncomputable def sec_middleBulk (M Q e ω L : ℝ) (R : ℝ → ℂ) (r : ℝ) : ℝ :=
  (‖P61.uxR M Q e ω R r‖ ^ 2 + normalizationG M Q e ω r ^ 4 *
    (L * delta M Q r - radialK e ω r ^ 2) * ‖P61.uR M Q e ω R r‖ ^ 2) * P61.wR M Q e ω r

private theorem sec_bulk_continuous {M Q e ω L σ : ℝ}
    (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω) (hL : 0 ≤ L)
    (ha : outerHorizon M Q < e / ω) (hN : e / ω < 2 * M)
    {R : ℝ → ℂ} (hU : ContinuousOn (P61.uR M Q e ω R) (Ioi (outerHorizon M Q)))
    (hV : ContinuousOn (P61.uxR M Q e ω R) (Ioi (outerHorizon M Q)))
    {s : Set ℝ} (hsub : s ⊆ Ioi (outerHorizon M Q))
    (hP : ∀ r ∈ s, L * delta M Q r < radialK e ω r ^ 2) :
    ContinuousOn (sec_allowedBulk M Q e ω L σ R) s := by
  intro r hr
  obtain ⟨hk, hx0, -⟩ := sec_coefficient_props hM hQ hω hL ha hN (hsub hr) (hP r hr)
  have hd : ContDiffAt ℝ 2 (fun r => delta M Q r * normalizationG M Q e ω r ^ 2) r := by
    rw [NormalizationFacts.normalizationG_eq_one hN]
    exact (CoordinateCoefficients.contDiff_delta M Q).contDiffAt.mul (contDiffAt_const.pow 2)
  have hx : ContDiffAt ℝ 1 (P61.khxR M Q e ω L) r :=
    (hd.of_le (by norm_num)).mul (hk.derivWithin (m := 1) (by norm_num))
  have hxx : ContinuousAt
      (xDeriv M Q (normalizationG M Q e ω) (P61.khxR M Q e ω L)) r :=
    hd.continuousAt.mul (hx.derivWithin (m := 0) (by norm_num)).continuousAt
  have hak : ContinuousAt (P61.akR M Q e ω L) r :=
    ((continuousAt_const.mul (hx.continuousAt.pow 2)).sub
      (hk.continuousAt.mul hxx)).div (hx.continuousAt.pow 2) (pow_ne_zero 2 hx0.ne')
  have hu := hU.continuousAt (Ioi_mem_nhds (hsub hr))
  have hv := hV.continuousAt (Ioi_mem_nhds (hsub hr))
  have hw := (P61.wR_continuousOn hM (e := e) (ω := ω)).continuousAt
    (Ioi_mem_nhds (hsub hr))
  have hn := (hv.add (((hk.continuousAt.ofReal.const_mul (σ : ℂ)).mul_const I).mul hu)).norm.pow 2
  exact ((hak.mul hn).mul hw).continuousWithinAt

private theorem sec_bulk_nonneg {M Q e ω L σ r : ℝ}
    (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω) (hL : 0 ≤ L)
    (ha : outerHorizon M Q < e / ω) (hN : e / ω < 2 * M)
    (hr : outerHorizon M Q < r) (hP : L * delta M Q r < radialK e ω r ^ 2) (R : ℝ → ℂ) :
    0 ≤ sec_allowedBulk M Q e ω L σ R r := by
  obtain ⟨-, hx, he⟩ := sec_coefficient_props hM hQ hω hL ha hN hr hP
  have hak : 0 < P61.akR M Q e ω L r := div_pos he (pow_pos hx 2)
  have hw : 0 < P61.wR M Q e ω r := by
    unfold P61.wR
    rw [NormalizationFacts.normalizationG_eq_one hN]
    simpa using one_div_pos.mpr (CoordinateCoefficients.delta_pos_of_lt hr)
  exact mul_nonneg (mul_nonneg hak.le (sq_nonneg _)) hw.le

/-- Identity (6.3) once its physical endpoint limits have been supplied. -/
theorem sec_identity_of_endpoints {M Q e ω L ρ₁ ρ₂ : ℝ}
    (h : P61.Range17 M Q e ω ρ₁ ρ₂) (hQ : |Q| = M) (hN : e / ω < 2 * M) (hL : 0 ≤ L)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI)
    (hH : Tendsto (sec_current M Q e ω L 1 R) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (hI : Tendsto (sec_current M Q e ω L (-1) R) atTop (𝓝 0)) :
    P61.SourceIdentityR M Q e ω L ρ₁ ρ₂ R S := by
  classical
  have hM := h.1
  have hω := h.2.2.2.1
  have ha0 : 0 < outerHorizon M Q := by
    unfold outerHorizon
    exact add_pos_of_pos_of_nonneg hM (Real.sqrt_nonneg _)
  have hKa : radialK e ω (outerHorizon M Q) < 0 := by
    have ht := (lt_div_iff₀ ha0).mp h.2.2.2.2.1
    have heq : radialK e ω (outerHorizon M Q) =
        outerHorizon M Q * (ω * outerHorizon M Q - e) := by
      unfold radialK
      ring
    rw [heq]
    exact mul_neg_of_pos_of_neg ha0 (sub_neg.mpr ht)
  have ha := outerHorizon_lt_corotation hM hω hKa
  have hR := hP.2.2.1.1
  have hS := fun u hu v hv => (hP.2.2.1.2 u hu v hv).1
  have hint := fun u hu v hv => (hP.2.2.1.2 u hu v hv).2
  have hred := sec_reduction hQ hN hR hS hint
  have hU : ContinuousOn (P61.uR M Q e ω R) (Ioi (outerHorizon M Q)) := by
    unfold P61.uR
    exact hred.1.continuousOn
  have hV : ContinuousOn (P61.uxR M Q e ω R) (Ioi (outerHorizon M Q)) := by
    unfold P61.uxR P61.uR
    rw [NormalizationFacts.normalizationG_eq_one hN]
    simp only [one_pow, mul_one, ofReal_one, div_one]
    exact source_flux_continuousOn (sec_radialCoeff_continuousOn M Q e ω L) hR hS hint
  obtain ⟨r₁, r₂, hr₁, h₁₂, hAH, hFb, hAI, hT₁, hT₂⟩ :=
    sec_regions_matching hM hQ hω hL hKa hN hU hV
  have hT₁' : Tendsto (sec_current M Q e ω L 1 R) (𝓝[<] r₁)
      (𝓝 (sec_middleCurrent M Q e ω R r₁)) := by
    unfold sec_current sec_middleCurrent
    simpa only [ofReal_one, one_mul] using hT₁
  have hT₂' : Tendsto (sec_current M Q e ω L (-1) R) (𝓝[>] r₂)
      (𝓝 (sec_middleCurrent M Q e ω R r₂)) := by
    unfold sec_current sec_middleCurrent
    simpa only [ofReal_neg, ofReal_one, neg_one_mul, neg_mul, one_mul,
      ← sub_eq_add_neg] using hT₂
  let C := fun r => P61.srcR M Q e ω S r * (starRingEnd ℂ) (P61.multR M Q e ω L R r) *
    (P61.wR M Q e ω r : ℂ)
  let src := fun r => (C r).re
  have hC0 : ∀ r ∉ Icc ρ₁ ρ₂, C r = 0 := by
    intro r hr
    dsimp [C, P61.srcR]
    rw [hP.1 r hr]
    simp
  have hCi : Integrable C :=
    (P61.integrableOn_src_mul_multR h hL hP).integrable_of_forall_notMem_eq_zero hC0
  have hsrci : Integrable src := reCLM.integrable_comp hCi
  have hsrc0 : ∀ r ∉ Ioi (outerHorizon M Q), src r = 0 := by
    intro r hr
    rw [show src r = (C r).re from rfl, hC0 r ?_, zero_re]
    intro hi
    exact hr (h.2.2.2.2.2.1.trans_le hi.1)
  have hleftP : ∀ r ∈ Ioo (outerHorizon M Q) r₁,
      L * delta M Q r < radialK e ω r ^ 2 := by
    intro r hr
    have hm : r ∈ P61.setAH M Q e ω L := by rw [hAH]; exact hr
    exact hm.2.2
  have hrightP : ∀ r ∈ Ioi r₂, L * delta M Q r < radialK e ω r ^ 2 := by
    intro r hr
    have hm : r ∈ P61.setAI M Q e ω L := by rw [hAI]; exact hr
    exact hm.2
  have hleft : ∀ u v, u ≤ v → Icc u v ⊆ Ioo (outerHorizon M Q) r₁ →
      (∫ r in u..v, -sec_allowedBulk M Q e ω L 1 R r - src r) =
        sec_current M Q e ω L 1 R v - sec_current M Q e ω L 1 R u := by
    intro u v huv hsub
    have ht := sec_allowed_integral (σ := 1) hM hQ hω hL ha hN
      (hsub ⟨le_rfl, huv⟩).1 (hsub ⟨huv, le_rfl⟩).1
      (fun r hr => hleftP r (hsub (by simpa only [uIcc_of_le huv] using hr)))
      (Or.inl rfl) hR hS hint
    dsimp only at ht
    unfold sec_current P61.uxR P61.uR P61.khxR
    rw [← ht]
    apply intervalIntegral.integral_congr
    intro r hr
    have hm : r ∈ P61.setAH M Q e ω L := by
      rw [hAH]
      exact hsub (by simpa only [uIcc_of_le huv] using hr)
    dsimp only [src, C]
    unfold sec_allowedBulk P61.multR P61.akR P61.wR P61.uxR P61.uR P61.srcR P61.khxR
    simp only [ite_eq_left hm, ← ofReal_div, ofReal_one, one_mul, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero]
    ring
  have hright : ∀ u v, u ≤ v → Icc u v ⊆ Ioi r₂ →
      (∫ r in u..v, -sec_allowedBulk M Q e ω L (-1) R r - src r) =
        sec_current M Q e ω L (-1) R v - sec_current M Q e ω L (-1) R u := by
    intro u v huv hsub
    have ht := sec_allowed_integral (σ := -1) hM hQ hω hL ha hN
      (hr₁.trans_le h₁₂ |>.trans (hsub ⟨le_rfl, huv⟩))
      (hr₁.trans_le h₁₂ |>.trans (hsub ⟨huv, le_rfl⟩))
      (fun r hr => hrightP r (hsub (by simpa only [uIcc_of_le huv] using hr)))
      (Or.inr rfl) hR hS hint
    dsimp only at ht
    unfold sec_current P61.uxR P61.uR P61.khxR
    rw [← ht]
    apply intervalIntegral.integral_congr
    intro r hr
    have hri := hsub (by simpa only [uIcc_of_le huv] using hr)
    have hmi : r ∈ P61.setAI M Q e ω L := by rw [hAI]; exact hri
    have hmh : r ∉ P61.setAH M Q e ω L := by
      rw [hAH]
      intro hh
      exact (not_lt.mpr (h₁₂.trans hri.le)) hh.2
    dsimp only [src, C]
    unfold sec_allowedBulk P61.multR P61.akR P61.wR P61.uxR P61.uR P61.srcR P61.khxR
    simp only [ite_eq_right hmh, ite_eq_left hmi, ← ofReal_div, ofReal_neg, ofReal_one,
      neg_mul, one_mul, ← sub_eq_add_neg, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    ring
  have hmiddle : (∫ r in r₁..r₂, -sec_middleBulk M Q e ω L R r - src r) =
      sec_middleCurrent M Q e ω R r₂ - sec_middleCurrent M Q e ω R r₁ := by
    have ht := sec_forbidden_integral hQ hN hr₁ (hr₁.trans_le h₁₂) hR hS hint
    dsimp only at ht
    unfold sec_middleCurrent P61.uxR P61.uR
    rw [← ht]
    apply intervalIntegral.integral_congr
    intro r hr
    have hrr : r ∈ Icc r₁ r₂ := by simpa only [uIcc_of_le h₁₂] using hr
    have hmh : r ∉ P61.setAH M Q e ω L := by
      rw [hAH]
      exact fun hh => (not_lt.mpr hrr.1) hh.2
    have hmi : r ∉ P61.setAI M Q e ω L := by
      rw [hAI]
      exact not_lt.mpr hrr.2
    dsimp only [src, C]
    unfold sec_middleBulk P61.multR P61.wR P61.uxR P61.uR P61.srcR
    simp only [ite_eq_right hmh, ite_eq_right hmi, mul_re, ofReal_re, ofReal_im,
      mul_zero, sub_zero]
    ring
  have hb₁ := sec_bulk_continuous (σ := 1) hM hQ hω hL ha hN hU hV
    (fun r hr => hr.1) hleftP
  have hb₂ := sec_bulk_continuous (σ := -1) hM hQ hω hL ha hN hU hV
    (fun r hr => hr₁.trans_le h₁₂ |>.trans hr) hrightP
  have hsubm : Icc r₁ r₂ ⊆ Ioi (outerHorizon M Q) := fun r hr => hr₁.trans_le hr.1
  have hbm : ContinuousOn (sec_middleBulk M Q e ω L R) (Icc r₁ r₂) := by
    have hu := hU.mono hsubm
    have hv := hV.mono hsubm
    have hg := (P61.normalizationG_continuousOn (e := e) (ω := ω) hM).mono hsubm
    have hd := (CoordinateCoefficients.contDiff_delta M Q).continuous.continuousOn
      (s := Icc r₁ r₂)
    have hk := (CoordinateCoefficients.contDiff_radialK e ω).continuous.continuousOn
      (s := Icc r₁ r₂)
    have hw := (P61.wR_continuousOn (e := e) (ω := ω) hM).mono hsubm
    exact ((hv.norm.pow 2).add (((hg.pow 4).mul
      ((continuousOn_const.mul hd).sub (hk.pow 2))).mul (hu.norm.pow 2))).mul hw
  have hp₁ : ∀ r ∈ Ioo (outerHorizon M Q) r₁,
      0 ≤ sec_allowedBulk M Q e ω L 1 R r := fun r hr =>
    sec_bulk_nonneg (σ := 1) hM hQ hω hL ha hN hr.1 (hleftP r hr) R
  have hp₂ : ∀ r ∈ Ioi r₂,
      0 ≤ sec_allowedBulk M Q e ω L (-1) R r := fun r hr =>
    sec_bulk_nonneg (σ := -1) hM hQ hω hL ha hN
    (hr₁.trans_le h₁₂ |>.trans hr) (hrightP r hr) R
  have hpm : ∀ r ∈ Icc r₁ r₂, 0 ≤ sec_middleBulk M Q e ω L R r := by
    intro r hr
    have hm : r ∈ P61.setFb M Q e ω L := by rw [hFb]; exact hr
    have hg0 : 0 ≤ normalizationG M Q e ω r ^ 4 := by positivity
    have hw : 0 ≤ P61.wR M Q e ω r := by
      unfold P61.wR
      rw [NormalizationFacts.normalizationG_eq_one hN]
      simpa using (one_div_pos.mpr (CoordinateCoefficients.delta_pos_of_lt (hsubm hr))).le
    exact mul_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg
      (mul_nonneg hg0 (sub_nonneg.mpr hm.2)) (sq_nonneg _))) hw
  have hid := source_three_region_identity hr₁ h₁₂ hleft hmiddle hright hb₁ hbm hb₂
    hp₁ hpm hp₂ hsrci hsrc0 hH hT₁' hT₂' hI
  have hbulk : P61.bulkR M Q e ω L R =
      (∫⁻ r in Ioo (outerHorizon M Q) r₁, ENNReal.ofReal (sec_allowedBulk M Q e ω L 1 R r)) +
      (∫⁻ r in Icc r₁ r₂, ENNReal.ofReal (sec_middleBulk M Q e ω L R r)) +
      (∫⁻ r in Ioi r₂, ENNReal.ofReal (sec_allowedBulk M Q e ω L (-1) R r)) := by
    simp only [P61.bulkR, hAH, hFb, hAI, sec_allowedBulk, sec_middleBulk,
      ofReal_one, one_mul, ofReal_neg, neg_mul, ← sub_eq_add_neg]
  unfold P61.SourceIdentityR
  refine ⟨by rw [hbulk]; exact hid.1, ?_⟩
  rw [hbulk, hid.2]
  congr 1
  have hsrcSupport : ∀ r ∉ Icc ρ₁ ρ₂, src r = 0 := fun r hr => by
    dsimp [src]
    rw [hC0 r hr, zero_re]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsrcSupport]
  exact reCLM.integral_comp_comm hCi.integrableOn

end ModeStability.AllAngular

end
