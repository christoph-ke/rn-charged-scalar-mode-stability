module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtReciprocalRegions

/-!
# Integrating the extremal reciprocal source current

Source: the all-angular research notes in preparation, identity (6.3),
pp. 7–8. The generic improper-integration theorem gives finite bulk from
nonnegative densities, zero endpoint limits and matching turning currents.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-- Assemble the exact radial identity from the two physical endpoint limits. -/
theorem ser_assemble {M Q e ω ρ₁ ρ₂ L : ℝ} (h : P61.Range17 M Q e ω ρ₁ ρ₂)
    (hQ : |Q| = M) (hN : 2 * M ≤ e / ω) (hL : 0 ≤ L)
    (hKa : radialK e ω (outerHorizon M Q) < 0)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI)
    (hH : Tendsto (ser_J M Q e ω L 1 R) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (hI : Tendsto (ser_J M Q e ω L (-1) R) atTop (𝓝 0)) :
    P61.SourceIdentityR M Q e ω L ρ₁ ρ₂ R S := by
  classical
  have hM := h.1
  have hω := h.2.2.2.1
  have ha := outerHorizon_lt_corotation hM hω hKa
  have hR := hP.2.2.1.1
  have hS := fun b hb c hc => (hP.2.2.1.2 b hb c hc).1
  have hint := fun b hb c hc => (hP.2.2.1.2 b hb c hc).2
  obtain ⟨r₁, r₂, hr₁, h₁₂, hAH, hFb, hAI, hT₁, hT₂⟩ :=
    ser_regions_matching h hQ hN hL hKa hP
  have hAHmem : ∀ r ∈ Ioo (outerHorizon M Q) r₁, r ∈ P61.setAH M Q e ω L := by
    rw [hAH]; exact fun _ hr => hr
  have hFmem : ∀ r ∈ Icc r₁ r₂, r ∈ P61.setFb M Q e ω L := by
    rw [hFb]; exact fun _ hr => hr
  have hAImem : ∀ r ∈ Ioi r₂, r ∈ P61.setAI M Q e ω L := by
    rw [hAI]; exact fun _ hr => hr
  have hAHex : Ioo (outerHorizon M Q) r₁ ⊆ Ioi (outerHorizon M Q) := fun _ hr => hr.1
  have hFmex : Icc r₁ r₂ ⊆ Ioi (outerHorizon M Q) := fun _ hr => hr₁.trans_le hr.1
  have hAIex : Ioi r₂ ⊆ Ioi (outerHorizon M Q) := fun _ hr => (hr₁.trans_le h₁₂).trans hr
  have hAHp := fun r hr => (hAHmem r hr).2.2
  have hFp := fun r hr => (hFmem r hr).2
  have hAIp := fun r hr => (hAImem r hr).2
  obtain ⟨hbc₁, hbn₁⟩ := ser_b_data (σ := 1) h hQ hN hL ha hP hAHex hAHp
  obtain ⟨hbcm, hbnm⟩ := ser_bm_data h hQ hN hP hFmex hFp
  obtain ⟨hbc₂, hbn₂⟩ := ser_b_data (σ := -1) h hQ hN hL ha hP hAIex hAIp
  obtain ⟨hsrc, hsrc0, hpair⟩ := ser_pair_data h hL hP
  have hmAH : ∀ r ∈ Ioo (outerHorizon M Q) r₁,
      P61.multR M Q e ω L R r = P61.uR M Q e ω R r +
        2 * ((effectiveK M Q e ω L r / P61.khxR M Q e ω L r : ℝ) : ℂ) *
          (P61.uxR M Q e ω R r + (effectiveK M Q e ω L r : ℂ) * I * P61.uR M Q e ω R r) := by
    intro r hr
    simp only [P61.multR, ite_eq_left (hAHmem r hr)]
  have hmAI : ∀ r ∈ Ioi r₂,
      P61.multR M Q e ω L R r = P61.uR M Q e ω R r +
        2 * ((effectiveK M Q e ω L r / P61.khxR M Q e ω L r : ℝ) : ℂ) *
          (P61.uxR M Q e ω R r - (effectiveK M Q e ω L r : ℂ) * I * P61.uR M Q e ω R r) := by
    intro r hr
    have hn : r ∉ P61.setAH M Q e ω L := by
      rw [hAH]
      exact fun hh => (not_lt.mpr (h₁₂.trans hr.le)) hh.2
    simp only [P61.multR, ite_eq_right hn, ite_eq_left (hAImem r hr)]
  have hmFb : ∀ r ∈ Icc r₁ r₂, P61.multR M Q e ω L R r = P61.uR M Q e ω R r := by
    intro r hr
    have hnh : r ∉ P61.setAH M Q e ω L := by
      rw [hAH]; exact fun hh => (not_lt.mpr hr.1) hh.2
    have hni : r ∉ P61.setAI M Q e ω L := by
      rw [hAI]; exact not_lt.mpr hr.2
    simp only [P61.multR, ite_eq_right hnh, ite_eq_right hni]
  have hweight : ∀ r, ser_src M Q e ω L R S r =
      P61.wR M Q e ω r *
        (P61.srcR M Q e ω S r * (starRingEnd ℂ) (P61.multR M Q e ω L R r)).re := by
    intro r
    simp only [ser_src, ser_pair, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    ring
  have hi₁ : ∀ u v, u ≤ v → Icc u v ⊆ Ioo (outerHorizon M Q) r₁ →
      (∫ r in u..v, -ser_b M Q e ω L 1 R r - ser_src M Q e ω L R S r) =
        ser_J M Q e ω L 1 R v - ser_J M Q e ω L 1 R u := by
    intro u v huv hsub
    have hu := (hsub ⟨le_rfl, huv⟩).1
    have hv := (hsub ⟨huv, le_rfl⟩).1
    have hc := ser_allowed_integral hM hQ hω hL ha hN hu hv
      (fun r hr => hAHp r (hsub (by rwa [uIcc_of_le huv] at hr)))
      (Or.inl rfl) hR hS hint
    dsimp only at hc
    convert hc using 1
    · apply intervalIntegral.integral_congr_ae
      filter_upwards with r hr
      have hm := hmAH r (hsub (by rw [← uIcc_of_le huv]; exact uIoc_subset_uIcc hr))
      rw [hweight, hm]
      dsimp only [ser_b, P61.akR, P61.uxR, P61.khxR, P61.wR, P61.srcR]
      unfold P61.uR
      simp only [ofReal_div, ofReal_one, one_mul]
      ring
    · unfold ser_J P61.uxR P61.uR P61.khxR
      simp only [ofReal_one, one_mul]
  have hi₂ : ∀ u v, u ≤ v → Icc u v ⊆ Ioi r₂ →
      (∫ r in u..v, -ser_b M Q e ω L (-1) R r - ser_src M Q e ω L R S r) =
        ser_J M Q e ω L (-1) R v - ser_J M Q e ω L (-1) R u := by
    intro u v huv hsub
    have hu := hAIex (hsub ⟨le_rfl, huv⟩)
    have hv := hAIex (hsub ⟨huv, le_rfl⟩)
    have hc := ser_allowed_integral hM hQ hω hL ha hN hu hv
      (fun r hr => hAIp r (hsub (by rwa [uIcc_of_le huv] at hr)))
      (Or.inr rfl) hR hS hint
    dsimp only at hc
    convert hc using 1
    · apply intervalIntegral.integral_congr_ae
      filter_upwards with r hr
      have hm := hmAI r (hsub (by rw [← uIcc_of_le huv]; exact uIoc_subset_uIcc hr))
      rw [hweight, hm]
      dsimp only [ser_b, P61.akR, P61.uxR, P61.khxR, P61.wR, P61.srcR]
      unfold P61.uR
      simp only [ofReal_div, ofReal_neg, ofReal_one, neg_mul, one_mul,
        ← sub_eq_add_neg]
      ring
    · unfold ser_J P61.uxR P61.uR P61.khxR
      simp only [ofReal_neg, ofReal_one, neg_mul, one_mul, ← sub_eq_add_neg]
  have him : (∫ r in r₁..r₂, -ser_bm M Q e ω L R r - ser_src M Q e ω L R S r) =
      ser_Jm M Q e ω R r₂ - ser_Jm M Q e ω R r₁ := by
    have hc := ser_forbidden_integral hQ hN hr₁ (hr₁.trans_le h₁₂) hR hS hint
    dsimp only at hc
    convert hc using 1
    · apply intervalIntegral.integral_congr_ae
      filter_upwards with r hr
      have hm := hmFb r (by have hh := uIoc_subset_uIcc hr; rwa [uIcc_of_le h₁₂] at hh)
      rw [hweight, hm]
      dsimp only [ser_bm, P61.uxR, P61.wR, P61.srcR]
      unfold P61.uR
      ring
    · unfold ser_Jm P61.uxR P61.uR
      rfl
  have hg := source_three_region_identity hr₁ h₁₂ hi₁ him hi₂ hbc₁ hbcm hbc₂ hbn₁ hbnm hbn₂
    hsrc hsrc0 hH hT₁ hT₂ hI
  dsimp only at hg
  have hbulk : P61.bulkR M Q e ω L R =
      (∫⁻ r in Ioo (outerHorizon M Q) r₁, ENNReal.ofReal (ser_b M Q e ω L 1 R r)) +
      (∫⁻ r in Icc r₁ r₂, ENNReal.ofReal (ser_bm M Q e ω L R r)) +
      (∫⁻ r in Ioi r₂, ENNReal.ofReal (ser_b M Q e ω L (-1) R r)) := by
    simp only [P61.bulkR, hAH, hFb, hAI, ser_b, ser_bm, ofReal_one, one_mul,
      ofReal_neg, neg_mul, ← sub_eq_add_neg]
  change P61.bulkR M Q e ω L R < ⊤ ∧
    (P61.bulkR M Q e ω L R).toReal = -(∫ r in Icc ρ₁ ρ₂, ser_pair M Q e ω L R S r).re
  rw [hbulk, ← hpair]
  exact hg

end ModeStability.AllAngular

end
