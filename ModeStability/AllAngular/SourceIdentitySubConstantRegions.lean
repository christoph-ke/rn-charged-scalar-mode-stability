module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentitySubConstantTurning
public import ModeStability.AllAngular.SourceIdentityRRegions

/-!
# Matching the three radial regions in the constant system

Source: the all-angular research notes in preparation, and (3.1), (4.6).
The exact interface sets and the turning-point currents are assembled for
both positive L and the coincident turning points at L = 0.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

private theorem ssc_regions_of_pattern {a r₀ r₁ r₂ : ℝ} {P : ℝ → ℝ}
    (ha : a < r₁) (h₁ : r₁ ≤ r₀) (h₂ : r₀ ≤ r₂)
    (hp₁ : ∀ r ∈ Ioo a r₁, 0 < P r)
    (hpm : ∀ r ∈ Icc r₁ r₂, P r ≤ 0)
    (hp₂ : ∀ r ∈ Ioi r₂, 0 < P r) :
    {r | a < r ∧ r < r₀ ∧ 0 < P r} = Ioo a r₁ ∧
      {r | a < r ∧ P r ≤ 0} = Icc r₁ r₂ ∧
      {r | r₀ < r ∧ 0 < P r} = Ioi r₂ := by
  refine ⟨?_, ?_, ?_⟩
  · ext r
    constructor
    · rintro ⟨har, hr₀, hp⟩
      refine ⟨har, lt_of_not_ge fun hr₁ => ?_⟩
      exact (not_le.mpr hp) (hpm r ⟨hr₁, hr₀.le.trans h₂⟩)
    · intro hr
      exact ⟨hr.1, hr.2.trans_le h₁, hp₁ r hr⟩
  · ext r
    constructor
    · rintro ⟨har, hp⟩
      refine ⟨le_of_not_gt fun hr₁ => ?_, le_of_not_gt fun hr₂ => ?_⟩
      · exact (not_lt.mpr hp) (hp₁ r ⟨har, hr₁⟩)
      · exact (not_lt.mpr hp) (hp₂ r hr₂)
    · intro hr
      exact ⟨ha.trans_le hr.1, hpm r hr⟩
  · ext r
    constructor
    · rintro ⟨hr₀, hp⟩
      refine lt_of_not_ge fun hr₂ => ?_
      exact (not_le.mpr hp) (hpm r ⟨h₁.trans hr₀.le, hr₂⟩)
    · intro hr
      exact ⟨h₂.trans_lt hr, hp₂ r hr⟩

/-- The three regions, with matching currents for continuous U and Ux. -/
theorem ssc_gluing_data {M Q e ω L : ℝ}
    (hM : 0 < M) (hQ : |Q| < M) (hω : 0 < ω) (hL : 0 ≤ L)
    (hKa : radialK e ω (outerHorizon M Q) < 0) (hN : e / ω < 2 * M)
    {U V : ℝ → ℂ} (hU : ContinuousOn U (Ioi (outerHorizon M Q)))
    (hV : ContinuousOn V (Ioi (outerHorizon M Q))) :
    let kh := effectiveK M Q e ω L
    let fx := xDeriv M Q (normalizationG M Q e ω) kh
    let JH := fun r => -(kh r / fx r) * ‖V r + (kh r : ℂ) * I * U r‖ ^ 2 -
      (V r * (starRingEnd ℂ) (U r)).re
    let JI := fun r => -(kh r / fx r) * ‖V r - (kh r : ℂ) * I * U r‖ ^ 2 -
      (V r * (starRingEnd ℂ) (U r)).re
    let Jm := fun r => -(V r * (starRingEnd ℂ) (U r)).re
    ∃ r₁ r₂ : ℝ, outerHorizon M Q < r₁ ∧ r₁ ≤ r₂ ∧
      P61.setAH M Q e ω L = Ioo (outerHorizon M Q) r₁ ∧
      P61.setFb M Q e ω L = Icc r₁ r₂ ∧ P61.setAI M Q e ω L = Ioi r₂ ∧
      Tendsto JH (𝓝[<] r₁) (𝓝 (Jm r₁)) ∧
      Tendsto JI (𝓝[>] r₂) (𝓝 (Jm r₂)) := by
  dsimp only
  have ha := outerHorizon_lt_corotation hM hω hKa
  rcases hL.lt_or_eq with hLp | hL0
  · obtain ⟨r₁, r₂, har₁, hr₁₀, hr₀₂, -, -, -, -, hp₁, hpm, hp₂,
      hz₁, hz₂, hk₁, hk₂, -, -, hd₁, hd₂⟩ := exists_turning_points hM hQ.le hω hLp hKa
    have hr₁₂ : r₁ ≤ r₂ := (hr₁₀.trans hr₀₂).le
    have har₂ : outerHorizon M Q < r₂ := har₁.trans_le hr₁₂
    have hm : ∀ r ∈ Icc r₁ r₂, radialK e ω r ^ 2 - L * delta M Q r ≤ 0 := by
      intro r hr
      rcases hr.1.eq_or_lt with he | hl
      · rw [← he, hz₁]
      · rcases hr.2.eq_or_lt with he | hu
        · rw [he, hz₂]
        · exact (hpm r ⟨hl, hu⟩).le
    obtain ⟨hAH, hFb, hAI⟩ := ssc_regions_of_pattern har₁ hr₁₀.le hr₀₂.le
      (fun r hr => (hp₁ r hr).1) hm (fun r hr => (hp₂ r hr).1)
    refine ⟨r₁, r₂, har₁, hr₁₂, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [P61.setAH, sub_pos] using hAH
    · simpa only [P61.setFb, sub_nonpos] using hFb
    · simpa only [P61.setAI, sub_pos] using hAI
    · simpa only [ofReal_one, one_mul] using
        ssc_turning_current_left (σ := 1) hQ hN har₁ hk₁ hz₁ hd₁
          (hU.continuousAt (Ioi_mem_nhds har₁)) (hV.continuousAt (Ioi_mem_nhds har₁))
    · simpa only [ofReal_neg, ofReal_one, neg_one_mul, neg_mul, one_mul,
        ← sub_eq_add_neg] using
        ssc_turning_current_right (σ := -1) hQ hN har₂ hk₂ hz₂ hd₂
          (hU.continuousAt (Ioi_mem_nhds har₂)) (hV.continuousAt (Ioi_mem_nhds har₂))
  · have hLz : L = 0 := hL0.symm
    subst L
    obtain ⟨r₁, r₂, har₁, hr₁₂, hAH, hFb, hAI⟩ :=
      source_radial_regions hM hQ.le hω (show (0 : ℝ) ≤ 0 from le_rfl) hKa
    have hFb0 : P61.setFb M Q e ω 0 = {e / ω} := by
      ext r
      simp only [P61.setFb, mem_ofPred_eq, zero_mul, mem_singleton_iff]
      constructor
      · rintro ⟨hr, hp⟩
        have hk : radialK e ω r = 0 := by nlinarith [sq_nonneg (radialK e ω r)]
        have ha0 : 0 < outerHorizon M Q := by
          unfold outerHorizon
          exact add_pos_of_pos_of_nonneg hM (Real.sqrt_nonneg _)
        have hr0 : 0 < r := ha0.trans hr
        have hf : radialK e ω r = r * (ω * r - e) := by unfold radialK; ring
        rw [hf] at hk
        have hωr := (mul_eq_zero.mp hk).resolve_left hr0.ne'
        apply (eq_div_iff hω.ne').mpr
        linarith
      · rintro rfl
        exact ⟨ha, by rw [radialK_corotation_eq_zero e hω.ne']; simp⟩
    have hset : Icc r₁ r₂ = {e / ω} := hFb.symm.trans hFb0
    have he₁ : r₁ = e / ω := by
      have ht : r₁ ∈ ({e / ω} : Set ℝ) := hset ▸ left_mem_Icc.mpr hr₁₂
      exact ht
    have he₂ : r₂ = e / ω := by
      have ht : r₂ ∈ ({e / ω} : Set ℝ) := hset ▸ right_mem_Icc.mpr hr₁₂
      exact ht
    subst r₁ r₂
    refine ⟨e / ω, e / ω, ha, le_rfl, hAH, hFb, hAI, ?_, ?_⟩
    · simpa only [ofReal_one, one_mul] using
        ssc_turning_current_zero (σ := 1) hM hQ hω ha hN
          (hU.continuousAt (Ioi_mem_nhds ha)) (hV.continuousAt (Ioi_mem_nhds ha))
          nhdsWithin_le_nhds
    · simpa only [ofReal_neg, ofReal_one, neg_one_mul, neg_mul, one_mul,
        ← sub_eq_add_neg] using
        ssc_turning_current_zero (σ := -1) hM hQ hω ha hN
          (hU.continuousAt (Ioi_mem_nhds ha)) (hV.continuousAt (Ioi_mem_nhds ha))
          nhdsWithin_le_nhds

end ModeStability.AllAngular

end
