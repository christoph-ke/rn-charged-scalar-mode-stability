module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtConstantTurning
public import ModeStability.AllAngular.SourceIdentityRRegions
public import ModeStability.AllAngular.Prop61Interface

/-!
# Three radial regions and their matching currents

Source: the all-angular research notes in preparation, identity (6.3),
and (3.1), (4.6). The positive-angular case has two simple turning points;
at L = 0 both turning points coincide at corotation.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

private theorem sec_regions_of_pattern {a r₀ r₁ r₂ : ℝ} {P : ℝ → ℝ}
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

/-- Regions and turning-current matches in the extremal constant system. -/
theorem sec_regions_matching {M Q e ω L : ℝ}
    (hM : 0 < M) (hQ : |Q| = M) (hω : 0 < ω) (hL : 0 ≤ L)
    (hK : radialK e ω (outerHorizon M Q) < 0) (hN : e / ω < 2 * M)
    {U V : ℝ → ℂ} (hU : ContinuousOn U (Ioi (outerHorizon M Q)))
    (hV : ContinuousOn V (Ioi (outerHorizon M Q))) :
    ∃ r₁ r₂ : ℝ, outerHorizon M Q < r₁ ∧ r₁ ≤ r₂ ∧
      P61.setAH M Q e ω L = Ioo (outerHorizon M Q) r₁ ∧
      P61.setFb M Q e ω L = Icc r₁ r₂ ∧
      P61.setAI M Q e ω L = Ioi r₂ ∧
      Tendsto (fun r => -(effectiveK M Q e ω L r / P61.khxR M Q e ω L r) *
        ‖V r + (effectiveK M Q e ω L r : ℂ) * I * U r‖ ^ 2 -
        (V r * (starRingEnd ℂ) (U r)).re)
        (𝓝[<] r₁) (𝓝 (-(V r₁ * (starRingEnd ℂ) (U r₁)).re)) ∧
      Tendsto (fun r => -(effectiveK M Q e ω L r / P61.khxR M Q e ω L r) *
        ‖V r - (effectiveK M Q e ω L r : ℂ) * I * U r‖ ^ 2 -
        (V r * (starRingEnd ℂ) (U r)).re)
        (𝓝[>] r₂) (𝓝 (-(V r₂ * (starRingEnd ℂ) (U r₂)).re)) := by
  rcases hL.lt_or_eq with hLp | hL0
  · obtain ⟨r₁, r₂, ha, h₁, h₂, -, -, -, -, hp₁, hpm, hp₂, hz₁, hz₂, rest⟩ :=
      exists_turning_points hM hQ.le hω hLp hK
    have hm : ∀ r ∈ Icc r₁ r₂, radialK e ω r ^ 2 - L * delta M Q r ≤ 0 := by
      intro r hr
      rcases hr.1.eq_or_lt with he | hl
      · rw [← he, hz₁]
      · rcases hr.2.eq_or_lt with he | hu
        · rw [he, hz₂]
        · exact (hpm r ⟨hl, hu⟩).le
    obtain ⟨hAH, hFb, hAI⟩ := sec_regions_of_pattern ha h₁.le h₂.le
      (fun r hr => (hp₁ r hr).1) hm (fun r hr => (hp₂ r hr).1)
    refine ⟨r₁, r₂, ha, (h₁.trans h₂).le, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [P61.setAH, sub_pos] using hAH
    · simpa only [P61.setFb, sub_nonpos] using hFb
    · simpa only [P61.setAI, sub_pos] using hAI
    · rcases rest with ⟨hk₁, hk₂, he₁, he₂, hd₁, hd₂⟩
      have ht := sec_turning_current_left (σ := 1) hQ hN ha hk₁ hz₁ hd₁
        (hU.continuousAt (Ioi_mem_nhds ha)) (hV.continuousAt (Ioi_mem_nhds ha))
      simpa only [P61.khxR, ofReal_one, one_mul] using ht
    · rcases rest with ⟨hk₁, hk₂, he₁, he₂, hd₁, hd₂⟩
      have ha₂ := ha.trans (h₁.trans h₂)
      have ht := sec_turning_current_right (σ := -1) hQ hN ha₂ hk₂ hz₂ hd₂
        (hU.continuousAt (Ioi_mem_nhds ha₂)) (hV.continuousAt (Ioi_mem_nhds ha₂))
      simpa only [P61.khxR, ofReal_neg, ofReal_one, neg_one_mul, neg_mul, one_mul,
        ← sub_eq_add_neg] using ht
  · have ha := outerHorizon_lt_corotation hM hω hK
    have ha0 : 0 < outerHorizon M Q := by
      unfold outerHorizon
      exact add_pos_of_pos_of_nonneg hM (Real.sqrt_nonneg _)
    have he : ω * (e / ω) = e := mul_div_cancel₀ e hω.ne'
    have hfactor : ∀ r, radialK e ω r = r * (ω * r - e) := by
      intro r
      unfold radialK
      ring
    have hn : ∀ r ∈ Ioo (outerHorizon M Q) (e / ω),
        0 < radialK e ω r ^ 2 - L * delta M Q r := by
      intro r hr
      have hr0 : 0 < r := ha0.trans hr.1
      have hk : radialK e ω r ≠ 0 := by
        rw [hfactor]
        exact mul_ne_zero hr0.ne' (by nlinarith [mul_lt_mul_of_pos_left hr.2 hω])
      rw [← hL0, zero_mul, sub_zero]
      exact sq_pos_of_ne_zero hk
    have hp : ∀ r ∈ Ioi (e / ω), 0 < radialK e ω r ^ 2 - L * delta M Q r := by
      intro r hr
      have hr0 : 0 < r := ha0.trans (ha.trans hr)
      have hk : radialK e ω r ≠ 0 := by
        rw [hfactor]
        exact mul_ne_zero hr0.ne' (by nlinarith [mul_lt_mul_of_pos_left hr hω])
      rw [← hL0, zero_mul, sub_zero]
      exact sq_pos_of_ne_zero hk
    have hm : ∀ r ∈ Icc (e / ω) (e / ω),
        radialK e ω r ^ 2 - L * delta M Q r ≤ 0 := by
      intro r hr
      have hr0 : r = e / ω := le_antisymm hr.2 hr.1
      rw [hr0, radialK_corotation_eq_zero e hω.ne', ← hL0]
      simp
    obtain ⟨hAH, hFb, hAI⟩ := sec_regions_of_pattern ha le_rfl le_rfl hn hm hp
    refine ⟨e / ω, e / ω, ha, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [P61.setAH, sub_pos] using hAH
    · simpa only [P61.setFb, sub_nonpos] using hFb
    · simpa only [P61.setAI, sub_pos] using hAI
    · rw [← hL0]
      have ht := sec_turning_current_zero (σ := 1) hM hQ hω ha hN
        (hU.continuousAt (Ioi_mem_nhds ha)) (hV.continuousAt (Ioi_mem_nhds ha))
        (l := 𝓝[<] (e / ω)) nhdsWithin_le_nhds
      simpa only [P61.khxR, ofReal_one, one_mul] using ht
    · rw [← hL0]
      have ht := sec_turning_current_zero (σ := -1) hM hQ hω ha hN
        (hU.continuousAt (Ioi_mem_nhds ha)) (hV.continuousAt (Ioi_mem_nhds ha))
        (l := 𝓝[>] (e / ω)) nhdsWithin_le_nhds
      simpa only [P61.khxR, ofReal_neg, ofReal_one, neg_one_mul, neg_mul, one_mul,
        ← sub_eq_add_neg] using ht

end ModeStability.AllAngular

end
