module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtReciprocalAssemblyAux

/-!
# Regions and matching currents in the extremal reciprocal source identity

Source: the all-angular research notes in preparation, pp. 7–8,
and (3.1), (4.6). The forbidden interval may be a singleton when `L = 0`.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

private theorem ser_regions_of_pattern {a r₀ r₁ r₂ : ℝ} {P : ℝ → ℝ}
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

/-- The exact shared regions and both one-sided matching currents. -/
theorem ser_regions_matching {M Q e ω ρ₁ ρ₂ L : ℝ} (h : P61.Range17 M Q e ω ρ₁ ρ₂)
    (hQ : |Q| = M) (hN : 2 * M ≤ e / ω) (hL : 0 ≤ L)
    (hKa : radialK e ω (outerHorizon M Q) < 0)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) :
    ∃ r₁ r₂ : ℝ, outerHorizon M Q < r₁ ∧ r₁ ≤ r₂ ∧
      P61.setAH M Q e ω L = Ioo (outerHorizon M Q) r₁ ∧
      P61.setFb M Q e ω L = Icc r₁ r₂ ∧ P61.setAI M Q e ω L = Ioi r₂ ∧
      Tendsto (ser_J M Q e ω L 1 R) (𝓝[<] r₁) (𝓝 (ser_Jm M Q e ω R r₁)) ∧
      Tendsto (ser_J M Q e ω L (-1) R) (𝓝[>] r₂) (𝓝 (ser_Jm M Q e ω R r₂)) := by
  have hM := h.1
  have hω := h.2.2.2.1
  have ha := outerHorizon_lt_corotation hM hω hKa
  have hu := (P61.uR_contDiffOn_one hM hP.2.2.1).continuousOn
  have hv := P61.uxR_continuousOn hM hP.2.2.1
  rcases hL.lt_or_eq with hLp | hL0
  · obtain ⟨r₁, r₂, hr₁, h₁, h₂, -, -, -, -, hp₁, hpm, hp₂, hz₁, hz₂,
      hk₁, hk₂, -, -, hd₁, hd₂⟩ := exists_turning_points hM hQ.le hω hLp hKa
    have hm : ∀ r ∈ Icc r₁ r₂, radialK e ω r ^ 2 - L * delta M Q r ≤ 0 := by
      intro r hr
      rcases hr.1.eq_or_lt with he | hl
      · rw [← he, hz₁]
      · rcases hr.2.eq_or_lt with he | hh
        · rw [he, hz₂]
        · exact (hpm r ⟨hl, hh⟩).le
    obtain ⟨hAH, hFb, hAI⟩ := ser_regions_of_pattern hr₁ h₁.le h₂.le
      (fun r hr => (hp₁ r hr).1) hm (fun r hr => (hp₂ r hr).1)
    have hr₂ := ha.trans h₂
    refine ⟨r₁, r₂, hr₁, (h₁.trans h₂).le, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [P61.setAH, sub_pos] using hAH
    · simpa only [P61.setFb, sub_nonpos] using hFb
    · simpa only [P61.setAI, sub_pos] using hAI
    · exact ser_turning_current_left hQ hN hr₁ hk₁ hz₁ hd₁
        (hu.continuousAt (Ioi_mem_nhds hr₁)) (hv.continuousAt (Ioi_mem_nhds hr₁))
    · exact ser_turning_current_right hQ hN hr₂ hk₂ hz₂ hd₂
        (hu.continuousAt (Ioi_mem_nhds hr₂)) (hv.continuousAt (Ioi_mem_nhds hr₂))
  · subst L
    have ha0 : 0 < outerHorizon M Q := by
      unfold outerHorizon
      exact add_pos_of_pos_of_nonneg hM (Real.sqrt_nonneg _)
    have he : ω * (e / ω) = e := mul_div_cancel₀ e hω.ne'
    have hfactor : ∀ r, radialK e ω r = r * (ω * r - e) := by
      intro r
      unfold radialK
      ring
    have hn : ∀ r ∈ Ioo (outerHorizon M Q) (e / ω),
        0 < radialK e ω r ^ 2 - 0 * delta M Q r := by
      intro r hr
      have hr0 : 0 < r := ha0.trans hr.1
      have hk : radialK e ω r ≠ 0 := by
        rw [hfactor]
        exact mul_ne_zero hr0.ne' (by nlinarith [mul_lt_mul_of_pos_left hr.2 hω])
      rw [zero_mul, sub_zero]
      exact sq_pos_of_ne_zero hk
    have hp : ∀ r ∈ Ioi (e / ω), 0 < radialK e ω r ^ 2 - 0 * delta M Q r := by
      intro r hr
      have hr0 : 0 < r := ha0.trans (ha.trans hr)
      have hk : radialK e ω r ≠ 0 := by
        rw [hfactor]
        exact mul_ne_zero hr0.ne' (by nlinarith [mul_lt_mul_of_pos_left hr hω])
      rw [zero_mul, sub_zero]
      exact sq_pos_of_ne_zero hk
    have hm : ∀ r ∈ Icc (e / ω) (e / ω),
        radialK e ω r ^ 2 - 0 * delta M Q r ≤ 0 := by
      intro r hr
      have hr0 : r = e / ω := le_antisymm hr.2 hr.1
      rw [hr0, radialK_corotation_eq_zero e hω.ne']
      simp
    obtain ⟨hAH, hFb, hAI⟩ := ser_regions_of_pattern ha le_rfl le_rfl hn hm hp
    refine ⟨e / ω, e / ω, ha, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [P61.setAH, sub_pos] using hAH
    · simpa only [P61.setFb, sub_nonpos] using hFb
    · simpa only [P61.setAI, sub_pos] using hAI
    · exact ser_turning_current_zero hM hQ hω ha hN
        (hu.continuousAt (Ioi_mem_nhds ha)) (hv.continuousAt (Ioi_mem_nhds ha))
        nhdsWithin_le_nhds
    · exact ser_turning_current_zero hM hQ hω ha hN
        (hu.continuousAt (Ioi_mem_nhds ha)) (hv.continuousAt (Ioi_mem_nhds ha))
        nhdsWithin_le_nhds

end ModeStability.AllAngular

end
