module

public import Mathlib
public import ModeStability.AllAngular.TurningPointGeometry

/-!
# The exact radial bulk regions in (6.3)

Source: the all-angular research notes in preparation, pp. 7–8,
and the turning-point geometry (3.1). The estimate's three sets are intervals
in radial order. For `L = 0` the forbidden interval is a singleton.
-/

public section

open Set

namespace ModeStability.AllAngular

private theorem sr_regions_of_pattern {a r₀ r₁ r₂ : ℝ} {P : ℝ → ℝ}
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

/-- The radial regions of the estimate are precisely the three intervals used
by the integrated source identity. This statement covers all four systems
and includes coincident turning points when `L = 0`. -/
theorem source_radial_regions {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hω : 0 < ω) (hL : 0 ≤ L) (hK : radialK e ω (outerHorizon M Q) < 0) :
    ∃ r₁ r₂ : ℝ, outerHorizon M Q < r₁ ∧ r₁ ≤ r₂ ∧
      {r | outerHorizon M Q < r ∧ r < e / ω ∧
        L * delta M Q r < radialK e ω r ^ 2} = Ioo (outerHorizon M Q) r₁ ∧
      {r | outerHorizon M Q < r ∧ radialK e ω r ^ 2 ≤ L * delta M Q r} = Icc r₁ r₂ ∧
      {r | e / ω < r ∧ L * delta M Q r < radialK e ω r ^ 2} = Ioi r₂ := by
  rcases hL.lt_or_eq with hLp | hL0
  · obtain ⟨r₁, r₂, ha, h₁, h₂, -, -, -, -, hp₁, hpm, hp₂, hz₁, hz₂, rest⟩ :=
      exists_turning_points hM hQ hω hLp hK
    have hm : ∀ r ∈ Icc r₁ r₂, radialK e ω r ^ 2 - L * delta M Q r ≤ 0 := by
      intro r hr
      rcases hr.1.eq_or_lt with he | hl
      · rw [← he, hz₁]
      · rcases hr.2.eq_or_lt with he | hu
        · rw [he, hz₂]
        · exact (hpm r ⟨hl, hu⟩).le
    obtain ⟨hAH, hFb, hAI⟩ := sr_regions_of_pattern ha h₁.le h₂.le
      (fun r hr => (hp₁ r hr).1) hm (fun r hr => (hp₂ r hr).1)
    refine ⟨r₁, r₂, ha, (h₁.trans h₂).le, ?_, ?_, ?_⟩
    · simpa only [sub_pos] using hAH
    · simpa only [sub_nonpos] using hFb
    · simpa only [sub_pos] using hAI
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
    obtain ⟨hAH, hFb, hAI⟩ := sr_regions_of_pattern ha le_rfl le_rfl hn hm hp
    refine ⟨e / ω, e / ω, ha, le_rfl, ?_, ?_, ?_⟩
    · simpa only [sub_pos] using hAH
    · simpa only [sub_nonpos] using hFb
    · simpa only [sub_pos] using hAI

end ModeStability.AllAngular

end
