module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentitySubReciprocalAux

/-!
# Matching the interface currents at reciprocal turning points

Source: the all-angular research notes in preparation, pp. 7–8,
and the turning-point matching (4.6). The radial regions select the same
turning points as the polynomial geometry; at L = 0 they both equal e/ω.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

open P61

private theorem ssr_zero_corotation {M Q e ω r : ℝ}
    (hM : 0 < M) (hω : 0 < ω) (hr : outerHorizon M Q < r)
    (hp : radialK e ω r ^ 2 ≤ 0) : r = e / ω := by
  have ha : 0 < outerHorizon M Q := by
    unfold outerHorizon
    exact add_pos_of_pos_of_nonneg hM (Real.sqrt_nonneg _)
  have hr0 := ha.trans hr
  have hK : radialK e ω r = 0 := (sq_eq_zero_iff).mp (le_antisymm hp (sq_nonneg _))
  have hf : radialK e ω r = r * (ω * r - e) := by unfold radialK; ring
  rw [hf] at hK
  have he := (mul_eq_zero.mp hK).resolve_left hr0.ne'
  apply (eq_div_iff hω.ne').mpr
  linarith

/-- The two interface currents match the middle flux for the radial regions,
including the singleton forbidden interval at L = 0. -/
theorem ssr_turning_currents {M Q e ω ρ₁ ρ₂ L r₁ r₂ : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) (hL : 0 ≤ L)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI)
    (ha : outerHorizon M Q < r₁) (h₁₂ : r₁ ≤ r₂)
    (hFb : setFb M Q e ω L = Icc r₁ r₂) :
    Tendsto (ssr_J M Q e ω L 1 R) (𝓝[<] r₁) (𝓝 (ssr_Jm M Q e ω R r₁)) ∧
      Tendsto (ssr_J M Q e ω L (-1) R) (𝓝[>] r₂) (𝓝 (ssr_Jm M Q e ω R r₂)) := by
  have hUC := (uR_contDiffOn_one h.1 hP.2.2.1).continuousOn
  have hVC := uxR_continuousOn h.1 hP.2.2.1
  have ha₂ := ha.trans_le h₁₂
  have hU₁ := hUC.continuousAt (Ioi_mem_nhds ha)
  have hV₁ := hVC.continuousAt (Ioi_mem_nhds ha)
  have hU₂ := hUC.continuousAt (Ioi_mem_nhds ha₂)
  have hV₂ := hVC.continuousAt (Ioi_mem_nhds ha₂)
  have hm₁ : r₁ ∈ setFb M Q e ω L := by rw [hFb]; exact ⟨le_rfl, h₁₂⟩
  have hm₂ : r₂ ∈ setFb M Q e ω L := by rw [hFb]; exact ⟨h₁₂, le_rfl⟩
  rcases hL.lt_or_eq with hpos | hzero
  · obtain ⟨s₁, s₂, hs₁, hs₁₀, hs₀₂, -, -, -, -, hp₁, -, hp₂,
      hz₁, hz₂, hK₁, hK₂, -, -, hd₁, hd₂⟩ :=
      exists_turning_points h.1 hQ.le h.2.2.2.1 hpos (ssr_range_geometry h).2
    have hms₁ : s₁ ∈ Icc r₁ r₂ := by
      rw [← hFb]
      exact ⟨hs₁, sub_nonpos.mp hz₁.le⟩
    have hms₂ : s₂ ∈ Icc r₁ r₂ := by
      rw [← hFb]
      exact ⟨hs₁.trans (hs₁₀.trans hs₀₂), sub_nonpos.mp hz₂.le⟩
    have he₁ : r₁ = s₁ := le_antisymm hms₁.1 (le_of_not_gt fun hl =>
      (not_lt.mpr (sub_nonpos.mpr hm₁.2)) (hp₁ r₁ ⟨ha, hl⟩).1)
    have he₂ : r₂ = s₂ := le_antisymm (le_of_not_gt fun hl =>
      (not_lt.mpr (sub_nonpos.mpr hm₂.2)) (hp₂ r₂ hl).1) hms₂.2
    subst s₁ s₂
    exact ⟨source_sub_reciprocal_turning_current_left (σ := 1) hQ hN ha hK₁ hz₁ hd₁ hU₁ hV₁,
      source_sub_reciprocal_turning_current_right (σ := -1) hQ hN ha₂ hK₂ hz₂ hd₂ hU₂ hV₂⟩
  · subst L
    have he₁ : r₁ = e / ω := ssr_zero_corotation h.1 h.2.2.2.1 ha (by simpa using hm₁.2)
    have he₂ : r₂ = e / ω := ssr_zero_corotation h.1 h.2.2.2.1 ha₂ (by simpa using hm₂.2)
    subst r₁ r₂
    exact ⟨source_sub_reciprocal_turning_current_zero (σ := 1) h.1 hQ h.2.2.2.1
        (ssr_range_geometry h).1 hN hU₁ hV₁ nhdsWithin_le_nhds,
      source_sub_reciprocal_turning_current_zero (σ := -1) h.1 hQ h.2.2.2.1
        (ssr_range_geometry h).1 hN hU₂ hV₂ nhdsWithin_le_nhds⟩

end ModeStability.AllAngular

end
