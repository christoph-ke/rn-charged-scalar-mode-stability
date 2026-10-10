module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentitySubReciprocalTurning

/-!
# The source identity (6.3) in the subextremal reciprocal system

Source: the all-angular research notes in preparation, pp. 7–8.
For |Q| < M and 2M ≤ e/ω, g = h and x = 1/h. The integrated source
currents glue across the two turning points, including their coincidence
when L = 0. Their physical endpoint limits vanish. The resulting identity
is stated against `P61.SourceIdentityR`, with no extra hypotheses.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

open P61

/-- Identity (6.3), including finiteness of the bulk, in the subextremal
reciprocal normalization g = h, x = 1/h. -/
theorem sourceIdentity_subReciprocal :
    ∀ (M Q e ω ρ₁ ρ₂ L : ℝ), P61.Range17 M Q e ω ρ₁ ρ₂ →
      (|Q| < M ∧ 2 * M ≤ e / ω) → 0 ≤ L →
      ∀ (S R : ℝ → ℂ) (BH BI : ℂ), P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI →
        P61.SourceIdentityR M Q e ω L ρ₁ ρ₂ R S := by
  intro M Q e ω ρ₁ ρ₂ L h hsys hL S R BH BI hP
  obtain ⟨hQ, hN⟩ := hsys
  obtain ⟨r₁, r₂, ha, h₁₂, hAH, hFb, hAI⟩ :=
    source_radial_regions h.1 hQ.le h.2.2.2.1 hL (ssr_range_geometry h).2
  change setAH M Q e ω L = Ioo (outerHorizon M Q) r₁ at hAH
  change setFb M Q e ω L = Icc r₁ r₂ at hFb
  change setAI M Q e ω L = Ioi r₂ at hAI
  have ha₂ := ha.trans_le h₁₂
  have hs₁ : Ioo (outerHorizon M Q) r₁ ⊆ Ioi (outerHorizon M Q) := fun _ hr => hr.1
  have hsm : Icc r₁ r₂ ⊆ Ioi (outerHorizon M Q) := fun _ hr => ha.trans_le hr.1
  have hs₂ : Ioi r₂ ⊆ Ioi (outerHorizon M Q) := fun _ hr => ha₂.trans hr
  have hb₁ : ContinuousOn (ssr_b M Q e ω L 1 R) (Ioo (outerHorizon M Q) r₁) := by
    intro r hr
    have hm : r ∈ setAH M Q e ω L := by rw [hAH]; exact hr
    exact (ssr_allowed_density h hQ hN hL hP hr.1 hm.2.2).1.continuousWithinAt
  have hb₂ : ContinuousOn (ssr_b M Q e ω L (-1) R) (Ioi r₂) := by
    intro r hr
    have hm : r ∈ setAI M Q e ω L := by rw [hAI]; exact hr
    exact (ssr_allowed_density h hQ hN hL hP (hs₂ hr) hm.2).1.continuousWithinAt
  have hp₁ : ∀ r ∈ Ioo (outerHorizon M Q) r₁, 0 ≤ ssr_b M Q e ω L 1 R r := by
    intro r hr
    have hm : r ∈ setAH M Q e ω L := by rw [hAH]; exact hr
    exact (ssr_allowed_density h hQ hN hL hP hr.1 hm.2.2).2
  have hp₂ : ∀ r ∈ Ioi r₂, 0 ≤ ssr_b M Q e ω L (-1) R r := by
    intro r hr
    have hm : r ∈ setAI M Q e ω L := by rw [hAI]; exact hr
    exact (ssr_allowed_density h hQ hN hL hP (hs₂ hr) hm.2).2
  obtain ⟨hbm, hpm⟩ := ssr_forbidden_density h hQ hN hP
  obtain ⟨hsrc, hsrc0, hsrca⟩ := ssr_source_integrable h hL hP
  obtain ⟨hH, hI⟩ := ssr_endpoint_currents h hQ hN hL hP
  obtain ⟨hT₁, hT₂⟩ := ssr_turning_currents h hQ hN hL hP ha h₁₂ hFb
  have h₁ : ∀ b c, b ≤ c → Icc b c ⊆ Ioo (outerHorizon M Q) r₁ →
      (∫ r in b..c, -ssr_b M Q e ω L 1 R r - ssr_src M Q e ω L R S r) =
        ssr_J M Q e ω L 1 R c - ssr_J M Q e ω L 1 R b := by
    intro b c hbc hsub
    exact ssr_allowed_integral h hQ hN hL hP hbc (hsub ⟨le_rfl, hbc⟩).1
      (hsub ⟨hbc, le_rfl⟩).1 (Or.inl ⟨rfl, by rw [hAH]; exact hsub⟩)
  have h₂ : ∀ b c, b ≤ c → Icc b c ⊆ Ioi r₂ →
      (∫ r in b..c, -ssr_b M Q e ω L (-1) R r - ssr_src M Q e ω L R S r) =
        ssr_J M Q e ω L (-1) R c - ssr_J M Q e ω L (-1) R b := by
    intro b c hbc hsub
    exact ssr_allowed_integral h hQ hN hL hP hbc (hs₂ (hsub ⟨le_rfl, hbc⟩))
      (hs₂ (hsub ⟨hbc, le_rfl⟩)) (Or.inr ⟨rfl, by rw [hAI]; exact hsub⟩)
  have hm := ssr_forbidden_integral hQ hN hP h₁₂ ha ha₂
    (show Icc r₁ r₂ ⊆ setFb M Q e ω L by rw [hFb])
  have hH' : Tendsto (ssr_J M Q e ω L 1 R) (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
    unfold ssr_J
    simpa only [ofReal_one, one_mul] using hH
  have hI' : Tendsto (ssr_J M Q e ω L (-1) R) atTop (𝓝 0) := by
    unfold ssr_J
    simpa only [ofReal_neg, ofReal_one, one_mul, neg_mul,
      ← sub_eq_add_neg] using hI
  have hg := source_three_region_identity ha h₁₂ h₁ hm h₂ hb₁ (hbm.mono hsm) hb₂ hp₁
    (fun r hr => hpm r (by rw [hFb]; exact hr)) hp₂ hsrc
    (fun r hr => hsrca r hr) hH' hT₁ hT₂ hI'
  have hbulk : bulkR M Q e ω L R =
      (∫⁻ r in Ioo (outerHorizon M Q) r₁, ENNReal.ofReal (ssr_b M Q e ω L 1 R r)) +
      (∫⁻ r in Icc r₁ r₂, ENNReal.ofReal (ssr_bm M Q e ω L R r)) +
      (∫⁻ r in Ioi r₂, ENNReal.ofReal (ssr_b M Q e ω L (-1) R r)) := by
    simp only [bulkR, hAH, hFb, hAI, ssr_b, ssr_bm, ofReal_one, one_mul,
      ofReal_neg, neg_mul, ← sub_eq_add_neg]
  have hpair : (∫ r, ssr_src M Q e ω L R S r) =
      (∫ r in Icc ρ₁ ρ₂, srcR M Q e ω S r *
        (starRingEnd ℂ) (multR M Q e ω L R r) * (wR M Q e ω r : ℂ)).re := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsrc0]
    exact reCLM.integral_comp_comm (integrableOn_src_mul_multR h hL hP)
  change bulkR M Q e ω L R < ⊤ ∧ (bulkR M Q e ω L R).toReal = _
  rw [hbulk]
  exact ⟨hg.1, hg.2.trans (congrArg Neg.neg hpair)⟩

end ModeStability.AllAngular

end
