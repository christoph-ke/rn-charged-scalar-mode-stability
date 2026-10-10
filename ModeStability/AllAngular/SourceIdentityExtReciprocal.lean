module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtReciprocalAssembly
public import ModeStability.AllAngular.SourceIdentityExtReciprocalEndpoints
public import ModeStability.AllAngular.SourceIdentityExtReciprocalPieces

/-!
# The source identity (6.3), extremal reciprocal normalization

Source: the all-angular research notes in preparation, pp. 7–8 of
the all-angular research notes in preparation. For `|Q| = M` and
`2M ≤ e/ω`, the frozen normalization is `g = h = 1/(r-M)`, `x = r-M`.
The integrated radial source equation gives locally absolutely continuous
currents. The homogeneous Green pieces give zero endpoint limits, and
turning-point matching glues the three nonnegative integrals, also at `L = 0`.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

/-- Identity (6.3) in the exact shared radial interface, including finiteness
of the bulk, in the extremal reciprocal system. -/
theorem sourceIdentity_extReciprocal : ∀ (M Q e ω ρ₁ ρ₂ L : ℝ),
    P61.Range17 M Q e ω ρ₁ ρ₂ → (|Q| = M ∧ 2 * M ≤ e / ω) → 0 ≤ L →
    ∀ (S R : ℝ → ℂ) (BH BI : ℂ), P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI →
      P61.SourceIdentityR M Q e ω L ρ₁ ρ₂ R S := by
  intro M Q e ω ρ₁ ρ₂ L h hsys hL S R BH BI hP
  obtain ⟨hQ, hN⟩ := hsys
  have hM := h.1
  have hω := h.2.2.2.1
  have ha0 : 0 < outerHorizon M Q := InfinityUniqueness.outerHorizon_pos hM
  have hka := (lt_div_iff₀ ha0).mp h.2.2.2.2.1
  have hKa : radialK e ω (outerHorizon M Q) < 0 := by
    have heq : radialK e ω (outerHorizon M Q) =
        outerHorizon M Q * (ω * outerHorizon M Q - e) := by unfold radialK; ring
    rw [heq]
    exact mul_neg_of_pos_of_neg ha0 (sub_neg.mpr hka)
  obtain ⟨T_H, T_I, B_H, B_I, hTH, hTI, hHC, hIC, hEH, hEI⟩ := ser_endpoint_pieces h hL hP
  have hΘ : ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
    fun r hr => hasDerivAt_integral_radialK_div_delta hr
  unfold HorizonConditionL at hHC
  rw [ite_eq_right fun hh => hKa.ne hh.2] at hHC
  have hH := ser_horizon_current hM hQ hω hL hKa hN h.2.2.2.2.2.1 hΘ
    hEH hP.2.2.1.1 hTH hHC.1 hHC.2
  have hI := ser_infinity_current hM hQ hω hL hKa hN hΘ
    hEI hP.2.2.1.1 hTI hIC.1 hIC.2
  apply ser_assemble h hQ hN hL hKa hP
  · unfold ser_J P61.uxR P61.uR P61.khxR
    simpa only [ofReal_one, one_mul] using hH
  · unfold ser_J P61.uxR P61.uR P61.khxR
    simpa only [ofReal_neg, ofReal_one, neg_one_mul, neg_mul, one_mul,
      ← sub_eq_add_neg] using hI


end ModeStability.AllAngular

end
