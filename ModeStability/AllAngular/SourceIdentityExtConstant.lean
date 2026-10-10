module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtConstantAssembly
public import ModeStability.AllAngular.SourceIdentityExtConstantEndpoints
public import ModeStability.AllAngular.SourceIdentityExtConstantPieces

/-!
# Source identity (6.3), extremal constant normalization

Source: the all-angular research notes in preparation, pp. 7–8,
the all-angular research notes in preparation. For `|Q| = M` and
`e/ω < 2M`, the normalization is `g = 1` and the landed coordinate is
`y = 1/(r − M)`. The reflected-current transport gives the physical zero
endpoint limits. Integration of the three radial currents then gives the
exact shared-interface identity, including finiteness of its bulk.
-/

public section

open Complex Set Filter Topology Asymptotics

namespace ModeStability.AllAngular

/-- Identity (6.3) in the exact shared radial form, extremal constant system. -/
theorem sourceIdentity_extConstant : ∀ (M Q e ω ρ₁ ρ₂ L : ℝ),
    P61.Range17 M Q e ω ρ₁ ρ₂ → (|Q| = M ∧ e / ω < 2 * M) → 0 ≤ L →
    ∀ (S R : ℝ → ℂ) (BH BI : ℂ), P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI →
      P61.SourceIdentityR M Q e ω L ρ₁ ρ₂ R S := by
  intro M Q e ω ρ₁ ρ₂ L h hsys hL S R BH BI hP
  rcases hsys with ⟨hQ, hN⟩
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
  have hΘ : ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
    fun r hr => hasDerivAt_integral_radialK_div_delta hr
  obtain ⟨TH, CH, TI, CI, hTH, hCH, heH, hTI, hCI, heI⟩ := sec_homogeneous_pieces h hL hP
  have hH : (fun r : ℝ => exp (I * (radialPhase M Q e ω r : ℂ)) * TH r - CH)
      =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) ∧
      deriv (fun r : ℝ => exp (I * (radialPhase M Q e ω r : ℂ)) * TH r)
      =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)) := by
    unfold HorizonConditionL at hCH
    rw [ite_eq_right (fun hc => hKa.ne hc.2)] at hCH
    exact hCH
  have hJH := sec_horizon_current hM hQ hω hL hKa hN h.2.2.2.2.2.1
    hΘ heH hP.2.2.1.1 hTH hH.1 hH.2
  have hJI := sec_infinity_current hM hQ hω hL hKa hN hΘ heI hP.2.2.1.1 hTI hCI.1 hCI.2
  apply sec_identity_of_endpoints h hQ hN hL hP
  · unfold sec_current P61.uxR P61.uR P61.khxR
    simpa only [ofReal_one, one_mul] using hJH
  · unfold sec_current P61.uxR P61.uR P61.khxR
    simpa only [ofReal_neg, ofReal_one, neg_one_mul, neg_mul, one_mul,
      ← sub_eq_add_neg] using hJI

end ModeStability.AllAngular

end
