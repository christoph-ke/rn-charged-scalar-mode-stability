module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentitySubConstantAssembly
public import ModeStability.AllAngular.SourceIdentitySubConstantEndpoints
public import ModeStability.AllAngular.SourceIdentitySubConstantGreen

/-!
# Identity (6.3), subextremal constant normalization

Source: the all-angular research notes in preparation, pp. 7–8.
This proves the exact shared radial identity for g = 1 and x = −h.
The reflected y = h transports the landed homogeneous endpoint limits;
the source currents are integrated in r and matched at the turning points.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

/-- Identity (6.3) with precisely the shared hypotheses, for the
subextremal constant system. The bulk is finite and equals the source pairing. -/
theorem sourceIdentity_subConstant : ∀ (M Q e ω ρ₁ ρ₂ L : ℝ),
    P61.Range17 M Q e ω ρ₁ ρ₂ → (|Q| < M ∧ e / ω < 2 * M) → 0 ≤ L →
    ∀ (S R : ℝ → ℂ) (BH BI : ℂ), P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI →
      P61.SourceIdentityR M Q e ω L ρ₁ ρ₂ R S := by
  intro M Q e ω ρ₁ ρ₂ L h hsys hL S R BH BI hP
  have ha0 : 0 < outerHorizon M Q := InfinityUniqueness.outerHorizon_pos h.1
  have he := (lt_div_iff₀ ha0).mp h.2.2.2.2.1
  have hKa : radialK e ω (outerHorizon M Q) < 0 :=
    radialK_neg_of_lt_corotation h.2.2.2.1 ha0
      ((lt_div_iff₀ h.2.2.2.1).mpr (by linarith))
  have hΘ : ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
    fun r hr => hasDerivAt_integral_radialK_div_delta hr
  obtain ⟨TH, TI, CH, CI, hTH, hTI, hEH, hEI, hHH, hII⟩ := ssc_green_pieces h hL hP
  unfold ssc_homogeneous at hTH hTI
  unfold HorizonConditionL at hHH
  rw [ite_eq_right fun hc => hKa.ne hc.2] at hHH
  apply ssc_identity_of_limits h hsys.1 hsys.2 hL hP
  · unfold ssc_J P61.khxR P61.uxR P61.uR
    simpa only [ofReal_one, one_mul] using
      ssc_horizon_current h.1 hsys.1 h.2.2.2.1 hL hKa hsys.2 h.2.2.2.2.2.1
        hΘ hEH hP.2.2.1.1 hTH hHH.1 hHH.2
  · unfold ssc_J P61.khxR P61.uxR P61.uR
    simpa only [ofReal_neg, ofReal_one,
      neg_one_mul, neg_mul, one_mul, ← sub_eq_add_neg] using
      ssc_infinity_current h.1 hsys.1 h.2.2.2.1 hL hKa hsys.2 hΘ hEI
        hP.2.2.1.1 hTI hII.1 hII.2

end ModeStability.AllAngular

end
