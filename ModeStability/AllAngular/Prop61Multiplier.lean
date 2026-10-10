module

public import Mathlib
public import ModeStability.AllAngular.Prop61MultiplierAux

/-!
# The shared radial multiplier for the source identity (6.3)

Source: the all-angular research notes in preparation, pp. 7–8,
Proposition 6.1 and its multiplier proof. Continuity across the turning
points is proved in `Prop61MultiplierAux`. On the compact source interval,
the continuous multiplier and coordinate density multiply the L² source
to give an integrable right-hand side of (6.3). The pointwise norm bound
is independent of the coordinate system and of any regularity assumptions.
-/

public section

open Complex Set MeasureTheory

namespace ModeStability.AllAngular.P61

/-- The source pairing on the right-hand side of (6.3) is integrable, for
both normalizations and for subextremal or extremal parameters. -/
theorem integrableOn_src_mul_multR {M Q e ω ρ₁ ρ₂ L : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hL : 0 ≤ L)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) :
    IntegrableOn (fun s => srcR M Q e ω S s * (starRingEnd ℂ) (multR M Q e ω L R s) *
      (wR M Q e ω s : ℂ)) (Icc ρ₁ ρ₂) := by
  have hsub : Icc ρ₁ ρ₂ ⊆ Ioi (outerHorizon M Q) :=
    fun s hs => h.2.2.2.2.2.1.trans_le hs.1
  have hS : IntegrableOn S (Icc ρ₁ ρ₂) := hP.2.1.integrable (by norm_num)
  have hg := (normalizationG_continuousOn (e := e) (ω := ω) h.1).mono hsub
  have hd : ContinuousOn (delta M Q) (Icc ρ₁ ρ₂) :=
    (CoordinateCoefficients.contDiff_delta M Q).continuous.continuousOn
  have hsrc : IntegrableOn (srcR M Q e ω S) (Icc ρ₁ ρ₂) :=
    hS.continuousOn_mul (continuous_ofReal.comp_continuousOn (hd.mul (hg.pow 3))) isCompact_Icc
  have hm := (multR_continuousOn h hL hP).mono hsub
  have hstar : ContinuousOn (fun s => (starRingEnd ℂ) (multR M Q e ω L R s))
      (Icc ρ₁ ρ₂) := continuous_star.comp_continuousOn hm
  exact (hsrc.mul_continuousOn hstar isCompact_Icc).mul_continuousOn
    (continuous_ofReal.comp_continuousOn ((wR_continuousOn h.1).mono hsub)) isCompact_Icc

/-- For fixed parameters and a fixed solution, the multiplier is bounded
on every compact subset of the exterior. -/
theorem exists_bound_multR_on_compact {M Q e ω ρ₁ ρ₂ L : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hL : 0 ≤ L)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI)
    {K : Set ℝ} (hK : IsCompact K) (hsub : K ⊆ Ioi (outerHorizon M Q)) :
    ∃ C : ℝ, ∀ s ∈ K, ‖multR M Q e ω L R s‖ ≤ C :=
  hK.exists_bound_of_continuousOn ((multR_continuousOn h hL hP).mono hsub)

private theorem pm_norm_plus (U V : ℂ) (γ k : ℝ) :
    ‖U + 2 * (γ : ℂ) * (V + (k : ℂ) * I * U)‖ ≤
      ‖U‖ + 2 * |γ| * (‖V‖ + |k| * ‖U‖) := by
  calc
    _ ≤ ‖U‖ + ‖2 * (γ : ℂ) * (V + (k : ℂ) * I * U)‖ := norm_add_le _ _
    _ = ‖U‖ + 2 * |γ| * ‖V + (k : ℂ) * I * U‖ := by
      simp [Complex.norm_real]
    _ ≤ ‖U‖ + 2 * |γ| * (‖V‖ + ‖(k : ℂ) * I * U‖) :=
      add_le_add (le_refl ‖U‖) (mul_le_mul_of_nonneg_left (norm_add_le V ((k : ℂ) * I * U))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg γ)))
    _ = _ := by simp [Complex.norm_real]

private theorem pm_norm_minus (U V : ℂ) (γ k : ℝ) :
    ‖U + 2 * (γ : ℂ) * (V - (k : ℂ) * I * U)‖ ≤
      ‖U‖ + 2 * |γ| * (‖V‖ + |k| * ‖U‖) := by
  calc
    _ ≤ ‖U‖ + ‖2 * (γ : ℂ) * (V - (k : ℂ) * I * U)‖ := norm_add_le _ _
    _ = ‖U‖ + 2 * |γ| * ‖V - (k : ℂ) * I * U‖ := by
      simp [Complex.norm_real]
    _ ≤ ‖U‖ + 2 * |γ| * (‖V‖ + ‖(k : ℂ) * I * U‖) :=
      add_le_add (le_refl ‖U‖) (mul_le_mul_of_nonneg_left (norm_sub_le V ((k : ℂ) * I * U))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg γ)))
    _ = _ := by simp [Complex.norm_real]

/-- A pointwise multiplier bound valid without parameter or solution hypotheses. -/
theorem norm_multR_le (M Q e ω L : ℝ) (R : ℝ → ℂ) (r : ℝ) :
    ‖multR M Q e ω L R r‖ ≤ ‖uR M Q e ω R r‖ +
      2 * |effectiveK M Q e ω L r / khxR M Q e ω L r| *
        (‖uxR M Q e ω R r‖ + |effectiveK M Q e ω L r| * ‖uR M Q e ω R r‖) := by
  classical
  unfold multR
  split_ifs with hh hi
  · exact pm_norm_plus _ _ _ _
  · exact pm_norm_minus _ _ _ _
  · exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
      (add_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))))

end ModeStability.AllAngular.P61

end
