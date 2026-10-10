module

public import Mathlib
public import ModeStability.AllAngular.BoundedLRPhase

/-!
# Comparison with the three radial bulk integrals

Source: the all-angular research notes in preparation, using (4.7) and
(5.3). All comparisons use lower Lebesgue integrals, so no integrability
of the singular allowed-region coefficient is assumed.
-/

public section

open Set MeasureTheory Complex

namespace ModeStability.AllAngular.P61

theorem blr_region {M Q e ω L r : ℝ} (hM : 0 < M) (hω : 0 < ω)
    (hL : 0 ≤ L) (hr : outerHorizon M Q < r) :
    r ∈ setAH M Q e ω L ∨ r ∈ setFb M Q e ω L ∨ r ∈ setAI M Q e ω L := by
  by_cases hf : radialK e ω r ^ 2 ≤ L * delta M Q r
  · exact Or.inr (Or.inl ⟨hr, hf⟩)
  · have ha : L * delta M Q r < radialK e ω r ^ 2 := lt_of_not_ge hf
    have hr0 : 0 < r := by
      unfold outerHorizon at hr
      linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
    have hne : r ≠ e / ω := by
      intro he
      have hk : radialK e ω r = 0 := by
        rw [he]
        unfold radialK
        field_simp
        ring
      rw [hk, zero_pow (by decide : (2 : ℕ) ≠ 0)] at ha
      exact (not_lt_of_ge (mul_nonneg hL
        (NormalizationFacts.delta_pos_of_outerHorizon_lt hr).le)) ha
    rcases hne.lt_or_gt with hn | hp
    · exact Or.inl ⟨hr, hn, ha⟩
    · exact Or.inr (Or.inr ⟨hp, ha⟩)

theorem blr_phase_AH {M Q e ω L r : ℝ} (hM : 0 < M) (hω : 0 < ω)
    (hr : r ∈ setAH M Q e ω L) :
    boundedLPhaseFrequency M Q e ω L r = -effectiveK M Q e ω L r := by
  have hr0 : 0 < r := by
    have har := hr.1
    unfold outerHorizon at har
    linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
  have hre : ω * r < e := by simpa [mul_comm] using (lt_div_iff₀ hω).mp hr.2.1
  have hk : radialK e ω r < 0 := by
    unfold radialK
    nlinarith [mul_neg_of_pos_of_neg hr0 (sub_neg.mpr hre)]
  simp only [boundedLPhaseFrequency, effectiveK, sign_neg hk, SignType.coe_neg_one,
    neg_one_mul, max_eq_left (sub_pos.mpr hr.2.2).le]
  ring

theorem blr_phase_AI {M Q e ω L r : ℝ} (hM : 0 < M) (hω : 0 < ω)
    (hr : outerHorizon M Q < r) (hAI : r ∈ setAI M Q e ω L) :
    boundedLPhaseFrequency M Q e ω L r = effectiveK M Q e ω L r := by
  have hr0 : 0 < r := by
    unfold outerHorizon at hr
    linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
  have hre : e < ω * r := by simpa [mul_comm] using (div_lt_iff₀ hω).mp hAI.1
  have hk : 0 < radialK e ω r := by
    unfold radialK
    nlinarith [mul_pos hr0 (sub_pos.mpr hre)]
  exact (blr_allowed_phase hAI.2 hk).1

theorem blr_multiplier {M Q e ω L r : ℝ} {R : ℝ → ℂ}
    (hM : 0 < M) (hω : 0 < ω) (hL : 0 ≤ L) (hr : outerHorizon M Q < r) :
    multR M Q e ω L R r = uR M Q e ω R r +
      2 * (boundedLGamma M Q e ω L r : ℂ) * blr_z M Q e ω L R r := by
  classical
  rcases blr_region (e := e) hM hω hL hr with hAH | hFb | hAI
  · simp only [multR, ite_eq_left hAH, boundedLGamma, ite_eq_left hAH.2.2, blr_z,
      blr_phase_AH hM hω hAH, ofReal_neg, khxR]
    ring
  · have hAH : r ∉ setAH M Q e ω L := fun hn => (not_lt_of_ge hFb.2) hn.2.2
    have hAI : r ∉ setAI M Q e ω L := fun hn => (not_lt_of_ge hFb.2) hn.2
    simp only [multR, ite_eq_right hAH, ite_eq_right hAI, boundedLGamma,
      ite_eq_right (not_lt_of_ge hFb.2), ofReal_zero, mul_zero, zero_mul, add_zero]
  · have hAH : r ∉ setAH M Q e ω L := fun hn => (not_lt_of_ge hAI.1.le) hn.2.1
    simp only [multR, ite_eq_right hAH, ite_eq_left hAI, boundedLGamma, ite_eq_left hAI.2,
      blr_z, blr_phase_AI hM hω hr hAI, khxR]

theorem blr_z_continuous {M Q e ω L : ℝ} {R S : ℝ → ℂ}
    (hM : 0 < M) (hQ : |Q| ≤ M)
    (hsol : IsRadialSolutionWithSourceL M Q e ω L R S) :
    ContinuousOn (blr_z M Q e ω L R) (Ioi (outerHorizon M Q)) := by
  obtain ⟨hU, -, hUx⟩ := blr_radial_regular hM hQ hsol
  have hUc : ContinuousOn (uR M Q e ω R) (Ioi (outerHorizon M Q)) :=
    fun r hr => (hU r hr).continuousAt.continuousWithinAt
  exact hUx.sub (((continuous_ofReal.comp_continuousOn
    (blr_phase_continuous hM hQ)).mul continuousOn_const).mul hUc)

theorem blr_bulk_bound {M Q e ω L m : ℝ} {R : ℝ → ℂ} {s : Set ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω) (hL : 0 ≤ L)
    (ha : outerHorizon M Q < e / ω)
    (_hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hcoeff : ∀ r ∈ Ioi (outerHorizon M Q),
      L * delta M Q r < radialK e ω r ^ 2 → m ≤ akR M Q e ω L r)
    (hs : s ⊆ Ioi (outerHorizon M Q)) :
    (∫⁻ r in s, ENNReal.ofReal (m * ‖blr_z M Q e ω L R r‖ ^ 2 * wR M Q e ω r)) ≤
      bulkR M Q e ω L R := by
  let f := fun r => ENNReal.ofReal (m * ‖blr_z M Q e ω L R r‖ ^ 2 * wR M Q e ω r)
  have hsub : s ⊆ (setAH M Q e ω L ∪ setFb M Q e ω L) ∪ setAI M Q e ω L := by
    intro r hr
    rcases blr_region (e := e) hM hω hL (hs hr) with hh | hf | hi
    · exact Or.inl (Or.inl hh)
    · exact Or.inl (Or.inr hf)
    · exact Or.inr hi
  have hH : (∫⁻ r in setAH M Q e ω L, f r) ≤
      ∫⁻ r in setAH M Q e ω L, ENNReal.ofReal (akR M Q e ω L r *
        ‖uxR M Q e ω R r + (effectiveK M Q e ω L r : ℂ) * I * uR M Q e ω R r‖ ^ 2 *
          wR M Q e ω r) := by
    apply setLIntegral_mono' (by
      have hk : Continuous (radialK e ω) := by unfold radialK; fun_prop
      have hd : Continuous (delta M Q) := by unfold delta; fun_prop
      exact measurableSet_Ioi.inter (measurableSet_Iio.inter
        (isOpen_lt (hd.const_mul L) (hk.pow 2)).measurableSet))
    intro r hr
    dsimp [f, blr_z]
    rw [blr_phase_AH hM hω hr, ofReal_neg, neg_mul, neg_mul, sub_neg_eq_add]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcoeff r hr.1 hr.2.2) (sq_nonneg _))
      ((blr_weight hM hQ).2 r hr.1).le
  have hF : (∫⁻ r in setFb M Q e ω L, f r) ≤
      ∫⁻ r in setFb M Q e ω L, ENNReal.ofReal ((‖uxR M Q e ω R r‖ ^ 2 +
        normalizationG M Q e ω r ^ 4 * (L * delta M Q r - radialK e ω r ^ 2) *
          ‖uR M Q e ω R r‖ ^ 2) * wR M Q e ω r) := by
    apply setLIntegral_mono' (by
      have hk : Continuous (radialK e ω) := by unfold radialK; fun_prop
      have hd : Continuous (delta M Q) := by unfold delta; fun_prop
      exact measurableSet_Ioi.inter (isClosed_le (hk.pow 2) (hd.const_mul L)).measurableSet)
    intro r hr
    dsimp [f, blr_z]
    rw [boundedL_phase_eq_zero hr.2, ofReal_zero, zero_mul, zero_mul, sub_zero]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ ((blr_weight hM hQ).2 r hr.1).le
    have hgap := sub_nonneg.mpr hr.2
    have hpot : 0 ≤ normalizationG M Q e ω r ^ 4 *
        (L * delta M Q r - radialK e ω r ^ 2) * ‖uR M Q e ω R r‖ ^ 2 := by positivity
    nlinarith only [hpot, mul_le_mul_of_nonneg_right hm1 (sq_nonneg (‖uxR M Q e ω R r‖))]
  have hI : (∫⁻ r in setAI M Q e ω L, f r) ≤
      ∫⁻ r in setAI M Q e ω L, ENNReal.ofReal (akR M Q e ω L r *
        ‖uxR M Q e ω R r - (effectiveK M Q e ω L r : ℂ) * I * uR M Q e ω R r‖ ^ 2 *
          wR M Q e ω r) := by
    apply setLIntegral_mono' (by
      have hk : Continuous (radialK e ω) := by unfold radialK; fun_prop
      have hd : Continuous (delta M Q) := by unfold delta; fun_prop
      exact measurableSet_Ioi.inter (isOpen_lt (hd.const_mul L) (hk.pow 2)).measurableSet)
    intro r hr
    have har := ha.trans hr.1
    dsimp [f, blr_z]
    rw [blr_phase_AI hM hω har hr]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcoeff r har hr.2) (sq_nonneg _))
      ((blr_weight hM hQ).2 r har).le
  calc
    _ ≤ ∫⁻ r in (setAH M Q e ω L ∪ setFb M Q e ω L) ∪ setAI M Q e ω L, f r :=
      lintegral_mono_set hsub
    _ ≤ (∫⁻ r in setAH M Q e ω L ∪ setFb M Q e ω L, f r) +
        ∫⁻ r in setAI M Q e ω L, f r := lintegral_union_le f _ _
    _ ≤ ((∫⁻ r in setAH M Q e ω L, f r) + ∫⁻ r in setFb M Q e ω L, f r) +
        ∫⁻ r in setAI M Q e ω L, f r :=
      add_le_add (lintegral_union_le f _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add hH hF) hI

end ModeStability.AllAngular.P61

end
