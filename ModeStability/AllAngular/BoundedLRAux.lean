module

public import Mathlib
public import ModeStability.AllAngular.BoundedLRBulk
public import ModeStability.AllAngular.BoundedLREnergy

/-!
# Compact metric and source bounds for the radial bounded-L estimate

Source: the all-angular research notes in preparation. The positive
coordinate Jacobian has upper and lower bounds on a fixed compact exterior
interval. The physical source is still only assumed L².
-/

public section

open Set MeasureTheory Complex

namespace ModeStability.AllAngular.P61

@[expose] noncomputable def blr_p (M Q e ω r : ℝ) : ℝ :=
  delta M Q r * normalizationG M Q e ω r ^ 2

theorem blr_p_spec {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) :
    ContinuousOn (blr_p M Q e ω) (Ioi (outerHorizon M Q)) ∧
      ∀ r ∈ Ioi (outerHorizon M Q), 0 < blr_p M Q e ω r := by
  have hd : Continuous (delta M Q) := by unfold delta; fun_prop
  have hg : ContinuousOn (normalizationG M Q e ω) (Ioi (outerHorizon M Q)) :=
    fun r hr => (boundedL_continuousAt_g hM hQ hr).continuousWithinAt
  obtain ⟨c, hgp⟩ := blr_gauge (e := e) (ω := ω) hM hQ
  exact ⟨hd.continuousOn.mul (hg.pow 2), fun r hr =>
    mul_pos (NormalizationFacts.delta_pos_of_outerHorizon_lt hr) (pow_pos (hgp r hr).2 2)⟩

theorem blr_p_bounds {M Q e ω a b : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (ha : outerHorizon M Q < a) (hab : a ≤ b) :
    ∃ p₀ p₁ : ℝ, 0 < p₀ ∧ 0 < p₁ ∧
      ∀ r ∈ Icc a b, p₀ ≤ blr_p M Q e ω r ∧ blr_p M Q e ω r ≤ p₁ := by
  have hsub : Icc a b ⊆ Ioi (outerHorizon M Q) := fun r hr => ha.trans_le hr.1
  have hc := (blr_p_spec (e := e) (ω := ω) hM hQ).1.mono hsub
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  exact ⟨blr_p M Q e ω r, blr_p M Q e ω s,
    (blr_p_spec hM hQ).2 r (hsub hr), (blr_p_spec hM hQ).2 s (hsub hs),
    fun t ht => ⟨hmin ht, hmax ht⟩⟩

theorem blr_metric_identity {M Q e ω L : ℝ} {R S : ℝ → ℂ} {r : ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hr : outerHorizon M Q < r)
    (hsol : IsRadialSolutionWithSourceL M Q e ω L R S) :
    blr_v M Q e ω L R r = (blr_p M Q e ω r : ℂ) * deriv (blr_w M Q e ω L R) r ∧
      ‖blr_z M Q e ω L R r‖ ^ 2 * wR M Q e ω r =
        blr_p M Q e ω r * ‖deriv (blr_w M Q e ω L R) r‖ ^ 2 := by
  have hp := (blr_p_spec (e := e) (ω := ω) hM hQ).2 r hr
  obtain ⟨-, -, hdw, -, hv⟩ := blr_dephase_regular hM hQ hsol
  have hd := hdw r hr
  constructor
  · rw [hd]
    change _ = (blr_p M Q e ω r : ℂ) * (((1 / blr_p M Q e ω r : ℝ) : ℂ) * _)
    push_cast
    field_simp [hp.ne']
  · have hn : ‖deriv (blr_w M Q e ω L R) r‖ =
        ‖blr_z M Q e ω L R r‖ / blr_p M Q e ω r := by
      rw [hd, norm_mul, hv r, norm_real, Real.norm_of_nonneg ((blr_weight hM hQ).2 r hr).le]
      change 1 / blr_p M Q e ω r * _ = _
      ring
    rw [hn]
    change _ * (1 / blr_p M Q e ω r) = _
    field_simp [hp.ne']

theorem blr_test_mass {M Q e ω L j₁ j₂ P κ₁ : ℝ}
    (_hj : j₁ < j₂) (hP : 0 < P) (hκ₁ : 0 < κ₁)
    (hp : ∀ r ∈ Icc j₁ j₂, 0 < blr_p M Q e ω r ∧ blr_p M Q e ω r ≤ P)
    (hk' : ContinuousOn (deriv (effectiveK M Q e ω L)) (Icc j₁ j₂))
    (hlow : ∀ r ∈ Icc j₁ j₂, κ₁ ≤ khxR M Q e ω L r) :
    (∀ r ∈ Icc j₁ j₂, 0 ≤ deriv (effectiveK M Q e ω L) r * boundedLCutoff j₁ j₂ r) ∧
      (κ₁ / P) * (∫ r in Icc j₁ j₂, boundedLCutoff j₁ j₂ r) ≤
        ∫ r in Icc j₁ j₂, deriv (effectiveK M Q e ω L) r * boundedLCutoff j₁ j₂ r := by
  have hder : ∀ r ∈ Icc j₁ j₂, κ₁ / P ≤ deriv (effectiveK M Q e ω L) r := by
    intro r hr
    have hh := hlow r hr
    change κ₁ ≤ blr_p M Q e ω r * deriv (effectiveK M Q e ω L) r at hh
    have hpos : 0 ≤ deriv (effectiveK M Q e ω L) r := by
      exact nonneg_of_mul_nonneg_right (hκ₁.le.trans hh) (hp r hr).1
    apply (div_le_iff₀ hP).mpr
    nlinarith only [hh, mul_le_mul_of_nonneg_right (hp r hr).2 hpos]
  have hφc : Continuous (boundedLCutoff j₁ j₂) := by unfold boundedLCutoff; fun_prop
  have hφ0 := (boundedL_cutoff_spec j₁ j₂).2.2.2.2
  refine ⟨fun r hr => mul_nonneg ((div_pos hκ₁ hP).le.trans (hder r hr)) (hφ0 r), ?_⟩
  rw [← integral_const_mul]
  exact setIntegral_mono_on (hφc.continuousOn.integrableOn_Icc.const_mul (κ₁ / P))
    (hk'.mul hφc.continuousOn).integrableOn_Icc measurableSet_Icc
    (fun r hr => mul_le_mul_of_nonneg_right (hder r hr) (hφ0 r))

theorem blr_source_regular {M Q e ω ρ₁ ρ₂ : ℝ} {S : ℝ → ℂ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hρ : outerHorizon M Q < ρ₁)
    (hS : MemLp S 2 (volume.restrict (Icc ρ₁ ρ₂))) :
    AEStronglyMeasurable (srcR M Q e ω S) (volume.restrict (Icc ρ₁ ρ₂)) ∧
      IntegrableOn (fun r => ‖srcR M Q e ω S r‖ ^ 2 * wR M Q e ω r) (Icc ρ₁ ρ₂) := by
  have hsub : Icc ρ₁ ρ₂ ⊆ Ioi (outerHorizon M Q) := fun r hr => hρ.trans_le hr.1
  have hd : Continuous (delta M Q) := by unfold delta; fun_prop
  have hg : ContinuousOn (normalizationG M Q e ω) (Icc ρ₁ ρ₂) :=
    fun r hr => (boundedL_continuousAt_g hM hQ (hsub hr)).continuousWithinAt
  have hA : ContinuousOn (fun r => delta M Q r * normalizationG M Q e ω r ^ 3)
      (Icc ρ₁ ρ₂) := hd.continuousOn.mul (hg.pow 3)
  have ht := (blr_weight (e := e) (ω := ω) hM hQ).1.mono hsub
  refine ⟨(continuous_ofReal.comp_continuousOn hA).aestronglyMeasurable measurableSet_Icc |>.mul
    hS.aestronglyMeasurable, ?_⟩
  have hSi : IntegrableOn (fun r => ‖S r‖ ^ 2) (Icc ρ₁ ρ₂) :=
    hS.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  apply (hSi.mul_continuousOn ((hA.pow 2).mul ht) isCompact_Icc).congr_fun
    (fun r hr => ?_) measurableSet_Icc
  simp only [srcR, norm_mul, norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    Pi.mul_apply, Pi.pow_apply]
  ring

theorem blr_ofReal_energy {s : Set ℝ} {t : ℝ → ℝ} {f : ℝ → ℂ}
    (hs : MeasurableSet s) (ht : ∀ r ∈ s, 0 ≤ t r)
    (hi : IntegrableOn (fun r => ‖f r‖ ^ 2 * t r) s) :
    ENNReal.ofReal (blr_energy s t f) =
      ∫⁻ r in s, ENNReal.ofReal (‖f r‖ ^ 2 * t r) :=
  ofReal_integral_eq_lintegral_ofReal hi
    (ae_restrict_of_forall_mem hs fun r hr => mul_nonneg (sq_nonneg _) (ht r hr))

end ModeStability.AllAngular.P61

end
