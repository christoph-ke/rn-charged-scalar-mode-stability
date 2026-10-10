module

public import Mathlib
public import ModeStability.AllAngular.BoundedLRAux

/-!
# The bounded angular regime of Proposition 6.1 in radius

Source: the all-angular research notes in preparation (all-angular paper
p. 8). A fixed test interval lies beyond the source and all outer turning
points. The radial version of (6.4) controls the constant part of the
dephased solution. Uniform compact metric bounds and (4.7) then give
the local energy estimates; Cauchy–Schwarz in (6.3) and absorption finish
the proof. Both normalizations and the extremal case are covered together.
-/

public section

open Set MeasureTheory Complex

namespace ModeStability.AllAngular

open P61

/-- Proposition 6.1 in the bounded angular range, with the exact shared
radial interface and a constant independent of L and of the solution. -/
theorem boundedLR_holds : P61.BoundedLR := by
  intro M Q e ω ρ₁ ρ₂ L₀ hrange hL₀
  obtain ⟨hM, hQ, -, hω, hωa, hρ₁, hρ⟩ := hrange
  have hap : 0 < outerHorizon M Q := by
    unfold outerHorizon
    linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
  have ha : outerHorizon M Q < e / ω := by
    apply (lt_div_iff₀ hω).mpr
    have hh := (lt_div_iff₀ hap).mp hωa
    nlinarith only [hh]
  obtain ⟨r₂₀, j₁, j₂, Γ, K₀, K₁, κ₁, κ₀, -, -, hj₁, hj,
    hΓ, hK₀, hK₁, hκ₁, -, hcoeffs⟩ :=
    boundedL_coefficients hM hQ hω ha hL₀ hρ₁ hρ.le
  have hρj : ρ₂ < j₁ := (le_max_left ρ₂ r₂₀).trans_lt hj₁
  have hab : ρ₁ ≤ j₂ := (hρ.trans hρj |>.trans hj).le
  have hI : Icc ρ₁ ρ₂ ⊆ Icc ρ₁ j₂ := Icc_subset_Icc le_rfl (hρj.trans hj).le
  have hJ : Icc j₁ j₂ ⊆ Icc ρ₁ j₂ := Icc_subset_Icc (hρ.trans hρj).le le_rfl
  have hex : Icc ρ₁ j₂ ⊆ Ioi (outerHorizon M Q) := fun r hr => hρ₁.trans_le hr.1
  have hexJ : Icc j₁ j₂ ⊆ Ioi (outerHorizon M Q) := fun r hr => hex (hJ hr)
  obtain ⟨p₀, p₁, hp₀, hp₁, hpbound⟩ := blr_p_bounds (e := e) (ω := ω) hM hQ hρ₁ hab
  let κ := κ₁ / p₁ * (∫ r in Icc j₁ j₂, boundedLCutoff j₁ j₂ r)
  have hκ : 0 < κ := mul_pos (div_pos hκ₁ hp₁) (boundedL_cutoff_integral_pos hj)
  let P := blr_supConstant ρ₁ j₂ j₁ j₂ p₁ K₀ κ (boundedLCutoff j₁ j₂)
  let A := (j₂ - ρ₁) * P ^ 2 / p₀
  let m := min (uniformConstant M Q e ω) 1
  let m₀ := m * p₀
  let T := 2 * p₁ + (2 * K₁ ^ 2 + 1 + L₀) * A
  let H := 2 * A + 8 * Γ ^ 2 * p₁
  let C := (1 + T / m₀) * (H / m₀) + 1
  have hm : 0 < m := lt_min (uniformConstant_spec hM hQ hω ha).1 one_pos
  have hm₀ : 0 < m₀ := mul_pos hm hp₀
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro L hL hLmax S R BH BI hprob hid
  obtain ⟨hallowed, htest, -, -, hgamma, hWK⟩ := hcoeffs L ⟨hL, hLmax⟩
  have hsol := hprob.2.2.1
  obtain ⟨hU, -, hUx⟩ := blr_radial_regular hM hQ hsol
  have hUc : ContinuousOn (uR M Q e ω R) (Icc ρ₁ j₂) :=
    fun r hr => (hU r (hex hr)).continuousAt.continuousWithinAt
  have hZc := (blr_z_continuous hM hQ hsol).mono hex
  have htc := (blr_weight (e := e) (ω := ω) hM hQ).1.mono hex
  have ht0 : ∀ r ∈ Icc ρ₁ j₂, 0 ≤ wR M Q e ω r :=
    fun r hr => ((blr_weight hM hQ).2 r (hex hr)).le
  have hpc := (blr_p_spec (e := e) (ω := ω) hM hQ).1.mono hex
  have hppos : ∀ r ∈ Icc ρ₁ j₂, 0 < blr_p M Q e ω r :=
    fun r hr => (blr_p_spec hM hQ).2 r (hex hr)
  obtain ⟨hkw, hkder⟩ := boundedL_test_regular hM hQ hL hexJ
    (fun r hr => (hallowed r hr).2.1) (fun r hr => (hallowed r hr).2.2)
  have hmass := blr_test_mass hj hp₁ hκ₁
    (fun r hr => ⟨hppos r (hJ hr), (hpbound r (hJ hr)).2⟩) hkder
    (fun r hr => (htest r hr).2)
  obtain ⟨hwd, hwdc, -, hwnorm, -⟩ := blr_dephase_regular hM hQ hsol
  have hws := fun r hr => hwd r (hex hr)
  have hdwc := hwdc.mono hex
  let E := boundedLEnergy (Icc ρ₁ j₂) (deriv (blr_w M Q e ω L R))
  have hE : 0 ≤ E := boundedLEnergy_nonneg _ _
  have hsup := blr_sup_bound hab hj.le hJ hp₁.le hK₀ hκ hws hdwc
    (hpc.mono hJ)
    (fun r hr => by rw [abs_of_pos (hppos r (hJ hr))]; exact (hpbound r (hJ hr)).2)
    hkw hkder (fun r hr => (htest r hr).1)
    (fun r hr => (blr_metric_identity hM hQ (hexJ hr) hsol).1)
    (fun r _ => (boundedL_cutoff_spec j₁ j₂).1 r)
    (boundedL_cutoff_spec j₁ j₂).2.1.continuousOn
    (boundedL_cutoff_spec j₁ j₂).2.2.1 (boundedL_cutoff_spec j₁ j₂).2.2.2.1
    hmass.1 hmass.2
    (fun r hr => blr_dephase_ode hM hQ (hρ₁.trans hρ) hprob
      (hρj.trans_le hr.1) (hallowed r hr).2.1 (hallowed r hr).2.2)
  have hP : 0 ≤ P := by dsimp [P, blr_supConstant]; positivity
  have hUsq : ∀ r ∈ Icc ρ₁ j₂, ‖uR M Q e ω R r‖ ^ 2 ≤ P ^ 2 * E := by
    intro r hr
    have hh : ‖uR M Q e ω R r‖ ≤ P * Real.sqrt E := by
      rw [← hwnorm r]
      exact hsup r hr
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hP (Real.sqrt_nonneg _))).mpr hh
    simpa only [mul_pow, Real.sq_sqrt hE] using hs
  have hUi := ((hUc.norm.pow 2).mul htc).integrableOn_Icc (μ := volume)
  have hZi := ((hZc.norm.pow 2).mul htc).integrableOn_Icc (μ := volume)
  have hdi := (hdwc.norm.pow 2).integrableOn_Icc (μ := volume)
  have htmax : ∀ r ∈ Icc ρ₁ j₂, wR M Q e ω r ≤ 1 / p₀ := by
    intro r hr
    exact one_div_le_one_div_of_le hp₀ (hpbound r hr).1
  have hUE : blr_energy (Icc ρ₁ j₂) (wR M Q e ω) (uR M Q e ω R) ≤ A * E := by
    have hh := setIntegral_mono_on hUi
      (integrableOn_const (C := P ^ 2 * E * (1 / p₀))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) measurableSet_Icc
      (fun r hr => mul_le_mul (hUsq r hr) (htmax r hr) (ht0 r hr)
        (mul_nonneg (sq_nonneg P) hE))
    simpa [blr_energy, integral_const, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab), A, smul_eq_mul,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  have hZE : blr_energy (Icc ρ₁ j₂) (wR M Q e ω) (blr_z M Q e ω L R) ≤ p₁ * E := by
    have hh := setIntegral_mono_on hZi (hdi.const_mul p₁) measurableSet_Icc (fun r hr => by
      change ‖blr_z M Q e ω L R r‖ ^ 2 * wR M Q e ω r ≤
        p₁ * ‖deriv (blr_w M Q e ω L R) r‖ ^ 2
      rw [(blr_metric_identity hM hQ (hex hr) hsol).2]
      exact mul_le_mul_of_nonneg_right (hpbound r hr).2 (sq_nonneg _))
    simpa only [integral_const_mul, Pi.mul_apply, Pi.pow_apply, blr_energy,
      boundedLEnergy, E] using hh
  have hZfloor : p₀ * E ≤ blr_energy (Icc ρ₁ j₂) (wR M Q e ω) (blr_z M Q e ω L R) := by
    have hh := setIntegral_mono_on (hdi.const_mul p₀) hZi measurableSet_Icc (fun r hr => by
      change p₀ * ‖deriv (blr_w M Q e ω L R) r‖ ^ 2 ≤
        ‖blr_z M Q e ω L R r‖ ^ 2 * wR M Q e ω r
      rw [(blr_metric_identity hM hQ (hex hr) hsol).2]
      exact mul_le_mul_of_nonneg_right (hpbound r hr).1 (sq_nonneg _))
    simpa only [integral_const_mul, Pi.mul_apply, Pi.pow_apply, blr_energy,
      boundedLEnergy, E] using hh
  have hZ0 : 0 ≤ blr_energy (Icc ρ₁ j₂) (wR M Q e ω) (blr_z M Q e ω L R) :=
    setIntegral_nonneg measurableSet_Icc fun r hr => mul_nonneg (sq_nonneg _) (ht0 r hr)
  have hbulk : m₀ * E ≤ (bulkR M Q e ω L R).toReal := by
    have hh := blr_bulk_bound (R := R) hM hQ hω hL ha hm.le (min_le_right _ _)
      (fun r hr hallow => (min_le_left _ _).trans
        ((uniformConstant_spec hM hQ hω ha).2.2.2 L hL r hr hallow)) hex
    have heq : ENNReal.ofReal (m * blr_energy (Icc ρ₁ j₂) (wR M Q e ω)
        (blr_z M Q e ω L R)) =
        ∫⁻ r in Icc ρ₁ j₂, ENNReal.ofReal (m * ‖blr_z M Q e ω L R r‖ ^ 2 * wR M Q e ω r) := by
      rw [blr_energy, ← integral_const_mul]
      have hh := ofReal_integral_eq_lintegral_ofReal (hZi.const_mul m)
        (ae_restrict_of_forall_mem measurableSet_Icc fun r hr =>
          mul_nonneg hm.le (mul_nonneg (sq_nonneg _) (ht0 r hr)))
      simpa only [Pi.mul_apply, Pi.pow_apply, mul_assoc] using hh
    rw [← heq] at hh
    have hreal := ENNReal.toReal_mono hid.1.ne hh
    rw [ENNReal.toReal_ofReal (mul_nonneg hm.le hZ0)] at hreal
    have hfloor : m₀ * E ≤ m * blr_energy (Icc ρ₁ j₂) (wR M Q e ω) (blr_z M Q e ω L R) := by
      simpa [m₀, mul_assoc] using mul_le_mul_of_nonneg_left hZfloor hm.le
    exact hfloor.trans hreal
  have hVbound : ∀ r ∈ Icc ρ₁ j₂, ‖uxR M Q e ω R r‖ ≤
      ‖blr_z M Q e ω L R r‖ + K₁ * ‖uR M Q e ω R r‖ := by
    intro r hr
    have hW0 : 0 ≤ boundedLPhaseFrequency M Q e ω L r := by
      unfold boundedLPhaseFrequency
      positivity
    have hh := norm_add_le (blr_z M Q e ω L R r)
      ((boundedLPhaseFrequency M Q e ω L r : ℂ) * I * uR M Q e ω R r)
    simp only [blr_z, sub_add_cancel, norm_mul, norm_real, Real.norm_of_nonneg hW0,
      norm_I, mul_one] at hh
    exact hh.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (hWK r hr).1 (norm_nonneg _)))
  have hMbound : ∀ r ∈ Icc ρ₁ ρ₂, ‖multR M Q e ω L R r‖ ≤
      ‖uR M Q e ω R r‖ + 2 * Γ * ‖blr_z M Q e ω L R r‖ := by
    intro r hr
    rw [blr_multiplier hM hω hL (hex (hI hr))]
    have hh := norm_add_le (uR M Q e ω R r)
      (2 * (boundedLGamma M Q e ω L r : ℂ) * blr_z M Q e ω L R r)
    simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_ofNat] at hh
    nlinarith only [hh, mul_le_mul_of_nonneg_right (hgamma r hr)
      (norm_nonneg (blr_z M Q e ω L R r))]
  obtain ⟨hFm, hFi⟩ := blr_source_regular hM hQ hρ₁ hprob.2.1
  have hfinal := blr_energy_estimate hI hm₀ hA hp₁.le hΓ hK₁ hL hLmax hE hUc
    (hUx.mono hex) hZc htc ht0 hUE hZE hVbound hbulk hFm hFi hMbound hid.2
  have hFi0 : 0 ≤ blr_energy (Icc ρ₁ ρ₂) (wR M Q e ω) (srcR M Q e ω S) :=
    setIntegral_nonneg measurableSet_Icc fun r hr => mul_nonneg (sq_nonneg _) (ht0 r (hI hr))
  have hfinalC : (bulkR M Q e ω L R).toReal +
      blr_energy (Icc ρ₁ ρ₂) (wR M Q e ω) (uxR M Q e ω R) +
      (1 + L) * blr_energy (Icc ρ₁ ρ₂) (wR M Q e ω) (uR M Q e ω R) ≤
        C * blr_energy (Icc ρ₁ ρ₂) (wR M Q e ω) (srcR M Q e ω S) := by
    apply hfinal.trans
    change (1 + T / m₀) * (H / m₀) * _ ≤ C * _
    dsimp [C]
    nlinarith only [hFi0]
  have hUXi := (((hUx.mono hex).norm.pow 2).mul htc).integrableOn_Icc (μ := volume) |>.mono_set hI
  have hUIi := hUi.mono_set hI
  have hUX0 : 0 ≤ blr_energy (Icc ρ₁ ρ₂) (wR M Q e ω) (uxR M Q e ω R) :=
    setIntegral_nonneg measurableSet_Icc fun r hr => mul_nonneg (sq_nonneg _) (ht0 r (hI hr))
  have hU0 : 0 ≤ blr_energy (Icc ρ₁ ρ₂) (wR M Q e ω) (uR M Q e ω R) :=
    setIntegral_nonneg measurableSet_Icc fun r hr => mul_nonneg (sq_nonneg _) (ht0 r (hI hr))
  have hB0 := ENNReal.toReal_nonneg (a := bulkR M Q e ω L R)
  have heqX := blr_ofReal_energy measurableSet_Icc (fun r hr => ht0 r (hI hr)) hUXi
  have heqU := blr_ofReal_energy measurableSet_Icc (fun r hr => ht0 r (hI hr)) hUIi
  have heqF := blr_ofReal_energy measurableSet_Icc (fun r hr => ht0 r (hI hr)) hFi
  change bulkR M Q e ω L R + _ + _ ≤ ENNReal.ofReal C * _
  rw [srcNormR, ← heqX, ← heqU, ← heqF, ← ENNReal.ofReal_toReal hid.1.ne,
    ← ENNReal.ofReal_mul (show 0 ≤ 1 + L by linarith),
    ← ENNReal.ofReal_add hB0 hUX0,
    ← ENNReal.ofReal_add (add_nonneg hB0 hUX0)
      (mul_nonneg (by linarith : 0 ≤ 1 + L) hU0),
    ← ENNReal.ofReal_mul hC.le]
  exact ENNReal.ofReal_le_ofReal hfinalC

end ModeStability.AllAngular

end
