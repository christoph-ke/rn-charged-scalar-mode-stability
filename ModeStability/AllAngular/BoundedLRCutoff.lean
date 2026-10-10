module

public import Mathlib
public import ModeStability.AllAngular.BoundedL

/-!
# The bounded angular cutoff estimate in radius

Source: the all-angular research notes in preparation, equation (6.4).
Writing `p = Δg²`, the homogeneous dephased equation is
`(p wᵣ)ᵣ = -2 i k̂ wᵣ - i k̂ᵣ w`. Its cutoff identity controls
the constant part without introducing inverse coordinate maps.
-/

public section

open Set MeasureTheory Complex

namespace ModeStability.AllAngular.P61

@[expose] noncomputable def blr_supConstant
    (a b j₁ j₂ P K κ : ℝ) (φ : ℝ → ℝ) : ℝ :=
  2 * Real.sqrt (b - a) +
    (P * Real.sqrt (∫ r in Icc j₁ j₂, deriv φ r ^ 2) +
      2 * K * Real.sqrt (∫ r in Icc j₁ j₂, φ r ^ 2)) / κ

theorem blr_cutoff_identity {j₁ j₂ : ℝ} (hj : j₁ ≤ j₂)
    {w v : ℝ → ℂ} {p k φ : ℝ → ℝ}
    (hw : ContinuousOn w (Icc j₁ j₂))
    (hd : ContinuousOn (deriv w) (Icc j₁ j₂))
    (hp : ContinuousOn p (Icc j₁ j₂))
    (hk : ContinuousOn k (Icc j₁ j₂))
    (hk' : ContinuousOn (deriv k) (Icc j₁ j₂))
    (hv : ∀ r ∈ Icc j₁ j₂, v r = (p r : ℂ) * deriv w r)
    (hφ : ∀ r ∈ Icc j₁ j₂, HasDerivAt φ (deriv φ r) r)
    (hφ' : ContinuousOn (deriv φ) (Icc j₁ j₂))
    (hφ₁ : φ j₁ = 0) (hφ₂ : φ j₂ = 0)
    (hODE : ∀ r ∈ Icc j₁ j₂, HasDerivAt v
      (-2 * I * (k r : ℂ) * deriv w r - I * ((deriv k r : ℝ) : ℂ) * w r) r) :
    I * (∫ r in Icc j₁ j₂, ((deriv k r : ℝ) : ℂ) * w r * (φ r : ℂ)) =
      (∫ r in Icc j₁ j₂, (p r : ℂ) * deriv w r * ((deriv φ r : ℝ) : ℂ)) -
        2 * I * (∫ r in Icc j₁ j₂, (k r : ℂ) * deriv w r * (φ r : ℂ)) := by
  have hφc : ContinuousOn φ (Icc j₁ j₂) :=
    fun r hr => (hφ r hr).continuousAt.continuousWithinAt
  have hcφ := continuous_ofReal.comp_continuousOn hφc
  have hcφ' := continuous_ofReal.comp_continuousOn hφ'
  have hcp := continuous_ofReal.comp_continuousOn hp
  have hck := continuous_ofReal.comp_continuousOn hk
  have hck' := continuous_ofReal.comp_continuousOn hk'
  have hA := ((hck'.mul hw).mul hcφ).integrableOn_Icc (μ := volume)
  have hB := ((hcp.mul hd).mul hcφ').integrableOn_Icc (μ := volume)
  have hC := ((hck.mul hd).mul hcφ).integrableOn_Icc (μ := volume)
  have hi : IntervalIntegrable (fun r =>
      (p r : ℂ) * deriv w r * ((deriv φ r : ℝ) : ℂ) -
        2 * I * ((k r : ℂ) * deriv w r * (φ r : ℂ)) -
        I * (((deriv k r : ℝ) : ℂ) * w r * (φ r : ℂ))) volume j₁ j₂ :=
    ((((hcp.mul hd).mul hcφ').sub
      (continuousOn_const.mul ((hck.mul hd).mul hcφ))).sub
      (continuousOn_const.mul ((hck'.mul hw).mul hcφ))).mono
        (by rw [uIcc_of_le hj]) |>.intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => v r * (φ r : ℂ))
    (fun r hr => by
      have hr' : r ∈ Icc j₁ j₂ := by simpa [uIcc_of_le hj] using hr
      convert (hODE r hr').mul (hφ r hr').ofReal_comp using 1
      rw [hv r hr']
      ring) hi
  rw [hφ₁, hφ₂] at he
  simp only [ofReal_zero, mul_zero, sub_zero] at he
  rw [intervalIntegral.integral_of_le hj, ← integral_Icc_eq_integral_Ioc] at he
  have hs₁ := integral_sub (hB.sub (hC.const_mul (2 * I))) (hA.const_mul I)
  have hs₂ := integral_sub hB (hC.const_mul (2 * I))
  simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply] at hs₁ hs₂
  rw [hs₁, hs₂, integral_const_mul, integral_const_mul] at he
  linear_combination -he

theorem blr_sup_bound {a b j₁ j₂ P K κ : ℝ}
    (hab : a ≤ b) (hj : j₁ ≤ j₂) (hsub : Icc j₁ j₂ ⊆ Icc a b)
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hκ : 0 < κ)
    {w v : ℝ → ℂ} {p k φ : ℝ → ℝ}
    (hw : ∀ r ∈ Icc a b, HasDerivAt w (deriv w r) r)
    (hd : ContinuousOn (deriv w) (Icc a b))
    (hp : ContinuousOn p (Icc j₁ j₂))
    (hpbound : ∀ r ∈ Icc j₁ j₂, |p r| ≤ P)
    (hk : ContinuousOn k (Icc j₁ j₂))
    (hk' : ContinuousOn (deriv k) (Icc j₁ j₂))
    (hkbound : ∀ r ∈ Icc j₁ j₂, |k r| ≤ K)
    (hv : ∀ r ∈ Icc j₁ j₂, v r = (p r : ℂ) * deriv w r)
    (hφ : ∀ r ∈ Icc j₁ j₂, HasDerivAt φ (deriv φ r) r)
    (hφ' : ContinuousOn (deriv φ) (Icc j₁ j₂))
    (hφ₁ : φ j₁ = 0) (hφ₂ : φ j₂ = 0)
    (hweight : ∀ r ∈ Icc j₁ j₂, 0 ≤ deriv k r * φ r)
    (hmass : κ ≤ ∫ r in Icc j₁ j₂, deriv k r * φ r)
    (hODE : ∀ r ∈ Icc j₁ j₂, HasDerivAt v
      (-2 * I * (k r : ℂ) * deriv w r - I * ((deriv k r : ℝ) : ℂ) * w r) r) :
    ∀ r ∈ Icc a b, ‖w r‖ ≤ blr_supConstant a b j₁ j₂ P K κ φ *
      Real.sqrt (boundedLEnergy (Icc a b) (deriv w)) := by
  have hwc : ContinuousOn w (Icc a b) :=
    fun r hr => (hw r hr).continuousAt.continuousWithinAt
  have hφc : ContinuousOn φ (Icc j₁ j₂) :=
    fun r hr => (hφ r hr).continuousAt.continuousWithinAt
  let D := Real.sqrt (boundedLEnergy (Icc a b) (deriv w))
  let P₀ := Real.sqrt (∫ r in Icc j₁ j₂, φ r ^ 2)
  let P₁ := Real.sqrt (∫ r in Icc j₁ j₂, deriv φ r ^ 2)
  have hDJ : Real.sqrt (boundedLEnergy (Icc j₁ j₂) (deriv w)) ≤ D :=
    Real.sqrt_le_sqrt (bl_energy_mono (hd.norm.pow 2).integrableOn_Icc hsub)
  have hB : ‖∫ r in Icc j₁ j₂, (p r : ℂ) * deriv w r * ((deriv φ r : ℝ) : ℂ)‖ ≤
      P * D * P₁ :=
    (bl_cutoff_pairing (hd.mono hsub) hp hφ' hP hpbound).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDJ hP) (Real.sqrt_nonneg _))
  have hC : ‖∫ r in Icc j₁ j₂, (k r : ℂ) * deriv w r * (φ r : ℂ)‖ ≤
      K * D * P₀ :=
    (bl_cutoff_pairing (hd.mono hsub) hk hφc hK hkbound).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDJ hK) (Real.sqrt_nonneg _))
  have hid := blr_cutoff_identity hj (hwc.mono hsub) (hd.mono hsub) hp hk hk'
    hv hφ hφ' hφ₁ hφ₂ hODE
  have hpair : ‖∫ r in Icc j₁ j₂, ((deriv k r * φ r : ℝ) : ℂ) * w r‖ ≤
      (P * P₁ + 2 * K * P₀) * D := by
    have he : (∫ r in Icc j₁ j₂, ((deriv k r * φ r : ℝ) : ℂ) * w r) =
        ∫ r in Icc j₁ j₂, ((deriv k r : ℝ) : ℂ) * w r * (φ r : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun r => by dsimp only; rw [ofReal_mul]; ring
    rw [he]
    calc
      _ = ‖I * (∫ r in Icc j₁ j₂, ((deriv k r : ℝ) : ℂ) * w r * (φ r : ℂ))‖ := by
        rw [norm_mul, norm_I, one_mul]
      _ = _ := by rw [hid]
      _ ≤ ‖∫ r in Icc j₁ j₂, (p r : ℂ) * deriv w r * ((deriv φ r : ℝ) : ℂ)‖ +
          2 * ‖∫ r in Icc j₁ j₂, (k r : ℂ) * deriv w r * (φ r : ℂ)‖ := by
        simpa [norm_mul] using norm_sub_le
          (∫ r in Icc j₁ j₂, (p r : ℂ) * deriv w r * ((deriv φ r : ℝ) : ℂ))
          (2 * I * (∫ r in Icc j₁ j₂, (k r : ℂ) * deriv w r * (φ r : ℂ)))
      _ ≤ _ := by nlinarith only [hB, hC]
  have hconst := bl_weighted_constant (hwc.mono hsub) (hk'.mul hφc) hweight hκ hmass
    (show 0 ≤ (P * P₁ + 2 * K * P₀) * D by dsimp [P₀, P₁, D]; positivity)
    (fun r hr => bl_oscillation hab hw hd (hsub hr)) hpair
  intro r hr
  have hosc := bl_oscillation hab hw hd hr
  have ht := norm_add_le (w r - w a) (w a)
  rw [sub_add_cancel] at ht
  change ‖w r‖ ≤ (2 * Real.sqrt (b - a) + (P * P₁ + 2 * K * P₀) / κ) * D
  change ‖w a‖ ≤ Real.sqrt (b - a) * D + (P * P₁ + 2 * K * P₀) * D / κ at hconst
  change ‖w r - w a‖ ≤ Real.sqrt (b - a) * D at hosc
  rw [show (P * P₁ + 2 * K * P₀) * D / κ = (P * P₁ + 2 * K * P₀) / κ * D by ring] at hconst
  nlinarith only [ht, hconst, hosc]

end ModeStability.AllAngular.P61

end
