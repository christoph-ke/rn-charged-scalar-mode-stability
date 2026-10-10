module

public import Mathlib
public import ModeStability.AllAngular.BoundedL

/-!
# Weighted source estimate and absorption in radius

Source: the all-angular research notes in preparation, proof of (6.2).
Cauchy–Schwarz is applied to a continuous upper bound for the multiplier;
no continuity of its piecewise definition at a turning point is required.
-/

public section

open Set MeasureTheory Complex

namespace ModeStability.AllAngular.P61

@[expose] noncomputable def blr_energy (s : Set ℝ) (t : ℝ → ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ r in s, ‖f r‖ ^ 2 * t r

theorem blr_weighted_cs {i₁ i₂ B : ℝ} {F MU : ℝ → ℂ} {H t : ℝ → ℝ}
    (ht : ContinuousOn t (Icc i₁ i₂))
    (ht0 : ∀ r ∈ Icc i₁ i₂, 0 ≤ t r)
    (hH : ContinuousOn H (Icc i₁ i₂))
    (hH0 : ∀ r ∈ Icc i₁ i₂, 0 ≤ H r)
    (hF : AEStronglyMeasurable F (volume.restrict (Icc i₁ i₂)))
    (hF2 : IntegrableOn (fun r => ‖F r‖ ^ 2 * t r) (Icc i₁ i₂))
    (hMU : ∀ r ∈ Icc i₁ i₂, ‖MU r‖ ≤ H r)
    (hB : 0 ≤ B)
    (hsource : B = -(∫ r in Icc i₁ i₂, F r * (starRingEnd ℂ) (MU r) * (t r : ℂ)).re) :
    B ^ 2 ≤ blr_energy (Icc i₁ i₂) t F * (∫ r in Icc i₁ i₂, H r ^ 2 * t r) := by
  let μ := volume.restrict (Icc i₁ i₂)
  let f := fun r => ‖F r‖ * Real.sqrt (t r)
  let g := fun r => H r * Real.sqrt (t r)
  have htm := ht.sqrt.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have hfm : AEStronglyMeasurable f μ := hF.norm.mul htm
  have hgm : AEStronglyMeasurable g μ := (hH.mul ht.sqrt).aestronglyMeasurable measurableSet_Icc
  have hf2 : Integrable (fun r => f r ^ 2) μ := by
    apply hF2.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt (ht0 r hr)]
  have hg2 : Integrable (fun r => g r ^ 2) μ := by
    apply ((hH.pow 2).mul ht).integrableOn_Icc.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (ht0 r hr)]
  have hfLp : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm).mpr hf2
  have hgLp : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgm).mpr hg2
  have hprod : Integrable (fun r => ‖F r‖ * H r * t r) μ := by
    apply (hfLp.integrable_mul hgLp).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp [f, g]
    calc
      _ = ‖F r‖ * H r * Real.sqrt (t r) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (ht0 r hr)]
  have hb : B ≤ ∫ r, ‖F r‖ * H r * t r ∂μ := by
    rw [hsource]
    apply ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans
    apply norm_integral_le_of_norm_le hprod
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [norm_mul, norm_mul, norm_conj, norm_real, Real.norm_of_nonneg (ht0 r hr)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hMU r hr) (norm_nonneg _)) (ht0 r hr)
  have hcs := bl_integral_product_le hfm hgm hf2 hg2
  have he₁ : (∫ r, ‖f r‖ * ‖g r‖ ∂μ) = ∫ r, ‖F r‖ * H r * t r ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp [f, g]
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)),
      abs_of_nonneg (mul_nonneg (hH0 r hr) (Real.sqrt_nonneg _))]
    calc
      _ = ‖F r‖ * H r * Real.sqrt (t r) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (ht0 r hr)]
  have he₂ : (∫ r, f r ^ 2 ∂μ) = blr_energy (Icc i₁ i₂) t F := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt (ht0 r hr)]
  have he₃ : (∫ r, g r ^ 2 ∂μ) = ∫ r in Icc i₁ i₂, H r ^ 2 * t r := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (ht0 r hr)]
  rw [he₁, he₂, he₃] at hcs
  have hF0 : 0 ≤ blr_energy (Icc i₁ i₂) t F :=
    setIntegral_nonneg measurableSet_Icc fun r hr => mul_nonneg (sq_nonneg _) (ht0 r hr)
  have hH2 : 0 ≤ ∫ r in Icc i₁ i₂, H r ^ 2 * t r :=
    setIntegral_nonneg measurableSet_Icc fun r hr => mul_nonneg (sq_nonneg _) (ht0 r hr)
  have hs := (sq_le_sq₀ hB (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
    (hb.trans hcs)
  simpa only [mul_pow, Real.sq_sqrt hF0, Real.sq_sqrt hH2] using hs

theorem blr_energy_mono {s t : Set ℝ} {v : ℝ → ℝ} {f : ℝ → ℂ}
    (hi : IntegrableOn (fun r => ‖f r‖ ^ 2 * v r) t)
    (hv : ∀ r ∈ t, 0 ≤ v r) (ht : MeasurableSet t) (hst : s ⊆ t) :
    blr_energy s v f ≤ blr_energy t v f := by
  apply setIntegral_mono_set hi
    (ae_restrict_of_forall_mem ht fun r hr => mul_nonneg (sq_nonneg _) (hv r hr))
  exact Filter.Eventually.of_forall fun r => hst (a := r)

theorem blr_energy_estimate {a b i₁ i₂ m A Z₀ Γ K₁ L₀ L B E : ℝ}
    {U V Z F MU : ℝ → ℂ} {t : ℝ → ℝ}
    (hI : Icc i₁ i₂ ⊆ Icc a b)
    (hm : 0 < m) (hA : 0 ≤ A) (hZ₀ : 0 ≤ Z₀) (hΓ : 0 ≤ Γ) (hK₁ : 0 ≤ K₁)
    (hL : 0 ≤ L) (hLmax : L ≤ L₀) (hE : 0 ≤ E)
    (hUc : ContinuousOn U (Icc a b)) (hVc : ContinuousOn V (Icc a b))
    (hZc : ContinuousOn Z (Icc a b)) (ht : ContinuousOn t (Icc a b))
    (ht0 : ∀ r ∈ Icc a b, 0 ≤ t r)
    (hUE : blr_energy (Icc a b) t U ≤ A * E)
    (hZE : blr_energy (Icc a b) t Z ≤ Z₀ * E)
    (hV : ∀ r ∈ Icc a b, ‖V r‖ ≤ ‖Z r‖ + K₁ * ‖U r‖)
    (hbulk : m * E ≤ B)
    (hF : AEStronglyMeasurable F (volume.restrict (Icc i₁ i₂)))
    (hF2 : IntegrableOn (fun r => ‖F r‖ ^ 2 * t r) (Icc i₁ i₂))
    (hMU : ∀ r ∈ Icc i₁ i₂, ‖MU r‖ ≤ ‖U r‖ + 2 * Γ * ‖Z r‖)
    (hsource : B = -(∫ r in Icc i₁ i₂, F r * (starRingEnd ℂ) (MU r) * (t r : ℂ)).re) :
    B + blr_energy (Icc i₁ i₂) t V + (1 + L) * blr_energy (Icc i₁ i₂) t U ≤
      (1 + (2 * Z₀ + (2 * K₁ ^ 2 + 1 + L₀) * A) / m) *
        ((2 * A + 8 * Γ ^ 2 * Z₀) / m) * blr_energy (Icc i₁ i₂) t F := by
  let T := 2 * Z₀ + (2 * K₁ ^ 2 + 1 + L₀) * A
  let R := 2 * A + 8 * Γ ^ 2 * Z₀
  have hUi := ((hUc.norm.pow 2).mul ht).integrableOn_Icc (μ := volume)
  have hZi := ((hZc.norm.pow 2).mul ht).integrableOn_Icc (μ := volume)
  have hVi := ((hVc.norm.pow 2).mul ht).integrableOn_Icc (μ := volume)
  have hUl := (blr_energy_mono hUi ht0 measurableSet_Icc hI).trans hUE
  have hZl := (blr_energy_mono hZi ht0 measurableSet_Icc hI).trans hZE
  have hVl : blr_energy (Icc i₁ i₂) t V ≤ (2 * Z₀ + 2 * K₁ ^ 2 * A) * E := by
    have hs : ∀ r ∈ Icc a b, ‖V r‖ ^ 2 * t r ≤
        2 * (‖Z r‖ ^ 2 * t r) + 2 * K₁ ^ 2 * (‖U r‖ ^ 2 * t r) := by
      intro r hr
      have hh := (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ ‖Z r‖ + K₁ * ‖U r‖ by positivity)).mpr
        (hV r hr)
      have hsq : ‖V r‖ ^ 2 ≤ 2 * ‖Z r‖ ^ 2 + 2 * K₁ ^ 2 * ‖U r‖ ^ 2 := by
        nlinarith only [hh, sq_nonneg (‖Z r‖ - K₁ * ‖U r‖)]
      nlinarith only [mul_le_mul_of_nonneg_right hsq (ht0 r hr)]
    have he := setIntegral_mono_on hVi ((hZi.const_mul 2).add (hUi.const_mul (2 * K₁ ^ 2)))
      measurableSet_Icc hs
    have hadd := integral_add (hZi.const_mul 2) (hUi.const_mul (2 * K₁ ^ 2))
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at he hadd
    rw [hadd, integral_const_mul, integral_const_mul] at he
    have hvlocal := blr_energy_mono hVi ht0 measurableSet_Icc hI
    change blr_energy (Icc a b) t V ≤ 2 * blr_energy (Icc a b) t Z +
      2 * K₁ ^ 2 * blr_energy (Icc a b) t U at he
    nlinarith only [hvlocal.trans he, mul_le_mul_of_nonneg_left hZE (by norm_num : (0 : ℝ) ≤ 2),
      mul_le_mul_of_nonneg_left hUE (show 0 ≤ 2 * K₁ ^ 2 by positivity)]
  let H := fun r => ‖U r‖ + 2 * Γ * ‖Z r‖
  have hH : ContinuousOn H (Icc i₁ i₂) :=
    (hUc.mono hI).norm.add ((hZc.mono hI).norm.const_mul (2 * Γ))
  have hH0 : ∀ r, 0 ≤ H r := fun r => by dsimp [H]; positivity
  have hHE : (∫ r in Icc i₁ i₂, H r ^ 2 * t r) ≤ R * E := by
    have hUil := hUi.mono_set hI
    have hZil := hZi.mono_set hI
    have hh := setIntegral_mono_on ((hH.pow 2).mul (ht.mono hI)).integrableOn_Icc
      ((hUil.const_mul 2).add (hZil.const_mul (8 * Γ ^ 2))) measurableSet_Icc
      (fun r hr => by
        change H r ^ 2 * t r ≤ 2 * (‖U r‖ ^ 2 * t r) + 8 * Γ ^ 2 * (‖Z r‖ ^ 2 * t r)
        have hs : H r ^ 2 ≤ 2 * ‖U r‖ ^ 2 + 8 * Γ ^ 2 * ‖Z r‖ ^ 2 := by
          dsimp [H]
          nlinarith only [sq_nonneg (‖U r‖ - 2 * Γ * ‖Z r‖)]
        nlinarith only [mul_le_mul_of_nonneg_right hs (ht0 r (hI hr))])
    have hadd := integral_add (hUil.const_mul 2) (hZil.const_mul (8 * Γ ^ 2))
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at hh hadd
    rw [hadd, integral_const_mul, integral_const_mul] at hh
    change (∫ r in Icc i₁ i₂, H r ^ 2 * t r) ≤
      2 * blr_energy (Icc i₁ i₂) t U + 8 * Γ ^ 2 * blr_energy (Icc i₁ i₂) t Z at hh
    dsimp [R]
    nlinarith only [hh, mul_le_mul_of_nonneg_left hUl (by norm_num : (0 : ℝ) ≤ 2),
      mul_le_mul_of_nonneg_left hZl (show 0 ≤ 8 * Γ ^ 2 by positivity)]
  have hB : 0 ≤ B := (mul_nonneg hm.le hE).trans hbulk
  have hF0 : 0 ≤ blr_energy (Icc i₁ i₂) t F :=
    setIntegral_nonneg measurableSet_Icc fun r hr => mul_nonneg (sq_nonneg _) (ht0 r (hI hr))
  have hbs := blr_weighted_cs (ht.mono hI) (fun r hr => ht0 r (hI hr)) hH
    (fun r _ => hH0 r) hF hF2 hMU hB hsource
  have hsourceSq : B ^ 2 ≤ blr_energy (Icc i₁ i₂) t F * R * E :=
    hbs.trans (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hHE hF0)
  have hT : 0 ≤ T := by dsimp [T]; have : 0 ≤ L₀ := hL.trans hLmax; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hfinal := bl_absorb hm hR hT hE hF0 hbulk hsourceSq
  have hlocal : blr_energy (Icc i₁ i₂) t V + (1 + L) * blr_energy (Icc i₁ i₂) t U ≤ T * E := by
    have h₁ := mul_le_mul_of_nonneg_left hUl (show 0 ≤ 1 + L by linarith)
    have h₂ := mul_le_mul_of_nonneg_right hLmax (mul_nonneg hA hE)
    dsimp [T]
    nlinarith only [hVl, h₁, h₂]
  change _ ≤ (1 + T / m) * (R / m) * blr_energy (Icc i₁ i₂) t F
  linarith only [hfinal, hlocal]

end ModeStability.AllAngular.P61

end
