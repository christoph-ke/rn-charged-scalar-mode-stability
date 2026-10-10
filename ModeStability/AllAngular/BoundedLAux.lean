module

public import Mathlib

/-!
# Compact interval estimates for the bounded angular regime

Source: the all-angular research notes in preparation, Proposition 6.1,
(6.4). Squared local L² norms are real Bochner integrals. These lemmas prove
Cauchy–Schwarz, the interval oscillation bound, and the cutoff identity directly;
none of these estimates is an assumption of the final resolvent theorem.
-/

public section

open Set MeasureTheory Complex

namespace ModeStability.AllAngular

/-- The squared L² norm on a measurable coordinate set. Integrability is supplied
explicitly whenever this definition is used in an estimate. -/
@[expose] noncomputable def boundedLEnergy (s : Set ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ x in s, ‖f x‖ ^ 2

/-- Nonnegativity does not require integrability. -/
theorem boundedLEnergy_nonneg (s : Set ℝ) (f : ℝ → ℂ) :
    0 ≤ boundedLEnergy s f := integral_nonneg fun _ => sq_nonneg _

/-- Cauchy–Schwarz for real functions, in square-root form. -/
theorem bl_integral_product_le {μ : Measure ℝ} {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f) (g := g) Real.HolderConjugate.two_two
    (by simpa using (memLp_two_iff_integrable_sq hf).2 hf2)
    (by simpa using (memLp_two_iff_integrable_sq hg).2 hg2)
  simpa only [ENNReal.ofReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    Real.sqrt_eq_rpow, one_div] using h

/-- Monotonicity of the squared local norm under restriction. -/
theorem bl_energy_mono {s t : Set ℝ} {f : ℝ → ℂ}
    (hi : IntegrableOn (fun x => ‖f x‖ ^ 2) t) (hst : s ⊆ t) :
    boundedLEnergy s f ≤ boundedLEnergy t f :=
  setIntegral_mono_set hi (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall fun x => show x ∈ s → x ∈ t from hst (a := x))

/-- Fundamental theorem of calculus and Cauchy–Schwarz control oscillation on
`[a,b]` using only the derivative's squared local norm. -/
theorem bl_oscillation {a b : ℝ} (hab : a ≤ b) {w : ℝ → ℂ}
    (hw : ∀ x ∈ Icc a b, HasDerivAt w (deriv w x) x)
    (hd : ContinuousOn (deriv w) (Icc a b)) {x : ℝ} (hx : x ∈ Icc a b) :
    ‖w x - w a‖ ≤ Real.sqrt (b - a) * Real.sqrt (boundedLEnergy (Icc a b) (deriv w)) := by
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  have hdi := hd.norm.integrableOn_Icc (μ := volume)
  have hsq := (hd.norm.pow 2).integrableOn_Icc (μ := volume)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := x)
    (fun y hy => hw y (hsub (by simpa [uIcc_of_le hx.1] using hy)))
    ((hd.mono hsub).mono (by rw [uIcc_of_le hx.1])).intervalIntegrable
  calc
    ‖w x - w a‖ = ‖∫ y in a..x, deriv w y‖ := by rw [hFTC]
    _ ≤ ∫ y in a..x, ‖deriv w y‖ := intervalIntegral.norm_integral_le_integral_norm hx.1
    _ = ∫ y in Icc a x, ‖deriv w y‖ := by
      rw [intervalIntegral.integral_of_le hx.1, integral_Icc_eq_integral_Ioc]
    _ ≤ ∫ y in Icc a b, ‖deriv w y‖ :=
      setIntegral_mono_set hdi (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall fun y => show y ∈ Icc a x → y ∈ Icc a b from hsub (a := y))
    _ ≤ Real.sqrt (b - a) * Real.sqrt (boundedLEnergy (Icc a b) (deriv w)) := by
      have h := bl_integral_product_le (μ := volume.restrict (Icc a b))
        (f := fun _ => (1 : ℝ)) (g := fun y => ‖deriv w y‖)
        aestronglyMeasurable_const (hd.norm.aestronglyMeasurable measurableSet_Icc)
        (by simp) hsq
      simpa [boundedLEnergy, Real.volume_Icc, hab, sub_nonneg.2 hab] using h

/-- A bounded real coefficient can be pulled out of a cutoff pairing. -/
theorem bl_cutoff_pairing {j₁ j₂ K : ℝ} {v : ℝ → ℂ} {k φ : ℝ → ℝ}
    (hv : ContinuousOn v (Icc j₁ j₂)) (hk : ContinuousOn k (Icc j₁ j₂))
    (hφ : ContinuousOn φ (Icc j₁ j₂)) (hK0 : 0 ≤ K) (hK : ∀ x ∈ Icc j₁ j₂, |k x| ≤ K) :
    ‖∫ x in Icc j₁ j₂, (k x : ℂ) * v x * (φ x : ℂ)‖ ≤
      K * Real.sqrt (boundedLEnergy (Icc j₁ j₂) v) *
        Real.sqrt (∫ x in Icc j₁ j₂, φ x ^ 2) := by
  have hprod := (hv.norm.mul hφ.norm).integrableOn_Icc (μ := volume)
  calc
    _ ≤ ∫ x in Icc j₁ j₂, ‖(k x : ℂ) * v x * (φ x : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in Icc j₁ j₂, K * (‖v x‖ * ‖φ x‖) := by
      apply setIntegral_mono_on
        (((continuous_ofReal.comp_continuousOn hk).mul hv |>.mul
          (continuous_ofReal.comp_continuousOn hφ)).norm.integrableOn_Icc (μ := volume))
        (hprod.const_mul K) measurableSet_Icc
      intro x hx
      change ‖(k x : ℂ) * v x * (φ x : ℂ)‖ ≤ K * (‖v x‖ * ‖φ x‖)
      simp only [norm_mul, norm_real, Real.norm_eq_abs]
      nlinarith [mul_le_mul_of_nonneg_right (hK x hx) (mul_nonneg (norm_nonneg (v x))
        (abs_nonneg (φ x)))]
    _ = K * (∫ x in Icc j₁ j₂, ‖v x‖ * ‖φ x‖) := integral_const_mul _ _
    _ ≤ _ := by
      have h := bl_integral_product_le
        (hv.norm.aestronglyMeasurable measurableSet_Icc)
        (hφ.aestronglyMeasurable measurableSet_Icc)
        ((hv.norm.pow 2).integrableOn_Icc (μ := volume))
        ((hφ.pow 2).integrableOn_Icc (μ := volume))
      simp only [norm_norm] at h
      simpa [boundedLEnergy, mul_assoc] using mul_le_mul_of_nonneg_left h hK0

/-- A positive weighted test detects the otherwise uncontrolled constant part.
The upper bound on the weight cancels out: only its sign and mass are used. -/
theorem bl_weighted_constant {j₁ j₂ a κ δ r : ℝ}
    {w : ℝ → ℂ} {ρ : ℝ → ℝ}
    (hw : ContinuousOn w (Icc j₁ j₂)) (hρ : ContinuousOn ρ (Icc j₁ j₂))
    (hρ0 : ∀ x ∈ Icc j₁ j₂, 0 ≤ ρ x) (hκ : 0 < κ)
    (hmass : κ ≤ ∫ x in Icc j₁ j₂, ρ x) (hr : 0 ≤ r)
    (hosc : ∀ x ∈ Icc j₁ j₂, ‖w x - w a‖ ≤ δ)
    (hpair : ‖∫ x in Icc j₁ j₂, (ρ x : ℂ) * w x‖ ≤ r) :
    ‖w a‖ ≤ δ + r / κ := by
  let A := ∫ x in Icc j₁ j₂, ρ x
  have hA : 0 < A := hκ.trans_le hmass
  have hcρ := continuous_ofReal.comp_continuousOn hρ
  have herr : ‖∫ x in Icc j₁ j₂, (ρ x : ℂ) * (w x - w a)‖ ≤ δ * A := by
    calc
      _ ≤ ∫ x in Icc j₁ j₂, δ * ρ x := by
        apply norm_integral_le_of_norm_le (hρ.integrableOn_Icc.const_mul δ)
        apply (ae_restrict_iff' measurableSet_Icc).2
        exact Filter.Eventually.of_forall fun x hx => by
          rw [norm_mul, norm_real, Real.norm_of_nonneg (hρ0 x hx)]
          nlinarith [mul_le_mul_of_nonneg_left (hosc x hx) (hρ0 x hx)]
      _ = δ * A := integral_const_mul _ _
  have he : (∫ x in Icc j₁ j₂, (ρ x : ℂ) * w x) -
      (∫ x in Icc j₁ j₂, (ρ x : ℂ) * (w x - w a)) = (A : ℂ) * w a := by
    have hs := integral_sub ((hcρ.mul hw).integrableOn_Icc (μ := volume))
      ((hcρ.mul (hw.sub (continuousOn_const (c := w a)))).integrableOn_Icc (μ := volume))
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply] at hs
    rw [← hs]
    simp_rw [show ∀ x, (ρ x : ℂ) * w x - (ρ x : ℂ) * (w x - w a) =
      (ρ x : ℂ) * w a from fun x => by ring]
    rw [integral_mul_const]
    congr 1
    exact Complex.ofRealCLM.integral_comp_comm hρ.integrableOn_Icc
  have hb : A * ‖w a‖ ≤ r + δ * A := by
    calc
      _ = ‖(A : ℂ) * w a‖ := by
        rw [norm_mul, norm_real, Real.norm_of_nonneg hA.le]
      _ = ‖(∫ x in Icc j₁ j₂, (ρ x : ℂ) * w x) -
          (∫ x in Icc j₁ j₂, (ρ x : ℂ) * (w x - w a))‖ := by rw [he]
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add hpair herr)
  by_contra hn
  have hgt : δ + r / κ < ‖w a‖ := lt_of_not_ge hn
  have hq : 0 ≤ r / κ := div_nonneg hr hκ.le
  have hdiff : 0 ≤ ‖w a‖ - δ := by linarith
  have hl := mul_le_mul_of_nonneg_right hmass hdiff
  have hdiv := (div_mul_cancel₀ r hκ.ne').symm
  nlinarith

/-- The final scalar absorption, including the case of zero bulk. -/
theorem bl_absorb {B E S m R T : ℝ} (hm : 0 < m) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hE : 0 ≤ E) (hS : 0 ≤ S) (hbulk : m * E ≤ B) (hsource : B ^ 2 ≤ S * R * E) :
    B + T * E ≤ (1 + T / m) * (R / m) * S := by
  have hB : 0 ≤ B := (mul_nonneg hm.le hE).trans hbulk
  have hEB : E ≤ B / m := (le_div_iff₀ hm).2 (by nlinarith)
  have hBS : B ≤ R / m * S := by
    rcases hB.eq_or_lt with hzero | hpos
    · rw [← hzero]
      positivity
    · have h₁ := mul_le_mul_of_nonneg_left hsource hm.le
      have h₂ := mul_le_mul_of_nonneg_left hbulk (mul_nonneg hS hR)
      have hcancel : m * B ≤ S * R := (mul_le_mul_iff_right₀ hpos).mp (by nlinarith [h₁, h₂])
      calc
        B ≤ S * R / m := (le_div_iff₀ hm).2 (by nlinarith only [hcancel])
        _ = R / m * S := by ring
  calc
    B + T * E ≤ B + T * (B / m) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hEB hT)
    _ = (1 + T / m) * B := by ring
    _ ≤ (1 + T / m) * (R / m * S) := mul_le_mul_of_nonneg_left hBS (by positivity)
    _ = _ := by ring

/-- Dephasing by any real primitive of the nonnegative allowed frequency. -/
@[expose] noncomputable def boundedLDephase (θ : ℝ → ℝ) (U : ℝ → ℂ) (x : ℝ) : ℂ :=
  exp (-(θ x : ℂ) * I) * U x

/-- Dephasing preserves the pointwise norm. -/
theorem bl_dephase_norm (θ : ℝ → ℝ) (U : ℝ → ℂ) (x : ℝ) :
    ‖boundedLDephase θ U x‖ = ‖U x‖ := by
  have he : ‖exp (-(θ x : ℂ) * I)‖ = 1 := by
    simpa only [ofReal_neg] using norm_exp_ofReal_mul_I (-θ x)
  simp only [boundedLDephase, norm_mul, he, one_mul]

end ModeStability.AllAngular

end
