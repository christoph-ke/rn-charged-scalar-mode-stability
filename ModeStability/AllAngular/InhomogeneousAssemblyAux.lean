module

public import Mathlib
public import ModeStability.AllAngular.LargeL
public import ModeStability.AllAngular.Prop61Interface

/-!
# Weighted integral estimates for the assembly of Proposition 6.1

Source: the all-angular research notes in preparation, paper p. 8.
The square root of `dx/dr` converts the radial source pairing and energies
to the measure-space estimate in `LargeL`.
-/

public section

open Complex Set Filter MeasureTheory
open scoped ComplexConjugate

namespace ModeStability.AllAngular

private theorem ia_memLp_top {f : ℝ → ℂ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) : MemLp f ⊤ (volume.restrict (Icc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hf.norm
  apply memLp_top_of_bound (hf.aestronglyMeasurable measurableSet_Icc) C
  exact (ae_restrict_mem measurableSet_Icc).mono fun x hx => hC (mem_image_of_mem _ hx)

private theorem ia_g_continuous {M Q e ω a b : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (ha : outerHorizon M Q < a) : ContinuousOn (normalizationG M Q e ω) (Icc a b) := by
  intro r hr
  obtain ⟨c, hd, -, -⟩ := NormalizationFacts.gauge_facts (e := e) (ω := ω) hM hQ
    (ha.trans_le hr.1)
  exact hd.self_of_nhds.continuousAt.continuousWithinAt

private theorem ia_w_pos {M Q e ω r : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hr : outerHorizon M Q < r) : 0 < P61.wR M Q e ω r := by
  obtain ⟨-, -, hg, -⟩ := NormalizationFacts.gauge_facts (e := e) (ω := ω) hM hQ hr
  exact one_div_pos.mpr (mul_pos (NormalizationFacts.delta_pos_of_outerHorizon_lt hr)
    (pow_pos hg 2))

private theorem ia_w_continuous {M Q e ω a b : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (ha : outerHorizon M Q < a) : ContinuousOn (P61.wR M Q e ω) (Icc a b) := by
  have hd : Continuous (delta M Q) := by unfold delta; fun_prop
  exact continuousOn_const.div (hd.continuousOn.mul ((ia_g_continuous hM hQ ha).pow 2))
    (fun r hr => (mul_pos (NormalizationFacts.delta_pos_of_outerHorizon_lt
      (ha.trans_le hr.1)) (pow_pos (NormalizationFacts.gauge_facts hM hQ
        (ha.trans_le hr.1)).choose_spec.2.1 2)).ne')

private theorem ia_weighted_norm (w : ℝ) (z : ℂ) (hw : 0 ≤ w) :
    ‖(Real.sqrt w : ℂ) * z‖ ^ 2 = ‖z‖ ^ 2 * w := by
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt hw]
  ring

private theorem ia_weighted_pair (w : ℝ) (F U : ℂ) (hw : 0 ≤ w) :
    ((Real.sqrt w : ℂ) * F) * conj ((Real.sqrt w : ℂ) * U) = F * conj U * (w : ℂ) := by
  simp only [map_mul, conj_ofReal]
  have hs : (Real.sqrt w : ℂ) ^ 2 = (w : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt hw]
  calc
    _ = (Real.sqrt w : ℂ) ^ 2 * (F * conj U) := by ring
    _ = _ := by rw [hs]; ring

private theorem ia_abstract_estimate {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F U X : α → ℂ} {B : ENNReal} {c L L₀ : ℝ}
    (hF : MemLp F 2 μ) (hU : MemLp U 2 μ) (hX : AEStronglyMeasurable X μ)
    (hB : B < ⊤) (hc : 0 < c) (hL₀ : 1 ≤ L₀) (hL : L₀ ≤ L)
    (hsource : B.toReal = -(∫ x, F x * conj (U x) ∂μ).re)
    (hcoerc : (∫⁻ x, ENNReal.ofReal (‖X x‖ ^ 2 + c * L * ‖U x‖ ^ 2) ∂μ) ≤ B) :
    B + (∫⁻ x, ENNReal.ofReal (‖X x‖ ^ 2) ∂μ) +
      ENNReal.ofReal (1 + L) * (∫⁻ x, ENNReal.ofReal (‖U x‖ ^ 2) ∂μ) ≤
      ENNReal.ofReal (4 * (1 + 1 / c) ^ 2 / (1 + L)) *
        (∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2) ∂μ) := by
  have hcL : 0 ≤ c * L := mul_nonneg hc.le (by linarith)
  have hxi : Integrable (fun x => ‖X x‖ ^ 2) μ := by
    refine ⟨hX.norm.pow 2, (hasFiniteIntegral_iff_ofReal
      (ae_of_all _ fun _ => sq_nonneg _)).mpr ?_⟩
    apply lt_of_le_of_lt _ hB
    exact (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
      (le_add_of_nonneg_right (mul_nonneg hcL (sq_nonneg _)))).trans hcoerc
  have hui := hU.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hfi := hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hxn : 0 ≤ ∫ x, ‖X x‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hun : 0 ≤ ∫ x, ‖U x‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hfn : 0 ≤ ∫ x, ‖F x‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hLn : 0 ≤ 1 + L := by linarith
  have hcoe : ∀ {f : α → ℝ}, Integrable f μ → (∀ x, 0 ≤ f x) →
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ENNReal.ofReal (∫ x, f x ∂μ) :=
    fun hi hn => (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)).symm
  have hcoercR : (∫ x, ‖X x‖ ^ 2 ∂μ) + c * L * (∫ x, ‖U x‖ ^ 2 ∂μ) ≤ B.toReal := by
    rw [hcoe (f := fun x => ‖X x‖ ^ 2 + c * L * ‖U x‖ ^ 2)
      (hxi.add (hui.const_mul (c * L)))
      (fun x => add_nonneg (sq_nonneg _) (mul_nonneg hcL (sq_nonneg _))),
      integral_add hxi (hui.const_mul _), integral_const_mul] at hcoerc
    have ht := ENNReal.toReal_mono hB.ne hcoerc
    simpa only [ENNReal.toReal_ofReal (add_nonneg (integral_nonneg fun _ => sq_nonneg _)
      (mul_nonneg hcL (integral_nonneg fun _ => sq_nonneg _)))] using ht
  have hh := largeL_integral_estimate hF hU hc hL₀ hL hsource hcoercR
  rw [hcoe hxi (fun _ => sq_nonneg _), hcoe hui (fun _ => sq_nonneg _),
    hcoe hfi (fun _ => sq_nonneg _), ← ENNReal.ofReal_toReal hB.ne,
    ← ENNReal.ofReal_mul hLn,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hxn,
    ← ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg hxn) (mul_nonneg hLn hun),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hh

/-- The large-angular estimate in the exact radial interface quantities. Finiteness
of the derivative energy follows from domination by the finite forbidden bulk. -/
theorem inhomogeneous_largeL_estimate {M Q e ω L₀ c L ρ₁ ρ₂ : ℝ}
    {S R : ℝ → ℂ} (hM : 0 < M) (hQ : |Q| ≤ M) (hρ : outerHorizon M Q < ρ₁)
    (hc : 0 < c) (hL₀ : 1 ≤ L₀) (hL : L₀ ≤ L)
    (hS : MemLp S 2 (volume.restrict (Icc ρ₁ ρ₂)))
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    (hid : P61.SourceIdentityR M Q e ω L ρ₁ ρ₂ R S)
    (hfb : Icc ρ₁ ρ₂ ⊆ P61.setFb M Q e ω L)
    (hcoef : ∀ r ∈ Icc ρ₁ ρ₂, c * L ≤ normalizationG M Q e ω r ^ 4 *
      (L * delta M Q r - radialK e ω r ^ 2)) :
    P61.lhsR M Q e ω L ρ₁ ρ₂ R ≤
      ENNReal.ofReal (4 * (1 + 1 / c) ^ 2 / (1 + L)) *
        P61.srcNormR M Q e ω ρ₁ ρ₂ S := by
  let μ := volume.restrict (Icc ρ₁ ρ₂)
  let w := P61.wR M Q e ω
  let F : ℝ → ℂ := fun r => (Real.sqrt (w r) : ℂ) * P61.srcR M Q e ω S r
  let U : ℝ → ℂ := fun r => (Real.sqrt (w r) : ℂ) * P61.uR M Q e ω R r
  let X : ℝ → ℂ := fun r => (Real.sqrt (w r) : ℂ) * P61.uxR M Q e ω R r
  have hw : ∀ r ∈ Icc ρ₁ ρ₂, 0 ≤ w r := fun r hr => (ia_w_pos hM hQ
    (hρ.trans_le hr.1)).le
  have hg := ia_g_continuous (e := e) (ω := ω) (b := ρ₂) hM hQ hρ
  have hδ : Continuous (delta M Q) := by unfold delta; fun_prop
  have hwC := ia_w_continuous (e := e) (ω := ω) (b := ρ₂) hM hQ hρ
  have hsC : ContinuousOn (fun r => (Real.sqrt (w r) : ℂ)) (Icc ρ₁ ρ₂) :=
    continuous_ofReal.comp_continuousOn hwC.sqrt
  have hUC : ContinuousOn (P61.uR M Q e ω R) (Icc ρ₁ ρ₂) := by
    apply ContinuousOn.div (fun r hr => (hR r (hρ.trans_le hr.1)).continuousAt.continuousWithinAt)
      (continuous_ofReal.comp_continuousOn hg)
    intro r hr
    exact ofReal_ne_zero.mpr (NormalizationFacts.gauge_facts hM hQ
      (hρ.trans_le hr.1)).choose_spec.2.1.ne'
  have hU : MemLp U 2 μ := (ia_memLp_top (hsC.mul hUC)).mono_exponent (by simp)
  have hF : MemLp F 2 μ := by
    have ht := (ia_memLp_top (hsC.mul (continuous_ofReal.comp_continuousOn
      (hδ.continuousOn.mul (hg.pow 3))))).mul (r := 2) hS
    change MemLp (fun r => ((Real.sqrt (w r) : ℂ) *
      ((delta M Q r * normalizationG M Q e ω r ^ 3 : ℝ) : ℂ)) * S r) 2 μ at ht
    simpa only [F, P61.srcR, mul_assoc] using ht
  have hX : AEStronglyMeasurable X μ := by
    have hdC : ContinuousOn (fun r => ((delta M Q r * normalizationG M Q e ω r ^ 2 : ℝ) : ℂ))
        (Icc ρ₁ ρ₂) := continuous_ofReal.comp_continuousOn (hδ.continuousOn.mul (hg.pow 2))
    exact (hsC.aestronglyMeasurable measurableSet_Icc).mul
      ((hdC.aestronglyMeasurable measurableSet_Icc).mul (aestronglyMeasurable_deriv _ _))
  have hmult : ∀ r ∈ Icc ρ₁ ρ₂, P61.multR M Q e ω L R r = P61.uR M Q e ω R r := by
    intro r hr
    have hf := (hfb hr).2
    have hh : r ∉ P61.setAH M Q e ω L := fun h => not_lt_of_ge hf h.2.2
    have hi : r ∉ P61.setAI M Q e ω L := fun h => not_lt_of_ge hf h.2
    simp only [P61.multR, ite_eq_right hh, ite_eq_right hi]
  have hsource : (P61.bulkR M Q e ω L R).toReal = -(∫ r, F r * conj (U r) ∂μ).re := by
    rw [hid.2]
    congr 2
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [hmult r hr]
    exact (ia_weighted_pair (w r) (P61.srcR M Q e ω S r) (P61.uR M Q e ω R r)
      (hw r hr)).symm
  have hcoerc : (∫⁻ r, ENNReal.ofReal (‖X r‖ ^ 2 + c * L * ‖U r‖ ^ 2) ∂μ) ≤
      P61.bulkR M Q e ω L R := by
    calc
      _ ≤ ∫⁻ r in Icc ρ₁ ρ₂, ENNReal.ofReal ((‖P61.uxR M Q e ω R r‖ ^ 2 +
          normalizationG M Q e ω r ^ 4 * (L * delta M Q r - radialK e ω r ^ 2) *
            ‖P61.uR M Q e ω R r‖ ^ 2) * w r) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        apply ENNReal.ofReal_le_ofReal
        change ‖(Real.sqrt (w r) : ℂ) * P61.uxR M Q e ω R r‖ ^ 2 +
          c * L * ‖(Real.sqrt (w r) : ℂ) * P61.uR M Q e ω R r‖ ^ 2 ≤ _
        rw [ia_weighted_norm _ _ (hw r hr), ia_weighted_norm _ _ (hw r hr)]
        have hh := mul_le_mul_of_nonneg_right (hcoef r hr)
          (mul_nonneg (sq_nonneg ‖P61.uR M Q e ω R r‖) (hw r hr))
        nlinarith only [hh]
      _ ≤ ∫⁻ r in P61.setFb M Q e ω L, ENNReal.ofReal ((‖P61.uxR M Q e ω R r‖ ^ 2 +
          normalizationG M Q e ω r ^ 4 * (L * delta M Q r - radialK e ω r ^ 2) *
            ‖P61.uR M Q e ω R r‖ ^ 2) * w r) := lintegral_mono_set hfb
      _ ≤ _ := (le_add_of_nonneg_left zero_le).trans
        (le_add_of_nonneg_right zero_le)
  have hh := ia_abstract_estimate hF hU hX hid.1 hc hL₀ hL hsource hcoerc
  have hnorm : ∀ Z : ℝ → ℂ,
      (∫⁻ r, ENNReal.ofReal (‖(Real.sqrt (w r) : ℂ) * Z r‖ ^ 2) ∂μ) =
        ∫⁻ r in Icc ρ₁ ρ₂, ENNReal.ofReal (‖Z r‖ ^ 2 * w r) := by
    intro Z
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [ia_weighted_norm _ _ (hw r hr)]
  simpa only [F, U, X, hnorm, P61.lhsR, P61.srcNormR] using hh

end ModeStability.AllAngular

end
