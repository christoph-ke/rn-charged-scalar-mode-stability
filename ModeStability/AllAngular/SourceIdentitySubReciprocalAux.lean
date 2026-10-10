module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentitySubReciprocalEndpoints
public import ModeStability.AllAngular.SourceIdentityRSubReciprocalCurrent
public import ModeStability.AllAngular.SourceIdentityRSubReciprocalTurning
public import ModeStability.AllAngular.SourceIdentityRGlobal

/-!
# Radial densities and current equations for the reciprocal source identity

Source: the all-angular research notes in preparation, pp. 7–8, (6.3).
The densities use the shared interface verbatim. Their regularity, positivity,
and integrated current equations allow the abstract three-region gluing lemma
to apply to a source in L², including coincident turning points.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

open P61 CoordinateCoefficients

noncomputable def ssr_b (M Q e ω L σ : ℝ) (R : ℝ → ℂ) : ℝ → ℝ := fun r =>
  akR M Q e ω L r *
    ‖uxR M Q e ω R r + (σ : ℂ) * (effectiveK M Q e ω L r : ℂ) * I * uR M Q e ω R r‖ ^ 2 *
    wR M Q e ω r

noncomputable def ssr_bm (M Q e ω L : ℝ) (R : ℝ → ℂ) : ℝ → ℝ := fun r =>
  (‖uxR M Q e ω R r‖ ^ 2 + normalizationG M Q e ω r ^ 4 *
    (L * delta M Q r - radialK e ω r ^ 2) * ‖uR M Q e ω R r‖ ^ 2) * wR M Q e ω r

noncomputable def ssr_J (M Q e ω L σ : ℝ) (R : ℝ → ℂ) : ℝ → ℝ := fun r =>
  -(effectiveK M Q e ω L r / khxR M Q e ω L r) *
    ‖uxR M Q e ω R r + (σ : ℂ) * (effectiveK M Q e ω L r : ℂ) * I * uR M Q e ω R r‖ ^ 2 -
    (uxR M Q e ω R r * (starRingEnd ℂ) (uR M Q e ω R r)).re

noncomputable def ssr_Jm (M Q e ω : ℝ) (R : ℝ → ℂ) : ℝ → ℝ := fun r =>
  -(uxR M Q e ω R r * (starRingEnd ℂ) (uR M Q e ω R r)).re

noncomputable def ssr_src (M Q e ω L : ℝ) (R S : ℝ → ℂ) : ℝ → ℝ := fun r =>
  (srcR M Q e ω S r * (starRingEnd ℂ) (multR M Q e ω L R r) * (wR M Q e ω r : ℂ)).re

/-- The source pairing is integrable on the whole line and vanishes off its support. -/
theorem ssr_source_integrable {M Q e ω ρ₁ ρ₂ L : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hL : 0 ≤ L)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) :
    Integrable (ssr_src M Q e ω L R S) ∧
      (∀ r, r ∉ Icc ρ₁ ρ₂ → ssr_src M Q e ω L R S r = 0) ∧
      (∀ r, r ∉ Ioi (outerHorizon M Q) → ssr_src M Q e ω L R S r = 0) := by
  have hz : ∀ r, r ∉ Icc ρ₁ ρ₂ → ssr_src M Q e ω L R S r = 0 := by
    intro r hr
    simp [ssr_src, srcR, hP.1 r hr]
  have hi : IntegrableOn (ssr_src M Q e ω L R S) (Icc ρ₁ ρ₂) :=
    reCLM.integrable_comp (integrableOn_src_mul_multR h hL hP)
  refine ⟨hi.integrable_of_forall_notMem_eq_zero hz, hz, ?_⟩
  intro r hr
  apply hz r
  intro hm
  exact hr (h.2.2.2.2.2.1.trans_le hm.1)

private theorem ssr_weight_pos {M Q e ω r : ℝ}
    (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) (hr : outerHorizon M Q < r) :
    0 < wR M Q e ω r := by
  unfold wR
  rw [source_sub_reciprocal_normalization hQ hN]
  exact one_div_pos.mpr (mul_pos (delta_pos hQ hr) (sq_pos_of_pos (staticSolution_pos hQ hr)))

/-- Allowed bulk densities are continuous and nonnegative on either allowed region. -/
theorem ssr_allowed_density {M Q e ω ρ₁ ρ₂ L σ : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) (hL : 0 ≤ L)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI)
    {r : ℝ} (hr : outerHorizon M Q < r) (hp : L * delta M Q r < radialK e ω r ^ 2) :
    ContinuousAt (ssr_b M Q e ω L σ R) r ∧ 0 ≤ ssr_b M Q e ω L σ R r := by
  obtain ⟨hk, hfx, hE⟩ := source_sub_reciprocal_coefficient_props h.1 hQ h.2.2.2.1
    hL (ssr_range_geometry h).1 hN hr hp
  have hd : ContDiffAt ℝ 1 (fun r => delta M Q r * normalizationG M Q e ω r ^ 2) r := by
    rw [source_sub_reciprocal_normalization hQ hN]
    exact ((contDiff_delta M Q).contDiffAt.mul
      ((contDiffAt_staticSolution hQ hr).pow 2)).of_le (by norm_num)
  have hx : ContDiffAt ℝ 1 (khxR M Q e ω L) r :=
    hd.mul (hk.derivWithin (m := 1) (by norm_num))
  have hxx : ContinuousAt (xDeriv M Q (normalizationG M Q e ω) (khxR M Q e ω L)) r :=
    hd.continuousAt.mul (hx.derivWithin (m := 0) (by norm_num)).continuousAt
  have hak : ContinuousAt (akR M Q e ω L) r :=
    ((continuousAt_const.mul (hx.continuousAt.pow 2)).sub
      (hk.continuousAt.mul hxx)).div (hx.continuousAt.pow 2) (pow_ne_zero 2 hfx.ne')
  have hU := (uR_contDiffOn_one h.1 hP.2.2.1).continuousOn.continuousAt (Ioi_mem_nhds hr)
  have hV := (uxR_continuousOn h.1 hP.2.2.1).continuousAt (Ioi_mem_nhds hr)
  have hw := (wR_continuousOn (e := e) (ω := ω) h.1).continuousAt (Ioi_mem_nhds hr)
  refine ⟨?_, ?_⟩
  · unfold ssr_b
    have hkc := hk.continuousAt
    fun_prop
  · exact mul_nonneg (mul_nonneg (div_nonneg hE.le (sq_nonneg _)) (sq_nonneg _))
      (ssr_weight_pos hQ hN hr).le

/-- The middle density is continuous on the exterior and nonnegative in the forbidden set. -/
theorem ssr_forbidden_density {M Q e ω ρ₁ ρ₂ L : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hQ : |Q| < M) (hN : 2 * M ≤ e / ω)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) :
    ContinuousOn (ssr_bm M Q e ω L R) (Ioi (outerHorizon M Q)) ∧
      ∀ r ∈ setFb M Q e ω L, 0 ≤ ssr_bm M Q e ω L R r := by
  have hU := (uR_contDiffOn_one h.1 hP.2.2.1).continuousOn
  have hV := uxR_continuousOn h.1 hP.2.2.1
  have hg := normalizationG_continuousOn (Q := Q) (e := e) (ω := ω) h.1
  have hw := wR_continuousOn (Q := Q) (e := e) (ω := ω) h.1
  have hd : ContinuousOn (delta M Q) (Ioi (outerHorizon M Q)) :=
    (contDiff_delta M Q).continuous.continuousOn
  have hk : ContinuousOn (radialK e ω) (Ioi (outerHorizon M Q)) :=
    (contDiff_radialK e ω).continuous.continuousOn
  refine ⟨?_, ?_⟩
  · unfold ssr_bm
    fun_prop
  · intro r hr
    exact mul_nonneg (add_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (pow_nonneg (le_of_lt (by
        rw [source_sub_reciprocal_normalization hQ hN]
        exact staticSolution_pos hQ hr.1)) 4) (sub_nonneg.mpr hr.2)) (sq_nonneg _)))
      (ssr_weight_pos hQ hN hr.1).le

private theorem ssr_pairing (F Z : ℂ) (w : ℝ) :
    (F * (starRingEnd ℂ) Z * (w : ℂ)).re = w * (F * (starRingEnd ℂ) Z).re := by
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  ring

/-- The allowed current equation in interface notation, with its piecewise multiplier. -/
theorem ssr_allowed_integral {M Q e ω ρ₁ ρ₂ L b c σ : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) (hL : 0 ≤ L)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI)
    (hbc : b ≤ c) (hb : outerHorizon M Q < b) (hc : outerHorizon M Q < c)
    (hreg : (σ = 1 ∧ Icc b c ⊆ setAH M Q e ω L) ∨
      (σ = -1 ∧ Icc b c ⊆ setAI M Q e ω L)) :
    (∫ r in b..c, -ssr_b M Q e ω L σ R r - ssr_src M Q e ω L R S r) =
      ssr_J M Q e ω L σ R c - ssr_J M Q e ω L σ R b := by
  classical
  have hi : uIcc b c = Icc b c := uIcc_of_le hbc
  have hp : ∀ r ∈ uIcc b c, L * delta M Q r < radialK e ω r ^ 2 := by
    intro r hr
    rw [hi] at hr
    rcases hreg with ⟨_, hs⟩ | ⟨_, hs⟩
    · exact (hs hr).2.2
    · exact (hs hr).2
  have ht := source_sub_reciprocal_allowed_integral h.1 hQ h.2.2.2.1 hL
    (ssr_range_geometry h).1 hN hb hc hp (hreg.elim (fun hs => Or.inl hs.1) (fun hs => Or.inr hs.1))
    hP.2.2.1.1 (fun x hx y hy => (hP.2.2.1.2 x hx y hy).1)
    (fun x hx y hy => (hP.2.2.1.2 x hx y hy).2)
  change (∫ r in b..c, wR M Q e ω r *
    (-akR M Q e ω L r *
      ‖uxR M Q e ω R r + (σ : ℂ) * (effectiveK M Q e ω L r : ℂ) *
        I * uR M Q e ω R r‖ ^ 2 -
      (srcR M Q e ω S r * (starRingEnd ℂ) (uR M Q e ω R r +
        2 * ((effectiveK M Q e ω L r : ℂ) / (khxR M Q e ω L r : ℂ)) *
          (uxR M Q e ω R r + (σ : ℂ) * (effectiveK M Q e ω L r : ℂ) *
            I * uR M Q e ω R r))).re)) =
      ssr_J M Q e ω L σ R c - ssr_J M Q e ω L σ R b at ht
  rw [← ht]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [hi] at hr
  have hm : multR M Q e ω L R r = uR M Q e ω R r +
      2 * ((effectiveK M Q e ω L r / khxR M Q e ω L r : ℝ) : ℂ) *
        (uxR M Q e ω R r + (σ : ℂ) * (effectiveK M Q e ω L r : ℂ) * I * uR M Q e ω R r) := by
    rcases hreg with ⟨hs, hsub⟩ | ⟨hs, hsub⟩
    · simp [multR, hsub hr, hs]
    · have hAH : r ∉ setAH M Q e ω L := fun hh => (not_lt.mpr (hsub hr).1.le) hh.2.1
      simp [multR, hAH, hsub hr, hs, sub_eq_add_neg]
  dsimp only [ssr_b, ssr_src]
  rw [hm, ssr_pairing, ofReal_div]
  ring

/-- The middle flux equation in interface notation. -/
theorem ssr_forbidden_integral {M Q e ω ρ₁ ρ₂ L b c : ℝ}
    (hQ : |Q| < M) (hN : 2 * M ≤ e / ω)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI)
    (hbc : b ≤ c) (hb : outerHorizon M Q < b) (hc : outerHorizon M Q < c)
    (hreg : Icc b c ⊆ setFb M Q e ω L) :
    (∫ r in b..c, -ssr_bm M Q e ω L R r - ssr_src M Q e ω L R S r) =
      ssr_Jm M Q e ω R c - ssr_Jm M Q e ω R b := by
  classical
  have ht := source_sub_reciprocal_forbidden_integral hQ hN hb hc hP.2.2.1.1
    (fun x hx y hy => (hP.2.2.1.2 x hx y hy).1)
    (fun x hx y hy => (hP.2.2.1.2 x hx y hy).2)
  change (∫ r in b..c, wR M Q e ω r *
    (-(‖uxR M Q e ω R r‖ ^ 2 + normalizationG M Q e ω r ^ 4 *
      (L * delta M Q r - radialK e ω r ^ 2) * ‖uR M Q e ω R r‖ ^ 2) -
      (srcR M Q e ω S r * (starRingEnd ℂ) (uR M Q e ω R r)).re)) =
      ssr_Jm M Q e ω R c - ssr_Jm M Q e ω R b at ht
  rw [← ht]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hbc] at hr
  have hAH : r ∉ setAH M Q e ω L := fun hh => (not_lt.mpr (hreg hr).2) hh.2.2
  have hAI : r ∉ setAI M Q e ω L := fun hh => (not_lt.mpr (hreg hr).2) hh.2
  have hm : multR M Q e ω L R r = uR M Q e ω R r := by simp [multR, hAH, hAI]
  dsimp only [ssr_bm, ssr_src]
  rw [hm, ssr_pairing]
  ring

end ModeStability.AllAngular

end
