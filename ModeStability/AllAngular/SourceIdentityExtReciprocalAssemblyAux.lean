module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtReciprocalCurrent
public import ModeStability.AllAngular.SourceIdentityExtReciprocalTurning
public import ModeStability.AllAngular.Prop61Multiplier
public import ModeStability.AllAngular.SourceIdentityRGlobal

/-!
# Radial densities for the extremal reciprocal source identity

Source: the all-angular research notes in preparation, pp. 7–8.
The bulk densities are the exact shared interface integrands. Their
continuity and nonnegativity provide the improper-integration hypotheses.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

open CoordinateCoefficients

noncomputable def ser_J (M Q e ω L σ : ℝ) (R : ℝ → ℂ) : ℝ → ℝ := fun r =>
  -(effectiveK M Q e ω L r / P61.khxR M Q e ω L r) *
    ‖P61.uxR M Q e ω R r + σ * effectiveK M Q e ω L r * I * P61.uR M Q e ω R r‖ ^ 2 -
    (P61.uxR M Q e ω R r * (starRingEnd ℂ) (P61.uR M Q e ω R r)).re

noncomputable def ser_Jm (M Q e ω : ℝ) (R : ℝ → ℂ) : ℝ → ℝ := fun r =>
  -(P61.uxR M Q e ω R r * (starRingEnd ℂ) (P61.uR M Q e ω R r)).re

noncomputable def ser_b (M Q e ω L σ : ℝ) (R : ℝ → ℂ) : ℝ → ℝ := fun r =>
  P61.akR M Q e ω L r *
    ‖P61.uxR M Q e ω R r + σ * effectiveK M Q e ω L r * I * P61.uR M Q e ω R r‖ ^ 2 *
      P61.wR M Q e ω r

noncomputable def ser_bm (M Q e ω L : ℝ) (R : ℝ → ℂ) : ℝ → ℝ := fun r =>
  (‖P61.uxR M Q e ω R r‖ ^ 2 + normalizationG M Q e ω r ^ 4 *
    (L * delta M Q r - radialK e ω r ^ 2) * ‖P61.uR M Q e ω R r‖ ^ 2) * P61.wR M Q e ω r

noncomputable def ser_pair (M Q e ω L : ℝ) (R S : ℝ → ℂ) : ℝ → ℂ := fun r =>
  P61.srcR M Q e ω S r * (starRingEnd ℂ) (P61.multR M Q e ω L R r) * (P61.wR M Q e ω r : ℂ)

noncomputable def ser_src (M Q e ω L : ℝ) (R S : ℝ → ℂ) : ℝ → ℝ :=
  fun r => (ser_pair M Q e ω L R S r).re

theorem ser_w_pos {M Q e ω r : ℝ} (hQ : |Q| = M) (hN : 2 * M ≤ e / ω)
    (hr : outerHorizon M Q < r) : 0 < P61.wR M Q e ω r := by
  unfold P61.wR
  rw [ser_density hQ hN hr]
  norm_num

theorem ser_ak_continuous {M Q e ω L r : ℝ} (hM : 0 < M) (hQ : |Q| = M)
    (hω : 0 < ω) (hL : 0 ≤ L) (ha : outerHorizon M Q < e / ω) (hN : 2 * M ≤ e / ω)
    (hr : outerHorizon M Q < r) (hP : L * delta M Q r < radialK e ω r ^ 2) :
    ContinuousAt (P61.akR M Q e ω L) r := by
  obtain ⟨hk, hfx, -⟩ := ser_coefficient_props hM hQ hω hL ha hN hr hP
  have hw : ContDiffAt ℝ 1 (fun r => delta M Q r * normalizationG M Q e ω r ^ 2) r := by
    rw [ser_normalization hQ hN]
    exact ((contDiff_delta M Q).contDiffAt.mul ((ser_g_smooth hQ hr).pow 2)).of_le
      (by norm_num)
  have hx : ContDiffAt ℝ 1 (P61.khxR M Q e ω L) r :=
    hw.mul (hk.derivWithin (m := 1) (by norm_num))
  have hxx : ContinuousAt
      (xDeriv M Q (normalizationG M Q e ω) (P61.khxR M Q e ω L)) r :=
    hw.continuousAt.mul (hx.derivWithin (m := 0) (by norm_num)).continuousAt
  exact ((hx.continuousAt.pow 2 |>.const_mul 2).sub
    (hk.continuousAt.mul hxx)).div (hx.continuousAt.pow 2) (pow_ne_zero 2 hfx.ne')

theorem ser_b_data {M Q e ω ρ₁ ρ₂ L σ : ℝ} (h : P61.Range17 M Q e ω ρ₁ ρ₂)
    (hQ : |Q| = M) (hN : 2 * M ≤ e / ω) (hL : 0 ≤ L)
    (ha : outerHorizon M Q < e / ω) {R S : ℝ → ℂ} {BH BI : ℂ}
    (hP : P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) {s : Set ℝ}
    (hs : s ⊆ Ioi (outerHorizon M Q))
    (hp : ∀ r ∈ s, L * delta M Q r < radialK e ω r ^ 2) :
    ContinuousOn (ser_b M Q e ω L σ R) s ∧ ∀ r ∈ s, 0 ≤ ser_b M Q e ω L σ R r := by
  have hU := (P61.uR_contDiffOn_one h.1 hP.2.2.1).continuousOn
  have hV := P61.uxR_continuousOn h.1 hP.2.2.1
  have hW := P61.wR_continuousOn (Q := Q) (e := e) (ω := ω) h.1
  refine ⟨?_, ?_⟩
  · intro r hr
    have hk := (ser_coefficient_props h.1 hQ h.2.2.2.1 hL ha hN (hs hr) (hp r hr)).1.continuousAt
    have hak := ser_ak_continuous h.1 hQ h.2.2.2.1 hL ha hN (hs hr) (hp r hr)
    have hu := hU.continuousAt (Ioi_mem_nhds (hs hr))
    have hv := hV.continuousAt (Ioi_mem_nhds (hs hr))
    have hw := hW.continuousAt (Ioi_mem_nhds (hs hr))
    have hb : ContinuousAt (ser_b M Q e ω L σ R) r := by unfold ser_b; fun_prop
    exact hb.continuousWithinAt
  · intro r hr
    obtain ⟨-, hx, hE⟩ := ser_coefficient_props h.1 hQ h.2.2.2.1 hL ha hN (hs hr) (hp r hr)
    exact mul_nonneg (mul_nonneg (div_nonneg hE.le (sq_nonneg _)) (sq_nonneg _))
      (ser_w_pos hQ hN (hs hr)).le

theorem ser_bm_data {M Q e ω ρ₁ ρ₂ L : ℝ} (h : P61.Range17 M Q e ω ρ₁ ρ₂)
    (hQ : |Q| = M) (hN : 2 * M ≤ e / ω)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI)
    {s : Set ℝ} (hs : s ⊆ Ioi (outerHorizon M Q))
    (hp : ∀ r ∈ s, radialK e ω r ^ 2 ≤ L * delta M Q r) :
    ContinuousOn (ser_bm M Q e ω L R) s ∧ ∀ r ∈ s, 0 ≤ ser_bm M Q e ω L R r := by
  have hu := ((P61.uR_contDiffOn_one h.1 hP.2.2.1).continuousOn).mono hs
  have hv := (P61.uxR_continuousOn h.1 hP.2.2.1).mono hs
  have hw := (P61.wR_continuousOn (Q := Q) (e := e) (ω := ω) h.1).mono hs
  have hg := (P61.normalizationG_continuousOn (Q := Q) (e := e) (ω := ω) h.1).mono hs
  have hk := (contDiff_radialK e ω).continuous.continuousOn (s := s)
  have hd := (contDiff_delta M Q).continuous.continuousOn (s := s)
  refine ⟨?_, fun r hr => ?_⟩
  · unfold ser_bm
    fun_prop
  · exact mul_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg
      (mul_nonneg (pow_nonneg (le_of_lt (by
        rw [ser_normalization hQ hN]; exact ser_g_pos hQ (hs hr))) 4)
        (sub_nonneg.mpr (hp r hr))) (sq_nonneg _))) (ser_w_pos hQ hN (hs hr)).le

theorem ser_pair_data {M Q e ω ρ₁ ρ₂ L : ℝ} (h : P61.Range17 M Q e ω ρ₁ ρ₂)
    (hL : 0 ≤ L) {R S : ℝ → ℂ} {BH BI : ℂ}
    (hP : P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) :
    Integrable (ser_src M Q e ω L R S) ∧
      (∀ r ∉ Ioi (outerHorizon M Q), ser_src M Q e ω L R S r = 0) ∧
      (∫ r, ser_src M Q e ω L R S r) = (∫ r in Icc ρ₁ ρ₂, ser_pair M Q e ω L R S r).re := by
  have hz : ∀ r ∉ Icc ρ₁ ρ₂, ser_pair M Q e ω L R S r = 0 := by
    intro r hr
    simp [ser_pair, P61.srcR, hP.1 r hr]
  have hi : Integrable (ser_pair M Q e ω L R S) :=
    (P61.integrableOn_src_mul_multR h hL hP).integrable_of_forall_notMem_eq_zero hz
  refine ⟨hi.re, ?_, ?_⟩
  · intro r hr
    have hc : r ∉ Icc ρ₁ ρ₂ := fun hc => hr (h.2.2.2.2.2.1.trans_le hc.1)
    simp [ser_src, hz r hc]
  · change (∫ r, (ser_pair M Q e ω L R S r).re) = _
    calc
      _ = (∫ r, ser_pair M Q e ω L R S r).re := integral_re hi
      _ = _ := congrArg Complex.re
        (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm


end ModeStability.AllAngular

end
