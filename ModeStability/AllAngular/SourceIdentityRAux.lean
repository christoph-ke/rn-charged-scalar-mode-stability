module

public import Mathlib
public import ModeStability.AllAngular.GreenFormulaAux
public import ModeStability.AllAngular.SourceIdentityAux

/-!
# Integrated source equations: local regularity for the identity (6.3)

Source: the all-angular research notes in preparation (pp. 7–8).
The Green solution satisfies (6.1) in integrated form. Its flux is locally
absolutely continuous, and the pointwise source equation holds almost everywhere;
no continuity assumption on the compactly supported source is required.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-- A real absolutely continuous current can be integrated using an almost-everywhere
source identity. This is the FTC needed for an `L²` source in (6.3). -/
theorem source_current_integral_of_ae {J j : ℝ → ℝ} {b c : ℝ}
    (hJ : AbsolutelyContinuousOnInterval J b c)
    (hd : ∀ᵐ r, r ∈ uIcc b c → HasDerivAt J (j r) r) :
    ∫ r in b..c, j r = J c - J b := by
  rw [← hJ.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hd] with r hr hmem
  exact (hr (uIoc_subset_uIcc hmem)).deriv.symm

/-- The integrated equation makes the radial flux locally absolutely continuous after
applying any real continuous linear functional (in particular `re` and `im`). -/
theorem source_flux_absolutelyContinuous {a b c : ℝ} {p q : ℝ → ℝ}
    {R S : ℝ → ℂ} (hq : ContinuousOn q (Ioi a))
    (hR : ∀ r ∈ Ioi a, DifferentiableAt ℝ R r)
    (hS : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a, IntervalIntegrable S volume x y)
    (hint : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a,
      (p y : ℂ) * deriv R y - (p x : ℂ) * deriv R x =
        ∫ r in x..y, S r - (q r : ℂ) * R r)
    (hb : b ∈ Ioi a) (hc : c ∈ Ioi a) (ell : ℂ →L[ℝ] ℝ) :
    AbsolutelyContinuousOnInterval (fun r => ell ((p r : ℂ) * deriv R r)) b c := by
  have hsub : uIcc b c ⊆ Ioi a := by
    intro r hr
    have hmin : a < min b c := lt_min hb hc
    exact hmin.trans_le hr.1
  have hqR : ContinuousOn (fun r => (q r : ℂ) * R r) (Ioi a) :=
    (continuous_ofReal.comp_continuousOn hq).mul fun r hr =>
      (hR r hr).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun r => S r - (q r : ℂ) * R r) volume b c :=
    (hS b hb c hc).sub (hqR.mono hsub).intervalIntegrable
  have hil : IntervalIntegrable (fun r => ell (S r - (q r : ℂ) * R r)) volume b c :=
    ⟨ell.integrable_comp hi.1, ell.integrable_comp hi.2⟩
  have hprim := hil.absolutelyContinuousOnInterval_intervalIntegral (c := b) (by simp)
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => ell ((p b : ℂ) * deriv R b)) b c :=
    (contDiffOn_const : ContDiffOn ℝ 1
      (fun _ : ℝ => ell ((p b : ℂ) * deriv R b)) (uIcc b c)).absolutelyContinuousOnInterval
  apply (hconst.add hprim).congr
  intro r hr
  have hir : IntervalIntegrable (fun s => S s - (q s : ℂ) * R s) volume b r :=
    (hS b hb r (hsub hr)).sub
      (hqR.mono (fun t ht => (lt_min hb (hsub hr)).trans_le ht.1)).intervalIntegrable
  change ell ((p b : ℂ) * deriv R b) + (∫ s in b..r, ell (S s - (q s : ℂ) * R s)) = _
  rw [ell.intervalIntegral_comp_comm hir]
  rw [← hint b hb r (hsub hr), map_sub]
  ring

/-- The integrated source equation yields the pointwise flux equation almost everywhere
on each compact subinterval of the exterior. -/
theorem source_flux_hasDerivAt_ae {a b c : ℝ} {p q : ℝ → ℝ} {R S : ℝ → ℂ}
    (hq : ContinuousOn q (Ioi a))
    (hR : ∀ r ∈ Ioi a, DifferentiableAt ℝ R r)
    (hS : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a, IntervalIntegrable S volume x y)
    (hint : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a,
      (p y : ℂ) * deriv R y - (p x : ℂ) * deriv R x =
        ∫ r in x..y, S r - (q r : ℂ) * R r)
    (hb : b ∈ Ioi a) (hc : c ∈ Ioi a) :
    ∀ᵐ r, r ∈ uIcc b c → HasDerivAt (fun s => (p s : ℂ) * deriv R s)
      (S r - (q r : ℂ) * R r) r := by
  have hsub : uIcc b c ⊆ Ioi a := by
    intro r hr
    have hmin : a < min b c := lt_min hb hc
    exact hmin.trans_le hr.1
  have hqR : ContinuousOn (fun r => (q r : ℂ) * R r) (Ioi a) :=
    (continuous_ofReal.comp_continuousOn hq).mul fun r hr =>
      (hR r hr).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable (fun r => S r - (q r : ℂ) * R r) volume b c :=
    (hS b hb c hc).sub (hqR.mono hsub).intervalIntegrable
  filter_upwards [hi.ae_hasDerivAt_integral] with r hr hmem
  have hd := (hasDerivAt_const r ((p b : ℂ) * deriv R b)).add (hr hmem b (by simp))
  apply (hd.congr_deriv (zero_add _)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (hsub hmem)] with s hs
  have hs' := hint b hb s hs
  change (p s : ℂ) * deriv R s = (p b : ℂ) * deriv R b + ∫ t in b..s, S t - (q t : ℂ) * R t
  linear_combination hs'

/-- The flux of an integrated source solution is continuous on the exterior. -/
theorem source_flux_continuousOn {a : ℝ} {p q : ℝ → ℝ} {R S : ℝ → ℂ}
    (hq : ContinuousOn q (Ioi a))
    (hR : ∀ r ∈ Ioi a, DifferentiableAt ℝ R r)
    (hS : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a, IntervalIntegrable S volume x y)
    (hint : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a,
      (p y : ℂ) * deriv R y - (p x : ℂ) * deriv R x =
        ∫ r in x..y, S r - (q r : ℂ) * R r) :
    ContinuousOn (fun r => (p r : ℂ) * deriv R r) (Ioi a) := by
  have hqR : ContinuousOn (fun r => (q r : ℂ) * R r) (Ioi a) :=
    (continuous_ofReal.comp_continuousOn hq).mul fun r hr =>
      (hR r hr).continuousAt.continuousWithinAt
  intro r hr
  change a < r at hr
  let b := (a + r) / 2
  let c := r + 1
  have hb : b ∈ Ioi a := by change a < (a + r) / 2; linarith
  have hc : c ∈ Ioi a := by change a < r + 1; linarith
  have hbr : b < r := by dsimp [b]; linarith
  have hrc : r < c := by dsimp [c]; linarith
  have hbc : b ≤ c := (hbr.trans hrc).le
  have hsub : uIcc b c ⊆ Ioi a := by
    intro s hs
    exact (lt_min hb hc).trans_le hs.1
  have hi : IntervalIntegrable (fun s => S s - (q s : ℂ) * R s) volume b c :=
    (hS b hb c hc).sub (hqR.mono hsub).intervalIntegrable
  have hprim := (intervalIntegral.continuousOn_primitive_interval' hi
    (left_mem_uIcc : b ∈ uIcc b c)).continuousAt
      (by rw [uIcc_of_le hbc]; exact Icc_mem_nhds hbr hrc)
  have hd : ContinuousAt (fun s => (p b : ℂ) * deriv R b +
      ∫ t in b..s, S t - (q t : ℂ) * R t) r := continuousAt_const.add hprim
  apply (hd.congr ?_).continuousWithinAt
  filter_upwards [Ioi_mem_nhds hr] with s hs
  linear_combination -(hint b hb s hs)

/-- An integrated source solution is `C¹` when the leading coefficient is continuous and
nonzero. In particular, its first derivative is continuous even for an `L²` source. -/
theorem source_solution_contDiffOn_one {a : ℝ} {p q : ℝ → ℝ} {R S : ℝ → ℂ}
    (hp : ContinuousOn p (Ioi a)) (hp0 : ∀ r ∈ Ioi a, p r ≠ 0)
    (hq : ContinuousOn q (Ioi a))
    (hR : ∀ r ∈ Ioi a, DifferentiableAt ℝ R r)
    (hS : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a, IntervalIntegrable S volume x y)
    (hint : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a,
      (p y : ℂ) * deriv R y - (p x : ℂ) * deriv R x =
        ∫ r in x..y, S r - (q r : ℂ) * R r) :
    ContDiffOn ℝ 1 R (Ioi a) := by
  have hf := source_flux_continuousOn hq hR hS hint
  have hd : ContinuousOn (deriv R) (Ioi a) := by
    apply (hf.div (continuous_ofReal.comp_continuousOn hp)
      (fun r hr => ofReal_ne_zero.mpr (hp0 r hr))).congr
    intro r hr
    dsimp
    exact (mul_div_cancel_left₀ (deriv R r) (ofReal_ne_zero.mpr (hp0 r hr))).symm
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  exact ⟨fun r hr => (hR r hr).differentiableWithinAt, by simp, contDiffOn_zero.mpr hd⟩

/-- Reconstruct complex absolute continuity from the two real components. -/
theorem source_complex_absolutelyContinuous {b c : ℝ} {f : ℝ → ℂ}
    (hre : AbsolutelyContinuousOnInterval (fun r => (f r).re) b c)
    (him : AbsolutelyContinuousOnInterval (fun r => (f r).im) b c) :
    AbsolutelyContinuousOnInterval f b c := by
  have h₁ := Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hre
  have h₂ := (Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval him).const_smul I
  apply (h₁.add h₂).congr
  intro r hr
  change ((f r).re : ℂ) + I * ((f r).im : ℂ) = f r
  rw [mul_comm I, Complex.re_add_im]

/-- The full complex radial flux is locally absolutely continuous. -/
theorem source_complex_flux_absolutelyContinuous {a b c : ℝ} {p q : ℝ → ℝ}
    {R S : ℝ → ℂ} (hq : ContinuousOn q (Ioi a))
    (hR : ∀ r ∈ Ioi a, DifferentiableAt ℝ R r)
    (hS : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a, IntervalIntegrable S volume x y)
    (hint : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a,
      (p y : ℂ) * deriv R y - (p x : ℂ) * deriv R x =
        ∫ r in x..y, S r - (q r : ℂ) * R r)
    (hb : b ∈ Ioi a) (hc : c ∈ Ioi a) :
    AbsolutelyContinuousOnInterval (fun r => (p r : ℂ) * deriv R r) b c :=
  source_complex_absolutelyContinuous
    (source_flux_absolutelyContinuous hq hR hS hint hb hc reCLM)
    (source_flux_absolutelyContinuous hq hR hS hint hb hc imCLM)

/-- An integrable complex source has an absolutely continuous primitive. -/
theorem source_primitive_absolutelyContinuous {b c d : ℝ} {f : ℝ → ℂ}
    (hi : IntervalIntegrable f volume b c) (hd : d ∈ uIcc b c) :
    AbsolutelyContinuousOnInterval (fun r => ∫ s in d..r, f s) b c := by
  have hre : IntervalIntegrable (fun r => (f r).re) volume b c :=
    ⟨reCLM.integrable_comp hi.1, reCLM.integrable_comp hi.2⟩
  have him : IntervalIntegrable (fun r => (f r).im) volume b c :=
    ⟨imCLM.integrable_comp hi.1, imCLM.integrable_comp hi.2⟩
  apply source_complex_absolutelyContinuous
  · apply (hre.absolutelyContinuousOnInterval_intervalIntegral hd).congr
    intro r hr
    exact reCLM.intervalIntegral_comp_comm
      (hi.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hd hr)))
  · apply (him.absolutelyContinuousOnInterval_intervalIntegral hd).congr
    intro r hr
    exact imCLM.intervalIntegral_comp_comm
      (hi.mono_set' (uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hd hr)))

/-- Squared modulus preserves absolute continuity on a compact interval. -/
theorem source_norm_sq_absolutelyContinuous {b c : ℝ} {f : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f b c) :
    AbsolutelyContinuousOnInterval (fun r => ‖f r‖ ^ 2) b c := by
  have hre := reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have him := imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf
  apply ((hre.mul hre).add (him.mul him)).congr
  intro r hr
  simp only [Function.comp_apply, reCLM_apply, imCLM_apply, Pi.add_apply, Pi.mul_apply,
    Complex.sq_norm, Complex.normSq_apply]

/-- The reduction with a source at any point where the flux equation holds. Here
`g' = c/p`, `U = R/g` and `V = g(pR') - cR`; hence `V = pg² ∂ᵣU` and
`∂ᵣV = (pg²)⁻¹(-g⁴pqU + pg³S)`. This applies almost everywhere to the Green solution. -/
theorem source_reduction_at {r c : ℝ} {p q g : ℝ → ℝ} {R S : ℝ → ℂ}
    (hp : p r ≠ 0) (hg0 : g r ≠ 0) (hg : HasDerivAt g (c / p r) r)
    (hR : DifferentiableAt ℝ R r)
    (hflux : HasDerivAt (fun s => (p s : ℂ) * deriv R s) (S r - (q r : ℂ) * R r) r) :
    HasDerivAt (fun s => R s / (g s : ℂ))
        (((g r : ℂ) * ((p r : ℂ) * deriv R r) - (c : ℂ) * R r) /
          (p r * g r ^ 2 : ℂ)) r ∧
      HasDerivAt (fun s => (g s : ℂ) * ((p s : ℂ) * deriv R s) - (c : ℂ) * R s)
        (((1 / (p r * g r ^ 2) : ℝ) : ℂ) *
          (-((g r ^ 4 * p r * q r : ℝ) : ℂ) * (R r / (g r : ℂ)) +
            ((p r * g r ^ 3 : ℝ) : ℂ) * S r)) r := by
  have hpc : (p r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp
  have hgc : (g r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hg0
  constructor
  · refine (hR.hasDerivAt.div hg.ofReal_comp hgc).congr_deriv ?_
    push_cast
    field_simp
  · refine ((hg.ofReal_comp.mul hflux).sub (hR.hasDerivAt.const_mul (c : ℂ))).congr_deriv ?_
    push_cast
    field_simp
    ring

/-- The allowed current source identity directly in `r`, for a positive or negative
coordinate Jacobian `w = ∂ᵣx`. The variables `V`, `fx`, `fxx` stand for the derivatives in `x`.
This form avoids assuming a pointwise second derivative for an `L²` source. -/
theorem source_weighted_current_hasDerivAt {f fx : ℝ → ℝ} {U V G : ℝ → ℂ}
    {r σ w fxx : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hf : HasDerivAt f (w * fx r) r) (hfx : HasDerivAt fx (w * fxx) r)
    (hfx0 : fx r ≠ 0) (hU : HasDerivAt U ((w : ℂ) * V r) r)
    (hV : HasDerivAt V ((w : ℂ) * (-((f r ^ 2 : ℝ) : ℂ) * U r + G r)) r) :
    HasDerivAt (fun s => -(f s / fx s) * ‖V s + σ * f s * I * U s‖ ^ 2 -
        (V s * (starRingEnd ℂ) (U s)).re)
      (w * (-((2 * fx r ^ 2 - f r * fxx) / fx r ^ 2) *
          ‖V r + σ * f r * I * U r‖ ^ 2 -
        (G r * (starRingEnd ℂ) (U r + 2 * (f r / fx r) *
          (V r + σ * f r * I * U r))).re)) r := by
  have hq := (hf.div hfx hfx0).neg
  have hv := hV.add (((hf.ofReal_comp.const_mul (σ : ℂ)).mul_const I).mul hU)
  have hn := hv.norm_sq
  have hp := Current.hasDerivAt_re (hV.mul hU.star)
  have h := (hq.mul hn).sub hp
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, Pi.div_apply, Pi.add_apply, Pi.mul_apply]
  generalize V r = v at *
  generalize U r = u at *
  generalize G r = z at *
  generalize fx r = k' at *
  generalize f r = k at *
  rcases hσ with rfl | rfl <;>
  · simp only [Complex.inner, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, Complex.neg_im,
      map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
      Complex.div_ofReal_re, Complex.div_ofReal_im]
    field_simp
    ring

/-- The allowed current is absolutely continuous on compact subintervals whenever
`f/fx`, `f`, `U`, and `V = Ux` are. -/
theorem source_allowed_current_absolutelyContinuous {b c σ : ℝ}
    {f fx : ℝ → ℝ} {U V : ℝ → ℂ}
    (hγ : AbsolutelyContinuousOnInterval (fun r => f r / fx r) b c)
    (hf : AbsolutelyContinuousOnInterval f b c)
    (hU : AbsolutelyContinuousOnInterval U b c)
    (hV : AbsolutelyContinuousOnInterval V b c) :
    AbsolutelyContinuousOnInterval
      (fun r => -(f r / fx r) * ‖V r + σ * f r * I * U r‖ ^ 2 -
        (V r * (starRingEnd ℂ) (U r)).re) b c := by
  have hfc := Complex.ofRealCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have hv : AbsolutelyContinuousOnInterval (fun r => V r + σ * f r * I * U r) b c := by
    apply (hV.add ((hfc.const_smul ((σ : ℂ) * I)).smul hU)).congr
    intro r hr
    change V r + ((σ : ℂ) * I * (f r : ℂ)) * U r = _
    ring
  have hconj := Complex.conjLIE.lipschitzWith.comp_absolutelyContinuousOnInterval hU
  have hp := reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval (hV.smul hconj)
  exact (hγ.neg.mul (source_norm_sq_absolutelyContinuous hv)).sub hp

/-- The forbidden current source identity directly in `r`. -/
theorem source_weighted_flux_hasDerivAt {U V G : ℝ → ℂ} {r w P : ℝ}
    (hU : HasDerivAt U ((w : ℂ) * V r) r)
    (hV : HasDerivAt V ((w : ℂ) * (-(P : ℂ) * U r + G r)) r) :
    HasDerivAt (fun s => -(V s * (starRingEnd ℂ) (U s)).re)
      (w * (-(‖V r‖ ^ 2 - P * ‖U r‖ ^ 2) -
        (G r * (starRingEnd ℂ) (U r)).re)) r := by
  refine (Current.hasDerivAt_re (hV.mul hU.star)).neg.congr_deriv ?_
  generalize V r = v
  generalize U r = u
  generalize G r = z
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.add_re,
    Complex.mul_im, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- Integrating the weighted allowed-current source identity for a rough source.
The derivative hypotheses are only almost everywhere on the compact interval. -/
theorem source_weighted_current_integral {b c σ : ℝ} {f fx fxx w : ℝ → ℝ}
    {U V G : ℝ → ℂ} (hσ : σ = 1 ∨ σ = -1)
    (hγ : AbsolutelyContinuousOnInterval (fun r => f r / fx r) b c)
    (hf : AbsolutelyContinuousOnInterval f b c)
    (hU : AbsolutelyContinuousOnInterval U b c)
    (hV : AbsolutelyContinuousOnInterval V b c)
    (hd : ∀ᵐ r, r ∈ uIcc b c →
      HasDerivAt f (w r * fx r) r ∧ HasDerivAt fx (w r * fxx r) r ∧ fx r ≠ 0 ∧
        HasDerivAt U ((w r : ℂ) * V r) r ∧
          HasDerivAt V ((w r : ℂ) * (-((f r ^ 2 : ℝ) : ℂ) * U r + G r)) r) :
    (∫ r in b..c, w r * (-((2 * fx r ^ 2 - f r * fxx r) / fx r ^ 2) *
          ‖V r + σ * f r * I * U r‖ ^ 2 -
        (G r * (starRingEnd ℂ) (U r + 2 * (f r / fx r) *
          (V r + σ * f r * I * U r))).re)) =
      (-(f c / fx c) * ‖V c + σ * f c * I * U c‖ ^ 2 -
        (V c * (starRingEnd ℂ) (U c)).re) -
      (-(f b / fx b) * ‖V b + σ * f b * I * U b‖ ^ 2 -
        (V b * (starRingEnd ℂ) (U b)).re) := by
  apply source_current_integral_of_ae (source_allowed_current_absolutelyContinuous hγ hf hU hV)
  filter_upwards [hd] with r hr hmem
  obtain ⟨hfr, hfxr, hfx0, hUr, hVr⟩ := hr hmem
  exact source_weighted_current_hasDerivAt hσ hfr hfxr hfx0 hUr hVr

end ModeStability.AllAngular

end
