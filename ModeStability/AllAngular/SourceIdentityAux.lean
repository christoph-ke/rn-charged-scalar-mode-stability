module

public import Mathlib
public import ModeStability.Current.Dephased
public import ModeStability.AllAngular.TurningPoint

/-!
# The current identity with a source: pointwise derivatives and improper integration

Source: the all-angular research notes in preparation, Section 6, proof of Proposition 6.1,
pp. 7–8: with `γ = k̂/k̂_x` on the allowed intervals and the multiplier
`𝓜U = U + 2γ(U_x ± ik̂U)` there (`𝓜U = U` on the forbidden interval), the sourced current
includes a forcing term; its integral yields the source identity (6.3).
The current is the one of (5.1), the bulk the integrand of (5.3).

In this file the paper's source `F` is called `G`, and the potential `k² − V = k̂²` is called `F`
(or `f²` on an allowed interval), so the equation (6.1) reads `U_xx + F U = G`.

* `hasDerivAt_phaseFree_current_source`: on an allowed interval (`F = f²`, `f_x ≠ 0`), the
  phase-free current `J = −(f/f_x)|U_x + iσfU|² − Re(U_x Ū)` (`σ = ±1`) of (4.2) satisfies
  `J_x = −((2f_x² − f f_xx)/f_x²)|U_x + iσfU|² − Re(G conj(U + 2(f/f_x)(U_x + iσfU)))`.
* `hasDerivAt_neg_re_flux_source`: on the forbidden interval, the current `m = −Re(U_x Ū)` of
  (5.2) satisfies `m_x = −(|U_x|² − F|U|²) − Re(G Ū)`.
* `integrableOn_bulk_of_aecover`, `integral_Ioo_bulk_eq`, `integral_Ioi_bulk_eq`: the improper
  integration step. If
  `φ_x = −b − g` on an interval with `b ≥ 0` continuous, `g` integrable, and `φ` has limits `A`,
  `B`
  at the two ends, then `b` is integrable and `∫ b = A − B − ∫ g`.
* `sourceMultiplier`: the multiplier `𝓜U` on the coordinate interval `(0, ∞)`, with turning points
  `x₁ ≤ x₂` (`x₁ = x₂` for `L = 0`); `sourceMultiplier_of_lt`, `_of_mem_Icc`, `_of_gt`.
* `contDiffAt_one_of_hasDerivAt_deriv`, `contDiffOn_sq_deriv_of_eq_sign_mul_sqrt`,
  `eq_zero_and_deriv_neg_of_left_turning_point`, `eq_zero_and_deriv_pos_of_right_turning_point`:
  local facts on the allowed intervals (`f = s√F`) and at simple turning points.
* `continuousOn_sourceMultiplier`, `continuousOn_sourceMultiplier_L0`: `𝓜U` is continuous on
  `(0, ∞)`; at a turning point `γ → 0` by the first claim of (4.6), so `𝓜U → U` there.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-! ### Pointwise derivatives of the currents with a source -/

/-- **The current identity with a source, allowed interval.** If `U_xx = −f² U + G` at `x`,
`f_x(x) ≠ 0` and `σ = ±1`, the phase-free current `J = −(f/f_x)|U_x + iσfU|² − Re(U_x Ū)` of (4.2)
has derivative `J_x = −((2f_x² − f f_xx)/f_x²)|U_x + iσfU|² − Re(G conj(𝓜U))` at `x`, with the
multiplier `𝓜U = U + 2(f/f_x)(U_x + iσfU)` of the proof of Proposition 6.1. -/
theorem hasDerivAt_phaseFree_current_source {f : ℝ → ℝ} {U G : ℝ → ℂ} {σ x : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : DifferentiableAt ℝ f x)
    (hf' : DifferentiableAt ℝ (deriv f) x) (hfx : deriv f x ≠ 0)
    (hU : DifferentiableAt ℝ U x)
    (hU' : HasDerivAt (deriv U) (-((f x ^ 2 : ℝ) : ℂ) * U x + G x) x) :
    HasDerivAt (fun y => -(f y / deriv f y) * ‖deriv U y + σ * f y * I * U y‖ ^ 2 -
        (deriv U y * (starRingEnd ℂ) (U y)).re)
      (-((2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2) *
          ‖deriv U x + σ * f x * I * U x‖ ^ 2 -
        (G x * (starRingEnd ℂ) (U x + 2 * (f x / deriv f x) *
          (deriv U x + σ * f x * I * U x))).re) x := by
  have hq := (hf.hasDerivAt.div hf'.hasDerivAt hfx).neg
  have hw := hU'.add (((hf.hasDerivAt.ofReal_comp.const_mul (σ : ℂ)).mul_const I).mul
    hU.hasDerivAt)
  have hN := hw.norm_sq
  have hP := Current.hasDerivAt_re (hU'.mul hU.hasDerivAt.star)
  have h := (hq.mul hN).sub hP
  convert h using 1
  · rfl
  have hqx : (-(f / deriv f)) x = -(f x / deriv f x) := rfl
  rw [hqx]
  simp only [Pi.add_apply, Pi.mul_apply]
  generalize deriv U x = w at *
  generalize U x = u at *
  generalize G x = g at *
  generalize deriv f x = K' at *
  generalize f x = K at *
  generalize deriv (deriv f) x = K'' at *
  rcases hσ with rfl | rfl <;>
  · simp only [Complex.inner, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, Complex.neg_im,
      map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
      Complex.div_ofReal_re, Complex.div_ofReal_im]
    field_simp
    ring

/-- **The current identity with a source, forbidden interval.** If `U_xx = −F U + G` at `x`, the
current `m = −Re(U_x Ū)` of (5.2) has derivative `m_x = −(|U_x|² − F|U|²) − Re(G Ū)` at `x`. -/
theorem hasDerivAt_neg_re_flux_source {F : ℝ → ℝ} {U G : ℝ → ℂ} {x : ℝ}
    (hU : DifferentiableAt ℝ U x) (hU' : HasDerivAt (deriv U) (-((F x : ℝ) : ℂ) * U x + G x) x) :
    HasDerivAt (fun y => -(deriv U y * (starRingEnd ℂ) (U y)).re)
      (-(‖deriv U x‖ ^ 2 - F x * ‖U x‖ ^ 2) - (G x * (starRingEnd ℂ) (U x)).re) x := by
  refine (Current.hasDerivAt_re (hU'.mul hU.hasDerivAt.star)).neg.congr_deriv ?_
  generalize deriv U x = w
  generalize U x = u
  generalize G x = g
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.add_re,
    Complex.mul_im, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-! ### Improper integration of a current with a nonnegative bulk -/

/-- **Improper integration, abstract form.** Let `S ⊆ ℝ` be measurable and covered (in the sense
of `MeasureTheory.AECover` for `volume` restricted to `S`) by the intervals `[a i, b i]` along a
countably generated filter `l`, eventually contained in `S`. If `φ_x = −b − g` on `S`, the bulk
`b` is continuous and nonnegative on `S`, the source term `g` is integrable on `S`, and
`φ(a i) → A`, `φ(b i) → B`, then `b` is integrable on `S` and `∫_S b = A − B − ∫_S g`. -/
theorem integrableOn_bulk_of_aecover {ι : Type*} {l : Filter ι} [l.NeBot]
    [l.IsCountablyGenerated] {S : Set ℝ} (hS : MeasurableSet S) {a b : ι → ℝ}
    (hcov : AECover (volume.restrict S) l fun i => Icc (a i) (b i))
    (hab : ∀ᶠ i in l, a i ≤ b i ∧ Icc (a i) (b i) ⊆ S)
    {φ bulk src : ℝ → ℝ} {A B : ℝ}
    (hφ : ∀ x ∈ S, HasDerivAt φ (-bulk x - src x) x)
    (hbc : ContinuousOn bulk S) (hb0 : ∀ x ∈ S, 0 ≤ bulk x) (hsrc : IntegrableOn src S)
    (hA : Tendsto (fun i => φ (a i)) l (𝓝 A)) (hB : Tendsto (fun i => φ (b i)) l (𝓝 B)) :
    IntegrableOn bulk S ∧ ∫ x in S, bulk x = A - B - ∫ x in S, src x := by
  have hres : ∀ {i}, Icc (a i) (b i) ⊆ S →
      (volume.restrict S).restrict (Icc (a i) (b i)) = volume.restrict (Icc (a i) (b i)) := by
    intro i hsub
    rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.2 hsub]
  -- the fundamental theorem of calculus on the truncated intervals
  have hftc : ∀ᶠ i in l, ∫ x in Icc (a i) (b i), bulk x ∂(volume.restrict S) =
      φ (a i) - φ (b i) - ∫ x in Icc (a i) (b i), src x ∂(volume.restrict S) := by
    filter_upwards [hab] with i ⟨hle, hsub⟩
    rw [hres hsub, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle]
    have hsub' : uIcc (a i) (b i) ⊆ S := by rwa [uIcc_of_le hle]
    have hbi : IntervalIntegrable bulk volume (a i) (b i) :=
      (hbc.mono hsub').intervalIntegrable
    have hsi : IntervalIntegrable src volume (a i) (b i) :=
      (hsrc.mono_set hsub').intervalIntegrable
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hφ x (hsub' hx)) (hbi.neg.sub hsi)
    rw [intervalIntegral.integral_sub (f := fun y => -bulk y) hbi.neg hsi,
      intervalIntegral.integral_neg] at h
    linarith
  have hsrcT := hcov.integral_tendsto_of_countably_generated hsrc
  have hlim : Tendsto (fun i => ∫ x in Icc (a i) (b i), bulk x ∂(volume.restrict S)) l
      (𝓝 (A - B - ∫ x in S, src x)) :=
    ((hA.sub hB).sub hsrcT).congr' (hftc.mono fun i hi => hi.symm)
  have hmeas : AEStronglyMeasurable bulk (volume.restrict S) := hbc.aestronglyMeasurable hS
  have hint : Integrable bulk (volume.restrict S) := by
    refine hcov.integrable_of_lintegral_enorm_tendsto (A - B - ∫ x in S, src x) hmeas ?_
    refine ((ENNReal.continuous_ofReal.tendsto _).comp hlim).congr' ?_
    filter_upwards [hab] with i hi
    have hsub := hi.2
    rw [Function.comp_apply, hres hsub, ofReal_integral_eq_lintegral_ofReal]
    · exact setLIntegral_congr_fun measurableSet_Icc fun x hx =>
        (Real.enorm_eq_ofReal (hb0 x (hsub hx))).symm
    · exact (hbc.mono hsub).integrableOn_compact isCompact_Icc
    · exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun x hx => hb0 x (hsub hx))
  exact ⟨hint, hcov.integral_eq_of_tendsto _ hint hlim⟩

/-- **Improper integration on a bounded open interval.** If `φ_x = −b − g` on `(α, β)`, `b` is
continuous and nonnegative there, `g` is integrable on `(α, β)`, `φ → A` at `α⁺` and `φ → B` at
`β⁻`, then `b` is integrable on `(α, β)` and `∫_{(α,β)} b = A − B − ∫_{(α,β)} g`. -/
theorem integral_Ioo_bulk_eq {α β : ℝ} (hαβ : α < β) {φ bulk src : ℝ → ℝ} {A B : ℝ}
    (hφ : ∀ x ∈ Ioo α β, HasDerivAt φ (-bulk x - src x) x)
    (hbc : ContinuousOn bulk (Ioo α β)) (hb0 : ∀ x ∈ Ioo α β, 0 ≤ bulk x)
    (hsrc : IntegrableOn src (Ioo α β))
    (hA : Tendsto φ (𝓝[>] α) (𝓝 A)) (hB : Tendsto φ (𝓝[<] β) (𝓝 B)) :
    IntegrableOn bulk (Ioo α β) ∧ ∫ x in Ioo α β, bulk x = A - B - ∫ x in Ioo α β, src x := by
  have hαc : α < (α + β) / 2 := by linarith
  have hcβ : (α + β) / 2 < β := by linarith
  have hfst : Tendsto Prod.fst (𝓝[>] α ×ˢ 𝓝[<] β) (𝓝[>] α) := tendsto_fst
  have hsnd : Tendsto Prod.snd (𝓝[>] α ×ˢ 𝓝[<] β) (𝓝[<] β) := tendsto_snd
  refine integrableOn_bulk_of_aecover measurableSet_Ioo
    (aecover_Ioo_of_Icc (hfst.mono_right nhdsWithin_le_nhds)
      (hsnd.mono_right nhdsWithin_le_nhds)) ?_ hφ hbc hb0 hsrc (hA.comp hfst) (hB.comp hsnd)
  filter_upwards [hfst.eventually (Ioo_mem_nhdsGT hαc), hsnd.eventually (Ioo_mem_nhdsLT hcβ)]
    with i h1 h2
  exact ⟨h1.2.le.trans h2.1.le, Icc_subset_Ioo h1.1 h2.2⟩

/-- **Improper integration on a half-line.** If `φ_x = −b − g` on `(α, ∞)`, `b` is continuous and
nonnegative there, `g` is integrable on `(α, ∞)`, `φ → A` at `α⁺` and `φ → B` at `+∞`, then `b`
is integrable on `(α, ∞)` and `∫_{(α,∞)} b = A − B − ∫_{(α,∞)} g`. -/
theorem integral_Ioi_bulk_eq {α : ℝ} {φ bulk src : ℝ → ℝ} {A B : ℝ}
    (hφ : ∀ x ∈ Ioi α, HasDerivAt φ (-bulk x - src x) x)
    (hbc : ContinuousOn bulk (Ioi α)) (hb0 : ∀ x ∈ Ioi α, 0 ≤ bulk x)
    (hsrc : IntegrableOn src (Ioi α))
    (hA : Tendsto φ (𝓝[>] α) (𝓝 A)) (hB : Tendsto φ atTop (𝓝 B)) :
    IntegrableOn bulk (Ioi α) ∧ ∫ x in Ioi α, bulk x = A - B - ∫ x in Ioi α, src x := by
  have hfst : Tendsto Prod.fst (𝓝[>] α ×ˢ (atTop : Filter ℝ)) (𝓝[>] α) := tendsto_fst
  have hsnd : Tendsto Prod.snd (𝓝[>] α ×ˢ (atTop : Filter ℝ)) atTop := tendsto_snd
  have hcov : AECover (volume.restrict (Ioi α)) (𝓝[>] α ×ˢ (atTop : Filter ℝ))
      fun i => Icc i.1 i.2 :=
    ((aecover_Ioi_of_Ioi (hfst.mono_right nhdsWithin_le_nhds)).inter (aecover_Iic hsnd)).superset
      (fun _ _ hx => ⟨hx.1.le, hx.2⟩) fun _ => measurableSet_Icc
  refine integrableOn_bulk_of_aecover measurableSet_Ioi hcov ?_ hφ hbc hb0 hsrc (hA.comp hfst)
    (hB.comp hsnd)
  filter_upwards [hfst.eventually (Ioo_mem_nhdsGT (lt_add_one α)),
    hsnd.eventually (eventually_ge_atTop (α + 1))] with i h1 h2
  exact ⟨h1.2.le.trans h2, fun x hx => lt_of_lt_of_le h1.1 hx.1⟩

/-! ### The multiplier `𝓜U` -/

/-- The multiplier `𝓜U` of the proof of Proposition 6.1: `U + 2(f₁/f₁ₓ)(U_x + iσ₁f₁U)` for
`x < x₁`, `U` on `[x₁, x₂]`, and `U + 2(f₂/f₂ₓ)(U_x + iσ₂f₂U)` for `x > x₂`. -/
@[expose] noncomputable def sourceMultiplier (f₁ f₂ : ℝ → ℝ) (σ₁ σ₂ x₁ x₂ : ℝ) (U : ℝ → ℂ)
    (x : ℝ) : ℂ :=
  if x < x₁ then U x + 2 * (f₁ x / deriv f₁ x) * (deriv U x + σ₁ * f₁ x * I * U x)
  else if x ≤ x₂ then U x
  else U x + 2 * (f₂ x / deriv f₂ x) * (deriv U x + σ₂ * f₂ x * I * U x)

theorem sourceMultiplier_of_lt {f₁ f₂ : ℝ → ℝ} {σ₁ σ₂ x₁ x₂ : ℝ} {U : ℝ → ℂ} {x : ℝ}
    (hx : x < x₁) : sourceMultiplier f₁ f₂ σ₁ σ₂ x₁ x₂ U x =
      U x + 2 * (f₁ x / deriv f₁ x) * (deriv U x + σ₁ * f₁ x * I * U x) := by
  rw [sourceMultiplier, ite_eq_left hx]

theorem sourceMultiplier_of_mem_Icc {f₁ f₂ : ℝ → ℝ} {σ₁ σ₂ x₁ x₂ : ℝ} {U : ℝ → ℂ} {x : ℝ}
    (hx : x ∈ Icc x₁ x₂) : sourceMultiplier f₁ f₂ σ₁ σ₂ x₁ x₂ U x = U x := by
  rw [sourceMultiplier, ite_eq_right (not_lt.2 hx.1), ite_eq_left hx.2]

theorem sourceMultiplier_of_gt {f₁ f₂ : ℝ → ℝ} {σ₁ σ₂ x₁ x₂ : ℝ} {U : ℝ → ℂ} {x : ℝ}
    (h₁₂ : x₁ ≤ x₂) (hx : x₂ < x) : sourceMultiplier f₁ f₂ σ₁ σ₂ x₁ x₂ U x =
      U x + 2 * (f₂ x / deriv f₂ x) * (deriv U x + σ₂ * f₂ x * I * U x) := by
  rw [sourceMultiplier, ite_eq_right (not_lt.2 (h₁₂.trans hx.le)), ite_eq_right (not_le.2 hx)]

/-! ### Local facts on the allowed intervals and at the turning points -/

/-- A solution of `U_xx = H` on `(0, ∞)` (pointwise, with `U` differentiable) is `C¹` at every
point of `(0, ∞)`. -/
theorem contDiffAt_one_of_hasDerivAt_deriv {U : ℝ → ℂ} {H : ℝ → ℂ}
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧ HasDerivAt (deriv U) (H x) x)
    {x : ℝ} (hx : 0 < x) : ContDiffAt ℝ 1 U x := by
  have h : ContDiffOn ℝ (0 + 1) U (Ioi 0) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (hU y hy).1.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact fun y hy => (hU y hy).2.continuousAt.continuousWithinAt
  rw [zero_add] at h
  exact h.contDiffAt (Ioi_mem_nhds hx)

/-- On an allowed interval `t` (open, inside `(0, ∞)`, `F > 0` there) with `f = s√F` on `t`:
`f` is `C²` on `t`, `f² = F` and `f_x = (s√F)_x` there. -/
theorem contDiffOn_sq_deriv_of_eq_sign_mul_sqrt {t : Set ℝ} (ht : IsOpen t) (ht0 : t ⊆ Ioi 0)
    {F f : ℝ → ℝ} {s : ℝ}
    (hF : ContDiffOn ℝ 2 F (Ioi 0)) (hFpos : ∀ x ∈ t, 0 < F x) (hs : s = 1 ∨ s = -1)
    (hf : ∀ x ∈ t, f x = s * Real.sqrt (F x)) :
    ContDiffOn ℝ 2 f t ∧ (∀ x ∈ t, f x ^ 2 = F x) ∧
      ∀ x ∈ t, deriv f x = deriv (fun y => s * Real.sqrt (F y)) x := by
  have hs2 : s ^ 2 = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  refine ⟨(contDiffOn_const.mul ((hF.mono ht0).sqrt fun x hx => (hFpos x hx).ne')).congr hf,
    fun x hx => ?_, fun x hx => ?_⟩
  · rw [hf x hx, mul_pow, hs2, one_mul, Real.sq_sqrt (hFpos x hx).le]
  · have hev : f =ᶠ[𝓝 x] fun y => s * Real.sqrt (F y) :=
      Filter.eventually_of_mem (ht.mem_nhds hx) hf
    exact hev.deriv_eq

/-- At the left turning point `x₁` (`F > 0` on `(0, x₁)`, `F < 0` on `(x₁, x₂)`, `F'(x₁) ≠ 0`):
`F(x₁) = 0` and `F'(x₁) < 0`. -/
theorem eq_zero_and_deriv_neg_of_left_turning_point {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₁₂ : x₁ < x₂)
    {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ 2 F (Ioi 0)) (hF₁ : ∀ x ∈ Ioo 0 x₁, 0 < F x)
    (hFm : ∀ x ∈ Ioo x₁ x₂, F x < 0) (hdF₁ : deriv F x₁ ≠ 0) :
    F x₁ = 0 ∧ deriv F x₁ < 0 := by
  have hFc : ContinuousAt F x₁ := hF.continuousOn.continuousAt (Ioi_mem_nhds hx₁)
  have hd : HasDerivAt F (deriv F x₁) x₁ :=
    (hF.contDiffAt (Ioi_mem_nhds hx₁)).differentiableAt (by norm_num) |>.hasDerivAt
  have h0 : F x₁ = 0 := by
    refine le_antisymm ?_ ?_
    · refine le_of_tendsto (hFc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi x₁))) ?_
      filter_upwards [Ioo_mem_nhdsGT hx₁₂] with y hy
      exact (hFm y hy).le
    · refine ge_of_tendsto (hFc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio x₁))) ?_
      filter_upwards [Ioo_mem_nhdsLT hx₁] with y hy
      exact (hF₁ y hy).le
  refine ⟨h0, lt_of_le_of_ne (not_lt.1 fun h => ?_) hdF₁⟩
  obtain ⟨y, hy, hy'⟩ := ((eventually_pos_right_of_deriv_pos hd h0 h).and
    (Ioo_mem_nhdsGT hx₁₂)).exists
  exact absurd (hFm y hy') (not_lt.2 hy.le)

/-- At the right turning point `x₂` (`F < 0` on `(x₁, x₂)`, `F > 0` on `(x₂, ∞)`, `F'(x₂) ≠ 0`):
`F(x₂) = 0` and `F'(x₂) > 0`. -/
theorem eq_zero_and_deriv_pos_of_right_turning_point {x₁ x₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₁₂ : x₁ < x₂) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ 2 F (Ioi 0)) (hFm : ∀ x ∈ Ioo x₁ x₂, F x < 0)
    (hF₂ : ∀ x ∈ Ioi x₂, 0 < F x) (hdF₂ : deriv F x₂ ≠ 0) :
    F x₂ = 0 ∧ 0 < deriv F x₂ := by
  have hx₂ : 0 < x₂ := hx₁.trans hx₁₂
  have hFc : ContinuousAt F x₂ := hF.continuousOn.continuousAt (Ioi_mem_nhds hx₂)
  have hd : HasDerivAt F (deriv F x₂) x₂ :=
    (hF.contDiffAt (Ioi_mem_nhds hx₂)).differentiableAt (by norm_num) |>.hasDerivAt
  have h0 : F x₂ = 0 := by
    refine le_antisymm ?_ ?_
    · refine le_of_tendsto (hFc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio x₂))) ?_
      filter_upwards [Ioo_mem_nhdsLT hx₁₂] with y hy
      exact (hFm y hy).le
    · refine ge_of_tendsto (hFc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi x₂))) ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hF₂ y hy).le
  refine ⟨h0, lt_of_le_of_ne (not_lt.1 fun h => ?_) hdF₂.symm⟩
  obtain ⟨y, hy, hy'⟩ := ((eventually_pos_left_of_deriv_neg hd h0 h).and
    (Ioo_mem_nhdsLT hx₁₂)).exists
  exact absurd (hFm y hy') (not_lt.2 hy.le)

/-! ### Continuity of the multiplier -/

/-- The allowed-interval multiplier `U + 2(f/f_x)(U_x + iσfU)` is continuous at a point where `f`,
`f_x`, `U`, `U_x` are continuous and `f_x ≠ 0`. -/
private theorem si_continuousAt_mult {f : ℝ → ℝ} {U : ℝ → ℂ} {σ x : ℝ}
    (hf : ContinuousAt f x) (hf' : ContinuousAt (deriv f) x) (hfx : deriv f x ≠ 0)
    (hU : ContinuousAt U x) (hU' : ContinuousAt (deriv U) x) :
    ContinuousAt (fun y => U y + 2 * (f y / deriv f y) * (deriv U y + σ * f y * I * U y)) x := by
  have hfc : ContinuousAt (fun y => ((f y : ℝ) : ℂ)) x :=
    continuous_ofReal.continuousAt.comp hf
  have hf'c : ContinuousAt (fun y => ((deriv f y : ℝ) : ℂ)) x :=
    continuous_ofReal.continuousAt.comp hf'
  exact hU.add ((continuousAt_const.mul (hfc.div hf'c (ofReal_ne_zero.2 hfx))).mul
    (hU'.add (((continuousAt_const.mul hfc).mul continuousAt_const).mul hU)))

/-- If `f/f_x → 0` and `f` has a limit along `l ≤ 𝓝 x_j`, the allowed-interval multiplier tends to
`U(x_j)` along `l`. -/
private theorem si_tendsto_mult {f : ℝ → ℝ} {U : ℝ → ℂ} {σ xj c : ℝ} {l : Filter ℝ}
    (hl : l ≤ 𝓝 xj) (hq : Tendsto (fun y => f y / deriv f y) l (𝓝 0))
    (hf : Tendsto f l (𝓝 c)) (hU : ContinuousAt U xj) (hU' : ContinuousAt (deriv U) xj) :
    Tendsto (fun y => U y + 2 * (f y / deriv f y) * (deriv U y + σ * f y * I * U y)) l
      (𝓝 (U xj)) := by
  have hq' : Tendsto (fun y => ((f y : ℝ) : ℂ) / ((deriv f y : ℝ) : ℂ)) l (𝓝 0) := by
    have h := (continuous_ofReal.tendsto 0).comp hq
    simpa only [Function.comp_def, ofReal_div, ofReal_zero] using h
  have hf' : Tendsto (fun y => ((f y : ℝ) : ℂ)) l (𝓝 (c : ℂ)) :=
    (continuous_ofReal.tendsto c).comp hf
  have hUl := hU.tendsto.mono_left hl
  have h2 : Tendsto (fun _ : ℝ => (2 : ℂ)) l (𝓝 2) := tendsto_const_nhds
  have hσ : Tendsto (fun _ : ℝ => (σ : ℂ)) l (𝓝 σ) := tendsto_const_nhds
  have hI : Tendsto (fun _ : ℝ => I) l (𝓝 I) := tendsto_const_nhds
  have h := hUl.add ((h2.mul hq').mul ((hU'.tendsto.mono_left hl).add
    (((hσ.mul hf').mul hI).mul hUl)))
  convert h using 2
  simp

/-- A function with the right one-sided limits on both sides of `x` is continuous at `x`. -/
private theorem si_continuousAt_of_left_right {M : ℝ → ℂ} {x : ℝ}
    (hl : Tendsto M (𝓝[<] x) (𝓝 (M x))) (hr : Tendsto M (𝓝[>] x) (𝓝 (M x))) :
    ContinuousAt M x :=
  continuousAt_iff_continuous_left'_right'.2 ⟨hl, hr⟩

/-- **Continuity of `𝓜U` (`L > 0`).** Under the hypotheses of the global identity, the
multiplier `𝓜U` is continuous on `(0, ∞)`: on the allowed intervals `f_j/f_{j,x}` is continuous,
and at the turning points `f_j/f_{j,x} → 0` (the first claim of (4.6)), so `𝓜U → U(x_j)`. -/
theorem continuousOn_sourceMultiplier {x₁ x₂ s₁ s₂ σ₁ σ₂ : ℝ} (hx₁ : 0 < x₁) (hx₁₂ : x₁ < x₂)
    {U H : ℝ → ℂ} {F f₁ f₂ : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Ioi 0))
    (hF₁ : ∀ x ∈ Ioo 0 x₁, 0 < F x) (hFm : ∀ x ∈ Ioo x₁ x₂, F x < 0)
    (hF₂ : ∀ x ∈ Ioi x₂, 0 < F x) (hdF₁ : deriv F x₁ ≠ 0) (hdF₂ : deriv F x₂ ≠ 0)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧ HasDerivAt (deriv U) (H x) x)
    (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (hf₁ : ∀ x ∈ Ioo 0 x₁, f₁ x = s₁ * Real.sqrt (F x))
    (hf₂ : ∀ x ∈ Ioi x₂, f₂ x = s₂ * Real.sqrt (F x))
    (hf₁x : ∀ x ∈ Ioo 0 x₁, deriv f₁ x ≠ 0) (hf₂x : ∀ x ∈ Ioi x₂, deriv f₂ x ≠ 0) :
    ContinuousOn (sourceMultiplier f₁ f₂ σ₁ σ₂ x₁ x₂ U) (Ioi 0) := by
  have hx₂ : 0 < x₂ := hx₁.trans hx₁₂
  obtain ⟨hF₁0, hdF₁'⟩ := eq_zero_and_deriv_neg_of_left_turning_point hx₁ hx₁₂ hF hF₁ hFm hdF₁
  obtain ⟨hF₂0, hdF₂'⟩ := eq_zero_and_deriv_pos_of_right_turning_point hx₁ hx₁₂ hF hFm hF₂ hdF₂
  obtain ⟨hf₁c, -, hf₁d⟩ := contDiffOn_sq_deriv_of_eq_sign_mul_sqrt isOpen_Ioo
    Ioo_subset_Ioi_self hF hF₁ hs₁ hf₁
  obtain ⟨hf₂c, -, hf₂d⟩ := contDiffOn_sq_deriv_of_eq_sign_mul_sqrt isOpen_Ioi
    (Ioi_subset_Ioi hx₂.le) hF hF₂ hs₂ hf₂
  have hUc : ∀ x ∈ Ioi (0 : ℝ), ContinuousAt U x := fun x hx => (hU x hx).1.continuousAt
  have hU'c : ∀ x ∈ Ioi (0 : ℝ), ContinuousAt (deriv U) x := fun x hx =>
    (hU x hx).2.continuousAt
  have hEq₁ : ∀ x ∈ Iio x₁, sourceMultiplier f₁ f₂ σ₁ σ₂ x₁ x₂ U x =
      U x + 2 * (f₁ x / deriv f₁ x) * (deriv U x + σ₁ * f₁ x * I * U x) :=
    fun x hx => sourceMultiplier_of_lt hx
  have hEq₂ : ∀ x ∈ Ioi x₂, sourceMultiplier f₁ f₂ σ₁ σ₂ x₁ x₂ U x =
      U x + 2 * (f₂ x / deriv f₂ x) * (deriv U x + σ₂ * f₂ x * I * U x) :=
    fun x hx => sourceMultiplier_of_gt hx₁₂.le hx
  have hEqm : ∀ x ∈ Icc x₁ x₂, sourceMultiplier f₁ f₂ σ₁ σ₂ x₁ x₂ U x = U x :=
    fun x hx => sourceMultiplier_of_mem_Icc hx
  -- the turning-point limits of the allowed multipliers
  have hq₁ : Tendsto (fun y => f₁ y / deriv f₁ y) (𝓝[<] x₁) (𝓝 0) := by
    refine (tendsto_khat_div_deriv_left hs₁ (hF.contDiffAt (Ioi_mem_nhds hx₁)) hF₁0
      hdF₁').congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hx₁] with y hy
    rw [hf₁d y hy, hf₁ y hy]
  have hq₂ : Tendsto (fun y => f₂ y / deriv f₂ y) (𝓝[>] x₂) (𝓝 0) := by
    refine (tendsto_khat_div_deriv_right hs₂ (hF.contDiffAt (Ioi_mem_nhds hx₂)) hF₂0
      hdF₂').congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [hf₂d y hy, hf₂ y hy]
  have hsq : ∀ {s x : ℝ}, 0 < x → ContinuousAt (fun y => s * Real.sqrt (F y)) x := fun hx =>
    continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
      (hF.continuousOn.continuousAt (Ioi_mem_nhds hx)))
  have hl₁ : Tendsto f₁ (𝓝[<] x₁) (𝓝 (s₁ * Real.sqrt (F x₁))) := by
    refine ((hsq hx₁).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hx₁] with y hy
    exact (hf₁ y hy).symm
  have hl₂ : Tendsto f₂ (𝓝[>] x₂) (𝓝 (s₂ * Real.sqrt (F x₂))) := by
    refine ((hsq hx₂).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hf₂ y hy).symm
  have hT₁ := si_tendsto_mult (σ := σ₁) nhdsWithin_le_nhds hq₁ hl₁ (hUc x₁ hx₁) (hU'c x₁ hx₁)
  have hT₂ := si_tendsto_mult (σ := σ₂) nhdsWithin_le_nhds hq₂ hl₂ (hUc x₂ hx₂) (hU'c x₂ hx₂)
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  rcases lt_trichotomy x x₁ with h | rfl | h
  · refine (si_continuousAt_mult (σ := σ₁) (hf₁c.continuousOn.continuousAt
      (isOpen_Ioo.mem_nhds ⟨hx, h⟩)) ((hf₁c.continuousOn_deriv_of_isOpen isOpen_Ioo
        (by norm_num)).continuousAt (isOpen_Ioo.mem_nhds ⟨hx, h⟩)) (hf₁x x ⟨hx, h⟩) (hUc x hx)
          (hU'c x hx)).congr ?_
    exact Filter.eventually_of_mem (Iio_mem_nhds h) fun y hy => (hEq₁ y hy).symm
  · refine si_continuousAt_of_left_right ?_ ?_
    · rw [hEqm x ⟨le_rfl, hx₁₂.le⟩]
      refine hT₁.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hEq₁ y hy).symm
    · rw [hEqm x ⟨le_rfl, hx₁₂.le⟩]
      refine ((hUc x hx).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hx₁₂] with y hy
      exact (hEqm y ⟨hy.1.le, hy.2.le⟩).symm
  · rcases lt_trichotomy x x₂ with h' | rfl | h'
    · refine (hUc x hx).congr ?_
      exact Filter.eventually_of_mem (Ioo_mem_nhds h h') fun y hy =>
        (hEqm y ⟨hy.1.le, hy.2.le⟩).symm
    · refine si_continuousAt_of_left_right ?_ ?_
      · rw [hEqm x ⟨hx₁₂.le, le_rfl⟩]
        refine ((hUc x hx).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [Ioo_mem_nhdsLT hx₁₂] with y hy
        exact (hEqm y ⟨hy.1.le, hy.2.le⟩).symm
      · rw [hEqm x ⟨hx₁₂.le, le_rfl⟩]
        refine hT₂.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (hEq₂ y hy).symm
    · refine (si_continuousAt_mult (σ := σ₂) (hf₂c.continuousOn.continuousAt
        (isOpen_Ioi.mem_nhds h')) ((hf₂c.continuousOn_deriv_of_isOpen isOpen_Ioi
          (by norm_num)).continuousAt (isOpen_Ioi.mem_nhds h')) (hf₂x x h') (hUc x hx)
            (hU'c x hx)).congr ?_
      exact Filter.eventually_of_mem (Ioi_mem_nhds h') fun y hy => (hEq₂ y hy).symm

/-- **Continuity of `𝓜U` (`L = 0`).** If `f` is `C²` on `(0, ∞)` with `f_x ≠ 0` and a zero `x₀`, and
`U`, `U_x` are differentiable on `(0, ∞)`, then the multiplier `𝓜U` with the single turning point
`x₁ = x₂ = x₀` is continuous on `(0, ∞)`: both allowed multipliers equal `U` at `x₀`. -/
theorem continuousOn_sourceMultiplier_L0 {f : ℝ → ℝ} {U H : ℝ → ℂ} {x₀ σ₁ σ₂ : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioi 0)) (hf0 : f x₀ = 0) (hfx : ∀ x ∈ Ioi (0 : ℝ), deriv f x ≠ 0)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧ HasDerivAt (deriv U) (H x) x) :
    ContinuousOn (sourceMultiplier f f σ₁ σ₂ x₀ x₀ U) (Ioi 0) := by
  have hc : ∀ (σ : ℝ), ∀ x ∈ Ioi (0 : ℝ), ContinuousAt
      (fun y => U y + 2 * (f y / deriv f y) * (deriv U y + σ * f y * I * U y)) x :=
    fun σ x hx => si_continuousAt_mult (hf.continuousOn.continuousAt (Ioi_mem_nhds hx))
      ((hf.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).continuousAt
        (Ioi_mem_nhds hx)) (hfx x hx) (hU x hx).1.continuousAt (hU x hx).2.continuousAt
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  rcases lt_trichotomy x x₀ with h | rfl | h
  · exact (hc σ₁ x hx).congr (Filter.eventually_of_mem (Iio_mem_nhds h) fun y hy =>
      (sourceMultiplier_of_lt hy).symm)
  · have hMx : sourceMultiplier f f σ₁ σ₂ x x U x = U x :=
      sourceMultiplier_of_mem_Icc ⟨le_rfl, le_rfl⟩
    have hv : ∀ σ : ℝ, U x + 2 * (f x / deriv f x) * (deriv U x + σ * f x * I * U x) = U x :=
      fun σ => by simp [hf0]
    refine si_continuousAt_of_left_right ?_ ?_
    · have h1 := (hc σ₁ x hx).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio x))
      rw [hv, ← hMx] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (sourceMultiplier_of_lt hy).symm
    · have h1 := (hc σ₂ x hx).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi x))
      rw [hv, ← hMx] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (sourceMultiplier_of_gt le_rfl hy).symm
  · exact (hc σ₂ x hx).congr (Filter.eventually_of_mem (Ioi_mem_nhds h) fun y hy =>
      (sourceMultiplier_of_gt le_rfl hy).symm)

end ModeStability.AllAngular

end
