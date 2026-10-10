module

public import Mathlib
public import ModeStability.AllAngular.Prop61Interface
public import ModeStability.AllAngular.NormalizationFacts
public import ModeStability.AllAngular.SourceIdentityRAux
public import ModeStability.AllAngular.CoordinateCoefficientsAux
public import ModeStability.AllAngular.TurningPointGeometry
public import ModeStability.Frozen.AllAngular.AngularPositivity

/-!
# Regularity of the radial multiplier for Proposition 6.1

Source: the all-angular research notes in preparation, pp. 7–8, (6.1), (6.3),
and the multiplier in the proof of Proposition 6.1. The integrated source
equation gives C¹ regularity. At a simple turning point the quotient
`k̂/k̂_x` equals `2F/(Δg² F')` on the allowed side, where `F = g⁴(K²-LΔ)`.
This expression vanishes at the turning point. The case `L = 0` uses the
smooth signed frequency `g²K` through corotation.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular.P61

open NormalizationFacts CoordinateCoefficients CoefficientIdentities

private theorem pm_g_smooth {M Q e ω r : ℝ} (hM : 0 < M)
    (hr : outerHorizon M Q < r) : ContDiffAt ℝ 2 (normalizationG M Q e ω) r := by
  by_cases hn : e / ω < 2 * M
  · rw [normalizationG_eq_one hn]
    exact contDiffAt_const
  · rw [normalizationG_eq_static hn]
    by_cases hd : 0 < M ^ 2 - Q ^ 2
    · rw [staticSolutionAA_eq_staticSolution hd]
      exact contDiffAt_staticSolution (abs_lt_of_sub_sq_pos hM hd) hr
    · rw [staticSolutionAA_eq_extremal hd]
      exact contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const)
        (sub_M_pos_of_outerHorizon_lt hr).ne'

private theorem pm_g_pos {M Q e ω r : ℝ} (hM : 0 < M)
    (hr : outerHorizon M Q < r) : 0 < normalizationG M Q e ω r := by
  by_cases hn : e / ω < 2 * M
  · rw [normalizationG_eq_one hn]; exact one_pos
  · rw [normalizationG_eq_static hn]; exact staticSolutionAA_pos hM hr

private theorem pm_corotation {M Q e ω ρ₁ ρ₂ : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) : outerHorizon M Q < e / ω := by
  have ha : 0 < outerHorizon M Q := by
    unfold outerHorizon
    exact add_pos_of_pos_of_nonneg h.1 (Real.sqrt_nonneg _)
  have he := (lt_div_iff₀ ha).mp h.2.2.2.2.1
  exact (lt_div_iff₀ h.2.2.2.1).mpr (by linarith)

/-- Both normalizations are continuous on the exterior. -/
theorem normalizationG_continuousOn {M Q e ω : ℝ} (hM : 0 < M) :
    ContinuousOn (normalizationG M Q e ω) (Ioi (outerHorizon M Q)) :=
  fun _ hr => (pm_g_smooth hM hr).continuousAt.continuousWithinAt

/-- An integrated radial source solution makes `U = R/g` C¹ on the exterior,
for either normalization and for subextremal or extremal parameters. -/
theorem uR_contDiffOn_one {M Q e ω L : ℝ} (hM : 0 < M)
    {R S : ℝ → ℂ} (h : IsRadialSolutionWithSourceL M Q e ω L R S) :
    ContDiffOn ℝ 1 (uR M Q e ω R) (Ioi (outerHorizon M Q)) := by
  have hp : ContinuousOn (delta M Q) (Ioi (outerHorizon M Q)) :=
    (contDiff_delta M Q).continuous.continuousOn
  have hp0 : ∀ r ∈ Ioi (outerHorizon M Q), delta M Q r ≠ 0 :=
    fun r hr => (delta_pos_of_lt hr).ne'
  have hq : ContinuousOn (fun r => radialK e ω r ^ 2 / delta M Q r - L)
      (Ioi (outerHorizon M Q)) :=
    (((contDiff_radialK e ω).continuous.pow 2).continuousOn.div hp hp0).sub
      continuousOn_const
  have hRC := source_solution_contDiffOn_one hp hp0 hq h.1
    (fun b hb c hc => (h.2 b hb c hc).1) (fun b hb c hc => (h.2 b hb c hc).2)
  have hg : ContDiffOn ℝ 1 (fun r => (normalizationG M Q e ω r : ℂ))
      (Ioi (outerHorizon M Q)) := by
    intro r hr
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp r
      ((pm_g_smooth hM hr).of_le (by norm_num))).contDiffWithinAt
  apply (hRC.mul (hg.inv (fun r hr => ofReal_ne_zero.mpr (pm_g_pos hM hr).ne'))).congr
  intro r hr
  simp [uR, div_eq_mul_inv]

/-- The integrated source equation makes the transformed first derivative
continuous, including through turning points. -/
theorem uxR_continuousOn {M Q e ω L : ℝ} (hM : 0 < M)
    {R S : ℝ → ℂ} (h : IsRadialSolutionWithSourceL M Q e ω L R S) :
    ContinuousOn (uxR M Q e ω R) (Ioi (outerHorizon M Q)) := by
  have hU := uR_contDiffOn_one hM h
  have hd : ContinuousOn (deriv (uR M Q e ω R)) (Ioi (outerHorizon M Q)) := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi] at hU
    exact contDiffOn_zero.mp hU.2.2
  have hg : ContinuousOn (normalizationG M Q e ω) (Ioi (outerHorizon M Q)) :=
    fun _ hr => (pm_g_smooth hM hr).continuousAt.continuousWithinAt
  exact (continuous_ofReal.comp_continuousOn
    ((contDiff_delta M Q).continuous.continuousOn.mul (hg.pow 2))).mul hd

/-- The coordinate measure density is continuous on the exterior. -/
theorem wR_continuousOn {M Q e ω : ℝ} (hM : 0 < M) :
    ContinuousOn (wR M Q e ω) (Ioi (outerHorizon M Q)) := by
  have hg : ContinuousOn (normalizationG M Q e ω) (Ioi (outerHorizon M Q)) :=
    fun _ hr => (pm_g_smooth hM hr).continuousAt.continuousWithinAt
  exact continuousOn_const.div
    ((contDiff_delta M Q).continuous.continuousOn.mul (hg.pow 2))
    (fun r hr => (mul_pos (delta_pos_of_lt hr) (sq_pos_of_pos (pm_g_pos hM hr))).ne')

private theorem pm_tendsto_ite {α β : Type*} {l : Filter α} {t : Filter β}
    {f g : α → β} {p : α → Prop} [DecidablePred p]
    (hf : Tendsto f l t) (hg : Tendsto g l t) :
    Tendsto (fun x => if p x then f x else g x) l t := by
  rw [Filter.tendsto_def] at hf hg ⊢
  intro s hs
  filter_upwards [hf s hs, hg s hs] with x hfx hgx
  by_cases hx : p x
  · simpa [hx] using hfx
  · simpa [hx] using hgx

private theorem pm_k_zero (M Q e ω : ℝ) :
    effectiveK M Q e ω 0 = fun r => normalizationG M Q e ω r ^ 2 * radialK e ω r := by
  funext r
  unfold effectiveK
  rw [mul_right_comm, sign_mul_sqrt_L0]
  ring

private theorem pm_k_sq {M Q e ω L r : ℝ} (hL : 0 ≤ L)
    (hr : outerHorizon M Q < r) (hp : L * delta M Q r < radialK e ω r ^ 2) :
    effectiveK M Q e ω L r ^ 2 =
      normalizationG M Q e ω r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r) := by
  have hk : radialK e ω r ≠ 0 := by
    intro hz
    rw [hz] at hp
    nlinarith [mul_nonneg hL (delta_pos_of_lt hr).le]
  have hs : (SignType.sign (radialK e ω r) : ℝ) ^ 2 = 1 := by
    rcases hk.lt_or_gt with hn | hn
    · rw [sign_neg hn]; norm_num
    · rw [sign_pos hn]; norm_num
  unfold effectiveK
  rw [mul_pow, mul_pow, hs, one_mul, Real.sq_sqrt (sub_pos.mpr hp).le]
  ring

private theorem pm_allowed_props {M Q e ω ρ₁ ρ₂ L r : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hL : 0 ≤ L)
    (hr : outerHorizon M Q < r) (hp : L * delta M Q r < radialK e ω r ^ 2) :
    ContDiffAt ℝ 2 (effectiveK M Q e ω L) r ∧ 0 < khxR M Q e ω L r := by
  have hk : radialK e ω r ≠ 0 := by
    intro hz
    rw [hz] at hp
    nlinarith [mul_nonneg hL (delta_pos_of_lt hr).le]
  exact ⟨contDiffAt_effectiveKAux (pm_g_smooth h.1 hr) hk (sub_pos.mpr hp),
    (angular_positivity M Q e ω L h.1 h.2.1 h.2.2.2.1 hL (e / ω) rfl
      (pm_corotation h) r hr hp).1⟩

private noncomputable def pm_potential (M Q e ω L : ℝ) : ℝ → ℝ :=
  fun r => normalizationG M Q e ω r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r)

private theorem pm_potential_smooth {M Q e ω L r : ℝ} (hM : 0 < M)
    (hr : outerHorizon M Q < r) : ContDiffAt ℝ 2 (pm_potential M Q e ω L) r :=
  ((pm_g_smooth hM hr).pow 4).mul
    (((contDiff_radialK e ω).contDiffAt.pow 2).sub
      (contDiffAt_const.mul (contDiff_delta M Q).contDiffAt))

private theorem pm_ratio_eq {M Q e ω ρ₁ ρ₂ L r : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hL : 0 ≤ L)
    (hr : outerHorizon M Q < r) (hp : L * delta M Q r < radialK e ω r ^ 2) :
    effectiveK M Q e ω L r / khxR M Q e ω L r =
      2 * pm_potential M Q e ω L r /
        (delta M Q r * normalizationG M Q e ω r ^ 2 * deriv (pm_potential M Q e ω L) r) := by
  obtain ⟨hkC, hkx⟩ := pm_allowed_props h hL hr hp
  have he : (fun s => effectiveK M Q e ω L s ^ 2) =ᶠ[𝓝 r] pm_potential M Q e ω L := by
    filter_upwards [Ioi_mem_nhds hr,
      (hasDerivAt_radicand M Q e ω L r).continuousAt.eventually
        (lt_mem_nhds (sub_pos.mpr hp))] with s hs hps
    exact pm_k_sq hL hs (sub_pos.mp hps)
  have hd : deriv (pm_potential M Q e ω L) r =
      2 * effectiveK M Q e ω L r * deriv (effectiveK M Q e ω L) r := by
    rw [← he.deriv_eq]
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      ((hkC.differentiableAt (by norm_num)).hasDerivAt.fun_pow 2).deriv
  have hk0 : effectiveK M Q e ω L r ≠ 0 := by
    have hs := pm_k_sq hL hr hp
    have hf : 0 < normalizationG M Q e ω r ^ 4 *
        (radialK e ω r ^ 2 - L * delta M Q r) :=
      mul_pos (pow_pos (pm_g_pos h.1 hr) 4) (sub_pos.mpr hp)
    intro hz
    rw [hz] at hs
    nlinarith
  have hx0 : delta M Q r * normalizationG M Q e ω r ^ 2 *
      deriv (effectiveK M Q e ω L) r ≠ 0 := hkx.ne'
  rw [hd]
  unfold pm_potential
  rw [← pm_k_sq hL hr hp]
  change effectiveK M Q e ω L r /
      (delta M Q r * normalizationG M Q e ω r ^ 2 * deriv (effectiveK M Q e ω L) r) = _
  have hd0 : delta M Q r * normalizationG M Q e ω r ^ 2 *
      (2 * effectiveK M Q e ω L r * deriv (effectiveK M Q e ω L) r) ≠ 0 := by
    have heq : delta M Q r * normalizationG M Q e ω r ^ 2 *
        (2 * effectiveK M Q e ω L r * deriv (effectiveK M Q e ω L) r) =
        2 * effectiveK M Q e ω L r *
          (delta M Q r * normalizationG M Q e ω r ^ 2 * deriv (effectiveK M Q e ω L) r) := by ring
    rw [heq]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hk0) hx0
  apply (div_eq_div_iff hx0 hd0).mpr
  ring

private theorem pm_k_continuous_of_ne {M Q e ω L r : ℝ} (hM : 0 < M)
    (hr : outerHorizon M Q < r) (hk : radialK e ω r ≠ 0) :
    ContinuousAt (effectiveK M Q e ω L) r := by
  have hb : ContinuousAt (fun s => normalizationG M Q e ω s ^ 2 *
      Real.sqrt (radialK e ω s ^ 2 - L * delta M Q s)) r :=
    ((pm_g_smooth hM hr).continuousAt.pow 2).mul
      (hasDerivAt_radicand M Q e ω L r).continuousAt.sqrt
  rcases hk.lt_or_gt with hk | hk
  · apply ((continuousAt_const (y := (-1 : ℝ))).mul hb).congr
    filter_upwards [(contDiff_radialK e ω).continuous.continuousAt.eventually
      (gt_mem_nhds hk)] with s hs
    simp [effectiveK, sign_neg hs]
  · apply ((continuousAt_const (y := (1 : ℝ))).mul hb).congr
    filter_upwards [(contDiff_radialK e ω).continuous.continuousAt.eventually
      (lt_mem_nhds hk)] with s hs
    simp [effectiveK, sign_pos hs]

private theorem pm_boundary_data {M Q e ω ρ₁ ρ₂ L r : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hL : 0 < L)
    (hr : outerHorizon M Q < r) (hp : radialK e ω r ^ 2 - L * delta M Q r = 0) :
    radialK e ω r ≠ 0 ∧ pm_potential M Q e ω L r = 0 ∧
      deriv (pm_potential M Q e ω L) r ≠ 0 := by
  have hk : radialK e ω r ≠ 0 := by
    intro hz
    rw [hz] at hp
    nlinarith [mul_pos hL (delta_pos_of_lt hr)]
  have ht := mul_abs_K_lt_T h.1 h.2.1 h.2.2.2.1 (pm_corotation h) hr
  rw [mul_div_cancel₀ e h.2.2.2.1.ne'] at ht
  have hT : 0 < delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r := by
    have hn := mul_nonneg (Real.sqrt_nonneg (M ^ 2 - Q ^ 2)) (abs_nonneg (radialK e ω r))
    linarith
  have hP : 2 * radialK e ω r * (2 * ω * r - e) - L * (2 * (r - M)) ≠ 0 := by
    intro hz
    have he := turningPoly_deriv_mul_delta_of_eq_zero hp
    rw [hz, zero_mul] at he
    exact (mul_ne_zero (mul_ne_zero (by norm_num) hk) hT.ne') he.symm
  refine ⟨hk, by simp [pm_potential, hp], ?_⟩
  have hd := (((pm_g_smooth (e := e) (ω := ω) h.1 hr).differentiableAt
    (by norm_num)).hasDerivAt.fun_pow 4).fun_mul
    (hasDerivAt_radicand M Q e ω L r)
  change deriv (fun s => normalizationG M Q e ω s ^ 4 *
    (radialK e ω s ^ 2 - L * delta M Q s)) r ≠ 0
  rw [hd.deriv, hp, mul_zero, zero_add]
  exact mul_ne_zero (pow_ne_zero 4 (pm_g_pos h.1 hr).ne') hP

private theorem pm_glue {U V : ℝ → ℂ} {k γ : ℝ → ℝ} {r : ℝ}
    {p q : ℝ → Prop} [DecidablePred p] [DecidablePred q]
    (hU : ContinuousAt U r) (hV : ContinuousAt V r) (hk : ContinuousAt k r)
    (hγ : ContinuousAt γ r) (hγ0 : γ r = 0) :
    ContinuousAt (fun s => if p s then
      U s + 2 * (γ s : ℂ) * (V s + (k s : ℂ) * I * U s)
      else if q s then U s + 2 * (γ s : ℂ) * (V s - (k s : ℂ) * I * U s)
      else U s) r := by
  have hc : ContinuousAt (fun s => (k s : ℂ)) r := continuous_ofReal.continuousAt.comp hk
  have hg : ContinuousAt (fun s => (γ s : ℂ)) r := continuous_ofReal.continuousAt.comp hγ
  have hp : ContinuousAt (fun s => U s + 2 * (γ s : ℂ) *
      (V s + (k s : ℂ) * I * U s)) r := by fun_prop
  have hq : ContinuousAt (fun s => U s + 2 * (γ s : ℂ) *
      (V s - (k s : ℂ) * I * U s)) r := by fun_prop
  have hp' : Tendsto (fun s => U s + 2 * (γ s : ℂ) *
      (V s + (k s : ℂ) * I * U s)) (𝓝 r) (𝓝 (U r)) := by simpa [hγ0] using hp.tendsto
  have hq' : Tendsto (fun s => U s + 2 * (γ s : ℂ) *
      (V s - (k s : ℂ) * I * U s)) (𝓝 r) (𝓝 (U r)) := by simpa [hγ0] using hq.tendsto
  simpa [ContinuousAt, hγ0] using pm_tendsto_ite (p := p) hp'
    (pm_tendsto_ite (p := q) hq' hU.tendsto)

private theorem pm_kx_continuous {M Q e ω L r : ℝ} (hM : 0 < M)
    (hr : outerHorizon M Q < r) (hk : ContDiffAt ℝ 2 (effectiveK M Q e ω L) r) :
    ContinuousAt (khxR M Q e ω L) r :=
  ((contDiff_delta M Q).continuous.continuousAt.mul
    ((pm_g_smooth hM hr).continuousAt.pow 2)).mul
      (hk.derivWithin (m := 1) (by norm_num)).continuousAt

private theorem pm_kx_zero_pos {M Q e ω ρ₁ ρ₂ r : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hr : outerHorizon M Q < r)
    (hk : radialK e ω r = 0) : 0 < khxR M Q e ω 0 r := by
  have hr0 : 0 < r := by
    have ha : 0 < outerHorizon M Q := by
      unfold outerHorizon
      exact add_pos_of_pos_of_nonneg h.1 (Real.sqrt_nonneg _)
    exact ha.trans hr
  have hf : r * (ω * r - e) = 0 := by
    unfold radialK at hk
    nlinarith only [hk]
  have he : e = ω * r := by
    have hz := (mul_eq_zero.mp hf).resolve_left hr0.ne'
    linarith
  have hd := (((pm_g_smooth (e := e) (ω := ω) h.1 hr).differentiableAt
    (by norm_num)).hasDerivAt.fun_pow 2).fun_mul (hasDerivAt_radialK e ω r)
  unfold khxR xDeriv
  rw [pm_k_zero, hd.deriv, hk, mul_zero, zero_add]
  have hkp : 0 < 2 * ω * r - e := by rw [he]; nlinarith [mul_pos h.2.2.2.1 hr0]
  exact mul_pos (mul_pos (delta_pos_of_lt hr) (sq_pos_of_pos (pm_g_pos h.1 hr)))
    (mul_pos (sq_pos_of_pos (pm_g_pos h.1 hr)) hkp)

private theorem pm_continuous_allowed {M Q e ω ρ₁ ρ₂ L r : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hL : 0 ≤ L)
    {R S : ℝ → ℂ} (hR : IsRadialSolutionWithSourceL M Q e ω L R S)
    (hr : outerHorizon M Q < r) (hp : L * delta M Q r < radialK e ω r ^ 2) :
    ContinuousAt (multR M Q e ω L R) r := by
  classical
  have hU := ((uR_contDiffOn_one h.1 hR).continuousOn r hr).continuousAt (Ioi_mem_nhds hr)
  have hV := (uxR_continuousOn h.1 hR r hr).continuousAt (Ioi_mem_nhds hr)
  obtain ⟨hkC, hkx⟩ := pm_allowed_props h hL hr hp
  have hk := continuous_ofReal.continuousAt.comp hkC.continuousAt
  have hγ := continuous_ofReal.continuousAt.comp
    (hkC.continuousAt.div (pm_kx_continuous h.1 hr hkC) hkx.ne')
  have hep : ∀ᶠ s in 𝓝 r, L * delta M Q s < radialK e ω s ^ 2 := by
    filter_upwards [(hasDerivAt_radicand M Q e ω L r).continuousAt.eventually
      (lt_mem_nhds (sub_pos.mpr hp))] with s hs
    exact sub_pos.mp hs
  have hne : r ≠ e / ω := by
    intro hz
    subst r
    rw [radialK_corotation_eq_zero e h.2.2.2.1.ne'] at hp
    nlinarith [mul_nonneg hL (delta_pos_of_lt hr).le]
  rcases hne.lt_or_gt with hb | hb
  · have hc : ContinuousAt (fun s => uR M Q e ω R s +
        2 * ((effectiveK M Q e ω L s / khxR M Q e ω L s : ℝ) : ℂ) *
          (uxR M Q e ω R s + (effectiveK M Q e ω L s : ℂ) * I * uR M Q e ω R s)) r := by
      fun_prop
    apply hc.congr
    filter_upwards [Ioi_mem_nhds hr, gt_mem_nhds hb, hep] with s hs hb hp
    have hh : s ∈ setAH M Q e ω L := ⟨hs, hb, hp⟩
    simp only [multR, ite_eq_left hh]
  · have hc : ContinuousAt (fun s => uR M Q e ω R s +
        2 * ((effectiveK M Q e ω L s / khxR M Q e ω L s : ℝ) : ℂ) *
          (uxR M Q e ω R s - (effectiveK M Q e ω L s : ℂ) * I * uR M Q e ω R s)) r := by
      fun_prop
    apply hc.congr
    filter_upwards [lt_mem_nhds hb, hep] with s hb hp
    have hn : ¬s < e / ω := not_lt.mpr hb.le
    simp [multR, setAH, setAI, hn, hb, hp]

private theorem pm_continuous_forbidden {M Q e ω L r : ℝ} (hM : 0 < M)
    {R S : ℝ → ℂ} (hR : IsRadialSolutionWithSourceL M Q e ω L R S)
    (hr : outerHorizon M Q < r) (hp : radialK e ω r ^ 2 - L * delta M Q r < 0) :
    ContinuousAt (multR M Q e ω L R) r := by
  classical
  apply (((uR_contDiffOn_one hM hR).continuousOn r hr).continuousAt
    (Ioi_mem_nhds hr)).congr
  filter_upwards [(hasDerivAt_radicand M Q e ω L r).continuousAt.eventually
    (gt_mem_nhds hp)] with s hs
  have hn : ¬L * delta M Q s < radialK e ω s ^ 2 := by linarith
  simp [multR, setAH, setAI, hn]

private theorem pm_continuous_boundary {M Q e ω ρ₁ ρ₂ L r : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hL : 0 < L)
    {R S : ℝ → ℂ} (hR : IsRadialSolutionWithSourceL M Q e ω L R S)
    (hr : outerHorizon M Q < r) (hp : radialK e ω r ^ 2 - L * delta M Q r = 0) :
    ContinuousAt (multR M Q e ω L R) r := by
  classical
  obtain ⟨hk0, hF0, hF'0⟩ := pm_boundary_data h hL hr hp
  have hF := pm_potential_smooth (e := e) (ω := ω) (L := L) h.1 hr
  let γ : ℝ → ℝ := fun s => 2 * pm_potential M Q e ω L s /
    (delta M Q s * normalizationG M Q e ω s ^ 2 * deriv (pm_potential M Q e ω L) s)
  have hγ : ContinuousAt γ r :=
    (continuousAt_const.mul hF.continuousAt).div
      (((contDiff_delta M Q).continuous.continuousAt.mul
        ((pm_g_smooth h.1 hr).continuousAt.pow 2)).mul
          (hF.derivWithin (m := 1) (by norm_num)).continuousAt)
      (mul_ne_zero (mul_ne_zero (delta_pos_of_lt hr).ne'
        (pow_ne_zero 2 (pm_g_pos h.1 hr).ne')) hF'0)
  have hγ0 : γ r = 0 := by simp [γ, hF0]
  have hU := ((uR_contDiffOn_one h.1 hR).continuousOn r hr).continuousAt (Ioi_mem_nhds hr)
  have hV := (uxR_continuousOn h.1 hR r hr).continuousAt (Ioi_mem_nhds hr)
  have hm := pm_glue (p := fun s => s ∈ setAH M Q e ω L)
    (q := fun s => s ∈ setAI M Q e ω L) hU hV
    (pm_k_continuous_of_ne (L := L) h.1 hr hk0) hγ hγ0
  apply hm.congr
  filter_upwards [Ioi_mem_nhds hr] with s hs
  by_cases hh : s ∈ setAH M Q e ω L
  · have he := pm_ratio_eq h hL.le hs hh.2.2
    simp only [multR, ite_eq_left hh]
    rw [he]
  · by_cases hi : s ∈ setAI M Q e ω L
    · have he := pm_ratio_eq h hL.le hs hi.2
      simp only [multR, ite_eq_right hh, ite_eq_left hi]
      rw [he]
    · simp [multR, hh, hi]

private theorem pm_continuous_zero {M Q e ω ρ₁ ρ₂ r : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) {R S : ℝ → ℂ}
    (hR : IsRadialSolutionWithSourceL M Q e ω 0 R S)
    (hr : outerHorizon M Q < r) : ContinuousAt (multR M Q e ω 0 R) r := by
  classical
  by_cases hk : radialK e ω r = 0
  · have hkC : ContDiffAt ℝ 2 (effectiveK M Q e ω 0) r := by
      rw [pm_k_zero]
      exact ((pm_g_smooth h.1 hr).pow 2).mul (contDiff_radialK e ω).contDiffAt
    have hγ := hkC.continuousAt.div (pm_kx_continuous h.1 hr hkC)
      (pm_kx_zero_pos h hr hk).ne'
    have hγ0 : effectiveK M Q e ω 0 r / khxR M Q e ω 0 r = 0 := by
      rw [pm_k_zero]; simp [hk]
    have hU := ((uR_contDiffOn_one h.1 hR).continuousOn r hr).continuousAt (Ioi_mem_nhds hr)
    have hV := (uxR_continuousOn h.1 hR r hr).continuousAt (Ioi_mem_nhds hr)
    exact pm_glue hU hV hkC.continuousAt hγ hγ0
  · apply pm_continuous_allowed h (by norm_num) hR hr
    simpa only [zero_mul] using sq_pos_of_ne_zero hk

/-- The multiplier of (6.3) is continuous on the entire exterior, including
both turning points for `L > 0` and corotation for `L = 0`. -/
theorem multR_continuousOn {M Q e ω ρ₁ ρ₂ L : ℝ}
    (h : Range17 M Q e ω ρ₁ ρ₂) (hL : 0 ≤ L)
    {R S : ℝ → ℂ} {BH BI : ℂ} (hP : SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI) :
    ContinuousOn (multR M Q e ω L R) (Ioi (outerHorizon M Q)) := by
  intro r hr
  apply ContinuousAt.continuousWithinAt
  rcases hL.eq_or_lt with hz | hL
  · subst L
    exact pm_continuous_zero h hP.2.2.1 hr
  · rcases lt_trichotomy (radialK e ω r ^ 2 - L * delta M Q r) 0 with hp | hp | hp
    · exact pm_continuous_forbidden h.1 hP.2.2.1 hr hp
    · exact pm_continuous_boundary h hL hP.2.2.1 hr hp
    · exact pm_continuous_allowed h hL.le hP.2.2.1 hr (sub_pos.mp hp)

end ModeStability.AllAngular.P61

end
