module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityAux
public import ModeStability.AllAngular.GlobalIdentity

/-!
# The current identity with a source, (6.3) of the all-angular paper

Source: the all-angular research notes in preparation, Section 6, proof of Proposition 6.1,
pp. 7–8. Put `γ = k̂/k̂_x` on the allowed intervals and
`𝓜U = U + 2γ(U_x + ik̂U)` for `x < x₁`, `𝓜U = U` on `[x₁, x₂]`, `𝓜U = U + 2γ(U_x − ik̂U)` for
`x > x₂`. the sourced current includes a forcing term; its integral yields the source identity
(6.3), where `𝓑[U]` is the sum of the three
nonnegative integrals of (5.3).

As in `ModeStability.AllAngular.GlobalIdentity`, everything is abstract on the coordinate interval
`(0, ∞)`, with physical endpoints `0⁺` and `+∞`; the paper's source `F` is called `G` and the
potential `k² − V` is called `F`, so (6.1) reads `U_xx + F U = G`, here in the pointwise form
`HasDerivAt (deriv U) (−F U + G)`, with `G` integrable on a compact `[y₁, y₂] ⊂ (0, ∞)` and zero
outside it. The signs `σ₁`, `σ₂` (in the paper `+1` on `x < x₁`, `−1` on `x > x₂`) and the signs
`s₁`, `s₂` of `k̂ = s√F` are arbitrary `±1`. The endpoint limits of the outer currents are
hypotheses, as in `eqOn_zero_of_global_current_L`.

* `integral_bulk_eq_source_L`, `lintegral_bulk_eq_source_L`: (6.3) for `L > 0` (forbidden
  interval `[x₁, x₂]`), with Bochner integrals (and integrability of the bulk terms) and with
  lower Lebesgue integrals (`𝓑[U] < ∞`);
* `integral_bulk_eq_source_L0`, `lintegral_bulk_eq_source_L0`: (6.3) for `L = 0` (a single zero
  `x₀` of `k̂ = k`, no forbidden interval).

The multiplier `sourceMultiplier`, its continuity, the pointwise derivatives of the currents with
a source and the improper-integration lemma are in `ModeStability.AllAngular.SourceIdentityAux`.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-! ### Local facts -/

/-- On an allowed interval, the phase-free current of `f` agrees with the current of `s√F` used
in `tendsto_current_at_turning_point_left`/`_right`. -/
private theorem si_current_congr {t : Set ℝ} (ht : IsOpen t) {F f : ℝ → ℝ} {s σ : ℝ}
    {U : ℝ → ℂ} (hf : ∀ x ∈ t, f x = s * Real.sqrt (F x)) {x : ℝ} (hx : x ∈ t) :
    -((s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x) *
          ‖deriv U x + σ * (s * Real.sqrt (F x)) * I * U x‖ ^ 2 -
        (deriv U x * (starRingEnd ℂ) (U x)).re =
      -(f x / deriv f x) * ‖deriv U x + σ * f x * I * U x‖ ^ 2 -
        (deriv U x * (starRingEnd ℂ) (U x)).re := by
  have hev : f =ᶠ[𝓝 x] fun y => s * Real.sqrt (F y) :=
    Filter.eventually_of_mem (ht.mem_nhds hx) hf
  rw [hev.deriv_eq, hf x hx, Complex.ofReal_mul]

/-- The bulk density `((2f_x² − f f_xx)/f_x²)|U_x + iσfU|²` is continuous on an open set where `f`
is `C²` with `f_x ≠ 0` and `U`, `U_x` are continuous. -/
private theorem si_continuousOn_bulk {t : Set ℝ} (ht : IsOpen t) {f : ℝ → ℝ} {U : ℝ → ℂ}
    {σ : ℝ} (hf : ContDiffOn ℝ 2 f t) (hfx : ∀ x ∈ t, deriv f x ≠ 0)
    (hU : ContinuousOn U t) (hU' : ContinuousOn (deriv U) t) :
    ContinuousOn (fun x => (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 *
      ‖deriv U x + σ * f x * I * U x‖ ^ 2) t := by
  have h0 : ContinuousOn f t := hf.continuousOn
  have h1 : ContinuousOn (deriv f) t := hf.continuousOn_deriv_of_isOpen ht (by norm_num)
  have h2 : ContinuousOn (deriv (deriv f)) t :=
    (hf.deriv_of_isOpen ht (m := 1) (by norm_num)).continuousOn_deriv_of_isOpen ht le_rfl
  have hc : ContinuousOn (fun x => ((f x : ℝ) : ℂ)) t := continuous_ofReal.comp_continuousOn h0
  refine ((((h1.pow 2).const_smul (2 : ℝ)).sub (h0.mul h2)).div (h1.pow 2)
    fun x hx => pow_ne_zero 2 (hfx x hx)).mul ?_
  exact ((hU'.add (((continuousOn_const.mul hc).mul continuousOn_const).mul hU)).norm).pow 2

/-! ### The source term -/

/-- If `G` is integrable on `[y₁, y₂] ⊂ (0, ∞)` and zero outside, and `M` is continuous on
`(0, ∞)`, then `G conj(M)` is integrable on `ℝ`. -/
private theorem si_integrable_source {G M : ℝ → ℂ} {y₁ y₂ : ℝ} (hy₁ : 0 < y₁)
    (hG : IntegrableOn G (Icc y₁ y₂)) (hGs : ∀ x ∉ Icc y₁ y₂, G x = 0)
    (hM : ContinuousOn M (Ioi 0)) : Integrable fun x => G x * (starRingEnd ℂ) (M x) := by
  have hsub : Icc y₁ y₂ ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hy₁ hx.1
  have h := hG.mul_continuousOn (continuous_conj.comp_continuousOn (hM.mono hsub)) isCompact_Icc
  refine (integrableOn_iff_integrable_of_support_subset fun x hx => ?_).1 h
  by_contra hx'
  exact (Function.mem_support.1 hx) (by rw [hGs x hx', zero_mul])

/-- The real part of the source term, `Re(G conj(M))`, is integrable, vanishes outside
`[y₁, y₂]`, and its integral over `[y₁, y₂]` is `Re ∫ G conj(M)`. -/
private theorem si_source_re {G M : ℝ → ℂ} {y₁ y₂ : ℝ} (hy₁ : 0 < y₁)
    (hGs : ∀ x ∉ Icc y₁ y₂, G x = 0) (hGM : Integrable fun x => G x * (starRingEnd ℂ) (M x)) :
    Integrable (fun x => (G x * (starRingEnd ℂ) (M x)).re) ∧
      (∀ x ∉ Ioi (0 : ℝ), (G x * (starRingEnd ℂ) (M x)).re = 0) ∧
      (∀ x ∉ Icc y₁ y₂, (G x * (starRingEnd ℂ) (M x)).re = 0) ∧
      ∫ x in Icc y₁ y₂, (G x * (starRingEnd ℂ) (M x)).re =
        (∫ x in Icc y₁ y₂, G x * (starRingEnd ℂ) (M x)).re := by
  have h2 : ∀ x ∉ Icc y₁ y₂, (G x * (starRingEnd ℂ) (M x)).re = 0 := fun x hx => by
    rw [hGs x hx, zero_mul, zero_re]
  refine ⟨by simpa only [Complex.reCLM_apply] using Complex.reCLM.integrable_comp hGM,
    fun x hx => h2 x fun h => hx (lt_of_lt_of_le hy₁ h.1), h2, ?_⟩
  simpa only [Complex.reCLM_apply] using Complex.reCLM.integral_comp_comm hGM.integrableOn

/-- Splitting `∫_{(0,∞)}` at `x₁ < x₂`: `∫_{(0,x₁)} + ∫_{[x₁,x₂]} + ∫_{(x₂,∞)} = ∫_{(0,∞)}`. -/
private theorem si_split {g : ℝ → ℝ} (hg : Integrable g) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₁₂ : x₁ < x₂) :
    (∫ x in Ioo 0 x₁, g x) + (∫ x in Icc x₁ x₂, g x) + ∫ x in Ioi x₂, g x =
      ∫ x in Ioi 0, g x := by
  rw [← setIntegral_union (Set.disjoint_left.2 fun x h1 h2 => absurd h2.1 (not_le.2 h1.2))
    measurableSet_Icc hg.integrableOn hg.integrableOn, Ioo_union_Icc_eq_Ioc hx₁ hx₁₂.le,
    ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hg.integrableOn hg.integrableOn,
    Ioc_union_Ioi_eq_Ioi (hx₁.trans hx₁₂).le]

/-- For an integrable function that is nonnegative on `s`, the lower Lebesgue integral of its
positive part is the real number `∫_s b ≥ 0`. -/
private theorem si_lintegral {s : Set ℝ} (hs : MeasurableSet s) {b : ℝ → ℝ}
    (hi : IntegrableOn b s) (h0 : ∀ x ∈ s, 0 ≤ b x) :
    ∫⁻ x in s, ENNReal.ofReal (b x) = ENNReal.ofReal (∫ x in s, b x) ∧ 0 ≤ ∫ x in s, b x :=
  ⟨(ofReal_integral_eq_lintegral_ofReal hi ((ae_restrict_iff' hs).2 (ae_of_all _ h0))).symm,
    setIntegral_nonneg hs h0⟩

/-! ### The identity (6.3) for `L > 0` -/

/-- **The identity (6.3) for `L > 0`.** Let `F` be `C²` on `(0, ∞)`, positive on the allowed
intervals `(0, x₁)` and `(x₂, ∞)`, negative on the forbidden interval `(x₁, x₂)`, with simple zeros
at the turning points, and let `U_xx = −F U + G` on `(0, ∞)`, with the source `G` integrable on a
compact `[y₁, y₂] ⊂ (0, ∞)` and zero outside it. On the allowed intervals let `f_j = s_j√F`
(`s_j = ±1`) with `f_{j,x} ≠ 0` and `a_j = (2f_{j,x}² − f_j f_{j,xx})/f_{j,x}² ≥ 0`, and let the
phase-free currents `−(f_j/f_{j,x})|U_x + iσⱼf_jU|² − Re(U_x Ū)` (`σⱼ = ±1`) tend to `0` at the
physical endpoints `0⁺` and `+∞`. Then the outer bulk terms are integrable and
`𝓑[U] = ∫_{(0,x₁)} a₁|U_x + iσ₁f₁U|² + ∫_{[x₁,x₂]} (|U_x|² − F|U|²) + ∫_{(x₂,∞)} a₂|U_x + iσ₂f₂U|²`
equals `−Re ∫_{[y₁,y₂]} G conj(𝓜U)`. -/
theorem integral_bulk_eq_source_L {x₁ x₂ s₁ s₂ σ₁ σ₂ y₁ y₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₁₂ : x₁ < x₂) {U G : ℝ → ℂ} {F f₁ f₂ : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Ioi 0))
    (hF₁ : ∀ x ∈ Ioo 0 x₁, 0 < F x) (hFm : ∀ x ∈ Ioo x₁ x₂, F x < 0)
    (hF₂ : ∀ x ∈ Ioi x₂, 0 < F x) (hdF₁ : deriv F x₁ ≠ 0) (hdF₂ : deriv F x₂ ≠ 0)
    (hy₁ : 0 < y₁) (hGi : IntegrableOn G (Icc y₁ y₂)) (hGs : ∀ x ∉ Icc y₁ y₂, G x = 0)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((F x : ℝ) : ℂ) * U x + G x) x)
    (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (hf₁ : ∀ x ∈ Ioo 0 x₁, f₁ x = s₁ * Real.sqrt (F x))
    (hf₂ : ∀ x ∈ Ioi x₂, f₂ x = s₂ * Real.sqrt (F x))
    (hf₁x : ∀ x ∈ Ioo 0 x₁, deriv f₁ x ≠ 0) (hf₂x : ∀ x ∈ Ioi x₂, deriv f₂ x ≠ 0)
    (hE₁ : ∀ x ∈ Ioo 0 x₁,
      0 ≤ (2 * deriv f₁ x ^ 2 - f₁ x * deriv (deriv f₁) x) / deriv f₁ x ^ 2)
    (hE₂ : ∀ x ∈ Ioi x₂,
      0 ≤ (2 * deriv f₂ x ^ 2 - f₂ x * deriv (deriv f₂) x) / deriv f₂ x ^ 2)
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hJ₁ : Tendsto (fun x => -(f₁ x / deriv f₁ x) * ‖deriv U x + σ₁ * f₁ x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) (𝓝[>] 0) (𝓝 0))
    (hJ₂ : Tendsto (fun x => -(f₂ x / deriv f₂ x) * ‖deriv U x + σ₂ * f₂ x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) atTop (𝓝 0)) :
    IntegrableOn (fun x => (2 * deriv f₁ x ^ 2 - f₁ x * deriv (deriv f₁) x) / deriv f₁ x ^ 2 *
        ‖deriv U x + σ₁ * f₁ x * I * U x‖ ^ 2) (Ioo 0 x₁) ∧
      IntegrableOn (fun x => ‖deriv U x‖ ^ 2 - F x * ‖U x‖ ^ 2) (Icc x₁ x₂) ∧
      IntegrableOn (fun x => (2 * deriv f₂ x ^ 2 - f₂ x * deriv (deriv f₂) x) / deriv f₂ x ^ 2 *
        ‖deriv U x + σ₂ * f₂ x * I * U x‖ ^ 2) (Ioi x₂) ∧
      (∫ x in Ioo 0 x₁, (2 * deriv f₁ x ^ 2 - f₁ x * deriv (deriv f₁) x) / deriv f₁ x ^ 2 *
          ‖deriv U x + σ₁ * f₁ x * I * U x‖ ^ 2) +
        (∫ x in Icc x₁ x₂, (‖deriv U x‖ ^ 2 - F x * ‖U x‖ ^ 2)) +
        (∫ x in Ioi x₂, (2 * deriv f₂ x ^ 2 - f₂ x * deriv (deriv f₂) x) / deriv f₂ x ^ 2 *
          ‖deriv U x + σ₂ * f₂ x * I * U x‖ ^ 2) =
      -(∫ x in Icc y₁ y₂,
          G x * (starRingEnd ℂ) (sourceMultiplier f₁ f₂ σ₁ σ₂ x₁ x₂ U x)).re := by
  have hx₂ : 0 < x₂ := hx₁.trans hx₁₂
  obtain ⟨hF₁0, hdF₁'⟩ := eq_zero_and_deriv_neg_of_left_turning_point hx₁ hx₁₂ hF hF₁ hFm hdF₁
  obtain ⟨hF₂0, hdF₂'⟩ := eq_zero_and_deriv_pos_of_right_turning_point hx₁ hx₁₂ hF hFm hF₂ hdF₂
  obtain ⟨hf₁c, hf₁sq, -⟩ := contDiffOn_sq_deriv_of_eq_sign_mul_sqrt isOpen_Ioo
    Ioo_subset_Ioi_self hF hF₁ hs₁ hf₁
  obtain ⟨hf₂c, hf₂sq, -⟩ := contDiffOn_sq_deriv_of_eq_sign_mul_sqrt isOpen_Ioi
    (Ioi_subset_Ioi hx₂.le) hF hF₂ hs₂ hf₂
  have hUc : ContinuousOn U (Ioi 0) := fun x hx =>
    (hU x hx).1.continuousAt.continuousWithinAt
  have hU'c : ContinuousOn (deriv U) (Ioi 0) := fun x hx =>
    (hU x hx).2.continuousAt.continuousWithinAt
  have hMc := continuousOn_sourceMultiplier (σ₁ := σ₁) (σ₂ := σ₂) hx₁ hx₁₂ hF hF₁ hFm hF₂ hdF₁
    hdF₂ hU hs₁ hs₂ hf₁ hf₂ hf₁x hf₂x
  have hGM := si_integrable_source hy₁ hGi hGs hMc
  obtain ⟨hg, hg0', hg0, hre⟩ := si_source_re hy₁ hGs hGM
  set M := sourceMultiplier f₁ f₂ σ₁ σ₂ x₁ x₂ U with hM
  set g : ℝ → ℝ := fun x => (G x * (starRingEnd ℂ) (M x)).re with hg_def
  -- the turning-point limits (4.6) of the outer currents
  have hT₁ := (tendsto_current_at_turning_point_left (σ := σ₁) hs₁
    (hF.contDiffAt (Ioi_mem_nhds hx₁)) hF₁0 hdF₁'
      (contDiffAt_one_of_hasDerivAt_deriv hU hx₁)).congr'
      (Filter.eventually_of_mem (Ioo_mem_nhdsLT hx₁) fun y hy => si_current_congr isOpen_Ioo hf₁ hy)
  have hT₂ := (tendsto_current_at_turning_point_right (σ := σ₂) hs₂
    (hF.contDiffAt (Ioi_mem_nhds hx₂)) hF₂0 hdF₂'
      (contDiffAt_one_of_hasDerivAt_deriv hU hx₂)).congr'
      (Filter.eventually_of_mem self_mem_nhdsWithin fun y hy =>
        si_current_congr isOpen_Ioi hf₂ hy)
  -- the allowed intervals
  have hd₁ : ∀ x ∈ Ioo 0 x₁, HasDerivAt
      (fun x => -(f₁ x / deriv f₁ x) * ‖deriv U x + σ₁ * f₁ x * I * U x‖ ^ 2 -
        (deriv U x * (starRingEnd ℂ) (U x)).re)
      (-((2 * deriv f₁ x ^ 2 - f₁ x * deriv (deriv f₁) x) / deriv f₁ x ^ 2 *
        ‖deriv U x + σ₁ * f₁ x * I * U x‖ ^ 2) - g x) x := by
    intro x hx
    have hUx := hU x hx.1
    rw [← hf₁sq x hx] at hUx
    refine (hasDerivAt_phaseFree_current_source hσ₁
      (differentiableAt_of_contDiffOn_on isOpen_Ioo hf₁c hx)
      (differentiableAt_deriv_of_contDiffOn_on isOpen_Ioo hf₁c hx) (hf₁x x hx) hUx.1
      hUx.2).congr_deriv ?_
    simp only [hg_def, hM]
    rw [sourceMultiplier_of_lt hx.2, neg_mul]
  have hd₂ : ∀ x ∈ Ioi x₂, HasDerivAt
      (fun x => -(f₂ x / deriv f₂ x) * ‖deriv U x + σ₂ * f₂ x * I * U x‖ ^ 2 -
        (deriv U x * (starRingEnd ℂ) (U x)).re)
      (-((2 * deriv f₂ x ^ 2 - f₂ x * deriv (deriv f₂) x) / deriv f₂ x ^ 2 *
        ‖deriv U x + σ₂ * f₂ x * I * U x‖ ^ 2) - g x) x := by
    intro x hx
    have hUx := hU x (hx₂.trans hx)
    rw [← hf₂sq x hx] at hUx
    refine (hasDerivAt_phaseFree_current_source hσ₂
      (differentiableAt_of_contDiffOn_on isOpen_Ioi hf₂c hx)
      (differentiableAt_deriv_of_contDiffOn_on isOpen_Ioi hf₂c hx) (hf₂x x hx) hUx.1
      hUx.2).congr_deriv ?_
    simp only [hg_def, hM]
    rw [sourceMultiplier_of_gt hx₁₂.le hx, neg_mul]
  obtain ⟨hi₁, he₁⟩ := integral_Ioo_bulk_eq hx₁ hd₁
    (si_continuousOn_bulk isOpen_Ioo hf₁c hf₁x (hUc.mono Ioo_subset_Ioi_self)
      (hU'c.mono Ioo_subset_Ioi_self)) (fun x hx => mul_nonneg (hE₁ x hx) (sq_nonneg _))
    hg.integrableOn hJ₁ hT₁
  obtain ⟨hi₂, he₂⟩ := integral_Ioi_bulk_eq hd₂
    (si_continuousOn_bulk isOpen_Ioi hf₂c hf₂x (hUc.mono (Ioi_subset_Ioi hx₂.le))
      (hU'c.mono (Ioi_subset_Ioi hx₂.le))) (fun x hx => mul_nonneg (hE₂ x hx) (sq_nonneg _))
    hg.integrableOn hT₂ hJ₂
  -- the forbidden interval: the fundamental theorem of calculus
  have hsub : Icc x₁ x₂ ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le hx₁ hx.1
  have hbm : ContinuousOn (fun x => ‖deriv U x‖ ^ 2 - F x * ‖U x‖ ^ 2) (Icc x₁ x₂) :=
    ((hU'c.norm.pow 2).sub (hF.continuousOn.mul (hUc.norm.pow 2))).mono hsub
  have hdm : ∀ x ∈ uIcc x₁ x₂, HasDerivAt (fun y => -(deriv U y * (starRingEnd ℂ) (U y)).re)
      (-(‖deriv U x‖ ^ 2 - F x * ‖U x‖ ^ 2) - g x) x := by
    intro x hx
    rw [uIcc_of_le hx₁₂.le] at hx
    refine (hasDerivAt_neg_re_flux_source (hU x (hsub hx)).1 (hU x (hsub hx)).2).congr_deriv ?_
    simp only [hg_def, hM]
    rw [sourceMultiplier_of_mem_Icc hx]
  have hbmi : IntervalIntegrable (fun x => ‖deriv U x‖ ^ 2 - F x * ‖U x‖ ^ 2) volume x₁ x₂ :=
    (hbm.mono (by rw [uIcc_of_le hx₁₂.le])).intervalIntegrable
  have hm := intervalIntegral.integral_eq_sub_of_hasDerivAt hdm (hbmi.neg.sub hg.intervalIntegrable)
  rw [intervalIntegral.integral_sub (f := fun x => -(‖deriv U x‖ ^ 2 - F x * ‖U x‖ ^ 2))
    hbmi.neg hg.intervalIntegrable, intervalIntegral.integral_neg,
    intervalIntegral.integral_of_le hx₁₂.le, intervalIntegral.integral_of_le hx₁₂.le,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hm
  -- the source term
  have hsplit := si_split hg hx₁ hx₁₂
  have e₁ : ∫ x in Ioi 0, g x = ∫ x, g x := setIntegral_eq_integral_of_forall_compl_eq_zero hg0'
  have e₂ : ∫ x in Icc y₁ y₂, g x = ∫ x, g x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hg0
  refine ⟨hi₁, hbm.integrableOn_compact isCompact_Icc, hi₂, ?_⟩
  linarith

/-- **The identity (6.3) for `L > 0`, with `𝓑[U]` as a lower Lebesgue integral.** Under the
hypotheses of `integral_bulk_eq_source_L`, the sum `𝓑[U]` of the three nonnegative integrals of
(5.3) is finite and equals `−Re ∫_{[y₁,y₂]} G conj(𝓜U)`. -/
theorem lintegral_bulk_eq_source_L {x₁ x₂ s₁ s₂ σ₁ σ₂ y₁ y₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₁₂ : x₁ < x₂) {U G : ℝ → ℂ} {F f₁ f₂ : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Ioi 0))
    (hF₁ : ∀ x ∈ Ioo 0 x₁, 0 < F x) (hFm : ∀ x ∈ Ioo x₁ x₂, F x < 0)
    (hF₂ : ∀ x ∈ Ioi x₂, 0 < F x) (hdF₁ : deriv F x₁ ≠ 0) (hdF₂ : deriv F x₂ ≠ 0)
    (hy₁ : 0 < y₁) (hGi : IntegrableOn G (Icc y₁ y₂)) (hGs : ∀ x ∉ Icc y₁ y₂, G x = 0)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((F x : ℝ) : ℂ) * U x + G x) x)
    (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (hf₁ : ∀ x ∈ Ioo 0 x₁, f₁ x = s₁ * Real.sqrt (F x))
    (hf₂ : ∀ x ∈ Ioi x₂, f₂ x = s₂ * Real.sqrt (F x))
    (hf₁x : ∀ x ∈ Ioo 0 x₁, deriv f₁ x ≠ 0) (hf₂x : ∀ x ∈ Ioi x₂, deriv f₂ x ≠ 0)
    (hE₁ : ∀ x ∈ Ioo 0 x₁,
      0 ≤ (2 * deriv f₁ x ^ 2 - f₁ x * deriv (deriv f₁) x) / deriv f₁ x ^ 2)
    (hE₂ : ∀ x ∈ Ioi x₂,
      0 ≤ (2 * deriv f₂ x ^ 2 - f₂ x * deriv (deriv f₂) x) / deriv f₂ x ^ 2)
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hJ₁ : Tendsto (fun x => -(f₁ x / deriv f₁ x) * ‖deriv U x + σ₁ * f₁ x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) (𝓝[>] 0) (𝓝 0))
    (hJ₂ : Tendsto (fun x => -(f₂ x / deriv f₂ x) * ‖deriv U x + σ₂ * f₂ x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) atTop (𝓝 0)) :
    (∫⁻ x in Ioo 0 x₁, ENNReal.ofReal
          ((2 * deriv f₁ x ^ 2 - f₁ x * deriv (deriv f₁) x) / deriv f₁ x ^ 2 *
            ‖deriv U x + σ₁ * f₁ x * I * U x‖ ^ 2)) +
        (∫⁻ x in Icc x₁ x₂, ENNReal.ofReal (‖deriv U x‖ ^ 2 - F x * ‖U x‖ ^ 2)) +
        (∫⁻ x in Ioi x₂, ENNReal.ofReal
          ((2 * deriv f₂ x ^ 2 - f₂ x * deriv (deriv f₂) x) / deriv f₂ x ^ 2 *
            ‖deriv U x + σ₂ * f₂ x * I * U x‖ ^ 2)) < ⊤ ∧
      ((∫⁻ x in Ioo 0 x₁, ENNReal.ofReal
          ((2 * deriv f₁ x ^ 2 - f₁ x * deriv (deriv f₁) x) / deriv f₁ x ^ 2 *
            ‖deriv U x + σ₁ * f₁ x * I * U x‖ ^ 2)) +
        (∫⁻ x in Icc x₁ x₂, ENNReal.ofReal (‖deriv U x‖ ^ 2 - F x * ‖U x‖ ^ 2)) +
        (∫⁻ x in Ioi x₂, ENNReal.ofReal
          ((2 * deriv f₂ x ^ 2 - f₂ x * deriv (deriv f₂) x) / deriv f₂ x ^ 2 *
            ‖deriv U x + σ₂ * f₂ x * I * U x‖ ^ 2))).toReal =
      -(∫ x in Icc y₁ y₂,
          G x * (starRingEnd ℂ) (sourceMultiplier f₁ f₂ σ₁ σ₂ x₁ x₂ U x)).re := by
  obtain ⟨hi₁, him, hi₂, he⟩ := integral_bulk_eq_source_L hx₁ hx₁₂ hF hF₁ hFm hF₂ hdF₁ hdF₂
    hy₁ hGi hGs hU hs₁ hs₂ hf₁ hf₂ hf₁x hf₂x hE₁ hE₂ hσ₁ hσ₂ hJ₁ hJ₂
  have hF₁0 := (eq_zero_and_deriv_neg_of_left_turning_point hx₁ hx₁₂ hF hF₁ hFm hdF₁).1
  have hF₂0 := (eq_zero_and_deriv_pos_of_right_turning_point hx₁ hx₁₂ hF hFm hF₂ hdF₂).1
  have hFle : ∀ x ∈ Icc x₁ x₂, F x ≤ 0 := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | h1
    · exact hF₁0.le
    rcases eq_or_lt_of_le hx.2 with rfl | h2
    · exact hF₂0.le
    exact (hFm x ⟨h1, h2⟩).le
  obtain ⟨l₁, p₁⟩ := si_lintegral measurableSet_Ioo hi₁
    fun x hx => mul_nonneg (hE₁ x hx) (sq_nonneg _)
  obtain ⟨lm, pm⟩ := si_lintegral measurableSet_Icc him fun x hx => by
    have := hFle x hx
    nlinarith [sq_nonneg ‖deriv U x‖, sq_nonneg ‖U x‖]
  obtain ⟨l₂, p₂⟩ := si_lintegral measurableSet_Ioi hi₂
    fun x hx => mul_nonneg (hE₂ x hx) (sq_nonneg _)
  rw [l₁, lm, l₂, ← ENNReal.ofReal_add p₁ pm, ← ENNReal.ofReal_add (add_nonneg p₁ pm) p₂, he]
  exact ⟨ENNReal.ofReal_lt_top, ENNReal.toReal_ofReal (he ▸ add_nonneg (add_nonneg p₁ pm) p₂)⟩

/-! ### The identity (6.3) for `L = 0` -/

/-- **The identity (6.3) for `L = 0`.** Let `f` be `C²` on `(0, ∞)` with a zero `x₀ > 0`,
`f_x ≠ 0` and `a = (2f_x² − f f_xx)/f_x² ≥ 0` on `(0, ∞)`, let `U_xx = −f² U + G` on `(0, ∞)` with
the source `G` integrable on a compact `[y₁, y₂] ⊂ (0, ∞)` and zero outside it, and let the
phase-free currents `−(f/f_x)|U_x + iσⱼfU|² − Re(U_x Ū)` (`σ₁` at `0⁺`, `σ₂` at `+∞`, `σⱼ = ±1`)
tend to `0` at the physical endpoints. Then the bulk terms are integrable and
`∫_{(0,x₀)} a|U_x + iσ₁fU|² + ∫_{(x₀,∞)} a|U_x + iσ₂fU|² = −Re ∫_{[y₁,y₂]} G conj(𝓜U)`, where
`𝓜U` has the single turning point `x₁ = x₂ = x₀`. -/
theorem integral_bulk_eq_source_L0 {f : ℝ → ℝ} {U G : ℝ → ℂ} {x₀ σ₁ σ₂ y₁ y₂ : ℝ}
    (hx₀ : 0 < x₀) (hf : ContDiffOn ℝ 2 f (Ioi 0)) (hf0 : f x₀ = 0)
    (hfx : ∀ x ∈ Ioi (0 : ℝ), deriv f x ≠ 0)
    (hE : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2)
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hy₁ : 0 < y₁) (hGi : IntegrableOn G (Icc y₁ y₂)) (hGs : ∀ x ∉ Icc y₁ y₂, G x = 0)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((f x ^ 2 : ℝ) : ℂ) * U x + G x) x)
    (hJ₁ : Tendsto (fun x => -(f x / deriv f x) * ‖deriv U x + σ₁ * f x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) (𝓝[>] 0) (𝓝 0))
    (hJ₂ : Tendsto (fun x => -(f x / deriv f x) * ‖deriv U x + σ₂ * f x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) atTop (𝓝 0)) :
    IntegrableOn (fun x => (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 *
        ‖deriv U x + σ₁ * f x * I * U x‖ ^ 2) (Ioo 0 x₀) ∧
      IntegrableOn (fun x => (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 *
        ‖deriv U x + σ₂ * f x * I * U x‖ ^ 2) (Ioi x₀) ∧
      (∫ x in Ioo 0 x₀, (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 *
          ‖deriv U x + σ₁ * f x * I * U x‖ ^ 2) +
        (∫ x in Ioi x₀, (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 *
          ‖deriv U x + σ₂ * f x * I * U x‖ ^ 2) =
      -(∫ x in Icc y₁ y₂, G x * (starRingEnd ℂ) (sourceMultiplier f f σ₁ σ₂ x₀ x₀ U x)).re := by
  have hUc : ContinuousOn U (Ioi 0) := fun x hx =>
    (hU x hx).1.continuousAt.continuousWithinAt
  have hU'c : ContinuousOn (deriv U) (Ioi 0) := fun x hx =>
    (hU x hx).2.continuousAt.continuousWithinAt
  have hMc := continuousOn_sourceMultiplier_L0 (σ₁ := σ₁) (σ₂ := σ₂) hf hf0 hfx hU
  have hGM := si_integrable_source hy₁ hGi hGs hMc
  obtain ⟨hg, hg0', hg0, hre⟩ := si_source_re hy₁ hGs hGM
  set M := sourceMultiplier f f σ₁ σ₂ x₀ x₀ U with hM
  set g : ℝ → ℝ := fun x => (G x * (starRingEnd ℂ) (M x)).re with hg_def
  -- the matching (4.6) at the simple zero `x₀`
  have hT := fun σ : ℝ => tendsto_phaseFree_current_at_zero (σ := σ)
    (hf.continuousOn.continuousAt (Ioi_mem_nhds hx₀))
    (differentiableAt_deriv_of_contDiffOn_on isOpen_Ioi hf hx₀).continuousAt hf0
    (hfx x₀ hx₀) (hUc.continuousAt (Ioi_mem_nhds hx₀)) (hU'c.continuousAt (Ioi_mem_nhds hx₀))
  have hd : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ x ∈ Ioi (0 : ℝ), HasDerivAt
      (fun x => -(f x / deriv f x) * ‖deriv U x + σ * f x * I * U x‖ ^ 2 -
        (deriv U x * (starRingEnd ℂ) (U x)).re)
      (-((2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 *
        ‖deriv U x + σ * f x * I * U x‖ ^ 2) -
        (G x * (starRingEnd ℂ) (U x + 2 * (f x / deriv f x) *
          (deriv U x + σ * f x * I * U x))).re) x := fun σ hσ x hx =>
    (hasDerivAt_phaseFree_current_source hσ (differentiableAt_of_contDiffOn_on isOpen_Ioi hf hx)
      (differentiableAt_deriv_of_contDiffOn_on isOpen_Ioi hf hx) (hfx x hx) (hU x hx).1
      (hU x hx).2).congr_deriv (by rw [neg_mul])
  have hbc := fun σ : ℝ => si_continuousOn_bulk (σ := σ) isOpen_Ioi hf hfx hUc hU'c
  obtain ⟨hi₁, he₁⟩ := integral_Ioo_bulk_eq (src := g) hx₀
    (fun x hx => (hd σ₁ hσ₁ x hx.1).congr_deriv (by
      simp only [hg_def, hM]
      rw [sourceMultiplier_of_lt hx.2]))
    ((hbc σ₁).mono Ioo_subset_Ioi_self) (fun x hx => mul_nonneg (hE x hx.1) (sq_nonneg _))
    hg.integrableOn hJ₁ ((hT σ₁).mono_left nhdsWithin_le_nhds)
  obtain ⟨hi₂, he₂⟩ := integral_Ioi_bulk_eq (src := g)
    (fun x hx => (hd σ₂ hσ₂ x (hx₀.trans hx)).congr_deriv (by
      simp only [hg_def, hM]
      rw [sourceMultiplier_of_gt le_rfl hx]))
    ((hbc σ₂).mono (Ioi_subset_Ioi hx₀.le))
    (fun x hx => mul_nonneg (hE x (hx₀.trans hx)) (sq_nonneg _))
    hg.integrableOn ((hT σ₂).mono_left nhdsWithin_le_nhds) hJ₂
  have hsplit : (∫ x in Ioo 0 x₀, g x) + ∫ x in Ioi x₀, g x = ∫ x in Ioi 0, g x := by
    rw [← integral_Ioc_eq_integral_Ioo, ← setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi hg.integrableOn hg.integrableOn, Ioc_union_Ioi_eq_Ioi hx₀.le]
  have e₁ : ∫ x in Ioi 0, g x = ∫ x, g x := setIntegral_eq_integral_of_forall_compl_eq_zero hg0'
  have e₂ : ∫ x in Icc y₁ y₂, g x = ∫ x, g x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hg0
  refine ⟨hi₁, hi₂, ?_⟩
  linarith

/-- **The identity (6.3) for `L = 0`, with `𝓑[U]` as a lower Lebesgue integral.** Under the
hypotheses of `integral_bulk_eq_source_L0`, the sum `𝓑[U]` of the two nonnegative integrals is
finite and equals `−Re ∫_{[y₁,y₂]} G conj(𝓜U)`. -/
theorem lintegral_bulk_eq_source_L0 {f : ℝ → ℝ} {U G : ℝ → ℂ} {x₀ σ₁ σ₂ y₁ y₂ : ℝ}
    (hx₀ : 0 < x₀) (hf : ContDiffOn ℝ 2 f (Ioi 0)) (hf0 : f x₀ = 0)
    (hfx : ∀ x ∈ Ioi (0 : ℝ), deriv f x ≠ 0)
    (hE : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2)
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hy₁ : 0 < y₁) (hGi : IntegrableOn G (Icc y₁ y₂)) (hGs : ∀ x ∉ Icc y₁ y₂, G x = 0)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((f x ^ 2 : ℝ) : ℂ) * U x + G x) x)
    (hJ₁ : Tendsto (fun x => -(f x / deriv f x) * ‖deriv U x + σ₁ * f x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) (𝓝[>] 0) (𝓝 0))
    (hJ₂ : Tendsto (fun x => -(f x / deriv f x) * ‖deriv U x + σ₂ * f x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) atTop (𝓝 0)) :
    (∫⁻ x in Ioo 0 x₀, ENNReal.ofReal
          ((2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 *
            ‖deriv U x + σ₁ * f x * I * U x‖ ^ 2)) +
        (∫⁻ x in Ioi x₀, ENNReal.ofReal
          ((2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 *
            ‖deriv U x + σ₂ * f x * I * U x‖ ^ 2)) < ⊤ ∧
      ((∫⁻ x in Ioo 0 x₀, ENNReal.ofReal
          ((2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 *
            ‖deriv U x + σ₁ * f x * I * U x‖ ^ 2)) +
        (∫⁻ x in Ioi x₀, ENNReal.ofReal
          ((2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 *
            ‖deriv U x + σ₂ * f x * I * U x‖ ^ 2))).toReal =
      -(∫ x in Icc y₁ y₂, G x * (starRingEnd ℂ) (sourceMultiplier f f σ₁ σ₂ x₀ x₀ U x)).re := by
  obtain ⟨hi₁, hi₂, he⟩ := integral_bulk_eq_source_L0 hx₀ hf hf0 hfx hE hσ₁ hσ₂ hy₁ hGi hGs hU
    hJ₁ hJ₂
  obtain ⟨l₁, p₁⟩ := si_lintegral measurableSet_Ioo hi₁
    fun x hx => mul_nonneg (hE x hx.1) (sq_nonneg _)
  obtain ⟨l₂, p₂⟩ := si_lintegral measurableSet_Ioi hi₂
    fun x hx => mul_nonneg (hE x (hx₀.trans hx)) (sq_nonneg _)
  rw [l₁, l₂, ← ENNReal.ofReal_add p₁ p₂, he]
  exact ⟨ENNReal.ofReal_lt_top, ENNReal.toReal_ofReal (he ▸ add_nonneg p₁ p₂)⟩

end ModeStability.AllAngular

end
