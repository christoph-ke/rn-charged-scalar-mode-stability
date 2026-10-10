module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.AllAngular.RadialPhase
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL
public import ModeStability.AllAngular.GreenFormulaAux
import ModeStability.AllAngular.RealModeExclusionL
import ModeStability.AllAngular.HorizonSolution
import ModeStability.AllAngular.InfinitySolution
import ModeStability.ODE.Uniqueness

/-!
# The Green-formula solution of the inhomogeneous radial problem (6.1)

Source: the all-angular research notes in preparation, p. 7, Section 6, before Proposition 6.1:
for `F ∈ L²(I)` supported in a
compact interval, mode exclusion makes the Wronskian nonzero and yields a unique Green solution
of `U_xx + (k² − V)U = F` with the ingoing and outgoing conditions at the
physical endpoints. In `r` (p. 8, after the proof of Proposition 6.1: `R = gU`, `F = Δg³S`) this
is the radial equation with a source,

  `(ΔR')' + (K²/Δ − L)R = S` on `(a, ∞)`,

in integrated form (`S` is only `L²`), with the horizon condition (1.4) and the infinity
condition (1.5) for some leading coefficients `B_H`, `B_I`.

Main results, in the strictly superradiant range (1.7) (`0 < e`, `0 < ω < e/a`), for `S ∈ L²`
on a compact `[ρ₁, ρ₂] ⊂ (a, ∞)` and `S = 0` off `[ρ₁, ρ₂]`:

* `exists_source_solution`: a solution exists, namely the Green formula
  `R(r) = (R_I(r) ∫_{ρ₁}^r R_H S + R_H(r) ∫_r^{ρ₂} R_I S) / W` built from the normalized solutions
  `R_H` (`exists_horizon_solution`) and `R_I` (`exists_infinity_solution`), whose Wronskian
  `W = Δ(R_H R_I' − R_H' R_I)` is nonzero by Theorem 1.1 (`wronskian_ne_zero`);
* `source_solution_unique`: two solutions agree on `(a, ∞)` (for every real `ω ≠ 0`): their
  difference is a homogeneous mode, which vanishes by Theorem 1.1;
* `existsUnique_source_solution`: both, as `∃!` of a function on the exterior `Ioi a`.

Theorem 1.1 enters as the landed helper `real_mode_exclusion_integralPhase`. The boundary
conditions are local at the endpoints (`horizonConditionL_congr`, `infinityConditionL_congr`) and
compatible with scalar multiples and differences of differentiable functions.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

/-! ### Elementary facts -/

/-- The radial coefficient `K²/Δ − L` is continuous on the exterior. -/
theorem continuousOn_radialCoeff (M Q e ω L : ℝ) :
    ContinuousOn (fun r => (radialK e ω r) ^ 2 / delta M Q r - L) (Ioi (outerHorizon M Q)) := by
  have hK : Continuous (radialK e ω) := by
    unfold radialK
    fun_prop
  exact (((hK.pow 2).continuousOn.div (InfinityUniqueness.continuous_delta M Q).continuousOn
    fun r hr => (InfinityUniqueness.delta_pos_of_lt hr).ne').sub continuousOn_const)

/-- The phase factor `e^{iΘ}` of the horizon condition is differentiable on the exterior. -/
theorem differentiableAt_horizonFactor {M Q e ω r : ℝ} (hr : outerHorizon M Q < r) :
    DifferentiableAt ℝ (fun s : ℝ => exp (I * radialPhase M Q e ω s)) r := by
  have h : HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
    hasDerivAt_integral_radialK_div_delta hr
  exact (h.ofReal_comp.const_mul I).cexp.differentiableAt

/-- The factor `r e^{−iΘ}` of the infinity condition is differentiable on the exterior. -/
theorem differentiableAt_infinityFactor {M Q e ω r : ℝ} (hr : outerHorizon M Q < r) :
    DifferentiableAt ℝ (fun s : ℝ => (s : ℂ) * exp (-(I * radialPhase M Q e ω s))) r := by
  have h : HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
    hasDerivAt_integral_radialK_div_delta hr
  exact (hasDerivAt_id r).ofReal_comp.differentiableAt.mul
    (h.ofReal_comp.const_mul I).neg.cexp.differentiableAt

/-! ### The boundary conditions: locality, scalar multiples, differences -/

/-- The horizon condition only depends on `R` on a right neighbourhood `(a, b)` of the horizon. -/
theorem horizonConditionL_of_eqOn {M Q e ω b : ℝ} {R₁ R₂ : ℝ → ℂ} {B : ℂ}
    (hb : outerHorizon M Q < b) (h : EqOn R₁ R₂ (Ioo (outerHorizon M Q) b))
    (h₁ : HorizonConditionL M Q e ω R₁ B) : HorizonConditionL M Q e ω R₂ B := by
  have hmem := Ioo_mem_nhdsGT hb
  have hE : ∀ᶠ r in 𝓝[>] outerHorizon M Q,
      exp (I * radialPhase M Q e ω r) * R₁ r = exp (I * radialPhase M Q e ω r) * R₂ r := by
    filter_upwards [hmem] with r hr
    rw [h hr]
  have hD : ∀ᶠ r in 𝓝[>] outerHorizon M Q,
      deriv (fun r => exp (I * radialPhase M Q e ω r) * R₁ r) r =
        deriv (fun r => exp (I * radialPhase M Q e ω r) * R₂ r) r := by
    filter_upwards [hmem] with r hr
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    rw [h hs]
  unfold HorizonConditionL at h₁ ⊢
  split_ifs at h₁ ⊢
  · exact h₁.congr' (eventuallyEq_of_mem hmem h) EventuallyEq.rfl
  · exact ⟨h₁.1.congr' (hE.mono fun r hr => by simp only [hr]) EventuallyEq.rfl,
      h₁.2.congr' hD EventuallyEq.rfl⟩

/-- The horizon condition only depends on `R` on a right neighbourhood `(a, b)` of the horizon. -/
theorem horizonConditionL_congr {M Q e ω b : ℝ} {R₁ R₂ : ℝ → ℂ} {B : ℂ}
    (hb : outerHorizon M Q < b) (h : EqOn R₁ R₂ (Ioo (outerHorizon M Q) b)) :
    HorizonConditionL M Q e ω R₁ B ↔ HorizonConditionL M Q e ω R₂ B :=
  ⟨horizonConditionL_of_eqOn hb h, horizonConditionL_of_eqOn hb h.symm⟩

/-- The infinity condition only depends on `R` on a neighbourhood `(b, ∞)` of infinity. -/
theorem infinityConditionL_of_eqOn {M Q e ω b : ℝ} {R₁ R₂ : ℝ → ℂ} {B : ℂ}
    (h : EqOn R₁ R₂ (Ioi b)) (h₁ : InfinityConditionL M Q e ω R₁ B) :
    InfinityConditionL M Q e ω R₂ B := by
  have hE : ∀ᶠ r : ℝ in atTop,
      (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * R₁ r - B =
        (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * R₂ r - B := by
    filter_upwards [Ioi_mem_atTop b] with r hr
    rw [h hr]
  have hD : ∀ᶠ r : ℝ in atTop,
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * R₁ r) r =
        deriv (fun r : ℝ => (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * R₂ r) r := by
    filter_upwards [Ioi_mem_atTop b] with r hr
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    rw [h hs]
  exact ⟨h₁.1.congr' hE EventuallyEq.rfl, h₁.2.congr' hD EventuallyEq.rfl⟩

/-- The infinity condition only depends on `R` on a neighbourhood `(b, ∞)` of infinity. -/
theorem infinityConditionL_congr {M Q e ω b : ℝ} {R₁ R₂ : ℝ → ℂ} {B : ℂ}
    (h : EqOn R₁ R₂ (Ioi b)) :
    InfinityConditionL M Q e ω R₁ B ↔ InfinityConditionL M Q e ω R₂ B :=
  ⟨infinityConditionL_of_eqOn h, infinityConditionL_of_eqOn h.symm⟩

/-- A scalar multiple `cR` satisfies the horizon condition with leading coefficient `cB`. -/
theorem horizonConditionL_const_mul {M Q e ω : ℝ} {R : ℝ → ℂ} {B : ℂ} (c : ℂ)
    (h : HorizonConditionL M Q e ω R B) :
    HorizonConditionL M Q e ω (fun r => c * R r) (c * B) := by
  unfold HorizonConditionL at h ⊢
  split_ifs at h ⊢
  · exact h.const_mul_left c
  · refine ⟨(h.1.const_mul_left c).congr_left fun r => by ring, ?_⟩
    have hfun : deriv (fun r : ℝ => exp (I * radialPhase M Q e ω r) * (c * R r)) =
        fun r => c * deriv (fun r : ℝ => exp (I * radialPhase M Q e ω r) * R r) r := by
      funext r
      rw [← deriv_const_mul_field]
      congr 1
      funext s
      ring
    rw [hfun]
    exact h.2.const_mul_left c

/-- A scalar multiple `cR` satisfies the infinity condition with leading coefficient `cB`. -/
theorem infinityConditionL_const_mul {M Q e ω : ℝ} {R : ℝ → ℂ} {B : ℂ} (c : ℂ)
    (h : InfinityConditionL M Q e ω R B) :
    InfinityConditionL M Q e ω (fun r => c * R r) (c * B) := by
  refine ⟨(h.1.const_mul_left c).congr_left fun r => by ring, ?_⟩
  have hfun : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * (c * R r)) =
      fun r => c * deriv (fun r : ℝ => (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * R r) r := by
    funext r
    rw [← deriv_const_mul_field]
    congr 1
    funext s
    ring
  rw [hfun]
  exact h.2.const_mul_left c

/-- The difference of two functions differentiable on the exterior and satisfying the horizon
condition satisfies it with the difference of the leading coefficients. -/
theorem horizonConditionL_sub {M Q e ω : ℝ} {R₁ R₂ : ℝ → ℂ} {B₁ B₂ : ℂ}
    (hR₁ : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R₁ r)
    (hR₂ : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R₂ r)
    (h₁ : HorizonConditionL M Q e ω R₁ B₁) (h₂ : HorizonConditionL M Q e ω R₂ B₂) :
    HorizonConditionL M Q e ω (fun r => R₁ r - R₂ r) (B₁ - B₂) := by
  unfold HorizonConditionL at h₁ h₂ ⊢
  split_ifs at h₁ h₂ ⊢
  · exact h₁.sub h₂
  · refine ⟨(h₁.1.sub h₂.1).congr_left fun r => by ring,
      (h₁.2.sub h₂.2).congr' ?_ EventuallyEq.rfl⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hfun : (fun r : ℝ => exp (I * radialPhase M Q e ω r) * (R₁ r - R₂ r)) =
        fun r => exp (I * radialPhase M Q e ω r) * R₁ r -
          exp (I * radialPhase M Q e ω r) * R₂ r := by
      funext s
      ring
    have d₁ : DifferentiableAt ℝ (fun s => exp (I * radialPhase M Q e ω s) * R₁ s) r :=
      (differentiableAt_horizonFactor hr).mul (hR₁ r hr)
    have d₂ : DifferentiableAt ℝ (fun s => exp (I * radialPhase M Q e ω s) * R₂ s) r :=
      (differentiableAt_horizonFactor hr).mul (hR₂ r hr)
    rw [hfun, deriv_fun_sub d₁ d₂]

/-- The difference of two functions differentiable on the exterior and satisfying the infinity
condition satisfies it with the difference of the leading coefficients. -/
theorem infinityConditionL_sub {M Q e ω : ℝ} {R₁ R₂ : ℝ → ℂ} {B₁ B₂ : ℂ}
    (hR₁ : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R₁ r)
    (hR₂ : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R₂ r)
    (h₁ : InfinityConditionL M Q e ω R₁ B₁) (h₂ : InfinityConditionL M Q e ω R₂ B₂) :
    InfinityConditionL M Q e ω (fun r => R₁ r - R₂ r) (B₁ - B₂) := by
  refine ⟨(h₁.1.sub h₂.1).congr_left fun r => by ring,
    (h₁.2.sub h₂.2).congr' ?_ EventuallyEq.rfl⟩
  filter_upwards [Ioi_mem_atTop (outerHorizon M Q)] with r hr
  have hfun : (fun r : ℝ => (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * (R₁ r - R₂ r)) =
      fun r : ℝ => (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * R₁ r -
        (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * R₂ r := by
    funext s
    ring
  have d₁ : DifferentiableAt ℝ
      (fun s : ℝ => (s : ℂ) * exp (-(I * radialPhase M Q e ω s)) * R₁ s) r :=
    (differentiableAt_infinityFactor hr).mul (hR₁ r hr)
  have d₂ : DifferentiableAt ℝ
      (fun s : ℝ => (s : ℂ) * exp (-(I * radialPhase M Q e ω s)) * R₂ s) r :=
    (differentiableAt_infinityFactor hr).mul (hR₂ r hr)
  rw [hfun, deriv_fun_sub d₁ d₂]

/-! ### The Wronskian of `R_H` and `R_I` -/

/-- **The homogeneous Wronskian is nonzero** (p. 7.). Let `u` solve the radial equation with the horizon condition (1.4) with
leading coefficient `1`, and `w` with the infinity condition (1.5) with leading coefficient `1`,
at a non-synchronized horizon and `ω ≠ 0`. Then `Δ(u w' − u' w) ≠ 0` on the exterior.

If it vanished, then (it is constant) at a point `r₀` with `u(r₀) ≠ 0` the solution
`w(r₀)u − u(r₀)w` would have zero Cauchy data, hence vanish (interior uniqueness), so `w` would
be a multiple of `u` and satisfy both conditions; Theorem 1.1 would give `w = 0`, contradicting
`r e^{−iΘ}w → 1`. -/
theorem wronskian_ne_zero {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hL : 0 ≤ L)
    (hω : ω ≠ 0) (hK : radialK e ω (outerHorizon M Q) ≠ 0) {u w : ℝ → ℂ}
    (hu : IsRadialSolutionL M Q e ω L u) (huH : HorizonConditionL M Q e ω u 1)
    (hw : IsRadialSolutionL M Q e ω L w) (hwI : InfinityConditionL M Q e ω w 1)
    {c : ℝ} (hc : c ∈ Ioi (outerHorizon M Q)) :
    (delta M Q c : ℂ) * (u c * deriv w c - deriv u c * w c) ≠ 0 := by
  set a := outerHorizon M Q with ha
  intro hW0
  have hWr : ∀ r ∈ Ioi a, (delta M Q r : ℂ) * (u r * deriv w r - deriv u r * w r) = 0 :=
    fun r hr => (wronskian_eq (p := delta M Q)
      (q := fun r => (radialK e ω r) ^ 2 / delta M Q r - L) hu hw hr hc).trans hW0
  -- a point `r₀ > a` with `u(r₀) ≠ 0`, from `e^{iΘ}u → 1`
  have huH' := huH
  unfold HorizonConditionL at huH'
  rw [ite_eq_right fun h => hK h.2] at huH'
  have hlin : Tendsto (fun r : ℝ => r - a) (𝓝[>] a) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' a 0 (by simp [ha])).mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ r in 𝓝[>] a, ‖exp (I * radialPhase M Q e ω r) * u r - 1‖ < 1 :=
    (tendsto_zero_iff_norm_tendsto_zero.1 (huH'.1.trans_tendsto hlin)).eventually
      (gt_mem_nhds zero_lt_one)
  obtain ⟨r₀, hr₀1, hr₀⟩ := (hev.and self_mem_nhdsWithin).exists
  have hu₀ : u r₀ ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, norm_neg, norm_one] at hr₀1
    exact lt_irrefl _ hr₀1
  -- `w(r₀) u − u(r₀) w` vanishes identically
  have hφ := solution_lincomb (p := delta M Q)
    (q := fun r => (radialK e ω r) ^ 2 / delta M Q r - L) (w r₀) (u r₀) hu hw
  have hΔ₀ : (delta M Q r₀ : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (InfinityUniqueness.delta_pos_of_lt hr₀).ne'
  have h1 : deriv (fun s => w r₀ * u s - u r₀ * w s) r₀ = 0 := by
    rw [deriv_fun_sub ((hu r₀ hr₀).1.const_mul _) ((hw r₀ hr₀).1.const_mul _),
      deriv_const_mul_field, deriv_const_mul_field]
    have h := hWr r₀ hr₀
    rw [mul_eq_zero, or_iff_right hΔ₀] at h
    linear_combination -h
  have hφ0 := ModeStability.ODE.eqOn_zero_of_linear_ode
    (InfinityUniqueness.continuous_delta M Q).continuousOn
    (fun r hr => InfinityUniqueness.delta_pos_of_lt hr) (continuousOn_radialCoeff M Q e ω L) hφ hr₀
    (by ring) h1
  -- so `w` is a multiple of `u` on the exterior and satisfies the horizon condition
  have hwu : EqOn (fun r => w r₀ / u r₀ * u r) w (Ioo a (a + 1)) := by
    intro r hr
    have h := hφ0 hr.1
    simp only [Pi.zero_apply] at h
    field_simp
    linear_combination h
  have hwH : HorizonConditionL M Q e ω w (w r₀ / u r₀ * 1) :=
    horizonConditionL_of_eqOn (lt_add_one a) hwu (horizonConditionL_const_mul _ huH)
  have hw0 := real_mode_exclusion_integralPhase M Q e ω L hM hQ hL hω w _ 1 hw hwH hwI
  -- contradiction with `r e^{−iΘ}w − 1 = O(r⁻¹)`
  have ht := hwI.1.trans_tendsto tendsto_inv_atTop_zero
  have hc1 : (fun r : ℝ => (r : ℂ) * exp (-(I * radialPhase M Q e ω r)) * w r - 1) =ᶠ[atTop]
      fun _ => (-1 : ℂ) := by
    filter_upwards [Ioi_mem_atTop a] with r hr
    rw [hw0 hr]
    simp
  have := tendsto_nhds_unique (ht.congr' hc1) tendsto_const_nhds
  norm_num at this

/-! ### Existence and uniqueness -/

/-- **The Green-formula solution of (6.1): existence.** In the strictly superradiant range (1.7)
(`0 < e`, `0 < ω < e/a`), for `S ∈ L²` on a compact `[ρ₁, ρ₂] ⊂ (a, ∞)` with `S = 0` off
`[ρ₁, ρ₂]`, there is a solution `R` of `(ΔR')' + (K²/Δ − L)R = S` on `(a, ∞)` (differentiable,
integrated form) satisfying the horizon condition (1.4) and the infinity condition (1.5) with
some leading coefficients `B_H`, `B_I`. It is the Green formula of `R_H` and `R_I`. The premise
`0 < e` of (1.7) is kept but not used (it follows from `0 < ω < e/a`). -/
theorem exists_source_solution {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (_he : 0 < e)
    (hω : 0 < ω) (hωa : ω < e / outerHorizon M Q) (hL : 0 ≤ L) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : outerHorizon M Q < ρ₁) (hρ : ρ₁ < ρ₂) {S : ℝ → ℂ}
    (hS0 : ∀ r, r ∉ Icc ρ₁ ρ₂ → S r = 0) (hS : MemLp S 2 (volume.restrict (Icc ρ₁ ρ₂))) :
    ∃ (R : ℝ → ℂ) (BH BI : ℂ),
      ((∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r) ∧
        ∀ r₁ ∈ Ioi (outerHorizon M Q), ∀ r₂ ∈ Ioi (outerHorizon M Q),
          IntervalIntegrable S volume r₁ r₂ ∧
            (delta M Q r₂ : ℂ) * deriv R r₂ - (delta M Q r₁ : ℂ) * deriv R r₁ =
              ∫ r in r₁..r₂, (S r - (((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r)) ∧
        HorizonConditionL M Q e ω R BH ∧ InfinityConditionL M Q e ω R BI := by
  set a := outerHorizon M Q with ha
  have ha0 : 0 < a := InfinityUniqueness.outerHorizon_pos hM
  have hK : radialK e ω a ≠ 0 := by
    have : ω * a < e := (lt_div_iff₀ ha0).1 hωa
    have h : radialK e ω a = a * (ω * a - e) := by
      unfold radialK
      ring
    rw [h]
    exact mul_ne_zero ha0.ne' (by linarith)
  have hΘ : ∀ r ∈ Ioi a, HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
    fun r hr => hasDerivAt_integral_radialK_div_delta hr
  -- the source is integrable
  have hSint : Integrable S volume :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero (hS.integrable one_le_two) hS0
  have hSi : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a, IntervalIntegrable S volume x y :=
    fun _ _ _ _ => hSint.intervalIntegrable
  -- the normalized solutions `R_H`, `R_I` and their Wronskian
  obtain ⟨u, hu, huH1, huH2⟩ := exists_horizon_solution (L := L) hM hQ hK hΘ
  obtain ⟨w, hw, hwI1, hwI2⟩ := exists_infinity_solution (L := L) hM hQ hω.ne' hΘ
  have huH : HorizonConditionL M Q e ω u 1 := by
    unfold HorizonConditionL
    rw [ite_eq_right fun h => hK h.2]
    exact ⟨huH1, huH2⟩
  have hwI : InfinityConditionL M Q e ω w 1 := ⟨hwI1, hwI2⟩
  have hρ₁' : ρ₁ ∈ Ioi a := hρ₁
  have hρ₂' : ρ₂ ∈ Ioi a := lt_trans hρ₁ hρ
  have hW := wronskian_ne_zero hM hQ hL hω.ne' hK hu huH hw hwI hρ₁'
  set W := (delta M Q ρ₁ : ℂ) * (u ρ₁ * deriv w ρ₁ - deriv u ρ₁ * w ρ₁) with hWdef
  -- the Green formula
  set R : ℝ → ℂ := fun r =>
    (w r * (∫ t in ρ₁..r, u t * S t) + u r * ∫ t in r..ρ₂, w t * S t) / W with hRdef
  obtain ⟨hRd, hRint⟩ := green_solution (p := delta M Q)
    (q := fun r => (radialK e ω r) ^ 2 / delta M Q r - L)
    (InfinityUniqueness.continuous_delta M Q).continuousOn
    (fun r hr => (InfinityUniqueness.delta_pos_of_lt hr).ne') (continuousOn_radialCoeff M Q e ω L)
    hu hw hρ₁' hW hρ₁' hρ₂' hSi (R := R) (fun r => rfl)
  have hcu := gf_continuousOn_sol hu
  have hcw := gf_continuousOn_sol hw
  refine ⟨R, (∫ t in ρ₁..ρ₂, w t * S t) / W * 1, (∫ t in ρ₁..ρ₂, u t * S t) / W * 1,
    ⟨hRd, fun r₁ hr₁ r₂ hr₂ => ⟨hSi r₁ hr₁ r₂ hr₂, hRint r₁ hr₁ r₂ hr₂⟩⟩, ?_, ?_⟩
  · refine horizonConditionL_of_eqOn hρ₁ (fun r hr => ?_) (horizonConditionL_const_mul _ huH)
    exact (green_eq_left hS0 hr.2.le (gf_intervalIntegrable_mul hcw hSi hr.1 hρ₁')
      (gf_intervalIntegrable_mul hcw hSi hρ₁' hρ₂')).symm
  · refine infinityConditionL_of_eqOn (b := ρ₂) (fun r hr => ?_)
      (infinityConditionL_const_mul _ hwI)
    exact (green_eq_right hS0 (le_of_lt hr) (gf_intervalIntegrable_mul hcu hSi hρ₁' hρ₂')
      (gf_intervalIntegrable_mul hcu hSi hρ₂' (lt_trans hρ₂' hr))).symm

/-- **The Green-formula solution of (6.1): uniqueness.** For `M > 0`, `|Q| ≤ M`, `L ≥ 0` and
real `ω ≠ 0`, two solutions of `(ΔR')' + (K²/Δ − L)R = S` on `(a, ∞)` (differentiable,
integrated form) satisfying the horizon condition (1.4) and the infinity condition (1.5) with
some leading coefficients agree on `(a, ∞)`: their difference is a mode with leading
coefficients `B_H − B_H'`, `B_I − B_I'`, which vanishes by Theorem 1.1. -/
theorem source_solution_unique {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hL : 0 ≤ L)
    (hω : ω ≠ 0) {S R₁ R₂ : ℝ → ℂ} {BH₁ BI₁ BH₂ BI₂ : ℂ}
    (h₁ : (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R₁ r) ∧
      ∀ r₁ ∈ Ioi (outerHorizon M Q), ∀ r₂ ∈ Ioi (outerHorizon M Q),
        IntervalIntegrable S volume r₁ r₂ ∧
          (delta M Q r₂ : ℂ) * deriv R₁ r₂ - (delta M Q r₁ : ℂ) * deriv R₁ r₁ =
            ∫ r in r₁..r₂, (S r - (((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R₁ r))
    (hH₁ : HorizonConditionL M Q e ω R₁ BH₁) (hI₁ : InfinityConditionL M Q e ω R₁ BI₁)
    (h₂ : (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R₂ r) ∧
      ∀ r₁ ∈ Ioi (outerHorizon M Q), ∀ r₂ ∈ Ioi (outerHorizon M Q),
        IntervalIntegrable S volume r₁ r₂ ∧
          (delta M Q r₂ : ℂ) * deriv R₂ r₂ - (delta M Q r₁ : ℂ) * deriv R₂ r₁ =
            ∫ r in r₁..r₂, (S r - (((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R₂ r))
    (hH₂ : HorizonConditionL M Q e ω R₂ BH₂) (hI₂ : InfinityConditionL M Q e ω R₂ BI₂) :
    EqOn R₁ R₂ (Ioi (outerHorizon M Q)) := by
  have hint := integrated_sub (p := delta M Q)
    (q := fun r => (radialK e ω r) ^ 2 / delta M Q r - L)
    (continuousOn_radialCoeff M Q e ω L) h₁.1 h₂.1 (fun x hx y hy => (h₁.2 x hx y hy).1)
    (fun r₁ hr₁ r₂ hr₂ => (h₁.2 r₁ hr₁ r₂ hr₂).2) (fun r₁ hr₁ r₂ hr₂ => (h₂.2 r₁ hr₁ r₂ hr₂).2)
  have hD : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ (fun s => R₁ s - R₂ s) r :=
    fun r hr => (h₁.1 r hr).sub (h₂.1 r hr)
  have hsol := hasDerivAt_of_integrated (continuousOn_radialCoeff M Q e ω L) hD hint
  have h0 := real_mode_exclusion_integralPhase M Q e ω L hM hQ hL hω (fun s => R₁ s - R₂ s)
    (BH₁ - BH₂) (BI₁ - BI₂) hsol (horizonConditionL_sub h₁.1 h₂.1 hH₁ hH₂)
    (infinityConditionL_sub h₁.1 h₂.1 hI₁ hI₂)
  intro r hr
  exact sub_eq_zero.1 (h0 hr)

/-- **The Green-formula solution of (6.1)** (p. 7.), in the strictly superradiant range
(1.7), for a source in `L²` supported in a compact `[ρ₁, ρ₂] ⊂ (a, ∞)`: there is exactly one
function on the exterior `(a, ∞)` that is the restriction of a solution `R` of
`(ΔR')' + (K²/Δ − L)R = S` (differentiable, integrated form) satisfying the horizon condition
(1.4) and the infinity condition (1.5) with some leading coefficients `B_H`, `B_I`. -/
theorem existsUnique_source_solution {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (he : 0 < e)
    (hω : 0 < ω) (hωa : ω < e / outerHorizon M Q) (hL : 0 ≤ L) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : outerHorizon M Q < ρ₁) (hρ : ρ₁ < ρ₂) {S : ℝ → ℂ}
    (hS0 : ∀ r, r ∉ Icc ρ₁ ρ₂ → S r = 0) (hS : MemLp S 2 (volume.restrict (Icc ρ₁ ρ₂))) :
    ∃! f : Ioi (outerHorizon M Q) → ℂ, ∃ (R : ℝ → ℂ) (BH BI : ℂ),
      (∀ r : Ioi (outerHorizon M Q), R r = f r) ∧
        ((∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r) ∧
          ∀ r₁ ∈ Ioi (outerHorizon M Q), ∀ r₂ ∈ Ioi (outerHorizon M Q),
            IntervalIntegrable S volume r₁ r₂ ∧
              (delta M Q r₂ : ℂ) * deriv R r₂ - (delta M Q r₁ : ℂ) * deriv R r₁ =
                ∫ r in r₁..r₂, (S r - (((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r)) ∧
          HorizonConditionL M Q e ω R BH ∧ InfinityConditionL M Q e ω R BI := by
  obtain ⟨R, BH, BI, hR, hH, hI⟩ := exists_source_solution hM hQ he hω hωa hL hρ₁ hρ hS0 hS
  refine ⟨fun r => R r, ⟨R, BH, BI, fun _ => rfl, hR, hH, hI⟩, ?_⟩
  rintro f ⟨R', BH', BI', hf, hR', hH', hI'⟩
  funext r
  rw [← hf r]
  exact source_solution_unique hM hQ hL hω.ne' hR' hH' hI' hR hH hI r.2

end ModeStability.AllAngular

end
