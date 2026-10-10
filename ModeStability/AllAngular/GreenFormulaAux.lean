module

public import Mathlib

/-!
# Variation of parameters for `(p R')' + q R = S` on a half-line

Auxiliary material for `ModeStability.AllAngular.GreenFormula`, which constructs the solution of
the inhomogeneous radial problem (6.1) of the all-angular research notes in preparation, p. 7.
The paper does not
write the formula out; this file proves the standard variation of parameters.

Setting: `p, q` real and continuous on `(a, ∞)`, `p ≠ 0` there, and `u, w` solutions of the
homogeneous equation `(p R')' + q R = 0` on `(a, ∞)` in the form
`HasDerivAt (p · u') (−q u)`. For a source `S` integrable on every compact interval in `(a, ∞)`:

* `wronskian_hasDerivAt_zero`, `wronskian_eq`: the Wronskian `p (u w' − u' w)` is constant;
* `green_solution`: if its value `W` is nonzero, then
  `R(r) = (w(r) ∫_{ρ₁}^r u S + u(r) ∫_r^{ρ₂} w S) / W`
  is differentiable on `(a, ∞)` and solves `(p R')' + q R = S` in integrated form,
  `p(r₂)R'(r₂) − p(r₁)R'(r₁) = ∫_{r₁}^{r₂} (S − q R)`;
* `green_eq_left`, `green_eq_right`: if `S = 0` off `[ρ₁, ρ₂]`, then `R = c_H u` on `(a, ρ₁]`
  and `R = c_I w` on `[ρ₂, ∞)`, with `c_H = W⁻¹ ∫_{ρ₁}^{ρ₂} w S`, `c_I = W⁻¹ ∫_{ρ₁}^{ρ₂} u S`;
* `hasDerivAt_of_integrated`, `integrated_sub`: a differentiable solution of the integrated
  homogeneous equation satisfies `HasDerivAt (p · R') (−q R)`, and the difference of two
  solutions of the integrated source equation solves the integrated homogeneous equation;
* `solution_lincomb`: linear combinations of homogeneous solutions are solutions;
* `gf_continuousOn_sol`, `gf_intervalIntegrable_mul`: small public helpers (continuity of a
  solution; integrability of a continuous function times the source).

Since `S` is only integrable, `p R'` is not differentiable. The key step,
`gf_hasDerivAt_sub_mul_integral`, differentiates `x ↦ f₁(x) ∫_{c₁}^x φ₁ g − f₂(x) ∫_{c₂}^x φ₂ g`
at every point where the kernel `f₁(x)φ₁(t) − f₂(x)φ₂(t)` is `O(|x − r|)` for `t` between `r` and
`x`: the remainder `∫_r^x (…) g` is then `o(x − r)`. This holds when `f₁ φ₁ = f₂ φ₂` and `f₁, f₂`
are locally Lipschitz. It gives the derivative of `R` and, applied to `p w' · ∫ u S − ∫ p w' u S`
(whose kernel is `(p w'(x) − p w'(t)) u(t)`), the integrated equation by the fundamental theorem
of calculus for an everywhere differentiable function with continuous derivative.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

/-! ### Differentiation of kernel integrals -/

/-- If `‖k(x, t)‖ ≤ C|x − r|` for `t` between `r` and `x` near `r`, and `g` is integrable near
`r`, then `∫_r^x k(x, t) g(t) dt = o(x − r)`. -/
private theorem gf_isLittleO_kernel {k : ℝ → ℝ → ℂ} {g : ℝ → ℂ} {r δ C : ℝ} (hδ : 0 < δ)
    (hC : 0 ≤ C)
    (hg : IntervalIntegrable g volume (r - δ) (r + δ))
    (hk : ∀ᶠ x in 𝓝 r, ∀ t ∈ uIcc r x, ‖k x t‖ ≤ C * |x - r|) :
    (fun x => ∫ t in r..x, k x t * g t) =o[𝓝 r] (fun x => x - r) := by
  have hmem : uIcc (r - δ) (r + δ) ∈ 𝓝 r := by
    rw [uIcc_of_le (by linarith)]
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hr : r ∈ uIcc (r - δ) (r + δ) := mem_of_mem_nhds hmem
  have hcont : ContinuousAt (fun x => ∫ t in r..x, ‖g t‖) r :=
    (intervalIntegral.continuousOn_primitive_interval' hg.norm hr).continuousAt hmem
  have hm : Tendsto (fun x => |∫ t in r..x, ‖g t‖|) (𝓝 r) (𝓝 0) := by
    simpa using hcont.tendsto.abs
  have hbound : ∀ᶠ x in 𝓝 r,
      ‖∫ t in r..x, k x t * g t‖ ≤ C * ‖(x - r) * |∫ t in r..x, ‖g t‖|‖ := by
    filter_upwards [hk, hmem] with x hx hxm
    have hgi : IntervalIntegrable (fun t => C * |x - r| * ‖g t‖) volume r x :=
      (hg.norm.mono_set (uIcc_subset_uIcc hr hxm)).const_mul _
    have h1 := intervalIntegral.norm_integral_le_abs_of_norm_le (f := fun t => k x t * g t)
      (ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hx t (uIoc_subset_uIcc ht)) (norm_nonneg _)) hgi
    rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by positivity)] at h1
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact h1.trans_eq (by ring)
  refine (IsBigO.of_bound C hbound).trans_isLittleO ?_
  have h2 : (fun x => |∫ t in r..x, ‖g t‖|) =o[𝓝 r] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 hm
  simpa using (isBigO_refl (fun x => x - r) (𝓝 r)).mul_isLittleO h2

/-- Differentiation of `x ↦ f₁(x) ∫_{c₁}^x φ₁ g − f₂(x) ∫_{c₂}^x φ₂ g` at `r`, when the kernel
`f₁(x)φ₁(t) − f₂(x)φ₂(t)` is `O(|x − r|)` for `t` between `r` and `x`. -/
private theorem gf_hasDerivAt_sub_mul_integral {f₁ f₂ φ₁ φ₂ g : ℝ → ℂ} {f₁' f₂' : ℂ}
    {c₁ c₂ r δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hf₁ : HasDerivAt f₁ f₁' r)
    (hf₂ : HasDerivAt f₂ f₂' r)
    (hi₁ : ∀ᶠ x in 𝓝 r, IntervalIntegrable (fun t => φ₁ t * g t) volume c₁ x)
    (hi₂ : ∀ᶠ x in 𝓝 r, IntervalIntegrable (fun t => φ₂ t * g t) volume c₂ x)
    (hg : IntervalIntegrable g volume (r - δ) (r + δ))
    (hk : ∀ᶠ x in 𝓝 r, ∀ t ∈ uIcc r x, ‖f₁ x * φ₁ t - f₂ x * φ₂ t‖ ≤ C * |x - r|) :
    HasDerivAt (fun x => f₁ x * (∫ t in c₁..x, φ₁ t * g t) - f₂ x * ∫ t in c₂..x, φ₂ t * g t)
      (f₁' * (∫ t in c₁..r, φ₁ t * g t) - f₂' * ∫ t in c₂..r, φ₂ t * g t) r := by
  rw [hasDerivAt_iff_isLittleO]
  have hrem := gf_isLittleO_kernel (k := fun x t => f₁ x * φ₁ t - f₂ x * φ₂ t) hδ hC hg hk
  have h₁ := (hasDerivAt_iff_isLittleO.1 hf₁).const_mul_left (∫ t in c₁..r, φ₁ t * g t)
  have h₂ := (hasDerivAt_iff_isLittleO.1 hf₂).const_mul_left (∫ t in c₂..r, φ₂ t * g t)
  refine ((h₁.sub h₂).add hrem).congr' ?_ EventuallyEq.rfl
  have hr₁ := hi₁.self_of_nhds
  have hr₂ := hi₂.self_of_nhds
  filter_upwards [hi₁, hi₂] with x hx₁ hx₂
  have hrx₁ : IntervalIntegrable (fun t => φ₁ t * g t) volume r x := hr₁.symm.trans hx₁
  have hrx₂ : IntervalIntegrable (fun t => φ₂ t * g t) volume r x := hr₂.symm.trans hx₂
  have e₁ := intervalIntegral.integral_add_adjacent_intervals hr₁ hrx₁
  have e₂ := intervalIntegral.integral_add_adjacent_intervals hr₂ hrx₂
  have e₃ : ∫ t in r..x, (f₁ x * φ₁ t - f₂ x * φ₂ t) * g t =
      f₁ x * (∫ t in r..x, φ₁ t * g t) - f₂ x * ∫ t in r..x, φ₂ t * g t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hrx₁.const_mul _) (hrx₂.const_mul _)]
    congr 1
    funext t
    ring
  simp only [← e₁, ← e₂, e₃, Complex.real_smul]
  ring

/-- A `C¹` function is Lipschitz on a compact interval inside its domain. -/
private theorem gf_lipschitz_Icc {f f' : ℝ → ℂ} {s : Set ℝ} {α β : ℝ} (hs : Icc α β ⊆ s)
    (hf : ∀ t ∈ s, HasDerivAt f (f' t) t) (hf' : ContinuousOn f' s) :
    ∃ K, 0 ≤ K ∧ ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, ‖f x - f y‖ ≤ K * |x - y| := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf'.mono hs)
  refine ⟨max C 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have := (convex_Icc α β).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hf t (hs ht)).hasDerivWithinAt) (fun t ht => (hC t ht).trans (le_max_left C 0))
    hy hx
  rwa [Real.norm_eq_abs] at this

/-- The kernel bound: if `f₁ φ₁ = f₂ φ₂` at `t`, then
`‖f₁(x)φ₁(t) − f₂(x)φ₂(t)‖ ≤ (K₁B₁ + K₂B₂)|x − r|` for `t` between `r` and `x`. -/
private theorem gf_kernel_le {f₁ f₂ φ₁ φ₂ : ℝ → ℂ} {K₁ K₂ B₁ B₂ x r t : ℝ} (hK₁ : 0 ≤ K₁)
    (hK₂ : 0 ≤ K₂) (hf₁ : ‖f₁ x - f₁ t‖ ≤ K₁ * |x - t|) (hf₂ : ‖f₂ x - f₂ t‖ ≤ K₂ * |x - t|)
    (hφ₁ : ‖φ₁ t‖ ≤ B₁) (hφ₂ : ‖φ₂ t‖ ≤ B₂) (hdiag : f₁ t * φ₁ t = f₂ t * φ₂ t)
    (ht : t ∈ uIcc r x) :
    ‖f₁ x * φ₁ t - f₂ x * φ₂ t‖ ≤ (K₁ * B₁ + K₂ * B₂) * |x - r| := by
  have hxt : |x - t| ≤ |x - r| := abs_sub_right_of_mem_uIcc ht
  have e : f₁ x * φ₁ t - f₂ x * φ₂ t = (f₁ x - f₁ t) * φ₁ t - (f₂ x - f₂ t) * φ₂ t := by
    linear_combination hdiag
  have h₁ : ‖f₁ x - f₁ t‖ ≤ K₁ * |x - r| := hf₁.trans (mul_le_mul_of_nonneg_left hxt hK₁)
  have h₂ : ‖f₂ x - f₂ t‖ ≤ K₂ * |x - r| := hf₂.trans (mul_le_mul_of_nonneg_left hxt hK₂)
  calc ‖f₁ x * φ₁ t - f₂ x * φ₂ t‖
      ≤ ‖f₁ x - f₁ t‖ * ‖φ₁ t‖ + ‖f₂ x - f₂ t‖ * ‖φ₂ t‖ := by
        rw [e, ← norm_mul, ← norm_mul]
        exact norm_sub_le _ _
    _ ≤ (K₁ * |x - r|) * B₁ + (K₂ * |x - r|) * B₂ := by
        gcongr
    _ = (K₁ * B₁ + K₂ * B₂) * |x - r| := by ring

/-- A continuous function times a function integrable on compact subintervals of `(a, ∞)` is
interval integrable between points of `(a, ∞)`. -/
theorem gf_intervalIntegrable_mul {a x y : ℝ} {φ S : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi a))
    (hS : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a, IntervalIntegrable S volume x y) (hx : x ∈ Ioi a)
    (hy : y ∈ Ioi a) : IntervalIntegrable (fun t => φ t * S t) volume x y :=
  (hS x hx y hy).continuousOn_mul (hφ.mono (ordConnected_Ioi.uIcc_subset hx hy))

/-- Differentiation of `x ↦ f₁(x) ∫_{c₁}^x φ₁ S − f₂(x) ∫_{c₂}^x φ₂ S` on `(a, ∞)` for `C¹`
functions `f₁, f₂`, continuous `φ₁, φ₂` with `f₁ φ₁ = f₂ φ₂`, and `S` integrable on compact
subintervals. -/
private theorem gf_hasDerivAt_Ioi {a c₁ c₂ : ℝ} {f₁ f₂ f₁' f₂' φ₁ φ₂ S : ℝ → ℂ}
    (hf₁ : ∀ t ∈ Ioi a, HasDerivAt f₁ (f₁' t) t) (hf₁' : ContinuousOn f₁' (Ioi a))
    (hf₂ : ∀ t ∈ Ioi a, HasDerivAt f₂ (f₂' t) t) (hf₂' : ContinuousOn f₂' (Ioi a))
    (hφ₁ : ContinuousOn φ₁ (Ioi a)) (hφ₂ : ContinuousOn φ₂ (Ioi a))
    (hdiag : ∀ t ∈ Ioi a, f₁ t * φ₁ t = f₂ t * φ₂ t)
    (hS : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a, IntervalIntegrable S volume x y)
    (hc₁ : c₁ ∈ Ioi a) (hc₂ : c₂ ∈ Ioi a) {r : ℝ} (hr : r ∈ Ioi a) :
    HasDerivAt (fun x => f₁ x * (∫ t in c₁..x, φ₁ t * S t) - f₂ x * ∫ t in c₂..x, φ₂ t * S t)
      (f₁' r * (∫ t in c₁..r, φ₁ t * S t) - f₂' r * ∫ t in c₂..r, φ₂ t * S t) r := by
  have hr' : a < r := hr
  have hδ : 0 < (r - a) / 2 := by linarith
  have hsub : Icc (r - (r - a) / 2) (r + (r - a) / 2) ⊆ Ioi a := fun t ht => by
    have := ht.1
    simp only [mem_Ioi]
    linarith
  have hnhds : Icc (r - (r - a) / 2) (r + (r - a) / 2) ∈ 𝓝 r :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hrI : r ∈ Icc (r - (r - a) / 2) (r + (r - a) / 2) := ⟨by linarith, by linarith⟩
  obtain ⟨K₁, hK₁, hL₁⟩ := gf_lipschitz_Icc hsub hf₁ hf₁'
  obtain ⟨K₂, hK₂, hL₂⟩ := gf_lipschitz_Icc hsub hf₂ hf₂'
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφ₁.mono hsub)
  obtain ⟨B₂, hB₂⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφ₂.mono hsub)
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ r hrI)
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ r hrI)
  refine gf_hasDerivAt_sub_mul_integral hδ (C := K₁ * B₁ + K₂ * B₂) (by positivity)
    (hf₁ r hr) (hf₂ r hr) ?_ ?_ (hS _ (hsub ⟨le_rfl, by linarith⟩) _ (hsub ⟨by linarith, le_rfl⟩))
    ?_
  · filter_upwards [Ioi_mem_nhds hr] with x hx using gf_intervalIntegrable_mul hφ₁ hS hc₁ hx
  · filter_upwards [Ioi_mem_nhds hr] with x hx using gf_intervalIntegrable_mul hφ₂ hS hc₂ hx
  · filter_upwards [hnhds] with x hx t ht
    have htI : t ∈ Icc (r - (r - a) / 2) (r + (r - a) / 2) := uIcc_subset_Icc hrI hx ht
    exact gf_kernel_le hK₁ hK₂ (hL₁ x hx t htI) (hL₂ x hx t htI) (hB₁ t htI) (hB₂ t htI)
      (hdiag t (hsub htI)) ht

/-! ### Homogeneous solutions and the Wronskian -/

/-- A solution of the homogeneous equation is continuous on `(a, ∞)`. -/
theorem gf_continuousOn_sol {a : ℝ} {p q : ℝ → ℝ} {u : ℝ → ℂ}
    (hu : ∀ r ∈ Ioi a, DifferentiableAt ℝ u r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv u s) (-(q r : ℂ) * u r) r) :
    ContinuousOn u (Ioi a) := fun r hr => (hu r hr).1.continuousAt.continuousWithinAt

/-- The flux `p u'` of a solution is continuous on `(a, ∞)`. -/
private theorem gf_continuousOn_flux {a : ℝ} {p q : ℝ → ℝ} {u : ℝ → ℂ}
    (hu : ∀ r ∈ Ioi a, DifferentiableAt ℝ u r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv u s) (-(q r : ℂ) * u r) r) :
    ContinuousOn (fun s => (p s : ℂ) * deriv u s) (Ioi a) := fun r hr =>
  (hu r hr).2.continuousAt.continuousWithinAt

/-- The derivative of a solution is continuous on `(a, ∞)` (`u' = (p u')/p`). -/
private theorem gf_continuousOn_deriv {a : ℝ} {p q : ℝ → ℝ} {u : ℝ → ℂ}
    (hp : ContinuousOn p (Ioi a)) (hp0 : ∀ r ∈ Ioi a, p r ≠ 0)
    (hu : ∀ r ∈ Ioi a, DifferentiableAt ℝ u r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv u s) (-(q r : ℂ) * u r) r) :
    ContinuousOn (deriv u) (Ioi a) := by
  have hpc : ContinuousOn (fun s => (p s : ℂ)) (Ioi a) := continuous_ofReal.comp_continuousOn hp
  have h : ContinuousOn (fun s => ((p s : ℂ))⁻¹ * ((p s : ℂ) * deriv u s)) (Ioi a) :=
    (hpc.inv₀ fun s hs => ofReal_ne_zero.2 (hp0 s hs)).mul (gf_continuousOn_flux hu)
  refine h.congr fun s hs => ?_
  have : (p s : ℂ) ≠ 0 := ofReal_ne_zero.2 (hp0 s hs)
  simp only
  rw [← mul_assoc, inv_mul_cancel₀ this, one_mul]

/-- The Wronskian `p (u w' − u' w)` of two solutions has derivative `0`. -/
theorem wronskian_hasDerivAt_zero {a : ℝ} {p q : ℝ → ℝ} {u w : ℝ → ℂ}
    (hu : ∀ r ∈ Ioi a, DifferentiableAt ℝ u r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv u s) (-(q r : ℂ) * u r) r)
    (hw : ∀ r ∈ Ioi a, DifferentiableAt ℝ w r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv w s) (-(q r : ℂ) * w r) r)
    {r : ℝ} (hr : r ∈ Ioi a) :
    HasDerivAt (fun s => (p s : ℂ) * (u s * deriv w s - deriv u s * w s)) 0 r := by
  have h := ((hu r hr).1.hasDerivAt.mul (hw r hr).2).sub
    ((hu r hr).2.mul (hw r hr).1.hasDerivAt)
  have e : (fun s => (p s : ℂ) * (u s * deriv w s - deriv u s * w s)) =
      fun s => u s * ((p s : ℂ) * deriv w s) - (p s : ℂ) * deriv u s * w s := by
    funext s
    ring
  rw [e]
  convert h using 1
  ring

/-- The Wronskian `p (u w' − u' w)` of two solutions is constant on `(a, ∞)`. -/
theorem wronskian_eq {a : ℝ} {p q : ℝ → ℝ} {u w : ℝ → ℂ}
    (hu : ∀ r ∈ Ioi a, DifferentiableAt ℝ u r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv u s) (-(q r : ℂ) * u r) r)
    (hw : ∀ r ∈ Ioi a, DifferentiableAt ℝ w r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv w s) (-(q r : ℂ) * w r) r)
    {r₁ r₂ : ℝ} (hr₁ : r₁ ∈ Ioi a) (hr₂ : r₂ ∈ Ioi a) :
    (p r₁ : ℂ) * (u r₁ * deriv w r₁ - deriv u r₁ * w r₁) =
      (p r₂ : ℂ) * (u r₂ * deriv w r₂ - deriv u r₂ * w r₂) :=
  isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun _ hr => (wronskian_hasDerivAt_zero hu hw hr).differentiableAt.differentiableWithinAt)
    (fun _ hr => (wronskian_hasDerivAt_zero hu hw hr).deriv) hr₁ hr₂

/-- A linear combination `α u − β w` of solutions of the homogeneous equation is a solution. -/
theorem solution_lincomb {a : ℝ} {p q : ℝ → ℝ} {u w : ℝ → ℂ} (α β : ℂ)
    (hu : ∀ r ∈ Ioi a, DifferentiableAt ℝ u r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv u s) (-(q r : ℂ) * u r) r)
    (hw : ∀ r ∈ Ioi a, DifferentiableAt ℝ w r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv w s) (-(q r : ℂ) * w r) r) :
    ∀ r ∈ Ioi a, DifferentiableAt ℝ (fun s => α * u s - β * w s) r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv (fun s => α * u s - β * w s) s)
        (-(q r : ℂ) * (α * u r - β * w r)) r := by
  intro r hr
  refine ⟨((hu r hr).1.const_mul α).sub ((hw r hr).1.const_mul β), ?_⟩
  have h := ((hu r hr).2.const_mul α).sub ((hw r hr).2.const_mul β)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards [Ioi_mem_nhds hr] with s hs
  change (p s : ℂ) * deriv (fun s => α * u s - β * w s) s =
    α * ((p s : ℂ) * deriv u s) - β * ((p s : ℂ) * deriv w s)
  rw [deriv_fun_sub ((hu s hs).1.const_mul α) ((hw s hs).1.const_mul β),
    deriv_const_mul_field, deriv_const_mul_field]
  ring

/-! ### The Green formula -/

/-- **Variation of parameters.** Let `u, w` solve `(p R')' + q R = 0` on `(a, ∞)` with nonzero
Wronskian `W = p(c)(u(c)w'(c) − u'(c)w(c))`, `c > a`, and let `S` be integrable on compact
subintervals of `(a, ∞)`. Then `R(r) = (w(r) ∫_{ρ₁}^r u S + u(r) ∫_r^{ρ₂} w S) / W` is
differentiable on `(a, ∞)` and solves `(p R')' + q R = S` in integrated form:
`p(r₂)R'(r₂) − p(r₁)R'(r₁) = ∫_{r₁}^{r₂} (S − q R)` for `r₁, r₂ > a`. -/
theorem green_solution {a c ρ₁ ρ₂ : ℝ} {p q : ℝ → ℝ} {u w S R : ℝ → ℂ}
    (hp : ContinuousOn p (Ioi a)) (hp0 : ∀ r ∈ Ioi a, p r ≠ 0) (hq : ContinuousOn q (Ioi a))
    (hu : ∀ r ∈ Ioi a, DifferentiableAt ℝ u r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv u s) (-(q r : ℂ) * u r) r)
    (hw : ∀ r ∈ Ioi a, DifferentiableAt ℝ w r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv w s) (-(q r : ℂ) * w r) r)
    (hc : c ∈ Ioi a) (hW : (p c : ℂ) * (u c * deriv w c - deriv u c * w c) ≠ 0)
    (hρ₁ : ρ₁ ∈ Ioi a) (hρ₂ : ρ₂ ∈ Ioi a)
    (hS : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a, IntervalIntegrable S volume x y)
    (hR : ∀ r, R r = (w r * (∫ t in ρ₁..r, u t * S t) + u r * ∫ t in r..ρ₂, w t * S t) /
      ((p c : ℂ) * (u c * deriv w c - deriv u c * w c))) :
    (∀ r ∈ Ioi a, DifferentiableAt ℝ R r) ∧
      ∀ r₁ ∈ Ioi a, ∀ r₂ ∈ Ioi a, (p r₂ : ℂ) * deriv R r₂ - (p r₁ : ℂ) * deriv R r₁ =
        ∫ r in r₁..r₂, (S r - (q r : ℂ) * R r) := by
  set W := (p c : ℂ) * (u c * deriv w c - deriv u c * w c) with hWdef
  have hWr : ∀ r ∈ Ioi a, (p r : ℂ) * (u r * deriv w r - deriv u r * w r) = W :=
    fun r hr => wronskian_eq hu hw hr hc
  have hcu := gf_continuousOn_sol hu
  have hcw := gf_continuousOn_sol hw
  have hcdu := gf_continuousOn_deriv hp hp0 hu
  have hcdw := gf_continuousOn_deriv hp hp0 hw
  have hcPu := gf_continuousOn_flux hu
  have hcPw := gf_continuousOn_flux hw
  have hcq : ContinuousOn (fun s => (q s : ℂ)) (Ioi a) := continuous_ofReal.comp_continuousOn hq
  have hcPwu : ContinuousOn (fun s => (p s : ℂ) * deriv w s * u s) (Ioi a) := hcPw.mul hcu
  have hcPuw : ContinuousOn (fun s => (p s : ℂ) * deriv u s * w s) (Ioi a) := hcPu.mul hcw
  have hR' : ∀ r, R r = (w r * (∫ t in ρ₁..r, u t * S t) - u r * ∫ t in ρ₂..r, w t * S t) / W := by
    intro r
    rw [hR r, intervalIntegral.integral_symm r ρ₂]
    ring
  -- the derivative of `R`
  have hN : ∀ r ∈ Ioi a, HasDerivAt
      (fun x => w x * (∫ t in ρ₁..x, u t * S t) - u x * ∫ t in ρ₂..x, w t * S t)
      (deriv w r * (∫ t in ρ₁..r, u t * S t) - deriv u r * ∫ t in ρ₂..r, w t * S t) r :=
    fun r hr => gf_hasDerivAt_Ioi (fun t ht => (hw t ht).1.hasDerivAt) hcdw
      (fun t ht => (hu t ht).1.hasDerivAt) hcdu hcu hcw (fun t _ => mul_comm _ _) hS hρ₁ hρ₂ hr
  have hRfun : R = fun x =>
      (w x * (∫ t in ρ₁..x, u t * S t) - u x * ∫ t in ρ₂..x, w t * S t) / W := funext hR'
  have hRd : ∀ r ∈ Ioi a, HasDerivAt R
      ((deriv w r * (∫ t in ρ₁..r, u t * S t) - deriv u r * ∫ t in ρ₂..r, w t * S t) / W) r := by
    intro r hr
    rw [hRfun]
    exact (hN r hr).div_const W
  refine ⟨fun r hr => (hRd r hr).differentiableAt, ?_⟩
  have hpR : ∀ r ∈ Ioi a, W * ((p r : ℂ) * deriv R r) =
      (p r : ℂ) * deriv w r * (∫ t in ρ₁..r, u t * S t) -
        (p r : ℂ) * deriv u r * ∫ t in ρ₂..r, w t * S t := by
    intro r hr
    rw [(hRd r hr).deriv]
    field_simp
  have hcR : ContinuousOn R (Ioi a) := fun r hr => (hRd r hr).continuousAt.continuousWithinAt
  -- the two primitives with continuous derivative
  have hΦw : ∀ r ∈ Ioi a, HasDerivAt
      (fun x => (p x : ℂ) * deriv w x * (∫ t in ρ₁..x, u t * S t) -
        1 * ∫ t in ρ₁..x, (p t : ℂ) * deriv w t * u t * S t)
      (-(q r : ℂ) * w r * (∫ t in ρ₁..r, u t * S t) -
        0 * ∫ t in ρ₁..r, (p t : ℂ) * deriv w t * u t * S t) r :=
    fun r hr => gf_hasDerivAt_Ioi (f₁ := fun s => (p s : ℂ) * deriv w s)
      (f₁' := fun s => -(q s : ℂ) * w s) (f₂ := fun _ => 1) (f₂' := fun _ => 0)
      (φ₁ := u) (φ₂ := fun s => (p s : ℂ) * deriv w s * u s)
      (fun t ht => (hw t ht).2) (hcq.neg.mul hcw) (fun t _ => hasDerivAt_const t (1 : ℂ))
      continuousOn_const hcu hcPwu (fun t _ => (one_mul _).symm) hS hρ₁ hρ₁ hr
  have hΦu : ∀ r ∈ Ioi a, HasDerivAt
      (fun x => (p x : ℂ) * deriv u x * (∫ t in ρ₂..x, w t * S t) -
        1 * ∫ t in ρ₂..x, (p t : ℂ) * deriv u t * w t * S t)
      (-(q r : ℂ) * u r * (∫ t in ρ₂..r, w t * S t) -
        0 * ∫ t in ρ₂..r, (p t : ℂ) * deriv u t * w t * S t) r :=
    fun r hr => gf_hasDerivAt_Ioi (f₁ := fun s => (p s : ℂ) * deriv u s)
      (f₁' := fun s => -(q s : ℂ) * u s) (f₂ := fun _ => 1) (f₂' := fun _ => 0)
      (φ₁ := w) (φ₂ := fun s => (p s : ℂ) * deriv u s * w s)
      (fun t ht => (hu t ht).2) (hcq.neg.mul hcu) (fun t _ => hasDerivAt_const t (1 : ℂ))
      continuousOn_const hcw hcPuw (fun t _ => (one_mul _).symm) hS hρ₂ hρ₂ hr
  have hΦ : ∀ r ∈ Ioi a, HasDerivAt
      (fun x => ((p x : ℂ) * deriv w x * (∫ t in ρ₁..x, u t * S t) -
          1 * ∫ t in ρ₁..x, (p t : ℂ) * deriv w t * u t * S t) -
        ((p x : ℂ) * deriv u x * (∫ t in ρ₂..x, w t * S t) -
          1 * ∫ t in ρ₂..x, (p t : ℂ) * deriv u t * w t * S t))
      (-(q r : ℂ) * (W * R r)) r := by
    intro r hr
    refine ((hΦw r hr).sub (hΦu r hr)).congr_deriv ?_
    rw [hR' r, mul_div_cancel₀ _ hW]
    ring
  intro r₁ hr₁ r₂ hr₂
  have hsub : uIcc r₁ r₂ ⊆ Ioi a := ordConnected_Ioi.uIcc_subset hr₁ hr₂
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hΦ x (hsub hx))
    ((((hcq.neg).mul (continuousOn_const.mul hcR)).mono hsub).intervalIntegrable)
  have hGw := intervalIntegral.integral_interval_sub_left
    (gf_intervalIntegrable_mul hcPwu hS hρ₁ hr₂)
    (gf_intervalIntegrable_mul hcPwu hS hρ₁ hr₁)
  have hGu := intervalIntegral.integral_interval_sub_left
    (gf_intervalIntegrable_mul hcPuw hS hρ₂ hr₂)
    (gf_intervalIntegrable_mul hcPuw hS hρ₂ hr₁)
  have hWS : (∫ t in r₁..r₂, (p t : ℂ) * deriv w t * u t * S t) -
      (∫ t in r₁..r₂, (p t : ℂ) * deriv u t * w t * S t) = W * ∫ t in r₁..r₂, S t := by
    rw [← intervalIntegral.integral_sub (gf_intervalIntegrable_mul hcPwu hS hr₁ hr₂)
      (gf_intervalIntegrable_mul hcPuw hS hr₁ hr₂), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [← hWr t (hsub ht)]
    ring
  have hqR : ∫ x in r₁..r₂, -(q x : ℂ) * (W * R x) = -(W * ∫ x in r₁..r₂, (q x : ℂ) * R x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  have hRHS : ∫ r in r₁..r₂, (S r - (q r : ℂ) * R r) =
      (∫ r in r₁..r₂, S r) - ∫ r in r₁..r₂, (q r : ℂ) * R r :=
    intervalIntegral.integral_sub (hS _ hr₁ _ hr₂) (((hcq.mul hcR).mono hsub).intervalIntegrable)
  apply mul_left_cancel₀ hW
  rw [mul_sub, hpR r₂ hr₂, hpR r₁ hr₁, hRHS]
  rw [hqR] at hFTC
  linear_combination (-1 : ℂ) * hFTC + hGw - hGu + hWS

/-- Left of the support of `S`: the Green formula is `c_H u` on `r ≤ ρ₁`, with
`c_H = W⁻¹ ∫_{ρ₁}^{ρ₂} w S`. -/
theorem green_eq_left {ρ₁ ρ₂ r : ℝ} {u w S : ℝ → ℂ} {W : ℂ}
    (hS0 : ∀ t, t ∉ Icc ρ₁ ρ₂ → S t = 0) (hr : r ≤ ρ₁)
    (hi₁ : IntervalIntegrable (fun t => w t * S t) volume r ρ₁)
    (hi₂ : IntervalIntegrable (fun t => w t * S t) volume ρ₁ ρ₂) :
    (w r * (∫ t in ρ₁..r, u t * S t) + u r * ∫ t in r..ρ₂, w t * S t) / W =
      (∫ t in ρ₁..ρ₂, w t * S t) / W * u r := by
  have hz : ∀ φ : ℝ → ℂ, ∫ t in r..ρ₁, φ t * S t = 0 := by
    intro φ
    rw [intervalIntegral.integral_of_le hr, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
      rw [hS0 t fun h => (not_le.2 ht.2) h.1, mul_zero]
  rw [intervalIntegral.integral_symm r ρ₁, hz u,
    ← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂, hz w]
  ring

/-- Right of the support of `S`: the Green formula is `c_I w` on `r ≥ ρ₂`, with
`c_I = W⁻¹ ∫_{ρ₁}^{ρ₂} u S`. -/
theorem green_eq_right {ρ₁ ρ₂ r : ℝ} {u w S : ℝ → ℂ} {W : ℂ}
    (hS0 : ∀ t, t ∉ Icc ρ₁ ρ₂ → S t = 0) (hr : ρ₂ ≤ r)
    (hi₁ : IntervalIntegrable (fun t => u t * S t) volume ρ₁ ρ₂)
    (hi₂ : IntervalIntegrable (fun t => u t * S t) volume ρ₂ r) :
    (w r * (∫ t in ρ₁..r, u t * S t) + u r * ∫ t in r..ρ₂, w t * S t) / W =
      (∫ t in ρ₁..ρ₂, u t * S t) / W * w r := by
  have hz : ∀ φ : ℝ → ℂ, ∫ t in ρ₂..r, φ t * S t = 0 := by
    intro φ
    rw [intervalIntegral.integral_of_le hr]
    exact setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
      rw [hS0 t fun h => (not_le.2 ht.1) h.2, mul_zero]
  rw [intervalIntegral.integral_symm ρ₂ r, hz w,
    ← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂, hz u]
  ring

/-! ### The integrated equation -/

/-- A differentiable solution of the integrated homogeneous equation
`p(r₂)R'(r₂) − p(r₁)R'(r₁) = −∫_{r₁}^{r₂} q R` on `(a, ∞)` satisfies `(p R')' = −q R`
pointwise. -/
theorem hasDerivAt_of_integrated {a : ℝ} {p q : ℝ → ℝ} {R : ℝ → ℂ}
    (hq : ContinuousOn q (Ioi a)) (hR : ∀ r ∈ Ioi a, DifferentiableAt ℝ R r)
    (hint : ∀ r₁ ∈ Ioi a, ∀ r₂ ∈ Ioi a,
      (p r₂ : ℂ) * deriv R r₂ - (p r₁ : ℂ) * deriv R r₁ = -∫ r in r₁..r₂, (q r : ℂ) * R r) :
    ∀ r ∈ Ioi a, DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv R s) (-(q r : ℂ) * R r) r := by
  intro r hr
  refine ⟨hR r hr, ?_⟩
  have hc : ContinuousOn (fun s => (q s : ℂ) * R s) (Ioi a) :=
    (continuous_ofReal.comp_continuousOn hq).mul fun s hs =>
      (hR s hs).continuousAt.continuousWithinAt
  have hF : HasDerivAt (fun x => ∫ s in r..x, (q s : ℂ) * R s) ((q r : ℂ) * R r) r :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hc.stronglyMeasurableAtFilter isOpen_Ioi r hr) (hc.continuousAt (Ioi_mem_nhds hr))
  have h := (hasDerivAt_const r ((p r : ℂ) * deriv R r)).sub hF
  refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards [Ioi_mem_nhds hr] with x hx
  change (p x : ℂ) * deriv R x = (p r : ℂ) * deriv R r - ∫ s in r..x, (q s : ℂ) * R s
  linear_combination hint r hr x hx

/-- The difference of two solutions of the integrated source equation solves the integrated
homogeneous equation. -/
theorem integrated_sub {a : ℝ} {p q : ℝ → ℝ} {R₁ R₂ S : ℝ → ℂ}
    (hq : ContinuousOn q (Ioi a)) (hR₁ : ∀ r ∈ Ioi a, DifferentiableAt ℝ R₁ r)
    (hR₂ : ∀ r ∈ Ioi a, DifferentiableAt ℝ R₂ r)
    (hS : ∀ x ∈ Ioi a, ∀ y ∈ Ioi a, IntervalIntegrable S volume x y)
    (h₁ : ∀ r₁ ∈ Ioi a, ∀ r₂ ∈ Ioi a, (p r₂ : ℂ) * deriv R₁ r₂ - (p r₁ : ℂ) * deriv R₁ r₁ =
      ∫ r in r₁..r₂, (S r - (q r : ℂ) * R₁ r))
    (h₂ : ∀ r₁ ∈ Ioi a, ∀ r₂ ∈ Ioi a, (p r₂ : ℂ) * deriv R₂ r₂ - (p r₁ : ℂ) * deriv R₂ r₁ =
      ∫ r in r₁..r₂, (S r - (q r : ℂ) * R₂ r)) :
    ∀ r₁ ∈ Ioi a, ∀ r₂ ∈ Ioi a,
      (p r₂ : ℂ) * deriv (fun s => R₁ s - R₂ s) r₂ -
          (p r₁ : ℂ) * deriv (fun s => R₁ s - R₂ s) r₁ =
        -∫ r in r₁..r₂, (q r : ℂ) * (R₁ r - R₂ r) := by
  intro r₁ hr₁ r₂ hr₂
  have hsub : uIcc r₁ r₂ ⊆ Ioi a := ordConnected_Ioi.uIcc_subset hr₁ hr₂
  have hcq : ContinuousOn (fun s => (q s : ℂ)) (Ioi a) := continuous_ofReal.comp_continuousOn hq
  have hi : ∀ {R : ℝ → ℂ}, (∀ r ∈ Ioi a, DifferentiableAt ℝ R r) →
      IntervalIntegrable (fun r => S r - (q r : ℂ) * R r) volume r₁ r₂ := fun hR =>
    (hS _ hr₁ _ hr₂).sub (((hcq.mul fun s hs => (hR s hs).continuousAt.continuousWithinAt).mono
      hsub).intervalIntegrable)
  have e : (∫ r in r₁..r₂, (S r - (q r : ℂ) * R₁ r)) - ∫ r in r₁..r₂, (S r - (q r : ℂ) * R₂ r) =
      ∫ r in r₁..r₂, -((q r : ℂ) * (R₁ r - R₂ r)) := by
    rw [← intervalIntegral.integral_sub (hi hR₁) (hi hR₂)]
    congr 1
    funext r
    ring
  rw [deriv_fun_sub (hR₁ r₂ hr₂) (hR₂ r₂ hr₂), deriv_fun_sub (hR₁ r₁ hr₁) (hR₂ r₁ hr₁),
    ← intervalIntegral.integral_neg]
  linear_combination h₁ r₁ hr₁ r₂ hr₂ - h₂ r₁ hr₁ r₂ hr₂ + e

end ModeStability.AllAngular

end
