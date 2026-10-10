module

public import Mathlib
public import ModeStability.Frozen.Dephase
public import ModeStability.Frozen.DephasedCurrent
public import ModeStability.Current.Dephased

/-!
# The dephased current on an arbitrary open interval

Source: the all-angular research notes in preparation, Section 4, (4.1)–(4.2), p. 5.; and the
middle-interval
identity (5.2), p. 6: `−J_x = |U_x|² + (V − k²)|U|²` for `J = −Re(U_x Ū)`.

The landed versions (`ModeStability.Current`, `ModeStability.dephasedCurrent_dephase_eq`) live on
`(0, ∞)` with a base point `x₀ > 0`. Here the same calculus is stated on an arbitrary open,
order-connected set `s ⊆ ℝ` (an open interval `Ioo α β`, `Ioi α`, `Iio β` or `univ`) containing
the base point `x₀` of the phase `ϑ(x) = ∫_{x₀}^x k`. The set is called `s` rather than `I`
because `I` is the imaginary unit under `open Complex`.

* `hasDerivAt_phase_on`: `ϑ' = k` on `s`;
* `hasDerivAt_dephase_on`, `deriv_dephase_on`, `norm_deriv_dephase_on`: the formula
  `v_x = e^{iσϑ}(U_x + iσkU)`, so `|v_x| = |U_x + iσkU|`;
* `hasDerivAt_deriv_dephase_on`: the conjugated equation (4.1), `v_xx = iσ(2 k v_x + k_x v)`;
* `hasDerivAt_dephasedCurrent_at`, `hasDerivAt_dephasedCurrent_on`: (4.2),
  `J' = −(E_k/k_x²)|v_x|²` wherever `k_x ≠ 0`;
* `dephasedCurrent_dephase_eq_on`: the phase-free form `J = −(k/k_x)|U_x + iσkU|² − Re(U_x Ū)`;
* `antitoneOn_dephasedCurrent_on`: `J` is antitone on `s` when `E_k/k_x² ≥ 0` there;
* `eqOn_zero_of_deriv_dephase_eq_zero_on`, `eqOn_zero_of_dephasedCurrent_const_on`: rigidity,
  `v_x = 0` (or `J` constant with `E_k/k_x² > 0`) on an open subset forces `U = 0` there;
* `hasDerivAt_neg_re_flux`, `antitoneOn_neg_re_flux`, `eqOn_zero_of_neg_re_flux_const_on`: the
  middle-interval current (5.2) for `U_xx = W U`.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

variable {k : ℝ → ℝ} {U : ℝ → ℂ} {s : Set ℝ} {x₀ σ : ℝ}

/-! ### The phase and the dephased function -/

/-- `ϑ(x) = ∫_{x₀}^x k` has derivative `k(x)` at every point of an open order-connected set `s`
containing `x₀` on which `k` is continuous (fundamental theorem of calculus). -/
theorem hasDerivAt_phase_on (hs : IsOpen s) (hsc : s.OrdConnected) (hx₀ : x₀ ∈ s)
    (hk : ContinuousOn k s) {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (fun y => ∫ ξ in x₀..y, k ξ) (k x) x := by
  refine intervalIntegral.integral_hasDerivAt_right ?_
    (hk.stronglyMeasurableAtFilter hs x hx) (hk.continuousAt (hs.mem_nhds hx))
  exact (hk.mono (hsc.uIcc_subset hx₀ hx)).intervalIntegrable

/-- A `C²` function on an open set is differentiable at every point of it. -/
theorem differentiableAt_of_contDiffOn_on (hs : IsOpen s) (hk : ContDiffOn ℝ 2 k s) {x : ℝ}
    (hx : x ∈ s) : DifferentiableAt ℝ k x :=
  (hk.differentiableOn (by norm_num)).differentiableAt (hs.mem_nhds hx)

/-- The derivative of a `C²` function on an open set is differentiable at every point of it. -/
theorem differentiableAt_deriv_of_contDiffOn_on (hs : IsOpen s) (hk : ContDiffOn ℝ 2 k s)
    {x : ℝ} (hx : x ∈ s) : DifferentiableAt ℝ (deriv k) x :=
  ((hk.deriv_of_isOpen hs (m := 1) (by norm_num)).differentiableOn
    (by norm_num)).differentiableAt (hs.mem_nhds hx)

/-- The phase factor `e^{iσϑ}` has modulus one. -/
theorem norm_exp_phase (k : ℝ → ℝ) (x₀ σ x : ℝ) :
    ‖exp (σ * (∫ ξ in x₀..x, k ξ) * I)‖ = 1 := by
  have h : (σ : ℂ) * ((∫ ξ in x₀..x, k ξ : ℝ) : ℂ) * I = ((σ * ∫ ξ in x₀..x, k ξ : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The dephased function `v = e^{iσϑ} U` has derivative `e^{iσϑ} (U_x + iσ k U)` on `s`. -/
theorem hasDerivAt_dephase_on (hs : IsOpen s) (hsc : s.OrdConnected) (hx₀ : x₀ ∈ s)
    (hk : ContinuousOn k s) {x : ℝ} (hx : x ∈ s) (hU : DifferentiableAt ℝ U x) :
    HasDerivAt (dephase k x₀ σ U)
      (exp (σ * (∫ ξ in x₀..x, k ξ) * I) * (deriv U x + σ * k x * I * U x)) x := by
  have hphase :=
    ((hasDerivAt_phase_on hs hsc hx₀ hk hx).ofReal_comp.const_mul (σ : ℂ)).mul_const I
  have h := hphase.cexp.mul hU.hasDerivAt
  change HasDerivAt (fun y => exp (σ * (∫ ξ in x₀..y, k ξ) * I) * U y) _ x
  convert h using 1
  ring

/-- Formula for the derivative of the dephased function on `s`. -/
theorem deriv_dephase_on (hs : IsOpen s) (hsc : s.OrdConnected) (hx₀ : x₀ ∈ s)
    (hk : ContinuousOn k s) {x : ℝ} (hx : x ∈ s) (hU : DifferentiableAt ℝ U x) :
    deriv (dephase k x₀ σ U) x =
      exp (σ * (∫ ξ in x₀..x, k ξ) * I) * (deriv U x + σ * k x * I * U x) :=
  (hasDerivAt_dephase_on hs hsc hx₀ hk hx hU).deriv

/-- `|v_x| = |U_x + iσ k U|` on `s`. -/
theorem norm_deriv_dephase_on (hs : IsOpen s) (hsc : s.OrdConnected) (hx₀ : x₀ ∈ s)
    (hk : ContinuousOn k s) {x : ℝ} (hx : x ∈ s) (hU : DifferentiableAt ℝ U x) :
    ‖deriv (dephase k x₀ σ U) x‖ = ‖deriv U x + σ * k x * I * U x‖ := by
  rw [deriv_dephase_on hs hsc hx₀ hk hx hU, norm_mul, norm_exp_phase, one_mul]

/-! ### The conjugated equation (4.1) and the current identity (4.2) -/

/-- **(4.1) on `s`.** For `k` real and `C²` on `s`, `U_xx = -k² U` on `s` and `σ = ±1`, the
dephased function `v = e^{iσϑ} U` satisfies `v_xx = iσ (2 k v_x + k_x v)` on `s`. -/
theorem hasDerivAt_deriv_dephase_on (hs : IsOpen s) (hsc : s.OrdConnected) (hx₀ : x₀ ∈ s)
    (hk : ContDiffOn ℝ 2 k s) (hσ : σ = 1 ∨ σ = -1)
    (hU : ∀ x ∈ s, DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x)
    {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (deriv (dephase k x₀ σ U))
      (σ * I * (2 * k x * deriv (dephase k x₀ σ U) x + deriv k x * dephase k x₀ σ U x)) x := by
  have hσ2 : (σ : ℂ) ^ 2 = 1 := by
    rcases hσ with rfl | rfl <;> simp
  have hkc : ContinuousOn k s := hk.continuousOn
  have hkd := (differentiableAt_of_contDiffOn_on hs hk hx).hasDerivAt
  -- the derivative of `v` agrees with an explicit formula near `x`
  have heq : deriv (dephase k x₀ σ U) =ᶠ[𝓝 x]
      fun y => exp (σ * (∫ ξ in x₀..y, k ξ) * I) * (deriv U y + σ * k y * I * U y) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact deriv_dephase_on hs hsc hx₀ hkc hy (hU y hy).1
  have hphase :=
    ((hasDerivAt_phase_on hs hsc hx₀ hkc hx).ofReal_comp.const_mul (σ : ℂ)).mul_const I
  have hE := hphase.cexp
  have hF := (hU x hx).2.add (((hkd.ofReal_comp.const_mul (σ : ℂ)).mul_const I).mul
    (hU x hx).1.hasDerivAt)
  have h := (hE.mul hF).congr_of_eventuallyEq heq
  rw [deriv_dephase_on hs hsc hx₀ hkc hx (hU x hx).1]
  simp only [Pi.add_apply, Pi.mul_apply] at h
  convert h using 1
  unfold dephase
  push_cast
  linear_combination (exp (σ * (∫ ξ in x₀..x, k ξ) * I) * (k x : ℂ) ^ 2 * U x * I ^ 2) * hσ2 +
    (exp (σ * (∫ ξ in x₀..x, k ξ) * I) * (k x : ℂ) ^ 2 * U x) * Complex.I_sq

/-- **(4.2), pointwise.** At a point `x ∈ s` with `k_x(x) ≠ 0`, the current of the dephased
function has derivative `J' = -((2 k_x² - k k_xx) / k_x²) |v_x|²`. -/
theorem hasDerivAt_dephasedCurrent_at (hs : IsOpen s) (hsc : s.OrdConnected) (hx₀ : x₀ ∈ s)
    (hk : ContDiffOn ℝ 2 k s) (hσ : σ = 1 ∨ σ = -1)
    (hU : ∀ x ∈ s, DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x)
    {x : ℝ} (hx : x ∈ s) (hkx : deriv k x ≠ 0) :
    HasDerivAt (dephasedCurrent k (dephase k x₀ σ U))
      (-((2 * deriv k x ^ 2 - k x * deriv (deriv k) x) / deriv k x ^ 2) *
        ‖deriv (dephase k x₀ σ U) x‖ ^ 2) x := by
  have hv : DifferentiableAt ℝ (dephase k x₀ σ U) x :=
    (hasDerivAt_dephase_on hs hsc hx₀ hk.continuousOn hx (hU x hx).1).differentiableAt
  exact Current.hasDerivAt_current (differentiableAt_of_contDiffOn_on hs hk hx)
    (differentiableAt_deriv_of_contDiffOn_on hs hk hx) hkx hv
    (hasDerivAt_deriv_dephase_on hs hsc hx₀ hk hσ hU hx)

/-- **(4.2) on `s`.** If `k` is real and `C²` on `s` with `k_x ≠ 0` there, `U_xx = -k² U` on `s`
and `σ = ±1`, then `J[v]' = -(E_k / k_x²) |v_x|²` on `s`, `E_k = 2 k_x² - k k_xx`. -/
theorem hasDerivAt_dephasedCurrent_on (hs : IsOpen s) (hsc : s.OrdConnected) (hx₀ : x₀ ∈ s)
    (hk : ContDiffOn ℝ 2 k s) (hkx : ∀ x ∈ s, deriv k x ≠ 0) (hσ : σ = 1 ∨ σ = -1)
    (hU : ∀ x ∈ s, DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x)
    {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (dephasedCurrent k (dephase k x₀ σ U))
      (-((2 * deriv k x ^ 2 - k x * deriv (deriv k) x) / deriv k x ^ 2) *
        ‖deriv (dephase k x₀ σ U) x‖ ^ 2) x :=
  hasDerivAt_dephasedCurrent_at hs hsc hx₀ hk hσ hU hx (hkx x hx)

/-- The current of the dephased function does not see the phase: on `s`,
`J[e^{iσϑ} U](x) = −(k/k_x) |U' + iσkU|² − Re(U' Ū)`. -/
theorem dephasedCurrent_dephase_eq_on (hs : IsOpen s) (hsc : s.OrdConnected) (hx₀ : x₀ ∈ s)
    (hk : ContinuousOn k s) (σ : ℝ) {x : ℝ} (hx : x ∈ s) (hU : DifferentiableAt ℝ U x) :
    dephasedCurrent k (dephase k x₀ σ U) x =
      -(k x / deriv k x) * ‖deriv U x + σ * k x * I * U x‖ ^ 2 -
        (deriv U x * (starRingEnd ℂ) (U x)).re := by
  have hdv := deriv_dephase_on (σ := σ) hs hsc hx₀ hk hx hU
  set θ : ℝ := σ * ∫ ξ in x₀..x, k ξ with hθ
  have he : exp (σ * (∫ ξ in x₀..x, k ξ) * I) = exp (θ * I) := by
    rw [hθ]; push_cast; ring_nf
  have hnorm : ‖exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hconj : exp (θ * I) * (starRingEnd ℂ) (exp (θ * I)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp
  unfold dephasedCurrent
  rw [hdv, he]
  have hv : dephase k x₀ σ U x = exp (θ * I) * U x := by
    unfold dephase; rw [← he]
  rw [hv, norm_mul, hnorm, one_mul, map_mul]
  congr 1
  have : exp (θ * I) * (deriv U x + σ * k x * I * U x) *
      ((starRingEnd ℂ) (exp (θ * I)) * (starRingEnd ℂ) (U x)) =
      (exp (θ * I) * (starRingEnd ℂ) (exp (θ * I))) *
        ((deriv U x + σ * k x * I * U x) * (starRingEnd ℂ) (U x)) := by ring
  rw [this, hconj, one_mul, add_mul, Complex.add_re]
  have : ((σ : ℂ) * k x * I * U x * (starRingEnd ℂ) (U x)).re = 0 := by
    rw [mul_assoc, Complex.mul_conj]
    simp [Complex.mul_re]
  rw [this, add_zero]

/-- At a zero of `k` in `s`, the current of the dephased function is `−Re(U_x Ū)`. -/
theorem dephasedCurrent_dephase_eq_of_eq_zero_on (hs : IsOpen s) (hsc : s.OrdConnected)
    (hx₀ : x₀ ∈ s) (hk : ContinuousOn k s) (σ : ℝ) {x : ℝ} (hx : x ∈ s)
    (hU : DifferentiableAt ℝ U x) (hkx : k x = 0) :
    dephasedCurrent k (dephase k x₀ σ U) x = -(deriv U x * (starRingEnd ℂ) (U x)).re := by
  rw [dephasedCurrent_dephase_eq_on hs hsc hx₀ hk σ hx hU, hkx]
  simp

/-! ### Monotonicity and rigidity -/

/-- **Monotonicity on `s`.** If `k_x ≠ 0` and `E_k / k_x² ≥ 0` on `s`, the current `J[v]` of the
dephased function is antitone on `s`. -/
theorem antitoneOn_dephasedCurrent_on (hs : IsOpen s) (hsc : s.OrdConnected) (hx₀ : x₀ ∈ s)
    (hk : ContDiffOn ℝ 2 k s) (hkx : ∀ x ∈ s, deriv k x ≠ 0)
    (hE : ∀ x ∈ s, 0 ≤ (2 * deriv k x ^ 2 - k x * deriv (deriv k) x) / deriv k x ^ 2)
    (hσ : σ = 1 ∨ σ = -1)
    (hU : ∀ x ∈ s, DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x) :
    AntitoneOn (dephasedCurrent k (dephase k x₀ σ U)) s := by
  have h := fun {x : ℝ} (hx : x ∈ s) => hasDerivAt_dephasedCurrent_on hs hsc hx₀ hk hkx hσ hU hx
  refine antitoneOn_of_deriv_nonpos hsc.convex ?_ ?_ ?_
  · exact fun x hx => (h hx).continuousAt.continuousWithinAt
  · rw [hs.interior_eq]
    exact fun x hx => (h hx).differentiableAt.differentiableWithinAt
  · rw [hs.interior_eq]
    intro x hx
    rw [(h hx).deriv, neg_mul, neg_nonpos]
    exact mul_nonneg (hE x hx) (sq_nonneg _)

/-- **Rigidity from `v_x = 0`.** If `v_x = 0` on an open set `t ⊆ s` on which `k_x ≠ 0`, then
`U = 0` on `t`: the conjugated equation (4.1) reduces to `iσ k_x v = 0` there. -/
theorem eqOn_zero_of_deriv_dephase_eq_zero_on (hs : IsOpen s) (hsc : s.OrdConnected)
    (hx₀ : x₀ ∈ s) (hk : ContDiffOn ℝ 2 k s) (hσ : σ = 1 ∨ σ = -1)
    (hU : ∀ x ∈ s, DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x)
    {t : Set ℝ} (ht : IsOpen t) (hts : t ⊆ s) (hkx : ∀ x ∈ t, deriv k x ≠ 0)
    (hv : ∀ x ∈ t, deriv (dephase k x₀ σ U) x = 0) :
    ∀ x ∈ t, U x = 0 := by
  intro x hx
  have hvv : HasDerivAt (deriv (dephase k x₀ σ U)) 0 x :=
    (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (ht.mem_nhds hx) hv)
  have h1 := hvv.unique (hasDerivAt_deriv_dephase_on hs hsc hx₀ hk hσ hU (hts hx))
  rw [hv x hx, mul_zero, zero_add] at h1
  have hσ0 : (σ : ℂ) ≠ 0 := by
    rcases hσ with rfl | rfl <;> simp
  have hkx0 : ((deriv k x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hkx x hx)
  have hexp : exp (σ * (∫ ξ in x₀..x, k ξ) * I) ≠ 0 := Complex.exp_ne_zero _
  have h2 : dephase k x₀ σ U x = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 h1.symm).resolve_left
      (mul_ne_zero hσ0 Complex.I_ne_zero))).resolve_left hkx0
  exact (mul_eq_zero.1 h2).resolve_left hexp

/-- **Rigidity on `s`.** If the current `J[v]` is constant on an open set `t ⊆ s` on which
`k_x ≠ 0` and `E_k / k_x² > 0`, then `U = 0` on `t`: `J' = -(E_k/k_x²)|v_x|² = 0` forces
`v_x = 0` there. -/
theorem eqOn_zero_of_dephasedCurrent_const_on (hs : IsOpen s) (hsc : s.OrdConnected)
    (hx₀ : x₀ ∈ s) (hk : ContDiffOn ℝ 2 k s) (hσ : σ = 1 ∨ σ = -1)
    (hU : ∀ x ∈ s, DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x)
    {t : Set ℝ} (ht : IsOpen t) (hts : t ⊆ s) (hkx : ∀ x ∈ t, deriv k x ≠ 0)
    (hE : ∀ x ∈ t, 0 < (2 * deriv k x ^ 2 - k x * deriv (deriv k) x) / deriv k x ^ 2)
    {C : ℝ} (hJ : ∀ x ∈ t, dephasedCurrent k (dephase k x₀ σ U) x = C) :
    ∀ x ∈ t, U x = 0 := by
  refine eqOn_zero_of_deriv_dephase_eq_zero_on hs hsc hx₀ hk hσ hU ht hts hkx fun x hx => ?_
  have h0 : HasDerivAt (dephasedCurrent k (dephase k x₀ σ U)) 0 x :=
    (hasDerivAt_const x C).congr_of_eventuallyEq (Filter.eventually_of_mem (ht.mem_nhds hx) hJ)
  have h1 := (hasDerivAt_dephasedCurrent_at hs hsc hx₀ hk hσ hU (hts hx) (hkx x hx)).unique h0
  rw [neg_mul, neg_eq_zero] at h1
  have h2 : ‖deriv (dephase k x₀ σ U) x‖ ^ 2 = 0 :=
    (mul_eq_zero.1 h1).resolve_left (hE x hx).ne'
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

/-! ### The middle-interval current (5.2) -/

/-- **(5.2), pointwise.** If `U_xx = W U` with `W` real, the current `−Re(U_x Ū)` has derivative
`−(|U_x|² + W |U|²)`. -/
theorem hasDerivAt_neg_re_flux {W : ℝ → ℝ} {x : ℝ} (hU : DifferentiableAt ℝ U x)
    (hU' : HasDerivAt (deriv U) ((W x : ℂ) * U x) x) :
    HasDerivAt (fun y => -(deriv U y * (starRingEnd ℂ) (U y)).re)
      (-(‖deriv U x‖ ^ 2 + W x * ‖U x‖ ^ 2)) x := by
  refine (Current.hasDerivAt_re (hU'.mul hU.hasDerivAt.star)).neg.congr_deriv ?_
  generalize deriv U x = w
  generalize U x = u
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.add_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/-- If `U_xx = W U` with `W ≥ 0` on an open order-connected set `s`, the current `−Re(U_x Ū)` is
antitone on `s`. -/
theorem antitoneOn_neg_re_flux {W : ℝ → ℝ} (hs : IsOpen s) (hsc : s.OrdConnected)
    (hW : ∀ x ∈ s, 0 ≤ W x)
    (hU : ∀ x ∈ s, DifferentiableAt ℝ U x ∧ HasDerivAt (deriv U) ((W x : ℂ) * U x) x) :
    AntitoneOn (fun y => -(deriv U y * (starRingEnd ℂ) (U y)).re) s := by
  have h := fun {x : ℝ} (hx : x ∈ s) => hasDerivAt_neg_re_flux (hU x hx).1 (hU x hx).2
  refine antitoneOn_of_deriv_nonpos hsc.convex ?_ ?_ ?_
  · exact fun x hx => (h hx).continuousAt.continuousWithinAt
  · rw [hs.interior_eq]
    exact fun x hx => (h hx).differentiableAt.differentiableWithinAt
  · rw [hs.interior_eq]
    intro x hx
    rw [(h hx).deriv, neg_nonpos]
    have := hW x hx
    positivity

/-- **Rigidity on the forbidden interval.** If `U_xx = W U` with `W > 0` on an open set `t` and
the current `−Re(U_x Ū)` is constant on `t`, then `U = 0` on `t`. -/
theorem eqOn_zero_of_neg_re_flux_const_on {W : ℝ → ℝ} {t : Set ℝ} (ht : IsOpen t)
    (hW : ∀ x ∈ t, 0 < W x)
    (hU : ∀ x ∈ t, DifferentiableAt ℝ U x ∧ HasDerivAt (deriv U) ((W x : ℂ) * U x) x)
    {C : ℝ} (hJ : ∀ x ∈ t, -(deriv U x * (starRingEnd ℂ) (U x)).re = C) :
    ∀ x ∈ t, U x = 0 := by
  intro x hx
  have h0 : HasDerivAt (fun y => -(deriv U y * (starRingEnd ℂ) (U y)).re) 0 x :=
    (hasDerivAt_const x C).congr_of_eventuallyEq (Filter.eventually_of_mem (ht.mem_nhds hx) hJ)
  have h1 := (hasDerivAt_neg_re_flux (hU x hx).1 (hU x hx).2).unique h0
  have h2 : W x * ‖U x‖ ^ 2 = 0 := by
    have h3 : 0 ≤ ‖deriv U x‖ ^ 2 := sq_nonneg _
    have h4 : 0 ≤ W x * ‖U x‖ ^ 2 := mul_nonneg (hW x hx).le (sq_nonneg _)
    linarith
  have h5 : ‖U x‖ ^ 2 = 0 := (mul_eq_zero.1 h2).resolve_left (hW x hx).ne'
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h5)

end ModeStability.AllAngular

end
