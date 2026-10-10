module

public import Mathlib
public import ModeStability.Frozen.DephasedCurrentLemma
public import ModeStability.Current.Dephased

/-!
# Monotonicity and rigidity of the dephased current

Abstract facts about the current `J[v](x) = -(k/k_x) |v_x|² - Re (v_x v̄)` of Lemma 2.2
(the spherical research notes in preparation, (2.5)-(2.8)) used in the proof of Proposition 2.3.
Throughout `k` is real, `C²` on `(0, ∞)` with `k_x > 0` and `E := 2 k_x² - k k_xx > 0` there,
`U_xx = -k² U` on `(0, ∞)`, `k(x₀) = 0`, and `v = e^{iσϑ} U` with `σ = ±1`.

* `antitoneOn_current`: `J` is antitone on `(0, ∞)` (by (2.7) and (2.4));
* `eqOn_zero_of_current_eq_zero`: if `J = 0` on an open interval `(c, d) ⊆ (0, ∞)`, then `U = 0`
  there (rigidity: `v_x = 0`, then the conjugated equation forces `v = 0`);
* `horizon_alternative`: if `J → 0` at `0⁺`, then `Re (U_x Ū)(x₀) > 0` or `U = 0` on `(0, x₀)`;
* `infinity_alternative`: if `J → 0` at `∞`, then `Re (U_x Ū)(x₀) < 0` or `U = 0` on `(x₀, ∞)`.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.Corotation

/-- The current `J[v]` is antitone on `(0, ∞)`: its derivative `-(E/k_x²)|v_x|²` is nonpositive. -/
theorem antitoneOn_current {k : ℝ → ℝ} {U : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hk : ContDiffOn ℝ 2 k (Ioi 0)) (hkx : ∀ x ∈ Ioi (0 : ℝ), 0 < deriv k x)
    (hE : ∀ x ∈ Ioi (0 : ℝ), 0 < 2 * deriv k x ^ 2 - k x * deriv (deriv k) x)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x)
    (hk₀ : k x₀ = 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    AntitoneOn (dephasedCurrent k (dephase k x₀ σ U)) (Ioi 0) := by
  have h := (dephased_current k U x₀ hx₀ hk hkx hU hk₀ σ hσ).1
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
  · exact fun x hx => (h x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (h x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(h x hx).deriv]
    have h1 := hE x hx
    have h2 : 0 < deriv k x ^ 2 := pow_pos (hkx x hx) 2
    have h3 : 0 ≤ (2 * deriv k x ^ 2 - k x * deriv (deriv k) x) / deriv k x ^ 2 *
        ‖deriv (dephase k x₀ σ U) x‖ ^ 2 := by positivity
    linarith

/-- Rigidity: if the current vanishes on an open interval `(c, d) ⊆ (0, ∞)`, then `U = 0` there.
Indeed `J' = -(E/k_x²)|v_x|² = 0` forces `v_x = 0`, and then the conjugated equation
`v_xx = iσ (2 k v_x + k_x v)` forces `k_x v = 0`. -/
theorem eqOn_zero_of_current_eq_zero {k : ℝ → ℝ} {U : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hk : ContDiffOn ℝ 2 k (Ioi 0)) (hkx : ∀ x ∈ Ioi (0 : ℝ), 0 < deriv k x)
    (hE : ∀ x ∈ Ioi (0 : ℝ), 0 < 2 * deriv k x ^ 2 - k x * deriv (deriv k) x)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x)
    (hk₀ : k x₀ = 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {c d : ℝ} (hc : 0 ≤ c)
    (hJ : ∀ x ∈ Ioo c d, dephasedCurrent k (dephase k x₀ σ U) x = 0) :
    ∀ x ∈ Ioo c d, U x = 0 := by
  have h := (dephased_current k U x₀ hx₀ hk hkx hU hk₀ σ hσ).1
  have hpos : ∀ x ∈ Ioo c d, 0 < x := fun x hx => lt_of_le_of_lt hc hx.1
  -- `v_x = 0` on `(c, d)`
  have hv' : ∀ x ∈ Ioo c d, deriv (dephase k x₀ σ U) x = 0 := by
    intro x hx
    have hx0 : x ∈ Ioi (0 : ℝ) := hpos x hx
    have h0 : HasDerivAt (dephasedCurrent k (dephase k x₀ σ U)) 0 x :=
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) hJ)
    have h1 := (h x hx0).unique h0
    have h2 := hE x hx0
    have h3 := hkx x hx0
    have h4 : 0 < (2 * deriv k x ^ 2 - k x * deriv (deriv k) x) / deriv k x ^ 2 := by positivity
    have h5 : ‖deriv (dephase k x₀ σ U) x‖ ^ 2 = 0 := by
      have h1' : (2 * deriv k x ^ 2 - k x * deriv (deriv k) x) / deriv k x ^ 2 *
          ‖deriv (dephase k x₀ σ U) x‖ ^ 2 = 0 := by linarith
      exact (mul_eq_zero.1 h1').resolve_left h4.ne'
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h5)
  intro x hx
  have hx0 : 0 < x := hpos x hx
  -- `v_xx = 0` at `x`
  have hvv : HasDerivAt (deriv (dephase k x₀ σ U)) 0 x :=
    (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) hv')
  have hconj := Current.hasDerivAt_deriv_dephased hx₀ hk hσ hU hx0
  have h1 := hvv.unique hconj
  have hv'x : deriv (dephase k x₀ σ U) x = 0 := hv' x hx
  have h2 : (σ : ℂ) * I * (2 * k x * deriv (dephase k x₀ σ U) x +
      deriv k x * (exp (σ * (∫ ξ in x₀..x, k ξ) * I) * U x)) = 0 := h1.symm
  rw [hv'x, mul_zero, zero_add] at h2
  have hσ0 : (σ : ℂ) ≠ 0 := by
    rcases hσ with rfl | rfl <;> simp
  have hkx0 : ((deriv k x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hkx x hx0).ne'
  have hexp : exp (σ * (∫ ξ in x₀..x, k ξ) * I) ≠ 0 := Complex.exp_ne_zero _
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (mul_ne_zero hσ0 Complex.I_ne_zero)
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 hkx0
    · exact (mul_eq_zero.1 h4).resolve_left hexp

/-- A function antitone on `(0, ∞)` with limit `0` at `0⁺` is nonpositive there. -/
theorem nonpos_of_tendsto_nhdsGT {f : ℝ → ℝ} (hanti : AntitoneOn f (Ioi 0))
    (hlim : Tendsto f (𝓝[>] 0) (𝓝 0)) {x : ℝ} (hx : 0 < x) : f x ≤ 0 :=
  ge_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT hx] with y hy
    exact hanti hy.1 hx hy.2.le)

/-- A function antitone on `(0, ∞)` with limit `0` at `∞` is nonnegative there. -/
theorem nonneg_of_tendsto_atTop {f : ℝ → ℝ} (hanti : AntitoneOn f (Ioi 0))
    (hlim : Tendsto f atTop (𝓝 0)) {x : ℝ} (hx : 0 < x) : 0 ≤ f x :=
  le_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hanti hx (lt_of_lt_of_le hx hy) hy)

/-- Separation at the horizon end: if `J[v] → 0` as `x ↓ 0`, then either
`Re (U_x Ū)(x₀) > 0` or `U = 0` on `(0, x₀)`. -/
theorem horizon_alternative {k : ℝ → ℝ} {U : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hk : ContDiffOn ℝ 2 k (Ioi 0)) (hkx : ∀ x ∈ Ioi (0 : ℝ), 0 < deriv k x)
    (hE : ∀ x ∈ Ioi (0 : ℝ), 0 < 2 * deriv k x ^ 2 - k x * deriv (deriv k) x)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x)
    (hk₀ : k x₀ = 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hlim : Tendsto (dephasedCurrent k (dephase k x₀ σ U)) (𝓝[>] 0) (𝓝 0)) :
    0 < (deriv U x₀ * (starRingEnd ℂ) (U x₀)).re ∨ ∀ x ∈ Ioo 0 x₀, U x = 0 := by
  have hanti := antitoneOn_current hx₀ hk hkx hE hU hk₀ hσ
  have hJ := (dephased_current k U x₀ hx₀ hk hkx hU hk₀ σ hσ).2
  rcases lt_or_ge (dephasedCurrent k (dephase k x₀ σ U) x₀) 0 with h | h
  · left
    linarith
  · right
    refine eqOn_zero_of_current_eq_zero hx₀ hk hkx hE hU hk₀ hσ le_rfl fun x hx => ?_
    have h1 : dephasedCurrent k (dephase k x₀ σ U) x₀ ≤
        dephasedCurrent k (dephase k x₀ σ U) x := hanti hx.1 hx₀ hx.2.le
    have h2 := nonpos_of_tendsto_nhdsGT hanti hlim hx.1
    linarith

/-- Separation at the infinity end: if `J[v] → 0` as `x → ∞`, then either
`Re (U_x Ū)(x₀) < 0` or `U = 0` on `(x₀, ∞)`. -/
theorem infinity_alternative {k : ℝ → ℝ} {U : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hk : ContDiffOn ℝ 2 k (Ioi 0)) (hkx : ∀ x ∈ Ioi (0 : ℝ), 0 < deriv k x)
    (hE : ∀ x ∈ Ioi (0 : ℝ), 0 < 2 * deriv k x ^ 2 - k x * deriv (deriv k) x)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((k x ^ 2 : ℝ) : ℂ) * U x) x)
    (hk₀ : k x₀ = 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hlim : Tendsto (dephasedCurrent k (dephase k x₀ σ U)) atTop (𝓝 0)) :
    (deriv U x₀ * (starRingEnd ℂ) (U x₀)).re < 0 ∨ ∀ x ∈ Ioi x₀, U x = 0 := by
  have hanti := antitoneOn_current hx₀ hk hkx hE hU hk₀ hσ
  have hJ := (dephased_current k U x₀ hx₀ hk hkx hU hk₀ σ hσ).2
  rcases lt_or_ge 0 (dephasedCurrent k (dephase k x₀ σ U) x₀) with h | h
  · left
    linarith
  · right
    intro x hx
    refine eqOn_zero_of_current_eq_zero hx₀ hk hkx hE hU hk₀ hσ hx₀.le (d := x + 1)
      (fun y hy => ?_) x ⟨hx, by linarith⟩
    have h1 : dephasedCurrent k (dephase k x₀ σ U) y ≤
        dephasedCurrent k (dephase k x₀ σ U) x₀ := hanti hx₀ (hx₀.trans hy.1) hy.1.le
    have h2 := nonneg_of_tendsto_atTop hanti hlim (hx₀.trans hy.1)
    linarith

end ModeStability.Corotation

end
