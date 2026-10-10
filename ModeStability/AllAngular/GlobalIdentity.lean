module

public import Mathlib
public import ModeStability.AllAngular.CurrentOnInterval
public import ModeStability.AllAngular.TurningPoint
public import ModeStability.ODE.Uniqueness

/-!
# The global positive identity (Section 5 of the all-angular paper)

Source: the all-angular research notes in preparation, Section 5, (5.1)–(5.3), pp. 6–7, with the
current (4.1)–(4.2) of Section 4, p. 5, and the turning-point matching (4.6), p. 6.

The paper glues one piecewise current (5.1) on the coordinate interval `(x_H, x_I)`: the
phase-free
form `−(k̂/k̂_x)|U_x ± ik̂U|² − Re(U_x Ū)` of (4.2) on the two allowed intervals `(x_H, x₁)`,
`(x₂, x_I)`, and `−Re(U_x Ū)` on the forbidden interval `[x₁, x₂]`. It is continuous at the
turning
points, vanishes at both physical endpoints and is nonincreasing, since `−J_x` is a sum of
nonnegative terms ((4.2) outside, (5.2) inside). Integration gives the identity (5.3). For `L > 0`
its middle term forces `U = 0` on `(x₁, x₂)`, hence everywhere by ODE uniqueness; for `L = 0`
(empty forbidden interval, `k̂ = k` through its simple zero `x₀`) the outer terms force `v_x = 0`
and then `U = 0` by (4.1).

Here everything is stated abstractly on the coordinate interval `(0, ∞)`: one physical endpoint is
`𝓝[>] 0`, the other `atTop` (which one is the horizon does not matter, both current limits are
`0`). Instead of integrating, the argument uses monotonicity of the currents and the squeeze
`m(x₂) ≤ m(x) ≤ m(x₁)` with `m = −Re(U_x Ū)`; this is the integrated identity (5.3) read through
the fundamental theorem of calculus, without improper integrals.

* `antitoneOn_phaseFree_current_on`, `eqOn_zero_of_phaseFree_current_const_on`: the phase-free
  current `−(f/f_x)|U_x + iσfU|² − Re(U_x Ū)` of (4.2) is antitone where `E_f/f_x² ≥ 0`, and if it
  is constant on an open set where `E_f/f_x² > 0`, then `U = 0` there.
* `le_of_antitoneOn_tendsto_of_le`, `le_of_antitoneOn_tendsto_of_ge`,
  `mem_Icc_of_antitoneOn_Ioo_tendsto`, `le_of_antitoneOn_Ioo_tendsto`,
  `mem_Icc_of_antitoneOn_Ioi_tendsto`, `le_of_antitoneOn_Ioi_tendsto`: an antitone function lies
  between its endpoint limits.
* `eqOn_zero_middle_of_global_current`, `eqOn_zero_of_global_current`: the case `L > 0`, from
  abstract outer currents; `U = 0` on the forbidden interval, and then on `(0, ∞)` by interior ODE
  uniqueness (`eqOn_zero_of_eqOn_zero_Ioo`, from `ModeStability.ODE.eqOn_zero_of_linear_ode`).
* `currents_eq_zero_of_global_current_L0`, `tendsto_phaseFree_current_at_zero`,
  `eqOn_zero_of_global_current_L0`: the case `L = 0`.
* `eqOn_zero_of_global_current_L`: the case `L > 0` with the outer currents built from
  `k̂ = s√F` and the turning-point limits (4.6).
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

/-! ### The phase-free current (4.2) on an open interval -/

/-- **Monotonicity of the phase-free current.** If `f` is `C²` on an open order-connected set `s`
with `f_x ≠ 0` and `E_f/f_x² ≥ 0` there, `U_xx = −f² U` on `s` and `σ = ±1`, then the current
`−(f/f_x)|U_x + iσfU|² − Re(U_x Ū)` of (4.2) is antitone on `s`. -/
theorem antitoneOn_phaseFree_current_on {f : ℝ → ℝ} {U : ℝ → ℂ} {s : Set ℝ} {σ : ℝ}
    (hs : IsOpen s) (hsc : s.OrdConnected) (hf : ContDiffOn ℝ 2 f s)
    (hfx : ∀ x ∈ s, deriv f x ≠ 0)
    (hE : ∀ x ∈ s, 0 ≤ (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2)
    (hσ : σ = 1 ∨ σ = -1)
    (hU : ∀ x ∈ s, DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((f x ^ 2 : ℝ) : ℂ) * U x) x) :
    AntitoneOn (fun x => -(f x / deriv f x) * ‖deriv U x + σ * f x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · intro a ha
    exact absurd ha (notMem_empty a)
  refine (antitoneOn_dephasedCurrent_on hs hsc hx₀ hf hfx hE hσ hU).congr fun x hx => ?_
  exact dephasedCurrent_dephase_eq_on hs hsc hx₀ hf.continuousOn σ hx (hU x hx).1

/-- **Rigidity of the phase-free current.** If the current `−(f/f_x)|U_x + iσfU|² − Re(U_x Ū)` is
constant on an open set `t ⊆ s` on which `f_x ≠ 0` and `E_f/f_x² > 0`, then `U = 0` on `t`. -/
theorem eqOn_zero_of_phaseFree_current_const_on {f : ℝ → ℝ} {U : ℝ → ℂ} {s t : Set ℝ}
    {σ C : ℝ} (hs : IsOpen s) (hsc : s.OrdConnected) (hf : ContDiffOn ℝ 2 f s)
    (hσ : σ = 1 ∨ σ = -1)
    (hU : ∀ x ∈ s, DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((f x ^ 2 : ℝ) : ℂ) * U x) x)
    (ht : IsOpen t) (hts : t ⊆ s) (hfx : ∀ x ∈ t, deriv f x ≠ 0)
    (hE : ∀ x ∈ t, 0 < (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2)
    (hJ : ∀ x ∈ t, -(f x / deriv f x) * ‖deriv U x + σ * f x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re = C) :
    ∀ x ∈ t, U x = 0 := by
  rcases t.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · intro x hx
    exact absurd hx (notMem_empty x)
  refine eqOn_zero_of_dephasedCurrent_const_on hs hsc (hts hx₀) hf hσ hU ht hts hfx hE
    (C := C) fun x hx => ?_
  rw [dephasedCurrent_dephase_eq_on hs hsc (hts hx₀) hf.continuousOn σ (hts hx)
    (hU x (hts hx)).1]
  exact hJ x hx

/-! ### An antitone function lies between its endpoint limits -/

/-- If `J` is antitone on `s`, `x ∈ s`, and `J → A` along a filter that eventually lies in `s`
to the left of `x`, then `J x ≤ A`. -/
theorem le_of_antitoneOn_tendsto_of_le {J : ℝ → ℝ} {s : Set ℝ} {l : Filter ℝ} [l.NeBot]
    {A x : ℝ} (hJ : AntitoneOn J s) (hx : x ∈ s) (hl : ∀ᶠ y in l, y ∈ s ∧ y ≤ x)
    (hA : Tendsto J l (𝓝 A)) : J x ≤ A :=
  ge_of_tendsto hA (hl.mono fun _ hy => hJ hy.1 hx hy.2)

/-- If `J` is antitone on `s`, `x ∈ s`, and `J → B` along a filter that eventually lies in `s`
to the right of `x`, then `B ≤ J x`. -/
theorem le_of_antitoneOn_tendsto_of_ge {J : ℝ → ℝ} {s : Set ℝ} {l : Filter ℝ} [l.NeBot]
    {B x : ℝ} (hJ : AntitoneOn J s) (hx : x ∈ s) (hl : ∀ᶠ y in l, y ∈ s ∧ x ≤ y)
    (hB : Tendsto J l (𝓝 B)) : B ≤ J x :=
  le_of_tendsto hB (hl.mono fun _ hy => hJ hx hy.1 hy.2)

/-- An antitone function on `(α, β)` with limits `A` at `α⁺` and `B` at `β⁻` takes its values in
`[B, A]`. -/
theorem mem_Icc_of_antitoneOn_Ioo_tendsto {J : ℝ → ℝ} {α β A B : ℝ}
    (hJ : AntitoneOn J (Ioo α β)) (hA : Tendsto J (𝓝[>] α) (𝓝 A))
    (hB : Tendsto J (𝓝[<] β) (𝓝 B)) {x : ℝ} (hx : x ∈ Ioo α β) : B ≤ J x ∧ J x ≤ A := by
  refine ⟨le_of_antitoneOn_tendsto_of_ge hJ hx ?_ hB, le_of_antitoneOn_tendsto_of_le hJ hx ?_ hA⟩
  · filter_upwards [Ioo_mem_nhdsLT hx.2] with y hy
    exact ⟨⟨hx.1.trans hy.1, hy.2⟩, hy.1.le⟩
  · filter_upwards [Ioo_mem_nhdsGT hx.1] with y hy
    exact ⟨⟨hy.1, hy.2.trans hx.2⟩, hy.2.le⟩

/-- An antitone function on `(α, β)`, `α < β`, with limits `A` at `α⁺` and `B` at `β⁻` has
`B ≤ A`. -/
theorem le_of_antitoneOn_Ioo_tendsto {J : ℝ → ℝ} {α β A B : ℝ} (hαβ : α < β)
    (hJ : AntitoneOn J (Ioo α β)) (hA : Tendsto J (𝓝[>] α) (𝓝 A))
    (hB : Tendsto J (𝓝[<] β) (𝓝 B)) : B ≤ A := by
  obtain ⟨x, hx⟩ := nonempty_Ioo.2 hαβ
  have h := mem_Icc_of_antitoneOn_Ioo_tendsto hJ hA hB hx
  exact h.1.trans h.2

/-- An antitone function on `(α, ∞)` with limits `A` at `α⁺` and `B` at `+∞` takes its values in
`[B, A]`. -/
theorem mem_Icc_of_antitoneOn_Ioi_tendsto {J : ℝ → ℝ} {α A B : ℝ}
    (hJ : AntitoneOn J (Ioi α)) (hA : Tendsto J (𝓝[>] α) (𝓝 A))
    (hB : Tendsto J atTop (𝓝 B)) {x : ℝ} (hx : x ∈ Ioi α) : B ≤ J x ∧ J x ≤ A := by
  refine ⟨le_of_antitoneOn_tendsto_of_ge hJ hx ?_ hB, le_of_antitoneOn_tendsto_of_le hJ hx ?_ hA⟩
  · filter_upwards [eventually_ge_atTop x] with y hy
    exact ⟨lt_of_lt_of_le hx hy, hy⟩
  · filter_upwards [Ioo_mem_nhdsGT (show α < x from hx)] with y hy
    exact ⟨hy.1, hy.2.le⟩

/-- An antitone function on `(α, ∞)` with limits `A` at `α⁺` and `B` at `+∞` has `B ≤ A`. -/
theorem le_of_antitoneOn_Ioi_tendsto {J : ℝ → ℝ} {α A B : ℝ}
    (hJ : AntitoneOn J (Ioi α)) (hA : Tendsto J (𝓝[>] α) (𝓝 A))
    (hB : Tendsto J atTop (𝓝 B)) : B ≤ A := by
  have h := mem_Icc_of_antitoneOn_Ioi_tendsto hJ hA hB (lt_add_one α)
  exact h.1.trans h.2

/-! ### The case `L > 0`: the forbidden interval -/

/-- The ODE `U_xx = −F U` in the form `U_xx = W U` with `W = −F`. -/
private theorem ga_ode_neg {U : ℝ → ℂ} {F : ℝ → ℝ} {x : ℝ}
    (h : HasDerivAt (deriv U) (-((F x : ℝ) : ℂ) * U x) x) :
    HasDerivAt (deriv U) ((((fun y => -F y) x : ℝ) : ℂ) * U x) x := by
  convert h using 1
  push_cast
  ring

/-- On the forbidden interval `[x₁, x₂]`, where `F ≤ 0`, the current `m = −Re(U_x Ū)` of (5.2) is
antitone on the closed interval. -/
private theorem ga_antitoneOn_Icc {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) {U : ℝ → ℂ} {F : ℝ → ℝ}
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((F x : ℝ) : ℂ) * U x) x)
    (hF : ∀ x ∈ Ioo x₁ x₂, F x < 0) :
    AntitoneOn (fun y => -(deriv U y * (starRingEnd ℂ) (U y)).re) (Icc x₁ x₂) := by
  have hpos : ∀ {y : ℝ}, y ∈ Icc x₁ x₂ → y ∈ Ioi (0 : ℝ) := fun hy => lt_of_lt_of_le hx₁ hy.1
  have h := fun {y : ℝ} (hy : y ∈ Icc x₁ x₂) =>
    hasDerivAt_neg_re_flux (W := fun y => -F y) (hU y (hpos hy)).1 (ga_ode_neg (hU y (hpos hy)).2)
  refine antitoneOn_of_deriv_nonpos (convex_Icc x₁ x₂) ?_ ?_ ?_
  · exact fun y hy => (h hy).continuousAt.continuousWithinAt
  · rw [interior_Icc]
    exact fun y hy => (h (Ioo_subset_Icc_self hy)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    rw [(h (Ioo_subset_Icc_self hy)).deriv, neg_nonpos]
    have : 0 ≤ -F y := by linarith [hF y hy]
    positivity

/-- **The global identity for `L > 0`, forbidden interval.** Let `U_xx = −F U` on `(0, ∞)` with
`F < 0` on the forbidden interval `(x₁, x₂)`, `0 < x₁ < x₂`, and let `m = −Re(U_x Ū)`. If outer
currents `J₁` on `(0, x₁)` and `J₂` on `(x₂, ∞)` are antitone, vanish at the physical endpoints
`0⁺` and `+∞`, and match `m` at the turning points (`J₁ → m(x₁)` from the left, `J₂ → m(x₂)` from
the right), then `U = 0` on `(x₁, x₂)`.

This is the middle term of (5.3): the glued current (5.1) is antitone and vanishes at both ends,
so it vanishes identically, and `−m_x = |U_x|² − F|U|²` with `−F > 0` forces `U = 0`. -/
theorem eqOn_zero_middle_of_global_current {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₁₂ : x₁ < x₂)
    {U : ℝ → ℂ} {F : ℝ → ℝ}
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((F x : ℝ) : ℂ) * U x) x)
    (hF : ∀ x ∈ Ioo x₁ x₂, F x < 0)
    {J₁ J₂ : ℝ → ℝ} (hJ₁ : AntitoneOn J₁ (Ioo 0 x₁)) (hJ₂ : AntitoneOn J₂ (Ioi x₂))
    (hJ₁0 : Tendsto J₁ (𝓝[>] 0) (𝓝 0)) (hJ₂0 : Tendsto J₂ atTop (𝓝 0))
    (hJ₁x : Tendsto J₁ (𝓝[<] x₁) (𝓝 (-(deriv U x₁ * (starRingEnd ℂ) (U x₁)).re)))
    (hJ₂x : Tendsto J₂ (𝓝[>] x₂) (𝓝 (-(deriv U x₂ * (starRingEnd ℂ) (U x₂)).re))) :
    ∀ x ∈ Ioo x₁ x₂, U x = 0 := by
  have hm := ga_antitoneOn_Icc hx₁ hU hF
  have h₁ : -(deriv U x₁ * (starRingEnd ℂ) (U x₁)).re ≤ 0 :=
    le_of_antitoneOn_Ioo_tendsto hx₁ hJ₁ hJ₁0 hJ₁x
  have h₂ : 0 ≤ -(deriv U x₂ * (starRingEnd ℂ) (U x₂)).re :=
    le_of_antitoneOn_Ioi_tendsto hJ₂ hJ₂x hJ₂0
  have hzero : ∀ x ∈ Ioo x₁ x₂, -(deriv U x * (starRingEnd ℂ) (U x)).re = 0 := by
    intro x hx
    have ha := hm (left_mem_Icc.2 hx₁₂.le) (Ioo_subset_Icc_self hx) hx.1.le
    have hb := hm (Ioo_subset_Icc_self hx) (right_mem_Icc.2 hx₁₂.le) hx.2.le
    simp only at ha hb
    linarith
  refine eqOn_zero_of_neg_re_flux_const_on (W := fun y => -F y) isOpen_Ioo
    (fun x hx => neg_pos.2 (hF x hx)) (fun x hx => ?_) hzero
  have hx0 : x ∈ Ioi (0 : ℝ) := hx₁.trans hx.1
  exact ⟨(hU x hx0).1, ga_ode_neg (hU x hx0).2⟩

/-- A solution of `U_xx = −F U` that vanishes on an open interval `(a, b) ⊆ (0, ∞)`, `a < b`,
vanishes on `(0, ∞)` (interior ODE uniqueness, `ModeStability.ODE.eqOn_zero_of_linear_ode`). -/
theorem eqOn_zero_of_eqOn_zero_Ioo {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {U : ℝ → ℂ}
    {F : ℝ → ℝ} (hFc : ContinuousOn F (Ioi 0))
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((F x : ℝ) : ℂ) * U x) x)
    (h0 : ∀ x ∈ Ioo a b, U x = 0) : ∀ x ∈ Ioi (0 : ℝ), U x = 0 := by
  set c := (a + b) / 2 with hc
  have hc_mem : c ∈ Ioo a b := ⟨by rw [hc]; linarith, by rw [hc]; linarith⟩
  have hev : U =ᶠ[𝓝 c] fun _ => (0 : ℂ) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hc_mem) h0
  refine ODE.eqOn_zero_of_linear_ode (p := fun _ => 1) (w := F) continuousOn_const
    (fun _ _ => one_pos) hFc (fun r hr => ⟨(hU r hr).1, ?_⟩)
    (show (0 : ℝ) < c from lt_of_le_of_lt ha hc_mem.1) (h0 c hc_mem) ?_
  · simp only [Complex.ofReal_one, one_mul]
    exact (hU r hr).2
  · rw [hev.deriv_eq, deriv_const]

/-- **The global identity for `L > 0`.** Under the hypotheses of
`eqOn_zero_middle_of_global_current`, and `F` continuous on `(0, ∞)`, `U = 0` on `(0, ∞)`: the
middle term of (5.3) forces `U = 0` on `(x₁, x₂)`, hence everywhere by ODE uniqueness. -/
theorem eqOn_zero_of_global_current {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₁₂ : x₁ < x₂)
    {U : ℝ → ℂ} {F : ℝ → ℝ} (hFc : ContinuousOn F (Ioi 0))
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((F x : ℝ) : ℂ) * U x) x)
    (hF : ∀ x ∈ Ioo x₁ x₂, F x < 0)
    {J₁ J₂ : ℝ → ℝ} (hJ₁ : AntitoneOn J₁ (Ioo 0 x₁)) (hJ₂ : AntitoneOn J₂ (Ioi x₂))
    (hJ₁0 : Tendsto J₁ (𝓝[>] 0) (𝓝 0)) (hJ₂0 : Tendsto J₂ atTop (𝓝 0))
    (hJ₁x : Tendsto J₁ (𝓝[<] x₁) (𝓝 (-(deriv U x₁ * (starRingEnd ℂ) (U x₁)).re)))
    (hJ₂x : Tendsto J₂ (𝓝[>] x₂) (𝓝 (-(deriv U x₂ * (starRingEnd ℂ) (U x₂)).re))) :
    ∀ x ∈ Ioi (0 : ℝ), U x = 0 :=
  eqOn_zero_of_eqOn_zero_Ioo hx₁.le hx₁₂ hFc hU
    (eqOn_zero_middle_of_global_current hx₁ hx₁₂ hU hF hJ₁ hJ₂ hJ₁0 hJ₂0 hJ₁x hJ₂x)

/-! ### The case `L = 0`: empty forbidden interval -/

/-- **The global identity for `L = 0`, currents.** If `J₁` is antitone on `(0, x₀)` and `J₂` on
`(x₀, ∞)`, both vanish at their physical endpoints (`0⁺`, `+∞`), and both tend to the same value
`c` at `x₀` (in the paper `c = −Re(U_x Ū)(x₀)`), then `c = 0` and both currents vanish
identically. -/
theorem currents_eq_zero_of_global_current_L0 {x₀ c : ℝ} (hx₀ : 0 < x₀) {J₁ J₂ : ℝ → ℝ}
    (hJ₁ : AntitoneOn J₁ (Ioo 0 x₀)) (hJ₂ : AntitoneOn J₂ (Ioi x₀))
    (hJ₁0 : Tendsto J₁ (𝓝[>] 0) (𝓝 0)) (hJ₂0 : Tendsto J₂ atTop (𝓝 0))
    (hJ₁x : Tendsto J₁ (𝓝[<] x₀) (𝓝 c)) (hJ₂x : Tendsto J₂ (𝓝[>] x₀) (𝓝 c)) :
    c = 0 ∧ (∀ x ∈ Ioo 0 x₀, J₁ x = 0) ∧ ∀ x ∈ Ioi x₀, J₂ x = 0 := by
  have h₁ : c ≤ 0 := le_of_antitoneOn_Ioo_tendsto hx₀ hJ₁ hJ₁0 hJ₁x
  have h₂ : 0 ≤ c := le_of_antitoneOn_Ioi_tendsto hJ₂ hJ₂x hJ₂0
  have hc : c = 0 := le_antisymm h₁ h₂
  refine ⟨hc, fun x hx => ?_, fun x hx => ?_⟩
  · have h := mem_Icc_of_antitoneOn_Ioo_tendsto hJ₁ hJ₁0 hJ₁x hx
    rw [hc] at h
    exact le_antisymm h.2 h.1
  · have h := mem_Icc_of_antitoneOn_Ioi_tendsto hJ₂ hJ₂x hJ₂0 hx
    rw [hc] at h
    exact le_antisymm h.2 h.1

/-- **Matching at a simple zero of `f` (`L = 0`).** If `f(x₀) = 0`, `f_x(x₀) ≠ 0`, and `f`, `f_x`,
`U`, `U_x` are continuous at `x₀`, then the phase-free current
`−(f/f_x)|U_x + iσfU|² − Re(U_x Ū)` tends to `−Re(U_x Ū)(x₀)` at `x₀` (from both sides). -/
theorem tendsto_phaseFree_current_at_zero {f : ℝ → ℝ} {U : ℝ → ℂ} {x₀ σ : ℝ}
    (hf : ContinuousAt f x₀) (hf' : ContinuousAt (deriv f) x₀) (hf0 : f x₀ = 0)
    (hf1 : deriv f x₀ ≠ 0) (hU : ContinuousAt U x₀) (hU' : ContinuousAt (deriv U) x₀) :
    Tendsto (fun x => -(f x / deriv f x) * ‖deriv U x + σ * f x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) (𝓝 x₀)
      (𝓝 (-(deriv U x₀ * (starRingEnd ℂ) (U x₀)).re)) := by
  have hfc : ContinuousAt (fun x => ((f x : ℝ) : ℂ)) x₀ :=
    Complex.continuous_ofReal.continuousAt.comp hf
  have hcont : ContinuousAt (fun x => -(f x / deriv f x) *
      ‖deriv U x + σ * f x * I * U x‖ ^ 2 - (deriv U x * (starRingEnd ℂ) (U x)).re) x₀ := by
    have hq : ContinuousAt (fun x => f x / deriv f x) x₀ := hf.div hf' hf1
    have hn : ContinuousAt (fun x => ‖deriv U x + σ * f x * I * U x‖ ^ 2) x₀ :=
      ((hU'.add (((continuousAt_const.mul hfc).mul continuousAt_const).mul hU)).norm).pow 2
    have hr : ContinuousAt (fun x => (deriv U x * (starRingEnd ℂ) (U x)).re) x₀ :=
      Complex.continuous_re.continuousAt.comp
        (hU'.mul (Complex.continuous_conj.continuousAt.comp hU))
    exact (hq.neg.mul hn).sub hr
  have h := hcont.tendsto
  simp only [hf0, zero_div, neg_zero, zero_mul, zero_sub] at h
  exact h

/-- **The global identity for `L = 0`.** Let `f` be `C²` on `(0, ∞)` with a zero `x₀ > 0`,
`f_x ≠ 0` and `E_f/f_x² > 0` on `(0, ∞)`, `U_xx = −f² U` on `(0, ∞)`, and `σ₁, σ₂ = ±1`. If the
phase-free currents `−(f/f_x)|U_x + iσⱼfU|² − Re(U_x Ū)` tend to `0` at the physical endpoints
(`σ₁` at `0⁺`, `σ₂` at `+∞`), then `U = 0` on `(0, ∞)`: the outer terms of (5.3) force `v_x = 0`,
and then (4.1) with `f_x ≠ 0` forces `U = 0`. -/
theorem eqOn_zero_of_global_current_L0 {f : ℝ → ℝ} {U : ℝ → ℂ} {x₀ σ₁ σ₂ : ℝ} (hx₀ : 0 < x₀)
    (hf : ContDiffOn ℝ 2 f (Ioi 0)) (hf0 : f x₀ = 0)
    (hfx : ∀ x ∈ Ioi (0 : ℝ), deriv f x ≠ 0)
    (hE : ∀ x ∈ Ioi (0 : ℝ), 0 < (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2)
    (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((f x ^ 2 : ℝ) : ℂ) * U x) x)
    (hJ₁ : Tendsto (fun x => -(f x / deriv f x) * ‖deriv U x + σ₁ * f x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) (𝓝[>] 0) (𝓝 0))
    (hJ₂ : Tendsto (fun x => -(f x / deriv f x) * ‖deriv U x + σ₂ * f x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) atTop (𝓝 0)) :
    ∀ x ∈ Ioi (0 : ℝ), U x = 0 := by
  have hE' : ∀ x ∈ Ioi (0 : ℝ),
      0 ≤ (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2 :=
    fun x hx => (hE x hx).le
  have hA₁ := antitoneOn_phaseFree_current_on isOpen_Ioi ordConnected_Ioi hf hfx hE' hσ₁ hU
  have hA₂ := antitoneOn_phaseFree_current_on isOpen_Ioi ordConnected_Ioi hf hfx hE' hσ₂ hU
  have hfc : ContinuousAt f x₀ := hf.continuousOn.continuousAt (Ioi_mem_nhds hx₀)
  have hf'c : ContinuousAt (deriv f) x₀ :=
    (differentiableAt_deriv_of_contDiffOn_on isOpen_Ioi hf hx₀).continuousAt
  have hUc : ContinuousAt U x₀ := (hU x₀ hx₀).1.continuousAt
  have hU'c : ContinuousAt (deriv U) x₀ := (hU x₀ hx₀).2.continuousAt
  have hT₁ := (tendsto_phaseFree_current_at_zero (σ := σ₁) hfc hf'c hf0 (hfx x₀ hx₀) hUc
    hU'c).mono_left (nhdsWithin_le_nhds (s := Iio x₀))
  have hT₂ := (tendsto_phaseFree_current_at_zero (σ := σ₂) hfc hf'c hf0 (hfx x₀ hx₀) hUc
    hU'c).mono_left (nhdsWithin_le_nhds (s := Ioi x₀))
  obtain ⟨-, hz₁, hz₂⟩ := currents_eq_zero_of_global_current_L0 hx₀
    (hA₁.mono Ioo_subset_Ioi_self) (hA₂.mono (Ioi_subset_Ioi hx₀.le)) hJ₁ hJ₂ hT₁ hT₂
  have hl : ∀ x ∈ Ioo 0 x₀, U x = 0 :=
    eqOn_zero_of_phaseFree_current_const_on isOpen_Ioi ordConnected_Ioi hf hσ₁ hU isOpen_Ioo
      Ioo_subset_Ioi_self (fun x hx => hfx x hx.1) (fun x hx => hE x hx.1) hz₁
  have hr : ∀ x ∈ Ioi x₀, U x = 0 :=
    eqOn_zero_of_phaseFree_current_const_on isOpen_Ioi ordConnected_Ioi hf hσ₂ hU isOpen_Ioi
      (Ioi_subset_Ioi hx₀.le) (fun x hx => hfx x (hx₀.trans hx))
      (fun x hx => hE x (hx₀.trans hx)) hz₂
  intro x hx
  rcases lt_trichotomy x x₀ with h | rfl | h
  · exact hl x ⟨hx, h⟩
  · have hlim : Tendsto U (𝓝[>] x) (𝓝 0) :=
      tendsto_const_nhds.congr' (Filter.eventually_of_mem self_mem_nhdsWithin
        fun y hy => (hr y hy).symm)
    exact tendsto_nhds_unique (hUc.tendsto.mono_left nhdsWithin_le_nhds) hlim
  · exact hr x h

/-! ### The case `L > 0` with the outer currents built from `k̂ = s√F` -/

/-- A solution of `U_xx = G` on `(0, ∞)` (pointwise, with `U` differentiable) is `C¹` at every
point of `(0, ∞)`. -/
private theorem ga_contDiffAt_one {U : ℝ → ℂ} {G : ℝ → ℂ}
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧ HasDerivAt (deriv U) (G x) x)
    {x : ℝ} (hx : 0 < x) : ContDiffAt ℝ 1 U x := by
  have h : ContDiffOn ℝ (0 + 1) U (Ioi 0) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy => (hU y hy).1.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact fun y hy => (hU y hy).2.continuousAt.continuousWithinAt
  rw [zero_add] at h
  exact h.contDiffAt (Ioi_mem_nhds hx)

/-- On an allowed interval `t` (open, order-connected, `F > 0` there) with `f = s√F` on `t`, the
phase-free current of `f` is antitone on `t` and agrees there with the current of `s√F` used in
`tendsto_current_at_turning_point_left`/`_right`. -/
private theorem ga_outer {t : Set ℝ} (ht : IsOpen t) (htc : t.OrdConnected) (ht0 : t ⊆ Ioi 0)
    {U : ℝ → ℂ} {F f : ℝ → ℝ} {s σ : ℝ} (hF : ContDiffOn ℝ 2 F (Ioi 0))
    (hFpos : ∀ x ∈ t, 0 < F x)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((F x : ℝ) : ℂ) * U x) x)
    (hs : s = 1 ∨ s = -1) (hf : ∀ x ∈ t, f x = s * Real.sqrt (F x))
    (hfx : ∀ x ∈ t, deriv f x ≠ 0)
    (hE : ∀ x ∈ t, 0 ≤ (2 * deriv f x ^ 2 - f x * deriv (deriv f) x) / deriv f x ^ 2)
    (hσ : σ = 1 ∨ σ = -1) :
    AntitoneOn (fun x => -(f x / deriv f x) * ‖deriv U x + σ * f x * I * U x‖ ^ 2 -
        (deriv U x * (starRingEnd ℂ) (U x)).re) t ∧
      ∀ x ∈ t, -(f x / deriv f x) * ‖deriv U x + σ * f x * I * U x‖ ^ 2 -
          (deriv U x * (starRingEnd ℂ) (U x)).re =
        -((s * Real.sqrt (F x)) / deriv (fun y => s * Real.sqrt (F y)) x) *
          ‖deriv U x + σ * (s * Real.sqrt (F x)) * I * U x‖ ^ 2 -
            (deriv U x * (starRingEnd ℂ) (U x)).re := by
  have hs2 : s ^ 2 = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  have hsq : ∀ x ∈ t, f x ^ 2 = F x := by
    intro x hx
    rw [hf x hx, mul_pow, hs2, one_mul, Real.sq_sqrt (hFpos x hx).le]
  have hUt : ∀ x ∈ t, DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((f x ^ 2 : ℝ) : ℂ) * U x) x := by
    intro x hx
    rw [hsq x hx]
    exact hU x (ht0 hx)
  have hfc : ContDiffOn ℝ 2 f t :=
    (contDiffOn_const.mul ((hF.mono ht0).sqrt fun x hx => (hFpos x hx).ne')).congr hf
  refine ⟨antitoneOn_phaseFree_current_on ht htc hfc hfx hE hσ hUt, fun x hx => ?_⟩
  have hev : f =ᶠ[𝓝 x] fun y => s * Real.sqrt (F y) :=
    Filter.eventually_of_mem (ht.mem_nhds hx) hf
  rw [hev.deriv_eq, hf x hx, Complex.ofReal_mul]

/-- **The global identity for `L > 0`, with the turning-point matching (4.6).** Let `F` be `C²` on
`(0, ∞)`, positive on the allowed intervals `(0, x₁)` and `(x₂, ∞)`, negative on the forbidden
interval `(x₁, x₂)`, with simple zeros at the turning points (`F'(x₁) ≠ 0`, `F'(x₂) ≠ 0`), and let
`U_xx = −F U` on `(0, ∞)`. On the allowed intervals let `f₁ = s₁√F`, `f₂ = s₂√F` (`s_j = ±1`, the
sign of `K` in the paper), with `f_x ≠ 0` and `E_f/f_x² ≥ 0` there. If the phase-free currents
`−(f_j/f_{j,x})|U_x + iσⱼf_jU|² − Re(U_x Ū)` (`σⱼ = ±1`) tend to `0` at the physical endpoints
`0⁺` and `+∞`, then `U = 0` on `(0, ∞)`. -/
theorem eqOn_zero_of_global_current_L {x₁ x₂ s₁ s₂ σ₁ σ₂ : ℝ} (hx₁ : 0 < x₁) (hx₁₂ : x₁ < x₂)
    {U : ℝ → ℂ} {F f₁ f₂ : ℝ → ℝ} (hF : ContDiffOn ℝ 2 F (Ioi 0))
    (hF₁ : ∀ x ∈ Ioo 0 x₁, 0 < F x) (hFm : ∀ x ∈ Ioo x₁ x₂, F x < 0)
    (hF₂ : ∀ x ∈ Ioi x₂, 0 < F x) (hdF₁ : deriv F x₁ ≠ 0) (hdF₂ : deriv F x₂ ≠ 0)
    (hU : ∀ x ∈ Ioi (0 : ℝ), DifferentiableAt ℝ U x ∧
      HasDerivAt (deriv U) (-((F x : ℝ) : ℂ) * U x) x)
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
    ∀ x ∈ Ioi (0 : ℝ), U x = 0 := by
  have hx₂ : 0 < x₂ := hx₁.trans hx₁₂
  have hFc₁ : ContinuousAt F x₁ := hF.continuousOn.continuousAt (Ioi_mem_nhds hx₁)
  have hFc₂ : ContinuousAt F x₂ := hF.continuousOn.continuousAt (Ioi_mem_nhds hx₂)
  have hd₁ : HasDerivAt F (deriv F x₁) x₁ :=
    (hF.contDiffAt (Ioi_mem_nhds hx₁)).differentiableAt (by norm_num) |>.hasDerivAt
  have hd₂ : HasDerivAt F (deriv F x₂) x₂ :=
    (hF.contDiffAt (Ioi_mem_nhds hx₂)).differentiableAt (by norm_num) |>.hasDerivAt
  -- the turning points are zeros of `F`
  have hF₁0 : F x₁ = 0 := by
    refine le_antisymm ?_ ?_
    · refine le_of_tendsto (hFc₁.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi x₁))) ?_
      filter_upwards [Ioo_mem_nhdsGT hx₁₂] with y hy
      exact (hFm y hy).le
    · refine ge_of_tendsto (hFc₁.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio x₁))) ?_
      filter_upwards [Ioo_mem_nhdsLT hx₁] with y hy
      exact (hF₁ y hy).le
  have hF₂0 : F x₂ = 0 := by
    refine le_antisymm ?_ ?_
    · refine le_of_tendsto (hFc₂.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio x₂))) ?_
      filter_upwards [Ioo_mem_nhdsLT hx₁₂] with y hy
      exact (hFm y hy).le
    · refine ge_of_tendsto (hFc₂.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi x₂))) ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hF₂ y hy).le
  -- the signs of `F'` at the turning points
  have hdF₁' : deriv F x₁ < 0 := by
    refine lt_of_le_of_ne (not_lt.1 fun h => ?_) hdF₁
    obtain ⟨y, hy, hy'⟩ := ((eventually_pos_right_of_deriv_pos hd₁ hF₁0 h).and
      (Ioo_mem_nhdsGT hx₁₂)).exists
    exact absurd (hFm y hy') (not_lt.2 hy.le)
  have hdF₂' : 0 < deriv F x₂ := by
    refine lt_of_le_of_ne (not_lt.1 fun h => ?_) hdF₂.symm
    obtain ⟨y, hy, hy'⟩ := ((eventually_pos_left_of_deriv_neg hd₂ hF₂0 h).and
      (Ioo_mem_nhdsLT hx₁₂)).exists
    exact absurd (hFm y hy') (not_lt.2 hy.le)
  obtain ⟨hA₁, he₁⟩ := ga_outer (σ := σ₁) isOpen_Ioo ordConnected_Ioo Ioo_subset_Ioi_self hF hF₁
    hU hs₁ hf₁ hf₁x hE₁ hσ₁
  obtain ⟨hA₂, he₂⟩ := ga_outer (σ := σ₂) isOpen_Ioi ordConnected_Ioi (Ioi_subset_Ioi hx₂.le) hF
    hF₂ hU hs₂ hf₂ hf₂x hE₂ hσ₂
  have hT₁ := tendsto_current_at_turning_point_left (σ := σ₁) hs₁
    (hF.contDiffAt (Ioi_mem_nhds hx₁)) hF₁0 hdF₁' (ga_contDiffAt_one hU hx₁)
  have hT₂ := tendsto_current_at_turning_point_right (σ := σ₂) hs₂
    (hF.contDiffAt (Ioi_mem_nhds hx₂)) hF₂0 hdF₂' (ga_contDiffAt_one hU hx₂)
  refine eqOn_zero_of_global_current hx₁ hx₁₂ hF.continuousOn hU hFm hA₁ hA₂ hJ₁ hJ₂
    (hT₁.congr' ?_) (hT₂.congr' ?_)
  · filter_upwards [Ioo_mem_nhdsLT hx₁] with y hy
    exact (he₁ y hy).symm
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (he₂ y hy).symm

end ModeStability.AllAngular

end
