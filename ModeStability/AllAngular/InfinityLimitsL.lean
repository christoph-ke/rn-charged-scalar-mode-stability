module

public import ModeStability.AllAngular.InfinityLimitsLCore
public import ModeStability.AllAngular.InterfaceEndpointAux
public import ModeStability.AllAngular.AngularReduction
public import ModeStability.AllAngular.ConstantEndpointsAux

/-!
# The infinity limits of the current with angular term

Source: the all-angular research notes in preparation, Section 4, pp. 5–6: the infinity half of
the endpoint limits (4.4), `lim_{x → x_I} J[v_I] = 0`, including the interface expansion (4.5)
(`k̂_x = 2D/x³ + O(x⁻⁵)`, `D = ω(M² + 2Q²)/3 + L/(2ω)`), for the radial equation with angular term
`(ΔR')' + (K²/Δ − L)R = 0`, real `L ≥ 0`, and the outgoing condition (1.5) in Θ-form
(`R̃ = r e^{−iΘ} R`, `Θ' = K/Δ`, `R̃ − B = O(r⁻¹)`, `R̃' = O(r⁻²)`).

The current is stated in its phase-free form, with the minus sign at infinity (σ = −1):
`J = −(f/f_t)|U_t − ifU|² − Re(U_t Ū)`, which is the current `J[v_I]` of (4.2) for
`v_I = e^{−i∫f} U` by `dephasedCurrent_dephase_eq_on`. The coefficient `f` and amplitude `U` are
bound by their defining equations on the coordinate interval `(0, ∞)`:

* `reciprocal_infinity_current_tendsto_L` (`|Q| < M`, `c = 2Mω − e ≠ 0`): `x = 1/h → ∞`,
  `U(x) = x R(r(x))`, `f = k̂ = sgn(K) x⁻² √(K² − LΔ)`;
* `reciprocal_interface_current_tendsto_L` (`|Q| < M`, `c = 0`, the interface `r₀ = 2M`): same;
* `constant_infinity_current_tendsto_L` (`|Q| < M`): reflected `y = h ↓ 0`, `U(y) = R(r(y))`,
  `f = f̂ = −sgn(K)√(K² − LΔ)`;
* `extremal_reciprocal_infinity_current_tendsto_L` (`|Q| = M`, all `c`): `x = r − M → ∞`,
  `U(x) = x R(M + x)`, `k̂ = sgn(K) x⁻² √(K² − Lx²)`;
* `extremal_constant_infinity_current_tendsto_L` (`|Q| = M`): `y = 1/(r − M) ↓ 0`,
  `U(y) = R(M + 1/y)`, `f̂ = −sgn(K)√(K² − L/y²)`.

All five follow from the abstract-coordinate versions `il_reciprocal_current_tendsto` and
`il_constant_current_tendsto` (`ModeStability.AllAngular.InfinityLimitsLCore`). The coefficient
asymptotics are: for `c ≠ 0`, `gΔK' − 2K ~ −cr` (`k̂_x ~ C/x²`, `C = −c`); at `c = 0`,
`gΔK' − 2K → ℓ` with `ℓ = 2ω(M² + 2Q²)/3` (`iface_tendsto_staticSolution_mul_delta_mul_sub`), so
`k̂_x ~ (ωℓ + L)/(ωx³) = 2D/x³` with `ωℓ + L = 2ωD > 0` for every real `ω ≠ 0`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-! ### Subextremal gauge facts -/

/-- `r − g(r)Δ(r) → M` as `r → ∞` (subextremal static solution `g = h`). -/
theorem il_tendsto_sub_staticSolution_mul_delta {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (fun r => r - staticSolution M Q r * delta M Q r) atTop (𝓝 M) := by
  have h := (Infinity.tendsto_staticSolution_mul_delta_sub hQ).neg
  rw [neg_neg] at h
  exact h.congr fun r => by ring

/-- `y ↦ r(1/y)` tends to infinity as `y ↓ 0`. -/
theorem il_tendsto_radiusOf_one_div {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (fun y => radiusOf M Q (1 / y)) (𝓝[>] 0) atTop := by
  have hy : Tendsto (fun y : ℝ => 1 / y) (𝓝[>] 0) atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero
  exact (Infinity.tendsto_radiusOf_atTop hQ).comp hy

/-! ### Extremal gauge facts (`g = 1/(r − M)`, `Δ = (r − M)²`) -/

/-- `r/(r − M) → 1` as `r → ∞`. -/
theorem il_extremal_tendsto_mul (M : ℝ) :
    Tendsto (fun r : ℝ => r * (1 / (r - M))) atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x := M)).div_atTop
    (tendsto_atTop_add_const_right atTop (-M) tendsto_id)).const_add 1
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop M] with r hr
  have hr' : r - M ≠ 0 := (sub_pos.2 hr).ne'
  simp only [id, ← sub_eq_add_neg]
  field_simp
  ring

/-- `r − gΔ = M` for `r > M` in the extremal case. -/
theorem il_extremal_tendsto_sub {M Q : ℝ} (hQ : |Q| = M) :
    Tendsto (fun r => r - 1 / (r - M) * delta M Q r) atTop (𝓝 M) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop M] with r hr
  have hr' : r - M ≠ 0 := (sub_pos.2 hr).ne'
  rw [delta_of_abs_eq hQ]
  field_simp
  ring

/-- Extremal coefficient: `gS/N = O(1)` for all `c = 2Mω − e` (with `M > 0`, `ω ≠ 0`, `L ≥ 0`),
since `gΔK' − 2K = −c(r + M) + 2M²ω` exactly. -/
theorem il_extremal_coef_isBigO {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| = M) (hL : 0 ≤ L)
    (hω : ω ≠ 0) :
    (fun r => 1 / (r - M) * (radialK e ω r ^ 2 - L * delta M Q r) /
        (delta M Q r * radialK e ω r * (2 * ω * r - e) - L * delta M Q r * (r - M) -
          2 * (1 / (1 / (r - M))) * (radialK e ω r ^ 2 - L * delta M Q r)))
      =O[atTop] (fun _ => (1 : ℝ)) := by
  have hrg := il_extremal_tendsto_mul M
  have hid : ∀ r : ℝ, M < r → 1 / (r - M) * delta M Q r * (2 * ω * r - e) - 2 * radialK e ω r =
      -(2 * M * ω - e) * (r + M) + 2 * M ^ 2 * ω := by
    intro r hr
    have hr' : r - M ≠ 0 := (sub_pos.2 hr).ne'
    rw [delta_of_abs_eq hQ]
    unfold radialK
    field_simp
    ring
  by_cases hc : 2 * M * ω - e = 0
  · have hK : Tendsto (fun r => 1 / (r - M) * delta M Q r * (2 * ω * r - e) -
        2 * radialK e ω r) atTop (𝓝 (2 * M ^ 2 * ω)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop M] with r hr
      rw [hid r hr, hc]
      ring
    have hℓ : ω * (2 * M ^ 2 * ω) + L ≠ 0 := by
      have : 0 < ω * (2 * M ^ 2 * ω) := by
        have := pow_pos hM 2
        have : 0 < ω ^ 2 := by positivity
        nlinarith
      linarith
    exact (il_coef_tendsto_of_eq (g := fun r => 1 / (r - M)) hℓ hrg hK).isBigO_one ℝ
  · have hK : Tendsto (fun r => (1 / (r - M) * delta M Q r * (2 * ω * r - e) -
        2 * radialK e ω r) / r) atTop (𝓝 (-(2 * M * ω - e))) := by
      have h := (tendsto_const_nhds (x := -(2 * M * ω - e))).add
        ((tendsto_const_nhds (x := 2 * M ^ 2 * ω - (2 * M * ω - e) * M)).div_atTop tendsto_id)
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (max M 0)] with r hr
      have hrM : M < r := lt_of_le_of_lt (le_max_left _ _) hr
      have hr0 : r ≠ 0 := (lt_of_le_of_lt (le_max_right _ _) hr).ne'
      rw [hid r hrM]
      simp only [id]
      field_simp
      ring
    exact (il_coef_tendsto_of_ne (g := fun r => 1 / (r - M)) hω hc hrg hK).isBigO_one ℝ

/-! ### The five limits -/

/-- **Infinity limit, subextremal reciprocal normalization, `c ≠ 0`** (all-angular paper, (4.4),
p. 6, `C = e − 2Mω ≠ 0`). For `|Q| < M`, `L ≥ 0`, `ω ≠ 0`, `2Mω − e ≠ 0`, a solution `R` of the
radial equation with angular term and the outgoing condition (1.5) in Θ-form, the phase-free
current `J = −(k̂/k̂_x)|U' − ik̂U|² − Re(U'Ū)` of `U(x) = x R(r(x))`,
`k̂(x) = sgn(K) x⁻² √(K² − LΔ)` at `r = r(x)`, tends to `0` as `x → ∞`. -/
theorem reciprocal_infinity_current_tendsto_L {M Q e ω L : ℝ} (hQ : |Q| < M) (hL : 0 ≤ L)
    (hω : ω ≠ 0) (hc : 2 * M * ω - e ≠ 0)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - B) =O[atTop]
      (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹))
    {k : ℝ → ℝ}
    (hk : ∀ x ∈ Ioi (0 : ℝ), k x = (SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) *
      (1 / x) ^ 2 * Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)))
    {U : ℝ → ℂ} (hU : ∀ x ∈ Ioi (0 : ℝ), U x = (x : ℂ) * R (radiusOf M Q x)) :
    Tendsto (fun x => -(k x / deriv k x) *
        ‖deriv U x + ((-1 : ℝ) : ℂ) * (k x : ℂ) * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) atTop (𝓝 0) :=
  il_reciprocal_current_tendsto hL hω (fun _ hx => hasDerivAt_radiusOf hQ hx)
    (fun _ hx => staticSolution_radiusOf hQ hx) (Infinity.tendsto_radiusOf_atTop hQ)
    (Infinity.tendsto_mul_staticSolution hQ) (il_tendsto_sub_staticSolution_mul_delta hQ)
    ((il_coef_tendsto_of_ne hω hc (Infinity.tendsto_mul_staticSolution hQ)
      (Infinity.tendsto_staticSolution_mul_delta_mul_sub_div hQ e ω)).isBigO_one ℝ)
    hΘ hR hI1 hI2 hk hU

/-- **Infinity limit at the interface `r₀ = 2M`** (all-angular paper, (4.5), p. 6). For `|Q| < M`,
`L ≥ 0`, `ω ≠ 0` and `2Mω − e = 0`, with the same data as `reciprocal_infinity_current_tendsto_L`,
`J → 0` as `x → ∞`: here `k̂_x ~ 2D/x³` with `2ωD = 2ω²(M² + 2Q²)/3 + L > 0`. (The paper's
`D > 0` uses `ω > 0`; the limit only needs `ω ≠ 0`.) -/
theorem reciprocal_interface_current_tendsto_L {M Q e ω L : ℝ} (hQ : |Q| < M) (hL : 0 ≤ L)
    (hω : ω ≠ 0) (hc : 2 * M * ω - e = 0)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - B) =O[atTop]
      (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹))
    {k : ℝ → ℝ}
    (hk : ∀ x ∈ Ioi (0 : ℝ), k x = (SignType.sign (radialK e ω (radiusOf M Q x)) : ℝ) *
      (1 / x) ^ 2 * Real.sqrt (radialK e ω (radiusOf M Q x) ^ 2 - L * delta M Q (radiusOf M Q x)))
    {U : ℝ → ℂ} (hU : ∀ x ∈ Ioi (0 : ℝ), U x = (x : ℂ) * R (radiusOf M Q x)) :
    Tendsto (fun x => -(k x / deriv k x) *
        ‖deriv U x + ((-1 : ℝ) : ℂ) * (k x : ℂ) * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) atTop (𝓝 0) := by
  have hM : 0 < M := lt_of_le_of_lt (abs_nonneg Q) hQ
  have hℓ : ω * (2 * ω * ((M ^ 2 + 2 * Q ^ 2) / 3)) + L ≠ 0 := by
    have h1 : 0 < ω ^ 2 := by positivity
    have h2 : 0 < (M ^ 2 + 2 * Q ^ 2) / 3 := by positivity
    have : 0 < ω * (2 * ω * ((M ^ 2 + 2 * Q ^ 2) / 3)) := by nlinarith
    linarith
  exact il_reciprocal_current_tendsto hL hω (fun _ hx => hasDerivAt_radiusOf hQ hx)
    (fun _ hx => staticSolution_radiusOf hQ hx) (Infinity.tendsto_radiusOf_atTop hQ)
    (Infinity.tendsto_mul_staticSolution hQ) (il_tendsto_sub_staticSolution_mul_delta hQ)
    ((il_coef_tendsto_of_eq hℓ (Infinity.tendsto_mul_staticSolution hQ)
      (iface_tendsto_staticSolution_mul_delta_mul_sub hQ hc)).isBigO_one ℝ)
    hΘ hR hI1 hI2 hk hU

/-- **Infinity limit, subextremal constant normalization** (all-angular paper, (4.4), p. 5,
`J[v_I] = |B|²/(2r) + O(r⁻²)`). For `|Q| < M`, `L ≥ 0`, `ω ≠ 0`, a solution `R` with the outgoing
condition (1.5) in Θ-form, the phase-free current of `U(y) = R(r(y))`, `r(y) = r(1/y)`,
`f̂(y) = −sgn(K)√(K² − LΔ)` at `r = r(y)`, in the reflected coordinate `y = h`, tends to `0` as
`y ↓ 0`. -/
theorem constant_infinity_current_tendsto_L {M Q e ω L : ℝ} (hQ : |Q| < M) (hL : 0 ≤ L)
    (hω : ω ≠ 0)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - B) =O[atTop]
      (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹))
    {f : ℝ → ℝ}
    (hf : ∀ y ∈ Ioi (0 : ℝ), f y = -((SignType.sign (radialK e ω (radiusOf M Q (1 / y))) : ℝ) *
      Real.sqrt (radialK e ω (radiusOf M Q (1 / y)) ^ 2 -
        L * delta M Q (radiusOf M Q (1 / y)))))
    {U : ℝ → ℂ} (hU : ∀ y ∈ Ioi (0 : ℝ), U y = R (radiusOf M Q (1 / y))) :
    Tendsto (fun y => -(f y / deriv f y) *
        ‖deriv U y + ((-1 : ℝ) : ℂ) * (f y : ℂ) * I * U y‖ ^ 2 -
      (deriv U y * (starRingEnd ℂ) (U y)).re) (𝓝[>] 0) (𝓝 0) :=
  il_constant_current_tendsto (ρ := fun y => radiusOf M Q (1 / y)) hL hω
    (fun _ hy => cn_hasDerivAt_radius hQ hy) (il_tendsto_radiusOf_one_div hQ)
    hΘ hR hI1 hI2 hf hU

/-- **Infinity limit, extremal reciprocal normalization** (all-angular paper, (4.4)–(4.5), p. 6,
at extremality). For `M > 0`, `|Q| = M`, `L ≥ 0`, `ω ≠ 0` and every `e` (both `2Mω − e ≠ 0` and
the interface `2Mω − e = 0`), with `x = r − M`, `U(x) = x R(M + x)` and
`k̂(x) = sgn(K) x⁻² √(K² − Lx²)` at `r = M + x`, the phase-free current tends to `0` as
`x → ∞`. -/
theorem extremal_reciprocal_infinity_current_tendsto_L {M Q e ω L : ℝ} (hM : 0 < M)
    (hQ : |Q| = M) (hL : 0 ≤ L) (hω : ω ≠ 0)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - B) =O[atTop]
      (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹))
    {k : ℝ → ℝ}
    (hk : ∀ x ∈ Ioi (0 : ℝ), k x = (SignType.sign (radialK e ω (M + x)) : ℝ) * (1 / x) ^ 2 *
      Real.sqrt (radialK e ω (M + x) ^ 2 - L * x ^ 2))
    {U : ℝ → ℂ} (hU : ∀ x ∈ Ioi (0 : ℝ), U x = (x : ℂ) * R (M + x)) :
    Tendsto (fun x => -(k x / deriv k x) *
        ‖deriv U x + ((-1 : ℝ) : ℂ) * (k x : ℂ) * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re) atTop (𝓝 0) := by
  refine il_reciprocal_current_tendsto (ρ := fun t => M + t) (g := fun r => 1 / (r - M)) hL hω
    (fun x hx => ?_) (fun x hx => ?_) (tendsto_atTop_add_const_left atTop M tendsto_id)
    (il_extremal_tendsto_mul M) (il_extremal_tendsto_sub hQ)
    (il_extremal_coef_isBigO hM hQ hL hω) hΘ hR hI1 hI2 (fun x hx => ?_) hU
  · have hx0 : x ≠ 0 := (show (0 : ℝ) < x from hx).ne'
    refine ((hasDerivAt_id' x).const_add M).congr_deriv ?_
    rw [delta_of_abs_eq hQ, add_sub_cancel_left]
    field_simp
  · simp only [add_sub_cancel_left]
  · rw [hk x hx, delta_of_abs_eq hQ, add_sub_cancel_left]

/-- **Infinity limit, extremal constant normalization** (all-angular paper, (4.4), p. 5, at
extremality). For `|Q| = M`, `L ≥ 0`, `ω ≠ 0`, with `y = 1/(r − M)`, `U(y) = R(M + 1/y)` and
`f̂(y) = −sgn(K)√(K² − L/y²)` at `r = M + 1/y`, the phase-free current tends to `0` as `y ↓ 0`. -/
theorem extremal_constant_infinity_current_tendsto_L {M Q e ω L : ℝ} (hQ : |Q| = M) (hL : 0 ≤ L)
    (hω : ω ≠ 0)
    {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - B) =O[atTop]
      (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹))
    {f : ℝ → ℝ}
    (hf : ∀ y ∈ Ioi (0 : ℝ), f y = -((SignType.sign (radialK e ω (M + 1 / y)) : ℝ) *
      Real.sqrt (radialK e ω (M + 1 / y) ^ 2 - L / y ^ 2)))
    {U : ℝ → ℂ} (hU : ∀ y ∈ Ioi (0 : ℝ), U y = R (M + 1 / y)) :
    Tendsto (fun y => -(f y / deriv f y) *
        ‖deriv U y + ((-1 : ℝ) : ℂ) * (f y : ℂ) * I * U y‖ ^ 2 -
      (deriv U y * (starRingEnd ℂ) (U y)).re) (𝓝[>] 0) (𝓝 0) := by
  have hy : Tendsto (fun y : ℝ => 1 / y) (𝓝[>] 0) atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero
  refine il_constant_current_tendsto (ρ := fun y => M + 1 / y) hL hω (fun y hy => ?_)
    (tendsto_atTop_add_const_left _ M hy) hΘ hR hI1 hI2 (fun y hy => ?_) hU
  · have hy0 : y ≠ 0 := (show (0 : ℝ) < y from hy).ne'
    have hr : HasDerivAt (fun t : ℝ => M + 1 / t) (-(y ^ 2)⁻¹) y := by
      simpa only [one_div] using (hasDerivAt_inv hy0).const_add M
    refine hr.congr_deriv ?_
    rw [delta_of_abs_eq hQ, add_sub_cancel_left]
    field_simp
  · rw [hf y hy, delta_of_abs_eq hQ, add_sub_cancel_left, div_pow, one_pow, mul_one_div]

end ModeStability.AllAngular

end
