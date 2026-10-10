module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.ODE.Uniqueness
public import ModeStability.AllAngular.InfinityUniquenessAux
public import ModeStability.AllAngular.InfinityUniqueness
public import ModeStability.AllAngular.HorizonUniquenessAux

/-!
# Uniqueness at the horizon

Source: the all-angular research notes in preparation, p. 2. The paper asserts this without
proof. The infinity half
is `eqOn_zero_of_outgoing_coefficient_zero`. Here the horizon half is proved: a solution of the
radial equation `(ΔR')' + (K²/Δ − L)R = 0` on `r > a` whose ingoing profile `R̃ = e^{iΘ}R`
(`Θ' = K/Δ`) satisfies the horizon condition (1.4) with vanishing leading coefficient `B_H = 0`,
i.e. `R̃ = O(r − a)` and `R̃' = O(1)`, vanishes identically
(`eqOn_zero_of_horizon_coefficient_zero`), provided `K(a) ≠ 0`. This covers the subextremal
(`|Q| < M`, regular singular) and the extremal (`|Q| = M`, irregular singular) horizon at once.

## Proof

With `P = ΔR'` the horizon amplitudes `A = e^{−iΘ}(P + iKR)` and `B = e^{iΘ}(P − iKR)` satisfy,
by `P' = −(K²/Δ − L)R` and `Θ' = K/Δ`,
`A' = e^{−iΘ}(L + iK')R` and `B' = e^{iΘ}(L − iK')R`: the singular terms `±iKR'` and `K²R/Δ`
cancel exactly. Since `2iKR = e^{iΘ}A − e^{−iΘ}B` and `K(a) ≠ 0`, near the horizon
`|A'|, |B'| ≤ C(|A| + |B|)` with a bounded `C`. No factor `1/Δ` survives, so the estimate
loses nothing at the irregular extremal horizon `Δ = (r − M)²`. On the other hand
`ΔR̃' = e^{iΘ}(P + iKR)`, so `|A| = Δ|R̃'|` and `B = ΔR̃' − 2iKR̃`; hence `R̃ → 0` and
`ΔR̃' → 0` as `r ↓ a` (which follow from `R̃ = O(r − a)`, `R̃' = O(1)`) give `A, B → 0`.
The forward Grönwall argument from the horizon (`hu_eq_zero_of_norm_deriv_le`) gives
`A = B = 0` at some `r₁ > a`, so `R(r₁) = R'(r₁) = 0`, and interior uniqueness
(`ModeStability.ODE.eqOn_zero_of_linear_ode`) gives `R ≡ 0` on `r > a`.

The general form `eqOn_zero_of_horizon_tendsto_profile` only uses `R̃ → 0` and `ΔR̃' → 0`;
`eqOn_zero_of_horizon_tendsto_zero` uses `R̃ → 0` and `R̃' = O(1)`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

open InfinityUniqueness

/-! ### The horizon amplitudes -/

/-- The horizon amplitude `A = e^{−iΘ}(ΔR' + iKR)`; `|A| = Δ|R̃'|` for `R̃ = e^{iΘ}R`. -/
@[expose] noncomputable def hu_ampOut (M Q e ω : ℝ) (Θ : ℝ → ℝ) (R : ℝ → ℂ) (r : ℝ) : ℂ :=
  exp (-(I * Θ r)) * ((delta M Q r : ℂ) * deriv R r + I * radialK e ω r * R r)

/-- The horizon amplitude `B = e^{iΘ}(ΔR' − iKR) = ΔR̃' − 2iKR̃` for `R̃ = e^{iΘ}R`. -/
@[expose] noncomputable def hu_ampIn (M Q e ω : ℝ) (Θ : ℝ → ℝ) (R : ℝ → ℂ) (r : ℝ) : ℂ :=
  exp (I * Θ r) * ((delta M Q r : ℂ) * deriv R r - I * radialK e ω r * R r)

variable {M Q e ω L : ℝ} {Θ : ℝ → ℝ} {R : ℝ → ℂ}

/-- `‖x + iy‖ ≤ |x| + |y|`. -/
theorem hu_norm_add_I_mul_le (x y : ℝ) : ‖(x : ℂ) + I * y‖ ≤ |x| + |y| := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

/-- `‖x − iy‖ ≤ |x| + |y|`. -/
theorem hu_norm_sub_I_mul_le (x y : ℝ) : ‖(x : ℂ) - I * y‖ ≤ |x| + |y| := by
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

/-- `e^{ix} e^{−ix} = 1`. -/
theorem hu_exp_I_mul_mul_exp_neg_I_mul (x : ℝ) : exp (I * x) * exp (-(I * x)) = 1 := by
  rw [mul_comm]
  exact exp_neg_I_mul_mul_exp_I_mul x

/-- The derivative of `A`: `A' = e^{−iΘ}(L + iK')R`. -/
theorem hu_hasDerivAt_ampOut {r : ℝ} (hΔ : delta M Q r ≠ 0)
    (hΘ : HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : DifferentiableAt ℝ R r ∧ HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    HasDerivAt (hu_ampOut M Q e ω Θ R)
      (exp (-(I * Θ r)) * (((L : ℂ) + I * ((2 * ω * r - e : ℝ) : ℂ)) * R r)) r := by
  have hE := hasDerivAt_exp_neg_phase (M := M) (Q := Q) hΘ
  have hK : HasDerivAt (fun s => (radialK e ω s : ℂ)) ((2 * ω * r - e : ℝ) : ℂ) r :=
    (hasDerivAt_radialK e ω r).ofReal_comp
  have h := hE.mul (hR.2.add ((hK.const_mul I).mul hR.1.hasDerivAt))
  refine h.congr_deriv ?_
  have hc : (radialK e ω r : ℂ) / delta M Q r * delta M Q r = radialK e ω r :=
    div_mul_cancel₀ _ (ofReal_ne_zero.2 hΔ)
  simp only [Pi.mul_apply, Pi.add_apply, phaseRate]
  push_cast
  linear_combination (-(exp (-(I * Θ r))) * I * deriv R r) * hc +
    (-(exp (-(I * Θ r))) * (radialK e ω r : ℂ) ^ 2 / delta M Q r * R r) * I_sq

/-- The derivative of `B`: `B' = e^{iΘ}(L − iK')R`. -/
theorem hu_hasDerivAt_ampIn {r : ℝ} (hΔ : delta M Q r ≠ 0)
    (hΘ : HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : DifferentiableAt ℝ R r ∧ HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    HasDerivAt (hu_ampIn M Q e ω Θ R)
      (exp (I * Θ r) * (((L : ℂ) - I * ((2 * ω * r - e : ℝ) : ℂ)) * R r)) r := by
  have hE := hasDerivAt_exp_phase (M := M) (Q := Q) hΘ
  have hK : HasDerivAt (fun s => (radialK e ω s : ℂ)) ((2 * ω * r - e : ℝ) : ℂ) r :=
    (hasDerivAt_radialK e ω r).ofReal_comp
  have h := hE.mul (hR.2.sub ((hK.const_mul I).mul hR.1.hasDerivAt))
  refine h.congr_deriv ?_
  have hc : (radialK e ω r : ℂ) / delta M Q r * delta M Q r = radialK e ω r :=
    div_mul_cancel₀ _ (ofReal_ne_zero.2 hΔ)
  simp only [Pi.mul_apply, Pi.sub_apply, phaseRate]
  push_cast
  linear_combination (exp (I * Θ r) * I * deriv R r) * hc +
    (-(exp (I * Θ r)) * (radialK e ω r : ℂ) ^ 2 / delta M Q r * R r) * I_sq

/-- The ingoing profile `R̃ = e^{iΘ}R` satisfies `ΔR̃' = e^{iΘ}(ΔR' + iKR)`. -/
theorem hu_delta_mul_deriv_profile {r : ℝ} (hΔ : delta M Q r ≠ 0)
    (hΘ : HasDerivAt Θ (radialK e ω r / delta M Q r) r) (hR : DifferentiableAt ℝ R r) :
    (delta M Q r : ℂ) * deriv (fun s : ℝ => exp (I * (Θ s : ℂ)) * R s) r =
      exp (I * Θ r) * ((delta M Q r : ℂ) * deriv R r + I * radialK e ω r * R r) := by
  have h : HasDerivAt (fun s : ℝ => exp (I * (Θ s : ℂ)) * R s)
      (exp (I * Θ r) * (I * phaseRate M Q e ω r) * R r + exp (I * Θ r) * deriv R r) r :=
    (hasDerivAt_exp_phase (M := M) (Q := Q) hΘ).mul hR.hasDerivAt
  rw [h.deriv]
  have hc : (radialK e ω r : ℂ) / delta M Q r * delta M Q r = radialK e ω r :=
    div_mul_cancel₀ _ (ofReal_ne_zero.2 hΔ)
  simp only [phaseRate]
  push_cast
  linear_combination (exp (I * Θ r) * I * R r) * hc

/-- Under `R̃ → 0` and `ΔR̃' → 0` as `r ↓ a`, both horizon amplitudes tend to `0`. -/
theorem hu_tendsto_amps
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    (h1 : Tendsto (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (h2 : Tendsto (fun r : ℝ =>
        (delta M Q r : ℂ) * deriv (fun s : ℝ => exp (I * (Θ s : ℂ)) * R s) r)
      (𝓝[>] (outerHorizon M Q)) (𝓝 0)) :
    Tendsto (hu_ampOut M Q e ω Θ R) (𝓝[>] (outerHorizon M Q)) (𝓝 0) ∧
      Tendsto (hu_ampIn M Q e ω Θ R) (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
  have hderiv : ∀ r ∈ Ioi (outerHorizon M Q),
      (delta M Q r : ℂ) * deriv (fun s : ℝ => exp (I * (Θ s : ℂ)) * R s) r =
        exp (I * Θ r) * ((delta M Q r : ℂ) * deriv R r + I * radialK e ω r * R r) :=
    fun r hr => hu_delta_mul_deriv_profile (delta_pos_of_lt hr).ne' (hΘ r hr) (hR r hr)
  have hKc : Continuous (fun r => (radialK e ω r : ℂ)) := by
    unfold radialK
    fun_prop
  have hKt : Tendsto (fun r => (radialK e ω r : ℂ)) (𝓝[>] (outerHorizon M Q))
      (𝓝 (radialK e ω (outerHorizon M Q) : ℂ)) :=
    (hKc.tendsto _).mono_left nhdsWithin_le_nhds
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := h2.norm
    rw [norm_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [hderiv r hr]
    simp only [hu_ampOut, norm_mul, norm_exp_neg_I_mul, norm_exp_I_mul]
  · have h := h2.sub (((tendsto_const_nhds (x := 2 * I)).mul hKt).mul h1)
    rw [mul_zero, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [hderiv r hr]
    simp only [hu_ampIn]
    ring

/-! ### Uniqueness at the horizon -/

/-- **Uniqueness at the horizon**, general form. A solution of the radial equation
`(ΔR')' + (K²/Δ − L)R = 0` on `r > a` (`Θ' = K/Δ`, `K(a) ≠ 0`) whose ingoing profile
`R̃ = e^{iΘ}R` satisfies `R̃ → 0` and `ΔR̃' → 0` as `r ↓ a` vanishes identically. -/
theorem eqOn_zero_of_horizon_tendsto_profile {M Q e ω L : ℝ}
    (hK : radialK e ω (outerHorizon M Q) ≠ 0) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (h1 : Tendsto (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (h2 : Tendsto (fun r : ℝ =>
        (delta M Q r : ℂ) * deriv (fun s : ℝ => exp (I * (Θ s : ℂ)) * R s) r)
      (𝓝[>] (outerHorizon M Q)) (𝓝 0)) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  set a := outerHorizon M Q with ha
  obtain ⟨hlo, hli⟩ := hu_tendsto_amps hΘ (fun r hr => (hR r hr).1) h1 h2
  -- the error coefficient `(|L| + |K'|)/(2|K|)` is bounded near the horizon
  set c : ℝ → ℝ := fun r => (|L| + |2 * ω * r - e|) / (2 * |radialK e ω r|) with hcdef
  have hKcont : Continuous (radialK e ω) := by
    unfold radialK
    fun_prop
  have hcc : ContinuousAt c a := by
    refine ContinuousAt.div (by fun_prop) (continuous_const.mul hKcont.abs).continuousAt ?_
    exact mul_ne_zero two_ne_zero (abs_ne_zero.2 hK)
  set C : ℝ := c a + 1 with hCdef
  have hC1 : 1 ≤ C := by
    have : 0 ≤ c a := div_nonneg (by positivity) (by positivity)
    linarith
  have hev1 : ∀ᶠ r in 𝓝[>] a, c r ≤ C :=
    (hcc.tendsto.eventually (eventually_le_nhds (lt_add_one (c a)))).filter_mono
      nhdsWithin_le_nhds
  have hev2 : ∀ᶠ r in 𝓝[>] a, radialK e ω r ≠ 0 :=
    (hKcont.continuousAt.eventually_ne hK).filter_mono nhdsWithin_le_nhds
  have hev3 : ∀ᶠ r in 𝓝[>] a, ‖hu_ampOut M Q e ω Θ R r‖ + ‖hu_ampIn M Q e ω Θ R r‖ ≤ 1 := by
    have h := hlo.norm.add hli.norm
    rw [norm_zero, add_zero] at h
    exact h.eventually_le_const zero_lt_one
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hev1.and (hev2.and (hev3.and (self_mem_nhdsWithin (s := Ioi a) (a := a)))))
  have hua : 0 < u - a := sub_pos.2 hu
  set η : ℝ := min ((u - a) / 2) (1 / (4 * C)) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by positivity)
  have hηu : η ≤ (u - a) / 2 := min_le_left _ _
  have hηC : 4 * C * η ≤ 1 := by
    have h := min_le_right ((u - a) / 2) (1 / (4 * C))
    rw [← hη] at h
    calc 4 * C * η ≤ 4 * C * (1 / (4 * C)) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 1 := by field_simp
  set b : ℝ := a + η with hb
  have hab : a < b := by linarith
  have hgood : ∀ t ∈ Ioc a b, c t ≤ C ∧ radialK e ω t ≠ 0 ∧
      ‖hu_ampOut M Q e ω Θ R t‖ + ‖hu_ampIn M Q e ω Θ R t‖ ≤ 1 ∧ t ∈ Ioi a :=
    fun t ht => hsub ⟨ht.1, by linarith [ht.2]⟩
  have hΔ : ∀ t ∈ Ioc a b, delta M Q t ≠ 0 := fun t ht => (delta_pos_of_lt ht.1).ne'
  -- the derivative bounds
  have hbd : ∀ t ∈ Ioc a b, ∀ (F ζ : ℂ), ‖F‖ = 1 → ‖ζ‖ ≤ |L| + |2 * ω * t - e| →
      ‖F * (ζ * R t)‖ ≤ C * (‖hu_ampOut M Q e ω Θ R t‖ + ‖hu_ampIn M Q e ω Θ R t‖) := by
    intro t ht F ζ hF hζ
    obtain ⟨hct, hKt, -, -⟩ := hgood t ht
    have h := hu_norm_amp_deriv_le (P := (delta M Q t : ℂ) * deriv R t) (R := R t)
      (norm_exp_I_mul (Θ t)) (norm_exp_neg_I_mul (Θ t)) (hu_exp_I_mul_mul_exp_neg_I_mul (Θ t))
      hF hKt hζ
    exact h.trans (mul_le_mul_of_nonneg_right hct (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  obtain ⟨hA, hB⟩ := hu_eq_zero_of_norm_deriv_le (a₁ := hu_ampOut M Q e ω Θ R)
    (a₂ := hu_ampIn M Q e ω Θ R) hab (by linarith) (by rw [hb, add_sub_cancel_left]; exact hηC)
    (fun t ht => hu_hasDerivAt_ampOut (hΔ t ht) (hΘ t ht.1) (hR t ht.1))
    (fun t ht => hu_hasDerivAt_ampIn (hΔ t ht) (hΘ t ht.1) (hR t ht.1))
    (fun t ht => hbd t ht _ _ (norm_exp_neg_I_mul (Θ t)) (hu_norm_add_I_mul_le _ _))
    (fun t ht => hbd t ht _ _ (norm_exp_I_mul (Θ t)) (hu_norm_sub_I_mul_le _ _))
    hlo hli (fun t ht => (hgood t ht).2.2.1)
  unfold hu_ampOut at hA
  unfold hu_ampIn at hB
  obtain ⟨hP, hR0⟩ := hu_eq_zero_of_amps_eq_zero (hu_exp_I_mul_mul_exp_neg_I_mul (Θ b))
    (hgood b ⟨hab, le_rfl⟩).2.1 hA hB
  have hR1 : deriv R b = 0 :=
    (mul_eq_zero.1 hP).resolve_left (ofReal_ne_zero.2 (hΔ b ⟨hab, le_rfl⟩))
  have hp0 : ∀ r ∈ Ioi a, 0 < delta M Q r := fun r hr => delta_pos_of_lt hr
  have hw : ContinuousOn (fun r => radialK e ω r ^ 2 / delta M Q r - L) (Ioi a) :=
    ContinuousOn.sub (ContinuousOn.div (hKcont.pow 2).continuousOn
      (continuous_delta M Q).continuousOn (fun r hr => (hp0 r hr).ne')) continuousOn_const
  exact ModeStability.ODE.eqOn_zero_of_linear_ode (continuous_delta M Q).continuousOn hp0 hw hR
    hab hR0 hR1

/-- `Δ → 0` as `r ↓ a`. -/
theorem hu_tendsto_delta (M Q : ℝ) :
    Tendsto (delta M Q) (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
  have h : Tendsto (delta M Q) (𝓝[>] (outerHorizon M Q)) (𝓝 (delta M Q (outerHorizon M Q))) :=
    ((continuous_delta M Q).tendsto (outerHorizon M Q)).mono_left nhdsWithin_le_nhds
  have h0 : delta M Q (outerHorizon M Q) = 0 := by
    unfold delta
    rw [sub_self, zero_mul]
  rwa [h0] at h

/-- **Uniqueness at the horizon**, limit form. A solution of the radial equation on `r > a`
(`Θ' = K/Δ`, `K(a) ≠ 0`) whose ingoing profile `R̃ = e^{iΘ}R` satisfies `R̃ → 0` and
`R̃' = O(1)` as `r ↓ a` vanishes identically. -/
theorem eqOn_zero_of_horizon_tendsto_zero {M Q e ω L : ℝ}
    (hK : radialK e ω (outerHorizon M Q) ≠ 0) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (h1 : Tendsto (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (h2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) =O[𝓝[>] (outerHorizon M Q)]
      (fun _ => (1 : ℝ))) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  refine eqOn_zero_of_horizon_tendsto_profile hK hΘ hR h1 ?_
  have hO : (fun r => (delta M Q r : ℂ) * deriv (fun s : ℝ => exp (I * (Θ s : ℂ)) * R s) r)
      =O[𝓝[>] (outerHorizon M Q)] (fun r => delta M Q r * (1 : ℝ)) :=
    (isBigO_of_le _ (fun r => le_of_eq (Complex.norm_real _))).mul h2
  refine hO.trans_tendsto ?_
  simpa only [mul_one] using hu_tendsto_delta M Q

/-- **Uniqueness at the horizon.** A solution of the radial equation
`(ΔR')' + (K²/Δ − L)R = 0` on `r > a` (`M > 0`, `|Q| ≤ M`, `Θ' = K/Δ`, non-synchronized
`K(a) ≠ 0`; subextremal or extremal) satisfying the ingoing horizon condition (1.4) with
vanishing leading coefficient, `R̃ = e^{iΘ}R = O(r − a)` and `R̃' = O(1)`, vanishes identically.
(the all-angular research notes in preparation, p. 2; asserted there without proof.)
The premises `M > 0`, `|Q| ≤ M` of the source are kept but not used: the proof only needs
`Δ > 0` on `r > a`, which holds for all real `M, Q` with the frozen `a`, `b`, `Δ`. -/
theorem eqOn_zero_of_horizon_coefficient_zero {M Q e ω L : ℝ} (_hM : 0 < M) (_hQ : |Q| ≤ M)
    (hK : radialK e ω (outerHorizon M Q) ≠ 0) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (h1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) =O[𝓝[>] (outerHorizon M Q)]
      (fun r => r - outerHorizon M Q))
    (h2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) =O[𝓝[>] (outerHorizon M Q)]
      (fun _ => (1 : ℝ))) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  refine eqOn_zero_of_horizon_tendsto_zero hK hΘ hR (h1.trans_tendsto ?_) h2
  have h : Tendsto (fun r : ℝ => r - outerHorizon M Q) (𝓝[>] (outerHorizon M Q))
      (𝓝 (outerHorizon M Q - outerHorizon M Q)) :=
    ((continuous_sub_right (outerHorizon M Q)).tendsto (outerHorizon M Q)).mono_left
      nhdsWithin_le_nhds
  rwa [sub_self] at h

end ModeStability.AllAngular

end
