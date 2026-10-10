module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.AllAngular.HorizonUniquenessAux
public import ModeStability.AllAngular.HorizonUniqueness

/-!
# The horizon condition from the limits of the horizon amplitudes

Source: the all-angular research notes in preparation, (1.2)–(1.4) and Sections 6, 8, which use
the
solution `R_H` with unit leading coefficient in the horizon condition (1.4). This file proves
the asymptotic
half of its construction: a solution of the radial equation `(ΔR')' + (K²/Δ − L)R = 0` on `r > a`
(`Θ' = K/Δ`, `K(a) ≠ 0`) whose horizon amplitudes
`A = e^{−iΘ}(ΔR' + iKR)` and `B = e^{iΘ}(ΔR' − iKR)` (`hu_ampOut`, `hu_ampIn`) satisfy
`A → 0` and `B → −2iK(a)` as `r ↓ a` satisfies the ingoing horizon condition (1.4) with leading
coefficient `B_H = 1`, in the form `e^{iΘ}R − 1 = O(r − a)`, `(e^{iΘ}R)' = O(1)`
(`hs_horizon_condition_of_tendsto_amps`). This covers the subextremal and the extremal horizon.

## Proof

Write `R̃ = e^{iΘ}R`. Algebraically `2iKR̃ = e^{2iΘ}A − B` and `ΔR̃' = e^{2iΘ}A`
(`hu_delta_mul_deriv_profile`). Hence `R̃ → 1`. Since `A' = e^{−iΘ}(L + iK')R` and
`B' = e^{iΘ}(L − iK')R` are bounded, the mean value inequality gives `A = O(r − a)` and
`B + 2iK(a) = O(r − a)`, hence `R̃ − 1 = O(r − a)`.

For `R̃' = O(1)` one needs `A = O(Δ)`, which at the extremal horizon `Δ = (r − a)²` is an
oscillation estimate. With `φ = (L + iK')/(−2iK)` and `h = φΔR̃`, the derivative
`(e^{−2iΘ})' = −2iΘ'e^{−2iΘ}` gives `(e^{−2iΘ})'h = e^{−iΘ}(L + iK')R = A'`, so the corrected
amplitude `Ã = A − e^{−2iΘ}h` has `Ã' = −e^{−2iΘ}h'` (an integration by parts). Now
`h' = φ'ΔR̃ + φ(Δ'R̃ + e^{2iΘ}A) = O(Δ')`, and `Δ' = 2r − 2M` is increasing, so the mean value
inequality gives `Ã = O((r − a)Δ') = O(Δ)` (`(r − a)Δ' ≤ 2Δ`). Since `h = O(Δ)`, `A = O(Δ)`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

open InfinityUniqueness

/-! ### Generic asymptotic tools -/

/-- Functions with equal norms have the same `O`-bounds. -/
theorem hs_isBigO_of_norm_eq {α E F G : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [Norm G] {l : Filter α}
    {f : α → E} {g : α → F} {k : α → G} (h : ∀ᶠ x in l, ‖f x‖ = ‖g x‖) (hg : g =O[l] k) :
    f =O[l] k :=
  (IsBigO.of_bound 1 (h.mono fun x hx => by rw [one_mul]; exact hx.le)).trans hg

/-- The mean value inequality in `O`-form at a left endpoint: if `c → 0` as `t ↓ a` and
`c' = O(g)` for a monotone `g ≥ 0`, then `c = O((t − a) g)`. -/
theorem hs_isBigO_mul_of_hasDerivAt {a : ℝ} {c c' : ℝ → ℂ} {g : ℝ → ℝ} (hg : Monotone g)
    (hg0 : ∀ᶠ t in 𝓝[>] a, 0 ≤ g t) (hc : ∀ᶠ t in 𝓝[>] a, HasDerivAt c (c' t) t)
    (hc' : c' =O[𝓝[>] a] g) (hlim : Tendsto c (𝓝[>] a) (𝓝 0)) :
    c =O[𝓝[>] a] (fun t => (t - a) * g t) := by
  obtain ⟨C, hC0, hC⟩ := hc'.exists_pos
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hg0.and (hc.and hC.bound))
  refine IsBigO.of_bound C ?_
  filter_upwards [Ioo_mem_nhdsGT hu] with t₀ ht₀
  have hin : ∀ t ∈ Ioc a t₀, t ∈ Ioo a u := fun t ht => ⟨ht.1, ht.2.trans_lt ht₀.2⟩
  have hD : ∀ t ∈ Ioc a t₀, ‖c' t‖ ≤ C * g t₀ := by
    intro t ht
    obtain ⟨hg0t, -, hbt⟩ := hsub (hin t ht)
    calc ‖c' t‖ ≤ C * ‖g t‖ := hbt
      _ = C * g t := by rw [Real.norm_of_nonneg hg0t]
      _ ≤ C * g t₀ := mul_le_mul_of_nonneg_left (hg ht.2) hC0.le
  have h := hu_norm_le_of_tendsto_nhdsGT ht₀.1 (fun t ht => (hsub (hin t ht)).2.1) hD hlim
  have hg0₀ : 0 ≤ g t₀ := (hsub ht₀).1
  have ha₀ : 0 ≤ t₀ - a := (sub_pos.2 ht₀.1).le
  rw [Real.norm_of_nonneg (mul_nonneg ha₀ hg0₀)]
  calc ‖c t₀‖ ≤ C * g t₀ * (t₀ - a) := h
    _ = C * ((t₀ - a) * g t₀) := by ring

/-- A function continuous at `a` is `O(1)` as `t ↓ a`. -/
theorem hs_isBigO_one_of_continuousAt {a : ℝ} {f : ℝ → ℂ} (hf : ContinuousAt f a) :
    f =O[𝓝[>] a] (fun _ => (1 : ℝ)) :=
  (hf.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ

/-! ### Algebra of the horizon amplitudes -/

variable {M Q e ω L : ℝ} {Θ : ℝ → ℝ} {R : ℝ → ℂ}

/-- `2iKR̃ = e^{2iΘ}A − B` for the ingoing profile `R̃ = e^{iΘ}R`. -/
theorem hs_two_I_mul_profile (r : ℝ) :
    2 * I * (radialK e ω r : ℂ) * (exp (I * (Θ r : ℂ)) * R r) =
      exp (I * Θ r) * exp (I * Θ r) * hu_ampOut M Q e ω Θ R r - hu_ampIn M Q e ω Θ R r := by
  have h := hu_exp_I_mul_mul_exp_neg_I_mul (Θ r)
  simp only [hu_ampOut, hu_ampIn]
  linear_combination
    (-(exp (I * Θ r) * ((delta M Q r : ℂ) * deriv R r + I * radialK e ω r * R r))) * h

/-- `ΔR̃' = e^{2iΘ}A` for the ingoing profile `R̃ = e^{iΘ}R`. -/
theorem hs_delta_mul_deriv_profile_eq {r : ℝ} (hΔ : delta M Q r ≠ 0)
    (hΘ : HasDerivAt Θ (radialK e ω r / delta M Q r) r) (hR : DifferentiableAt ℝ R r) :
    (delta M Q r : ℂ) * deriv (fun s : ℝ => exp (I * (Θ s : ℂ)) * R s) r =
      exp (I * Θ r) * exp (I * Θ r) * hu_ampOut M Q e ω Θ R r := by
  rw [hu_delta_mul_deriv_profile hΔ hΘ hR]
  have h := hu_exp_I_mul_mul_exp_neg_I_mul (Θ r)
  simp only [hu_ampOut]
  linear_combination
    (-(exp (I * Θ r) * ((delta M Q r : ℂ) * deriv R r + I * radialK e ω r * R r))) * h

/-! ### First consequences of the amplitude limits -/

/-- `K` is continuous (as a complex-valued function). -/
theorem hs_continuous_radialK_complex (e ω : ℝ) :
    Continuous (fun r => (radialK e ω r : ℂ)) := by
  unfold radialK
  fun_prop

/-- Near a non-synchronized horizon, `K ≠ 0`. -/
theorem hs_eventually_radialK_ne (hK : radialK e ω (outerHorizon M Q) ≠ 0) :
    ∀ᶠ r in 𝓝[>] (outerHorizon M Q), radialK e ω r ≠ 0 := by
  have hKcont : Continuous (radialK e ω) := by
    unfold radialK
    fun_prop
  exact (hKcont.continuousAt.eventually_ne hK).filter_mono nhdsWithin_le_nhds

/-- `2iK ≠ 0` where `K ≠ 0`. -/
theorem hs_two_I_mul_ne_zero {k : ℝ} (hk : k ≠ 0) : (2 * I * (k : ℂ)) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (ofReal_ne_zero.2 hk)

/-- If `A → 0` and `B → −2iK(a)`, the ingoing profile tends to `1`. -/
theorem hs_tendsto_profile (hK : radialK e ω (outerHorizon M Q) ≠ 0)
    (hA : Tendsto (hu_ampOut M Q e ω Θ R) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (hB : Tendsto (hu_ampIn M Q e ω Θ R) (𝓝[>] (outerHorizon M Q))
      (𝓝 (-(2 * I * radialK e ω (outerHorizon M Q))))) :
    Tendsto (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) (𝓝[>] (outerHorizon M Q)) (𝓝 1) := by
  set a := outerHorizon M Q with ha
  have hKt : Tendsto (fun r => 2 * I * (radialK e ω r : ℂ)) (𝓝[>] a)
      (𝓝 (2 * I * (radialK e ω a : ℂ))) :=
    (((hs_continuous_radialK_complex e ω).tendsto a).const_mul (2 * I)).mono_left
      nhdsWithin_le_nhds
  have hEA : Tendsto (fun r => exp (I * (Θ r : ℂ)) * exp (I * (Θ r : ℂ)) *
      hu_ampOut M Q e ω Θ R r) (𝓝[>] a) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := hA.norm
    rw [norm_zero] at h
    refine h.congr' (Eventually.of_forall fun r => ?_)
    simp only [norm_mul, norm_exp_I_mul, one_mul]
  have hK0 := hs_two_I_mul_ne_zero hK
  have h := (hEA.sub hB).div hKt hK0
  rw [zero_sub, neg_neg, div_self hK0] at h
  refine h.congr' ?_
  filter_upwards [hs_eventually_radialK_ne hK] with r hr
  simp only [Pi.div_apply]
  rw [div_eq_iff (hs_two_I_mul_ne_zero hr), ← hs_two_I_mul_profile]
  ring

/-- If `A → 0` and `B → −2iK(a)`, then `A = O(r − a)` and `B + 2iK(a) = O(r − a)`. -/
theorem hs_isBigO_amps (hK : radialK e ω (outerHorizon M Q) ≠ 0)
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hA : Tendsto (hu_ampOut M Q e ω Θ R) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (hB : Tendsto (hu_ampIn M Q e ω Θ R) (𝓝[>] (outerHorizon M Q))
      (𝓝 (-(2 * I * radialK e ω (outerHorizon M Q))))) :
    hu_ampOut M Q e ω Θ R =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) ∧
      (fun r => hu_ampIn M Q e ω Θ R r + 2 * I * radialK e ω (outerHorizon M Q))
        =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) := by
  set a := outerHorizon M Q with ha
  have hRt := (hs_tendsto_profile hK hA hB).isBigO_one ℝ
  have hN₁ : (fun r : ℝ => ((L : ℂ) + I * ((2 * ω * r - e : ℝ) : ℂ)) *
      (exp (I * (Θ r : ℂ)) * R r)) =O[𝓝[>] a] (fun _ => (1 : ℝ)) := by
    have h := (hs_isBigO_one_of_continuousAt (a := a)
      (f := fun r : ℝ => (L : ℂ) + I * ((2 * ω * r - e : ℝ) : ℂ))
      (by fun_prop)).mul hRt
    simpa only [mul_one] using h
  have hN₂ : (fun r : ℝ => ((L : ℂ) - I * ((2 * ω * r - e : ℝ) : ℂ)) *
      (exp (I * (Θ r : ℂ)) * R r)) =O[𝓝[>] a] (fun _ => (1 : ℝ)) := by
    have h := (hs_isBigO_one_of_continuousAt (a := a)
      (f := fun r : ℝ => (L : ℂ) - I * ((2 * ω * r - e : ℝ) : ℂ))
      (by fun_prop)).mul hRt
    simpa only [mul_one] using h
  have hev : ∀ᶠ r in 𝓝[>] a, r ∈ Ioi a := self_mem_nhdsWithin
  constructor
  · have h := hs_isBigO_mul_of_hasDerivAt (a := a) (g := fun _ => (1 : ℝ)) monotone_const
      (Eventually.of_forall fun _ => zero_le_one)
      (hev.mono fun t ht => hu_hasDerivAt_ampOut (delta_pos_of_lt ht).ne' (hΘ t ht) (hR t ht))
      (hs_isBigO_of_norm_eq (Eventually.of_forall fun r => by
        simp only [norm_mul, norm_exp_neg_I_mul, norm_exp_I_mul, one_mul]) hN₁) hA
    simpa only [mul_one] using h
  · have hB0 : Tendsto (fun r => hu_ampIn M Q e ω Θ R r + 2 * I * radialK e ω a) (𝓝[>] a)
        (𝓝 0) := by
      have h := hB.add_const (2 * I * (radialK e ω a : ℂ))
      rwa [neg_add_cancel] at h
    have h := hs_isBigO_mul_of_hasDerivAt (a := a) (g := fun _ => (1 : ℝ)) monotone_const
      (Eventually.of_forall fun _ => zero_le_one)
      (hev.mono fun t ht =>
        (hu_hasDerivAt_ampIn (delta_pos_of_lt ht).ne' (hΘ t ht) (hR t ht)).add_const _)
      (hs_isBigO_of_norm_eq (Eventually.of_forall fun r => by
        simp only [norm_mul, norm_exp_I_mul, one_mul]) hN₂) hB0
    simpa only [mul_one] using h

/-- The first half of the horizon condition: `e^{iΘ}R − 1 = O(r − a)`. -/
theorem hs_isBigO_profile_sub_one (hK : radialK e ω (outerHorizon M Q) ≠ 0)
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hA : Tendsto (hu_ampOut M Q e ω Θ R) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (hB : Tendsto (hu_ampIn M Q e ω Θ R) (𝓝[>] (outerHorizon M Q))
      (𝓝 (-(2 * I * radialK e ω (outerHorizon M Q))))) :
    (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - 1) =O[𝓝[>] (outerHorizon M Q)]
      (fun r => r - outerHorizon M Q) := by
  set a := outerHorizon M Q with ha
  obtain ⟨hA1, hB1⟩ := hs_isBigO_amps hK hΘ hR hA hB
  have hEA : (fun r => exp (I * (Θ r : ℂ)) * exp (I * (Θ r : ℂ)) * hu_ampOut M Q e ω Θ R r)
      =O[𝓝[>] a] (fun r => r - a) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => by
      simp only [norm_mul, norm_exp_I_mul, one_mul]) hA1
  have hKa : (fun r => ((radialK e ω r - radialK e ω a : ℝ) : ℂ)) =O[𝓝[>] a]
      (fun r => r - a) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => Complex.norm_real _)
      ((hasDerivAt_radialK e ω a).isBigO_sub.mono nhdsWithin_le_nhds)
  have hnum := (hEA.sub hB1).sub (hKa.const_mul_left (2 * I))
  have hinv : (fun r => (2 * I * (radialK e ω r : ℂ))⁻¹) =O[𝓝[>] a] (fun _ => (1 : ℝ)) := by
    refine hs_isBigO_one_of_continuousAt ?_
    exact ((hs_continuous_radialK_complex e ω).continuousAt.const_mul (2 * I)).inv₀
      (hs_two_I_mul_ne_zero hK)
  have h := hnum.mul hinv
  simp only [mul_one] at h
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hs_eventually_radialK_ne hK] with r hr
  have h2 := hs_two_I_mul_profile (M := M) (Q := Q) (Θ := Θ) (R := R) (e := e) (ω := ω) r
  have hne := hs_two_I_mul_ne_zero hr
  rw [← div_eq_mul_inv, div_eq_iff hne]
  push_cast
  linear_combination -h2

/-! ### The integration by parts at the horizon -/

/-- The coefficient `φ = (L + iK')/(−2iK)` of the integration by parts. -/
@[expose] noncomputable def hs_phi (e ω L r : ℝ) : ℂ :=
  ((L : ℂ) + I * ((2 * ω * r - e : ℝ) : ℂ)) / (-(2 * I * (radialK e ω r : ℂ)))

/-- The derivative `φ'` of `φ = (L + iK')/(−2iK)`. -/
@[expose] noncomputable def hs_phiDeriv (e ω L r : ℝ) : ℂ :=
  (I * ((2 * ω : ℝ) : ℂ) * (-(2 * I * (radialK e ω r : ℂ))) -
      ((L : ℂ) + I * ((2 * ω * r - e : ℝ) : ℂ)) * (-(2 * I * ((2 * ω * r - e : ℝ) : ℂ)))) /
    (-(2 * I * (radialK e ω r : ℂ))) ^ 2

/-- `−2iK ≠ 0` where `K ≠ 0`. -/
theorem hs_neg_two_I_mul_ne_zero {k : ℝ} (hk : k ≠ 0) : (-(2 * I * (k : ℂ))) ≠ 0 :=
  neg_ne_zero.2 (hs_two_I_mul_ne_zero hk)

/-- `φ' ` is the derivative of `φ` where `K ≠ 0`. -/
theorem hs_hasDerivAt_phi {r : ℝ} (hr : radialK e ω r ≠ 0) :
    HasDerivAt (hs_phi e ω L) (hs_phiDeriv e ω L r) r := by
  have hN : HasDerivAt (fun s : ℝ => (L : ℂ) + I * ((2 * ω * s - e : ℝ) : ℂ))
      (I * ((2 * ω : ℝ) : ℂ)) r := by
    have h := ((((hasDerivAt_id r).const_mul (2 * ω)).sub_const e).ofReal_comp.const_mul
      I).const_add (L : ℂ)
    refine h.congr_deriv ?_
    simp
  have hD : HasDerivAt (fun s : ℝ => -(2 * I * (radialK e ω s : ℂ)))
      (-(2 * I * ((2 * ω * r - e : ℝ) : ℂ))) r :=
    ((hasDerivAt_radialK e ω r).ofReal_comp.const_mul (2 * I)).neg
  exact hN.div hD (hs_neg_two_I_mul_ne_zero hr)

/-- `φ'` is continuous where `K ≠ 0`. -/
theorem hs_continuousAt_phiDeriv {r : ℝ} (hr : radialK e ω r ≠ 0) :
    ContinuousAt (hs_phiDeriv e ω L) r := by
  unfold hs_phiDeriv
  have hD : (-(2 * I * (radialK e ω r : ℂ))) ^ 2 ≠ 0 := pow_ne_zero 2 (hs_neg_two_I_mul_ne_zero hr)
  unfold radialK at hD ⊢
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hD

/-- The algebra behind the integration by parts: with `xy = 1`,
`(e^{−2iΘ})'φΔR̃ = e^{−iΘ}(L + iK')R` in the form
`2x²(−iK/Δ)(N/(−2iK))Δ(yR) = x N R`. -/
theorem hs_ibp_alg {x y N R k d : ℂ} (hxy : y * x = 1) (hk : k ≠ 0) (hd : d ≠ 0) :
    (x * -(I * (k / d)) * x + x * (x * -(I * (k / d)))) * (N / -(2 * I * k) * (d * (y * R))) =
      x * (N * R) := by
  have h2 : (-(2 * I * k)) ≠ 0 := neg_ne_zero.2 (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hk)
  have key : -(I * (k / d)) * (N / -(2 * I * k)) * d = N / 2 := by
    field_simp
  calc (x * -(I * (k / d)) * x + x * (x * -(I * (k / d)))) * (N / -(2 * I * k) * (d * (y * R)))
      = 2 * x * (y * x) * R * (-(I * (k / d)) * (N / -(2 * I * k)) * d) := by ring
    _ = x * (N * R) := by rw [key, hxy]; ring

/-- The corrected amplitude `Ã = A − e^{−2iΘ}φΔR̃` has `Ã' = −e^{−2iΘ}h'` with
`h' = φ'ΔR̃ + φ(Δ'R̃ + e^{2iΘ}A)`: the derivative of `e^{−2iΘ}` absorbs `A'`. -/
theorem hs_hasDerivAt_corrected {r : ℝ} (hΔ : delta M Q r ≠ 0) (hKr : radialK e ω r ≠ 0)
    (hΘ : HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : DifferentiableAt ℝ R r ∧ HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    HasDerivAt (fun s => hu_ampOut M Q e ω Θ R s -
        exp (-(I * (Θ s : ℂ))) * exp (-(I * (Θ s : ℂ))) *
          (hs_phi e ω L s * ((delta M Q s : ℂ) * (exp (I * (Θ s : ℂ)) * R s))))
      (-(exp (-(I * (Θ r : ℂ))) * exp (-(I * (Θ r : ℂ)))) *
        (hs_phiDeriv e ω L r * ((delta M Q r : ℂ) * (exp (I * (Θ r : ℂ)) * R r)) +
          hs_phi e ω L r * (((2 * r - 2 * M : ℝ) : ℂ) * (exp (I * (Θ r : ℂ)) * R r) +
            exp (I * (Θ r : ℂ)) * exp (I * (Θ r : ℂ)) * hu_ampOut M Q e ω Θ R r))) r := by
  have hA' := hu_hasDerivAt_ampOut hΔ hΘ hR
  have hEi := hasDerivAt_exp_neg_phase (M := M) (Q := Q) hΘ
  have hRt : HasDerivAt (fun s => exp (I * (Θ s : ℂ)) * R s)
      (deriv (fun s => exp (I * (Θ s : ℂ)) * R s) r) r :=
    (((hasDerivAt_exp_phase (M := M) (Q := Q) hΘ).mul
      hR.1.hasDerivAt).differentiableAt).hasDerivAt
  have hDRt := ((hasDerivAt_delta M Q r).ofReal_comp).mul hRt
  have hφ := hs_hasDerivAt_phi (L := L) hKr
  have htot := hA'.sub ((hEi.mul hEi).mul (hφ.mul hDRt))
  refine htot.congr_deriv ?_
  have hprof := hs_delta_mul_deriv_profile_eq hΔ hΘ hR.1
  have hEEi := hu_exp_I_mul_mul_exp_neg_I_mul (Θ r)
  have hk : (radialK e ω r : ℂ) ≠ 0 := ofReal_ne_zero.2 hKr
  have hd : (delta M Q r : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ
  have hEiE : exp (I * (Θ r : ℂ)) * exp (-(I * (Θ r : ℂ))) = 1 := hEEi
  simp only [Pi.mul_apply]
  rw [hprof]
  have halg := hs_ibp_alg (N := (L : ℂ) + I * ((2 * ω * r - e : ℝ) : ℂ)) (R := R r) hEiE hk hd
  simp only [hs_phi, phaseRate] at halg ⊢
  push_cast at halg ⊢
  linear_combination -halg

/-- `b ≤ a`. -/
theorem hs_innerHorizon_le (M Q : ℝ) : innerHorizon M Q ≤ outerHorizon M Q := by
  unfold innerHorizon outerHorizon
  linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]

/-- `a + b = 2M`. -/
theorem hs_outer_add_inner (M Q : ℝ) : outerHorizon M Q + innerHorizon M Q = 2 * M := by
  unfold innerHorizon outerHorizon
  ring

/-- `A = O(Δ)` as `r ↓ a`, by the integration by parts `hs_hasDerivAt_corrected`. -/
theorem hs_isBigO_ampOut_delta (hK : radialK e ω (outerHorizon M Q) ≠ 0)
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hA : Tendsto (hu_ampOut M Q e ω Θ R) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (hB : Tendsto (hu_ampIn M Q e ω Θ R) (𝓝[>] (outerHorizon M Q))
      (𝓝 (-(2 * I * radialK e ω (outerHorizon M Q))))) :
    hu_ampOut M Q e ω Θ R =O[𝓝[>] (outerHorizon M Q)] (delta M Q) := by
  have hba := hs_innerHorizon_le M Q
  have hab2 := hs_outer_add_inner M Q
  set a := outerHorizon M Q with ha
  set b := innerHorizon M Q with hb
  obtain ⟨hA1, -⟩ := hs_isBigO_amps hK hΘ hR hA hB
  have hRt := (hs_tendsto_profile hK hA hB).isBigO_one ℝ
  have hev : ∀ᶠ r in 𝓝[>] a, r ∈ Ioi a := self_mem_nhdsWithin
  have hg : Monotone (fun t : ℝ => 2 * t - 2 * M) := fun x y hxy => by linarith
  have hg0 : ∀ᶠ t in 𝓝[>] a, 0 ≤ 2 * t - 2 * M := hev.mono fun t ht => by
    have : a < t := ht
    linarith
  -- `r − a ≤ Δ'` and `Δ ≤ (a − b + 1)Δ'` near `a`
  have hlin : (fun r : ℝ => r - a) =O[𝓝[>] a] (fun t : ℝ => 2 * t - 2 * M) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hev] with t ht
    have ht' : a < t := ht
    rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith), one_mul]
    linarith
  have hΔg : (fun r => (delta M Q r : ℂ)) =O[𝓝[>] a] (fun t : ℝ => 2 * t - 2 * M) := by
    refine IsBigO.of_bound (a - b + 1) ?_
    filter_upwards [hev, Ioo_mem_nhdsGT (show a < a + 1 by linarith)] with t ht ht1
    have ht' : a < t := ht
    rw [Complex.norm_real, Real.norm_of_nonneg (delta_pos_of_lt ht).le,
      Real.norm_of_nonneg (by linarith)]
    have hd : delta M Q t = (t - a) * (t - b) := rfl
    rw [hd]
    have h1 : (t - a) * (t - b) ≤ (2 * t - 2 * M) * (t - b) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (2 * t - 2 * M) * (t - b) ≤ (2 * t - 2 * M) * (a - b + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [ht1.2]) (by linarith)
    linarith
  have hEEA : (fun r => exp (I * (Θ r : ℂ)) * exp (I * (Θ r : ℂ)) * hu_ampOut M Q e ω Θ R r)
      =O[𝓝[>] a] (fun t : ℝ => 2 * t - 2 * M) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => by
      simp only [norm_mul, norm_exp_I_mul, one_mul]) (hA1.trans hlin)
  have hΔ'c : (fun r : ℝ => ((2 * r - 2 * M : ℝ) : ℂ)) =O[𝓝[>] a]
      (fun t : ℝ => 2 * t - 2 * M) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => Complex.norm_real _) (isBigO_refl _ _)
  have hφ1 := hs_isBigO_one_of_continuousAt (hs_hasDerivAt_phi (L := L) hK).continuousAt
  have hφ'1 := hs_isBigO_one_of_continuousAt (hs_continuousAt_phiDeriv (L := L) hK)
  have h'O : (fun r => hs_phiDeriv e ω L r * ((delta M Q r : ℂ) * (exp (I * (Θ r : ℂ)) * R r)) +
        hs_phi e ω L r * (((2 * r - 2 * M : ℝ) : ℂ) * (exp (I * (Θ r : ℂ)) * R r) +
          exp (I * (Θ r : ℂ)) * exp (I * (Θ r : ℂ)) * hu_ampOut M Q e ω Θ R r))
      =O[𝓝[>] a] (fun t : ℝ => 2 * t - 2 * M) := by
    have t1 := hφ'1.mul (hΔg.mul hRt)
    have t21 := hΔ'c.mul hRt
    simp only [mul_one] at t21
    have t2 := hφ1.mul (t21.add hEEA)
    simp only [one_mul, mul_one] at t1 t2
    exact t1.add t2
  -- the corrected amplitude
  have hc' := hs_isBigO_of_norm_eq (l := 𝓝[>] a) (f := fun r =>
      -(exp (-(I * (Θ r : ℂ))) * exp (-(I * (Θ r : ℂ)))) *
        (hs_phiDeriv e ω L r * ((delta M Q r : ℂ) * (exp (I * (Θ r : ℂ)) * R r)) +
          hs_phi e ω L r * (((2 * r - 2 * M : ℝ) : ℂ) * (exp (I * (Θ r : ℂ)) * R r) +
            exp (I * (Θ r : ℂ)) * exp (I * (Θ r : ℂ)) * hu_ampOut M Q e ω Θ R r)))
    (Eventually.of_forall fun r => by
      simp only [norm_mul, norm_neg, norm_exp_neg_I_mul, one_mul]) h'O
  have hderiv : ∀ᶠ t in 𝓝[>] a, HasDerivAt (fun s => hu_ampOut M Q e ω Θ R s -
        exp (-(I * (Θ s : ℂ))) * exp (-(I * (Θ s : ℂ))) *
          (hs_phi e ω L s * ((delta M Q s : ℂ) * (exp (I * (Θ s : ℂ)) * R s))))
      (-(exp (-(I * (Θ t : ℂ))) * exp (-(I * (Θ t : ℂ)))) *
        (hs_phiDeriv e ω L t * ((delta M Q t : ℂ) * (exp (I * (Θ t : ℂ)) * R t)) +
          hs_phi e ω L t * (((2 * t - 2 * M : ℝ) : ℂ) * (exp (I * (Θ t : ℂ)) * R t) +
            exp (I * (Θ t : ℂ)) * exp (I * (Θ t : ℂ)) * hu_ampOut M Q e ω Θ R t))) t := by
    filter_upwards [hev, hs_eventually_radialK_ne hK] with t ht hKt
    exact hs_hasDerivAt_corrected (delta_pos_of_lt ht).ne' hKt (hΘ t ht) (hR t ht)
  have hΔΔ : (fun r => (delta M Q r : ℂ)) =O[𝓝[>] a] (delta M Q) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => Complex.norm_real _) (isBigO_refl _ _)
  have hh : (fun r => hs_phi e ω L r * ((delta M Q r : ℂ) * (exp (I * (Θ r : ℂ)) * R r)))
      =O[𝓝[>] a] (delta M Q) := by
    have h := hφ1.mul (hΔΔ.mul hRt)
    simpa only [one_mul, mul_one] using h
  have hEEh : (fun r => exp (-(I * (Θ r : ℂ))) * exp (-(I * (Θ r : ℂ))) *
      (hs_phi e ω L r * ((delta M Q r : ℂ) * (exp (I * (Θ r : ℂ)) * R r))))
      =O[𝓝[>] a] (delta M Q) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => by
      simp only [norm_mul, norm_exp_neg_I_mul, one_mul]) hh
  have hlim := hA.sub (hEEh.trans_tendsto (hu_tendsto_delta M Q))
  rw [sub_zero] at hlim
  have hcorr := hs_isBigO_mul_of_hasDerivAt hg hg0 hderiv hc' hlim
  have hgΔ : (fun t : ℝ => (t - a) * (2 * t - 2 * M)) =O[𝓝[>] a] (delta M Q) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [hev] with t ht
    have ht' : a < t := ht
    rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (by linarith)),
      Real.norm_of_nonneg (delta_pos_of_lt ht).le]
    have hd : delta M Q t = (t - a) * (t - b) := rfl
    rw [hd]
    have h1 : (t - a) * (2 * t - 2 * M) - 2 * ((t - a) * (t - b)) = (t - a) * (b - a) := by
      linear_combination (t - a) * hab2
    nlinarith [mul_nonneg (show 0 ≤ t - a by linarith) (show 0 ≤ a - b by linarith)]
  refine ((hcorr.trans hgΔ).add hEEh).congr_left fun r => ?_
  ring

/-! ### The horizon condition -/

/-- **The horizon condition from the limits of the amplitudes.** Let `K(a) ≠ 0`, `Θ' = K/Δ` on
`r > a`, and let `R` solve `(ΔR')' + (K²/Δ − L)R = 0` on `r > a`. If the horizon amplitudes
satisfy `A = e^{−iΘ}(ΔR' + iKR) → 0` and `B = e^{iΘ}(ΔR' − iKR) → −2iK(a)` as `r ↓ a`, then `R`
satisfies the ingoing horizon condition (1.4) with leading coefficient `B_H = 1`:
`e^{iΘ}R − 1 = O(r − a)` and `(e^{iΘ}R)' = O(1)`. Subextremal and extremal horizons alike. -/
theorem hs_horizon_condition_of_tendsto_amps (hK : radialK e ω (outerHorizon M Q) ≠ 0)
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hA : Tendsto (hu_ampOut M Q e ω Θ R) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (hB : Tendsto (hu_ampIn M Q e ω Θ R) (𝓝[>] (outerHorizon M Q))
      (𝓝 (-(2 * I * radialK e ω (outerHorizon M Q))))) :
    (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - 1) =O[𝓝[>] (outerHorizon M Q)]
        (fun r => r - outerHorizon M Q) ∧
      deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) =O[𝓝[>] (outerHorizon M Q)]
        (fun _ => (1 : ℝ)) := by
  refine ⟨hs_isBigO_profile_sub_one hK hΘ hR hA hB, ?_⟩
  obtain ⟨C, hC⟩ := (hs_isBigO_ampOut_delta hK hΘ hR hA hB).bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, self_mem_nhdsWithin] with r hr hra
  have hΔ := delta_pos_of_lt hra
  have hn := congrArg norm (hs_delta_mul_deriv_profile_eq hΔ.ne' (hΘ r hra) (hR r hra).1)
  rw [norm_mul, norm_mul, norm_mul, norm_exp_I_mul, one_mul, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hΔ.le] at hn
  rw [Real.norm_of_nonneg hΔ.le] at hr
  rw [norm_one, mul_one]
  have h : delta M Q r * ‖deriv (fun s : ℝ => exp (I * (Θ s : ℂ)) * R s) r‖ ≤
      delta M Q r * C := by
    rw [hn]
    linarith
  exact le_of_mul_le_mul_left h hΔ

end ModeStability.AllAngular

end
