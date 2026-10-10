module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.AllAngular.HorizonUniqueness
public import ModeStability.AllAngular.HorizonSolutionAsymp

/-!
# The horizon amplitude system on the whole exterior

Source: the all-angular research notes in preparation, (1.2)–(1.4) and Sections 6, 8, which use
the
solution `R_H` of the radial equation `(ΔR')' + (K²/Δ − L)R = 0` normalized by (1.4) with leading
coefficient 1. The paper takes its existence from the Frobenius construction. This file reduces
the construction to a first-order linear system with coefficients that are continuous on `r > a`
and bounded at the horizon, which a Volterra existence theorem solves.

## The system

The horizon amplitudes `e^{∓iΘ}(ΔR' ± iKR)` solve a system with bounded coefficients near `a`, but
their coefficients contain `1/K`, and `K` may vanish at some `r > a`. Instead, fix `c` with
`κ = K + cΔ ≠ 0` on `[a, ∞)` (`hs_exists_kap_ne`; `κ = K` at the horizon) and use
`A = e^{−iΘ}(P + iκR)`, `B = e^{iΘ}(P − iκR)`, `P = ΔR'`. By `P' = −(K²/Δ − L)R` and
`Θ' = K/Δ`, using `κ − K = cΔ`,
`A' = e^{−iΘ}((L + cK + iκ')R + icP)`, `B' = e^{iΘ}((L + cK − iκ')R − icP)`. With
`2iκR = e^{iΘ}A − e^{−iΘ}B` and `2P = e^{iΘ}A + e^{−iΘ}B` this is the linear system
`A' = m₁₁A + m₁₂B`, `B' = m₂₁A + m₂₂B` with `α± = (L + cK ± iκ')/(2iκ)`, `β = ic/2`,
`m₁₁ = α₊ + β`, `m₁₂ = (β − α₊)e^{−2iΘ}`, `m₂₁ = (α₋ − β)e^{2iΘ}`, `m₂₂ = −(α₋ + β)`.
Its coefficients are continuous on `r > a` and bounded near `a`.

Conversely (`hs_hasDerivAt_sysR`, `hs_hasDerivAt_sysP`), if `(A, B)` solves the system, then
`R = (e^{iΘ}A − e^{−iΘ}B)/(2iκ)` and `P = (e^{iΘ}A + e^{−iΘ}B)/2` satisfy `R' = P/Δ` and
`P' = −(K²/Δ − L)R`. The horizon amplitudes of `R` are `A − icΔe^{−iΘ}R` and
`B + icΔe^{iΘ}R`, so `A → 0`, `B → −2iK(a)` gives the hypotheses of
`hs_horizon_condition_of_tendsto_amps` (`hs_horizon_solution_of_system`).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

open InfinityUniqueness

/-! ### The modified amplitude coefficient `κ = K + cΔ` -/

/-- `κ = K + cΔ`. -/
@[expose] noncomputable def hs_kap (M Q e ω c r : ℝ) : ℝ := radialK e ω r + c * delta M Q r

/-- `κ' = K' + cΔ'`. -/
@[expose] noncomputable def hs_kapD (M e ω c r : ℝ) : ℝ := (2 * ω * r - e) + c * (2 * r - 2 * M)

/-- `κ' ` is the derivative of `κ`. -/
theorem hs_hasDerivAt_kap (M Q e ω c r : ℝ) :
    HasDerivAt (hs_kap M Q e ω c) (hs_kapD M e ω c r) r :=
  (hasDerivAt_radialK e ω r).add ((hasDerivAt_delta M Q r).const_mul c)

/-- `κ` is continuous. -/
theorem hs_continuous_kap (M Q e ω c : ℝ) : Continuous (hs_kap M Q e ω c) := by
  have hK : Continuous (radialK e ω) := by
    unfold radialK
    fun_prop
  exact hK.add (continuous_const.mul (continuous_delta M Q))

/-- At a non-synchronized horizon there is `c` with `κ = K + cΔ ≠ 0` on `[a, ∞)`: with
`k₀ = K(a)`, `k₁ = K'(a)`, `x = r − a` and `c = (|k₀ω| + k₁²)/k₀`,
`k₀κ ≥ k₀² + k₀k₁x + k₁²x² ≥ 3k₀²/4 > 0`. -/
theorem hs_exists_kap_ne {M Q e ω : ℝ} (hK : radialK e ω (outerHorizon M Q) ≠ 0) :
    ∃ c : ℝ, ∀ r, outerHorizon M Q ≤ r → hs_kap M Q e ω c r ≠ 0 := by
  set a := outerHorizon M Q with ha
  set k₀ := radialK e ω a with hk₀
  set k₁ := 2 * ω * a - e with hk₁
  refine ⟨(|k₀ * ω| + k₁ ^ 2) / k₀, fun r hr => ?_⟩
  have hba := hs_innerHorizon_le M Q
  set x := r - a with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have hKr : radialK e ω r = k₀ + k₁ * x + ω * x ^ 2 := by
    rw [hk₀, hk₁, hx]
    unfold radialK
    ring
  have hΔ : x ^ 2 ≤ delta M Q r := by
    have hd : delta M Q r = x * (x + (a - innerHorizon M Q)) := by
      rw [hx]
      unfold delta
      ring
    rw [hd]
    nlinarith [mul_nonneg hx0 (show 0 ≤ a - innerHorizon M Q by linarith)]
  have hmul : k₀ * hs_kap M Q e ω ((|k₀ * ω| + k₁ ^ 2) / k₀) r =
      k₀ * radialK e ω r + (|k₀ * ω| + k₁ ^ 2) * delta M Q r := by
    unfold hs_kap
    field_simp
  have hpos : 0 < k₀ * hs_kap M Q e ω ((|k₀ * ω| + k₁ ^ 2) / k₀) r := by
    rw [hmul, hKr]
    have h1 : (|k₀ * ω| + k₁ ^ 2) * x ^ 2 ≤ (|k₀ * ω| + k₁ ^ 2) * delta M Q r :=
      mul_le_mul_of_nonneg_left hΔ (by positivity)
    have h2 : -(k₀ * ω) ≤ |k₀ * ω| := neg_le_abs _
    have h3 : 0 < k₀ ^ 2 := by positivity
    nlinarith [sq_nonneg (k₀ + 2 * k₁ * x), mul_le_mul_of_nonneg_right h2 (sq_nonneg x)]
  intro h0
  rw [h0, mul_zero] at hpos
  exact lt_irrefl 0 hpos

/-! ### The coefficients of the system -/

/-- `α₊ = (L + cK + iκ')/(2iκ)`. -/
@[expose] noncomputable def hs_alphaP (M Q e ω L c r : ℝ) : ℂ :=
  (((L + c * radialK e ω r : ℝ) : ℂ) + I * (hs_kapD M e ω c r : ℂ)) /
    (2 * I * (hs_kap M Q e ω c r : ℂ))

/-- `α₋ = (L + cK − iκ')/(2iκ)`. -/
@[expose] noncomputable def hs_alphaM (M Q e ω L c r : ℝ) : ℂ :=
  (((L + c * radialK e ω r : ℝ) : ℂ) - I * (hs_kapD M e ω c r : ℂ)) /
    (2 * I * (hs_kap M Q e ω c r : ℂ))

/-- `m₁₁ = α₊ + ic/2`. -/
@[expose] noncomputable def hs_m11 (M Q e ω L c r : ℝ) : ℂ := hs_alphaP M Q e ω L c r + I * c / 2

/-- `m₁₂ = (ic/2 − α₊)e^{−2iΘ}`. -/
@[expose] noncomputable def hs_m12 (M Q e ω L c : ℝ) (Θ : ℝ → ℝ) (r : ℝ) : ℂ :=
  (I * c / 2 - hs_alphaP M Q e ω L c r) * (exp (-(I * (Θ r : ℂ))) * exp (-(I * (Θ r : ℂ))))

/-- `m₂₁ = (α₋ − ic/2)e^{2iΘ}`. -/
@[expose] noncomputable def hs_m21 (M Q e ω L c : ℝ) (Θ : ℝ → ℝ) (r : ℝ) : ℂ :=
  (hs_alphaM M Q e ω L c r - I * c / 2) * (exp (I * (Θ r : ℂ)) * exp (I * (Θ r : ℂ)))

/-- `m₂₂ = −(α₋ + ic/2)`. -/
@[expose] noncomputable def hs_m22 (M Q e ω L c r : ℝ) : ℂ := -(hs_alphaM M Q e ω L c r + I * c / 2)

/-- `R = (e^{iΘ}A − e^{−iΘ}B)/(2iκ)`, recovered from the amplitudes. -/
@[expose] noncomputable def hs_sysR (M Q e ω c : ℝ) (Θ : ℝ → ℝ) (A B : ℝ → ℂ) (r : ℝ) : ℂ :=
  (exp (I * (Θ r : ℂ)) * A r - exp (-(I * (Θ r : ℂ))) * B r) / (2 * I * (hs_kap M Q e ω c r : ℂ))

/-- `P = ΔR' = (e^{iΘ}A + e^{−iΘ}B)/2`, recovered from the amplitudes. -/
@[expose] noncomputable def hs_sysP (Θ : ℝ → ℝ) (A B : ℝ → ℂ) (r : ℝ) : ℂ :=
  (exp (I * (Θ r : ℂ)) * A r + exp (-(I * (Θ r : ℂ))) * B r) / 2

/-! ### The converse algebra -/

/-- `R' = P/Δ` for `R = (e^{iΘ}A − e^{−iΘ}B)/(2iκ)` and `P = (e^{iΘ}A + e^{−iΘ}B)/2`. -/
theorem hs_hasDerivAt_sysR {M Q e ω L c : ℝ} {Θ : ℝ → ℝ} {A B : ℝ → ℂ} {r : ℝ}
    (hΔ : delta M Q r ≠ 0) (hκ : hs_kap M Q e ω c r ≠ 0)
    (hΘ : HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hA : HasDerivAt A (hs_m11 M Q e ω L c r * A r + hs_m12 M Q e ω L c Θ r * B r) r)
    (hB : HasDerivAt B (hs_m21 M Q e ω L c Θ r * A r + hs_m22 M Q e ω L c r * B r) r) :
    HasDerivAt (hs_sysR M Q e ω c Θ A B) (hs_sysP Θ A B r / delta M Q r) r := by
  have hE := hasDerivAt_exp_phase (M := M) (Q := Q) hΘ
  have hEi := hasDerivAt_exp_neg_phase (M := M) (Q := Q) hΘ
  have hk := (hs_hasDerivAt_kap M Q e ω c r).ofReal_comp.const_mul (2 * I)
  have h := ((hE.mul hA).sub (hEi.mul hB)).div hk
    (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (ofReal_ne_zero.2 hκ))
  refine h.congr_deriv ?_
  have hκc : ((hs_kap M Q e ω c r : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hκ
  have hrel : ((hs_kap M Q e ω c r : ℝ) : ℂ) = (radialK e ω r : ℂ) + c * delta M Q r := by
    simp only [hs_kap]
    push_cast
    ring
  have hd : (delta M Q r : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ
  have hE0 : exp (I * (Θ r : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hI : I ≠ 0 := I_ne_zero
  simp only [hs_m11, hs_m12, hs_m21, hs_m22, hs_alphaP, hs_alphaM, hs_sysP, phaseRate,
    Complex.exp_neg, Pi.mul_apply, Pi.sub_apply]
  push_cast
  generalize ((hs_kap M Q e ω c r : ℝ) : ℂ) = κ at hκc hrel ⊢
  generalize exp (I * (Θ r : ℂ)) = E at hE0 ⊢
  field_simp
  subst hrel
  ring

/-- `P' = −(K²/Δ − L)R` for `R = (e^{iΘ}A − e^{−iΘ}B)/(2iκ)` and `P = (e^{iΘ}A + e^{−iΘ}B)/2`. -/
theorem hs_hasDerivAt_sysP {M Q e ω L c : ℝ} {Θ : ℝ → ℝ} {A B : ℝ → ℂ} {r : ℝ}
    (hΔ : delta M Q r ≠ 0) (hκ : hs_kap M Q e ω c r ≠ 0)
    (hΘ : HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hA : HasDerivAt A (hs_m11 M Q e ω L c r * A r + hs_m12 M Q e ω L c Θ r * B r) r)
    (hB : HasDerivAt B (hs_m21 M Q e ω L c Θ r * A r + hs_m22 M Q e ω L c r * B r) r) :
    HasDerivAt (hs_sysP Θ A B)
      (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * hs_sysR M Q e ω c Θ A B r) r := by
  have hE := hasDerivAt_exp_phase (M := M) (Q := Q) hΘ
  have hEi := hasDerivAt_exp_neg_phase (M := M) (Q := Q) hΘ
  have h := ((hE.mul hA).add (hEi.mul hB)).div_const 2
  refine h.congr_deriv ?_
  have hκc : ((hs_kap M Q e ω c r : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hκ
  have hrel : ((hs_kap M Q e ω c r : ℝ) : ℂ) = (radialK e ω r : ℂ) + c * delta M Q r := by
    simp only [hs_kap]
    push_cast
    ring
  have hd : (delta M Q r : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ
  have hE0 : exp (I * (Θ r : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hI : I ≠ 0 := I_ne_zero
  simp only [hs_m11, hs_m12, hs_m21, hs_m22, hs_alphaP, hs_alphaM, hs_sysR, phaseRate,
    Complex.exp_neg]
  push_cast
  generalize ((hs_kap M Q e ω c r : ℝ) : ℂ) = κ at hκc hrel ⊢
  generalize exp (I * (Θ r : ℂ)) = E at hE0 ⊢
  field_simp
  subst hrel
  ring_nf
  simp only [I_sq]
  ring

/-! ### The radial solution recovered from the system -/

/-- A solution `(A, B)` of the system on `r > a` gives a solution `R = hs_sysR` of the radial
equation `(ΔR')' + (K²/Δ − L)R = 0` on `r > a`, with `ΔR' = hs_sysP`. -/
theorem hs_radial_of_system {M Q e ω L c : ℝ} {Θ : ℝ → ℝ} {A B : ℝ → ℂ}
    (hκ : ∀ r ∈ Ioi (outerHorizon M Q), hs_kap M Q e ω c r ≠ 0)
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hsys : ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt A (hs_m11 M Q e ω L c r * A r + hs_m12 M Q e ω L c Θ r * B r) r ∧
        HasDerivAt B (hs_m21 M Q e ω L c Θ r * A r + hs_m22 M Q e ω L c r * B r) r) :
    (∀ r ∈ Ioi (outerHorizon M Q),
      deriv (hs_sysR M Q e ω c Θ A B) r = hs_sysP Θ A B r / delta M Q r) ∧
    ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ (hs_sysR M Q e ω c Θ A B) r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv (hs_sysR M Q e ω c Θ A B) s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * hs_sysR M Q e ω c Θ A B r) r := by
  have hderR : ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt (hs_sysR M Q e ω c Θ A B) (hs_sysP Θ A B r / delta M Q r) r :=
    fun r hr => hs_hasDerivAt_sysR (delta_pos_of_lt hr).ne' (hκ r hr) (hΘ r hr) (hsys r hr).1
      (hsys r hr).2
  refine ⟨fun r hr => (hderR r hr).deriv, fun r hr => ⟨(hderR r hr).differentiableAt, ?_⟩⟩
  have hP := hs_hasDerivAt_sysP (delta_pos_of_lt hr).ne' (hκ r hr) (hΘ r hr) (hsys r hr).1
    (hsys r hr).2
  refine hP.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hr] with s hs
  rw [(hderR s hs).deriv]
  have hd : (delta M Q s : ℂ) ≠ 0 := ofReal_ne_zero.2 (delta_pos_of_lt hs).ne'
  field_simp

/-- The horizon amplitudes of `R = hs_sysR`: `e^{−iΘ}(ΔR' + iKR) = A − icΔe^{−iΘ}R` and
`e^{iΘ}(ΔR' − iKR) = B + icΔe^{iΘ}R`. -/
theorem hs_amps_sysR {M Q e ω c : ℝ} {Θ : ℝ → ℝ} {A B : ℝ → ℂ} {r : ℝ}
    (hκ : hs_kap M Q e ω c r ≠ 0)
    (hder : deriv (hs_sysR M Q e ω c Θ A B) r = hs_sysP Θ A B r / delta M Q r)
    (hΔ : delta M Q r ≠ 0) :
    hu_ampOut M Q e ω Θ (hs_sysR M Q e ω c Θ A B) r =
        A r - I * c * delta M Q r * exp (-(I * (Θ r : ℂ))) * hs_sysR M Q e ω c Θ A B r ∧
      hu_ampIn M Q e ω Θ (hs_sysR M Q e ω c Θ A B) r =
        B r + I * c * delta M Q r * exp (I * (Θ r : ℂ)) * hs_sysR M Q e ω c Θ A B r := by
  have hκc : ((hs_kap M Q e ω c r : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 hκ
  have hrel : ((hs_kap M Q e ω c r : ℝ) : ℂ) = (radialK e ω r : ℂ) + c * delta M Q r := by
    simp only [hs_kap]
    push_cast
    ring
  have hd : (delta M Q r : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ
  have hE0 : exp (I * (Θ r : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hI : I ≠ 0 := I_ne_zero
  simp only [hu_ampOut, hu_ampIn, hder, hs_sysR, hs_sysP, Complex.exp_neg]
  generalize ((hs_kap M Q e ω c r : ℝ) : ℂ) = κ at hκc hrel ⊢
  generalize exp (I * (Θ r : ℂ)) = E at hE0 ⊢
  constructor
  · field_simp
    subst hrel
    ring
  · field_simp
    subst hrel
    ring

/-- `κ(a) = K(a)`. -/
theorem hs_kap_outerHorizon (M Q e ω c : ℝ) :
    hs_kap M Q e ω c (outerHorizon M Q) = radialK e ω (outerHorizon M Q) := by
  unfold hs_kap delta
  rw [sub_self, zero_mul, mul_zero, add_zero]

/-- **Conditional existence of the normalized horizon solution.** If `κ = K + cΔ ≠ 0` on `r > a`
and `(A, B)` solves the system on `r > a` with `A → 0` and `B → −2iK(a)` as `r ↓ a`, then
`R = (e^{iΘ}A − e^{−iΘ}B)/(2iκ)` solves the radial equation on `r > a` and satisfies the horizon
condition (1.4) with leading coefficient `1`. -/
theorem hs_exists_horizon_solution_of_system {M Q e ω L c : ℝ}
    (hK : radialK e ω (outerHorizon M Q) ≠ 0)
    (hκ : ∀ r ∈ Ioi (outerHorizon M Q), hs_kap M Q e ω c r ≠ 0) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {A B : ℝ → ℂ}
    (hsys : ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt A (hs_m11 M Q e ω L c r * A r + hs_m12 M Q e ω L c Θ r * B r) r ∧
        HasDerivAt B (hs_m21 M Q e ω L c Θ r * A r + hs_m22 M Q e ω L c r * B r) r)
    (hA : Tendsto A (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (hB : Tendsto B (𝓝[>] (outerHorizon M Q)) (𝓝 (-(2 * I * radialK e ω (outerHorizon M Q))))) :
    ∃ R : ℝ → ℂ, (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) ∧
      (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - 1) =O[𝓝[>] (outerHorizon M Q)]
        (fun r => r - outerHorizon M Q) ∧
      deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) =O[𝓝[>] (outerHorizon M Q)]
        (fun _ => (1 : ℝ)) := by
  obtain ⟨hder, hR⟩ := hs_radial_of_system hκ hΘ hsys
  refine ⟨hs_sysR M Q e ω c Θ A B, hR, ?_⟩
  set a := outerHorizon M Q with ha
  have hev : ∀ᶠ r in 𝓝[>] a, r ∈ Ioi a := self_mem_nhdsWithin
  -- `R = O(1)`
  have hκa : (2 * I * (hs_kap M Q e ω c a : ℂ)) ≠ 0 := by
    rw [hs_kap_outerHorizon]
    exact hs_two_I_mul_ne_zero hK
  have hinv : (fun r => (2 * I * (hs_kap M Q e ω c r : ℂ))⁻¹) =O[𝓝[>] a]
      (fun _ => (1 : ℝ)) := by
    refine hs_isBigO_one_of_continuousAt (ContinuousAt.inv₀ ?_ hκa)
    exact (continuous_const.mul
      (Complex.continuous_ofReal.comp (hs_continuous_kap M Q e ω c))).continuousAt
  have hEA : (fun r => exp (I * (Θ r : ℂ)) * A r) =O[𝓝[>] a] (fun _ => (1 : ℝ)) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => by
      simp only [norm_mul, norm_exp_I_mul, one_mul]) (hA.isBigO_one ℝ)
  have hEB : (fun r => exp (-(I * (Θ r : ℂ))) * B r) =O[𝓝[>] a] (fun _ => (1 : ℝ)) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => by
      simp only [norm_mul, norm_exp_neg_I_mul, one_mul]) (hB.isBigO_one ℝ)
  have hR1 : hs_sysR M Q e ω c Θ A B =O[𝓝[>] a] (fun _ => (1 : ℝ)) := by
    have h := (hEA.sub hEB).mul hinv
    simp only [mul_one] at h
    refine h.congr_left fun r => ?_
    simp only [hs_sysR, div_eq_mul_inv]
  -- the corrections `icΔe^{∓iΘ}R` tend to `0`
  have hΔΔ : (fun r => (delta M Q r : ℂ)) =O[𝓝[>] a] (delta M Q) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => Complex.norm_real _) (isBigO_refl _ _)
  have hΔR := hΔΔ.mul (hR1.const_mul_left (c : ℂ))
  simp only [mul_one] at hΔR
  have hlim0 := hΔR.trans_tendsto (hu_tendsto_delta M Q)
  have hcorr₁ : Tendsto (fun r => I * c * delta M Q r * exp (-(I * (Θ r : ℂ))) *
      hs_sysR M Q e ω c Θ A B r) (𝓝[>] a) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := hlim0.norm
    rw [norm_zero] at h
    refine h.congr' (Eventually.of_forall fun r => ?_)
    simp only [norm_mul, norm_exp_neg_I_mul, Complex.norm_I]
    ring
  have hcorr₂ : Tendsto (fun r => I * c * delta M Q r * exp (I * (Θ r : ℂ)) *
      hs_sysR M Q e ω c Θ A B r) (𝓝[>] a) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := hlim0.norm
    rw [norm_zero] at h
    refine h.congr' (Eventually.of_forall fun r => ?_)
    simp only [norm_mul, norm_exp_I_mul, Complex.norm_I]
    ring
  have hamps : ∀ᶠ r in 𝓝[>] a, _ := hev.mono fun r hr =>
    hs_amps_sysR (hκ r hr) (hder r hr) (delta_pos_of_lt hr).ne'
  have hAo : Tendsto (hu_ampOut M Q e ω Θ (hs_sysR M Q e ω c Θ A B)) (𝓝[>] a) (𝓝 0) := by
    have h := hA.sub hcorr₁
    rw [sub_zero] at h
    exact h.congr' (hamps.mono fun r hr => hr.1.symm)
  have hBi : Tendsto (hu_ampIn M Q e ω Θ (hs_sysR M Q e ω c Θ A B)) (𝓝[>] a)
      (𝓝 (-(2 * I * radialK e ω a))) := by
    have h := hB.add hcorr₂
    rw [add_zero] at h
    exact h.congr' (hamps.mono fun r hr => hr.2.symm)
  exact hs_horizon_condition_of_tendsto_amps hK hΘ hR hAo hBi

/-! ### Continuity and boundedness of the coefficients -/

/-- `κ'` is continuous. -/
theorem hs_continuous_kapD (M e ω c : ℝ) : Continuous (hs_kapD M e ω c) := by
  unfold hs_kapD
  fun_prop

/-- `α₊` and `α₋` are continuous where `κ ≠ 0`. -/
theorem hs_continuousOn_alpha {M Q e ω L c : ℝ} {s : Set ℝ}
    (hκ : ∀ r ∈ s, hs_kap M Q e ω c r ≠ 0) :
    ContinuousOn (hs_alphaP M Q e ω L c) s ∧ ContinuousOn (hs_alphaM M Q e ω L c) s := by
  have hK : Continuous (fun r => ((L + c * radialK e ω r : ℝ) : ℂ)) := by
    unfold radialK
    fun_prop
  have hkD : Continuous (fun r => (hs_kapD M e ω c r : ℂ)) :=
    Complex.continuous_ofReal.comp (hs_continuous_kapD M e ω c)
  have hk : Continuous (fun r => 2 * I * (hs_kap M Q e ω c r : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp (hs_continuous_kap M Q e ω c))
  have hne : ∀ r ∈ s, 2 * I * (hs_kap M Q e ω c r : ℂ) ≠ 0 :=
    fun r hr => hs_two_I_mul_ne_zero (hκ r hr)
  exact ⟨((hK.add (continuous_const.mul hkD)).continuousOn).div hk.continuousOn hne,
    ((hK.sub (continuous_const.mul hkD)).continuousOn).div hk.continuousOn hne⟩

/-- The four coefficients are continuous on `r > a` (`Θ` is differentiable there). -/
theorem hs_continuousOn_coeffs {M Q e ω L c : ℝ} {Θ : ℝ → ℝ}
    (hκ : ∀ r ∈ Ioi (outerHorizon M Q), hs_kap M Q e ω c r ≠ 0)
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r) :
    ContinuousOn (hs_m11 M Q e ω L c) (Ioi (outerHorizon M Q)) ∧
      ContinuousOn (hs_m12 M Q e ω L c Θ) (Ioi (outerHorizon M Q)) ∧
      ContinuousOn (hs_m21 M Q e ω L c Θ) (Ioi (outerHorizon M Q)) ∧
      ContinuousOn (hs_m22 M Q e ω L c) (Ioi (outerHorizon M Q)) := by
  obtain ⟨hP, hM⟩ := hs_continuousOn_alpha (L := L) hκ
  have hΘc : ContinuousOn (fun r => (Θ r : ℂ)) (Ioi (outerHorizon M Q)) := fun r hr =>
    (Complex.continuous_ofReal.continuousAt.comp (hΘ r hr).continuousAt).continuousWithinAt
  have hE : ContinuousOn (fun r => exp (I * (Θ r : ℂ))) (Ioi (outerHorizon M Q)) :=
    (continuousOn_const.mul hΘc).cexp
  have hEi : ContinuousOn (fun r => exp (-(I * (Θ r : ℂ)))) (Ioi (outerHorizon M Q)) :=
    (continuousOn_const.mul hΘc).neg.cexp
  refine ⟨hP.add continuousOn_const, (continuousOn_const.sub hP).mul (hEi.mul hEi),
    (hM.sub continuousOn_const).mul (hE.mul hE), (hM.add continuousOn_const).neg⟩

/-- The four coefficients are bounded on `(a, a + 1]` when `κ ≠ 0` on `[a, a + 1]`. -/
theorem hs_bound_coeffs {M Q e ω L c : ℝ} (Θ : ℝ → ℝ)
    (hκ : ∀ r ∈ Icc (outerHorizon M Q) (outerHorizon M Q + 1), hs_kap M Q e ω c r ≠ 0) :
    ∃ C, ∀ t ∈ Ioc (outerHorizon M Q) (outerHorizon M Q + 1),
      ‖hs_m11 M Q e ω L c t‖ + ‖hs_m12 M Q e ω L c Θ t‖ + ‖hs_m21 M Q e ω L c Θ t‖ +
        ‖hs_m22 M Q e ω L c t‖ ≤ C := by
  obtain ⟨hP, hM⟩ := hs_continuousOn_alpha (L := L) hκ
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hP
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hM
  refine ⟨2 * (C₁ + C₂ + ‖I * (c : ℂ) / 2‖ + ‖I * (c : ℂ) / 2‖), fun t ht => ?_⟩
  have h1 := hC₁ t (Ioc_subset_Icc_self ht)
  have h2 := hC₂ t (Ioc_subset_Icc_self ht)
  have e12 : ‖hs_m12 M Q e ω L c Θ t‖ = ‖I * (c : ℂ) / 2 - hs_alphaP M Q e ω L c t‖ := by
    simp only [hs_m12, norm_mul, norm_exp_neg_I_mul, mul_one]
  have e21 : ‖hs_m21 M Q e ω L c Θ t‖ = ‖hs_alphaM M Q e ω L c t - I * (c : ℂ) / 2‖ := by
    simp only [hs_m21, norm_mul, norm_exp_I_mul, mul_one]
  have e22 : ‖hs_m22 M Q e ω L c t‖ = ‖hs_alphaM M Q e ω L c t + I * (c : ℂ) / 2‖ := by
    simp only [hs_m22, norm_neg]
  rw [e12, e21, e22, hs_m11]
  have := norm_add_le (hs_alphaP M Q e ω L c t) (I * (c : ℂ) / 2)
  have := norm_sub_le (I * (c : ℂ) / 2) (hs_alphaP M Q e ω L c t)
  have := norm_sub_le (hs_alphaM M Q e ω L c t) (I * (c : ℂ) / 2)
  have := norm_add_le (hs_alphaM M Q e ω L c t) (I * (c : ℂ) / 2)
  linarith

end ModeStability.AllAngular

end
