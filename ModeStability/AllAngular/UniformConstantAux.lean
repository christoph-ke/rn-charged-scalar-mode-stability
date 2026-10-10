module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.AllAngular.StaticSolutionAA
public import ModeStability.AllAngular.NormalizationFacts

/-!
# Helpers for the uniform constant (4.7) of the all-angular paper

Source: the all-angular research notes in preparation, p. 6, the uniform angular-momentum bound,
(4.7); the coefficients (2.3), (2.5)–(2.7) on p. 2.

* `scalarChi`, `scalarH`, `scalarA₀`: `χ = 0` (`r₀ < 2M`) or `χ = h⁻¹` (`r₀ ≥ 2M`) of (2.3),
  `H = ΔK' − 2χK` of (2.5) and `A₀ = 2Δ²K'² − 2Δ(χ + z)KK' − Δ²KK'' + 2χ²K²` of (2.6), written
  in `r` (`K' = 2ωr − e`, `K'' = 2ω`, `z = r − M`, `r₀ = e/ω`).
* `uc_exists_lower_bound`: a continuous positive function on `(a, ∞)` that is bounded below by
  positive constants near both ends is bounded below by a positive constant (compactness on the
  middle part).
* `uc_tendsto_horizon_static`: `Δh → 0` and `Δh²z → 0` as `r ↓ a`, for `δ > 0` (where
  `h = (2δ)⁻¹ log((r − b)/(r − a))`, via `t log t → 0` and `t log² t → 0`) and for `δ = 0` (where
  `h = 1/(r − M)`).
* `uc_div_sq_eq`, `uc_constant_horizon_alg`, `uc_constant_infinity_alg`,
  `uc_reciprocal_horizon_alg`, `uc_reciprocal_infinity_alg`: the algebra behind the endpoint
  asymptotics of `a_k = A₀/H²` in the two normalizations.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

/-! ### The scalar coefficients `χ`, `H`, `A₀` in `r` -/

/-- `χ = −Δg'/g` of (2.3) for the normalization (2.2): `χ = 0` if `r₀ = e/ω < 2M` (`g = 1`) and
`χ = h⁻¹` if `r₀ ≥ 2M` (`g = h`). -/
@[expose] noncomputable def scalarChi (M Q e ω r : ℝ) : ℝ :=
  if e / ω < 2 * M then 0 else 1 / staticSolutionAA M Q r

/-- `H = ΔK' − 2χK` of (2.5), with `K' = 2ωr − e`. -/
@[expose] noncomputable def scalarH (M Q e ω r : ℝ) : ℝ :=
  delta M Q r * (2 * ω * r - e) - 2 * scalarChi M Q e ω r * radialK e ω r

/-- `A₀ = 2Δ²K'² − 2Δ(χ + z)KK' − Δ²KK'' + 2χ²K²` of (2.6), with `K' = 2ωr − e`, `K'' = 2ω`,
`z = r − M`. -/
@[expose] noncomputable def scalarA₀ (M Q e ω r : ℝ) : ℝ :=
  2 * delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
      2 * delta M Q r * (scalarChi M Q e ω r + (r - M)) * radialK e ω r * (2 * ω * r - e) -
    delta M Q r ^ 2 * radialK e ω r * (2 * ω) + 2 * scalarChi M Q e ω r ^ 2 * radialK e ω r ^ 2

/-- `χ = 0` for `g = 1` (`r₀ < 2M`). -/
theorem scalarChi_of_lt {M Q e ω : ℝ} (h : e / ω < 2 * M) (r : ℝ) : scalarChi M Q e ω r = 0 := by
  unfold scalarChi
  rw [ite_eq_left h]

/-- `χ = h⁻¹` for `g = h` (`r₀ ≥ 2M`). -/
theorem scalarChi_of_not_lt {M Q e ω : ℝ} (h : ¬ e / ω < 2 * M) (r : ℝ) :
    scalarChi M Q e ω r = 1 / staticSolutionAA M Q r := by
  unfold scalarChi
  rw [ite_eq_right h]

/-! ### A positive lower bound from the two ends -/

/-- A function that is continuous and positive on `(a, ∞)`, bounded below by `c₁ > 0` near `a`
and by `c₂ > 0` near `∞`, is bounded below on `(a, ∞)` by a positive constant. -/
theorem uc_exists_lower_bound {f : ℝ → ℝ} {a c₁ c₂ : ℝ} (hf : ContinuousOn f (Ioi a))
    (hpos : ∀ r ∈ Ioi a, 0 < f r) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h₁ : ∀ᶠ r in 𝓝[>] a, c₁ ≤ f r) (h₂ : ∀ᶠ r in atTop, c₂ ≤ f r) :
    ∃ c, 0 < c ∧ ∀ r ∈ Ioi a, c ≤ f r := by
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h₁
  obtain ⟨R, hR⟩ := eventually_atTop.1 h₂
  have hne : (Icc r₁ (max R r₁)).Nonempty := nonempty_Icc.2 (le_max_right _ _)
  have hKs : Icc r₁ (max R r₁) ⊆ Ioi a := fun x hx => lt_of_lt_of_le (mem_Ioi.1 hr₁) hx.1
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne (hf.mono hKs)
  refine ⟨min (min c₁ c₂) (f x₀), lt_min (lt_min hc₁ hc₂) (hpos x₀ (hKs hx₀)), fun r hr => ?_⟩
  rcases lt_or_ge r r₁ with h | h
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans (hsub ⟨hr, h⟩))
  rcases le_or_gt r (max R r₁) with h' | h'
  · exact (min_le_right _ _).trans (hmin (show r ∈ Icc r₁ (max R r₁) from ⟨h, h'⟩))
  · exact (min_le_left _ _).trans
      ((min_le_right _ _).trans (hR r ((le_max_left _ _).trans h'.le)))

/-! ### Limits at the horizon -/

/-- `r − a → 0⁺` as `r ↓ a`. -/
theorem uc_tendsto_sub_nhdsGT (a : ℝ) : Tendsto (fun r : ℝ => r - a) (𝓝[>] a) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun r : ℝ => r - a) (𝓝 a) (𝓝 (a - a)) := (continuous_sub_right a).tendsto a
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact sub_pos.2 hr

/-- `t log t → 0` as `t ↓ 0`. -/
theorem uc_tendsto_mul_log : Tendsto (fun t : ℝ => t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
  refine (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).congr fun t => ?_
  rw [Real.rpow_one, mul_comm]

/-- `t log² t → 0` as `t ↓ 0`. -/
theorem uc_tendsto_mul_log_sq : Tendsto (fun t : ℝ => t * Real.log t ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1 / 2)).pow 2
  rw [zero_pow two_ne_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (mem_Ioi.1 ht).le, mul_comm]

/-- `Δh → 0` and `Δh²z → 0` as `r ↓ a`, for the static solution `h` of (2.1) and `z = r − M`. -/
theorem uc_tendsto_horizon_static {M Q : ℝ} (hQ : |Q| ≤ M) :
    Tendsto (fun r => delta M Q r * staticSolutionAA M Q r) (𝓝[>] (outerHorizon M Q)) (𝓝 0) ∧
      Tendsto (fun r => delta M Q r * staticSolutionAA M Q r ^ 2 * (r - M))
        (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
  by_cases hδ : 0 < M ^ 2 - Q ^ 2
  · have hs : 0 < Real.sqrt (M ^ 2 - Q ^ 2) := Real.sqrt_pos.2 hδ
    have hab : outerHorizon M Q - innerHorizon M Q = 2 * Real.sqrt (M ^ 2 - Q ^ 2) := by
      unfold outerHorizon innerHorizon
      ring
    have hab0 : outerHorizon M Q - innerHorizon M Q ≠ 0 := by rw [hab]; positivity
    have hσ := uc_tendsto_sub_nhdsGT (outerHorizon M Q)
    have hσ0 : Tendsto (fun r => r - outerHorizon M Q) (𝓝[>] (outerHorizon M Q)) (𝓝 0) :=
      hσ.mono_right nhdsWithin_le_nhds
    have hL1 := uc_tendsto_mul_log.comp hσ
    have hL2 := uc_tendsto_mul_log_sq.comp hσ
    have hrb : Tendsto (fun r => r - innerHorizon M Q) (𝓝[>] (outerHorizon M Q))
        (𝓝 (outerHorizon M Q - innerHorizon M Q)) :=
      ((continuous_sub_right _).tendsto _).mono_left nhdsWithin_le_nhds
    have hrM : Tendsto (fun r => r - M) (𝓝[>] (outerHorizon M Q)) (𝓝 (outerHorizon M Q - M)) :=
      ((continuous_sub_right _).tendsto _).mono_left nhdsWithin_le_nhds
    have hlogb : Tendsto (fun r => Real.log (r - innerHorizon M Q)) (𝓝[>] (outerHorizon M Q))
        (𝓝 (Real.log (outerHorizon M Q - innerHorizon M Q))) :=
      (Real.continuousAt_log hab0).tendsto.comp hrb
    have hp := (hσ0.mul hlogb).sub hL1
    have hq := ((hσ0.mul (hlogb.pow 2)).sub ((tendsto_const_nhds (x := (2 : ℝ))).mul
      hlogb |>.mul hL1)).add hL2
    simp only [zero_mul, mul_zero, sub_zero, add_zero, Function.comp_apply] at hp hq
    have key : ∀ r ∈ Ioi (outerHorizon M Q), staticSolutionAA M Q r =
        1 / (2 * Real.sqrt (M ^ 2 - Q ^ 2)) *
          (Real.log (r - innerHorizon M Q) - Real.log (r - outerHorizon M Q)) := by
      intro r hr
      have hra : 0 < r - outerHorizon M Q := sub_pos.2 hr
      have hrb' : 0 < r - innerHorizon M Q := by linarith
      unfold staticSolutionAA
      rw [ite_eq_left hδ, Real.log_div hrb'.ne' hra.ne']
    constructor
    · have h := (hrb.div_const (2 * Real.sqrt (M ^ 2 - Q ^ 2))).mul hp
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [key r hr]
      unfold delta
      field_simp
    · have h := ((hrb.mul hrM).div_const (4 * (M ^ 2 - Q ^ 2))).mul hq
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [key r hr]
      unfold delta
      have hs2 : Real.sqrt (M ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - Q ^ 2 := Real.sq_sqrt hδ.le
      field_simp
      rw [hs2]
      ring
  · obtain ⟨-, -, ha, hb⟩ := NormalizationFacts.extremal_facts hQ hδ
    rw [NormalizationFacts.staticSolutionAA_eq_extremal hδ, ha]
    have hσ0 : Tendsto (fun r => r - M) (𝓝[>] M) (𝓝 0) :=
      (uc_tendsto_sub_nhdsGT M).mono_right nhdsWithin_le_nhds
    have hev : ∀ r ∈ Ioi M, delta M Q r = (r - M) ^ 2 := by
      intro r _
      unfold delta
      rw [ha, hb]
      ring
    constructor
    · refine hσ0.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : r - M ≠ 0 := (sub_pos.2 hr).ne'
      rw [hev r hr]
      field_simp
    · refine hσ0.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : r - M ≠ 0 := (sub_pos.2 hr).ne'
      rw [hev r hr]
      field_simp

/-! ### The algebra of the endpoint asymptotics -/

/-- `N/D² = xᵐ (P/S²)` when `N = x^(m + 2n) P` and `D = xⁿ S`, `x ≠ 0`. -/
theorem uc_div_sq_eq {N D P S x : ℝ} (m n : ℕ) (hx : x ≠ 0) (hN : N = x ^ (m + 2 * n) * P)
    (hD : D = x ^ n * S) : N / D ^ 2 = x ^ m * (P / S ^ 2) := by
  subst hN hD
  by_cases hS : S = 0
  · simp [hS]
  · rw [mul_pow, ← pow_mul, pow_add, mul_comm n 2]
    field_simp

/-- `g = 1` near the horizon: `A₀/H² = (2 − 2ωK/K'²) + (z/Δ)(−2K/K')` for `χ = 0`. -/
theorem uc_constant_horizon_alg {Δ z K K' ω : ℝ} (hΔ : Δ ≠ 0) (hK' : K' ≠ 0) :
    (2 * Δ ^ 2 * K' ^ 2 - 2 * Δ * (0 + z) * K * K' - Δ ^ 2 * K * (2 * ω) + 2 * 0 ^ 2 * K ^ 2) /
        (Δ * K' - 2 * 0 * K) ^ 2 =
      (2 - 2 * ω * K / K' ^ 2) + z / Δ * (-2 * K / K') := by
  field_simp
  ring

/-- `g = 1` at infinity: with `u = r⁻¹`, `A₀ = r⁶ P₆(u)` and `H = r³ S(u)`, where
`S(u) = (1 − 2Mu + Q²u²)(2ω − eu)`. -/
theorem uc_constant_infinity_alg {M Q e ω r Δ K : ℝ} (hr : r ≠ 0)
    (hΔ : Δ = (r - M) ^ 2 - (M ^ 2 - Q ^ 2)) (hK : K = ω * r ^ 2 - e * r) :
    2 * Δ ^ 2 * (2 * ω * r - e) ^ 2 - 2 * Δ * (0 + (r - M)) * K * (2 * ω * r - e) -
          Δ ^ 2 * K * (2 * ω) + 2 * 0 ^ 2 * K ^ 2 =
        r ^ (0 + 2 * 3) *
          (2 * (1 - 2 * M * r⁻¹ + Q ^ 2 * r⁻¹ ^ 2) ^ 2 * (2 * ω - e * r⁻¹) ^ 2 -
            2 * (1 - 2 * M * r⁻¹ + Q ^ 2 * r⁻¹ ^ 2) * (1 - M * r⁻¹) * (ω - e * r⁻¹) *
              (2 * ω - e * r⁻¹) -
            2 * ω * (1 - 2 * M * r⁻¹ + Q ^ 2 * r⁻¹ ^ 2) ^ 2 * (ω - e * r⁻¹)) ∧
      Δ * (2 * ω * r - e) - 2 * 0 * K =
        r ^ 3 * ((1 - 2 * M * r⁻¹ + Q ^ 2 * r⁻¹ ^ 2) * (2 * ω - e * r⁻¹)) := by
  subst hΔ hK
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- `g = h` near the horizon: with `χ = 1/h`, `p = Δh`, `q = Δh²z`,
`A₀/H² = N/D²` with `N = 2p²K'² − 2pKK' − 2qKK' − 2ωp²K + 2K²` and `D = pK' − 2K`. -/
theorem uc_reciprocal_horizon_alg {Δ h z K K' ω : ℝ} (hh : h ≠ 0) :
    (2 * Δ ^ 2 * K' ^ 2 - 2 * Δ * (1 / h + z) * K * K' - Δ ^ 2 * K * (2 * ω) +
          2 * (1 / h) ^ 2 * K ^ 2) / (Δ * K' - 2 * (1 / h) * K) ^ 2 =
      (2 * (Δ * h) ^ 2 * K' ^ 2 - 2 * (Δ * h) * K * K' - 2 * (Δ * h ^ 2 * z) * K * K' -
          2 * ω * (Δ * h) ^ 2 * K + 2 * K ^ 2) / ((Δ * h) * K' - 2 * K) ^ 2 := by
  have hN : 2 * Δ ^ 2 * K' ^ 2 - 2 * Δ * (1 / h + z) * K * K' - Δ ^ 2 * K * (2 * ω) +
        2 * (1 / h) ^ 2 * K ^ 2 =
      (2 * (Δ * h) ^ 2 * K' ^ 2 - 2 * (Δ * h) * K * K' - 2 * (Δ * h ^ 2 * z) * K * K' -
          2 * ω * (Δ * h) ^ 2 * K + 2 * K ^ 2) / h ^ 2 := by
    field_simp
    ring
  have hD : Δ * K' - 2 * (1 / h) * K = ((Δ * h) * K' - 2 * K) / h := by
    field_simp
  rw [hN, hD, div_pow, div_div_div_cancel_right₀ (pow_ne_zero 2 hh)]

/-- The polynomial `P₄(u, ε)` of the reciprocal normalization at infinity (`u = r⁻¹`,
`χ = z − ε`): `A₀ = r⁵ · 2ω(e − 2Mω) + r⁴ P₄(u, ε)`. -/
@[expose] noncomputable def ucP4 (M Q e ω u ε : ℝ) : ℝ :=
  (10 * M ^ 2 * ω ^ 2 - 4 * M * e * ω - 4 * M * ε * ω ^ 2 + 4 * Q ^ 2 * ω ^ 2 + 2 * e * ε * ω +
      2 * ε ^ 2 * ω ^ 2) +
    (-4 * M ^ 2 * e * ω - 16 * M * Q ^ 2 * ω ^ 2 + 4 * M * e * ε * ω + 4 * Q ^ 2 * ε * ω ^ 2 -
      2 * e ^ 2 * ε - 4 * e * ε ^ 2 * ω) * u +
    (2 * M ^ 2 * e ^ 2 + 12 * M * Q ^ 2 * e * ω + 6 * Q ^ 4 * ω ^ 2 - 6 * Q ^ 2 * e * ε * ω +
      2 * e ^ 2 * ε ^ 2) * u ^ 2 +
    (-4 * M * Q ^ 2 * e ^ 2 - 6 * Q ^ 4 * e * ω + 2 * Q ^ 2 * e ^ 2 * ε) * u ^ 3 +
    2 * Q ^ 4 * e ^ 2 * u ^ 4

/-- `g = h` at infinity: with `χ = z − ε`, `A₀ = r⁵ · 2ωC + r⁴ P₄(r⁻¹, ε)` and
`H = r²(C + 2εω) + r(2Q²ω − 2eε) − Q²e`, where `C = e − 2Mω`. -/
theorem uc_reciprocal_infinity_alg {M Q e ω r Δ K ε : ℝ} (hr : r ≠ 0)
    (hΔ : Δ = (r - M) ^ 2 - (M ^ 2 - Q ^ 2)) (hK : K = ω * r ^ 2 - e * r) :
    2 * Δ ^ 2 * (2 * ω * r - e) ^ 2 -
          2 * Δ * ((r - M - ε) + (r - M)) * K * (2 * ω * r - e) -
          Δ ^ 2 * K * (2 * ω) + 2 * (r - M - ε) ^ 2 * K ^ 2 =
        r ^ 5 * (2 * ω * (e - 2 * M * ω)) + r ^ 4 * ucP4 M Q e ω r⁻¹ ε ∧
      Δ * (2 * ω * r - e) - 2 * (r - M - ε) * K =
        r ^ 2 * ((e - 2 * M * ω) + 2 * ε * ω) + r * (2 * Q ^ 2 * ω - 2 * e * ε) - Q ^ 2 * e := by
  subst hΔ hK
  constructor
  · unfold ucP4
    field_simp
    ring
  · ring

end ModeStability.AllAngular

end
