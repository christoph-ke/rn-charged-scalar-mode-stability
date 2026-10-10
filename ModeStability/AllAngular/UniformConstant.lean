module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.AllAngular.StaticSolutionAA
public import ModeStability.Frozen.AllAngular.NormalizationG
public import ModeStability.Frozen.AllAngular.XDeriv
public import ModeStability.Frozen.AllAngular.EffectiveK
public import ModeStability.Frozen.AllAngular.CommonGeometry
public import ModeStability.Frozen.AllAngular.ScalarPositivity
public import ModeStability.Frozen.AllAngular.AngularPositivity
public import ModeStability.AllAngular.NormalizationFacts
public import ModeStability.AllAngular.UniformConstantAux

/-!
# The constant (4.7), uniform in angular momentum

Source: the all-angular research notes in preparation, p. 6, the uniform angular-momentum bound,
the table of endpoint limits and (4.7); with Lemma 2.2 (p. 3), (2.7) (p. 2) and
Proposition 3.1, (3.4) (p. 4).

In the strictly superradiant range (1.7) (`0 < M`, `|Q| ≤ M`, `ω > 0`, `r₀ = e/ω > a`), with the
normalization `g` of (2.2), `k = g²K` and `∂ₓ = Δg²∂ᵣ` (`xDeriv`), the coefficient
`a_k = E_k/k_x² = (2k_x² − k k_xx)/k_x²` (`scalarCoeffRatio`, a function of `r`) equals `A₀/H²`
on the exterior (Lemma 2.2's identities (2.7), `scalarCoeffRatio_eq`), and has the endpoint
limits of the paper's table:

* `g = 1` (`r₀ < 2M`): `a_k → +∞` as `r ↓ a` (`tendsto_scalarCoeffRatio_horizon_of_lt`) and
  `a_k → 1/2` as `r → ∞` (`tendsto_scalarCoeffRatio_atTop_of_lt`);
* `g = h` (`r₀ ≥ 2M`): `a_k → 1/2` as `r ↓ a` (`tendsto_scalarCoeffRatio_horizon_of_le`) and
  `a_k → +∞` as `r → ∞` (`tendsto_scalarCoeffRatio_atTop_of_le`).

Since `a_k` is continuous and positive on `(a, ∞)` (Lemma 2.2), its infimum
`c_* = uniformConstant` lies in `(0, 1/2]`, and by (3.4), `a_k̂ ≥ min{a_k, 2} ≥ c_*` for every
`L ≥ 0` on the allowed set `LΔ < K²` (`uniformConstant_spec`, `exists_uniform_constant`).

The asymptotics: for `g = 1` (`χ = 0`), `a_k = 2 − 2ωK/K'² + (z/Δ)(−2K/K')` with `z/Δ → +∞` at
the horizon (`K(a) < 0 < K'(a)`), and `A₀ = r⁶P₆(1/r)`, `H = r³S(1/r)`, `P₆(0)/S(0)² = 1/2` at
infinity. For `g = h` (`χ = 1/h`), `a_k = A₀h²/(Hh)²` is a rational function of `Δh → 0`,
`Δh²z → 0` and `r` at the horizon, with limit `2K(a)²/(2K(a))²`; at infinity, with
`ε = z − χ ∈ [0, δ²/z]` (Lemma 2.1) and `C = e − 2Mω ≥ 0`, `A₀ = 2ωCr⁵ + r⁴P₄(1/r, ε)` and
`H = Cr² + O(r)`, so `a_k ~ (2ω/C) r` if `C > 0`, and `a_k ≥ P₄/B² · r²` with `P₄ → (2M² + 4Q²)ω²`
if `C = 0` (the interface `r₀ = 2M`).
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

/-- The coefficient `a_k = E_k/k_x² = (2k_x² − k k_xx)/k_x²` of (3.4) and (4.7) for `L = 0`,
`k = g²K`, with `g` the normalization (2.2) and `∂ₓ = Δg²∂ᵣ` (`xDeriv`), as a function of `r`. -/
@[expose] noncomputable def scalarCoeffRatio (M Q e ω r : ℝ) : ℝ :=
  (2 * xDeriv M Q (normalizationG M Q e ω)
        (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s) r ^ 2 -
      normalizationG M Q e ω r ^ 2 * radialK e ω r *
        xDeriv M Q (normalizationG M Q e ω)
          (xDeriv M Q (normalizationG M Q e ω)
            (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s)) r) /
    xDeriv M Q (normalizationG M Q e ω)
      (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s) r ^ 2

/-! ### The explicit form `a_k = A₀/H²`, positivity and continuity -/

/-- By (2.7), `a_k = g⁸A₀/(g⁴H)² = A₀/H²` on the exterior. -/
theorem scalarCoeffRatio_eq {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) {r : ℝ}
    (hr : outerHorizon M Q < r) :
    scalarCoeffRatio M Q e ω r = scalarA₀ M Q e ω r / scalarH M Q e ω r ^ 2 := by
  obtain ⟨c, hc, hg, hχ⟩ := NormalizationFacts.gauge_facts (e := e) (ω := ω) hM hQ hr
  obtain ⟨h1, h2⟩ := NormalizationFacts.xDeriv_k (e := e) (ω := ω)
    (NormalizationFacts.delta_pos_of_outerHorizon_lt hr).ne' hg.ne' hc
  have hχ' : -c / normalizationG M Q e ω r = scalarChi M Q e ω r := hχ
  unfold scalarCoeffRatio
  rw [h2, h1, hχ']
  unfold scalarA₀ scalarH
  rw [show ∀ G X : ℝ, (G ^ 4 * X) ^ 2 = G ^ 8 * X ^ 2 from fun G X => by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hg.ne')

/-- Lemma 2.2: `H > 0` and `A₀ > 0` on the exterior. -/
theorem scalarH_pos_and_scalarA₀_pos {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) {r : ℝ} (hr : outerHorizon M Q < r) :
    0 < scalarH M Q e ω r ∧ 0 < scalarA₀ M Q e ω r := by
  obtain ⟨h1, h2, -, -⟩ := scalar_positivity M Q e ω hM hQ hω (e / ω) rfl ha r hr
  exact ⟨h1, h2⟩

/-- `A₀/H²` is continuous on the exterior. -/
theorem continuousOn_scalarA₀_div {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) :
    ContinuousOn (fun r => scalarA₀ M Q e ω r / scalarH M Q e ω r ^ 2)
      (Ioi (outerHorizon M Q)) := by
  intro r hr
  have hχ : ContinuousAt (fun s => scalarChi M Q e ω s) r := by
    by_cases h : e / ω < 2 * M
    · simp only [scalarChi_of_lt h]
      exact continuousAt_const
    · simp only [scalarChi_of_not_lt h]
      exact continuousAt_const.div
        (NormalizationFacts.hasDerivAt_staticSolutionAA hM hQ hr).continuousAt
        (NormalizationFacts.staticSolutionAA_pos hM hr).ne'
  have hA : ContinuousAt (fun s => scalarA₀ M Q e ω s) r := by
    unfold scalarA₀ delta radialK
    fun_prop
  have hH : ContinuousAt (fun s => scalarH M Q e ω s) r := by
    unfold scalarH delta radialK
    fun_prop
  exact (hA.div (hH.pow 2)
    (pow_pos (scalarH_pos_and_scalarA₀_pos hM hQ hω ha hr).1 2).ne').continuousWithinAt

/-! ### The endpoint limits for `g = 1` (`a < r₀ < 2M`) -/

/-- `g = 1`: `a_k → +∞` as `r ↓ a`. -/
theorem tendsto_scalarCoeffRatio_horizon_of_lt {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hω : 0 < ω) (ha : outerHorizon M Q < e / ω) (h2M : e / ω < 2 * M) :
    Tendsto (scalarCoeffRatio M Q e ω) (𝓝[>] (outerHorizon M Q)) atTop := by
  have hMa : M ≤ outerHorizon M Q := by
    unfold outerHorizon
    linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
  have hab : outerHorizon M Q + innerHorizon M Q = 2 * M := by
    unfold outerHorizon innerHorizon
    ring
  have hba : innerHorizon M Q ≤ outerHorizon M Q := by
    unfold outerHorizon innerHorizon
    linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
  have he : e < 2 * M * ω := (div_lt_iff₀ hω).1 h2M
  have hae : outerHorizon M Q * ω < e := (lt_div_iff₀ hω).1 ha
  have hK1a : 0 < 2 * ω * outerHorizon M Q - e := by nlinarith
  have hKa : radialK e ω (outerHorizon M Q) < 0 := by
    unfold radialK
    nlinarith
  have hKc : Continuous (fun r => radialK e ω r) := by
    unfold radialK
    fun_prop
  have hK1c : Continuous (fun r : ℝ => 2 * ω * r - e) := by fun_prop
  have hf1 : Tendsto (fun r => 2 - 2 * ω * radialK e ω r / (2 * ω * r - e) ^ 2)
      (𝓝[>] (outerHorizon M Q))
      (𝓝 (2 - 2 * ω * radialK e ω (outerHorizon M Q) /
        (2 * ω * outerHorizon M Q - e) ^ 2)) :=
    (tendsto_const_nhds.sub ((tendsto_const_nhds.mul (hKc.tendsto _)).div
      ((hK1c.tendsto _).pow 2) (pow_pos hK1a 2).ne')).mono_left nhdsWithin_le_nhds
  have hf3 : Tendsto (fun r => -2 * radialK e ω r / (2 * ω * r - e)) (𝓝[>] (outerHorizon M Q))
      (𝓝 (-2 * radialK e ω (outerHorizon M Q) / (2 * ω * outerHorizon M Q - e))) :=
    ((tendsto_const_nhds.mul (hKc.tendsto _)).div (hK1c.tendsto _) hK1a.ne').mono_left
      nhdsWithin_le_nhds
  have hf3pos : 0 < -2 * radialK e ω (outerHorizon M Q) / (2 * ω * outerHorizon M Q - e) :=
    div_pos (by linarith) hK1a
  have hf2 : Tendsto (fun r => (r - M) / delta M Q r) (𝓝[>] (outerHorizon M Q)) atTop := by
    have hinv := (tendsto_inv_nhdsGT_zero.comp
      (uc_tendsto_sub_nhdsGT (outerHorizon M Q))).const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    refine tendsto_atTop_mono' _ ?_ hinv
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hra : 0 < r - outerHorizon M Q := sub_pos.2 hr
    have hrb : 0 < r - innerHorizon M Q := by linarith [mem_Ioi.1 hr]
    have hsplit : (r - M) / delta M Q r =
        1 / 2 * (r - outerHorizon M Q)⁻¹ + 1 / 2 * (r - innerHorizon M Q)⁻¹ := by
      unfold delta
      field_simp
      linarith
    change 1 / 2 * (r - outerHorizon M Q)⁻¹ ≤ _
    rw [hsplit]
    linarith [inv_pos.2 hrb]
  refine (hf1.add_atTop (hf2.atTop_mul_pos hf3pos hf3)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hΔ := NormalizationFacts.delta_pos_of_outerHorizon_lt hr
  have hK1 : 0 < 2 * ω * r - e := by nlinarith [mem_Ioi.1 hr]
  rw [scalarCoeffRatio_eq hM hQ hr]
  unfold scalarA₀ scalarH
  rw [scalarChi_of_lt h2M]
  exact (uc_constant_horizon_alg hΔ.ne' hK1.ne').symm

/-- `g = 1`: `a_k → 1/2` as `r → ∞`. -/
theorem tendsto_scalarCoeffRatio_atTop_of_lt {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hω : 0 < ω) (h2M : e / ω < 2 * M) :
    Tendsto (scalarCoeffRatio M Q e ω) atTop (𝓝 (1 / 2)) := by
  have hS0 : ((1 - 2 * M * 0 + Q ^ 2 * 0 ^ 2) * (2 * ω - e * 0)) ^ 2 ≠ 0 := by
    norm_num
    exact hω.ne'
  have hcont : ContinuousAt (fun u : ℝ =>
      (2 * (1 - 2 * M * u + Q ^ 2 * u ^ 2) ^ 2 * (2 * ω - e * u) ^ 2 -
          2 * (1 - 2 * M * u + Q ^ 2 * u ^ 2) * (1 - M * u) * (ω - e * u) * (2 * ω - e * u) -
          2 * ω * (1 - 2 * M * u + Q ^ 2 * u ^ 2) ^ 2 * (ω - e * u)) /
        ((1 - 2 * M * u + Q ^ 2 * u ^ 2) * (2 * ω - e * u)) ^ 2) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) hS0
  have hlim := hcont.tendsto.comp tendsto_inv_atTop_zero
  have hval : (2 * (1 - 2 * M * 0 + Q ^ 2 * 0 ^ 2) ^ 2 * (2 * ω - e * 0) ^ 2 -
          2 * (1 - 2 * M * 0 + Q ^ 2 * 0 ^ 2) * (1 - M * 0) * (ω - e * 0) * (2 * ω - e * 0) -
          2 * ω * (1 - 2 * M * 0 + Q ^ 2 * 0 ^ 2) ^ 2 * (ω - e * 0)) /
        ((1 - 2 * M * 0 + Q ^ 2 * 0 ^ 2) * (2 * ω - e * 0)) ^ 2 = (1 : ℝ) / 2 := by
    have := hω.ne'
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
  have hr0 : r ≠ 0 := (lt_of_lt_of_le hM (by
    have := NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr
    linarith)).ne'
  rw [Function.comp_apply, scalarCoeffRatio_eq hM hQ hr]
  unfold scalarA₀ scalarH
  rw [scalarChi_of_lt h2M]
  obtain ⟨h1, h2⟩ := uc_constant_infinity_alg (e := e) (ω := ω) (K := radialK e ω r) hr0
    (CoefficientIdentities.delta_eq_sq_sub hQ r) rfl
  rw [uc_div_sq_eq 0 3 hr0 h1 h2, pow_zero, one_mul]

/-! ### The endpoint limits for `g = h` (`r₀ ≥ 2M`) -/

/-- `g = h`: `a_k → 1/2` as `r ↓ a`. -/
theorem tendsto_scalarCoeffRatio_horizon_of_le {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hω : 0 < ω) (ha : outerHorizon M Q < e / ω) (h2M : 2 * M ≤ e / ω) :
    Tendsto (scalarCoeffRatio M Q e ω) (𝓝[>] (outerHorizon M Q)) (𝓝 (1 / 2)) := by
  have h2M' : ¬ e / ω < 2 * M := not_lt.2 h2M
  have hMa : M ≤ outerHorizon M Q := by
    unfold outerHorizon
    linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
  have hae : outerHorizon M Q * ω < e := (lt_div_iff₀ hω).1 ha
  have hKa : radialK e ω (outerHorizon M Q) ≠ 0 := by
    unfold radialK
    nlinarith
  obtain ⟨hp, hq⟩ := uc_tendsto_horizon_static (M := M) hQ
  have hφ := hp.prodMk_nhds (hq.prodMk_nhds
    ((tendsto_id (x := 𝓝 (outerHorizon M Q))).mono_left nhdsWithin_le_nhds))
  have hF : ContinuousAt (fun x : ℝ × ℝ × ℝ =>
      (2 * x.1 ^ 2 * (2 * ω * x.2.2 - e) ^ 2 - 2 * x.1 * radialK e ω x.2.2 * (2 * ω * x.2.2 - e) -
          2 * x.2.1 * radialK e ω x.2.2 * (2 * ω * x.2.2 - e) -
          2 * ω * x.1 ^ 2 * radialK e ω x.2.2 + 2 * radialK e ω x.2.2 ^ 2) /
        (x.1 * (2 * ω * x.2.2 - e) - 2 * radialK e ω x.2.2) ^ 2) (0, 0, outerHorizon M Q) := by
    refine ContinuousAt.div ?_ ?_ ?_
    · unfold radialK
      fun_prop
    · unfold radialK
      fun_prop
    · simpa using hKa
  have hlim := hF.tendsto.comp hφ
  have hval : (2 * (0 : ℝ) ^ 2 * (2 * ω * outerHorizon M Q - e) ^ 2 -
          2 * 0 * radialK e ω (outerHorizon M Q) * (2 * ω * outerHorizon M Q - e) -
          2 * 0 * radialK e ω (outerHorizon M Q) * (2 * ω * outerHorizon M Q - e) -
          2 * ω * 0 ^ 2 * radialK e ω (outerHorizon M Q) + 2 * radialK e ω (outerHorizon M Q) ^ 2) /
        (0 * (2 * ω * outerHorizon M Q - e) - 2 * radialK e ω (outerHorizon M Q)) ^ 2 = 1 / 2 := by
    field_simp
    ring
  simp only at hlim
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hh := (NormalizationFacts.staticSolutionAA_pos hM hr).ne'
  dsimp only [Function.comp_apply, id]
  rw [scalarCoeffRatio_eq hM hQ hr]
  unfold scalarA₀ scalarH
  rw [scalarChi_of_not_lt h2M', uc_reciprocal_horizon_alg hh]

/-- `r⁵X + r⁴P = r⁵(X + r⁻¹P)`. -/
private theorem uc_pow_five_add {r X P : ℝ} (hr : r ≠ 0) :
    r ^ 5 * X + r ^ 4 * P = r ^ (1 + 2 * 2) * (X + r⁻¹ * P) := by
  field_simp
  ring

/-- `r²A + rB − c = r²(A + Br⁻¹ − cr⁻²)`. -/
private theorem uc_quad_eq {r A B c : ℝ} (hr : r ≠ 0) :
    r ^ 2 * A + r * B - c = r ^ 2 * (A + B * r⁻¹ - c * r⁻¹ ^ 2) := by
  field_simp

/-- `r²A + rB − c = r(rA + B − cr⁻¹)`. -/
private theorem uc_lin_eq {r A B c : ℝ} (hr : r ≠ 0) :
    r ^ 2 * A + r * B - c = r ^ 1 * (r * A + B - c * r⁻¹) := by
  field_simp

/-- `g = h`: `a_k → +∞` as `r → ∞`. -/
theorem tendsto_scalarCoeffRatio_atTop_of_le {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hω : 0 < ω) (ha : outerHorizon M Q < e / ω) (h2M : 2 * M ≤ e / ω) :
    Tendsto (scalarCoeffRatio M Q e ω) atTop atTop := by
  have h2M' : ¬ e / ω < 2 * M := not_lt.2 h2M
  have he2 : 2 * M * ω ≤ e := (le_div_iff₀ hω).1 h2M
  have hC : 0 ≤ e - 2 * M * ω := by linarith
  have he : 0 < e := by nlinarith
  have hQM := NormalizationFacts.sub_sq_nonneg_of_abs_le hQ
  have hrpos : ∀ r ∈ Ioi (outerHorizon M Q), 0 < r := fun r hr => by
    have := NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr
    linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ → ℝ, ε = fun r => (r - M) - 1 / staticSolutionAA M Q r := ⟨_, rfl⟩
  have hχ : ∀ r, 1 / staticSolutionAA M Q r = r - M - ε r := fun r => by
    rw [hεdef]
    ring
  -- Lemma 2.1: `0 ≤ ε` and `εz ≤ δ²`
  have hεb : ∀ r ∈ Ioi (outerHorizon M Q), 0 ≤ ε r ∧ ε r * (r - M) ≤ M ^ 2 - Q ^ 2 := by
    intro r hr
    obtain ⟨-, h0, hle, hprod, -, -, -, -⟩ :=
      common_geometry M Q e ω hM hQ hω (e / ω) rfl ha r hr
    rw [hεdef]
    exact ⟨h0, by nlinarith [mul_nonneg h0 (sub_nonneg.2 hle)]⟩
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    have hzt : Tendsto (fun r : ℝ => r - M) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-M) tendsto_id
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((tendsto_const_nhds (x := M ^ 2 - Q ^ 2)).div_atTop hzt) ?_ ?_
    · filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
      exact (hεb r hr).1
    · filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
      rw [le_div_iff₀ (NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr)]
      exact (hεb r hr).2
  have hφ := tendsto_inv_atTop_zero.prodMk_nhds hε0
  -- the explicit form at infinity
  have hform : ∀ r ∈ Ioi (outerHorizon M Q),
      scalarA₀ M Q e ω r =
          r ^ 5 * (2 * ω * (e - 2 * M * ω)) + r ^ 4 * ucP4 M Q e ω r⁻¹ (ε r) ∧
        scalarH M Q e ω r = r ^ 2 * ((e - 2 * M * ω) + 2 * ε r * ω) +
          r * (2 * Q ^ 2 * ω - 2 * e * ε r) - Q ^ 2 * e := by
    intro r hr
    unfold scalarA₀ scalarH
    rw [scalarChi_of_not_lt h2M', hχ r]
    exact uc_reciprocal_infinity_alg (e := e) (ω := ω) (K := radialK e ω r) (hrpos r hr).ne'
      (CoefficientIdentities.delta_eq_sq_sub hQ r) rfl
  have hP : Continuous (fun p : ℝ × ℝ => ucP4 M Q e ω p.1 p.2) := by
    unfold ucP4
    fun_prop
  rcases hC.lt_or_eq with hCpos | hC0
  · -- `C > 0`: `a_k = r · G(1/r, ε)` with `G → 2ω/C`
    have hS0 : ((e - 2 * M * ω) + 2 * (0 : ℝ) * ω + (2 * Q ^ 2 * ω - 2 * e * 0) * 0 -
        Q ^ 2 * e * 0 ^ 2) ^ 2 ≠ 0 := by
      simpa using hCpos.ne'
    have hG : ContinuousAt (fun p : ℝ × ℝ =>
        (2 * ω * (e - 2 * M * ω) + p.1 * ucP4 M Q e ω p.1 p.2) /
          ((e - 2 * M * ω) + 2 * p.2 * ω + (2 * Q ^ 2 * ω - 2 * e * p.2) * p.1 -
            Q ^ 2 * e * p.1 ^ 2) ^ 2) (0, 0) :=
      ContinuousAt.div (by fun_prop) (by fun_prop) hS0
    have hval : (2 * ω * (e - 2 * M * ω) + (0 : ℝ) * ucP4 M Q e ω 0 0) /
        ((e - 2 * M * ω) + 2 * 0 * ω + (2 * Q ^ 2 * ω - 2 * e * 0) * 0 - Q ^ 2 * e * 0 ^ 2) ^ 2 =
          2 * ω / (e - 2 * M * ω) := by
      rw [div_eq_div_iff hS0 hCpos.ne']
      ring
    have hlim := hG.tendsto.comp hφ
    simp only [hval] at hlim
    refine (hlim.pos_mul_atTop (div_pos (by linarith) hCpos) tendsto_id).congr' ?_
    filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
    have hr0 := (hrpos r hr).ne'
    obtain ⟨hA, hH⟩ := hform r hr
    dsimp only [Function.comp_apply, id]
    rw [scalarCoeffRatio_eq hM hQ hr, hA, hH, uc_pow_five_add hr0, uc_quad_eq hr0,
      uc_div_sq_eq 1 2 hr0 rfl rfl, pow_one, mul_comm]
  · -- `C = 0` (the interface `r₀ = 2M`): `a_k = r² P₄/S₁² ≥ (P₄/B²) r²`
    have hp0 : 0 < ucP4 M Q e ω 0 0 := by
      have he' : e = 2 * M * ω := by linarith
      unfold ucP4
      rw [he']
      nlinarith [sq_nonneg Q, mul_pos hM hω]
    set B : ℝ := 4 * ω * (M ^ 2 - Q ^ 2) + 2 * Q ^ 2 * ω with hB
    have hBpos : 0 < B := by nlinarith [sq_nonneg Q, mul_pos hM hω]
    have hPlim : Tendsto (fun r => ucP4 M Q e ω r⁻¹ (ε r)) atTop (𝓝 (ucP4 M Q e ω 0 0)) := by
      have h := (hP.tendsto (0, 0)).comp hφ
      exact h
    have hlow := ((hPlim.div_const (B ^ 2)).pos_mul_atTop (div_pos hp0 (pow_pos hBpos 2))
      (tendsto_pow_atTop two_ne_zero))
    refine tendsto_atTop_mono' _ ?_ hlow
    filter_upwards [eventually_gt_atTop (outerHorizon M Q), eventually_ge_atTop (2 * M),
      hPlim.eventually_const_lt hp0] with r hr hr2 hpr
    have hr0 := (hrpos r hr).ne'
    obtain ⟨hA, hH⟩ := hform r hr
    have hHpos := (scalarH_pos_and_scalarA₀_pos hM hQ hω ha hr).1
    rw [scalarCoeffRatio_eq hM hQ hr, hA, hH, ← hC0]
    rw [hH, ← hC0, uc_lin_eq hr0] at hHpos
    rw [uc_lin_eq hr0, show ∀ X : ℝ, r ^ 5 * (2 * ω * 0) + r ^ 4 * X = r ^ (2 + 2 * 1) * X from
      fun X => by ring, uc_div_sq_eq 2 1 hr0 rfl rfl]
    have hS1 : 0 < r * (0 + 2 * ε r * ω) + (2 * Q ^ 2 * ω - 2 * e * ε r) - Q ^ 2 * e * r⁻¹ := by
      rw [pow_one] at hHpos
      exact pos_of_mul_pos_right hHpos (hrpos r hr).le
    have hS1B : r * (0 + 2 * ε r * ω) + (2 * Q ^ 2 * ω - 2 * e * ε r) - Q ^ 2 * e * r⁻¹ ≤ B := by
      obtain ⟨hε0', hεz⟩ := hεb r hr
      have h1 : ε r * r ≤ 2 * (M ^ 2 - Q ^ 2) := by
        nlinarith only [hεz, mul_nonneg hε0'
          (by linarith only [hr2] : (0 : ℝ) ≤ r - 2 * M)]
      have h2 : 0 ≤ Q ^ 2 * e * r⁻¹ := by
        have := inv_pos.2 (hrpos r hr)
        positivity
      have h3 : 0 ≤ e * ε r := mul_nonneg he.le hε0'
      nlinarith only [hB, h2, h3,
        mul_le_mul_of_nonneg_left h1 (by linarith only [hω] : (0 : ℝ) ≤ 2 * ω)]
    rw [mul_comm (r ^ 2)]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hpr.le (pow_pos hS1 2)
      (pow_le_pow_left₀ hS1.le hS1B 2)) (sq_nonneg r)

/-! ### The constant `c_*` of (4.7) -/

/-- `a_k` is bounded below on the exterior by a positive constant: it is continuous and positive
(Lemma 2.2) with positive limits (or `+∞`) at both ends. -/
theorem exists_pos_le_scalarCoeffRatio {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) :
    ∃ c, 0 < c ∧ ∀ r ∈ Ioi (outerHorizon M Q), c ≤ scalarCoeffRatio M Q e ω r := by
  have hcont : ContinuousOn (scalarCoeffRatio M Q e ω) (Ioi (outerHorizon M Q)) :=
    (continuousOn_scalarA₀_div hM hQ hω ha).congr fun r hr => scalarCoeffRatio_eq hM hQ hr
  have hpos : ∀ r ∈ Ioi (outerHorizon M Q), 0 < scalarCoeffRatio M Q e ω r := fun r hr => by
    obtain ⟨hH, hA⟩ := scalarH_pos_and_scalarA₀_pos hM hQ hω ha hr
    rw [scalarCoeffRatio_eq hM hQ hr]
    positivity
  have hq : (1 : ℝ) / 4 < 1 / 2 := by norm_num
  by_cases h2M : e / ω < 2 * M
  · exact uc_exists_lower_bound hcont hpos one_pos (by norm_num)
      ((tendsto_scalarCoeffRatio_horizon_of_lt hM hQ hω ha h2M).eventually_ge_atTop 1)
      ((tendsto_scalarCoeffRatio_atTop_of_lt hM hQ hω h2M).eventually_const_le hq)
  · exact uc_exists_lower_bound hcont hpos (by norm_num) one_pos
      ((tendsto_scalarCoeffRatio_horizon_of_le hM hQ hω ha (not_lt.1 h2M)).eventually_const_le hq)
      ((tendsto_scalarCoeffRatio_atTop_of_le hM hQ hω ha (not_lt.1 h2M)).eventually_ge_atTop 1)

/-- The constant `c_* = inf_{x_H < x < x_I} a_k(x)` of (4.7), written in `r`: the infimum of
`a_k = scalarCoeffRatio` over the exterior `r > a`. -/
@[expose] noncomputable def uniformConstant (M Q e ω : ℝ) : ℝ :=
  sInf (scalarCoeffRatio M Q e ω '' Ioi (outerHorizon M Q))

/-- **(4.7)**: in the strictly superradiant range (1.7), `c_* ∈ (0, 1/2]`, `a_k ≥ c_*` on the
exterior, and `a_k̂ ≥ c_*` for every `L ≥ 0` at every exterior point of the allowed set `LΔ < K²`
(by (3.4), `a_k̂ ≥ min{a_k, 2}`). The constant does not depend on `L`. -/
theorem uniformConstant_spec {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < e / ω) :
    0 < uniformConstant M Q e ω ∧ uniformConstant M Q e ω ≤ 1 / 2 ∧
      (∀ r ∈ Ioi (outerHorizon M Q), uniformConstant M Q e ω ≤ scalarCoeffRatio M Q e ω r) ∧
      ∀ (L : ℝ), 0 ≤ L → ∀ r ∈ Ioi (outerHorizon M Q), L * delta M Q r < radialK e ω r ^ 2 →
        uniformConstant M Q e ω ≤
          (2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2 -
              effectiveK M Q e ω L r *
                xDeriv M Q (normalizationG M Q e ω)
                  (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) r) /
            xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2 := by
  obtain ⟨c, hc, hle⟩ := exists_pos_le_scalarCoeffRatio hM hQ hω ha
  have hbdd : BddBelow (scalarCoeffRatio M Q e ω '' Ioi (outerHorizon M Q)) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact hle r hr
  have hlow : ∀ r ∈ Ioi (outerHorizon M Q), uniformConstant M Q e ω ≤ scalarCoeffRatio M Q e ω r :=
    fun r hr => csInf_le hbdd (mem_image_of_mem _ hr)
  have hpos : 0 < uniformConstant M Q e ω := by
    refine lt_of_lt_of_le hc (le_csInf (nonempty_Ioi.image _) ?_)
    rintro _ ⟨r, hr, rfl⟩
    exact hle r hr
  have hhalf : uniformConstant M Q e ω ≤ 1 / 2 := by
    by_cases h2M : e / ω < 2 * M
    · exact ge_of_tendsto (tendsto_scalarCoeffRatio_atTop_of_lt hM hQ hω h2M)
        ((eventually_gt_atTop _).mono fun r hr => hlow r hr)
    · exact ge_of_tendsto (tendsto_scalarCoeffRatio_horizon_of_le hM hQ hω ha (not_lt.1 h2M))
        (eventually_mem_nhdsWithin.mono fun r hr => hlow r hr)
  refine ⟨hpos, hhalf, hlow, fun L hL r hr hLK => ?_⟩
  obtain ⟨-, -, hmin⟩ := angular_positivity M Q e ω L hM hQ hω hL (e / ω) rfl ha r hr hLK
  exact le_trans (le_min (hlow r hr) (by linarith)) hmin

/-- **The uniform constant (4.7)**, written in `r`: in the strictly superradiant range (1.7)
there is `c ∈ (0, 1/2]` with `a_k = E_k/k_x² ≥ c` on the exterior (`L = 0`, `k = g²K`) and
`a_k̂ = E_k̂/k̂_x² ≥ c` for every `L ≥ 0` at every exterior point with `LΔ < K²`; `c` does not
depend on `L`. Here `g` is the normalization (2.2), `k̂` the effective frequency (3.2), and
`∂ₓ = Δg²∂ᵣ` (`xDeriv`). -/
theorem exists_uniform_constant :
    ∀ (M Q e ω : ℝ), 0 < M → |Q| ≤ M → 0 < ω → ∀ (r₀ : ℝ), r₀ = e / ω →
      outerHorizon M Q < r₀ → ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
        (∀ r ∈ Ioi (outerHorizon M Q),
          c ≤ (2 * xDeriv M Q (normalizationG M Q e ω)
                  (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s) r ^ 2 -
                normalizationG M Q e ω r ^ 2 * radialK e ω r *
                  xDeriv M Q (normalizationG M Q e ω)
                    (xDeriv M Q (normalizationG M Q e ω)
                      (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s)) r) /
              xDeriv M Q (normalizationG M Q e ω)
                (fun s => normalizationG M Q e ω s ^ 2 * radialK e ω s) r ^ 2) ∧
        ∀ (L : ℝ), 0 ≤ L → ∀ r ∈ Ioi (outerHorizon M Q), L * delta M Q r < radialK e ω r ^ 2 →
          c ≤ (2 * xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2 -
                effectiveK M Q e ω L r *
                  xDeriv M Q (normalizationG M Q e ω)
                    (xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)) r) /
              xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L) r ^ 2 := by
  intro M Q e ω hM hQ hω r₀ hr₀ ha
  subst hr₀
  obtain ⟨h1, h2, h3, h4⟩ := uniformConstant_spec hM hQ hω ha
  exact ⟨uniformConstant M Q e ω, h1, h2, h3, h4⟩

end ModeStability.AllAngular

end
