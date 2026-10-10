module

public import Mathlib
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.RadiusOf
public import ModeStability.Frozen.StaticSolution
public import ModeStability.Exterior.Calculus
public import ModeStability.AllAngular.Geometry
public import ModeStability.AllAngular.ScalarPositivity
public import ModeStability.AllAngular.AngularAlgebra
public import ModeStability.AllAngular.CoefficientIdentities

/-!
# Coordinate transport of Lemma 2.2 and Proposition 3.1: the abstract part

Source: the all-angular research notes in preparation, pp. 2–4, (2.2)–(2.7), Lemma 2.2 and
Proposition 3.1. The paper states the
coefficient identities in `r`, with `∂ₓ = Δ g² ∂ᵣ`
(`ModeStability.AllAngular.xDeriv_k_identities`,
`ModeStability.AllAngular.xDeriv_khat_identities`). The main assembly works in concrete
coordinates
`y ∈ (0, ∞)` with `r = ρ(y)` and `ρ' = s · Δ(ρ) g(ρ)²`, `s = ±1` (`s = 1` for the reciprocal
normalization `y = x`, `s = −1` for the constant normalization in the reflected coordinate
`y = −x`). This file proves the abstract transport, in the namespace
`ModeStability.AllAngular.CoordinateCoefficients`:

* `coordinate_chain_rule`: for `f = s · κ ∘ ρ` near `y`, `f' = (wκ') ∘ ρ` and
  `f'' = s · (w (wκ')') ∘ ρ` with `w = Δ g²`; since `s² = 1`, `E_f = 2f'² − ff''` is `E_κ ∘ ρ`
  in the paper's `x`-derivative (`E_κ = 2(wκ')² − κ · w(wκ')'`).
* `xDeriv_khat_pos`, `xDeriv_k_pos`: the conclusions (3.3) of Proposition 3.1 and (2.7) of
  Lemma 2.2 at a point `r`, in `r`-form, from the identities (3.5)–(3.6) resp. (2.7) and the
  positivity of `H`, `A₀` (Lemma 2.2), `T > δ|K|` (Lemma 2.1) and `0 ≤ χ ≤ z`.
* `coordinate_khat_props`, `coordinate_k_props`: the same conclusions for the coordinate
  coefficient `f`, together with `ContDiffAt ℝ 2 f`.
* smoothness helpers: `contDiffAt_radiusOf`, `contDiffAt_staticSolution`,
  `contDiffAt_effectiveKAux`; scalar helpers `sq_sign_mul_sqrt`, `sign_mul_sqrt_L0`.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

namespace CoordinateCoefficients

open CoefficientIdentities

/-! ### Scalar and gauge helpers -/

/-- `(sgn(K) √F)² = F` for `F ≥ 0`, provided `F = 0` when `K = 0`. -/
theorem sq_sign_mul_sqrt {K F : ℝ} (hF : 0 ≤ F) (hK : K = 0 → F = 0) :
    ((SignType.sign K : ℝ) * Real.sqrt F) ^ 2 = F := by
  rcases eq_or_ne K 0 with h | h
  · rw [hK h, Real.sqrt_zero, mul_zero]
    norm_num
  · have hs : (SignType.sign K : ℝ) ^ 2 = 1 := by
      rcases h.lt_or_gt with h | h
      · rw [sign_neg h]
        norm_num
      · rw [sign_pos h]
        norm_num
    rw [mul_pow, Real.sq_sqrt hF, hs, one_mul]

/-- At `L = 0`, `sgn(K) √(K² − 0·D) = K`. -/
theorem sign_mul_sqrt_L0 (K D : ℝ) :
    (SignType.sign K : ℝ) * Real.sqrt (K ^ 2 - 0 * D) = K := by
  rw [zero_mul, sub_zero, Real.sqrt_sq_eq_abs, sign_mul_abs]

/-- `z = r − M > 0` on the exterior `r > a`. -/
theorem sub_pos_of_outerHorizon_lt {M Q r : ℝ} (hr : outerHorizon M Q < r) : 0 < r - M := by
  unfold outerHorizon at hr
  linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]

/-- The constant gauge `g = 1` has `g' = 0 = 0/Δ`. -/
theorem eventually_hasDerivAt_one (M Q r : ℝ) :
    ∀ᶠ s in 𝓝 r, HasDerivAt (fun _ : ℝ => (1 : ℝ)) (0 / delta M Q s) s :=
  Eventually.of_forall fun s => by
    rw [zero_div]
    exact hasDerivAt_const s 1

/-! ### Smoothness -/

/-- `K = ωr² − er` is `C²`. -/
theorem contDiff_radialK (e ω : ℝ) : ContDiff ℝ 2 (radialK e ω) := by
  change ContDiff ℝ 2 (fun r => ω * r ^ 2 - e * r)
  fun_prop

/-- `Δ = (r − a)(r − b)` is `C²`. -/
theorem contDiff_delta (M Q : ℝ) : ContDiff ℝ 2 (delta M Q) := by
  change ContDiff ℝ 2 (fun r => (r - outerHorizon M Q) * (r - innerHorizon M Q))
  fun_prop

/-- `Δ(r) > 0` for `r > a` (no restriction on `M`, `Q`, since `b ≤ a`). -/
theorem delta_pos_of_lt {M Q r : ℝ} (hr : outerHorizon M Q < r) : 0 < delta M Q r := by
  have hba : innerHorizon M Q ≤ outerHorizon M Q := by
    unfold innerHorizon outerHorizon
    linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
  unfold delta
  exact mul_pos (sub_pos.2 hr) (by linarith)

/-- `r(x) = radiusOf M Q x` is `C²` at `x > 0`. -/
theorem contDiffAt_radiusOf {M Q : ℝ} (hQ : |Q| < M) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ 2 (radiusOf M Q) x := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hE : Real.exp ((outerHorizon M Q - innerHorizon M Q) / x) - 1 ≠ 0 :=
    (sub_pos.2 (Real.one_lt_exp_iff.2 (div_pos hd hx))).ne'
  change ContDiffAt ℝ 2 (fun y => outerHorizon M Q + (outerHorizon M Q - innerHorizon M Q) /
    (Real.exp ((outerHorizon M Q - innerHorizon M Q) / y) - 1)) x
  exact contDiffAt_const.add (contDiffAt_const.div
    ((contDiffAt_const.div contDiffAt_id hx.ne').exp.sub contDiffAt_const) hE)

/-- The static solution `h = g` of (2.1) is `C²` at `r > a`. -/
theorem contDiffAt_staticSolution {M Q : ℝ} (hQ : |Q| < M) {r : ℝ}
    (hr : outerHorizon M Q < r) : ContDiffAt ℝ 2 (staticSolution M Q) r := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hra : 0 < r - outerHorizon M Q := sub_pos.2 hr
  have hrb : 0 < r - innerHorizon M Q := by linarith
  change ContDiffAt ℝ 2 (fun s => 1 / (outerHorizon M Q - innerHorizon M Q) *
    Real.log ((s - innerHorizon M Q) / (s - outerHorizon M Q))) r
  exact contDiffAt_const.mul (((contDiffAt_id.sub contDiffAt_const).div
    (contDiffAt_id.sub contDiffAt_const) hra.ne').log (div_pos hrb hra).ne')

/-- Near a point where a continuous function is nonzero, its sign is locally constant. -/
private theorem cc_sign_eventually {f : ℝ → ℝ} {r : ℝ} (hf : ContinuousAt f r) (h0 : f r ≠ 0) :
    ∀ᶠ t in 𝓝 r, (SignType.sign (f t) : ℝ) = SignType.sign (f r) := by
  rcases h0.lt_or_gt with h | h
  · filter_upwards [hf.eventually (gt_mem_nhds h)] with t ht
    rw [sign_neg h, sign_neg ht]
  · filter_upwards [hf.eventually (lt_mem_nhds h)] with t ht
    rw [sign_pos h, sign_pos ht]

/-- `k̂ = sgn(K) g² √(K² − LΔ)` is `C²` at a point where `g` is `C²`, `K ≠ 0` and `K² > LΔ`. -/
theorem contDiffAt_effectiveKAux {M Q e ω L : ℝ} {g : ℝ → ℝ} {r : ℝ}
    (hg : ContDiffAt ℝ 2 g r) (hK0 : radialK e ω r ≠ 0)
    (hP : 0 < radialK e ω r ^ 2 - L * delta M Q r) :
    ContDiffAt ℝ 2 (effectiveKAux M Q e ω L g) r := by
  have hσ := cc_sign_eventually (contDiff_radialK e ω).continuous.continuousAt hK0
  have hP' : ContDiffAt ℝ 2 (fun t => radialK e ω t ^ 2 - L * delta M Q t) r :=
    ((contDiff_radialK e ω).contDiffAt.pow 2).sub
      (contDiffAt_const.mul (contDiff_delta M Q).contDiffAt)
  refine (((contDiffAt_const (c := (SignType.sign (radialK e ω r) : ℝ))).mul
    (hg.pow 2)).mul (hP'.sqrt hP.ne')).congr_of_eventuallyEq ?_
  filter_upwards [hσ] with t ht
  unfold effectiveKAux
  rw [ht]

/-! ### The abstract chain rule -/

/-- `E_f = E_κ ∘ ρ` from the chain rule, since `s² = 1`. -/
private theorem cc_E_eq {s κ W Y fx f1 f2 : ℝ} (hs : s * s = 1) (h0 : fx = s * κ)
    (h1 : f1 = W) (h2 : f2 = s * Y) : 2 * f1 ^ 2 - fx * f2 = 2 * W ^ 2 - κ * Y := by
  rw [h0, h1, h2]
  linear_combination (-(κ * Y)) * hs

/-- Chain rule for a coordinate change `r = ρ(y)` with `ρ' = s · w(ρ)`, `s² = 1` (in the paper
`w = Δg²`, so `∂_y = s ∂ₓ`): for `f = s · κ ∘ ρ` near `y`, `f(y) = s κ(ρ y)`,
`f'(y) = (w κ')(ρ y)` and `f''(y) = s (w (w κ')')(ρ y)`; hence `2f'² − ff'' = E_κ(ρ y)` with
`E_κ = 2(wκ')² − κ · w(wκ')'`. -/
theorem coordinate_chain_rule {f ρ κ w : ℝ → ℝ} {s x : ℝ} (hs : s * s = 1)
    (hf : f =ᶠ[𝓝 x] fun y => s * κ (ρ y))
    (hρ : ∀ᶠ y in 𝓝 x, HasDerivAt ρ (s * w (ρ y)) y)
    (hκ : ∀ᶠ r in 𝓝 (ρ x), DifferentiableAt ℝ κ r)
    (hG : DifferentiableAt ℝ (fun r => w r * deriv κ r) (ρ x)) :
    f x = s * κ (ρ x) ∧ deriv f x = w (ρ x) * deriv κ (ρ x) ∧
      deriv (deriv f) x = s * (w (ρ x) * deriv (fun r => w r * deriv κ r) (ρ x)) ∧
      2 * deriv f x ^ 2 - f x * deriv (deriv f) x =
        2 * (w (ρ x) * deriv κ (ρ x)) ^ 2 -
          κ (ρ x) * (w (ρ x) * deriv (fun r => w r * deriv κ r) (ρ x)) := by
  have hρx : HasDerivAt ρ (s * w (ρ x)) x := hρ.self_of_nhds
  have hκ' : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ κ (ρ y) := hρx.continuousAt.tendsto.eventually hκ
  have hd : ∀ᶠ y in 𝓝 x, deriv f y = w (ρ y) * deriv κ (ρ y) := by
    filter_upwards [hf.eventuallyEq_nhds, hρ, hκ'] with y h1 h2 h3
    have h4 : HasDerivAt (fun y => s * κ (ρ y)) (s * (deriv κ (ρ y) * (s * w (ρ y)))) y :=
      (h3.hasDerivAt.comp y h2).const_mul s
    rw [h1.deriv_eq, h4.deriv]
    linear_combination (w (ρ y) * deriv κ (ρ y)) * hs
  have h2 : HasDerivAt (fun y => w (ρ y) * deriv κ (ρ y))
      (deriv (fun r => w r * deriv κ r) (ρ x) * (s * w (ρ x))) x :=
    hG.hasDerivAt.comp x hρx
  have h3 : deriv (deriv f) x = s * (w (ρ x) * deriv (fun r => w r * deriv κ r) (ρ x)) := by
    rw [(h2.congr_of_eventuallyEq hd).deriv]
    ring
  exact ⟨hf.eq_of_nhds, hd.self_of_nhds, h3, cc_E_eq hs hf.eq_of_nhds hd.self_of_nhds h3⟩

/-! ### Proposition 3.1 and Lemma 2.2 at a point, in `r`-form -/

/-- The algebra closing (3.3): with `k̂_x = G⁴S/q`, `E_k̂ = G⁸N`, `S = (1 − τ)H + τT`,
`N = (1 − τ)A₀ + τB + 3T²τ²/(1 − τ)`. -/
private theorem cc_final_alg {G q τ A₀ B H T : ℝ} (hG : 0 < G) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hq : 0 < q) (hA₀ : 0 < A₀) (hH : 0 < H) (hT : 0 < T) (hB : A₀ + 2 * T ^ 2 < B) :
    0 < G ^ 4 / q * ((1 - τ) * H + τ * T) ∧
      0 < G ^ 8 * ((1 - τ) * A₀ + τ * B + 3 * T ^ 2 * τ ^ 2 / (1 - τ)) := by
  have hS := angular_slope_pos hH hT hτ0 hτ1
  have hBpos : 0 < B := by nlinarith only [hA₀, hB, sq_nonneg T]
  have hN := angular_numerator_pos (T := T) hA₀ hBpos hτ0 hτ1
  exact ⟨mul_pos (div_pos (pow_pos hG 4) hq) hS, mul_pos (pow_pos hG 8) hN⟩

/-- Proposition 3.1, (3.3), at a point `r > a`, in `r`-form (`∂ₓ = Δg²∂ᵣ`): for a gauge `g > 0`
with `Δg' = c` near `r`, `χ = −c/g(r)` with `0 ≤ χ ≤ z` and `H > 0`, `A₀ > 0` (Lemma 2.2), the
signed effective frequency `k̂ = effectiveKAux g` has `k̂_x > 0` and `2k̂_x² − k̂k̂_xx > 0` wherever
`LΔ < K²`. -/
theorem xDeriv_khat_pos {M Q e ω c L χ : ℝ} {g : ℝ → ℝ} {r : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hω : 0 < ω) (hL : 0 ≤ L) (hr₀ : outerHorizon M Q < e / ω) (hr : outerHorizon M Q < r)
    (hg0 : 0 < g r) (hK : L * delta M Q r < radialK e ω r ^ 2)
    (hg : ∀ᶠ s in 𝓝 r, HasDerivAt g (c / delta M Q s) s) (hχ : -c / g r = χ) (hχ0 : 0 ≤ χ)
    (hχz : χ ≤ r - M)
    (hH : 0 < delta M Q r * (2 * ω * r - e) - 2 * χ * radialK e ω r)
    (hA : 0 < 2 * delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
      2 * delta M Q r * (χ + (r - M)) * radialK e ω r * (2 * ω * r - e) -
      delta M Q r ^ 2 * radialK e ω r * (2 * ω) + 2 * χ ^ 2 * radialK e ω r ^ 2) :
    0 < delta M Q r * g r ^ 2 * deriv (effectiveKAux M Q e ω L g) r ∧
      0 < 2 * (delta M Q r * g r ^ 2 * deriv (effectiveKAux M Q e ω L g) r) ^ 2 -
          effectiveKAux M Q e ω L g r *
            (delta M Q r * g r ^ 2 * deriv (fun s => delta M Q s * g s ^ 2 *
              deriv (effectiveKAux M Q e ω L g) s) r) := by
  have hΔ := delta_pos_of_lt hr
  obtain ⟨j1, j2⟩ := xDeriv_khat_identities (e := e) (ω := ω) (L := L) hQ hL hΔ hg0 hK hg
  rw [hχ] at j1 j2
  rw [j2, j1]
  -- `τ = LΔ/K² ∈ [0, 1)`, `q = √(1 − τ) > 0`
  have hLΔ : 0 ≤ L * delta M Q r := mul_nonneg hL hΔ.le
  have hK2 : 0 < radialK e ω r ^ 2 := lt_of_le_of_lt hLΔ hK
  have hτ0 : 0 ≤ L * delta M Q r / radialK e ω r ^ 2 := div_nonneg hLΔ hK2.le
  have hτ1 : L * delta M Q r / radialK e ω r ^ 2 < 1 := (div_lt_one hK2).2 hK
  have hq := Real.sqrt_pos.2 (sub_pos.2 hτ1)
  -- Lemma 2.1: `T > δ|K| ≥ 0`, hence `T > 0` and `T² > δ²K²`
  have he : ω * (e / ω) = e := mul_div_cancel₀ e hω.ne'
  have hT := mul_abs_K_lt_T hM hQ hω hr₀ hr
  rw [he] at hT
  have hδK : 0 ≤ Real.sqrt (M ^ 2 - Q ^ 2) * |radialK e ω r| :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hTpos := lt_of_le_of_lt hδK hT
  have hT2 := pow_lt_pow_left₀ hT hδK (n := 2) two_ne_zero
  rw [mul_pow, sq_abs] at hT2
  -- (3.9): `B > A₀ + 2T²`
  have hB := mixed_coefficient_gt (A₀ := 2 * delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
      2 * delta M Q r * (χ + (r - M)) * radialK e ω r * (2 * ω * r - e) -
      delta M Q r ^ 2 * radialK e ω r * (2 * ω) + 2 * χ ^ 2 * radialK e ω r ^ 2)
    hT2 hχ0 hχz
  rw [sq_sqrt_sub_sq hQ] at hB
  exact cc_final_alg hg0 hτ0 hτ1 hq hA hH hTpos hB

/-- Lemma 2.2, (2.7), at a point `r > a`, in `r`-form: for `k = g²K`, `k_x = g⁴H > 0` and
`2k_x² − kk_xx = g⁸A₀ > 0`. -/
theorem xDeriv_k_pos {M Q e ω c χ : ℝ} {g : ℝ → ℝ} {r : ℝ} (hr : outerHorizon M Q < r)
    (hg0 : 0 < g r) (hg : ∀ᶠ s in 𝓝 r, HasDerivAt g (c / delta M Q s) s) (hχ : -c / g r = χ)
    (hH : 0 < delta M Q r * (2 * ω * r - e) - 2 * χ * radialK e ω r)
    (hA : 0 < 2 * delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
      2 * delta M Q r * (χ + (r - M)) * radialK e ω r * (2 * ω * r - e) -
      delta M Q r ^ 2 * radialK e ω r * (2 * ω) + 2 * χ ^ 2 * radialK e ω r ^ 2) :
    0 < delta M Q r * g r ^ 2 * deriv (fun s => g s ^ 2 * radialK e ω s) r ∧
      0 < 2 * (delta M Q r * g r ^ 2 * deriv (fun s => g s ^ 2 * radialK e ω s) r) ^ 2 -
          g r ^ 2 * radialK e ω r *
            (delta M Q r * g r ^ 2 * deriv (fun s => delta M Q s * g s ^ 2 *
              deriv (fun t => g t ^ 2 * radialK e ω t) s) r) := by
  obtain ⟨k1, k2⟩ := xDeriv_k_identities (e := e) (ω := ω) (delta_pos_of_lt hr).ne' hg0.ne' hg
  rw [hχ] at k1 k2
  rw [k2, k1]
  exact ⟨mul_pos (pow_pos hg0 4) hH, mul_pos (pow_pos hg0 8) hA⟩

/-! ### Transport to a coordinate `y` with `ρ' = s Δg²` -/

/-- Proposition 3.1 in a coordinate `y` with `r = ρ(y)`, `ρ' = s Δ(ρ) g(ρ)²`, `s² = 1`: for
`f = s · k̂ ∘ ρ` near `x` (`k̂ = effectiveKAux g`), at a point with `LΔ < K²` at `r = ρ(x)`,
`f` is `C²` at `x`, `f' > 0` and `2f'² − ff'' > 0`. -/
theorem coordinate_khat_props {M Q e ω c L χ s : ℝ} {f g ρ : ℝ → ℝ} {x : ℝ} (hs : s * s = 1)
    (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω) (hL : 0 ≤ L) (hr₀ : outerHorizon M Q < e / ω)
    (hr : outerHorizon M Q < ρ x) (hg0 : 0 < g (ρ x))
    (hK : L * delta M Q (ρ x) < radialK e ω (ρ x) ^ 2)
    (hg : ∀ᶠ r in 𝓝 (ρ x), HasDerivAt g (c / delta M Q r) r) (hgC : ContDiffAt ℝ 2 g (ρ x))
    (hρ : ∀ᶠ y in 𝓝 x, HasDerivAt ρ (s * (delta M Q (ρ y) * g (ρ y) ^ 2)) y)
    (hρC : ContDiffAt ℝ 2 ρ x) (hf : f =ᶠ[𝓝 x] fun y => s * effectiveKAux M Q e ω L g (ρ y))
    (hχ : -c / g (ρ x) = χ) (hχ0 : 0 ≤ χ) (hχz : χ ≤ ρ x - M)
    (hH : 0 < delta M Q (ρ x) * (2 * ω * ρ x - e) - 2 * χ * radialK e ω (ρ x))
    (hA : 0 < 2 * delta M Q (ρ x) ^ 2 * (2 * ω * ρ x - e) ^ 2 -
      2 * delta M Q (ρ x) * (χ + (ρ x - M)) * radialK e ω (ρ x) * (2 * ω * ρ x - e) -
      delta M Q (ρ x) ^ 2 * radialK e ω (ρ x) * (2 * ω) + 2 * χ ^ 2 * radialK e ω (ρ x) ^ 2) :
    ContDiffAt ℝ 2 f x ∧ 0 < deriv f x ∧ 0 < 2 * deriv f x ^ 2 - f x * deriv (deriv f) x := by
  have hΔ := delta_pos_of_lt hr
  have hK0 : radialK e ω (ρ x) ≠ 0 := by
    intro h
    rw [h] at hK
    nlinarith [mul_nonneg hL hΔ.le]
  have hκC := contDiffAt_effectiveKAux hgC hK0 (sub_pos.2 hK)
  have hκ : ∀ᶠ r in 𝓝 (ρ x), DifferentiableAt ℝ (effectiveKAux M Q e ω L g) r :=
    (hκC.eventually (by simp)).mono fun r hr => hr.differentiableAt (by norm_num)
  have hG : DifferentiableAt ℝ (fun r => delta M Q r * g r ^ 2 *
      deriv (effectiveKAux M Q e ω L g) r) (ρ x) :=
    (((contDiff_delta M Q).differentiable (by norm_num) _).mul
      ((hgC.differentiableAt (by norm_num)).pow 2)).mul
      ((hκC.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  obtain ⟨-, h1, -, hE⟩ :=
    coordinate_chain_rule (w := fun r => delta M Q r * g r ^ 2) hs hf hρ hκ hG
  obtain ⟨p1, p2⟩ := xDeriv_khat_pos hM hQ hω hL hr₀ hr hg0 hK hg hχ hχ0 hχz hH hA
  refine ⟨(contDiffAt_const.mul (hκC.comp x hρC)).congr_of_eventuallyEq hf, ?_, ?_⟩
  · rw [h1]
    exact p1
  · rw [hE]
    exact p2

/-- Lemma 2.2 in a coordinate `y` with `r = ρ(y)`, `ρ' = s Δ(ρ) g(ρ)²`, `s² = 1`: for
`f = s · k ∘ ρ` near `x` (`k = g²K`), `f` is `C²` at `x`, `f' > 0` and `2f'² − ff'' > 0`. -/
theorem coordinate_k_props {M Q e ω c χ s : ℝ} {f g ρ : ℝ → ℝ} {x : ℝ} (hs : s * s = 1)
    (hr : outerHorizon M Q < ρ x) (hg0 : 0 < g (ρ x))
    (hg : ∀ᶠ r in 𝓝 (ρ x), HasDerivAt g (c / delta M Q r) r) (hgC : ContDiffAt ℝ 2 g (ρ x))
    (hρ : ∀ᶠ y in 𝓝 x, HasDerivAt ρ (s * (delta M Q (ρ y) * g (ρ y) ^ 2)) y)
    (hρC : ContDiffAt ℝ 2 ρ x)
    (hf : f =ᶠ[𝓝 x] fun y => s * (g (ρ y) ^ 2 * radialK e ω (ρ y)))
    (hχ : -c / g (ρ x) = χ)
    (hH : 0 < delta M Q (ρ x) * (2 * ω * ρ x - e) - 2 * χ * radialK e ω (ρ x))
    (hA : 0 < 2 * delta M Q (ρ x) ^ 2 * (2 * ω * ρ x - e) ^ 2 -
      2 * delta M Q (ρ x) * (χ + (ρ x - M)) * radialK e ω (ρ x) * (2 * ω * ρ x - e) -
      delta M Q (ρ x) ^ 2 * radialK e ω (ρ x) * (2 * ω) + 2 * χ ^ 2 * radialK e ω (ρ x) ^ 2) :
    ContDiffAt ℝ 2 f x ∧ 0 < deriv f x ∧ 0 < 2 * deriv f x ^ 2 - f x * deriv (deriv f) x := by
  have hκC : ContDiffAt ℝ 2 (fun r => g r ^ 2 * radialK e ω r) (ρ x) :=
    (hgC.pow 2).mul (contDiff_radialK e ω).contDiffAt
  have hκ : ∀ᶠ r in 𝓝 (ρ x), DifferentiableAt ℝ (fun r => g r ^ 2 * radialK e ω r) r :=
    (hκC.eventually (by simp)).mono fun r hr => hr.differentiableAt (by norm_num)
  have hG : DifferentiableAt ℝ (fun r => delta M Q r * g r ^ 2 *
      deriv (fun t => g t ^ 2 * radialK e ω t) r) (ρ x) :=
    (((contDiff_delta M Q).differentiable (by norm_num) _).mul
      ((hgC.differentiableAt (by norm_num)).pow 2)).mul
      ((hκC.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  obtain ⟨-, h1, -, hE⟩ :=
    coordinate_chain_rule (w := fun r => delta M Q r * g r ^ 2) hs hf hρ hκ hG
  obtain ⟨p1, p2⟩ := xDeriv_k_pos hr hg0 hg hχ hH hA
  refine ⟨(contDiffAt_const.mul (hκC.comp x hρC)).congr_of_eventuallyEq hf, ?_, ?_⟩
  · rw [h1]
    exact p1
  · rw [hE]
    exact p2

end CoordinateCoefficients

end ModeStability.AllAngular

end
