module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK

/-!
# The derivative identities (2.7), (3.5), (3.6) of the all-angular paper

Source: the all-angular research notes in preparation, p. 2, (2.3), (2.5)–(2.7), and p. 4,
(3.2), (3.5)–(3.7).

The paper's coordinate `x` satisfies `x' = 1/(Δg²)`, so `∂ₓ = Δ g² ∂ᵣ`, and both normalizations
of the gauge function `g` in (2.2) satisfy `Δ g' = c` with a constant `c` (`g = 1`: `c = 0`;
`g = h`: `c = −1`). With `χ = −c/g = −Δg'/g`, `z = r − M`, `K = ωr² − er`, `K' = 2ωr − e`,
`K'' = 2ω`, `δ² = M² − Q²`, and

* `T = ΔK' − zK`, `H = ΔK' − 2χK` (2.5),
* `A₀ = 2Δ²K'² − 2Δ(χ + z)KK' − Δ²KK'' + 2χ²K²` (2.6),
* `B = A₀ + 3T² + [2χ(z − χ) − δ²]K²` (3.7),
* `τ = LΔ/K²`, `k̂ = sgn(K) g² √(K² − LΔ)` (3.2),

this file proves, at a point `r` with `Δ(r) ≠ 0` and `g(r) ≠ 0`:

* `xDeriv_k_identities`: (2.7), `k_x = g⁴H` and `2k_x² − k k_xx = g⁸A₀` for `k = g²K`;
* `xDeriv_khat_identities`: (3.5), `k̂_x = g⁴[(1 − τ)H + τT]/√(1 − τ)`, and (3.6),
  `2k̂_x² − k̂ k̂_xx = g⁸[(1 − τ)A₀ + τB + 3T²τ²/(1 − τ)]`, at a point with `L ≥ 0`, `Δ > 0`,
  `g > 0`, `LΔ < K²` (so `K ≠ 0`, `τ ∈ [0, 1)`), and `|Q| ≤ M` (for `Δ = z² − δ²`).

All `x`-derivatives are written as `Δ g² ∂ᵣ` of explicit functions of `r`. The proof of
(3.5)–(3.6)
differentiates `√(K² − LΔ)` directly, using `(K² − LΔ)' = 2KK' − 2Lz` (from `Δ' = 2z`; this is the
paper's `τ' = −2τT/(ΔK)`), and closes the algebra with `√(K² − LΔ) = sgn(K) K √(1 − τ)`. The
calculus and algebra helpers live in the namespace
`ModeStability.AllAngular.CoefficientIdentities`.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

/-! ### Calculus and algebra helpers -/

namespace CoefficientIdentities

/-- `Δ' = 2(r − M)` for `Δ = (r − a)(r − b)`, `a + b = 2M`. -/
theorem hasDerivAt_delta (M Q s : ℝ) : HasDerivAt (fun t => delta M Q t) (2 * (s - M)) s := by
  have h : HasDerivAt (fun t => (t - outerHorizon M Q) * (t - innerHorizon M Q))
      (1 * (s - innerHorizon M Q) + (s - outerHorizon M Q) * 1) s :=
    ((hasDerivAt_id' s).sub_const (outerHorizon M Q)).mul
      ((hasDerivAt_id' s).sub_const (innerHorizon M Q))
  change HasDerivAt (fun t => (t - outerHorizon M Q) * (t - innerHorizon M Q)) _ s
  convert h using 1
  unfold outerHorizon innerHorizon
  ring

/-- `K' = 2ωr − e` for `K = ωr² − er`. -/
theorem hasDerivAt_radialK (e ω s : ℝ) :
    HasDerivAt (fun t => radialK e ω t) (2 * ω * s - e) s := by
  have h : HasDerivAt (fun t => ω * t ^ 2 - e * t) (ω * (2 * s) - e * 1) s := by
    have h2 : HasDerivAt (fun t => t ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    exact (h2.const_mul ω).sub ((hasDerivAt_id' s).const_mul e)
  change HasDerivAt (fun t => ω * t ^ 2 - e * t) _ s
  convert h using 1
  ring

/-- `Δ = (r − M)² − (M² − Q²)` for `|Q| ≤ M`. -/
theorem delta_eq_sq_sub {M Q : ℝ} (hQ : |Q| ≤ M) (r : ℝ) :
    delta M Q r = (r - M) ^ 2 - (M ^ 2 - Q ^ 2) := by
  have h := sq_le_sq' (abs_le.1 hQ).1 (abs_le.1 hQ).2
  have hs : Real.sqrt (M ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - Q ^ 2 := Real.sq_sqrt (by linarith)
  unfold delta outerHorizon innerHorizon
  linear_combination -hs

/-- `(g²)' = 2gg'`, `(g³)' = 3g²g'`, `(g⁴)' = 4g³g'` with `g' = c/Δ`. -/
theorem hasDerivAt_gpow {M Q c : ℝ} {g : ℝ → ℝ} {s : ℝ} (hs : HasDerivAt g (c / delta M Q s) s) :
    HasDerivAt (fun t => g t ^ 2) (2 * g s * (c / delta M Q s)) s ∧
      HasDerivAt (fun t => g t ^ 3) (3 * g s ^ 2 * (c / delta M Q s)) s ∧
      HasDerivAt (fun t => g t ^ 4) (4 * g s ^ 3 * (c / delta M Q s)) s := by
  refine ⟨?_, ?_, ?_⟩
  · convert hs.fun_pow 2 using 1
    norm_num
  · convert hs.fun_pow 3 using 1
  · convert hs.fun_pow 4 using 1

/-- `(K² − LΔ)' = 2KK' − 2Lz`. -/
theorem hasDerivAt_radicand (M Q e ω L s : ℝ) :
    HasDerivAt (fun t => radialK e ω t ^ 2 - L * delta M Q t)
      (2 * radialK e ω s * (2 * ω * s - e) - L * (2 * (s - M))) s := by
  convert ((hasDerivAt_radialK e ω s).fun_pow 2).sub ((hasDerivAt_delta M Q s).const_mul L)
    using 1
  norm_num

/-- The algebra behind (3.5) and (3.6) at a point, with `G = g(r)`, `D = Δ(r)`, `K = K(r)`,
`P = √(K² − LΔ) = σKq`, `q = √(1 − τ)`, `σ = sgn K`, `τ = LΔ/K²`. -/
theorem khat_identities_alg {σ G c D K ω r e M Q L P q : ℝ} (hσ : σ = 1 ∨ σ = -1) (hG : G ≠ 0)
    (hD : D ≠ 0) (hK : K ≠ 0) (hq : q ≠ 0) (hP : P = σ * K * q) (hτ : L * D / K ^ 2 = 1 - q ^ 2)
    (hd : D = (r - M) ^ 2 - (M ^ 2 - Q ^ 2)) :
    D * G ^ 2 * (σ * (2 * G * (c / D)) * P +
        σ * G ^ 2 * ((2 * K * (2 * ω * r - e) - L * (2 * (r - M))) / (2 * P))) =
      G ^ 4 / q * ((1 - L * D / K ^ 2) * (D * (2 * ω * r - e) - 2 * (-c / G) * K) +
        L * D / K ^ 2 * (D * (2 * ω * r - e) - (r - M) * K)) ∧
    2 * (D * G ^ 2 * (σ * (2 * G * (c / D)) * P +
        σ * G ^ 2 * ((2 * K * (2 * ω * r - e) - L * (2 * (r - M))) / (2 * P)))) ^ 2 -
        σ * G ^ 2 * P *
          (D * G ^ 2 *
            (σ * (2 * c * (3 * G ^ 2 * (c / D)) * P +
              2 * c * G ^ 3 * ((2 * K * (2 * ω * r - e) - L * (2 * (r - M))) / (2 * P)) +
              (((2 * (r - M) * G ^ 4 + D * (4 * G ^ 3 * (c / D))) *
                    (K * (2 * ω * r - e) - L * (r - M)) +
                  D * G ^ 4 * ((2 * ω * r - e) * (2 * ω * r - e) + K * (2 * ω) - L * 1)) * P -
                D * G ^ 4 * (K * (2 * ω * r - e) - L * (r - M)) *
                  ((2 * K * (2 * ω * r - e) - L * (2 * (r - M))) / (2 * P))) / P ^ 2))) =
      G ^ 8 * ((1 - L * D / K ^ 2) *
          (2 * D ^ 2 * (2 * ω * r - e) ^ 2 - 2 * D * (-c / G + (r - M)) * K * (2 * ω * r - e) -
            D ^ 2 * K * (2 * ω) + 2 * (-c / G) ^ 2 * K ^ 2) +
        L * D / K ^ 2 *
          (2 * D ^ 2 * (2 * ω * r - e) ^ 2 - 2 * D * (-c / G + (r - M)) * K * (2 * ω * r - e) -
              D ^ 2 * K * (2 * ω) + 2 * (-c / G) ^ 2 * K ^ 2 +
            3 * (D * (2 * ω * r - e) - (r - M) * K) ^ 2 +
            (2 * (-c / G) * (r - M - -c / G) - (M ^ 2 - Q ^ 2)) * K ^ 2) +
        3 * (D * (2 * ω * r - e) - (r - M) * K) ^ 2 * (L * D / K ^ 2) ^ 2 /
          (1 - L * D / K ^ 2)) := by
  have hL : L = (1 - q ^ 2) * K ^ 2 / D := by
    rw [← hτ]
    field_simp
  have hd' : M ^ 2 - Q ^ 2 = (r - M) ^ 2 - D := by linarith only [hd]
  rw [hτ, hd', show (1 : ℝ) - (1 - q ^ 2) = q ^ 2 by ring]
  subst hP hL
  rcases hσ with rfl | rfl <;> constructor <;> field_simp <;> ring

end CoefficientIdentities

open CoefficientIdentities

/-! ### (2.7): the coefficients of `k = g²K` -/

/-- (2.7), written in `r` with `∂ₓ = Δ g² ∂ᵣ`: for `k = g²K` and `Δ g' = c`, `χ = −c/g`,
`k_x = g⁴H` with `H = ΔK' − 2χK`, and `2k_x² − k k_xx = g⁸A₀` with
`A₀ = 2Δ²K'² − 2Δ(χ + z)KK' − Δ²KK'' + 2χ²K²`, `z = r − M`, `K' = 2ωr − e`, `K'' = 2ω`. -/
theorem xDeriv_k_identities {M Q e ω c : ℝ} {g : ℝ → ℝ} {r : ℝ} (hΔ : delta M Q r ≠ 0)
    (hg0 : g r ≠ 0) (hg : ∀ᶠ s in 𝓝 r, HasDerivAt g (c / delta M Q s) s) :
    delta M Q r * g r ^ 2 * deriv (fun s => g s ^ 2 * radialK e ω s) r =
        g r ^ 4 * (delta M Q r * (2 * ω * r - e) - 2 * (-c / g r) * radialK e ω r) ∧
      2 * (delta M Q r * g r ^ 2 * deriv (fun s => g s ^ 2 * radialK e ω s) r) ^ 2 -
          g r ^ 2 * radialK e ω r *
            (delta M Q r * g r ^ 2 * deriv (fun s => delta M Q s * g s ^ 2 *
              deriv (fun t => g t ^ 2 * radialK e ω t) s) r) =
        g r ^ 8 * (2 * delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
          2 * delta M Q r * ((-c / g r) + (r - M)) * radialK e ω r * (2 * ω * r - e) -
          delta M Q r ^ 2 * radialK e ω r * (2 * ω) + 2 * (-c / g r) ^ 2 * radialK e ω r ^ 2) := by
  have hF1 : ∀ᶠ s in 𝓝 r, deriv (fun s => g s ^ 2 * radialK e ω s) s =
      2 * g s * (c / delta M Q s) * radialK e ω s + g s ^ 2 * (2 * ω * s - e) := by
    filter_upwards [hg] with s hs
    exact ((hasDerivAt_gpow hs).1.fun_mul (hasDerivAt_radialK e ω s)).deriv
  have hΔev : ∀ᶠ s in 𝓝 r, delta M Q s ≠ 0 :=
    (hasDerivAt_delta M Q r).continuousAt.eventually_ne hΔ
  have hG : (fun s => delta M Q s * g s ^ 2 * deriv (fun t => g t ^ 2 * radialK e ω t) s) =ᶠ[𝓝 r]
      fun s => 2 * c * g s ^ 3 * radialK e ω s + delta M Q s * g s ^ 4 * (2 * ω * s - e) := by
    filter_upwards [hF1, hΔev] with s hs hsΔ
    rw [hs]
    field_simp
  have hgr : HasDerivAt g (c / delta M Q r) r := hg.self_of_nhds
  have hK1 : HasDerivAt (fun t => 2 * ω * t - e) (2 * ω) r := by
    simpa using ((hasDerivAt_id' r).const_mul (2 * ω)).sub_const e
  have hG2 : HasDerivAt
      (fun s => 2 * c * g s ^ 3 * radialK e ω s + delta M Q s * g s ^ 4 * (2 * ω * s - e)) _ r :=
    ((((hasDerivAt_gpow hgr).2.1.const_mul (2 * c)).fun_mul (hasDerivAt_radialK e ω r)).fun_add
      (((hasDerivAt_delta M Q r).fun_mul (hasDerivAt_gpow hgr).2.2).fun_mul hK1))
  rw [hG.deriv_eq, hF1.self_of_nhds, hG2.deriv]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-! ### (3.5), (3.6): the coefficients of `k̂ = sgn(K) g² √(K² − LΔ)` -/

/-- The signed effective frequency `k̂ = sgn(K) g² √(K² − LΔ) = k√(1 − τ)` of (3.2), as a function
of `r`, for a gauge function `g`. -/
@[expose] noncomputable def effectiveKAux (M Q e ω L : ℝ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  (SignType.sign (radialK e ω s) : ℝ) * g s ^ 2 * Real.sqrt (radialK e ω s ^ 2 - L * delta M Q s)

/-- (3.5) and (3.6), written in `r` with `∂ₓ = Δ g² ∂ᵣ`: for `k̂ = sgn(K) g² √(K² − LΔ)`,
`Δ g' = c`, `χ = −c/g`, `τ = LΔ/K²`, `T = ΔK' − zK`, `H = ΔK' − 2χK`, `A₀` as in (2.6) and
`B = A₀ + 3T² + [2χ(z − χ) − δ²]K²` (3.7) with `δ² = M² − Q²`:
`k̂_x = g⁴[(1 − τ)H + τT]/√(1 − τ)` and
`2k̂_x² − k̂ k̂_xx = g⁸[(1 − τ)A₀ + τB + 3T²τ²/(1 − τ)]`. -/
theorem xDeriv_khat_identities {M Q e ω c L : ℝ} {g : ℝ → ℝ} {r : ℝ} (hQ : |Q| ≤ M)
    (hL : 0 ≤ L) (hΔ : 0 < delta M Q r) (hg0 : 0 < g r)
    (hK : L * delta M Q r < radialK e ω r ^ 2)
    (hg : ∀ᶠ s in 𝓝 r, HasDerivAt g (c / delta M Q s) s) :
    delta M Q r * g r ^ 2 * deriv (effectiveKAux M Q e ω L g) r =
        g r ^ 4 / Real.sqrt (1 - L * delta M Q r / radialK e ω r ^ 2) *
          ((1 - L * delta M Q r / radialK e ω r ^ 2) *
              (delta M Q r * (2 * ω * r - e) - 2 * (-c / g r) * radialK e ω r) +
            L * delta M Q r / radialK e ω r ^ 2 *
              (delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r)) ∧
      2 * (delta M Q r * g r ^ 2 * deriv (effectiveKAux M Q e ω L g) r) ^ 2 -
          effectiveKAux M Q e ω L g r *
            (delta M Q r * g r ^ 2 * deriv (fun s => delta M Q s * g s ^ 2 *
              deriv (effectiveKAux M Q e ω L g) s) r) =
        g r ^ 8 * ((1 - L * delta M Q r / radialK e ω r ^ 2) *
            (2 * delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
              2 * delta M Q r * ((-c / g r) + (r - M)) * radialK e ω r * (2 * ω * r - e) -
              delta M Q r ^ 2 * radialK e ω r * (2 * ω) +
              2 * (-c / g r) ^ 2 * radialK e ω r ^ 2) +
          L * delta M Q r / radialK e ω r ^ 2 *
            ((2 * delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
              2 * delta M Q r * ((-c / g r) + (r - M)) * radialK e ω r * (2 * ω * r - e) -
              delta M Q r ^ 2 * radialK e ω r * (2 * ω) +
              2 * (-c / g r) ^ 2 * radialK e ω r ^ 2) +
              3 * (delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r) ^ 2 +
              (2 * (-c / g r) * ((r - M) - (-c / g r)) - (M ^ 2 - Q ^ 2)) *
                radialK e ω r ^ 2) +
          3 * (delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r) ^ 2 *
              (L * delta M Q r / radialK e ω r ^ 2) ^ 2 /
            (1 - L * delta M Q r / radialK e ω r ^ 2)) := by
  -- the sign `σ = sgn K(r)` and the nondegeneracy facts at `r`
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, (SignType.sign (radialK e ω r) : ℝ) = σ := ⟨_, rfl⟩
  have hLΔ : 0 ≤ L * delta M Q r := mul_nonneg hL hΔ.le
  have hK0 : radialK e ω r ≠ 0 := by
    intro h
    rw [h] at hK
    norm_num at hK
    linarith
  have hS0 : 0 < radialK e ω r ^ 2 - L * delta M Q r := sub_pos.2 hK
  have hσK : σ * radialK e ω r = |radialK e ω r| := by
    rw [← hσ]
    exact sign_mul_self _
  have hσ1 : σ = 1 ∨ σ = -1 := by
    rcases hK0.lt_or_gt with h | h
    · right
      rw [← hσ, sign_neg h]
      simp
    · left
      rw [← hσ, sign_pos h]
      simp
  -- eventual facts near `r`
  have hσev : ∀ᶠ s in 𝓝 r, (SignType.sign (radialK e ω s) : ℝ) = σ := by
    rcases hK0.lt_or_gt with h | h
    · filter_upwards [(hasDerivAt_radialK e ω r).continuousAt.tendsto.eventually
        (gt_mem_nhds h)] with s hs
      rw [← hσ, sign_neg h, sign_neg hs]
    · filter_upwards [(hasDerivAt_radialK e ω r).continuousAt.tendsto.eventually
        (lt_mem_nhds h)] with s hs
      rw [← hσ, sign_pos h, sign_pos hs]
  have hev : ∀ᶠ s in 𝓝 r, HasDerivAt g (c / delta M Q s) s ∧ 0 < delta M Q s ∧
      0 < radialK e ω s ^ 2 - L * delta M Q s ∧ (SignType.sign (radialK e ω s) : ℝ) = σ :=
    hg.and (((hasDerivAt_delta M Q r).continuousAt.tendsto.eventually (lt_mem_nhds hΔ)).and
      (((hasDerivAt_radicand M Q e ω L r).continuousAt.tendsto.eventually
        (lt_mem_nhds hS0)).and hσev))
  -- `k̂ = σ g² √(K² − LΔ)` near every point near `r`
  have hkhat : ∀ᶠ s in 𝓝 r, effectiveKAux M Q e ω L g =ᶠ[𝓝 s]
      fun t => σ * g t ^ 2 * Real.sqrt (radialK e ω t ^ 2 - L * delta M Q t) :=
    hev.eventually_nhds.mono fun s hs => hs.mono fun t ht => by
      unfold effectiveKAux
      rw [ht.2.2.2]
  -- first derivative near `r`
  have hd1 : ∀ᶠ s in 𝓝 r, deriv (effectiveKAux M Q e ω L g) s =
      σ * (2 * g s * (c / delta M Q s)) * Real.sqrt (radialK e ω s ^ 2 - L * delta M Q s) +
        σ * g s ^ 2 * ((2 * radialK e ω s * (2 * ω * s - e) - L * (2 * (s - M))) /
          (2 * Real.sqrt (radialK e ω s ^ 2 - L * delta M Q s))) := by
    filter_upwards [hkhat, hev] with s h1 h2
    rw [h1.deriv_eq]
    exact (((hasDerivAt_gpow h2.1).1.const_mul σ).fun_mul
      ((hasDerivAt_radicand M Q e ω L s).sqrt h2.2.2.1.ne')).deriv
  -- `Δ g² k̂'` near `r`
  have hX : (fun s => delta M Q s * g s ^ 2 * deriv (effectiveKAux M Q e ω L g) s) =ᶠ[𝓝 r]
      fun s => σ * (2 * c * g s ^ 3 * Real.sqrt (radialK e ω s ^ 2 - L * delta M Q s) +
        delta M Q s * g s ^ 4 * (radialK e ω s * (2 * ω * s - e) - L * (s - M)) /
          Real.sqrt (radialK e ω s ^ 2 - L * delta M Q s)) := by
    filter_upwards [hd1, hev] with s h1 h2
    have hP : Real.sqrt (radialK e ω s ^ 2 - L * delta M Q s) ≠ 0 :=
      (Real.sqrt_pos.2 h2.2.2.1).ne'
    have hD : delta M Q s ≠ 0 := h2.2.1.ne'
    rw [h1]
    field_simp
  -- its derivative at `r`
  have hgr : HasDerivAt g (c / delta M Q r) r := hg.self_of_nhds
  have hK1 : HasDerivAt (fun t => 2 * ω * t - e) (2 * ω) r := by
    simpa using ((hasDerivAt_id' r).const_mul (2 * ω)).sub_const e
  have hN : HasDerivAt (fun t => radialK e ω t * (2 * ω * t - e) - L * (t - M)) _ r :=
    ((hasDerivAt_radialK e ω r).fun_mul hK1).sub (((hasDerivAt_id' r).sub_const M).const_mul L)
  have hP := (hasDerivAt_radicand M Q e ω L r).sqrt hS0.ne'
  have hX1 : HasDerivAt (fun s => σ * (2 * c * g s ^ 3 *
      Real.sqrt (radialK e ω s ^ 2 - L * delta M Q s) +
        delta M Q s * g s ^ 4 * (radialK e ω s * (2 * ω * s - e) - L * (s - M)) /
          Real.sqrt (radialK e ω s ^ 2 - L * delta M Q s))) _ r :=
    ((((hasDerivAt_gpow hgr).2.1.const_mul (2 * c)).fun_mul hP).fun_add
      ((((hasDerivAt_delta M Q r).fun_mul (hasDerivAt_gpow hgr).2.2).fun_mul hN).fun_div hP
        (Real.sqrt_pos.2 hS0).ne')).const_mul σ
  have hk : effectiveKAux M Q e ω L g r =
      σ * g r ^ 2 * Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r) :=
    hkhat.self_of_nhds.eq_of_nhds
  rw [hX.deriv_eq, hX1.deriv, hd1.self_of_nhds, hk]
  -- the algebra, with `q = √(1 − τ)` and `√(K² − LΔ) = σKq`
  have hτ1 : L * delta M Q r / radialK e ω r ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    exact hK
  have hq0 : 0 < Real.sqrt (1 - L * delta M Q r / radialK e ω r ^ 2) :=
    Real.sqrt_pos.2 (sub_pos.2 hτ1)
  have hq2 : Real.sqrt (1 - L * delta M Q r / radialK e ω r ^ 2) ^ 2 =
      1 - L * delta M Q r / radialK e ω r ^ 2 := Real.sq_sqrt (sub_pos.2 hτ1).le
  have hτ : L * delta M Q r / radialK e ω r ^ 2 =
      1 - Real.sqrt (1 - L * delta M Q r / radialK e ω r ^ 2) ^ 2 := by
    rw [hq2]
    ring
  have hPr : Real.sqrt (radialK e ω r ^ 2 - L * delta M Q r) =
      σ * radialK e ω r * Real.sqrt (1 - L * delta M Q r / radialK e ω r ^ 2) := by
    have e1 : radialK e ω r ^ 2 - L * delta M Q r =
        radialK e ω r ^ 2 * (1 - L * delta M Q r / radialK e ω r ^ 2) := by
      field_simp
    rw [e1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, hσK]
  exact khat_identities_alg hσ1 hg0.ne' hΔ.ne' hK0 hq0.ne' hPr hτ (delta_eq_sq_sub hQ r)

end ModeStability.AllAngular
