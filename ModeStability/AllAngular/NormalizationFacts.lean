module

public import Mathlib
public import ModeStability.Frozen.StaticSolution
public import ModeStability.Frozen.AllAngular.StaticSolutionAA
public import ModeStability.Frozen.AllAngular.NormalizationG
public import ModeStability.Frozen.AllAngular.XDeriv
public import ModeStability.Frozen.AllAngular.EffectiveK
public import ModeStability.Exterior.Basic
public import ModeStability.Exterior.Calculus
public import ModeStability.AllAngular.CoefficientIdentities
public import ModeStability.AllAngular.AngularAlgebra

/-!
# Facts on the frozen definitions `staticSolutionAA`, `normalizationG`, `xDeriv`, `effectiveK`

Source: the all-angular research notes in preparation, p. 2, (2.1)–(2.3), (2.5)–(2.7), and
p. 4, (3.2), (3.5)–(3.7). Helpers for the providers of `common_geometry` (Lemma 2.1),
`scalar_positivity` (Lemma 2.2) and `angular_positivity` (Proposition 3.1).

* `staticSolutionAA_eq_staticSolution`: for `δ > 0`, `h = (2δ)⁻¹ log((r − b)/(r − a))` is the
  frozen `staticSolution` `(a − b)⁻¹ log((r − b)/(r − a))`, since `a − b = 2δ`;
  `staticSolutionAA_eq_extremal`: for `δ = 0`, `h = 1/(r − M)`.
* `staticSolutionAA_pos`, `hasDerivAt_staticSolutionAA`: `h > 0` and `h' = −1/Δ` on the exterior.
* `gauge_facts`: the normalization `g = normalizationG` is locally `1` or `h`, so `Δ g' = c` with
  `c = 0` or `c = −1`, `g > 0`, and `χ = −c/g` is `0` or `1/h`.
* `xDeriv_k`, `xDeriv_khat`: (2.7) and (3.5)–(3.6) in the notation `∂ₓ = xDeriv` (`Δ g² ∂ᵣ`),
  from `ModeStability.AllAngular.xDeriv_k_identities` and
  `ModeStability.AllAngular.xDeriv_khat_identities`.
* `effectiveK_eq_effectiveKAux`: `effectiveK` is `effectiveKAux` for `g = normalizationG`.
* `angular_final_alg`: the algebra closing Proposition 3.1.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular.NormalizationFacts

/-! ### Elementary facts on the parameters -/

/-- `M² − Q² ≥ 0` for `|Q| ≤ M`. -/
theorem sub_sq_nonneg_of_abs_le {M Q : ℝ} (hQ : |Q| ≤ M) : 0 ≤ M ^ 2 - Q ^ 2 := by
  have h := sq_le_sq' (abs_le.1 hQ).1 (abs_le.1 hQ).2
  linarith

/-- `M² − Q² > 0` and `M > 0` give `|Q| < M`. -/
theorem abs_lt_of_sub_sq_pos {M Q : ℝ} (hM : 0 < M) (hδ : 0 < M ^ 2 - Q ^ 2) :
    |Q| < M :=
  abs_lt_of_sq_lt_sq (by linarith) hM.le

/-- The extremal case `δ = 0`: `M² − Q² = 0`, `√(M² − Q²) = 0`, `a = b = M`. -/
theorem extremal_facts {M Q : ℝ} (hQ : |Q| ≤ M) (hδ : ¬ 0 < M ^ 2 - Q ^ 2) :
    M ^ 2 - Q ^ 2 = 0 ∧ Real.sqrt (M ^ 2 - Q ^ 2) = 0 ∧ outerHorizon M Q = M ∧
      innerHorizon M Q = M := by
  have h0 : M ^ 2 - Q ^ 2 = 0 := le_antisymm (not_lt.1 hδ) (sub_sq_nonneg_of_abs_le hQ)
  have hs : Real.sqrt (M ^ 2 - Q ^ 2) = 0 := by rw [h0, Real.sqrt_zero]
  refine ⟨h0, hs, ?_, ?_⟩
  · unfold outerHorizon
    rw [hs, add_zero]
  · unfold innerHorizon
    rw [hs, sub_zero]

/-- `Δ(r) > 0` on the exterior `r > a`. -/
theorem delta_pos_of_outerHorizon_lt {M Q : ℝ} {r : ℝ} (hr : outerHorizon M Q < r) :
    0 < delta M Q r := by
  have hba : innerHorizon M Q ≤ outerHorizon M Q := by
    unfold innerHorizon outerHorizon
    linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]
  unfold delta
  exact mul_pos (sub_pos.2 hr) (by linarith)

/-- `z = r − M > 0` on the exterior. -/
theorem sub_M_pos_of_outerHorizon_lt {M Q : ℝ} {r : ℝ} (hr : outerHorizon M Q < r) :
    0 < r - M := by
  unfold outerHorizon at hr
  linarith [Real.sqrt_nonneg (M ^ 2 - Q ^ 2)]

/-! ### The static solution `h` and the normalization `g` -/

/-- For `δ > 0`, `staticSolutionAA` is the frozen `staticSolution`, since `a − b = 2δ`. -/
theorem staticSolutionAA_eq_staticSolution {M Q : ℝ} (hδ : 0 < M ^ 2 - Q ^ 2) :
    staticSolutionAA M Q = staticSolution M Q := by
  funext r
  have hd : outerHorizon M Q - innerHorizon M Q = 2 * Real.sqrt (M ^ 2 - Q ^ 2) := by
    unfold outerHorizon innerHorizon
    ring
  unfold staticSolutionAA staticSolution
  rw [ite_eq_left hδ, hd]

/-- For `δ = 0`, `h = 1/(r − M)`. -/
theorem staticSolutionAA_eq_extremal {M Q : ℝ} (hδ : ¬ 0 < M ^ 2 - Q ^ 2) :
    staticSolutionAA M Q = fun r => 1 / (r - M) := by
  funext r
  unfold staticSolutionAA
  rw [ite_eq_right hδ]

/-- `h(r) > 0` on the exterior. -/
theorem staticSolutionAA_pos {M Q : ℝ} (hM : 0 < M) {r : ℝ}
    (hr : outerHorizon M Q < r) : 0 < staticSolutionAA M Q r := by
  by_cases hδ : 0 < M ^ 2 - Q ^ 2
  · rw [staticSolutionAA_eq_staticSolution hδ]
    exact staticSolution_pos (abs_lt_of_sub_sq_pos hM hδ) hr
  · rw [staticSolutionAA_eq_extremal hδ]
    exact one_div_pos.2 (sub_M_pos_of_outerHorizon_lt hr)

/-- `h' = −1/Δ` on the exterior, in both the subextremal and the extremal case. -/
theorem hasDerivAt_staticSolutionAA {M Q : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) {r : ℝ}
    (hr : outerHorizon M Q < r) :
    HasDerivAt (staticSolutionAA M Q) (-1 / delta M Q r) r := by
  by_cases hδ : 0 < M ^ 2 - Q ^ 2
  · rw [staticSolutionAA_eq_staticSolution hδ]
    exact hasDerivAt_staticSolution (abs_lt_of_sub_sq_pos hM hδ) hr
  · obtain ⟨-, -, ha, hb⟩ := extremal_facts hQ hδ
    rw [staticSolutionAA_eq_extremal hδ]
    have hne : r - M ≠ 0 := (sub_M_pos_of_outerHorizon_lt hr).ne'
    have h := (hasDerivAt_const r (1 : ℝ)).div ((hasDerivAt_id' r).sub_const M) hne
    refine h.congr_deriv ?_
    unfold delta
    rw [ha, hb]
    field_simp
    ring

/-- `g = 1` when `e/ω < 2M`. -/
theorem normalizationG_eq_one {M Q e ω : ℝ} (h : e / ω < 2 * M) :
    normalizationG M Q e ω = fun _ => 1 := by
  funext r
  unfold normalizationG
  rw [ite_eq_left h]

/-- `g = h` when `e/ω ≥ 2M`. -/
theorem normalizationG_eq_static {M Q e ω : ℝ} (h : ¬ e / ω < 2 * M) :
    normalizationG M Q e ω = staticSolutionAA M Q := by
  funext r
  unfold normalizationG
  rw [ite_eq_right h]

/-- The gauge facts: near an exterior point, `Δ g' = c` (`c = 0` for `g = 1`, `c = −1` for
`g = h`), `g > 0`, and `χ = −c/g` is `0` resp. `1/h`. -/
theorem gauge_facts {M Q e ω : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) {r : ℝ}
    (hr : outerHorizon M Q < r) :
    ∃ c : ℝ, (∀ᶠ s in 𝓝 r, HasDerivAt (normalizationG M Q e ω) (c / delta M Q s) s) ∧
      0 < normalizationG M Q e ω r ∧
      -c / normalizationG M Q e ω r =
        (if e / ω < 2 * M then 0 else 1 / staticSolutionAA M Q r) := by
  by_cases h : e / ω < 2 * M
  · refine ⟨0, Filter.Eventually.of_forall fun s => ?_, ?_, ?_⟩
    · rw [normalizationG_eq_one h, zero_div]
      exact hasDerivAt_const s 1
    · rw [normalizationG_eq_one h]
      exact one_pos
    · rw [ite_eq_left h, neg_zero, zero_div]
  · refine ⟨-1, ?_, ?_, ?_⟩
    · rw [normalizationG_eq_static h]
      filter_upwards [lt_mem_nhds hr] with s hs
      exact hasDerivAt_staticSolutionAA hM hQ hs
    · rw [normalizationG_eq_static h]
      exact staticSolutionAA_pos hM hr
    · rw [ite_eq_right h, normalizationG_eq_static h, neg_neg]

/-! ### The identities (2.7), (3.5), (3.6) in the `xDeriv` notation -/

/-- (2.7) with `∂ₓ = xDeriv`: `k_x = g⁴H`, `2k_x² − k k_xx = g⁸A₀` for `k = g²K`, `Δg' = c`,
`χ = −c/g`. -/
theorem xDeriv_k {M Q e ω c : ℝ} {g : ℝ → ℝ} {r : ℝ} (hΔ : delta M Q r ≠ 0)
    (hg0 : g r ≠ 0) (hg : ∀ᶠ s in 𝓝 r, HasDerivAt g (c / delta M Q s) s) :
    xDeriv M Q g (fun s => g s ^ 2 * radialK e ω s) r =
        g r ^ 4 * (delta M Q r * (2 * ω * r - e) - 2 * (-c / g r) * radialK e ω r) ∧
      2 * xDeriv M Q g (fun s => g s ^ 2 * radialK e ω s) r ^ 2 -
          g r ^ 2 * radialK e ω r *
            xDeriv M Q g (xDeriv M Q g (fun s => g s ^ 2 * radialK e ω s)) r =
        g r ^ 8 * (2 * delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
          2 * delta M Q r * ((-c / g r) + (r - M)) * radialK e ω r * (2 * ω * r - e) -
          delta M Q r ^ 2 * radialK e ω r * (2 * ω) + 2 * (-c / g r) ^ 2 * radialK e ω r ^ 2) :=
  ModeStability.AllAngular.xDeriv_k_identities hΔ hg0 hg

/-- (3.5), (3.6) with `∂ₓ = xDeriv`, for `k̂ = effectiveKAux g`. -/
theorem xDeriv_khat {M Q e ω c L : ℝ} {g : ℝ → ℝ} {r : ℝ} (hQ : |Q| ≤ M)
    (hL : 0 ≤ L) (hΔ : 0 < delta M Q r) (hg0 : 0 < g r)
    (hK : L * delta M Q r < radialK e ω r ^ 2)
    (hg : ∀ᶠ s in 𝓝 r, HasDerivAt g (c / delta M Q s) s) :
    xDeriv M Q g (effectiveKAux M Q e ω L g) r =
        g r ^ 4 / Real.sqrt (1 - L * delta M Q r / radialK e ω r ^ 2) *
          ((1 - L * delta M Q r / radialK e ω r ^ 2) *
              (delta M Q r * (2 * ω * r - e) - 2 * (-c / g r) * radialK e ω r) +
            L * delta M Q r / radialK e ω r ^ 2 *
              (delta M Q r * (2 * ω * r - e) - (r - M) * radialK e ω r)) ∧
      2 * xDeriv M Q g (effectiveKAux M Q e ω L g) r ^ 2 -
          effectiveKAux M Q e ω L g r *
            xDeriv M Q g (xDeriv M Q g (effectiveKAux M Q e ω L g)) r =
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
            (1 - L * delta M Q r / radialK e ω r ^ 2)) :=
  ModeStability.AllAngular.xDeriv_khat_identities hQ hL hΔ hg0 hK hg

/-- `effectiveK` is `effectiveKAux` for the gauge `g = normalizationG`. -/
theorem effectiveK_eq_effectiveKAux (M Q e ω L : ℝ) :
    effectiveK M Q e ω L = effectiveKAux M Q e ω L (normalizationG M Q e ω) :=
  rfl

/-- The algebra closing Proposition 3.1: with `k̂_x = G⁴S/q`, `E_k̂ = G⁸N`, `k_x = G⁴H`,
`E_k = G⁸A₀`, `S = (1 − τ)H + τT`, `N = (1 − τ)A₀ + τB + 3T²τ²/(1 − τ)`, `q² = 1 − τ`. -/
theorem angular_final_alg {G q τ A₀ B H T : ℝ} (hG : 0 < G) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hq : 0 < q) (hq2 : q ^ 2 = 1 - τ) (hA₀ : 0 < A₀) (hH : 0 < H) (hT : 0 < T)
    (hB : A₀ + 2 * T ^ 2 < B) :
    0 < G ^ 4 / q * ((1 - τ) * H + τ * T) ∧
      0 < G ^ 8 * ((1 - τ) * A₀ + τ * B + 3 * T ^ 2 * τ ^ 2 / (1 - τ)) ∧
      min (G ^ 8 * A₀ / (G ^ 4 * H) ^ 2) 2 ≤
        G ^ 8 * ((1 - τ) * A₀ + τ * B + 3 * T ^ 2 * τ ^ 2 / (1 - τ)) /
          (G ^ 4 / q * ((1 - τ) * H + τ * T)) ^ 2 := by
  have hS := ModeStability.AllAngular.angular_slope_pos hH hT hτ0 hτ1
  have hBpos : 0 < B := by nlinarith only [hA₀, hB, sq_nonneg T]
  have hN := ModeStability.AllAngular.angular_numerator_pos (T := T) hA₀ hBpos hτ0 hτ1
  refine ⟨mul_pos (div_pos (pow_pos hG 4) hq) hS, mul_pos (pow_pos hG 8) hN, ?_⟩
  have hG0 : G ≠ 0 := hG.ne'
  have e1 : ∀ X Y : ℝ, Y ≠ 0 → G ^ 8 * X / (G ^ 4 * Y) ^ 2 = X / Y ^ 2 := by
    intro X Y hY
    field_simp
  have e2 : ∀ X Y : ℝ, Y ≠ 0 → G ^ 8 * X / (G ^ 4 / q * Y) ^ 2 = X / Y ^ 2 * (1 - τ) := by
    intro X Y hY
    rw [← hq2]
    field_simp
  rw [e1 _ _ hH.ne', e2 _ _ hS.ne', ModeStability.AllAngular.angular_ratio_eq (ne_of_lt hτ1)]
  exact ModeStability.AllAngular.angular_ratio_ge_min hA₀ hH hT hB.le (sub_pos.2 hτ1) hτ0
    (sub_add_cancel 1 τ)

end ModeStability.AllAngular.NormalizationFacts

end
