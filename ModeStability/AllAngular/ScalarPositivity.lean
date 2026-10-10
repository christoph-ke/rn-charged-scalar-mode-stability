module

public import Mathlib
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK

/-!
# Scalar positivity (Lemma 2.2 of the all-angular paper)

Lemma 2.2 of the all-angular research notes in preparation (p. 3): in the superradiant regime
(1.7) (`ω > 0`, `r₀ = e/ω > a`, so `K = ωr² − er = ωr(r − r₀)`), for the frequency-dependent
normalization (2.2) the scalar coefficients `H` of (2.5) and `A₀` of (2.6) are positive throughout
the exterior `r > a`.

* `scalar_positivity_constant`: the range `a < r₀ < 2M` (`g = 1`, `χ = 0`), where
  `H = ΔK'` and `A₀ = 2Δ²K'² − 2ΔzKK' − Δ²KK''`.
* `scalar_positivity_reciprocal`: the range `r₀ ≥ 2M` (`g = h`, `χ = 1/h`), stated for any
  `χ > 0` satisfying the bounds (2.8) of Lemma 2.1, `ε = z − χ`; here `H = ΔK' − 2χK` and
  `A₀ = 2Δ²K'² − 2Δ(χ + z)KK' − Δ²KK'' + 2χ²K²`.

Notation: `δ = √(M² − Q²)`, `a = M + δ`, `b = M − δ`, `Δ = (r − a)(r − b)`, `z = r − M`,
`K' = 2ωr − ωr₀`, `K'' = 2ω`, `T = ΔK' − zK` (2.5).

The proof follows the paper. The first claim `T > δ|K|` of Lemma 2.1 enters through the
factorizations (2.9)–(2.10), which are reproved here locally (`T_pm_pos_aux`). The algebraic
cores are stated over a free parameter `s` standing for `δ`.
-/

public section

open Set

namespace ModeStability.AllAngular

/-- For `|Q| ≤ M`: `0 ≤ δ ≤ M` and `δ² = M² − Q²`, where `δ = √(M² − Q²)`. -/
private theorem sqrt_facts_aux {M Q : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) :
    0 ≤ Real.sqrt (M ^ 2 - Q ^ 2) ∧ Real.sqrt (M ^ 2 - Q ^ 2) ≤ M ∧
      Real.sqrt (M ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - Q ^ 2 := by
  have hQ2 : Q ^ 2 ≤ M ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg Q) hQ 2
    rwa [sq_abs] at h
  exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.2 ⟨hM.le, by nlinarith [sq_nonneg Q]⟩,
    Real.sq_sqrt (by linarith)⟩

/-- Local form of the first claim of Lemma 2.1 (`T > δ|K|`) via the factorizations (2.9)–(2.10):
`T − δK = ω(r − b)[(r − a)² + a(r₀ − a)] > 0` and `T + δK = ω(r − a)[(r − b)² + b(r₀ − b)] > 0`,
with `δ = s`, `a = M + s`, `b = M − s`. -/
private theorem T_pm_pos_aux {M s ω r₀ r : ℝ} (hM : 0 < M) (hs : 0 ≤ s) (hsM : s ≤ M)
    (hω : 0 < ω) (ha : M + s < r₀) (hr : M + s < r) :
    0 < (r - (M + s)) * (r - (M - s)) * (2 * ω * r - ω * r₀) -
          (r - M) * (ω * r ^ 2 - ω * r₀ * r) - s * (ω * r ^ 2 - ω * r₀ * r) ∧
      0 < (r - (M + s)) * (r - (M - s)) * (2 * ω * r - ω * r₀) -
          (r - M) * (ω * r ^ 2 - ω * r₀ * r) + s * (ω * r ^ 2 - ω * r₀ * r) := by
  have hra : 0 < r - (M + s) := by linarith
  have hrb : 0 < r - (M - s) := by linarith
  have hb : 0 ≤ M - s := by linarith
  have hr₀a : 0 < r₀ - (M + s) := by linarith
  have hr₀b : 0 < r₀ - (M - s) := by linarith
  have ha0 : 0 < M + s := by linarith
  constructor
  · have h : (r - (M + s)) * (r - (M - s)) * (2 * ω * r - ω * r₀) -
          (r - M) * (ω * r ^ 2 - ω * r₀ * r) - s * (ω * r ^ 2 - ω * r₀ * r) =
        ω * (r - (M - s)) * ((r - (M + s)) ^ 2 + (M + s) * (r₀ - (M + s))) := by ring
    rw [h]
    exact mul_pos (mul_pos hω hrb) (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos ha0 hr₀a))
  · have h : (r - (M + s)) * (r - (M - s)) * (2 * ω * r - ω * r₀) -
          (r - M) * (ω * r ^ 2 - ω * r₀ * r) + s * (ω * r ^ 2 - ω * r₀ * r) =
        ω * (r - (M + s)) * ((r - (M - s)) ^ 2 + (M - s) * (r₀ - (M - s))) := by ring
    rw [h]
    exact mul_pos (mul_pos hω hra)
      (add_pos_of_pos_of_nonneg (pow_pos hrb 2) (mul_nonneg hb hr₀b.le))

/-- Algebraic core of the constant normalization `a < r₀ < 2M` (`χ = 0`), with `δ = s`. -/
private theorem constant_core {M s ω r₀ r Δ K : ℝ} (hM : 0 < M) (hs : 0 ≤ s) (hsM : s ≤ M)
    (hω : 0 < ω) (ha : M + s < r₀) (h2M : r₀ < 2 * M) (hr : M + s < r)
    (hΔ : (r - (M + s)) * (r - (M - s)) = Δ) (hK : ω * r ^ 2 - ω * r₀ * r = K) :
    0 < Δ * (2 * ω * r - ω * r₀) ∧
      0 < 2 * Δ ^ 2 * (2 * ω * r - ω * r₀) ^ 2 - 2 * Δ * (r - M) * K * (2 * ω * r - ω * r₀) -
          Δ ^ 2 * K * (2 * ω) := by
  obtain ⟨hTm, hTp⟩ := T_pm_pos_aux hM hs hsM hω ha hr
  -- `ωΔ² − zT = δ²K − ω(c₀ + δ²)Δ` with `c₀ = M(r₀ − M)`, first identity of (2.11).
  have hzT : (r - M) * (Δ * (2 * ω * r - ω * r₀) - (r - M) * K) - ω * Δ ^ 2 =
      ω * (M * (r₀ - M) + s ^ 2) * Δ - s ^ 2 * K := by
    rw [← hΔ, ← hK]; ring
  rw [hΔ, hK] at hTm hTp
  have hΔpos : 0 < Δ := hΔ ▸ mul_pos (by linarith) (by linarith)
  have hK1 : 0 < 2 * ω * r - ω * r₀ := by
    have h : 2 * ω * r - ω * r₀ = ω * (2 * r - r₀) := by ring
    rw [h]
    exact mul_pos hω (by linarith)
  have hz : 0 < r - M := by linarith
  refine ⟨mul_pos hΔpos hK1, ?_⟩
  rcases lt_or_ge K 0 with hKneg | hKnn
  · -- `K < 0`: all three terms of `A₀` are positive.
    have hm : 0 < -K := neg_pos.2 hKneg
    have h1 : 0 < Δ ^ 2 * (2 * ω * r - ω * r₀) ^ 2 := by positivity
    have h2 : 0 < Δ * (r - M) * (-K) * (2 * ω * r - ω * r₀) :=
      mul_pos (mul_pos (mul_pos hΔpos hz) hm) hK1
    have h3 : 0 < Δ ^ 2 * (-K) * ω := mul_pos (mul_pos (pow_pos hΔpos 2) hm) hω
    linarith
  · -- `K ≥ 0`: `A₀/2 = T² − δ²K² + ω(c₀ + δ²)ΔK`, second identity of (2.11).
    have hc : 0 < M * (r₀ - M) + s ^ 2 :=
      add_pos_of_pos_of_nonneg (mul_pos hM (by linarith)) (sq_nonneg s)
    have key : 2 * Δ ^ 2 * (2 * ω * r - ω * r₀) ^ 2 -
          2 * Δ * (r - M) * K * (2 * ω * r - ω * r₀) - Δ ^ 2 * K * (2 * ω) =
        2 * ((Δ * (2 * ω * r - ω * r₀) - (r - M) * K - s * K) *
            (Δ * (2 * ω * r - ω * r₀) - (r - M) * K + s * K)) +
          2 * (ω * (M * (r₀ - M) + s ^ 2) * Δ * K) := by
      linear_combination (2 * K) * hzT
    rw [key]
    have h1 := mul_pos hTm hTp
    have h2 : 0 ≤ ω * (M * (r₀ - M) + s ^ 2) * Δ * K :=
      mul_nonneg (mul_nonneg (mul_pos hω hc).le hΔpos.le) hKnn
    linarith

/-- Algebraic core of the reciprocal normalization `r₀ ≥ 2M`, with `δ = s` and `ε = z − χ`
satisfying (2.8). -/
private theorem reciprocal_core {M s ω r₀ r χ Δ K : ℝ} (hM : 0 < M) (hs : 0 ≤ s) (hsM : s ≤ M)
    (hω : 0 < ω) (ha : M + s < r₀) (h2M : 2 * M ≤ r₀) (hr : M + s < r)
    (hχ : 0 < χ) (hε0 : 0 ≤ (r - M) - χ) (hεδ : (r - M) - χ ≤ s)
    (hεχ : ((r - M) - χ) * (s + χ) ≤ s ^ 2)
    (hΔ : (r - (M + s)) * (r - (M - s)) = Δ) (hK : ω * r ^ 2 - ω * r₀ * r = K) :
    0 < Δ * (2 * ω * r - ω * r₀) - 2 * χ * K ∧
      0 < 2 * Δ ^ 2 * (2 * ω * r - ω * r₀) ^ 2 -
          2 * Δ * (χ + (r - M)) * K * (2 * ω * r - ω * r₀) -
          Δ ^ 2 * K * (2 * ω) + 2 * χ ^ 2 * K ^ 2 := by
  obtain ⟨hTm, hTp⟩ := T_pm_pos_aux hM hs hsM hω ha hr
  -- (2.12): `D₀ = ΔK' − 2zK = ω[(r₀ − 2M)r² + (2r − r₀)Q²]`, with `Q² = M² − δ²`.
  have hD0 : Δ * (2 * ω * r - ω * r₀) - 2 * (r - M) * K =
      ω * ((r₀ - 2 * M) * r ^ 2 + (2 * r - r₀) * (M ^ 2 - s ^ 2)) := by
    rw [← hΔ, ← hK]; ring
  have hKsq : (2 * ω * r - ω * r₀) ^ 2 = 4 * ω * K + ω ^ 2 * r₀ ^ 2 := by
    rw [← hK]; ring
  have hKr : K = ω * r * (r - r₀) := by rw [← hK]; ring
  rw [hΔ, hK] at hTm hTp
  have hΔpos : 0 < Δ := hΔ ▸ mul_pos (by linarith) (by linarith)
  have hr0 : 0 < r := by linarith
  have hr₀ : 0 < r₀ := by linarith
  rcases lt_or_ge K 0 with hKneg | hKnn
  · -- `K < 0` (`r < r₀`).
    have hm : 0 < -K := neg_pos.2 hKneg
    constructor
    · -- `H = (T + δK) + |K|(δ − ε + χ)`.
      have h : 0 < (-K) * (s - ((r - M) - χ) + χ) := mul_pos hm (by linarith)
      linarith
    · -- (2.13)–(2.14) with `u = T + δK = T − δ|K| > 0`:
      -- `A₀/2 = K²[δ² − ε(δ + χ)] + u(|K|(2δ − ε) + u) + ωΔ²|K|`.
      have h1 : 0 ≤ K ^ 2 * (s ^ 2 - ((r - M) - χ) * (s + χ)) :=
        mul_nonneg (sq_nonneg K) (by linarith)
      have h2 : 0 < (Δ * (2 * ω * r - ω * r₀) - (r - M) * K + s * K) *
          ((-K) * (2 * s - ((r - M) - χ)) + (Δ * (2 * ω * r - ω * r₀) - (r - M) * K + s * K)) :=
        mul_pos hTp (add_pos_of_nonneg_of_pos (mul_nonneg hm.le (by linarith)) hTp)
      have h3 : 0 < ω * Δ ^ 2 * (-K) := mul_pos (mul_pos hω (pow_pos hΔpos 2)) hm
      have key : 2 * Δ ^ 2 * (2 * ω * r - ω * r₀) ^ 2 -
            2 * Δ * (χ + (r - M)) * K * (2 * ω * r - ω * r₀) -
            Δ ^ 2 * K * (2 * ω) + 2 * χ ^ 2 * K ^ 2 =
          2 * (K ^ 2 * (s ^ 2 - ((r - M) - χ) * (s + χ)) +
            (Δ * (2 * ω * r - ω * r₀) - (r - M) * K + s * K) *
              ((-K) * (2 * s - ((r - M) - χ)) +
                (Δ * (2 * ω * r - ω * r₀) - (r - M) * K + s * K)) +
            ω * Δ ^ 2 * (-K)) := by
        ring
      rw [key]
      linarith
  · -- `K ≥ 0` (`r ≥ r₀`).
    have hrr : 0 ≤ r - r₀ := by
      by_contra h
      have h' : ω * r * (r - r₀) < 0 := mul_neg_of_pos_of_neg (mul_pos hω hr0) (by linarith)
      linarith
    -- `D₀ > 0`: `(r₀ − 2M)r² + (2r − r₀)(M² − δ²) ≥ rM(r₀ − M − δ) > 0`.
    have hD0pos : 0 < Δ * (2 * ω * r - ω * r₀) - 2 * (r - M) * K := by
      rw [hD0]
      have h1 : 0 ≤ (r₀ - 2 * M) * (r * (r - M)) :=
        mul_nonneg (by linarith) (mul_nonneg hr0.le (by linarith))
      have h2 : 0 ≤ (M - s) * ((r - r₀) * (M + s) + r * s) :=
        mul_nonneg (by linarith) (add_nonneg (mul_nonneg hrr (by linarith)) (mul_nonneg hr0.le hs))
      have h3 : 0 < r * M * (r₀ - M - s) := mul_pos (mul_pos hr0 hM) (by linarith)
      have h : (r₀ - 2 * M) * r ^ 2 + (2 * r - r₀) * (M ^ 2 - s ^ 2) =
          (r₀ - 2 * M) * (r * (r - M)) + (M - s) * ((r - r₀) * (M + s) + r * s) +
            r * M * (r₀ - M - s) := by ring
      rw [h]
      exact mul_pos hω (by linarith)
    have hK1 : 0 < 2 * ω * r - ω * r₀ := by
      have h : 2 * ω * r - ω * r₀ = ω * ((r - r₀) + r) := by ring
      rw [h]
      exact mul_pos hω (by linarith)
    have hεK : 0 ≤ ((r - M) - χ) * K := mul_nonneg hε0 hKnn
    constructor
    · -- `H = D₀ + 2εK`.
      linarith
    · -- (2.13): `T ≥ ΔK'/2 > 0`, `T − χK = D₀ + εK ≥ 0`, `K'² = 4ωK + ω²r₀²`.
      have hΔK1 : 0 < Δ * (2 * ω * r - ω * r₀) := mul_pos hΔpos hK1
      have h1 : 0 ≤ (Δ * (2 * ω * r - ω * r₀) - (r - M) * K - Δ * (2 * ω * r - ω * r₀) / 2) *
          (Δ * (2 * ω * r - ω * r₀) - (r - M) * K + Δ * (2 * ω * r - ω * r₀) / 2) :=
        mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ ((r - M) - χ) * K * (Δ * (2 * ω * r - ω * r₀) - (r - M) * K - χ * K) :=
        mul_nonneg hεK (by linarith)
      have h3 : 0 < Δ ^ 2 * ω ^ 2 * r₀ ^ 2 := by positivity
      have key : 2 * Δ ^ 2 * (2 * ω * r - ω * r₀) ^ 2 -
            2 * Δ * (χ + (r - M)) * K * (2 * ω * r - ω * r₀) -
            Δ ^ 2 * K * (2 * ω) + 2 * χ ^ 2 * K ^ 2 =
          2 * ((Δ * (2 * ω * r - ω * r₀) - (r - M) * K - Δ * (2 * ω * r - ω * r₀) / 2) *
            (Δ * (2 * ω * r - ω * r₀) - (r - M) * K + Δ * (2 * ω * r - ω * r₀) / 2)) +
          2 * (((r - M) - χ) * K * (Δ * (2 * ω * r - ω * r₀) - (r - M) * K - χ * K)) +
          Δ ^ 2 * ω ^ 2 * r₀ ^ 2 / 2 := by
        linear_combination (Δ ^ 2 / 2) * hKsq
      rw [key]
      linarith

/-- Lemma 2.2, constant normalization `a < r₀ < 2M` (`g = 1`, `χ = 0`): `H = ΔK' > 0` and
`A₀ = 2Δ²K'² − 2ΔzKK' − Δ²KK'' > 0`. -/
theorem scalar_positivity_constant {M Q ω r₀ : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < r₀) (h2M : r₀ < 2 * M) {r : ℝ} (hr : outerHorizon M Q < r) :
    0 < delta M Q r * (2 * ω * r - ω * r₀) ∧
      0 < 2 * delta M Q r ^ 2 * (2 * ω * r - ω * r₀) ^ 2 -
          2 * delta M Q r * (r - M) * radialK (ω * r₀) ω r * (2 * ω * r - ω * r₀) -
          delta M Q r ^ 2 * radialK (ω * r₀) ω r * (2 * ω) := by
  obtain ⟨hs, hsM, -⟩ := sqrt_facts_aux hM hQ
  unfold outerHorizon at ha hr
  exact constant_core hM hs hsM hω ha h2M hr rfl rfl

/-- Lemma 2.2, reciprocal normalization `r₀ ≥ 2M` (`g = h`, `χ = 1/h`), stated for any `χ`
with the bounds (2.8) of Lemma 2.1 (`ε = z − χ`): `H = ΔK' − 2χK > 0` and
`A₀ = 2Δ²K'² − 2Δ(χ + z)KK' − Δ²KK'' + 2χ²K² > 0`. -/
theorem scalar_positivity_reciprocal {M Q ω r₀ : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hω : 0 < ω)
    (ha : outerHorizon M Q < r₀) (h2M : 2 * M ≤ r₀) {r : ℝ} (hr : outerHorizon M Q < r)
    {χ : ℝ} (hχ : 0 < χ) (hε0 : 0 ≤ (r - M) - χ) (hεδ : (r - M) - χ ≤ Real.sqrt (M ^ 2 - Q ^ 2))
    (hεχ : ((r - M) - χ) * (Real.sqrt (M ^ 2 - Q ^ 2) + χ) ≤ M ^ 2 - Q ^ 2) :
    0 < delta M Q r * (2 * ω * r - ω * r₀) - 2 * χ * radialK (ω * r₀) ω r ∧
      0 < 2 * delta M Q r ^ 2 * (2 * ω * r - ω * r₀) ^ 2 -
          2 * delta M Q r * (χ + (r - M)) * radialK (ω * r₀) ω r * (2 * ω * r - ω * r₀) -
          delta M Q r ^ 2 * radialK (ω * r₀) ω r * (2 * ω) +
          2 * χ ^ 2 * radialK (ω * r₀) ω r ^ 2 := by
  obtain ⟨hs, hsM, hsq⟩ := sqrt_facts_aux hM hQ
  unfold outerHorizon at ha hr
  exact reciprocal_core hM hs hsM hω ha h2M hr hχ hε0 hεδ (hεχ.trans_eq hsq.symm) rfl rfl

end ModeStability.AllAngular

end
