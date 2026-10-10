module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.AllAngular.FluxL

/-!
# Zero frequency: an `L²` solution has zero flux

Source: the all-angular research notes in preparation, p. 9, Proposition 7.1 and its proof. At
`ω = 0` we have
`K = −er` and the radial equation (7.2) is `(ΔR')' + (e²r²/Δ − L)R = 0`. For `e ≠ 0` the paper
uses Frobenius theory at infinity (exponents `−1/2 ± ν`) to show that a solution with
`∫_a^∞ |R|² < ∞` (7.1) is the real decaying branch, hence has zero flux, which contradicts the
horizon flux `Δ Im(R' R̄) = e a |B_H|²`. Here the Frobenius step is replaced by a limit-point
argument that needs only the boundedness of the coefficient `q = e²r²/Δ − L` at infinity.

* `zero_frequency_flux_eq_zero_of_integrable`: an `L²` solution at `ω = 0` has
  `Δ Im(R' R̄) ≡ 0` on `(a, ∞)` (no hypothesis on `Q`, `e` or the sign of `L`).
* `zero_frequency_charged`: for `e ≠ 0`, an `L²` solution with the Θ-form horizon condition
  (1.4) with leading coefficient `B` has `B = 0` (the flux tends to `−K(a)‖B‖² = e a ‖B‖²` by
  `tendsto_flux_horizon_L`).

The argument (`zi_flux_bound`). Let `F` be the constant flux and `G = Δ R' R̄`, so `Im G = F`,
`(Re G)² + F² = ‖G‖² = Δ · Δ‖R'‖² · ‖R‖²` and `(Re G)' = Δ‖R'‖² − q‖R‖²`. On `[ρ, 2ρ]`,
`ρ ≥ 2a`, take the weight `χ = (r − ρ)(2ρ − r)`, which vanishes at both ends, and
`T = |F| ∫χ² − ρ χ² Re G`. By AM–GM (`zi_core`, a Caccioppoli-type absorption),
`T' = |F|χ² − ρ(2χχ' Re G + χ²(Δ‖R'‖² − q‖R‖²)) ≤ (2ρχ'²Δ + ρχ²|q| + χ²Δ/(2ρ))‖R‖²`, and the
coefficient is `≤ (9 + 4e² + |L|)ρ⁵` because `Δ ≤ 4ρ²`, `χ ≤ ρ²/4`, `|χ'| ≤ ρ`, `|q| ≤ 4e² + |L|`.
Integrating (`intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le`, which needs no
integrability of `T'`), `|F| ρ⁵/30 ≤ (9 + 4e² + |L|) ρ⁵ ∫_ρ^{2ρ} ‖R‖²`. The right side tends to
`0` as `ρ → ∞`, so `F = 0`.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

/-- Algebraic core of the estimate: if `g² + C² = D A u` with `A, u, D ≥ 0` and `λ > 0`, then
`|C| x² − λ(2xyg + x²(A − qu)) ≤ (2λy²D + λx²|q| + x²D/(2λ)) u`. Here `g = Re G`, `C = Im G`,
`A = Δ‖R'‖²`, `u = ‖R‖²`, `D = Δ`, `x = χ`, `y = χ'`. -/
theorem zi_core {C g A u D lam x y q : ℝ} (hA : 0 ≤ A) (hu : 0 ≤ u) (hD : 0 ≤ D)
    (hlam : 0 < lam) (hG : g ^ 2 + C ^ 2 = D * A * u) :
    |C| * x ^ 2 - lam * (2 * x * y * g + x ^ 2 * (A - q * u)) ≤
      (2 * lam * y ^ 2 * D + lam * x ^ 2 * |q| + x ^ 2 * D / (2 * lam)) * u := by
  have h1 : |C| ≤ lam / 2 * A + D * u / (2 * lam) := by
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    have key : (lam / 2 * A + D * u / (2 * lam)) ^ 2 =
        (lam / 2 * A - D * u / (2 * lam)) ^ 2 + D * A * u := by
      field_simp
      ring
    nlinarith [sq_nonneg g, sq_nonneg (lam / 2 * A - D * u / (2 * lam))]
  have h2 : -(2 * x * y * g) ≤ x ^ 2 * A / 2 + 2 * y ^ 2 * D * u := by
    have h : |2 * x * y * g| ≤ x ^ 2 * A / 2 + 2 * y ^ 2 * D * u := by
      refine abs_le_of_sq_le_sq ?_ (by positivity)
      have key : (x ^ 2 * A / 2 + 2 * y ^ 2 * D * u) ^ 2 =
          (x ^ 2 * A / 2 - 2 * y ^ 2 * D * u) ^ 2 + 4 * (x ^ 2 * y ^ 2) * (D * A * u) := by
        ring
      have hg : (2 * x * y * g) ^ 2 ≤ 4 * (x ^ 2 * y ^ 2) * (D * A * u) := by
        rw [← hG]
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg y)) (sq_nonneg C)]
      nlinarith [sq_nonneg (x ^ 2 * A / 2 - 2 * y ^ 2 * D * u)]
    linarith [neg_abs_le (2 * x * y * g)]
  have h3 : x ^ 2 * q * u ≤ x ^ 2 * |q| * u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self q) (sq_nonneg x)) hu
  have e1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg x)
  have e2 := mul_le_mul_of_nonneg_left h2 hlam.le
  have e3 := mul_le_mul_of_nonneg_left h3 hlam.le
  linear_combination e1 + e2 + e3

/-- `0 ≤ b` for `M > 0`. -/
theorem zi_innerHorizon_nonneg {M Q : ℝ} (hM : 0 < M) :
    0 ≤ innerHorizon M Q := by
  unfold innerHorizon
  have h : Real.sqrt (M ^ 2 - Q ^ 2) ≤ M := by
    rw [Real.sqrt_le_left hM.le]
    nlinarith [sq_nonneg Q]
  linarith

/-- `0 < a` for `M > 0`. -/
theorem zi_outerHorizon_pos {M Q : ℝ} (hM : 0 < M) : 0 < outerHorizon M Q := by
  unfold outerHorizon
  have := Real.sqrt_nonneg (M ^ 2 - Q ^ 2)
  linarith

/-- On `[2a, ∞)`: `r²/4 ≤ Δ(r) ≤ r²`. -/
theorem zi_delta_bounds {M Q r : ℝ} (hM : 0 < M) (hr : 2 * outerHorizon M Q ≤ r) :
    r ^ 2 / 4 ≤ delta M Q r ∧ delta M Q r ≤ r ^ 2 := by
  have ha := zi_outerHorizon_pos (Q := Q) hM
  have hb := zi_innerHorizon_nonneg (Q := Q) hM
  have hba := fl_innerHorizon_le M Q
  unfold delta
  constructor <;> nlinarith

/-- Derivative of the cutoff weight `χ² = ((r − ρ)(2ρ − r))²`. -/
theorem zi_hasDerivAt_weight (ρ r : ℝ) :
    HasDerivAt (fun s : ℝ => ((s - ρ) * (2 * ρ - s)) ^ 2)
      (2 * ((r - ρ) * (2 * ρ - r)) * (3 * ρ - 2 * r)) r := by
  have h := (((hasDerivAt_id r).sub_const ρ).mul ((hasDerivAt_const r (2 * ρ)).sub
    (hasDerivAt_id r))).pow 2
  refine h.congr_deriv ?_
  simp only [id, Pi.mul_apply, Pi.sub_apply]
  ring

/-- Antiderivative of the cutoff weight. -/
theorem zi_hasDerivAt_primitive (ρ r : ℝ) :
    HasDerivAt (fun s : ℝ => ρ ^ 2 * (s - ρ) ^ 3 / 3 - ρ * (s - ρ) ^ 4 / 2 + (s - ρ) ^ 5 / 5)
      (((r - ρ) * (2 * ρ - r)) ^ 2) r := by
  have h1 := (hasDerivAt_id r).sub_const ρ
  have h := (((h1.pow 3).const_mul (ρ ^ 2)).div_const 3).sub (((h1.pow 4).const_mul ρ).div_const 2)
    |>.add ((h1.pow 5).div_const 5)
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- Derivative of `Re(Δ R' R̄)`: `(Re(Δ R' R̄))' = Δ‖R'‖² − q‖R‖²`. -/
theorem zi_hasDerivAt_re {M Q e ω L : ℝ} {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {r : ℝ} (hr : r ∈ Ioi (outerHorizon M Q)) :
    HasDerivAt (fun s => ((delta M Q s : ℂ) * deriv R s * (starRingEnd ℂ) (R s)).re)
      (delta M Q r * ‖deriv R r‖ ^ 2 -
        ((radialK e ω r) ^ 2 / delta M Q r - L) * ‖R r‖ ^ 2) r := by
  obtain ⟨hd, hP⟩ := hR r hr
  have hc : HasDerivAt (fun s => (starRingEnd ℂ) (R s)) ((starRingEnd ℂ) (deriv R r)) r :=
    hd.hasDerivAt.star
  have hG := hP.fun_mul hc
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r hG
  have hfun : (fun s => ((delta M Q s : ℂ) * deriv R s * (starRingEnd ℂ) (R s)).re) =
      Complex.reCLM ∘ fun s => (delta M Q s : ℂ) * deriv R s * (starRingEnd ℂ) (R s) := by
    funext s
    simp
  rw [hfun]
  refine hRe.congr_deriv ?_
  rw [Complex.reCLM_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.sq_norm,
    Complex.normSq_apply]
  ring

/-- The coefficient `q = K²/Δ − L` at `ω = 0` is bounded where `r²/4 ≤ Δ`. -/
theorem zi_q_bound {e L D r : ℝ} (hD : 0 < D) (hDr : r ^ 2 / 4 ≤ D) :
    |(radialK e 0 r) ^ 2 / D - L| ≤ 4 * e ^ 2 + |L| := by
  have hK2 : 0 ≤ (radialK e 0 r) ^ 2 / D := by positivity
  have hK4 : (radialK e 0 r) ^ 2 / D ≤ 4 * e ^ 2 := by
    rw [div_le_iff₀ hD]
    have h : (radialK e 0 r) ^ 2 = e ^ 2 * r ^ 2 := by
      unfold radialK
      ring
    rw [h]
    linear_combination 4 * mul_le_mul_of_nonneg_left hDr (sq_nonneg e)
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith [le_abs_self L]
  · linarith [neg_abs_le L]

/-- Bound of the coefficients on `[ρ, 2ρ]` for the weight `x = (r − ρ)(2ρ − r)`,
`y = x' = 3ρ − 2r`. -/
theorem zi_coef_bound {ρ r D q Q0 : ℝ} (hρ : 0 < ρ) (hr1 : ρ ≤ r) (hr2 : r ≤ 2 * ρ) (hD : 0 < D)
    (hD4 : D ≤ 4 * ρ ^ 2) (hq : |q| ≤ Q0) :
    2 * ρ * (3 * ρ - 2 * r) ^ 2 * D + ρ * ((r - ρ) * (2 * ρ - r)) ^ 2 * |q| +
        ((r - ρ) * (2 * ρ - r)) ^ 2 * D / (2 * ρ) ≤ (9 + Q0) * ρ ^ 5 := by
  set x := (r - ρ) * (2 * ρ - r) with hx
  set y := 3 * ρ - 2 * r with hy
  have hQ0 : 0 ≤ Q0 := (abs_nonneg q).trans hq
  have hx0 : 0 ≤ x := mul_nonneg (by linarith) (by linarith)
  have hx4 : x ^ 2 ≤ ρ ^ 4 / 16 := by
    have h1 : x ≤ ρ ^ 2 / 4 := by
      have h := sq_nonneg (r - 3 * ρ / 2)
      linear_combination h
    have h2 := pow_le_pow_left₀ hx0 h1 2
    linear_combination h2
  have hy2 : y ^ 2 ≤ ρ ^ 2 := by
    have h := mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hr2)
    linear_combination 4 * h
  have t1 : 2 * ρ * y ^ 2 * D ≤ 8 * ρ ^ 5 := by
    have h := mul_le_mul hy2 hD4 hD.le (sq_nonneg ρ)
    have h' := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * ρ)
    linear_combination h'
  have t2 : ρ * x ^ 2 * |q| ≤ ρ ^ 5 * Q0 := by
    have h := mul_le_mul hx4 hq (abs_nonneg q) (by positivity)
    have h' := mul_le_mul_of_nonneg_left h hρ.le
    have h0 : 0 ≤ ρ ^ 5 * Q0 := by positivity
    linear_combination h' + (15 / 16 : ℝ) * h0
  have t3 : x ^ 2 * D / (2 * ρ) ≤ ρ ^ 5 := by
    rw [div_le_iff₀ (by linarith)]
    have h := mul_le_mul hx4 hD4 hD.le (by positivity)
    have h0 : 0 ≤ ρ ^ 6 := by positivity
    linear_combination h + (7 / 4 : ℝ) * h0
  linear_combination t1 + t2 + t3

/-- The interval estimate behind the limit-point argument: for `ρ ≥ 2a`, the constant flux `F`
of an `L²` solution at `ω = 0` satisfies `|F| ≤ 30(9 + 4e² + |L|) ∫_ρ^{2ρ} ‖R‖²`. -/
theorem zi_flux_bound {M Q e L : ℝ} (hM : 0 < M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e 0 r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hL2 : IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi (outerHorizon M Q)))
    {C : ℝ} (hC : ∀ r ∈ Ioi (outerHorizon M Q),
      delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im = C)
    {ρ : ℝ} (hρ : 2 * outerHorizon M Q ≤ ρ) :
    |C| ≤ 30 * (9 + 4 * e ^ 2 + |L|) * ∫ r in ρ..2 * ρ, ‖R r‖ ^ 2 := by
  have ha := zi_outerHorizon_pos (Q := Q) hM
  have hρ0 : 0 < ρ := by linarith
  have haρ : outerHorizon M Q < ρ := by linarith
  set K0 : ℝ := 9 + 4 * e ^ 2 + |L| with hK0
  obtain ⟨T, hT⟩ : ∃ T : ℝ → ℝ, T = fun s =>
      |C| * (ρ ^ 2 * (s - ρ) ^ 3 / 3 - ρ * (s - ρ) ^ 4 / 2 + (s - ρ) ^ 5 / 5) -
        ρ * (((s - ρ) * (2 * ρ - s)) ^ 2 *
          ((delta M Q s : ℂ) * deriv R s * (starRingEnd ℂ) (R s)).re) := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T' : ℝ → ℝ, T' = fun s =>
      |C| * ((s - ρ) * (2 * ρ - s)) ^ 2 -
        ρ * (2 * ((s - ρ) * (2 * ρ - s)) * (3 * ρ - 2 * s) *
            ((delta M Q s : ℂ) * deriv R s * (starRingEnd ℂ) (R s)).re +
          ((s - ρ) * (2 * ρ - s)) ^ 2 * (delta M Q s * ‖deriv R s‖ ^ 2 -
            ((radialK e 0 s) ^ 2 / delta M Q s - L) * ‖R s‖ ^ 2)) := ⟨_, rfl⟩
  have hTd : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt T (T' r) r := by
    intro r hr
    rw [hT]
    have h := ((zi_hasDerivAt_primitive ρ r).const_mul |C|).sub
      (((zi_hasDerivAt_weight ρ r).fun_mul (zi_hasDerivAt_re hR hr)).const_mul ρ)
    refine h.congr_deriv ?_
    rw [hT']
  have hbound : ∀ r ∈ Icc ρ (2 * ρ), T' r ≤ K0 * ρ ^ 5 * ‖R r‖ ^ 2 := by
    intro r hr
    have hr2a : 2 * outerHorizon M Q ≤ r := le_trans hρ hr.1
    have hra : outerHorizon M Q < r := by linarith [hr.1]
    obtain ⟨hΔl, hΔu⟩ := zi_delta_bounds (Q := Q) hM hr2a
    have hΔ0 : 0 < delta M Q r := fl_delta_pos hra
    set x := (r - ρ) * (2 * ρ - r) with hx
    set y := 3 * ρ - 2 * r with hy
    set D := delta M Q r with hD
    set q := (radialK e 0 r) ^ 2 / delta M Q r - L with hq
    set u := ‖R r‖ ^ 2 with hu
    set G : ℂ := (D : ℂ) * deriv R r * (starRingEnd ℂ) (R r) with hG
    have hGim : G.im = C := by
      rw [← hC r hra, hG, mul_assoc, Complex.im_ofReal_mul]
    have hGn : G.re ^ 2 + C ^ 2 = D * (D * ‖deriv R r‖ ^ 2) * u := by
      rw [← hGim]
      have h1 : G.re ^ 2 + G.im ^ 2 = ‖G‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      rw [h1, hG, norm_mul, norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs,
        abs_of_pos hΔ0, hu]
      ring
    have hcore := zi_core (C := C) (g := G.re) (x := x) (y := y) (q := q)
      (by positivity : 0 ≤ D * ‖deriv R r‖ ^ 2) (by positivity : 0 ≤ u) hΔ0.le hρ0 hGn
    have hD4 : D ≤ 4 * ρ ^ 2 := by
      have h := mul_le_mul hr.2 hr.2 (by linarith [hr.1]) (by linarith)
      linear_combination hΔu + h
    have hcoef : 2 * ρ * y ^ 2 * D + ρ * x ^ 2 * |q| + x ^ 2 * D / (2 * ρ) ≤ K0 * ρ ^ 5 := by
      have h := zi_coef_bound hρ0 hr.1 hr.2 hΔ0 hD4 (zi_q_bound (e := e) (L := L) hΔ0 hΔl)
      rw [hK0]
      linear_combination h
    calc T' r = |C| * x ^ 2 -
          ρ * (2 * x * y * G.re + x ^ 2 * (D * ‖deriv R r‖ ^ 2 - q * u)) := by
          rw [hT']
      _ ≤ _ := hcore
      _ ≤ K0 * ρ ^ 5 * u := mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hmem : ∀ r ∈ Icc ρ (2 * ρ), r ∈ Ioi (outerHorizon M Q) :=
    fun r hr => lt_of_lt_of_le haρ hr.1
  have hint := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (g := T) (g' := T')
    (φ := fun r => K0 * ρ ^ 5 * ‖R r‖ ^ 2) (by linarith : ρ ≤ 2 * ρ)
    (fun r hr => (hTd r (hmem r hr)).continuousAt.continuousWithinAt)
    (fun r hr => (hTd r (hmem r (Ioo_subset_Icc_self hr))).hasDerivWithinAt)
    ((hL2.mono_set hmem).const_mul _)
    (fun r hr => hbound r (Ioo_subset_Icc_self hr))
  have hTv : T (2 * ρ) - T ρ = |C| * ρ ^ 5 / 30 := by
    rw [hT]
    ring
  rw [hTv, intervalIntegral.integral_const_mul] at hint
  have h5 : 0 < ρ ^ 5 := by positivity
  have h' : |C| * ρ ^ 5 ≤ (30 * K0 * ∫ r in ρ..2 * ρ, ‖R r‖ ^ 2) * ρ ^ 5 := by
    linear_combination 30 * hint
  exact le_of_mul_le_mul_right h' h5

/-- **Zero frequency, `L²` solutions have zero flux.** At `ω = 0` (`K = −er`), a solution of
`(ΔR')' + (e²r²/Δ − L)R = 0` on `(a, ∞)` with `∫_a^∞ ‖R‖² < ∞` has `Δ Im(R' R̄) ≡ 0`.

This replaces the Frobenius analysis at infinity in the proof of Proposition 7.1 (p. 9) by a
limit-point argument: the coefficient `e²r²/Δ − L` is bounded at infinity, and a nonzero constant
flux `F` would give `|F| ≤ C ∫_ρ^{2ρ} ‖R‖²` for all large `ρ` (`zi_flux_bound`), whose right side
tends to `0`. No hypothesis on `Q` and no sign of `L` is needed. -/
theorem zero_frequency_flux_eq_zero_of_integrable {M Q e L : ℝ} (hM : 0 < M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e 0 r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hL2 : IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi (outerHorizon M Q))) :
    ∀ r ∈ Ioi (outerHorizon M Q), delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im = 0 := by
  obtain ⟨C, hC⟩ := flux_const_L hR
  suffices hC0 : C = 0 by
    intro r hr
    rw [hC r hr, hC0]
  set a := outerHorizon M Q with ha_def
  have ha := zi_outerHorizon_pos (Q := Q) hM
  have hI : ∀ x, a ≤ x → IntervalIntegrable (fun r => ‖R r‖ ^ 2) volume a x := fun x hx =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2 (hL2.mono_set Ioc_subset_Ioi_self)
  have h1 := intervalIntegral_tendsto_integral_Ioi (b := fun ρ : ℝ => 2 * ρ) a hL2
    (tendsto_id.const_mul_atTop two_pos)
  have h2 := intervalIntegral_tendsto_integral_Ioi (b := fun ρ : ℝ => ρ) a hL2 tendsto_id
  have htail : Tendsto (fun ρ => ∫ r in ρ..2 * ρ, ‖R r‖ ^ 2) atTop (𝓝 0) := by
    have h := h1.sub h2
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop a] with ρ hρ
    exact intervalIntegral.integral_interval_sub_left (hI _ (by linarith)) (hI _ hρ)
  have hlim := htail.const_mul (30 * (9 + 4 * e ^ 2 + |L|))
  rw [mul_zero] at hlim
  have hle : |C| ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (2 * a)] with ρ hρ
    exact zi_flux_bound hM hR hL2 hC hρ
  exact abs_nonpos_iff.1 hle

/-- **Zero frequency, charged case** (Proposition 7.1, p. 9, `e ≠ 0`). At `ω = 0`, an `L²`
solution with the Θ-form ingoing horizon condition (1.4) with leading coefficient `B` has
`B = 0`: the flux is `≡ 0` (`zero_frequency_flux_eq_zero_of_integrable`) and tends to
`−K(a)‖B‖² = e a ‖B‖²` at the horizon (`tendsto_flux_horizon_L`), with `a > 0`. -/
theorem zero_frequency_charged {M Q e L : ℝ} (hM : 0 < M) (he : e ≠ 0)
    {Θ : ℝ → ℝ} (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e 0 r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e 0 r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    {B : ℂ}
    (hH1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - B)
      =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q))
    (hH2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r)
      =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))
    (hL2 : IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi (outerHorizon M Q))) :
    B = 0 := by
  have hF := zero_frequency_flux_eq_zero_of_integrable hM hR hL2
  have hlim := tendsto_flux_horizon_L hΘ hR hH1 hH2
  have h0 : Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im)
      (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hF r hr).symm
  have heq := tendsto_nhds_unique hlim h0
  have ha := zi_outerHorizon_pos (Q := Q) hM
  have hK : -radialK e 0 (outerHorizon M Q) = e * outerHorizon M Q := by
    unfold radialK
    ring
  rw [hK] at heq
  have hB : ‖B‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 heq with h | h
    · exact absurd h (mul_ne_zero he ha.ne')
    · exact h
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hB)

end ModeStability.AllAngular

end
