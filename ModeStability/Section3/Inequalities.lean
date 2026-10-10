module

public import Mathlib
public import ModeStability.Section3.Numerators
public import ModeStability.Section3.Expansion

/-!
# Section 3: the inequalities `k_x > 0` and `𝓔 > 0`

Let `G(x) = ω (δ/x)² f(δ/x)` with `f = sec3f ν χ` (the representation (3.2) of `k` for `x > 0`).
For `ν > 0`, `χ ≥ 0`, `ω > 0`, `δ > 0` we show, for `x > 0`, with `t = δ/x`:

* `G` is `C²` on `x > 0`, with `G' = −(ω/δ) F'(t) t²` and `G'' = (ω/δ²)(F''(t) t² + 2 t F'(t)) t²`
  where `F = t² f`;
* `G' > 0`, since `F'(t) < 0` by the sign form (3.5) of `(t² f)'`;
* `2 G'² − G G'' = ω² t⁶ 𝓔 / δ² > 0`, since `𝓔 > 0` by the expansion (3.4) and the positivity of
  the
  numerators (3.5).

(the spherical research notes in preparation, Section 3.)
-/

@[expose] public section

namespace ModeStability.Section3

open Set Filter Topology

/-- `F'(t) = (t² f)' = 2 t f + t² f'`. -/
noncomputable def sec3F1 (ν χ t : ℝ) : ℝ := 2 * t * sec3f ν χ t + t ^ 2 * sec3f1 ν t

/-- `F''(t) = 2 f + 4 t f' + t² f''`. -/
noncomputable def sec3F2 (ν χ t : ℝ) : ℝ :=
  2 * sec3f ν χ t + 4 * t * sec3f1 ν t + t ^ 2 * sec3f2 ν t

/-- `G(x) = ω (δ/x)² f(δ/x)`. -/
noncomputable def sec3G (ω δ ν χ x : ℝ) : ℝ := ω * ((δ / x) ^ 2 * sec3f ν χ (δ / x))

/-- `G'(x) = −(ω/δ) F'(t) t²` with `t = δ/x`. -/
noncomputable def sec3G1 (ω δ ν χ x : ℝ) : ℝ :=
  -(ω / δ) * (sec3F1 ν χ (δ / x) * (δ / x) ^ 2)

/-- `G''(x) = (ω/δ²)(F''(t) t² + 2 t F'(t)) t²` with `t = δ/x`. -/
noncomputable def sec3G2 (ω δ ν χ x : ℝ) : ℝ :=
  ω / δ ^ 2 * ((sec3F2 ν χ (δ / x) * (δ / x) ^ 2 + 2 * (δ / x) * sec3F1 ν χ (δ / x)) *
    (δ / x) ^ 2)

/-! ### Derivatives -/

theorem hasDerivAt_div_scale {δ x : ℝ} (hδ : δ ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => δ / y) (-((δ / x) ^ 2 / δ)) x := by
  have h := (hasDerivAt_inv hx).const_mul δ
  convert h using 1
  · ext y
    simp [div_eq_mul_inv]
  · field_simp

theorem hasDerivAt_sec3G {ω δ ν χ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) :
    HasDerivAt (sec3G ω δ ν χ) (sec3G1 ω δ ν χ x) x := by
  have ht : 0 < δ / x := div_pos hδ hx
  have h1 := (hasDerivAt_sq_mul_sec3f ν χ ht).comp x (hasDerivAt_div_scale hδ.ne' hx.ne')
  refine (h1.const_mul ω).congr_deriv ?_
  unfold sec3G1 sec3F1
  field_simp

theorem hasDerivAt_sec3G1 {ω δ ν χ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) :
    HasDerivAt (sec3G1 ω δ ν χ) (sec3G2 ω δ ν χ x) x := by
  have ht : 0 < δ / x := div_pos hδ hx
  have h2 := hasDerivAt_sq_mul_sec3f_deriv ν χ ht
  have h3 := h2.mul (hasDerivAt_pow 2 (δ / x))
  have h4 := h3.comp x (hasDerivAt_div_scale hδ.ne' hx.ne')
  refine (h4.const_mul (-(ω / δ))).congr_deriv ?_
  unfold sec3G2 sec3F1 sec3F2
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp

/-! ### Smoothness -/

theorem contDiffOn_sec3G (ω δ ν χ : ℝ) (hδ : 0 < δ) :
    ContDiffOn ℝ 2 (sec3G ω δ ν χ) (Ioi 0) := by
  have hT : ContDiffOn ℝ 2 (fun x : ℝ => δ / x) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun x hx => ne_of_gt hx)
  have hE : ContDiffOn ℝ 2 (fun x : ℝ => Real.exp (2 * (δ / x))) (Ioi 0) :=
    Real.contDiff_exp.comp_contDiffOn (contDiffOn_const.mul hT)
  have hE1 : ContDiffOn ℝ 2 (fun x : ℝ => Real.exp (2 * (δ / x)) - 1) (Ioi 0) :=
    hE.sub contDiffOn_const
  have hne : ∀ x ∈ Ioi (0 : ℝ), Real.exp (2 * (δ / x)) - 1 ≠ 0 :=
    fun x hx => exp_two_mul_sub_one_ne_zero (div_pos hδ hx)
  have hq1 : ContDiffOn ℝ 2
      (fun x : ℝ => 4 * Real.exp (2 * (δ / x)) / (Real.exp (2 * (δ / x)) - 1) ^ 2) (Ioi 0) :=
    (contDiffOn_const.mul hE).div (hE1.pow 2) (fun x hx => pow_ne_zero 2 (hne x hx))
  have hq2 : ContDiffOn ℝ 2
      (fun x : ℝ => ν * (2 * Real.exp (2 * (δ / x)) / (Real.exp (2 * (δ / x)) - 1))) (Ioi 0) :=
    contDiffOn_const.mul ((contDiffOn_const.mul hE).div hE1 hne)
  have hf : ContDiffOn ℝ 2 (fun x : ℝ => sec3f ν χ (δ / x)) (Ioi 0) :=
    (hq1.sub hq2).sub contDiffOn_const
  exact contDiffOn_const.mul ((hT.pow 2).mul hf)

/-! ### Signs -/

theorem sec3F1_neg {ν χ t : ℝ} (hν : 0 < ν) (hχ : 0 ≤ χ) (ht : 0 < t) : sec3F1 ν χ t < 0 := by
  have hu := one_lt_exp_two_mul ht
  have h1 := exp_two_mul_sub_one_lt ht
  have h2 := exp_two_mul_sub_one_sub_pos ht
  have hu1 : 0 < Real.exp (2 * t) - 1 := sub_pos.2 hu
  have hA : 8 * t * Real.exp (2 * t) * ((Real.exp (2 * t) - 1) - t * (Real.exp (2 * t) + 1)) /
      (Real.exp (2 * t) - 1) ^ 3 < 0 := by
    refine div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (by linarith)) ?_
    positivity
  have hB : 0 < ν * (4 * t * Real.exp (2 * t) * ((Real.exp (2 * t) - 1) - t) /
      (Real.exp (2 * t) - 1) ^ 2) := by positivity
  have hC : 0 ≤ 2 * χ * t := by positivity
  unfold sec3F1
  rw [two_mul_sec3f_add_eq ν χ ht]
  linarith

theorem sec3E_pos {ν χ t : ℝ} (hν : 0 < ν) (hχ : 0 ≤ χ) (ht : 0 < t) : 0 < sec3E ν χ t := by
  have hu := one_lt_exp_two_mul ht
  have hu1 : 0 < Real.exp (2 * t) - 1 := sub_pos.2 hu
  have hA : 0 < Real.exp (2 * t) - 1 - 2 * t - 2 * t ^ 2 := numA_pos ht
  have hB : 0 < (Real.exp (2 * t) - 1) ^ 2 - t * (Real.exp (2 * t) - 1) -
      t ^ 2 * (Real.exp (2 * t) + 1) := numB_pos ht
  have hC : 0 < (t ^ 2 + t - 1) * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1 := numC_pos ht
  have hD : 0 < (t ^ 2 + t - 1) * Real.exp (2 * t) ^ 2 +
      (4 * t ^ 2 + 2) * Real.exp (2 * t) + t ^ 2 - t - 1 := numD_pos ht
  have hH : 0 < (2 * t ^ 2 - 2 * t + 1) * Real.exp (2 * t) ^ 2 -
      2 * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1 := numH_pos ht
  rw [sec3E_eq ν χ ht]
  have t1 : 0 ≤ 8 * Real.exp (2 * t) ^ 2 * (Real.exp (2 * t) - 1 - 2 * t - 2 * t ^ 2) /
      (Real.exp (2 * t) - 1) ^ 3 * ν ^ 2 := by positivity
  have t2 : 0 ≤ 8 * Real.exp (2 * t) * ((Real.exp (2 * t) - 1) ^ 2 - t * (Real.exp (2 * t) - 1) -
      t ^ 2 * (Real.exp (2 * t) + 1)) / (Real.exp (2 * t) - 1) ^ 3 * (ν * χ) := by positivity
  have t3 : 0 ≤ 32 * Real.exp (2 * t) ^ 2 *
      ((t ^ 2 + t - 1) * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1) /
        (Real.exp (2 * t) - 1) ^ 4 * ν := by positivity
  have t4 : 0 ≤ 2 * χ ^ 2 := by positivity
  have t5 : 0 ≤ 16 * Real.exp (2 * t) * ((t ^ 2 + t - 1) * Real.exp (2 * t) ^ 2 +
      (4 * t ^ 2 + 2) * Real.exp (2 * t) + t ^ 2 - t - 1) / (Real.exp (2 * t) - 1) ^ 4 * χ := by
    positivity
  have t6 : 0 < 32 * Real.exp (2 * t) ^ 2 * ((2 * t ^ 2 - 2 * t + 1) * Real.exp (2 * t) ^ 2 -
      2 * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1) / (Real.exp (2 * t) - 1) ^ 6 := by
    positivity
  linarith

theorem sec3G1_pos {ω δ ν χ x : ℝ} (hω : 0 < ω) (hδ : 0 < δ) (hν : 0 < ν) (hχ : 0 ≤ χ)
    (hx : 0 < x) : 0 < sec3G1 ω δ ν χ x := by
  have ht : 0 < δ / x := div_pos hδ hx
  have hF := sec3F1_neg hν hχ ht
  unfold sec3G1
  have : 0 < -(sec3F1 ν χ (δ / x)) := neg_pos.2 hF
  have h2 : 0 < ω / δ * (-(sec3F1 ν χ (δ / x)) * (δ / x) ^ 2) := by positivity
  linarith

theorem sec3G_two_mul_sq_sub_pos {ω δ ν χ x : ℝ} (hω : 0 < ω) (hδ : 0 < δ) (hν : 0 < ν)
    (hχ : 0 ≤ χ) (hx : 0 < x) :
    0 < 2 * sec3G1 ω δ ν χ x ^ 2 - sec3G ω δ ν χ x * sec3G2 ω δ ν χ x := by
  have ht : 0 < δ / x := div_pos hδ hx
  have hE := sec3E_pos hν hχ ht
  have hid := sec3_chain_identity (sec3f ν χ (δ / x)) (sec3f1 ν (δ / x)) (sec3f2 ν (δ / x))
    (δ / x)
  have key : 2 * sec3G1 ω δ ν χ x ^ 2 - sec3G ω δ ν χ x * sec3G2 ω δ ν χ x =
      ω ^ 2 / δ ^ 2 * (δ / x) ^ 3 * ((δ / x) ^ 3 * sec3E ν χ (δ / x)) := by
    rw [← sec3E] at hid
    rw [← hid]
    unfold sec3G1 sec3G sec3G2 sec3F1 sec3F2
    field_simp
    ring
  rw [key]
  positivity

/-- On `x > 0`, a function agreeing with `G` has first and second derivatives `G'`, `G''`. -/
theorem deriv_eq_of_eqOn {k : ℝ → ℝ} {ω δ ν χ x : ℝ} (hδ : 0 < δ)
    (hk : EqOn k (sec3G ω δ ν χ) (Ioi 0)) (hx : 0 < x) :
    deriv k x = sec3G1 ω δ ν χ x ∧ deriv (deriv k) x = sec3G2 ω δ ν χ x := by
  have hnhds : ∀ y : ℝ, 0 < y → k =ᶠ[𝓝 y] sec3G ω δ ν χ := fun y hy =>
    hk.eventuallyEq_of_mem (Ioi_mem_nhds hy)
  have h1 : ∀ y : ℝ, 0 < y → deriv k y = sec3G1 ω δ ν χ y := fun y hy => by
    rw [(hnhds y hy).deriv_eq]
    exact (hasDerivAt_sec3G hδ hy).deriv
  refine ⟨h1 x hx, ?_⟩
  have h2 : deriv k =ᶠ[𝓝 x] sec3G1 ω δ ν χ :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => h1 y hy
  rw [h2.deriv_eq]
  exact (hasDerivAt_sec3G1 hδ hx).deriv

/-- The coefficient inequalities of Lemma 2.1, (2.4), for any `k` with `k = G` on `x > 0`. -/
theorem coefficient_inequalities_of_eqOn {k : ℝ → ℝ} {ω δ ν χ : ℝ} (hω : 0 < ω) (hδ : 0 < δ)
    (hν : 0 < ν) (hχ : 0 ≤ χ) (hk : EqOn k (sec3G ω δ ν χ) (Ioi 0)) :
    ContDiffOn ℝ 2 k (Ioi 0) ∧
      ∀ x ∈ Ioi (0 : ℝ), 0 < deriv k x ∧ 0 < 2 * deriv k x ^ 2 - k x * deriv (deriv k) x := by
  refine ⟨(contDiffOn_sec3G ω δ ν χ hδ).congr hk, fun x hx => ?_⟩
  have hx' : 0 < x := hx
  obtain ⟨h1, h2⟩ := deriv_eq_of_eqOn hδ hk hx'
  rw [h1, h2, hk hx]
  exact ⟨sec3G1_pos hω hδ hν hχ hx', sec3G_two_mul_sq_sub_pos hω hδ hν hχ hx'⟩

end ModeStability.Section3

end
