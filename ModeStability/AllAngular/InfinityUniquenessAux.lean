module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK

/-!
# Uniqueness at infinity: auxiliary estimates

Auxiliary material for `ModeStability.AllAngular.InfinityUniqueness`, which proves the assertion
of the all-angular research notes in preparation, p. 1, that a nonzero solution of the radial
equation satisfying the outgoing condition at infinity has a nonzero leading coefficient there.

* `norm_le_of_tendsto_zero_of_norm_deriv_le`: if `c → 0` at `+∞` and `‖c'(t)‖ ≤ D/t²` on
  `[s, ∞)`, then `‖c(s)‖ ≤ D/s` (mean value inequality on `[s, t]`, then `t → ∞`).
* `eq_zero_of_norm_deriv_le`: the backward Grönwall argument from infinity for a pair of
  amplitudes with `‖a'ᵢ‖ ≤ C t⁻² (‖a₁‖ + ‖a₂‖)` that tend to `0`.
* Elementary facts about `Δ = (r − a)(r − b) = r² − 2Mr + Q²` for `|Q| ≤ M` (including the
  extremal case `a = b`).
* The coefficient functions of the equation for `u = rR`, namely `Θ' = K/Δ` (`phaseRate`), its
  derivative (`phaseAccel`), the damping `α = (2Mr − 2Q²)/(rΔ)` (`dampCoeff`) and the potential
  `γ = (−2Mr + 2Q² − Lr²)/(r²Δ)` (`potCoeff`), with `u'' + αu' + (Θ'² + γ)u = 0`, and their
  limits: `Θ' → ω`, `r²Θ'' → e − 2Mω`, `r²α → 2M`, `r²γ → −L`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular.InfinityUniqueness

/-! ### The tail estimate and the backward Grönwall argument -/

/-- If `c → 0` at `+∞` and `‖c'(t)‖ ≤ D/t²` on `[s, ∞)` with `s > 0`, then `‖c(s)‖ ≤ D/s`. -/
theorem norm_le_of_tendsto_zero_of_norm_deriv_le {c c' : ℝ → ℂ} {s D : ℝ} (hs : 0 < s)
    (hc : ∀ t, s ≤ t → HasDerivAt c (c' t) t) (hb : ∀ t, s ≤ t → ‖c' t‖ ≤ D / t ^ 2)
    (hlim : Tendsto c atTop (𝓝 0)) : ‖c s‖ ≤ D / s := by
  have hD : 0 ≤ D := by
    have h := (norm_nonneg _).trans (hb s le_rfl)
    have hs2 : 0 < s ^ 2 := by positivity
    by_contra hneg
    have : D / s ^ 2 < 0 := div_neg_of_neg_of_pos (not_le.1 hneg) hs2
    linarith
  have key : ∀ t, s ≤ t → ‖c t - c s‖ ≤ D / s - D / t := by
    intro t hst
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := fun x => c x - c s)
      (f' := c') (B := fun x => D / s - D / x) (B' := fun x => D / x ^ 2) ?_ ?_ ?_ ?_ ?_ ?_
      (right_mem_Icc.2 hst)
    · intro x hx
      exact ((hc x hx.1).continuousAt.sub continuousAt_const).continuousWithinAt
    · intro x hx
      exact ((hc x hx.1).sub_const (c s)).hasDerivWithinAt
    · simp
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
      exact (continuousAt_const.sub
        (continuousAt_const.div continuousAt_id hx0.ne')).continuousWithinAt
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hs hx.1
      have h := ((hasDerivAt_inv hx0.ne').const_mul D).const_sub (D / s)
      refine HasDerivAt.hasDerivWithinAt ?_
      convert h using 1
      · funext y
        simp [div_eq_mul_inv]
      · ring
    · intro x hx
      exact hb x hx.1
  have hT : Tendsto (fun t => ‖c t - c s‖) atTop (𝓝 ‖0 - c s‖) := (hlim.sub_const (c s)).norm
  rw [zero_sub, norm_neg] at hT
  refine le_of_tendsto hT (eventually_atTop.2 ⟨s, fun t hst => ?_⟩)
  have : 0 ≤ D / t := div_nonneg hD (hs.le.trans hst)
  linarith [key t hst]

/-- The backward Grönwall argument from infinity: two amplitudes on `[s₀, ∞)` with
`‖a'ᵢ(t)‖ ≤ C t⁻² (‖a₁(t)‖ + ‖a₂(t)‖)`, `4C ≤ s₀`, `‖a₁‖ + ‖a₂‖ ≤ 1` and `aᵢ → 0` vanish
at `s₀`. -/
theorem eq_zero_of_norm_deriv_le {a₁ a₂ a₁' a₂' : ℝ → ℂ} {s₀ C : ℝ} (hs₀ : 0 < s₀) (hC : 0 ≤ C)
    (hCs : 4 * C ≤ s₀)
    (h₁ : ∀ t, s₀ ≤ t → HasDerivAt a₁ (a₁' t) t) (h₂ : ∀ t, s₀ ≤ t → HasDerivAt a₂ (a₂' t) t)
    (hb₁ : ∀ t, s₀ ≤ t → ‖a₁' t‖ ≤ C / t ^ 2 * (‖a₁ t‖ + ‖a₂ t‖))
    (hb₂ : ∀ t, s₀ ≤ t → ‖a₂' t‖ ≤ C / t ^ 2 * (‖a₁ t‖ + ‖a₂ t‖))
    (hl₁ : Tendsto a₁ atTop (𝓝 0)) (hl₂ : Tendsto a₂ atTop (𝓝 0))
    (hbd : ∀ t, s₀ ≤ t → ‖a₁ t‖ + ‖a₂ t‖ ≤ 1) :
    a₁ s₀ = 0 ∧ a₂ s₀ = 0 := by
  have half : ∀ B : ℝ, (∀ t, s₀ ≤ t → ‖a₁ t‖ + ‖a₂ t‖ ≤ B) →
      ∀ t, s₀ ≤ t → ‖a₁ t‖ + ‖a₂ t‖ ≤ B / 2 := by
    intro B hB t ht
    have hB0 : 0 ≤ B := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hB s₀ le_rfl)
    have ht0 : 0 < t := hs₀.trans_le ht
    have bound : ∀ (c c' : ℝ → ℂ), (∀ x, s₀ ≤ x → HasDerivAt c (c' x) x) →
        (∀ x, s₀ ≤ x → ‖c' x‖ ≤ C / x ^ 2 * (‖a₁ x‖ + ‖a₂ x‖)) → Tendsto c atTop (𝓝 0) →
        ‖c t‖ ≤ C * B / s₀ := by
      intro c c' hc hb hl
      have hb' : ∀ x, t ≤ x → ‖c' x‖ ≤ C * B / x ^ 2 := by
        intro x hx
        have hx0 : 0 < x := ht0.trans_le hx
        calc ‖c' x‖ ≤ C / x ^ 2 * (‖a₁ x‖ + ‖a₂ x‖) := hb x (ht.trans hx)
          _ ≤ C / x ^ 2 * B := mul_le_mul_of_nonneg_left (hB x (ht.trans hx)) (by positivity)
          _ = C * B / x ^ 2 := by ring
      calc ‖c t‖ ≤ C * B / t :=
            norm_le_of_tendsto_zero_of_norm_deriv_le ht0 (fun x hx => hc x (ht.trans hx)) hb' hl
        _ ≤ C * B / s₀ := div_le_div_of_nonneg_left (mul_nonneg hC hB0) hs₀ ht
    have e1 := bound a₁ a₁' h₁ hb₁ hl₁
    have e2 := bound a₂ a₂' h₂ hb₂ hl₂
    have : C * B / s₀ ≤ B / 4 := by
      rw [div_le_div_iff₀ hs₀ (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_left hCs hB0]
    linarith
  have hpow : ∀ n : ℕ, ∀ t, s₀ ≤ t → ‖a₁ t‖ + ‖a₂ t‖ ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simpa using hbd
    | succ n ih =>
      intro t ht
      have := half _ ih t ht
      rw [pow_succ]
      linarith
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h0 : ‖a₁ s₀‖ + ‖a₂ s₀‖ ≤ 0 := ge_of_tendsto' hlim (fun n => hpow n s₀ le_rfl)
  constructor
  · exact norm_le_zero_iff.1 (by linarith [norm_nonneg (a₂ s₀)])
  · exact norm_le_zero_iff.1 (by linarith [norm_nonneg (a₁ s₀)])

/-! ### Elementary facts about `Δ` for `|Q| ≤ M` -/

/-- `(√(M² − Q²))² = M² − Q²` for `|Q| ≤ M`. -/
theorem sqrt_sq_sub_sq {M Q : ℝ} (hQ : |Q| ≤ M) :
    Real.sqrt (M ^ 2 - Q ^ 2) ^ 2 = M ^ 2 - Q ^ 2 := by
  have h := sq_le_sq' (abs_le.1 hQ).1 (abs_le.1 hQ).2
  exact Real.sq_sqrt (by linarith)

/-- `Δ(r) = r² − 2Mr + Q²` for `|Q| ≤ M`. -/
theorem delta_eq {M Q : ℝ} (hQ : |Q| ≤ M) (r : ℝ) :
    delta M Q r = r ^ 2 - 2 * M * r + Q ^ 2 := by
  have hs := sqrt_sq_sub_sq hQ
  unfold delta outerHorizon innerHorizon
  linear_combination (-1 : ℝ) * hs

/-- `a > 0` for `M > 0`. -/
theorem outerHorizon_pos {M Q : ℝ} (hM : 0 < M) : 0 < outerHorizon M Q := by
  unfold outerHorizon
  have := Real.sqrt_nonneg (M ^ 2 - Q ^ 2)
  linarith

/-- `Δ(r) > 0` for `r > a` (subextremal or extremal). -/
theorem delta_pos_of_lt {M Q r : ℝ} (hr : outerHorizon M Q < r) : 0 < delta M Q r := by
  have hab : innerHorizon M Q ≤ outerHorizon M Q := by
    unfold innerHorizon outerHorizon
    have := Real.sqrt_nonneg (M ^ 2 - Q ^ 2)
    linarith
  unfold delta
  have h1 : 0 < r - outerHorizon M Q := sub_pos.2 hr
  have h2 : 0 < r - innerHorizon M Q := by linarith
  positivity

/-- `Δ'(r) = 2r − 2M`. -/
theorem hasDerivAt_delta (M Q r : ℝ) : HasDerivAt (delta M Q) (2 * r - 2 * M) r := by
  have h := ((hasDerivAt_id r).sub_const (outerHorizon M Q)).mul
    ((hasDerivAt_id r).sub_const (innerHorizon M Q))
  have hfun : delta M Q = fun s => (id s - outerHorizon M Q) * (id s - innerHorizon M Q) := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  unfold outerHorizon innerHorizon
  simp only [id]
  ring

/-- `Δ` is continuous. -/
theorem continuous_delta (M Q : ℝ) : Continuous (delta M Q) := by
  unfold delta
  fun_prop

/-- `K'(r) = 2ωr − e`. -/
theorem hasDerivAt_radialK (e ω r : ℝ) : HasDerivAt (radialK e ω) (2 * ω * r - e) r := by
  have h := ((hasDerivAt_pow 2 r).const_mul ω).sub ((hasDerivAt_id r).const_mul e)
  have hfun : radialK e ω = fun s => ω * s ^ 2 - e * id s := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring

/-! ### The coefficients of the equation for `u = rR` -/

/-- The phase rate `Θ' = K/Δ`. -/
@[expose] noncomputable def phaseRate (M Q e ω r : ℝ) : ℝ := radialK e ω r / delta M Q r

/-- The derivative `Θ'' = (K'Δ − KΔ')/Δ²` of the phase rate. -/
@[expose] noncomputable def phaseAccel (M Q e ω r : ℝ) : ℝ :=
  ((2 * ω * r - e) * delta M Q r - radialK e ω r * (2 * r - 2 * M)) / delta M Q r ^ 2

/-- The damping coefficient `α = (2Mr − 2Q²)/(rΔ)` of `u'' + αu' + (Θ'² + γ)u = 0`. -/
@[expose] noncomputable def dampCoeff (M Q r : ℝ) : ℝ := (2 * M * r - 2 * Q ^ 2) / (r * delta M Q r)

/-- The potential coefficient `γ = (−2Mr + 2Q² − Lr²)/(r²Δ)` of `u'' + αu' + (Θ'² + γ)u = 0`. -/
@[expose] noncomputable def potCoeff (M Q L r : ℝ) : ℝ :=
  (-2 * M * r + 2 * Q ^ 2 - L * r ^ 2) / (r ^ 2 * delta M Q r)

/-- The coefficient `|α|/2 + (|γ| + |Θ''|)/(2|Θ'|)` bounding the derivatives of the amplitudes. -/
@[expose] noncomputable def errCoeff (M Q e ω L r : ℝ) : ℝ :=
  |dampCoeff M Q r| / 2 + (|potCoeff M Q L r| + |phaseAccel M Q e ω r|) /
    (2 * |phaseRate M Q e ω r|)

/-- `(Θ')' = Θ''` where `Δ ≠ 0`. -/
theorem hasDerivAt_phaseRate {M Q e ω r : ℝ} (hΔ : delta M Q r ≠ 0) :
    HasDerivAt (phaseRate M Q e ω) (phaseAccel M Q e ω r) r :=
  (hasDerivAt_radialK e ω r).div (hasDerivAt_delta M Q r) hΔ

/-! ### Limits at infinity -/

/-- `Δ(r)/r² = 1 − 2M r⁻¹ + Q² r⁻²` for `r ≠ 0`. -/
theorem delta_eq_sq_mul {M Q : ℝ} (hQ : |Q| ≤ M) {r : ℝ} (hr : r ≠ 0) :
    delta M Q r = r ^ 2 * (1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2) := by
  rw [delta_eq hQ]
  field_simp

theorem tendsto_deltaHat (M Q : ℝ) :
    Tendsto (fun r : ℝ => 1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2) atTop (𝓝 1) := by
  have hy : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hy.const_mul (2 * M))).add
    ((hy.pow 2).const_mul (Q ^ 2))
  simpa using h

/-- Eventually `r > 0`, `r > a` and the normalized `Δ̂ = Δ/r²` is nonzero. -/
theorem eventually_good {M Q : ℝ} (hQ : |Q| ≤ M) :
    ∀ᶠ r : ℝ in atTop, 0 < r ∧ 0 < delta M Q r ∧ (1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2) ≠ 0 := by
  filter_upwards [eventually_gt_atTop (max 0 (outerHorizon M Q))] with r hr
  have hr0 : 0 < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hΔ : 0 < delta M Q r := delta_pos_of_lt (lt_of_le_of_lt (le_max_right _ _) hr)
  refine ⟨hr0, hΔ, ?_⟩
  intro h0
  rw [delta_eq_sq_mul hQ hr0.ne', h0, mul_zero] at hΔ
  exact lt_irrefl _ hΔ

/-- `Θ' → ω` at infinity. -/
theorem tendsto_phaseRate {M Q : ℝ} (hQ : |Q| ≤ M) (e ω : ℝ) :
    Tendsto (phaseRate M Q e ω) atTop (𝓝 ω) := by
  have hy : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := ((tendsto_const_nhds (x := ω)).sub (hy.const_mul e)).div (tendsto_deltaHat M Q)
    one_ne_zero
  rw [mul_zero, sub_zero, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_good hQ] with r ⟨hr0, _, hD⟩
  simp only [Pi.div_apply]
  unfold phaseRate radialK
  rw [delta_eq_sq_mul hQ hr0.ne']
  field_simp

/-- `r²Θ'' → e − 2Mω` at infinity. -/
theorem tendsto_phaseAccel_mul_sq {M Q : ℝ} (hQ : |Q| ≤ M) (e ω : ℝ) :
    Tendsto (fun r => phaseAccel M Q e ω r * r ^ 2) atTop (𝓝 (e - 2 * M * ω)) := by
  have hy : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := (((tendsto_const_nhds (x := e - 2 * M * ω)).add (hy.const_mul (2 * ω * Q ^ 2))).sub
    ((hy.pow 2).const_mul (e * Q ^ 2))).div ((tendsto_deltaHat M Q).pow 2) (by norm_num)
  simp only [mul_zero, add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, one_pow, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_good hQ] with r ⟨hr0, _, hD⟩
  simp only [Pi.div_apply]
  unfold phaseAccel radialK
  rw [delta_eq_sq_mul hQ hr0.ne']
  field_simp
  ring

/-- `r²α → 2M` at infinity. -/
theorem tendsto_dampCoeff_mul_sq {M Q : ℝ} (hQ : |Q| ≤ M) :
    Tendsto (fun r => dampCoeff M Q r * r ^ 2) atTop (𝓝 (2 * M)) := by
  have hy : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := ((tendsto_const_nhds (x := 2 * M)).sub (hy.const_mul (2 * Q ^ 2))).div
    (tendsto_deltaHat M Q) one_ne_zero
  rw [mul_zero, sub_zero, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_good hQ] with r ⟨hr0, _, hD⟩
  simp only [Pi.div_apply]
  unfold dampCoeff
  rw [delta_eq_sq_mul hQ hr0.ne']
  field_simp

/-- `r²γ → −L` at infinity. -/
theorem tendsto_potCoeff_mul_sq {M Q : ℝ} (hQ : |Q| ≤ M) (L : ℝ) :
    Tendsto (fun r => potCoeff M Q L r * r ^ 2) atTop (𝓝 (-L)) := by
  have hy : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := (((hy.const_mul (-2 * M)).add ((hy.pow 2).const_mul (2 * Q ^ 2))).sub
    (tendsto_const_nhds (x := L))).div (tendsto_deltaHat M Q) one_ne_zero
  simp only [mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_sub, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_good hQ] with r ⟨hr0, _, hD⟩
  simp only [Pi.div_apply]
  unfold potCoeff
  rw [delta_eq_sq_mul hQ hr0.ne']
  field_simp

/-- The error coefficient is `O(r⁻²)`: there is `C ≥ 0` with eventually
`|α|/2 + (|γ| + |Θ''|)/(2|Θ'|) ≤ C/r²` (here `ω ≠ 0` is used). -/
theorem exists_errCoeff_le {M Q : ℝ} (hQ : |Q| ≤ M) (e L : ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ r in atTop, errCoeff M Q e ω L r ≤ C / r ^ 2 := by
  set ℓ : ℝ := |2 * M| / 2 + (|-L| + |e - 2 * M * ω|) / (2 * |ω|) with hℓ
  have hℓ0 : 0 ≤ ℓ := by positivity
  have hω2 : 2 * |ω| ≠ 0 := by positivity
  have h := ((tendsto_dampCoeff_mul_sq hQ).abs.div_const 2).add
    (((tendsto_potCoeff_mul_sq hQ L).abs.add (tendsto_phaseAccel_mul_sq hQ e ω).abs).div
      ((tendsto_phaseRate hQ e ω).abs.const_mul 2) hω2)
  have hlim : Tendsto (fun r => errCoeff M Q e ω L r * r ^ 2) atTop (𝓝 ℓ) := by
    refine h.congr' (Eventually.of_forall fun r => ?_)
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    simp only [Pi.div_apply, errCoeff, abs_mul, abs_of_nonneg hr2]
    ring
  refine ⟨ℓ + 1, by linarith, ?_⟩
  filter_upwards [hlim.eventually_le_const (lt_add_one ℓ), eventually_gt_atTop 0] with r hr hr0
  rw [le_div_iff₀ (by positivity)]
  exact hr

end ModeStability.AllAngular.InfinityUniqueness

end
