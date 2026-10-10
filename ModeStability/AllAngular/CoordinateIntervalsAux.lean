module

public import Mathlib
public import ModeStability.AllAngular.TurningPointGeometry

/-!
# Generic transport of the turning-point geometry through a coordinate map

Source: the all-angular research notes in preparation, Section 3, p. 4), and Section 5, pp. 6–7,
(5.1)–(5.3).

Abstract bookkeeping for a coordinate map `ρ : (0, ∞) → (a, ∞)` that is strictly increasing
(reciprocal normalizations) or strictly decreasing (constant normalizations), used in
`ModeStability.AllAngular.CoordinateIntervals` and
`ModeStability.AllAngular.CoordinateIntervalsExtremal` for the four concrete coordinate systems.

* `coordinate_intervals_of_strictMonoOn`, `coordinate_intervals_of_strictAntiOn`: for
  `ρ(x_j) = r_j`, `r₁ < r₂`, the order of `x₁, x₂` and the images of the three coordinate
  intervals.
* `coordinate_point_of_strictMonoOn`, `coordinate_point_of_strictAntiOn`: the same for one point.
* `coordinate_signs_of_strictMonoOn`, `coordinate_signs_of_strictAntiOn`: if `F = c · (P ∘ ρ)`
  with
  `c > 0`, the radial sign pattern of `P` and `K` gives the sign pattern of `F` and `K ∘ ρ` on the
  coordinate intervals.
* `hasDerivAt_coefficient_at_turning_point`: `F'(x_j) = c(x_j) P'(r_j) ρ'(x_j)` when `P(r_j) = 0`.
* `radialK_neg_of_lt_corotation`, `radialK_pos_of_corotation_lt`,
  `corotation_sign_of_strictMonoOn`, `corotation_sign_of_strictAntiOn`: the sign of `K` on the two
  sides of corotation `r₀ = e/ω`, in `r` and in the coordinate.
-/

public section

open Set Filter Topology

namespace ModeStability.AllAngular

/-! ### Generic transport through a monotone coordinate map -/

/-- Images of the three coordinate intervals under an increasing coordinate map. -/
theorem coordinate_intervals_of_strictMonoOn {ρ : ℝ → ℝ} {a r₁ r₂ x₁ x₂ : ℝ}
    (hmono : StrictMonoOn ρ (Ioi 0)) (hmaps : ∀ x ∈ Ioi (0 : ℝ), a < ρ x)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hρ₁ : ρ x₁ = r₁) (hρ₂ : ρ x₂ = r₂) (h₁₂ : r₁ < r₂) :
    x₁ < x₂ ∧ (∀ x ∈ Ioo 0 x₁, ρ x ∈ Ioo a r₁) ∧ (∀ x ∈ Ioo x₁ x₂, ρ x ∈ Ioo r₁ r₂) ∧
      ∀ x ∈ Ioi x₂, ρ x ∈ Ioi r₂ := by
  subst hρ₁ hρ₂
  refine ⟨(hmono.lt_iff_lt hx₁ hx₂).1 h₁₂, fun x hx => ⟨hmaps x hx.1, hmono hx.1 hx₁ hx.2⟩,
    fun x hx => ?_, fun x hx => hmono hx₂ (hx₂.trans hx) hx⟩
  have h0 : 0 < x := hx₁.trans hx.1
  exact ⟨hmono hx₁ h0 hx.1, hmono h0 hx₂ hx.2⟩

/-- Images of the three coordinate intervals under a decreasing coordinate map. -/
theorem coordinate_intervals_of_strictAntiOn {ρ : ℝ → ℝ} {a r₁ r₂ y₁ y₂ : ℝ}
    (hanti : StrictAntiOn ρ (Ioi 0)) (hmaps : ∀ y ∈ Ioi (0 : ℝ), a < ρ y)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hρ₁ : ρ y₁ = r₁) (hρ₂ : ρ y₂ = r₂) (h₁₂ : r₁ < r₂) :
    y₂ < y₁ ∧ (∀ y ∈ Ioo 0 y₂, ρ y ∈ Ioi r₂) ∧ (∀ y ∈ Ioo y₂ y₁, ρ y ∈ Ioo r₁ r₂) ∧
      ∀ y ∈ Ioi y₁, ρ y ∈ Ioo a r₁ := by
  subst hρ₁ hρ₂
  refine ⟨(hanti.lt_iff_gt hy₁ hy₂).1 h₁₂, fun y hy => hanti hy.1 hy₂ hy.2, fun y hy => ?_,
    fun y hy => ⟨hmaps y (hy₁.trans hy), hanti hy₁ (hy₁.trans hy) hy⟩⟩
  have h0 : 0 < y := hy₂.trans hy.1
  exact ⟨hanti h0 hy₁ hy.2, hanti hy₂ h0 hy.1⟩

/-- Images of the two sides of one point under an increasing coordinate map. -/
theorem coordinate_point_of_strictMonoOn {ρ : ℝ → ℝ} {a r₀ x₀ : ℝ}
    (hmono : StrictMonoOn ρ (Ioi 0)) (hmaps : ∀ x ∈ Ioi (0 : ℝ), a < ρ x)
    (hx₀ : 0 < x₀) (hρ₀ : ρ x₀ = r₀) :
    (∀ x ∈ Ioo 0 x₀, ρ x ∈ Ioo a r₀) ∧ ∀ x ∈ Ioi x₀, ρ x ∈ Ioi r₀ := by
  subst hρ₀
  exact ⟨fun x hx => ⟨hmaps x hx.1, hmono hx.1 hx₀ hx.2⟩,
    fun x hx => hmono hx₀ (hx₀.trans hx) hx⟩

/-- Images of the two sides of one point under a decreasing coordinate map. -/
theorem coordinate_point_of_strictAntiOn {ρ : ℝ → ℝ} {a r₀ y₀ : ℝ}
    (hanti : StrictAntiOn ρ (Ioi 0)) (hmaps : ∀ y ∈ Ioi (0 : ℝ), a < ρ y)
    (hy₀ : 0 < y₀) (hρ₀ : ρ y₀ = r₀) :
    (∀ y ∈ Ioo 0 y₀, ρ y ∈ Ioi r₀) ∧ ∀ y ∈ Ioi y₀, ρ y ∈ Ioo a r₀ := by
  subst hρ₀
  exact ⟨fun y hy => hanti hy.1 hy₀ hy.2,
    fun y hy => ⟨hmaps y (hy₀.trans hy), hanti hy₀ (hy₀.trans hy) hy⟩⟩

/-- Sign transport for an increasing coordinate map and `F = c · (P ∘ ρ)` with `c > 0`. -/
theorem coordinate_signs_of_strictMonoOn {ρ F c P K : ℝ → ℝ} {a r₁ r₂ x₁ x₂ : ℝ}
    (hmono : StrictMonoOn ρ (Ioi 0)) (hmaps : ∀ x ∈ Ioi (0 : ℝ), a < ρ x)
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hρ₁ : ρ x₁ = r₁) (hρ₂ : ρ x₂ = r₂) (h₁₂ : r₁ < r₂)
    (hF : ∀ x ∈ Ioi (0 : ℝ), F x = c x * P (ρ x)) (hc : ∀ x ∈ Ioi (0 : ℝ), 0 < c x)
    (hP₁ : ∀ r ∈ Ioo a r₁, 0 < P r ∧ K r < 0) (hPm : ∀ r ∈ Ioo r₁ r₂, P r < 0)
    (hP₂ : ∀ r ∈ Ioi r₂, 0 < P r ∧ 0 < K r) :
    x₁ < x₂ ∧ (∀ x ∈ Ioo 0 x₁, 0 < F x ∧ K (ρ x) < 0) ∧ (∀ x ∈ Ioo x₁ x₂, F x < 0) ∧
      ∀ x ∈ Ioi x₂, 0 < F x ∧ 0 < K (ρ x) := by
  obtain ⟨h₁₂', hI₁, hIm, hI₂⟩ :=
    coordinate_intervals_of_strictMonoOn hmono hmaps hx₁ hx₂ hρ₁ hρ₂ h₁₂
  refine ⟨h₁₂', fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h0 : x ∈ Ioi (0 : ℝ) := hx.1
    obtain ⟨hp, hk⟩ := hP₁ _ (hI₁ x hx)
    rw [hF x h0]
    exact ⟨mul_pos (hc x h0) hp, hk⟩
  · have h0 : x ∈ Ioi (0 : ℝ) := hx₁.trans hx.1
    rw [hF x h0]
    exact mul_neg_of_pos_of_neg (hc x h0) (hPm _ (hIm x hx))
  · have h0 : x ∈ Ioi (0 : ℝ) := hx₂.trans hx
    obtain ⟨hp, hk⟩ := hP₂ _ (hI₂ x hx)
    rw [hF x h0]
    exact ⟨mul_pos (hc x h0) hp, hk⟩

/-- Sign transport for a decreasing coordinate map and `F = c · (P ∘ ρ)` with `c > 0`. -/
theorem coordinate_signs_of_strictAntiOn {ρ F c P K : ℝ → ℝ} {a r₁ r₂ y₁ y₂ : ℝ}
    (hanti : StrictAntiOn ρ (Ioi 0)) (hmaps : ∀ y ∈ Ioi (0 : ℝ), a < ρ y)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hρ₁ : ρ y₁ = r₁) (hρ₂ : ρ y₂ = r₂) (h₁₂ : r₁ < r₂)
    (hF : ∀ y ∈ Ioi (0 : ℝ), F y = c y * P (ρ y)) (hc : ∀ y ∈ Ioi (0 : ℝ), 0 < c y)
    (hP₁ : ∀ r ∈ Ioo a r₁, 0 < P r ∧ K r < 0) (hPm : ∀ r ∈ Ioo r₁ r₂, P r < 0)
    (hP₂ : ∀ r ∈ Ioi r₂, 0 < P r ∧ 0 < K r) :
    y₂ < y₁ ∧ (∀ y ∈ Ioo 0 y₂, 0 < F y ∧ 0 < K (ρ y)) ∧ (∀ y ∈ Ioo y₂ y₁, F y < 0) ∧
      ∀ y ∈ Ioi y₁, 0 < F y ∧ K (ρ y) < 0 := by
  obtain ⟨h₂₁, hI₂, hIm, hI₁⟩ :=
    coordinate_intervals_of_strictAntiOn hanti hmaps hy₁ hy₂ hρ₁ hρ₂ h₁₂
  refine ⟨h₂₁, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have h0 : y ∈ Ioi (0 : ℝ) := hy.1
    obtain ⟨hp, hk⟩ := hP₂ _ (hI₂ y hy)
    rw [hF y h0]
    exact ⟨mul_pos (hc y h0) hp, hk⟩
  · have h0 : y ∈ Ioi (0 : ℝ) := hy₂.trans hy.1
    rw [hF y h0]
    exact mul_neg_of_pos_of_neg (hc y h0) (hPm _ (hIm y hy))
  · have h0 : y ∈ Ioi (0 : ℝ) := hy₁.trans hy
    obtain ⟨hp, hk⟩ := hP₁ _ (hI₁ y hy)
    rw [hF y h0]
    exact ⟨mul_pos (hc y h0) hp, hk⟩

/-- The derivative of `F = c · (P ∘ ρ)` at a coordinate turning point `x` with `ρ(x) = r`,
`P(r) = 0`. -/
theorem hasDerivAt_coefficient_at_turning_point {F c ρ P : ℝ → ℝ} {x r c' ρ' p : ℝ} (hx : 0 < x)
    (hF : ∀ y ∈ Ioi (0 : ℝ), F y = c y * P (ρ y)) (hc : HasDerivAt c c' x)
    (hρ : HasDerivAt ρ ρ' x) (hρx : ρ x = r) (hP : HasDerivAt P p r) (h0 : P r = 0) :
    HasDerivAt F (c x * (p * ρ')) x := by
  subst hρx
  exact (hasDerivAt_mul_comp_at_zero hc hρ hP h0).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioi_mem_nhds hx) hF)

/-- `a ≥ 0` for `|Q| ≤ M`. -/
theorem outerHorizon_nonneg_of_abs_le {M Q : ℝ} (hQ : |Q| ≤ M) : 0 ≤ outerHorizon M Q := by
  have h1 := Real.sqrt_nonneg (M ^ 2 - Q ^ 2)
  have h2 := abs_nonneg Q
  unfold outerHorizon
  linarith

/-- `K(r) < 0` for `0 < r < e/ω`, `ω > 0`. -/
theorem radialK_neg_of_lt_corotation {e ω r : ℝ} (hω : 0 < ω) (hr : 0 < r) (h : r < e / ω) :
    radialK e ω r < 0 := by
  have h' : r * ω < e := (lt_div_iff₀ hω).1 h
  have hK : radialK e ω r = r * (ω * r - e) := by
    unfold radialK
    ring
  rw [hK]
  exact mul_neg_of_pos_of_neg hr (by linarith)

/-- `K(r) > 0` for `r > e/ω`, `r > 0`, `ω > 0`. -/
theorem radialK_pos_of_corotation_lt {e ω r : ℝ} (hω : 0 < ω) (hr : 0 < r) (h : e / ω < r) :
    0 < radialK e ω r := by
  have h' : e < r * ω := (div_lt_iff₀ hω).1 h
  have hK : radialK e ω r = r * (ω * r - e) := by
    unfold radialK
    ring
  rw [hK]
  exact mul_pos hr (by linarith)

/-- The corotation sign pattern, increasing systems: `K(ρ(x)) < 0` left of `x₀`, `> 0` right. -/
theorem corotation_sign_of_strictMonoOn {ρ : ℝ → ℝ} {a e ω x₀ : ℝ} (ha : 0 ≤ a) (hω : 0 < ω)
    (hmono : StrictMonoOn ρ (Ioi 0)) (hmaps : ∀ x ∈ Ioi (0 : ℝ), a < ρ x)
    (hx₀ : 0 < x₀) (hρ₀ : ρ x₀ = e / ω) :
    (∀ x ∈ Ioo 0 x₀, radialK e ω (ρ x) < 0) ∧ ∀ x ∈ Ioi x₀, 0 < radialK e ω (ρ x) := by
  obtain ⟨h₁, h₂⟩ := coordinate_point_of_strictMonoOn hmono hmaps hx₀ hρ₀
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨hl, hr⟩ := h₁ x hx
    exact radialK_neg_of_lt_corotation hω (lt_of_le_of_lt ha hl) hr
  · exact radialK_pos_of_corotation_lt hω (lt_of_le_of_lt ha (hmaps x (hx₀.trans hx))) (h₂ x hx)

/-- The corotation sign pattern, decreasing systems: `K(ρ(y)) > 0` left of `y₀`, `< 0` right. -/
theorem corotation_sign_of_strictAntiOn {ρ : ℝ → ℝ} {a e ω y₀ : ℝ} (ha : 0 ≤ a) (hω : 0 < ω)
    (hanti : StrictAntiOn ρ (Ioi 0)) (hmaps : ∀ y ∈ Ioi (0 : ℝ), a < ρ y)
    (hy₀ : 0 < y₀) (hρ₀ : ρ y₀ = e / ω) :
    (∀ y ∈ Ioo 0 y₀, 0 < radialK e ω (ρ y)) ∧ ∀ y ∈ Ioi y₀, radialK e ω (ρ y) < 0 := by
  obtain ⟨h₁, h₂⟩ := coordinate_point_of_strictAntiOn hanti hmaps hy₀ hρ₀
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · exact radialK_pos_of_corotation_lt hω (lt_of_le_of_lt ha (hmaps y hy.1)) (h₁ y hy)
  · obtain ⟨hl, hr⟩ := h₂ y hy
    exact radialK_neg_of_lt_corotation hω (lt_of_le_of_lt ha hl) hr
end ModeStability.AllAngular

end
