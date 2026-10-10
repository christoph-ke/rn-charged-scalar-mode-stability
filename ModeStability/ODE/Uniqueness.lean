module

public import Mathlib

/-!
# Interior uniqueness for linear second-order ODEs

For continuous `p > 0` and continuous `w` on a half-line `(α, ∞)`, a complex-valued solution of
the self-adjoint equation `(p R')' + w R = 0` with `R(r₁) = R'(r₁) = 0` at an interior point
`r₁ > α` vanishes identically on `(α, ∞)`.

This is the standard Cauchy–Lipschitz uniqueness, applied to the first-order system
`Y = (R, p R')`, `Y' = (Y₂ / p, -w Y₁)`. On every compact `[c, d] ⊆ (α, ∞)` the coefficients
`1/p` and `w` are bounded, so the right-hand side is uniformly Lipschitz in `Y`, and Mathlib's
`ODE_solution_unique_of_mem_Ioo` applies on `(c, d)`.

It is used for the radial equation `(Δ R')' + K²/Δ · R = 0` of
the spherical research notes in preparation, (1.2), with `p = Δ`, `w = K²/Δ`. The paper does not
prove it.
-/

public section

namespace ModeStability.ODE

open Set

/-- The linear vector field `(y₁, y₂) ↦ (a y₂, b y₁)` on `ℂ × ℂ` with real coefficients bounded
by `K` is `K`-Lipschitz for the sup norm. -/
lemma lipschitzWith_linearField {a b : ℝ} {K : NNReal} (ha : |a| ≤ K) (hb : |b| ≤ K) :
    LipschitzWith K (fun y : ℂ × ℂ => ((a : ℂ) * y.2, (b : ℂ) * y.1)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Prod.dist_eq, Prod.dist_eq]
  have key : ∀ (c : ℝ) (u v : ℂ), |c| ≤ K → dist ((c : ℂ) * u) ((c : ℂ) * v) ≤
      K * dist u v := by
    intro c u v hc
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  refine max_le ?_ ?_
  · exact (key a _ _ ha).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) K.coe_nonneg)
  · exact (key b _ _ hb).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) K.coe_nonneg)

/-- On a compact subinterval `[c, d] ⊆ (α, ∞)`, the zero solution is the only solution of the
first-order system with vanishing initial value at an interior point. -/
lemma eqOn_zero_Ioo_of_linear_ode {α : ℝ} {p w : ℝ → ℝ} {R : ℝ → ℂ}
    (hp : ContinuousOn p (Set.Ioi α)) (hp0 : ∀ r ∈ Set.Ioi α, 0 < p r)
    (hw : ContinuousOn w (Set.Ioi α))
    (hR : ∀ r ∈ Set.Ioi α, DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv R s) (-((w r : ℝ) : ℂ) * R r) r)
    {c d r₁ : ℝ} (hc : α < c) (hr₁ : r₁ ∈ Ioo c d)
    (h0 : R r₁ = 0) (h1 : deriv R r₁ = 0) :
    EqOn R 0 (Ioo c d) := by
  have hcd : Icc c d ⊆ Ioi α := fun x hx => lt_of_lt_of_le hc hx.1
  have hne : (Icc c d).Nonempty := ⟨r₁, hr₁.1.le, hr₁.2.le⟩
  -- a positive lower bound for `p` and an upper bound for `|w|` on `[c, d]`
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne (hp.mono hcd)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hw.mono hcd)
  set m : ℝ := p x₀ with hm
  have hm0 : 0 < m := hp0 x₀ (hcd hx₀)
  let K : NNReal := Real.toNNReal (max m⁻¹ C)
  have hKm : m⁻¹ ≤ (K : ℝ) := (le_max_left _ _).trans (Real.le_coe_toNNReal _)
  have hKC : C ≤ (K : ℝ) := (le_max_right _ _).trans (Real.le_coe_toNNReal _)
  -- the vector field
  let v : ℝ → ℂ × ℂ → ℂ × ℂ := fun t y => (((p t)⁻¹ : ℝ) * y.2, ((-w t : ℝ) : ℂ) * y.1)
  have hv : ∀ t ∈ Ioo c d, LipschitzOnWith K (v t) univ := by
    intro t ht
    have htI : t ∈ Icc c d := ⟨ht.1.le, ht.2.le⟩
    refine (lipschitzWith_linearField (K := K) (a := (p t)⁻¹) (b := -w t) ?_ ?_).lipschitzOnWith
    · rw [abs_of_pos (inv_pos.2 (hp0 t (hcd htI)))]
      refine le_trans ?_ hKm
      exact inv_anti₀ hm0 (isMinOn_iff.1 hmin t htI)
    · rw [abs_neg]
      exact (Real.norm_eq_abs _ ▸ hC t htI).trans hKC
  -- the solution `Y = (R, p R')`
  have hf : ∀ t ∈ Ioo c d,
      HasDerivAt (fun s => (R s, (p s : ℂ) * deriv R s)) (v t (R t, (p t : ℂ) * deriv R t)) t ∧
        (R t, (p t : ℂ) * deriv R t) ∈ (univ : Set (ℂ × ℂ)) := by
    intro t ht
    have htα : t ∈ Ioi α := hcd ⟨ht.1.le, ht.2.le⟩
    obtain ⟨hdiff, hder⟩ := hR t htα
    refine ⟨?_, mem_univ _⟩
    have hpt : (p t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hp0 t htα).ne'
    have h1' : HasDerivAt R (deriv R t) t := hdiff.hasDerivAt
    have : v t (R t, (p t : ℂ) * deriv R t) = (deriv R t, -((w t : ℝ) : ℂ) * R t) := by
      simp only [v, Complex.ofReal_inv, Complex.ofReal_neg, neg_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hpt, one_mul]
    rw [this]
    exact h1'.prodMk hder
  have hg : ∀ t ∈ Ioo c d,
      HasDerivAt (fun _ : ℝ => ((0 : ℂ), (0 : ℂ))) (v t ((0 : ℂ), (0 : ℂ))) t ∧
        ((0 : ℂ), (0 : ℂ)) ∈ (univ : Set (ℂ × ℂ)) := by
    intro t _
    refine ⟨?_, mem_univ _⟩
    have : v t ((0 : ℂ), (0 : ℂ)) = 0 := by simp [v]
    rw [this]
    exact hasDerivAt_const t _
  have heq : (fun s => (R s, (p s : ℂ) * deriv R s)) r₁ = (fun _ : ℝ => ((0 : ℂ), (0 : ℂ))) r₁ := by
    simp [h0, h1]
  have := ODE_solution_unique_of_mem_Ioo hv hr₁ hf hg heq
  intro t ht
  exact congrArg Prod.fst (this ht)

/-- Interior uniqueness for `(p R')' + w R = 0` on `(α, ∞)`, `p > 0`, `p, w` continuous:
a solution with `R(r₁) = R'(r₁) = 0` at an interior point vanishes on `(α, ∞)`. -/
theorem eqOn_zero_of_linear_ode {α : ℝ} {p w : ℝ → ℝ} {R : ℝ → ℂ}
    (hp : ContinuousOn p (Set.Ioi α)) (hp0 : ∀ r ∈ Set.Ioi α, 0 < p r)
    (hw : ContinuousOn w (Set.Ioi α))
    (hR : ∀ r ∈ Set.Ioi α, DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (p s : ℂ) * deriv R s) (-((w r : ℝ) : ℂ) * R r) r)
    {r₁ : ℝ} (hr₁ : α < r₁) (h0 : R r₁ = 0) (h1 : deriv R r₁ = 0) :
    Set.EqOn R 0 (Set.Ioi α) := by
  intro t ht
  have hlt : α < min r₁ t := lt_min hr₁ ht
  set c : ℝ := (α + min r₁ t) / 2 with hc
  have hαc : α < c := by rw [hc]; linarith
  have hcr : c < r₁ := by
    have := min_le_left r₁ t
    rw [hc]; linarith
  have hct : c < t := by
    have := min_le_right r₁ t
    rw [hc]; linarith
  have hr₁d : r₁ < max r₁ t + 1 := by
    have := le_max_left r₁ t
    linarith
  have htd : t < max r₁ t + 1 := by
    have := le_max_right r₁ t
    linarith
  exact eqOn_zero_Ioo_of_linear_ode hp hp0 hw hR hαc ⟨hcr, hr₁d⟩ h0 h1 ⟨hct, htd⟩

end ModeStability.ODE

end
