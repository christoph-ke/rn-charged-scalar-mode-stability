module

public import Mathlib

/-!
# Uniqueness at the horizon: the forward Grönwall argument

Auxiliary material for `ModeStability.AllAngular.HorizonUniqueness`, which proves the horizon
half of the assertion of the all-angular research notes in preparation, p. 2, that a nonzero
solution of the radial equation satisfying the ingoing horizon condition (1.4) has a nonzero
leading coefficient there.

* `hu_norm_le_of_tendsto_nhdsGT`: if `c → 0` as `t ↓ a` and `‖c'‖ ≤ D` on `(a, t₀]`, then
  `‖c(t₀)‖ ≤ D (t₀ − a)` (mean value inequality on `[s, t₀]`, then `s ↓ a`).
* `hu_eq_zero_of_norm_deriv_le`: the forward Grönwall argument from the horizon for a pair of
  amplitudes with `‖a'ᵢ‖ ≤ C (‖a₁‖ + ‖a₂‖)` on `(a, b]` that tend to `0` as `t ↓ a`.
* `hu_norm_amp_deriv_le`, `hu_eq_zero_of_amps_eq_zero`: the algebra of the horizon amplitudes
  `A = e^{−iΘ}(P + iKR)`, `B = e^{iΘ}(P − iKR)` (`P = ΔR'`), namely
  `2iKR = e^{iΘ}A − e^{−iΘ}B` and `2P = e^{iΘ}A + e^{−iΘ}B`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-! ### The forward Grönwall argument from the horizon -/

/-- If `c → 0` as `t ↓ a` and `‖c'(t)‖ ≤ D` on `(a, t₀]`, then `‖c(t₀)‖ ≤ D (t₀ − a)`. -/
theorem hu_norm_le_of_tendsto_nhdsGT {c c' : ℝ → ℂ} {a t₀ D : ℝ} (ht₀ : a < t₀)
    (hc : ∀ t ∈ Ioc a t₀, HasDerivAt c (c' t) t) (hb : ∀ t ∈ Ioc a t₀, ‖c' t‖ ≤ D)
    (hlim : Tendsto c (𝓝[>] a) (𝓝 0)) : ‖c t₀‖ ≤ D * (t₀ - a) := by
  have hD : 0 ≤ D := (norm_nonneg _).trans (hb t₀ ⟨ht₀, le_rfl⟩)
  have key : ∀ s ∈ Ioo a t₀, ‖c t₀ - c s‖ ≤ D * (t₀ - a) := by
    intro s hs
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := c) (f' := c') (a := s)
      (b := t₀) (C := D)
      (fun x hx => (hc x ⟨hs.1.trans_le hx.1, hx.2⟩).hasDerivWithinAt)
      (fun x hx => hb x ⟨hs.1.trans_le hx.1, hx.2.le⟩) t₀ (right_mem_Icc.2 hs.2.le)
    calc ‖c t₀ - c s‖ ≤ D * (t₀ - s) := h
      _ ≤ D * (t₀ - a) := mul_le_mul_of_nonneg_left (by linarith [hs.1]) hD
  have hT : Tendsto (fun s => ‖c t₀ - c s‖) (𝓝[>] a) (𝓝 ‖c t₀ - 0‖) :=
    (tendsto_const_nhds.sub hlim).norm
  rw [sub_zero] at hT
  refine le_of_tendsto hT ?_
  filter_upwards [Ioo_mem_nhdsGT ht₀] with s hs using key s hs

/-- The forward Grönwall argument from the horizon: two amplitudes on `(a, b]` with
`‖a'ᵢ(t)‖ ≤ C (‖a₁(t)‖ + ‖a₂(t)‖)`, `4C(b − a) ≤ 1`, `‖a₁‖ + ‖a₂‖ ≤ 1` and `aᵢ → 0` as `t ↓ a`
vanish at `b`. -/
theorem hu_eq_zero_of_norm_deriv_le {a₁ a₂ a₁' a₂' : ℝ → ℂ} {a b C : ℝ} (hab : a < b)
    (hC : 0 ≤ C) (hCb : 4 * C * (b - a) ≤ 1)
    (h₁ : ∀ t ∈ Ioc a b, HasDerivAt a₁ (a₁' t) t) (h₂ : ∀ t ∈ Ioc a b, HasDerivAt a₂ (a₂' t) t)
    (hb₁ : ∀ t ∈ Ioc a b, ‖a₁' t‖ ≤ C * (‖a₁ t‖ + ‖a₂ t‖))
    (hb₂ : ∀ t ∈ Ioc a b, ‖a₂' t‖ ≤ C * (‖a₁ t‖ + ‖a₂ t‖))
    (hl₁ : Tendsto a₁ (𝓝[>] a) (𝓝 0)) (hl₂ : Tendsto a₂ (𝓝[>] a) (𝓝 0))
    (hbd : ∀ t ∈ Ioc a b, ‖a₁ t‖ + ‖a₂ t‖ ≤ 1) :
    a₁ b = 0 ∧ a₂ b = 0 := by
  have half : ∀ B : ℝ, (∀ t ∈ Ioc a b, ‖a₁ t‖ + ‖a₂ t‖ ≤ B) →
      ∀ t ∈ Ioc a b, ‖a₁ t‖ + ‖a₂ t‖ ≤ B / 2 := by
    intro B hB t ht
    have hB0 : 0 ≤ B :=
      (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hB b ⟨hab, le_rfl⟩)
    have hsub : Ioc a t ⊆ Ioc a b := Ioc_subset_Ioc_right ht.2
    have bound : ∀ (c c' : ℝ → ℂ), (∀ x ∈ Ioc a b, HasDerivAt c (c' x) x) →
        (∀ x ∈ Ioc a b, ‖c' x‖ ≤ C * (‖a₁ x‖ + ‖a₂ x‖)) → Tendsto c (𝓝[>] a) (𝓝 0) →
        ‖c t‖ ≤ B / 4 := by
      intro c c' hc hb hl
      have h := hu_norm_le_of_tendsto_nhdsGT ht.1 (fun x hx => hc x (hsub hx))
        (fun x hx => (hb x (hsub hx)).trans (mul_le_mul_of_nonneg_left (hB x (hsub hx)) hC)) hl
      have h4 : B * (4 * C * (b - a)) ≤ B * 1 := mul_le_mul_of_nonneg_left hCb hB0
      calc ‖c t‖ ≤ C * B * (t - a) := h
        _ ≤ C * B * (b - a) :=
            mul_le_mul_of_nonneg_left (by linarith [ht.2]) (mul_nonneg hC hB0)
        _ ≤ B / 4 := by linarith
    linarith [bound a₁ a₁' h₁ hb₁ hl₁, bound a₂ a₂' h₂ hb₂ hl₂]
  have hpow : ∀ n : ℕ, ∀ t ∈ Ioc a b, ‖a₁ t‖ + ‖a₂ t‖ ≤ (1 / 2 : ℝ) ^ n := by
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
  have h0 : ‖a₁ b‖ + ‖a₂ b‖ ≤ 0 := ge_of_tendsto' hlim (fun n => hpow n b ⟨hab, le_rfl⟩)
  constructor
  · exact norm_le_zero_iff.1 (by linarith [norm_nonneg (a₂ b)])
  · exact norm_le_zero_iff.1 (by linarith [norm_nonneg (a₁ b)])

/-! ### Algebra of the horizon amplitudes -/

/-- The amplitude bound: with `A = E⁻¹(P + iKR)`, `B = E(P − iKR)`, `|E| = 1`,
`‖F(ζR)‖ ≤ c/(2|K|) (‖A‖ + ‖B‖)` whenever `|F| = 1`, `‖ζ‖ ≤ c`, `K ≠ 0`. -/
theorem hu_norm_amp_deriv_le {E Ei F P R ζ : ℂ} {K c : ℝ} (hE : ‖E‖ = 1) (hEi : ‖Ei‖ = 1)
    (hEEi : E * Ei = 1) (hF : ‖F‖ = 1) (hK : K ≠ 0) (hζ : ‖ζ‖ ≤ c) :
    ‖F * (ζ * R)‖ ≤
      c / (2 * |K|) * (‖Ei * (P + I * K * R)‖ + ‖E * (P - I * K * R)‖) := by
  set A := Ei * (P + I * K * R) with hA
  set B := E * (P - I * K * R) with hB
  have hK0 : 0 < |K| := abs_pos.2 hK
  have hc : 0 ≤ c := (norm_nonneg _).trans hζ
  have h2R : (2 * I * K : ℂ) * R = E * A - Ei * B := by
    rw [hA, hB]
    linear_combination (-2 * I * K * R) * hEEi
  have hR : ‖R‖ ≤ (‖A‖ + ‖B‖) / (2 * |K|) := by
    have h := congrArg norm h2R
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_two, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs] at h
    have h' : ‖E * A - Ei * B‖ ≤ ‖A‖ + ‖B‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul E A, norm_mul Ei B, hE, hEi, one_mul, one_mul]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc ‖F * (ζ * R)‖ = ‖ζ‖ * ‖R‖ := by rw [norm_mul, hF, one_mul, norm_mul]
    _ ≤ c * ((‖A‖ + ‖B‖) / (2 * |K|)) :=
        mul_le_mul hζ hR (norm_nonneg _) hc
    _ = c / (2 * |K|) * (‖A‖ + ‖B‖) := by ring

/-- If both horizon amplitudes vanish, so do `P` and `R` (for `K ≠ 0`). -/
theorem hu_eq_zero_of_amps_eq_zero {E Ei P R : ℂ} {K : ℝ} (hEEi : E * Ei = 1) (hK : K ≠ 0)
    (hA : Ei * (P + I * K * R) = 0) (hB : E * (P - I * K * R) = 0) : P = 0 ∧ R = 0 := by
  have hE : E ≠ 0 := left_ne_zero_of_mul_eq_one hEEi
  have hEi : Ei ≠ 0 := right_ne_zero_of_mul_eq_one hEEi
  have h1 := (mul_eq_zero.1 hA).resolve_left hEi
  have h2 := (mul_eq_zero.1 hB).resolve_left hE
  have h3 : (2 * I * K : ℂ) * R = 0 := by linear_combination h1 - h2
  have h4 : (2 * I * K : ℂ) ≠ 0 := by
    have : (K : ℂ) ≠ 0 := ofReal_ne_zero.2 hK
    simp [this, I_ne_zero]
  have hR : R = 0 := (mul_eq_zero.1 h3).resolve_left h4
  refine ⟨?_, hR⟩
  rw [hR, mul_zero, add_zero] at h1
  exact h1

end ModeStability.AllAngular

end
