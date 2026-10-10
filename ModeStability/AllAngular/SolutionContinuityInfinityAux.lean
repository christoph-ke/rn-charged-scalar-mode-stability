module

public import Mathlib
public import ModeStability.AllAngular.SolutionContinuityAux
public import ModeStability.AllAngular.InfinitySolution

/-!
# Uniform tail bounds for frequency continuity

Source: the all-angular research notes in preparation, p. 10, continuity of the
normalized outgoing solution used in Proposition 6.1. Compactifying the radius
by `y = 1/r` gives locally uniform bounds for the integrable amplitude system.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

open InfinityUniqueness InfinitySolution

@[expose] noncomputable def sc_errI_hat (M Q e L : ℝ) (p : ℝ × ℝ) : ℝ :=
  let D := 1 - 2 * M * p.2 + Q ^ 2 * p.2 ^ 2
  |(2 * M - 2 * Q ^ 2 * p.2) / D| / 2 +
    (|(-2 * M * p.2 + 2 * Q ^ 2 * p.2 ^ 2 - L) / D| +
      |(e - 2 * M * p.1 + 2 * p.1 * Q ^ 2 * p.2 - e * Q ^ 2 * p.2 ^ 2) / D ^ 2|) /
      (2 * |(p.1 - e * p.2) / D|)

theorem sc_errI_hat_eq {M Q e L ω r : ℝ} (hQ : |Q| ≤ M) (hr : r ≠ 0)
    (hD : 1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2 ≠ 0) :
    errCoeff M Q e ω L r * r ^ 2 = sc_errI_hat M Q e L (ω, r⁻¹) := by
  have hd : dampCoeff M Q r * r ^ 2 =
      (2 * M - 2 * Q ^ 2 * r⁻¹) / (1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2) := by
    unfold dampCoeff
    rw [delta_eq_sq_mul hQ hr]
    field_simp
  have hp : potCoeff M Q L r * r ^ 2 =
      (-2 * M * r⁻¹ + 2 * Q ^ 2 * (r⁻¹) ^ 2 - L) /
        (1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2) := by
    unfold potCoeff
    rw [delta_eq_sq_mul hQ hr]
    field_simp
  have ha : phaseAccel M Q e ω r * r ^ 2 =
      (e - 2 * M * ω + 2 * ω * Q ^ 2 * r⁻¹ - e * Q ^ 2 * (r⁻¹) ^ 2) /
        (1 - 2 * M * r⁻¹ + Q ^ 2 * (r⁻¹) ^ 2) ^ 2 := by
    unfold phaseAccel radialK
    rw [delta_eq_sq_mul hQ hr]
    field_simp
    ring
  unfold sc_errI_hat
  dsimp only
  rw [← hd, ← hp, ← ha, ← phaseRate_eq_inv hQ hr hD]
  simp only [errCoeff, abs_mul, abs_of_nonneg (sq_nonneg r)]
  ring

/-- A common exterior tail and integrable bound near any nonzero frequency. -/
theorem sc_infinity_patch {M Q e L ω₀ : ℝ} (hQ : |Q| ≤ M) (hω₀ : ω₀ ≠ 0) :
    ∃ S : Set ℝ, IsOpen S ∧ ω₀ ∈ S ∧ ∃ b C : ℝ,
      outerHorizon M Q ≤ b ∧ 0 < b ∧
      ∀ ω ∈ S, ω ≠ 0 ∧ ∀ r, b < r →
        phaseRate M Q e ω r ≠ 0 ∧ errCoeff M Q e ω L r ≤ C / r ^ 2 := by
  have hD : Continuous (fun p : ℝ × ℝ => 1 - 2 * M * p.2 + Q ^ 2 * p.2 ^ 2) := by fun_prop
  have hN : Continuous (fun p : ℝ × ℝ => p.1 - e * p.2) := by fun_prop
  have hDc : ContinuousAt (fun p : ℝ × ℝ => 1 - 2 * M * p.2 + Q ^ 2 * p.2 ^ 2) (ω₀, 0) :=
    hD.continuousAt
  have hDn : (1 - 2 * M * (0 : ℝ) + Q ^ 2 * 0 ^ 2) ≠ 0 := by norm_num
  have hθ := hN.continuousAt.div hDc hDn
  have hθn : ((ω₀ - e * 0) / (1 - 2 * M * 0 + Q ^ 2 * 0 ^ 2)) ≠ 0 := by simpa using hω₀
  have hF : ContinuousAt (sc_errI_hat M Q e L) (ω₀, 0) := by
    unfold sc_errI_hat
    dsimp only
    refine ContinuousAt.add ((ContinuousAt.div (by fun_prop) hDc hDn).abs.div_const 2) ?_
    refine ContinuousAt.div ?_ (hθ.abs.const_mul 2) (mul_ne_zero two_ne_zero (abs_ne_zero.2 hθn))
    exact ((ContinuousAt.div (by fun_prop) hDc hDn).abs).add
      ((ContinuousAt.div (by fun_prop) (hDc.pow 2) (pow_ne_zero 2 hDn)).abs)
  have hmap : Tendsto (fun p : ℝ × ℝ => (p.1, p.2⁻¹)) (𝓝 ω₀ ×ˢ (atTop : Filter ℝ))
      (𝓝 (ω₀, 0)) :=
    tendsto_fst.prodMk_nhds (tendsto_inv_atTop_zero.comp tendsto_snd)
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 ω₀ ×ˢ (atTop : Filter ℝ),
      p.1 ≠ 0 ∧ (1 - 2 * M * p.2⁻¹ + Q ^ 2 * (p.2⁻¹) ^ 2) ≠ 0 ∧
      (p.1 - e * p.2⁻¹) ≠ 0 ∧
      sc_errI_hat M Q e L (p.1, p.2⁻¹) ≤ sc_errI_hat M Q e L (ω₀, 0) + 1 := by
    have hω := (continuous_fst.continuousAt.tendsto.comp hmap).eventually_ne hω₀
    have hd := (hDc.tendsto.comp hmap).eventually_ne hDn
    have hn := (hN.continuousAt.tendsto.comp hmap).eventually_ne (by simpa using hω₀)
    have hf := (hF.tendsto.comp hmap).eventually_le_const (lt_add_one _)
    filter_upwards [hω, hd, hn, hf] with p hp hd hn hf using ⟨hp, hd, hn, hf⟩
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.1 hev
  obtain ⟨S, hSU, hSo, hωS⟩ := mem_nhds_iff.1 hU
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.1 hV
  let b := max (max b₀ (outerHorizon M Q)) 1
  have hb₀b : b₀ ≤ b := (le_max_left _ _).trans (le_max_left _ _)
  have hab : outerHorizon M Q ≤ b := (le_max_right _ _).trans (le_max_left _ _)
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨S, hSo, hωS, b, sc_errI_hat M Q e L (ω₀, 0) + 1, hab, hb, ?_⟩
  intro ω hω
  have hωn := (hUV (show (ω, b) ∈ U ×ˢ V from ⟨hSU hω, hb₀ b hb₀b⟩)).1
  refine ⟨hωn, fun r hr => ?_⟩
  have hx := hUV (show (ω, r) ∈ U ×ˢ V from ⟨hSU hω, hb₀ r (hb₀b.trans hr.le)⟩)
  have hr0 : r ≠ 0 := (hb.trans hr).ne'
  refine ⟨?_, ?_⟩
  · rw [phaseRate_eq_inv hQ hr0 hx.2.1]
    exact div_ne_zero hx.2.2.1 hx.2.1
  · rw [le_div_iff₀ (sq_pos_of_ne_zero hr0), sc_errI_hat_eq hQ hr0 hx.2.1]
    exact hx.2.2.2

end ModeStability.AllAngular

end
