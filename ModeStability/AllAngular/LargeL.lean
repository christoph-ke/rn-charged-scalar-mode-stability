module

public import Mathlib
public import ModeStability.AllAngular.LargeLAux
public import ModeStability.AllAngular.NormalizationFacts

/-!
# The large-`L` regime of Proposition 6.1

Source: the all-angular research notes in preparation, all-angular paper p. 8.
The abstract integral estimate uses the source identity and coercivity as inputs.
The compact-interval coefficient theorem supplies a uniform forbidden-set lower
bound for the frozen normalization `normalizationG`, including the extremal exterior.
-/

public section

open MeasureTheory Complex Set
open scoped ComplexConjugate

namespace ModeStability.AllAngular

/-- The large-`L` energy bound on any measure space (in particular, the measure
restricted to the source interval). `Ux` denotes the derivative supplied by the
application; the estimate itself needs only the source identity and coercivity.
The explicit constant is `4 (1 + 1/c)²`, depending only on `c`. -/
theorem largeL_integral_estimate {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F U Ux : α → ℂ} {B c L L₀ : ℝ}
    (hF : MemLp F 2 μ) (hU : MemLp U 2 μ)
    (hc : 0 < c) (hL₀ : 1 ≤ L₀) (hL : L₀ ≤ L)
    (hsource : B = -(∫ x, F x * conj (U x) ∂μ).re)
    (hcoerc : (∫ x, ‖Ux x‖ ^ 2 ∂μ) + c * L * (∫ x, ‖U x‖ ^ 2 ∂μ) ≤ B) :
    B + (∫ x, ‖Ux x‖ ^ 2 ∂μ) + (1 + L) * (∫ x, ‖U x‖ ^ 2 ∂μ) ≤
      (4 * (1 + 1 / c) ^ 2 / (1 + L)) * (∫ x, ‖F x‖ ^ 2 ∂μ) := by
  apply largeL_scalar_estimate (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    hc hL₀ hL hcoerc
  rw [hsource]
  exact largeL_source_cauchy_schwarz hF hU

private theorem ll_continuous_delta (M Q : ℝ) : Continuous (delta M Q) := by
  unfold delta
  fun_prop

private theorem ll_continuous_K (e ω : ℝ) : Continuous (radialK e ω) := by
  unfold radialK
  fun_prop

private theorem ll_g_pos {M Q e ω r : ℝ} (hM : 0 < M)
    (hr : outerHorizon M Q < r) : 0 < normalizationG M Q e ω r := by
  unfold normalizationG
  split_ifs
  · exact one_pos
  · exact NormalizationFacts.staticSolutionAA_pos hM hr

private theorem ll_g_continuousOn {M Q e ω ρ₁ ρ₂ : ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hρ : outerHorizon M Q < ρ₁) :
    ContinuousOn (normalizationG M Q e ω) (Icc ρ₁ ρ₂) := by
  intro r hr
  by_cases h : e / ω < 2 * M
  · rw [NormalizationFacts.normalizationG_eq_one h]
    exact continuousWithinAt_const
  · rw [NormalizationFacts.normalizationG_eq_static h]
    exact (NormalizationFacts.hasDerivAt_staticSolutionAA hM hQ
      (hρ.trans_le hr.1)).continuousAt.continuousWithinAt

/-- Uniformly on a compact exterior interval, large `L` makes `K² ≤ LΔ/2`.
The interval is contained in the forbidden set `Fb = {r > a | K² ≤ LΔ}`,
and its forbidden bulk coefficient `g⁴ (LΔ − K²)` is bounded below by `c' L`
with `c' > 0` independent of `L`. The intermediate lower bound has factor `1/2`.
No sign or nonzero assumption on the fixed real frequency is needed. -/
theorem largeL_compact_lower_bound {M Q e ω ρ₁ ρ₂ : ℝ}
    (hM : 0 < M) (hQ : |Q| ≤ M) (hρ : outerHorizon M Q < ρ₁)
    (hρ₁₂ : ρ₁ ≤ ρ₂) :
    ∃ L₀ c' : ℝ, 1 ≤ L₀ ∧ 0 < c' ∧
      (∀ r ∈ Icc ρ₁ ρ₂, radialK e ω r ^ 2 ≤ L₀ * delta M Q r / 2) ∧
      ∀ L : ℝ, L₀ ≤ L →
        Icc ρ₁ ρ₂ ⊆ {r | outerHorizon M Q < r ∧
          radialK e ω r ^ 2 ≤ L * delta M Q r} ∧
        ∀ r ∈ Icc ρ₁ ρ₂,
          radialK e ω r ^ 2 ≤ L * delta M Q r / 2 ∧
          (L / 2) * (normalizationG M Q e ω r ^ 4 * delta M Q r) ≤
            normalizationG M Q e ω r ^ 4 * (L * delta M Q r - radialK e ω r ^ 2) ∧
          c' * L ≤ normalizationG M Q e ω r ^ 4 *
            (L * delta M Q r - radialK e ω r ^ 2) := by
  have hΔ : ∀ r ∈ Icc ρ₁ ρ₂, 0 < delta M Q r := fun r hr =>
    NormalizationFacts.delta_pos_of_outerHorizon_lt (hρ.trans_le hr.1)
  have hcont : ContinuousOn (fun r => 2 * radialK e ω r ^ 2 / delta M Q r)
      (Icc ρ₁ ρ₂) :=
    (continuous_const.mul ((ll_continuous_K e ω).pow 2)).continuousOn.div
      (ll_continuous_delta M Q).continuousOn (fun r hr => (hΔ r hr).ne')
  obtain ⟨rmax, hrmax, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hρ₁₂) hcont
  let L₀ := max 1 (2 * radialK e ω rmax ^ 2 / delta M Q rmax)
  have hL₀ : 1 ≤ L₀ := le_max_left _ _
  have hK₀ : ∀ r ∈ Icc ρ₁ ρ₂, radialK e ω r ^ 2 ≤ L₀ * delta M Q r / 2 := by
    intro r hr
    have hh : 2 * radialK e ω r ^ 2 / delta M Q r ≤ L₀ :=
      (hmax hr).trans (le_max_right _ _)
    have := (div_le_iff₀ (hΔ r hr)).mp hh
    linarith
  have hwcont : ContinuousOn
      (fun r => normalizationG M Q e ω r ^ 4 * delta M Q r) (Icc ρ₁ ρ₂) :=
    (ll_g_continuousOn hM hQ hρ).pow 4 |>.mul (ll_continuous_delta M Q).continuousOn
  obtain ⟨d, hd, hdlower⟩ := isCompact_Icc.exists_forall_le' hwcont
    (fun r hr => mul_pos (pow_pos (ll_g_pos hM (hρ.trans_le hr.1)) 4) (hΔ r hr))
  refine ⟨L₀, d / 2, hL₀, by positivity, hK₀, ?_⟩
  intro L hL
  have hLp : 0 < L := by linarith
  have hKL : ∀ r ∈ Icc ρ₁ ρ₂, radialK e ω r ^ 2 ≤ L * delta M Q r / 2 := by
    intro r hr
    exact (hK₀ r hr).trans (by
      gcongr
      exact (hΔ r hr).le)
  refine ⟨?_, ?_⟩
  · intro r hr
    refine ⟨hρ.trans_le hr.1, ?_⟩
    have := hKL r hr
    have := mul_pos hLp (hΔ r hr)
    linarith
  · intro r hr
    have hg4 : 0 ≤ normalizationG M Q e ω r ^ 4 := by positivity
    have hhalf : (L / 2) * (normalizationG M Q e ω r ^ 4 * delta M Q r) ≤
        normalizationG M Q e ω r ^ 4 * (L * delta M Q r - radialK e ω r ^ 2) := by
      have hh := mul_le_mul_of_nonneg_left (hKL r hr) hg4
      nlinarith
    refine ⟨hKL r hr, hhalf, ?_⟩
    have hh := mul_le_mul_of_nonneg_left (hdlower r hr) (by positivity : 0 ≤ L / 2)
    nlinarith

end ModeStability.AllAngular

end
