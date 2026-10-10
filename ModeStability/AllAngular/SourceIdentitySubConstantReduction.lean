module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityRAux
public import ModeStability.AllAngular.SourceIdentitySubConstantCoefficients

/-!
# The constant source reduction in radial variables

Source: the all-angular research notes in preparation, (6.1) and (6.3).
For `g = 1`, `x = −h`, the reduced flux is `Ux = ΔR'`. The integrated
source equation supplies its absolute continuity and derivative almost
everywhere, without a pointwise second derivative for the L² source.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-- The exact frozen constant reduction, including the rough source. -/
theorem ssc_reduction {M Q e ω L : ℝ}
    (hQ : |Q| < M) (hN : e / ω < 2 * M) {R S : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    (hS : ∀ b ∈ Ioi (outerHorizon M Q), ∀ c ∈ Ioi (outerHorizon M Q),
      IntervalIntegrable S volume b c)
    (hint : ∀ b ∈ Ioi (outerHorizon M Q), ∀ c ∈ Ioi (outerHorizon M Q),
      (delta M Q c : ℂ) * deriv R c - (delta M Q b : ℂ) * deriv R b =
        ∫ r in b..c, S r - (((radialK e ω r ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r)) :
    let g := normalizationG M Q e ω
    let U := fun r => R r / (g r : ℂ)
    let Ux := fun r => ((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r
    ContDiffOn ℝ 1 U (Ioi (outerHorizon M Q)) ∧
      ∀ b ∈ Ioi (outerHorizon M Q), ∀ c ∈ Ioi (outerHorizon M Q),
        AbsolutelyContinuousOnInterval Ux b c ∧
          ∀ᵐ r, r ∈ uIcc b c → HasDerivAt Ux
            (((1 / (delta M Q r * g r ^ 2) : ℝ) : ℂ) *
              (-((g r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r) : ℝ) : ℂ) * U r +
                ((delta M Q r * g r ^ 3 : ℝ) : ℂ) * S r)) r := by
  rw [NormalizationFacts.normalizationG_eq_one hN]
  simp only [one_pow, mul_one, ofReal_one, div_one]
  have hp : ContinuousOn (delta M Q) (Ioi (outerHorizon M Q)) :=
    (CoordinateCoefficients.contDiff_delta M Q).continuous.continuousOn
  have hp0 : ∀ r ∈ Ioi (outerHorizon M Q), delta M Q r ≠ 0 :=
    fun r hr => (delta_pos hQ hr).ne'
  have hq : ContinuousOn (fun r => radialK e ω r ^ 2 / delta M Q r - L)
      (Ioi (outerHorizon M Q)) :=
    (((CoordinateCoefficients.contDiff_radialK e ω).continuous.pow 2).continuousOn.div
      hp hp0).sub continuousOn_const
  refine ⟨source_solution_contDiffOn_one hp hp0 hq hR hS hint, ?_⟩
  intro b hb c hc
  refine ⟨source_complex_flux_absolutelyContinuous hq hR hS hint hb hc, ?_⟩
  filter_upwards [source_flux_hasDerivAt_ae hq hR hS hint hb hc] with r hr hmem
  have hra : outerHorizon M Q < r := (lt_min hb hc).trans_le hmem.1
  apply (hr hmem).congr_deriv
  push_cast
  field_simp [ofReal_ne_zero.mpr (hp0 r hra)]
  ring

end ModeStability.AllAngular

end
