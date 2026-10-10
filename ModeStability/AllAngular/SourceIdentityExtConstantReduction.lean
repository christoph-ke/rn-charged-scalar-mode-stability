module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityRAux
public import ModeStability.AllAngular.SourceIdentityExtConstantCoefficients

/-!
# Constant-normalization reduction for an integrated source equation

Source: the all-angular research notes in preparation, (6.1) and (6.3).
The source flux is locally absolutely continuous, with the reduced equation
almost everywhere, so no continuity of the L² source is assumed.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-- Continuity of the radial zeroth-order coefficient on the exterior. -/
theorem sec_radialCoeff_continuousOn (M Q e ω L : ℝ) :
    ContinuousOn (fun r => radialK e ω r ^ 2 / delta M Q r - L)
      (Ioi (outerHorizon M Q)) := by
  have hk := (CoordinateCoefficients.contDiff_radialK e ω).continuous.continuousOn
    (s := Ioi (outerHorizon M Q))
  have hd := (CoordinateCoefficients.contDiff_delta M Q).continuous.continuousOn
    (s := Ioi (outerHorizon M Q))
  exact ((hk.pow 2).div hd (fun r hr =>
    (CoordinateCoefficients.delta_pos_of_lt hr).ne')).sub continuousOn_const

/-- The constant source reduction in the exact shared radial notation. -/
theorem sec_reduction {M Q e ω L : ℝ}
    (_hQ : |Q| = M) (hN : e / ω < 2 * M) {R S : ℝ → ℂ}
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
  simp only [ofReal_one, div_one, one_pow, mul_one]
  have hp : ContinuousOn (delta M Q) (Ioi (outerHorizon M Q)) :=
    (CoordinateCoefficients.contDiff_delta M Q).continuous.continuousOn
  have hp0 : ∀ r ∈ Ioi (outerHorizon M Q), delta M Q r ≠ 0 :=
    fun r hr => (CoordinateCoefficients.delta_pos_of_lt hr).ne'
  have hq := sec_radialCoeff_continuousOn M Q e ω L
  refine ⟨source_solution_contDiffOn_one hp hp0 hq hR hS hint, ?_⟩
  intro b hb c hc
  refine ⟨source_complex_flux_absolutelyContinuous hq hR hS hint hb hc, ?_⟩
  filter_upwards [source_flux_hasDerivAt_ae hq hR hS hint hb hc] with r hr hmem
  apply (hr hmem).congr_deriv
  have hd0 := ofReal_ne_zero.mpr (hp0 r ((lt_min hb hc).trans_le hmem.1))
  push_cast
  field_simp
  ring

end ModeStability.AllAngular

end
