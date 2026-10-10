module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityRAux
public import ModeStability.AllAngular.CoordinateIntervals
public import ModeStability.AllAngular.NormalizationFacts

/-!
# The `r` measure in the subextremal reciprocal source identity

Source: the all-angular research notes in preparation, identity (6.3),
and (2.2): `x = 1/h`, `dx = dr/(Δg²)`. These change-of-variables lemmas
apply to arbitrary measurable subsets of the exterior, including the three
bulk regions and the compact source interval. No integrability or regularity
of the integrand is needed for the lower Lebesgue integral formula.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-- In the subextremal reciprocal system the frozen normalization is `h`. -/
theorem source_sub_reciprocal_normalization {M Q e ω : ℝ}
    (hQ : |Q| < M) (hN : 2 * M ≤ e / ω) :
    normalizationG M Q e ω = staticSolution M Q := by
  have hδ : 0 < M ^ 2 - Q ^ 2 := by
    have := sq_lt_sq' (abs_lt.mp hQ).1 (abs_lt.mp hQ).2
    linarith
  rw [NormalizationFacts.normalizationG_eq_static (not_lt.mpr hN),
    NormalizationFacts.staticSolutionAA_eq_staticSolution hδ]

end ModeStability.AllAngular

end
