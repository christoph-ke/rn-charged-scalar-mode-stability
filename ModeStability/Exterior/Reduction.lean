module

public import ModeStability.Exterior.Calculus
public import ModeStability.Frozen.IsRadialSolution

/-!
# The first derivative in the static transformation

For a solution `R` of (1.2) and `U(y) = y R(r(y))` (Lemma 2.1 of
the spherical research notes in preparation), `U' = R(r) + g(r) · (Δ R')(r)` at `r = r(y)`,
`y > 0`. This is the identity `P U_r = U_x` used in the proof of Lemma 2.1 and in (2.19).
-/

public section

open Set

namespace ModeStability

/-- `U' = R(r) + g(r) · (Δ R')(r)` for `U(y) = y R(r(y))`, `y > 0`. -/
theorem hasDerivAt_reducedSolution {M Q q ω : ℝ} (hQ : |Q| < M) {R : ℝ → ℂ}
    (hR : IsRadialSolution M Q q ω R) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))
      (R (radiusOf M Q y) + ((staticSolution M Q (radiusOf M Q y) : ℝ) : ℂ) *
        (((delta M Q (radiusOf M Q y) : ℝ) : ℂ) * deriv R (radiusOf M Q y))) y := by
  have hra := outerHorizon_lt_radiusOf hQ hy
  have h1 : HasDerivAt (fun y : ℝ => R (radiusOf M Q y))
      ((delta M Q (radiusOf M Q y) * staticSolution M Q (radiusOf M Q y) ^ 2 : ℝ) •
        deriv R (radiusOf M Q y)) y :=
    ((hR _ hra).1.hasDerivAt).scomp y (hasDerivAt_radiusOf_eq_mul_sq hQ hy)
  have h2 := (hasDerivAt_id' y).ofReal_comp.mul h1
  refine h2.congr_deriv ?_
  rw [Complex.real_smul, staticSolution_radiusOf hQ hy]
  have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  push_cast
  field_simp

end ModeStability

end
