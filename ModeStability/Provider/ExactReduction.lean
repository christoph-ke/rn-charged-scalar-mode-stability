module

public import ModeStability.Exterior.Reduction
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.RadiusOf
public import ModeStability.Frozen.TransformedK

/-!
# Proof implementation

`ModeStability.Provider.ExactReduction` supplies the proof of the corresponding source-facing
theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Provider

theorem exact_reduction :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M →
      ∀ (R : ℝ → ℂ), IsRadialSolution M Q q ω R →
        ∀ x ∈ Ioi (0 : ℝ),
          DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x ∧
            HasDerivAt (deriv fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))
              (-((transformedK M Q q ω x ^ 2 : ℝ) : ℂ) * ((x : ℂ) * R (radiusOf M Q x))) x := by
  intro M Q q ω _ hQ R hR x hx
  -- the first derivative `U' = R(r) + g(r) · (Δ R')(r)` on `y > 0`
  have hU : ∀ y ∈ Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y))
        (R (radiusOf M Q y) + ((staticSolution M Q (radiusOf M Q y) : ℝ) : ℂ) *
          (((delta M Q (radiusOf M Q y) : ℝ) : ℂ) * deriv R (radiusOf M Q y))) y :=
    fun y hy => hasDerivAt_reducedSolution hQ hR hy
  refine ⟨(hU x hx).differentiableAt, ?_⟩
  have hx0 : 0 < x := hx
  have hra := outerHorizon_lt_radiusOf hQ hx0
  have hD : 0 < delta M Q (radiusOf M Q x) := delta_pos hQ hra
  -- the second derivative
  have h1 : HasDerivAt (fun y : ℝ => R (radiusOf M Q y))
      ((delta M Q (radiusOf M Q x) * staticSolution M Q (radiusOf M Q x) ^ 2 : ℝ) •
        deriv R (radiusOf M Q x)) x :=
    ((hR _ hra).1.hasDerivAt).scomp x (hasDerivAt_radiusOf_eq_mul_sq hQ hx0)
  have hG := ((hasDerivAt_staticSolution hQ hra).ofReal_comp).mul (hR _ hra).2
  have h2 := h1.add (hG.scomp x (hasDerivAt_radiusOf_eq_mul_sq hQ hx0))
  have hev : (deriv fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) =ᶠ[𝓝 x]
      fun y : ℝ => R (radiusOf M Q y) + ((staticSolution M Q (radiusOf M Q y) : ℝ) : ℂ) *
        (((delta M Q (radiusOf M Q y) : ℝ) : ℂ) * deriv R (radiusOf M Q y)) := by
    filter_upwards [Ioi_mem_nhds hx0] with y hy using (hU y hy).deriv
  refine (h2.congr_deriv ?_).congr_of_eventuallyEq hev
  have hDc : ((delta M Q (radiusOf M Q x) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hD.ne'
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0.ne'
  simp only [Complex.real_smul, transformedK, staticSolution_radiusOf hQ hx0]
  push_cast
  field_simp
  ring

end ModeStability.Provider

end
