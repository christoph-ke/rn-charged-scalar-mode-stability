module

public import Mathlib
public import ModeStability.AllAngular.Prop61Interface
public import ModeStability.AllAngular.SourceIdentityRAux
public import ModeStability.AllAngular.CoordinateCoefficientsExtremal
public import ModeStability.AllAngular.NormalizationFacts

/-!
# Extremal reciprocal normalization for the source identity

Source: the all-angular research notes in preparation, identity (6.3),
with `|Q| = M`, `g = h = 1/(r-M)` and `x = r-M`.
The radial coordinate density is exactly one on the exterior.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

noncomputable def ser_g (M : ℝ) : ℝ → ℝ := fun r => 1 / (r - M)

/-- The frozen normalization in the extremal reciprocal system. -/
theorem ser_normalization {M Q e ω : ℝ} (hQ : |Q| = M) (hN : 2 * M ≤ e / ω) :
    normalizationG M Q e ω = ser_g M := by
  have hδ : M ^ 2 - Q ^ 2 = 0 := by rw [← sq_abs Q, hQ, sub_self]
  rw [NormalizationFacts.normalizationG_eq_static (not_lt.mpr hN),
    NormalizationFacts.staticSolutionAA_eq_extremal (by rw [hδ]; exact lt_irrefl 0)]
  rfl

theorem ser_g_pos {M Q r : ℝ} (_hQ : |Q| = M) (hr : outerHorizon M Q < r) :
    0 < ser_g M r := one_div_pos.mpr (NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr)

theorem ser_g_smooth {M Q r : ℝ} (_hQ : |Q| = M) (hr : outerHorizon M Q < r) :
    ContDiffAt ℝ 2 (ser_g M) r :=
  contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const)
    (NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr).ne'

theorem ser_g_derivative {M Q r : ℝ} (hQ : |Q| = M) (hr : outerHorizon M Q < r) :
    HasDerivAt (ser_g M) (-1 / delta M Q r) r := by
  have h := (hasDerivAt_const r (1 : ℝ)).div ((hasDerivAt_id' r).sub_const M)
    (NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr).ne'
  refine h.congr_deriv ?_
  rw [delta_of_abs_eq hQ]
  ring

/-- `dr/dx = Δg² = 1` on the extremal exterior. -/
theorem ser_density {M Q e ω r : ℝ} (hQ : |Q| = M) (hN : 2 * M ≤ e / ω)
    (hr : outerHorizon M Q < r) : delta M Q r * normalizationG M Q e ω r ^ 2 = 1 := by
  rw [ser_normalization hQ hN, delta_of_abs_eq hQ]
  dsimp [ser_g]
  field_simp [(NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr).ne']

end ModeStability.AllAngular

end
