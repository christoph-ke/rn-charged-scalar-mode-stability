module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.StaticSolution
public import ModeStability.Frozen.RadiusOf

/-!
# Basic facts about the subextremal exterior

Elementary properties of the horizon radii `a`, `b`, the static solution `g` of (2.1) and the
inverse coordinate map `r(x)` of (2.11) (the spherical research notes in preparation).
-/

public section

open Set

namespace ModeStability

/-- `d = a − b > 0` for subextremal parameters. -/
theorem outerHorizon_sub_innerHorizon_pos {M Q : ℝ} (hQ : |Q| < M) :
    0 < outerHorizon M Q - innerHorizon M Q := by
  have h : 0 < M ^ 2 - Q ^ 2 := by
    have := sq_lt_sq' (abs_lt.1 hQ).1 (abs_lt.1 hQ).2
    linarith
  unfold outerHorizon innerHorizon
  have := Real.sqrt_pos.2 h
  linarith

namespace Exterior

/-- With `d = a − b > 0` and `r = a + d/(e^{d/x} − 1)`, one has `d⁻¹ log((r − b)/(r − a)) = 1/x`. -/
theorem log_ratio_radius {a b x : ℝ} (hd : 0 < a - b) (hx : 0 < x) :
    1 / (a - b) * Real.log ((a + (a - b) / (Real.exp ((a - b) / x) - 1) - b) /
      (a + (a - b) / (Real.exp ((a - b) / x) - 1) - a)) = 1 / x := by
  have hE : 1 < Real.exp ((a - b) / x) := Real.one_lt_exp_iff.2 (div_pos hd hx)
  have hE1 : Real.exp ((a - b) / x) - 1 ≠ 0 := (sub_pos.2 hE).ne'
  have hratio : (a + (a - b) / (Real.exp ((a - b) / x) - 1) - b) /
      (a + (a - b) / (Real.exp ((a - b) / x) - 1) - a) = Real.exp ((a - b) / x) := by
    set E := Real.exp ((a - b) / x)
    have hden : a + (a - b) / (E - 1) - a = (a - b) / (E - 1) := by ring
    have hnum : a + (a - b) / (E - 1) - b = (a - b) * E / (E - 1) := by
      field_simp
      ring
    rw [hden, hnum]
    field_simp
  rw [hratio, Real.log_exp]
  field_simp

/-- Conversely, `a + d/(e^{d/x} − 1) = r` for `x = 1/g(r)`, `r > a`. -/
theorem radius_log_ratio {a b r : ℝ} (hd : 0 < a - b) (hr : a < r) :
    a + (a - b) / (Real.exp ((a - b) / (1 / (1 / (a - b) * Real.log ((r - b) / (r - a))))) - 1) =
      r := by
  have hra : 0 < r - a := sub_pos.2 hr
  have hrb : 0 < r - b := by linarith
  have hq : 0 < (r - b) / (r - a) := div_pos hrb hra
  have hx : (a - b) / (1 / (1 / (a - b) * Real.log ((r - b) / (r - a)))) =
      Real.log ((r - b) / (r - a)) := by
    field_simp
  rw [hx, Real.exp_log hq]
  have h1 : (r - b) / (r - a) - 1 = (a - b) / (r - a) := by
    field_simp
    ring
  rw [h1]
  field_simp
  ring

end Exterior

/-- `g(r(x)) = 1/x` for `x > 0`. -/
theorem staticSolution_radiusOf {M Q : ℝ} (hQ : |Q| < M) {x : ℝ} (hx : 0 < x) :
    staticSolution M Q (radiusOf M Q x) = 1 / x :=
  Exterior.log_ratio_radius (outerHorizon_sub_innerHorizon_pos hQ) hx

/-- `r(1/g(r)) = r` for `r > a`. -/
theorem radiusOf_one_div_staticSolution {M Q : ℝ} (hQ : |Q| < M) {r : ℝ}
    (hr : outerHorizon M Q < r) : radiusOf M Q (1 / staticSolution M Q r) = r :=
  Exterior.radius_log_ratio (outerHorizon_sub_innerHorizon_pos hQ) hr

/-- `g(r) > 0` for `r > a`. -/
theorem staticSolution_pos {M Q : ℝ} (hQ : |Q| < M) {r : ℝ} (hr : outerHorizon M Q < r) :
    0 < staticSolution M Q r := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hra : 0 < r - outerHorizon M Q := sub_pos.2 hr
  have hlog : 0 < Real.log ((r - innerHorizon M Q) / (r - outerHorizon M Q)) :=
    Real.log_pos ((one_lt_div hra).2 (by linarith))
  unfold staticSolution
  positivity

/-- `r(x) > a` for `x > 0`. -/
theorem outerHorizon_lt_radiusOf {M Q : ℝ} (hQ : |Q| < M) {x : ℝ} (hx : 0 < x) :
    outerHorizon M Q < radiusOf M Q x := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hE : 1 < Real.exp ((outerHorizon M Q - innerHorizon M Q) / x) :=
    Real.one_lt_exp_iff.2 (div_pos hd hx)
  unfold radiusOf
  have := div_pos hd (sub_pos.2 hE)
  linarith

end ModeStability

end
