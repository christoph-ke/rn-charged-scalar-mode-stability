module

public import ModeStability.Exterior.Basic
public import ModeStability.Frozen.Delta

/-!
# Calculus on the subextremal exterior

Derivative formulas for the objects of Lemma 2.1 (the spherical research notes in preparation,
(2.1)-(2.2), (2.11)): for `r > a`

* `Δ(r) > 0` (`delta_pos`);
* `g'(r) = -1/Δ(r)` (`hasDerivAt_staticSolution`), the derivative form of (2.1);

and for `x > 0`

* `r'(x) = Δ(r(x)) / x²` (`hasDerivAt_radiusOf`), equivalently `r' = Δ g²` at `r = r(x)`
  (`hasDerivAt_radiusOf_eq_mul_sq`), the derivative form of (2.2).
-/

public section

open Set

namespace ModeStability

/-- `Δ(r) > 0` for `r > a`. -/
theorem delta_pos {M Q : ℝ} (hQ : |Q| < M) {r : ℝ} (hr : outerHorizon M Q < r) :
    0 < delta M Q r := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  unfold delta
  have h1 : 0 < r - outerHorizon M Q := sub_pos.2 hr
  have h2 : 0 < r - innerHorizon M Q := by linarith
  positivity

/-- The derivative form of (2.1): `g'(r) = -1/Δ(r)` for `r > a`. -/
theorem hasDerivAt_staticSolution {M Q : ℝ} (hQ : |Q| < M) {r : ℝ}
    (hr : outerHorizon M Q < r) :
    HasDerivAt (staticSolution M Q) (-1 / delta M Q r) r := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hra : 0 < r - outerHorizon M Q := sub_pos.2 hr
  have hrb : 0 < r - innerHorizon M Q := by linarith
  have h1 : HasDerivAt (fun s : ℝ => s - innerHorizon M Q) 1 r :=
    (hasDerivAt_id r).sub_const _
  have h2 : HasDerivAt (fun s : ℝ => s - outerHorizon M Q) 1 r :=
    (hasDerivAt_id r).sub_const _
  have h3 := (h1.div h2 hra.ne').log (div_pos hrb hra).ne'
  have h4 := h3.const_mul (1 / (outerHorizon M Q - innerHorizon M Q))
  have hfun : staticSolution M Q = fun s => 1 / (outerHorizon M Q - innerHorizon M Q) *
      Real.log ((s - innerHorizon M Q) / (s - outerHorizon M Q)) := rfl
  rw [hfun]
  refine h4.congr_deriv ?_
  simp only [Pi.div_apply]
  unfold delta
  field_simp
  ring

/-- The derivative form of (2.2): `r'(x) = Δ(r(x)) / x²` for `x > 0`. -/
theorem hasDerivAt_radiusOf {M Q : ℝ} (hQ : |Q| < M) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (radiusOf M Q) (delta M Q (radiusOf M Q x) / x ^ 2) x := by
  have hd := outerHorizon_sub_innerHorizon_pos hQ
  have hE : 1 < Real.exp ((outerHorizon M Q - innerHorizon M Q) / x) :=
    Real.one_lt_exp_iff.2 (div_pos hd hx)
  have hE1 : Real.exp ((outerHorizon M Q - innerHorizon M Q) / x) - 1 ≠ 0 := (sub_pos.2 hE).ne'
  have h1 : HasDerivAt (fun y : ℝ => (outerHorizon M Q - innerHorizon M Q) / y)
      ((0 * x - (outerHorizon M Q - innerHorizon M Q) * 1) / x ^ 2) x :=
    (hasDerivAt_const x _).div (hasDerivAt_id x) hx.ne'
  have h2 := (h1.exp).sub_const 1
  have h3 := (hasDerivAt_const x (outerHorizon M Q - innerHorizon M Q)).div h2 hE1
  have h4 := h3.const_add (outerHorizon M Q)
  have hfun : radiusOf M Q = fun y => outerHorizon M Q + (outerHorizon M Q - innerHorizon M Q) /
      (Real.exp ((outerHorizon M Q - innerHorizon M Q) / y) - 1) := rfl
  rw [hfun]
  refine h4.congr_deriv ?_
  beta_reduce
  unfold delta
  field_simp
  ring

/-- `r'(x) = Δ(r(x)) g(r(x))²` for `x > 0`. -/
theorem hasDerivAt_radiusOf_eq_mul_sq {M Q : ℝ} (hQ : |Q| < M) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (radiusOf M Q)
      (delta M Q (radiusOf M Q x) * staticSolution M Q (radiusOf M Q x) ^ 2) x := by
  have h := hasDerivAt_radiusOf hQ hx
  rw [staticSolution_radiusOf hQ hx]
  convert h using 1
  field_simp

end ModeStability

end
