module

public import ModeStability.Exterior.Calculus
public import ModeStability.Frozen.TransformedK
public import ModeStability.Frozen.Dephase
public import ModeStability.Frozen.DephasedCurrent
public import ModeStability.Current.Dephased

/-!
# Shared facts for the endpoint currents

For the endpoint limits (2.11)–(2.15) of the spherical research notes in preparation:

* `k(x) = K(r(x)) / x²` for `x > 0` (`transformedK_eq_div`), with derivative
  `k_x = K'(r) Δ(r) / x⁴ − 2 K(r) / x³` at `r = r(x)` (`hasDerivAt_transformedK`);
* the current of the dephased function does not see the phase:
  `J[e^{iσϑ} U] = −(k/k_x) |U' + iσkU|² − Re(U' Ū)` (`dephasedCurrent_dephase_eq`).
-/

public section

open Complex Set Filter Topology

namespace ModeStability

/-- `k(x) = K(r(x)) / x²` for `x > 0`. -/
theorem transformedK_eq_div {M Q q ω : ℝ} (hQ : |Q| < M) {x : ℝ} (hx : 0 < x) :
    transformedK M Q q ω x = radialK (q * Q) ω (radiusOf M Q x) / x ^ 2 := by
  unfold transformedK
  rw [staticSolution_radiusOf hQ hx]
  field_simp

/-- `k_x = K'(r) Δ(r) / x⁴ − 2 K(r) / x³` at `r = r(x)`, `x > 0`, with `K'(r) = 2ωr − qQ`. -/
theorem hasDerivAt_transformedK {M Q q ω : ℝ} (hQ : |Q| < M) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (transformedK M Q q ω)
      ((2 * ω * radiusOf M Q x - q * Q) * delta M Q (radiusOf M Q x) / x ^ 4 -
        2 * radialK (q * Q) ω (radiusOf M Q x) / x ^ 3) x := by
  have hr := hasDerivAt_radiusOf hQ hx
  have hK : HasDerivAt (fun y => radialK (q * Q) ω (radiusOf M Q y))
      ((2 * ω * radiusOf M Q x - q * Q) * (delta M Q (radiusOf M Q x) / x ^ 2)) x := by
    have h := ((hr.pow 2).const_mul ω).sub (hr.const_mul (q * Q))
    unfold radialK
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  have h := hK.div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx.ne')
  have hev : (fun y => radialK (q * Q) ω (radiusOf M Q y) / y ^ 2) =ᶠ[𝓝 x]
      transformedK M Q q ω :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy => (transformedK_eq_div hQ hy).symm
  refine (h.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  simp only [Nat.cast_ofNat]
  field_simp
  ring

/-- `k` is continuous on `x > 0`. -/
theorem continuousOn_transformedK {M Q q ω : ℝ} (hQ : |Q| < M) :
    ContinuousOn (transformedK M Q q ω) (Ioi 0) :=
  fun _ hx => (hasDerivAt_transformedK hQ hx).continuousAt.continuousWithinAt

/-- The current of the dephased function does not see the phase:
`J[e^{iσϑ} U](x) = −(k/k_x) |U' + iσkU|² − Re(U' Ū)`. -/
theorem dephasedCurrent_dephase_eq {k : ℝ → ℝ} {U : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hk : ContinuousOn k (Ioi 0)) (σ : ℝ) {x : ℝ} (hx : 0 < x) (hU : DifferentiableAt ℝ U x) :
    dephasedCurrent k (dephase k x₀ σ U) x =
      -(k x / deriv k x) * ‖deriv U x + σ * k x * I * U x‖ ^ 2 -
        (deriv U x * (starRingEnd ℂ) (U x)).re := by
  have hdv : deriv (dephase k x₀ σ U) x =
      exp (σ * (∫ ξ in x₀..x, k ξ) * I) * (deriv U x + σ * k x * I * U x) :=
    Current.deriv_dephased hx₀ hk σ hx hU
  set θ : ℝ := σ * ∫ ξ in x₀..x, k ξ with hθ
  have he : exp (σ * (∫ ξ in x₀..x, k ξ) * I) = exp (θ * I) := by
    rw [hθ]; push_cast; ring_nf
  have hnorm : ‖exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hconj : exp (θ * I) * (starRingEnd ℂ) (exp (θ * I)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; simp
  unfold dephasedCurrent
  rw [hdv, he]
  have hv : dephase k x₀ σ U x = exp (θ * I) * U x := by
    unfold dephase; rw [← he]
  rw [hv, norm_mul, hnorm, one_mul, map_mul]
  congr 1
  have : exp (θ * I) * (deriv U x + σ * k x * I * U x) *
      ((starRingEnd ℂ) (exp (θ * I)) * (starRingEnd ℂ) (U x)) =
      (exp (θ * I) * (starRingEnd ℂ) (exp (θ * I))) *
        ((deriv U x + σ * k x * I * U x) * (starRingEnd ℂ) (U x)) := by ring
  rw [this, hconj, one_mul, add_mul, Complex.add_re]
  have : ((σ : ℂ) * k x * I * U x * (starRingEnd ℂ) (U x)).re = 0 := by
    rw [mul_assoc, Complex.mul_conj]
    simp [Complex.mul_re]
  rw [this, add_zero]

end ModeStability

end
