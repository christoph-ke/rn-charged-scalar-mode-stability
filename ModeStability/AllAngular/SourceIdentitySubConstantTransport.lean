module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentitySubConstantCoefficients
public import ModeStability.AllAngular.CoordinateIntervals
public import ModeStability.AllAngular.HorizonLimitsL
public import ModeStability.AllAngular.InfinityLimitsL
public import ModeStability.AllAngular.SourceIdentityRRegions

/-!
# Constant-coordinate currents and endpoint filters

Source: the all-angular research notes in preparation, pp. 7–8.
The landed endpoint limits use the reflected coordinate `y = h`. Its
frequency and amplitude derivative are the negatives of the corresponding
quantities for `x = −h`; its current is consequently the negative radial current.
-/

public section

open Complex Set Filter Topology

namespace ModeStability.AllAngular

open CoordinateCoefficients

/-- The reflected coordinate tends to infinity at the radial horizon. -/
theorem ssc_coordinate_horizon {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (staticSolution M Q) (𝓝[>] (outerHorizon M Q)) atTop := by
  apply tendsto_atTop.mpr
  intro b
  let c := max b 1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  have hr := outerHorizon_lt_radiusOf hQ (one_div_pos.mpr hc)
  filter_upwards [Ioo_mem_nhdsGT hr] with r hra
  have hi := constant_inverse hQ hra.1
  have hlt : c < staticSolution M Q r :=
    ((constant_strictAntiOn hQ).lt_iff_gt hi.1 hc).mp (by rw [hi.2]; exact hra.2)
  exact (le_max_left b 1).trans hlt.le

/-- The reflected coordinate tends to zero from the right at radial infinity. -/
theorem ssc_coordinate_infinity {M Q : ℝ} (hQ : |Q| < M) :
    Tendsto (staticSolution M Q) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_order.mpr ⟨?_, ?_⟩, ?_⟩
  · intro b hb
    filter_upwards [Ioi_mem_atTop (outerHorizon M Q)] with r hr
    exact hb.trans (staticSolution_pos hQ hr)
  · intro b hb
    filter_upwards [Ioi_mem_atTop (max (outerHorizon M Q) (radiusOf M Q (1 / b)))] with r hr
    have hi := constant_inverse hQ ((le_max_left _ _).trans_lt hr)
    exact ((constant_strictAntiOn hQ).lt_iff_gt hb hi.1).mp (by
      rw [hi.2]
      exact (le_max_right _ _).trans_lt hr)
  · filter_upwards [Ioi_mem_atTop (outerHorizon M Q)] with r hr
    exact staticSolution_pos hQ hr

/-- Reflection transports the phase-free current to its negative radial expression. -/
theorem ssc_current_jet {M Q e ω L σ : ℝ}
    (hQ : |Q| < M) (hN : e / ω < 2 * M) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    {y : ℝ} (hy : 0 < y)
    (hf : ContDiffAt ℝ 2 (effectiveK M Q e ω L) (radiusOf M Q (1 / y))) :
    let f : ℝ → ℝ := fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
      Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
        L * delta M Q (radiusOf M Q (1 / t))))
    let A := fun t : ℝ => R (radiusOf M Q (1 / t))
    let g := normalizationG M Q e ω
    let U := fun r => R r / (g r : ℂ)
    let V := fun r => ((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r
    let kh := effectiveK M Q e ω L
    let fx := xDeriv M Q g kh
    (-(f y / deriv f y) * ‖deriv A y + σ * f y * I * A y‖ ^ 2 -
        (deriv A y * (starRingEnd ℂ) (A y)).re =
      -(-(kh (radiusOf M Q (1 / y)) / fx (radiusOf M Q (1 / y))) *
        ‖V (radiusOf M Q (1 / y)) + σ * kh (radiusOf M Q (1 / y)) * I *
          U (radiusOf M Q (1 / y))‖ ^ 2 -
        (V (radiusOf M Q (1 / y)) * (starRingEnd ℂ) (U (radiusOf M Q (1 / y)))).re)) := by
  dsimp only
  have hg := NormalizationFacts.normalizationG_eq_one (Q := Q) hN
  have hr := outerHorizon_lt_radiusOf hQ (one_div_pos.mpr hy)
  have he : (fun t => -((SignType.sign (radialK e ω (radiusOf M Q (1 / t))) : ℝ) *
      Real.sqrt (radialK e ω (radiusOf M Q (1 / t)) ^ 2 -
        L * delta M Q (radiusOf M Q (1 / t))))) =
      fun t => -effectiveK M Q e ω L (radiusOf M Q (1 / t)) := by
    funext t
    simp only [effectiveK, hg, one_pow, mul_one]
  have hdf := ((hf.differentiableAt (by norm_num)).hasDerivAt.comp y
    (hasDerivAt_radiusOf_one_div hQ hy)).const_mul (-1 : ℝ)
  have hdA := (hR _ hr).hasDerivAt.scomp y (hasDerivAt_radiusOf_one_div hQ hy)
  have hdF : HasDerivAt (fun t => -effectiveK M Q e ω L (radiusOf M Q (1 / t)))
      (-(deriv (effectiveK M Q e ω L) (radiusOf M Q (1 / y)) *
        -delta M Q (radiusOf M Q (1 / y)))) y := by
    simpa only [Function.comp_def, neg_one_mul] using hdf
  have hdA' : HasDerivAt (fun t => R (radiusOf M Q (1 / t)))
      (-delta M Q (radiusOf M Q (1 / y)) • deriv R (radiusOf M Q (1 / y))) y := hdA
  have he0 := congrFun he y
  rw [he, he0, hdF.deriv, hdA'.deriv, hg]
  simp only [one_pow, mul_one, ofReal_one, div_one, xDeriv,
    Complex.real_smul, ofReal_neg, mul_neg, neg_mul, ← neg_add]
  rw [norm_neg]
  simp only [neg_div, neg_neg, neg_mul, neg_re]
  ring

/-- Radial equality on an open set transfers the current, including its first jet. -/
theorem ssc_current_eqOn {s : Set ℝ} (hs : IsOpen s) {R T : ℝ → ℂ}
    (h : EqOn R T s) (d f fx : ℝ → ℝ) (σ : ℝ) :
    EqOn (fun r => -(f r / fx r) * ‖(d r : ℂ) * deriv R r + σ * f r * I * R r‖ ^ 2 -
      ((d r : ℂ) * deriv R r * (starRingEnd ℂ) (R r)).re)
      (fun r => -(f r / fx r) * ‖(d r : ℂ) * deriv T r + σ * f r * I * T r‖ ^ 2 -
      ((d r : ℂ) * deriv T r * (starRingEnd ℂ) (T r)).re) s := by
  intro r hr
  have hd := (eventuallyEq_of_mem (hs.mem_nhds hr) h).deriv_eq
  dsimp only
  rw [hd, h hr]

end ModeStability.AllAngular

end
