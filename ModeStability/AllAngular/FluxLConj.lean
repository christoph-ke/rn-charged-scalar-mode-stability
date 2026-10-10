module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK

/-!
# Complex conjugation in the Θ-form encodings

Source: the all-angular research notes in preparation, p. 2, after (1.6). The radial equation
(1.2) with the angular term has real coefficients and
`K(−e, −ω) = −K(e, ω)`, so:

* `radialEquation_conj_L`: `conj ∘ R` solves `(ΔR')' + (K²/Δ − L)R = 0` for `(−e, −ω, L)`
  whenever `R` solves it for `(e, ω, L)`;
* `phase_conj_L`: if `Θ' = K_{e,ω}/Δ` then `(−Θ)' = K_{−e,−ω}/Δ`;
* `horizonTheta_conj_L`, `infinityTheta_conj_L`: the Θ-form horizon condition (1.4) and infinity
  condition (1.5) for `(Θ, R, B)` give them for `(−Θ, conj ∘ R, conj B)`;
* `bounded_conj_L`, `radialK_neg_eq_zero_iff`: the bounded clause at an extremal synchronized
  horizon and the synchronization test `K(a) = 0` are invariant.

The landed `L = 0` analogues with complex powers are in `ModeStability.Main.Conjugation`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- `K(−e, −ω) = −K(e, ω)`. -/
theorem fl_radialK_neg (e ω r : ℝ) : radialK (-e) (-ω) r = -radialK e ω r := by
  unfold radialK
  ring

/-- The synchronization test `K(r) = 0` is invariant under `(e, ω) ↦ (−e, −ω)`. -/
theorem radialK_neg_eq_zero_iff (e ω r : ℝ) : radialK (-e) (-ω) r = 0 ↔ radialK e ω r = 0 := by
  rw [fl_radialK_neg, neg_eq_zero]

/-- Complex conjugation maps solutions of `(ΔR')' + (K²/Δ − L)R = 0` for `(e, ω, L)` to solutions
for `(−e, −ω, L)`. -/
theorem radialEquation_conj_L {M Q e ω L : ℝ} {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ (fun s => (starRingEnd ℂ) (R s)) r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv (fun s => (starRingEnd ℂ) (R s)) s)
        (-(((radialK (-e) (-ω) r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * (starRingEnd ℂ) (R r)) r := by
  intro r hr
  obtain ⟨hd, hder⟩ := hR r hr
  refine ⟨hd.star, ?_⟩
  have h := hder.star
  convert h using 1
  · funext s
    have hs : deriv (fun r => (starRingEnd ℂ) (R r)) s = (starRingEnd ℂ) (deriv R s) :=
      deriv.star
    rw [hs]
    change _ = (starRingEnd ℂ) _
    rw [map_mul, Complex.conj_ofReal]
  · change _ = (starRingEnd ℂ) _
    rw [map_mul, map_neg, Complex.conj_ofReal, fl_radialK_neg, neg_sq]

/-- If `Θ' = K_{e,ω}/Δ` on the exterior, then `(−Θ)' = K_{−e,−ω}/Δ` there. -/
theorem phase_conj_L {M Q e ω : ℝ} {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r) :
    ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt (fun s => -Θ s) (radialK (-e) (-ω) r / delta M Q r) r := by
  intro r hr
  refine (hΘ r hr).neg.congr_deriv ?_
  rw [fl_radialK_neg, neg_div]

/-- Big-O bounds with real comparison function pass to the complex conjugate. -/
theorem fl_isBigO_conj {l : Filter ℝ} {f : ℝ → ℂ} {g : ℝ → ℝ} (h : f =O[l] g) :
    (fun r => (starRingEnd ℂ) (f r)) =O[l] g := by
  refine isBigO_norm_left.1 ?_
  simpa only [Complex.norm_conj] using h.norm_left

/-- `e^{i(−Θ)} conj R = conj(e^{iΘ} R)`. -/
theorem fl_horizon_twist_conj (θ : ℝ) (z : ℂ) :
    exp (I * ((-θ : ℝ) : ℂ)) * (starRingEnd ℂ) z = (starRingEnd ℂ) (exp (I * (θ : ℂ)) * z) := by
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 2
  push_cast
  ring

/-- `r e^{−i(−Θ)} conj R = conj(r e^{−iΘ} R)`. -/
theorem fl_infinity_twist_conj (r θ : ℝ) (z : ℂ) :
    (r : ℂ) * exp (-(I * ((-θ : ℝ) : ℂ))) * (starRingEnd ℂ) z =
      (starRingEnd ℂ) ((r : ℂ) * exp (-(I * (θ : ℂ))) * z) := by
  rw [map_mul, map_mul, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
    Complex.conj_ofReal]
  congr 3
  push_cast
  ring

/-- Complex conjugation carries the Θ-form horizon condition (1.4) for `(Θ, R, B)` to the one for
`(−Θ, conj ∘ R, conj B)`. -/
theorem horizonTheta_conj_L {a : ℝ} {Θ : ℝ → ℝ} {R : ℝ → ℂ} {B : ℂ}
    (hH1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - B) =O[𝓝[>] a] (fun r => r - a))
    (hH2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) =O[𝓝[>] a] (fun _ => (1 : ℝ))) :
    (fun r : ℝ => exp (I * ((-Θ r : ℝ) : ℂ)) * (starRingEnd ℂ) (R r) - (starRingEnd ℂ) B)
        =O[𝓝[>] a] (fun r => r - a) ∧
      deriv (fun r : ℝ => exp (I * ((-Θ r : ℝ) : ℂ)) * (starRingEnd ℂ) (R r))
        =O[𝓝[>] a] (fun _ => (1 : ℝ)) := by
  have key : (fun r : ℝ => exp (I * ((-Θ r : ℝ) : ℂ)) * (starRingEnd ℂ) (R r)) =
      fun r : ℝ => (starRingEnd ℂ) (exp (I * (Θ r : ℂ)) * R r) := by
    funext r
    exact fl_horizon_twist_conj _ _
  refine ⟨?_, ?_⟩
  · have h := fl_isBigO_conj hH1
    refine h.congr_left fun r => ?_
    rw [map_sub, ← fl_horizon_twist_conj]
  · have hd : deriv (fun r : ℝ => (starRingEnd ℂ) (exp (I * (Θ r : ℂ)) * R r)) =
        fun r => (starRingEnd ℂ) (deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) r) :=
      funext fun r => deriv.star
    rw [key, hd]
    exact fl_isBigO_conj hH2

/-- Complex conjugation carries the Θ-form infinity condition (1.5) for `(Θ, R, B)` to the one for
`(−Θ, conj ∘ R, conj B)`. -/
theorem infinityTheta_conj_L {Θ : ℝ → ℝ} {R : ℝ → ℂ} {B : ℂ}
    (hI1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r - B)
      =O[atTop] (fun r : ℝ => r⁻¹))
    (hI2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    (fun r : ℝ => (r : ℂ) * exp (-(I * ((-Θ r : ℝ) : ℂ))) * (starRingEnd ℂ) (R r) -
        (starRingEnd ℂ) B) =O[atTop] (fun r : ℝ => r⁻¹) ∧
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * ((-Θ r : ℝ) : ℂ))) * (starRingEnd ℂ) (R r))
        =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹) := by
  have key : (fun r : ℝ => (r : ℂ) * exp (-(I * ((-Θ r : ℝ) : ℂ))) * (starRingEnd ℂ) (R r)) =
      fun r : ℝ => (starRingEnd ℂ) ((r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) := by
    funext r
    exact fl_infinity_twist_conj _ _ _
  refine ⟨?_, ?_⟩
  · have h := fl_isBigO_conj hI1
    refine h.congr_left fun r => ?_
    rw [map_sub, ← fl_infinity_twist_conj]
  · have hd : deriv (fun r : ℝ => (starRingEnd ℂ) ((r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r)) =
        fun r => (starRingEnd ℂ) (deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * R r) r) :=
      funext fun r => deriv.star
    rw [key, hd]
    exact fl_isBigO_conj hI2

/-- The bounded clause at an extremal synchronized horizon passes to `conj ∘ R`. -/
theorem bounded_conj_L {a : ℝ} {R : ℝ → ℂ}
    (hbdd : (fun r => R r) =O[𝓝[>] a] (fun _ => (1 : ℝ))) :
    (fun r => (starRingEnd ℂ) (R r)) =O[𝓝[>] a] (fun _ => (1 : ℝ)) :=
  fl_isBigO_conj hbdd

end ModeStability.AllAngular

end
