module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition

/-!
# Complex conjugation of radial modes

the spherical research notes in preparation, p. 1: complex conjugation sends `(ω, e)` to
`(−ω, −e)`. The radial equation (1.2) has real coefficients, `K(−e, −ω) = −K(e, ω)`, so
`conj ∘ R` solves (1.2) for `(−q, −ω)` whenever `R` solves it for `(q, ω)`, and the boundary
conditions (1.3) and (1.4) are carried to the conjugate leading coefficients. This reduces
Theorem 1.1 to `ω > 0`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Main

/-- `K(−e, −ω) = −K(e, ω)`. -/
theorem radialK_neg (e ω r : ℝ) : radialK (-e) (-ω) r = -radialK e ω r := by
  unfold radialK
  ring

/-- Conjugating a complex power with positive real base conjugates the exponent. -/
theorem conj_ofReal_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ z) = (x : ℂ) ^ ((starRingEnd ℂ) z) := by
  rw [Complex.cpow_conj _ _ ?_, Complex.conj_ofReal]
  rw [Complex.arg_ofReal_of_nonneg hx.le]
  exact Real.pi_pos.ne

/-- Complex conjugation maps solutions for `(q, ω)` to solutions for `(−q, −ω)`. -/
theorem isRadialSolution_conj {M Q q ω : ℝ} {R : ℝ → ℂ} (hR : IsRadialSolution M Q q ω R) :
    IsRadialSolution M Q (-q) (-ω) (fun r => (starRingEnd ℂ) (R r)) := by
  intro r hr
  obtain ⟨hd, hder⟩ := hR r hr
  refine ⟨hd.star, ?_⟩
  have h := hder.star
  have hK : radialK (-q * Q) (-ω) r = -radialK (q * Q) ω r := by
    rw [neg_mul]
    exact radialK_neg _ _ _
  convert h using 1
  · funext s
    have hs : deriv (fun r => (starRingEnd ℂ) (R r)) s = (starRingEnd ℂ) (deriv R s) :=
      deriv.star
    rw [hs]
    change _ = (starRingEnd ℂ) _
    rw [map_mul, Complex.conj_ofReal]
  · change _ = (starRingEnd ℂ) _
    rw [map_mul, map_neg, Complex.conj_ofReal, hK, neg_sq]

/-- Abstract form of the transfer of (1.3) under conjugation, for a horizon radius `a` and a
real exponent `κ`. -/
theorem horizon_aux {a κ : ℝ} {R : ℝ → ℂ} {B : ℂ}
    (h1 : (fun r : ℝ => ((r - a : ℝ) : ℂ) ^ (I * (κ : ℂ)) * R r - B)
      =O[𝓝[>] a] (fun r => r - a))
    (h2 : deriv (fun r : ℝ => ((r - a : ℝ) : ℂ) ^ (I * (κ : ℂ)) * R r)
      =O[𝓝[>] a] (fun _ => (1 : ℝ))) :
    (fun r : ℝ => ((r - a : ℝ) : ℂ) ^ (I * ((-κ : ℝ) : ℂ)) * (starRingEnd ℂ) (R r) -
        (starRingEnd ℂ) B) =O[𝓝[>] a] (fun r => r - a) ∧
      deriv (fun r : ℝ => ((r - a : ℝ) : ℂ) ^ (I * ((-κ : ℝ) : ℂ)) * (starRingEnd ℂ) (R r))
        =O[𝓝[>] a] (fun _ => (1 : ℝ)) := by
  have key : ∀ r : ℝ, a < r →
      ((r - a : ℝ) : ℂ) ^ (I * ((-κ : ℝ) : ℂ)) * (starRingEnd ℂ) (R r) =
        (starRingEnd ℂ) (((r - a : ℝ) : ℂ) ^ (I * (κ : ℂ)) * R r) := by
    intro r hr
    rw [map_mul, conj_ofReal_cpow (sub_pos.2 hr)]
    congr 2
    simp
  have hev : ∀ᶠ r in 𝓝[>] a, a < r := self_mem_nhdsWithin
  refine ⟨?_, ?_⟩
  · refine isBigO_norm_left.1 ?_
    refine h1.norm_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [hev] with r hr
    rw [key r hr, ← map_sub, Complex.norm_conj]
  · have hd : ∀ r : ℝ, a < r →
        deriv (fun r : ℝ => ((r - a : ℝ) : ℂ) ^ (I * ((-κ : ℝ) : ℂ)) * (starRingEnd ℂ) (R r)) r =
          (starRingEnd ℂ) (deriv (fun r : ℝ => ((r - a : ℝ) : ℂ) ^ (I * (κ : ℂ)) * R r) r) := by
      intro r hr
      have hnhds : (fun r : ℝ => ((r - a : ℝ) : ℂ) ^ (I * ((-κ : ℝ) : ℂ)) *
            (starRingEnd ℂ) (R r)) =ᶠ[𝓝 r]
          fun r : ℝ => (starRingEnd ℂ) (((r - a : ℝ) : ℂ) ^ (I * (κ : ℂ)) * R r) := by
        filter_upwards [Ioi_mem_nhds hr] with s hs
        exact key s hs
      rw [hnhds.deriv_eq]
      exact deriv.star
    refine isBigO_norm_left.1 ?_
    refine h2.norm_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [hev] with r hr
    rw [hd r hr, Complex.norm_conj]

/-- Complex conjugation carries the horizon condition (1.3) for `(q, ω)` with leading
coefficient `B` to the horizon condition for `(−q, −ω)` with leading coefficient `conj B`. -/
theorem horizonCondition_conj {M Q q ω : ℝ} {R : ℝ → ℂ} {B : ℂ}
    (hH : HorizonCondition M Q q ω R B) :
    HorizonCondition M Q (-q) (-ω) (fun r => (starRingEnd ℂ) (R r)) ((starRingEnd ℂ) B) := by
  obtain ⟨h1, h2⟩ := hH
  have hK : radialK (-q * Q) (-ω) (outerHorizon M Q) / (outerHorizon M Q - innerHorizon M Q) =
      -(radialK (q * Q) ω (outerHorizon M Q) / (outerHorizon M Q - innerHorizon M Q)) := by
    rw [neg_mul, radialK_neg, neg_div]
  unfold HorizonCondition
  rw [hK]
  exact horizon_aux h1 h2

/-- Abstract form of the transfer of (1.4) under conjugation, for a real frequency `ω` and a
real phase exponent `s`. -/
theorem infinity_aux {ω s : ℝ} {R : ℝ → ℂ} {B : ℂ}
    (h1 : (fun r : ℝ => (r : ℂ) * exp (-(I * (ω : ℂ) * r)) * (r : ℂ) ^ (-(I * (s : ℂ))) * R r - B)
      =O[atTop] (fun r : ℝ => r⁻¹))
    (h2 : deriv (fun r : ℝ =>
        (r : ℂ) * exp (-(I * (ω : ℂ) * r)) * (r : ℂ) ^ (-(I * (s : ℂ))) * R r)
      =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹)) :
    (fun r : ℝ => (r : ℂ) * exp (-(I * ((-ω : ℝ) : ℂ) * r)) *
        (r : ℂ) ^ (-(I * ((-s : ℝ) : ℂ))) * (starRingEnd ℂ) (R r) - (starRingEnd ℂ) B)
        =O[atTop] (fun r : ℝ => r⁻¹) ∧
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * ((-ω : ℝ) : ℂ) * r)) *
          (r : ℂ) ^ (-(I * ((-s : ℝ) : ℂ))) * (starRingEnd ℂ) (R r))
        =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹) := by
  have key : ∀ r : ℝ, 0 < r →
      (r : ℂ) * exp (-(I * ((-ω : ℝ) : ℂ) * r)) *
          (r : ℂ) ^ (-(I * ((-s : ℝ) : ℂ))) * (starRingEnd ℂ) (R r) =
        (starRingEnd ℂ) ((r : ℂ) * exp (-(I * (ω : ℂ) * r)) *
          (r : ℂ) ^ (-(I * (s : ℂ))) * R r) := by
    intro r hr
    rw [map_mul, map_mul, map_mul, conj_ofReal_cpow hr, ← Complex.exp_conj, Complex.conj_ofReal]
    congr 3
    · simp
    · simp
  have hev : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  refine ⟨?_, ?_⟩
  · refine isBigO_norm_left.1 ?_
    refine h1.norm_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [hev] with r hr
    rw [key r hr, ← map_sub, Complex.norm_conj]
  · have hd : ∀ r : ℝ, 0 < r →
        deriv (fun r : ℝ => (r : ℂ) * exp (-(I * ((-ω : ℝ) : ℂ) * r)) *
            (r : ℂ) ^ (-(I * ((-s : ℝ) : ℂ))) * (starRingEnd ℂ) (R r)) r =
          (starRingEnd ℂ) (deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (ω : ℂ) * r)) *
            (r : ℂ) ^ (-(I * (s : ℂ))) * R r) r) := by
      intro r hr
      have hnhds : (fun r : ℝ => (r : ℂ) * exp (-(I * ((-ω : ℝ) : ℂ) * r)) *
            (r : ℂ) ^ (-(I * ((-s : ℝ) : ℂ))) * (starRingEnd ℂ) (R r)) =ᶠ[𝓝 r]
          fun r : ℝ => (starRingEnd ℂ) ((r : ℂ) * exp (-(I * (ω : ℂ) * r)) *
            (r : ℂ) ^ (-(I * (s : ℂ))) * R r) := by
        filter_upwards [Ioi_mem_nhds hr] with t ht
        exact key t ht
      rw [hnhds.deriv_eq]
      exact deriv.star
    refine isBigO_norm_left.1 ?_
    refine h2.norm_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [hev] with r hr
    rw [hd r hr, Complex.norm_conj]

/-- Complex conjugation carries the infinity condition (1.4) for `(q, ω)` with leading
coefficient `B` to the infinity condition for `(−q, −ω)` with leading coefficient `conj B`. -/
theorem infinityCondition_conj {M Q q ω : ℝ} {R : ℝ → ℂ} {B : ℂ}
    (hI : InfinityCondition M Q q ω R B) :
    InfinityCondition M Q (-q) (-ω) (fun r => (starRingEnd ℂ) (R r)) ((starRingEnd ℂ) B) := by
  obtain ⟨h1, h2⟩ := hI
  have e1 : (2 * (M : ℂ) * (ω : ℂ) - (q : ℂ) * (Q : ℂ)) = ((2 * M * ω - q * Q : ℝ) : ℂ) := by
    push_cast
    ring
  have e2 : (2 * (M : ℂ) * ((-ω : ℝ) : ℂ) - ((-q : ℝ) : ℂ) * (Q : ℂ)) =
      ((-(2 * M * ω - q * Q) : ℝ) : ℂ) := by
    push_cast
    ring
  unfold InfinityCondition
  rw [e1] at h1 h2
  rw [e2]
  exact infinity_aux h1 h2

end ModeStability.Main

end
