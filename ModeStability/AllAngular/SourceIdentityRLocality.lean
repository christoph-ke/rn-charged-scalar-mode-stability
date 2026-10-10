module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityRSubReciprocalReduction
public import ModeStability.AllAngular.HorizonLimitsL
public import ModeStability.AllAngular.InfinityLimitsL

/-!+# Locality of the source current at the physical endpoints

Source: the all-angular research notes in preparation, pp. 7–8.
Outside the compact source support the Green solution is a homogeneous
solution. The current depends only on the local first jet of the amplitude,
so its endpoint limits transfer without a homogeneous equation for the
Green solution on the whole exterior.
-/

public section

open Complex Set Filter Topology Asymptotics

namespace ModeStability.AllAngular

/-- Equality on an open set transfers both the amplitude and its derivative
in the phase-free current. No differential equation is needed. -/
theorem source_current_eqOn {s : Set ℝ} (hs : IsOpen s) {U V : ℝ → ℂ}
    (h : EqOn U V s) (f : ℝ → ℝ) (σ : ℝ) :
    EqOn (fun x => -(f x / deriv f x) * ‖deriv U x + σ * f x * I * U x‖ ^ 2 -
      (deriv U x * (starRingEnd ℂ) (U x)).re)
      (fun x => -(f x / deriv f x) * ‖deriv V x + σ * f x * I * V x‖ ^ 2 -
      (deriv V x * (starRingEnd ℂ) (V x)).re) s := by
  intro x hx
  have hd : deriv U x = deriv V x :=
    (eventuallyEq_of_mem (hs.mem_nhds hx) h).deriv_eq
  dsimp only
  rw [hd, h hx]

private theorem sr_reciprocal_amplitude_eqOn {M Q : ℝ} (_hQ : |Q| < M)
    {s : Set ℝ} (_hs : IsOpen s) {R T : ℝ → ℂ} (h : EqOn R T s) :
    EqOn (fun x : ℝ => (x : ℂ) * R (radiusOf M Q x))
      (fun x : ℝ => (x : ℂ) * T (radiusOf M Q x))
      {x | 0 < x ∧ radiusOf M Q x ∈ s} := by
  intro x hx
  dsimp only
  rw [h hx.2]

private theorem sr_reciprocal_preimage_open {M Q : ℝ} (hQ : |Q| < M)
    {s : Set ℝ} (hs : IsOpen s) :
    IsOpen {x | 0 < x ∧ radiusOf M Q x ∈ s} := by
  have hc : ContinuousOn (radiusOf M Q) (Ioi 0) :=
    (reciprocal_contDiffOn hQ).continuousOn
  exact hc.isOpen_inter_preimage isOpen_Ioi hs

/-- A radial equality near the horizon transfers the reciprocal current limit
from a homogeneous endpoint piece to the Green amplitude. -/
theorem source_sub_reciprocal_horizon_locality {M Q b : ℝ} (hQ : |Q| < M)
    (hb : outerHorizon M Q < b) {R T : ℝ → ℂ}
    (h : EqOn R T (Ioo (outerHorizon M Q) b)) {f : ℝ → ℝ} {σ C : ℝ}
    (ht : Tendsto (fun x => -(f x / deriv f x) *
      ‖deriv (fun y : ℝ => (y : ℂ) * T (radiusOf M Q y)) x +
        σ * f x * I * ((x : ℂ) * T (radiusOf M Q x))‖ ^ 2 -
      (deriv (fun y : ℝ => (y : ℂ) * T (radiusOf M Q y)) x *
        (starRingEnd ℂ) ((x : ℂ) * T (radiusOf M Q x))).re)
      (𝓝[>] 0) (𝓝 C)) :
    Tendsto (fun x => -(f x / deriv f x) *
      ‖deriv (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x +
        σ * f x * I * ((x : ℂ) * R (radiusOf M Q x))‖ ^ 2 -
      (deriv (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x *
        (starRingEnd ℂ) ((x : ℂ) * R (radiusOf M Q x))).re)
      (𝓝[>] 0) (𝓝 C) := by
  apply ht.congr'
  have he := source_current_eqOn (sr_reciprocal_preimage_open hQ isOpen_Ioo)
    (sr_reciprocal_amplitude_eqOn hQ isOpen_Ioo h) f σ
  filter_upwards [self_mem_nhdsWithin,
    (Endpoint.tendsto_radiusOf_nhdsGT hQ).eventually (Ioo_mem_nhdsGT hb)] with x hx hr
  exact (he ⟨hx, hr⟩).symm

/-- A radial equality beyond the support transfers the reciprocal infinity
current limit, including the interface `2Mω = e`. -/
theorem source_sub_reciprocal_infinity_locality {M Q b : ℝ} (hQ : |Q| < M)
    {R T : ℝ → ℂ} (h : EqOn R T (Ioi b)) {f : ℝ → ℝ} {σ C : ℝ}
    (ht : Tendsto (fun x => -(f x / deriv f x) *
      ‖deriv (fun y : ℝ => (y : ℂ) * T (radiusOf M Q y)) x +
        σ * f x * I * ((x : ℂ) * T (radiusOf M Q x))‖ ^ 2 -
      (deriv (fun y : ℝ => (y : ℂ) * T (radiusOf M Q y)) x *
        (starRingEnd ℂ) ((x : ℂ) * T (radiusOf M Q x))).re) atTop (𝓝 C)) :
    Tendsto (fun x => -(f x / deriv f x) *
      ‖deriv (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x +
        σ * f x * I * ((x : ℂ) * R (radiusOf M Q x))‖ ^ 2 -
      (deriv (fun y : ℝ => (y : ℂ) * R (radiusOf M Q y)) x *
        (starRingEnd ℂ) ((x : ℂ) * R (radiusOf M Q x))).re) atTop (𝓝 C) := by
  apply ht.congr'
  have he := source_current_eqOn (sr_reciprocal_preimage_open hQ isOpen_Ioi)
    (sr_reciprocal_amplitude_eqOn hQ isOpen_Ioi h) f σ
  filter_upwards [Ioi_mem_atTop (0 : ℝ),
    (Infinity.tendsto_radiusOf_atTop hQ).eventually (Ioi_mem_atTop b)] with x hx hr
  exact (he ⟨hx, hr⟩).symm

end ModeStability.AllAngular

end
