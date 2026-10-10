module

public import Mathlib
public import ModeStability.Flux.Basic
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK

/-!
# Proof implementation

`ModeStability.Provider.FluxIdentity` supplies the proof of the corresponding source-facing
theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Provider

theorem flux_identity :
    ∀ (M Q q ω : ℝ), 0 < M → |Q| < M →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ), IsRadialSolution M Q q ω R →
        HorizonCondition M Q q ω R BH → InfinityCondition M Q q ω R BI →
          (∀ r ∈ Ioi (outerHorizon M Q),
            delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im =
              -radialK (q * Q) ω (outerHorizon M Q) * ‖BH‖ ^ 2) ∧
            -radialK (q * Q) ω (outerHorizon M Q) * ‖BH‖ ^ 2 = ω * ‖BI‖ ^ 2 := by
  intro M Q q ω hM hQ R BH BI hR hH hI
  obtain ⟨C, hC⟩ := Flux.flux_const hR
  have hHor := Flux.tendsto_flux_horizon hQ hR hH
  have hInf := Flux.tendsto_flux_infinity hM hR hI
  have hconstH : Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im)
      (𝓝[>] outerHorizon M Q) (𝓝 C) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with r hr using (hC r hr).symm)
  have hconstI : Tendsto (fun r => delta M Q r * (deriv R r * (starRingEnd ℂ) (R r)).im)
      atTop (𝓝 C) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr using (hC r hr).symm)
  have h1 : C = -radialK (q * Q) ω (outerHorizon M Q) * ‖BH‖ ^ 2 :=
    tendsto_nhds_unique hconstH hHor
  have h2 : C = ω * ‖BI‖ ^ 2 := tendsto_nhds_unique hconstI hInf
  exact ⟨fun r hr => (hC r hr).trans h1, h1.symm.trans h2⟩

end ModeStability.Provider

end
