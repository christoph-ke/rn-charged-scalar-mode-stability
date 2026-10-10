module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.AllAngular.StaticSolutionAA
public import ModeStability.Frozen.AllAngular.NormalizationG
public import ModeStability.Frozen.AllAngular.XDeriv
public import ModeStability.Frozen.AllAngular.CommonGeometry
public import ModeStability.AllAngular.ScalarPositivity
public import ModeStability.AllAngular.NormalizationFacts

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.ScalarPositivity` supplies the proof of the corresponding
source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Set Filter Topology

namespace ModeStability.Provider.AllAngular

theorem scalar_positivity :
    ∀ (M Q e ω : ℝ), 0 < M → |Q| ≤ M → 0 < ω → ∀ (r₀ : ℝ), r₀ = e / ω →
      ModeStability.outerHorizon M Q < r₀ → ∀ r ∈ Ioi (ModeStability.outerHorizon M Q),
        0 < ModeStability.delta M Q r * (2 * ω * r - e) -
            2 * (if r₀ < 2 * M then 0 else 1 / ModeStability.AllAngular.staticSolutionAA M Q r) *
              ModeStability.radialK e ω r ∧
          0 < 2 * ModeStability.delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
            2 * ModeStability.delta M Q r *
                ((if r₀ < 2 * M then 0 else 1 / ModeStability.AllAngular.staticSolutionAA M Q r) +
                  (r - M)) *
              ModeStability.radialK e ω r * (2 * ω * r - e) -
            ModeStability.delta M Q r ^ 2 * ModeStability.radialK e ω r * (2 * ω) +
            2 * (if r₀ < 2 * M then 0
                else 1 / ModeStability.AllAngular.staticSolutionAA M Q r) ^ 2 *
              ModeStability.radialK e ω r ^ 2 ∧
          0 < ModeStability.AllAngular.xDeriv M Q
              (ModeStability.AllAngular.normalizationG M Q e ω)
              (fun s => ModeStability.AllAngular.normalizationG M Q e ω s ^ 2 *
                ModeStability.radialK e ω s) r ∧
          0 < 2 * ModeStability.AllAngular.xDeriv M Q
                (ModeStability.AllAngular.normalizationG M Q e ω)
                (fun s => ModeStability.AllAngular.normalizationG M Q e ω s ^ 2 *
                  ModeStability.radialK e ω s) r ^ 2 -
              ModeStability.AllAngular.normalizationG M Q e ω r ^ 2 *
                ModeStability.radialK e ω r *
                ModeStability.AllAngular.xDeriv M Q
                  (ModeStability.AllAngular.normalizationG M Q e ω)
                  (ModeStability.AllAngular.xDeriv M Q
                    (ModeStability.AllAngular.normalizationG M Q e ω)
                    (fun s => ModeStability.AllAngular.normalizationG M Q e ω s ^ 2 *
                      ModeStability.radialK e ω s)) r := by
  intro M Q e ω hM hQ hω r₀ hr₀ ha r hr
  have hr' : ModeStability.outerHorizon M Q < r := hr
  have he : ω * r₀ = e := by
    rw [hr₀]
    field_simp
  have hcore : 0 < ModeStability.delta M Q r * (2 * ω * r - e) -
        2 * (if r₀ < 2 * M then 0 else 1 / ModeStability.AllAngular.staticSolutionAA M Q r) *
          ModeStability.radialK e ω r ∧
      0 < 2 * ModeStability.delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
        2 * ModeStability.delta M Q r *
            ((if r₀ < 2 * M then 0 else 1 / ModeStability.AllAngular.staticSolutionAA M Q r) +
              (r - M)) *
          ModeStability.radialK e ω r * (2 * ω * r - e) -
        ModeStability.delta M Q r ^ 2 * ModeStability.radialK e ω r * (2 * ω) +
        2 * (if r₀ < 2 * M then 0 else 1 / ModeStability.AllAngular.staticSolutionAA M Q r) ^ 2 *
          ModeStability.radialK e ω r ^ 2 := by
    split_ifs with h2M
    · obtain ⟨h1, h2⟩ :=
        ModeStability.AllAngular.scalar_positivity_constant hM hQ hω ha h2M hr'
      rw [he] at h1 h2
      constructor
      · convert h1 using 1
        ring
      · convert h2 using 1
        ring
    · obtain ⟨-, h0, hεδ, hεχ, hχ, -, -, -⟩ :=
        ModeStability.AllAngular.common_geometry M Q e ω hM hQ hω r₀ hr₀ ha r hr
      obtain ⟨h1, h2⟩ := ModeStability.AllAngular.scalar_positivity_reciprocal hM hQ hω ha
        (not_lt.1 h2M) hr' hχ h0 hεδ hεχ
      rw [he] at h1 h2
      exact ⟨h1, h2⟩
  obtain ⟨c, hg, hg0, hχ⟩ :=
    ModeStability.AllAngular.NormalizationFacts.gauge_facts (e := e) (ω := ω) hM hQ hr'
  rw [← hr₀] at hχ
  obtain ⟨k1, k2⟩ := ModeStability.AllAngular.NormalizationFacts.xDeriv_k (e := e) (ω := ω)
    (ModeStability.AllAngular.NormalizationFacts.delta_pos_of_outerHorizon_lt hr').ne'
    hg0.ne' hg
  rw [hχ] at k1 k2
  refine ⟨hcore.1, hcore.2, ?_, ?_⟩
  · rw [k1]
    exact mul_pos (pow_pos hg0 4) hcore.1
  · rw [k2]
    exact mul_pos (pow_pos hg0 8) hcore.2

end ModeStability.Provider.AllAngular

end
