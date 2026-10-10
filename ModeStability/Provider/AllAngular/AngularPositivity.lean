module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.Frozen.AllAngular.NormalizationG
public import ModeStability.Frozen.AllAngular.XDeriv
public import ModeStability.Frozen.AllAngular.EffectiveK
public import ModeStability.Frozen.AllAngular.CommonGeometry
public import ModeStability.Frozen.AllAngular.ScalarPositivity
public import ModeStability.AllAngular.Geometry
public import ModeStability.AllAngular.AngularAlgebra
public import ModeStability.AllAngular.NormalizationFacts

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.AngularPositivity` supplies the proof of the corresponding
source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Set Filter Topology

namespace ModeStability.Provider.AllAngular

theorem angular_positivity :
    ∀ (M Q e ω L : ℝ), 0 < M → |Q| ≤ M → 0 < ω → 0 ≤ L → ∀ (r₀ : ℝ), r₀ = e / ω →
      ModeStability.outerHorizon M Q < r₀ → ∀ r ∈ Ioi (ModeStability.outerHorizon M Q),
        L * ModeStability.delta M Q r < ModeStability.radialK e ω r ^ 2 →
        0 < ModeStability.AllAngular.xDeriv M Q (ModeStability.AllAngular.normalizationG M Q e ω)
            (ModeStability.AllAngular.effectiveK M Q e ω L) r ∧
          0 < 2 * ModeStability.AllAngular.xDeriv M Q
                (ModeStability.AllAngular.normalizationG M Q e ω)
                (ModeStability.AllAngular.effectiveK M Q e ω L) r ^ 2 -
              ModeStability.AllAngular.effectiveK M Q e ω L r *
                ModeStability.AllAngular.xDeriv M Q
                  (ModeStability.AllAngular.normalizationG M Q e ω)
                  (ModeStability.AllAngular.xDeriv M Q
                    (ModeStability.AllAngular.normalizationG M Q e ω)
                    (ModeStability.AllAngular.effectiveK M Q e ω L)) r ∧
          min ((2 * ModeStability.AllAngular.xDeriv M Q
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
                        ModeStability.radialK e ω s)) r) /
                ModeStability.AllAngular.xDeriv M Q
                  (ModeStability.AllAngular.normalizationG M Q e ω)
                  (fun s => ModeStability.AllAngular.normalizationG M Q e ω s ^ 2 *
                    ModeStability.radialK e ω s) r ^ 2) 2 ≤
            (2 * ModeStability.AllAngular.xDeriv M Q
                  (ModeStability.AllAngular.normalizationG M Q e ω)
                  (ModeStability.AllAngular.effectiveK M Q e ω L) r ^ 2 -
                ModeStability.AllAngular.effectiveK M Q e ω L r *
                  ModeStability.AllAngular.xDeriv M Q
                    (ModeStability.AllAngular.normalizationG M Q e ω)
                    (ModeStability.AllAngular.xDeriv M Q
                      (ModeStability.AllAngular.normalizationG M Q e ω)
                      (ModeStability.AllAngular.effectiveK M Q e ω L)) r) /
              ModeStability.AllAngular.xDeriv M Q
                (ModeStability.AllAngular.normalizationG M Q e ω)
                (ModeStability.AllAngular.effectiveK M Q e ω L) r ^ 2 := by
  intro M Q e ω L hM hQ hω hL r₀ hr₀ ha r hr hK
  obtain ⟨hT, -, -, -, hχpos, hχz, -, -⟩ :=
    ModeStability.AllAngular.common_geometry M Q e ω hM hQ hω r₀ hr₀ ha r hr
  obtain ⟨hH, hA, -, -⟩ :=
    ModeStability.AllAngular.scalar_positivity M Q e ω hM hQ hω r₀ hr₀ ha r hr
  rw [mem_Ioi] at hr
  have hΔ := ModeStability.AllAngular.NormalizationFacts.delta_pos_of_outerHorizon_lt hr
  obtain ⟨c, hg, hg0, hχ⟩ :=
    ModeStability.AllAngular.NormalizationFacts.gauge_facts (e := e) (ω := ω) hM hQ hr
  rw [← hr₀] at hχ
  obtain ⟨k1, k2⟩ :=
    ModeStability.AllAngular.NormalizationFacts.xDeriv_k (e := e) (ω := ω) hΔ.ne' hg0.ne' hg
  obtain ⟨j1, j2⟩ := ModeStability.AllAngular.NormalizationFacts.xDeriv_khat (e := e) (ω := ω)
    (L := L) hQ hL hΔ hg0 hK hg
  rw [hχ] at k1 k2 j1 j2
  rw [ModeStability.AllAngular.NormalizationFacts.effectiveK_eq_effectiveKAux, j2, j1, k2, k1]
  -- `τ = LΔ/K² ∈ [0, 1)`, `q = √(1 − τ)`
  have hLΔ : 0 ≤ L * ModeStability.delta M Q r := mul_nonneg hL hΔ.le
  have hK2 : 0 < ModeStability.radialK e ω r ^ 2 := lt_of_le_of_lt hLΔ hK
  have hτ0 : 0 ≤ L * ModeStability.delta M Q r / ModeStability.radialK e ω r ^ 2 :=
    div_nonneg hLΔ hK2.le
  have hτ1 : L * ModeStability.delta M Q r / ModeStability.radialK e ω r ^ 2 < 1 :=
    (div_lt_one hK2).2 hK
  have hq := Real.sqrt_pos.2 (sub_pos.2 hτ1)
  have hq2 := Real.sq_sqrt (sub_pos.2 hτ1).le
  -- `T > δ|K| ≥ 0`, hence `T > 0` and `T² > δ²K²`
  have hδK : 0 ≤ Real.sqrt (M ^ 2 - Q ^ 2) * |ModeStability.radialK e ω r| :=
    mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hTpos := lt_of_le_of_lt hδK hT
  have hT2 := pow_lt_pow_left₀ hT hδK (n := 2) two_ne_zero
  rw [mul_pow, sq_abs] at hT2
  -- `0 ≤ χ ≤ z`, hence `B > A₀ + 2T²` (3.9)
  have hχ0z : 0 ≤ (if r₀ < 2 * M then 0
        else 1 / ModeStability.AllAngular.staticSolutionAA M Q r) ∧
      (if r₀ < 2 * M then 0 else 1 / ModeStability.AllAngular.staticSolutionAA M Q r) ≤
        r - M := by
    split_ifs
    · exact ⟨le_rfl,
        (ModeStability.AllAngular.NormalizationFacts.sub_M_pos_of_outerHorizon_lt hr).le⟩
    · exact ⟨hχpos.le, hχz⟩
  have hB := ModeStability.AllAngular.mixed_coefficient_gt
    (A₀ := 2 * ModeStability.delta M Q r ^ 2 * (2 * ω * r - e) ^ 2 -
      2 * ModeStability.delta M Q r *
          ((if r₀ < 2 * M then 0 else 1 / ModeStability.AllAngular.staticSolutionAA M Q r) +
            (r - M)) *
        ModeStability.radialK e ω r * (2 * ω * r - e) -
      ModeStability.delta M Q r ^ 2 * ModeStability.radialK e ω r * (2 * ω) +
      2 * (if r₀ < 2 * M then 0 else 1 / ModeStability.AllAngular.staticSolutionAA M Q r) ^ 2 *
        ModeStability.radialK e ω r ^ 2)
    hT2 hχ0z.1 hχ0z.2
  rw [ModeStability.AllAngular.sq_sqrt_sub_sq hQ] at hB
  exact ModeStability.AllAngular.NormalizationFacts.angular_final_alg hg0 hτ0 hτ1 hq hq2 hA hH
    hTpos hB

end ModeStability.Provider.AllAngular

end
