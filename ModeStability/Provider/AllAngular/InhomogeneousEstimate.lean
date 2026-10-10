module

public import Mathlib
public import ModeStability.AllAngular.InhomogeneousAssembly
public import ModeStability.AllAngular.SourceIdentityAll
public import ModeStability.AllAngular.BoundedLR

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.InhomogeneousEstimate` supplies the proof of the
corresponding source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.Provider.AllAngular

/-- **Proposition 6.1** (inhomogeneous estimate uniform in angular momentum), written in `r`:
with `g` the normalization (2.2), `U = R/g`, `U_x = Δg² ∂_r U`, `k̂` the effective frequency
(3.2), `a_{k̂} = E_{k̂}/k̂_x²`, `V − k² = g⁴(LΔ − K²)`, `F = Δg³S` and `dx = dr/(Δg²)`:
`𝓑[U] + ‖U_x‖²_{L²(I)} + (1 + L)‖U‖²_{L²(I)} ≤ C_I/(1 + L) · ‖F‖²_{L²(I)}`, with `C_I > 0`
depending on `(M, Q, e, ω, I)` only. -/
theorem inhomogeneous_estimate :
    ∀ (M Q e ω : ℝ), 0 < M → |Q| ≤ M → 0 < e → 0 < ω → ω < e / ModeStability.outerHorizon M Q →
      ∀ (ρ₁ ρ₂ : ℝ), ModeStability.outerHorizon M Q < ρ₁ → ρ₁ < ρ₂ →
        ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 0 ≤ L →
          ∀ (S R : ℝ → ℂ) (BH BI : ℂ), (∀ r, r ∉ Icc ρ₁ ρ₂ → S r = 0) →
            MemLp S 2 (volume.restrict (Icc ρ₁ ρ₂)) →
            ModeStability.AllAngular.IsRadialSolutionWithSourceL M Q e ω L R S →
            ModeStability.AllAngular.HorizonConditionL M Q e ω R BH →
            ModeStability.AllAngular.InfinityConditionL M Q e ω R BI →
            let g : ℝ → ℝ := ModeStability.AllAngular.normalizationG M Q e ω
            let U : ℝ → ℂ := fun s => R s / (g s : ℂ)
            let Ux : ℝ → ℂ := fun s => ((ModeStability.delta M Q s * g s ^ 2 : ℝ) : ℂ) * deriv U s
            let kh : ℝ → ℝ := ModeStability.AllAngular.effectiveK M Q e ω L
            let khx : ℝ → ℝ := ModeStability.AllAngular.xDeriv M Q g kh
            let khxx : ℝ → ℝ := ModeStability.AllAngular.xDeriv M Q g khx
            let ak : ℝ → ℝ := fun s => (2 * khx s ^ 2 - kh s * khxx s) / khx s ^ 2
            let w : ℝ → ℝ := fun s => 1 / (ModeStability.delta M Q s * g s ^ 2)
            let AH : Set ℝ := {s | ModeStability.outerHorizon M Q < s ∧ s < e / ω ∧
              L * ModeStability.delta M Q s < ModeStability.radialK e ω s ^ 2}
            let Fb : Set ℝ := {s | ModeStability.outerHorizon M Q < s ∧
              ModeStability.radialK e ω s ^ 2 ≤ L * ModeStability.delta M Q s}
            let AI : Set ℝ := {s | e / ω < s ∧
              L * ModeStability.delta M Q s < ModeStability.radialK e ω s ^ 2}
            ((∫⁻ s in AH, ENNReal.ofReal (ak s * ‖Ux s + (kh s : ℂ) * I * U s‖ ^ 2 * w s)) +
              (∫⁻ s in Fb, ENNReal.ofReal ((‖Ux s‖ ^ 2 +
                g s ^ 4 * (L * ModeStability.delta M Q s - ModeStability.radialK e ω s ^ 2) *
                  ‖U s‖ ^ 2) * w s)) +
              (∫⁻ s in AI, ENNReal.ofReal (ak s * ‖Ux s - (kh s : ℂ) * I * U s‖ ^ 2 * w s)) +
              (∫⁻ s in Icc ρ₁ ρ₂, ENNReal.ofReal (‖Ux s‖ ^ 2 * w s)) +
              ENNReal.ofReal (1 + L) * (∫⁻ s in Icc ρ₁ ρ₂, ENNReal.ofReal (‖U s‖ ^ 2 * w s)))
              ≤ ENNReal.ofReal (C / (1 + L)) *
                ∫⁻ s in Icc ρ₁ ρ₂,
                  ENNReal.ofReal
                    (‖((ModeStability.delta M Q s * g s ^ 3 : ℝ) : ℂ) * S s‖ ^ 2 * w s) :=
  ModeStability.AllAngular.inhomogeneous_estimate_of_interfaces
    ModeStability.AllAngular.sourceIdentityAll_holds ModeStability.AllAngular.boundedLR_holds

end ModeStability.Provider.AllAngular

end
