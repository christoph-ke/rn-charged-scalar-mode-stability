module

public import Mathlib
public import ModeStability.AllAngular.InhomogeneousAssemblyAux

/-!
# Final assembly of Proposition 6.1 against the radial interfaces

Source: the all-angular research notes in preparation, paper p. 8.
The source identity and bounded-angular estimate are explicit hypotheses.
The conclusion matches the public theorem statement without importing its anchor.
-/

public section

open Complex Set Filter MeasureTheory

namespace ModeStability.AllAngular

/-- Proposition 6.1 in the shared radial notation, conditional on its two interfaces. -/
theorem inhomogeneous_estimateR_of_interfaces
    (h63 : P61.SourceIdentityAll) (hBL : P61.BoundedLR)
    {M Q e ω ρ₁ ρ₂ : ℝ} (hrange : P61.Range17 M Q e ω ρ₁ ρ₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 ≤ L →
      ∀ (S R : ℝ → ℂ) (BH BI : ℂ), P61.SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI →
        P61.lhsR M Q e ω L ρ₁ ρ₂ R ≤
          ENNReal.ofReal (C / (1 + L)) * P61.srcNormR M Q e ω ρ₁ ρ₂ S := by
  obtain ⟨L₀, c, hL₀, hc, -, hlarge⟩ := largeL_compact_lower_bound
    hrange.1 hrange.2.1 hrange.2.2.2.2.2.1 hrange.2.2.2.2.2.2.le
  obtain ⟨Cb, hCb, hbounded⟩ := hBL M Q e ω ρ₁ ρ₂ L₀ hrange (by linarith)
  let Cl : ℝ := 4 * (1 + 1 / c) ^ 2
  let C : ℝ := max Cl (Cb * (1 + L₀))
  have hC : 0 < C := lt_of_lt_of_le (mul_pos hCb (by linarith)) (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro L hL S R BH BI hp
  have hid := h63 M Q e ω ρ₁ ρ₂ L hrange hL S R BH BI hp
  have hden : 0 < 1 + L := by linarith
  by_cases hLL : L₀ ≤ L
  · obtain ⟨hfb, hcoef⟩ := hlarge L hLL
    have hh := inhomogeneous_largeL_estimate hrange.1 hrange.2.1
      hrange.2.2.2.2.2.1 hc hL₀ hLL hp.2.1 hp.2.2.1.1 hid hfb
      (fun r hr => (hcoef r hr).2.2)
    apply hh.trans
    gcongr
    exact le_max_left _ _
  · have hh := hbounded L hL (le_of_not_ge hLL) S R BH BI hp hid
    apply hh.trans
    gcongr
    apply (le_div_iff₀ hden).mpr
    calc
      Cb * (1 + L) ≤ Cb * (1 + L₀) := by gcongr; exact le_of_not_ge hLL
      _ ≤ C := le_max_right _ _

/-- The exact frozen Proposition 6.1 conclusion, with the source-identity and bounded-`L`
interfaces as its only additional hypotheses. Its energies unfold definitionally to `P61`. -/
theorem inhomogeneous_estimate_of_interfaces
    (h63 : P61.SourceIdentityAll) (hBL : P61.BoundedLR) :
    ∀ (M Q e ω : ℝ), 0 < M → |Q| ≤ M → 0 < e → 0 < ω → ω < e / outerHorizon M Q →
      ∀ (ρ₁ ρ₂ : ℝ), outerHorizon M Q < ρ₁ → ρ₁ < ρ₂ →
        ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 0 ≤ L →
          ∀ (S R : ℝ → ℂ) (BH BI : ℂ), (∀ r, r ∉ Icc ρ₁ ρ₂ → S r = 0) →
            MemLp S 2 (volume.restrict (Icc ρ₁ ρ₂)) →
            IsRadialSolutionWithSourceL M Q e ω L R S →
            HorizonConditionL M Q e ω R BH → InfinityConditionL M Q e ω R BI →
            let g : ℝ → ℝ := normalizationG M Q e ω
            let U : ℝ → ℂ := fun s => R s / (g s : ℂ)
            let Ux : ℝ → ℂ := fun s => ((delta M Q s * g s ^ 2 : ℝ) : ℂ) * deriv U s
            let kh : ℝ → ℝ := effectiveK M Q e ω L
            let khx : ℝ → ℝ := xDeriv M Q g kh
            let khxx : ℝ → ℝ := xDeriv M Q g khx
            let ak : ℝ → ℝ := fun s => (2 * khx s ^ 2 - kh s * khxx s) / khx s ^ 2
            let w : ℝ → ℝ := fun s => 1 / (delta M Q s * g s ^ 2)
            let AH : Set ℝ := {s | outerHorizon M Q < s ∧ s < e / ω ∧
              L * delta M Q s < radialK e ω s ^ 2}
            let Fb : Set ℝ := {s | outerHorizon M Q < s ∧ radialK e ω s ^ 2 ≤ L * delta M Q s}
            let AI : Set ℝ := {s | e / ω < s ∧ L * delta M Q s < radialK e ω s ^ 2}
            ((∫⁻ s in AH, ENNReal.ofReal (ak s * ‖Ux s + (kh s : ℂ) * I * U s‖ ^ 2 * w s)) +
              (∫⁻ s in Fb, ENNReal.ofReal ((‖Ux s‖ ^ 2 +
                g s ^ 4 * (L * delta M Q s - radialK e ω s ^ 2) * ‖U s‖ ^ 2) * w s)) +
              (∫⁻ s in AI, ENNReal.ofReal (ak s * ‖Ux s - (kh s : ℂ) * I * U s‖ ^ 2 * w s)) +
              (∫⁻ s in Icc ρ₁ ρ₂, ENNReal.ofReal (‖Ux s‖ ^ 2 * w s)) +
              ENNReal.ofReal (1 + L) * (∫⁻ s in Icc ρ₁ ρ₂, ENNReal.ofReal (‖U s‖ ^ 2 * w s)))
              ≤ ENNReal.ofReal (C / (1 + L)) *
                ∫⁻ s in Icc ρ₁ ρ₂, ENNReal.ofReal (‖((delta M Q s * g s ^ 3 : ℝ) : ℂ) * S s‖ ^ 2 * w s) := by
  intro M Q e ω hM hQ he hω hband ρ₁ ρ₂ hρ hρ₁₂
  have hrange : P61.Range17 M Q e ω ρ₁ ρ₂ :=
    ⟨hM, hQ, he, hω, hband, hρ, hρ₁₂⟩
  obtain ⟨C, hC, hestimate⟩ := inhomogeneous_estimateR_of_interfaces h63 hBL hrange
  refine ⟨C, hC, ?_⟩
  intro L hL S R BH BI hsupport hS hR hH hI
  change P61.lhsR M Q e ω L ρ₁ ρ₂ R ≤
    ENNReal.ofReal (C / (1 + L)) * P61.srcNormR M Q e ω ρ₁ ρ₂ S
  exact hestimate L hL S R BH BI ⟨hsupport, hS, hR, hH, hI⟩

end ModeStability.AllAngular

end
