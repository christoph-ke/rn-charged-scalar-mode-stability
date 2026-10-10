module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.StaticSolution
public import ModeStability.Frozen.IsRadialSolution
public import ModeStability.Frozen.HorizonCondition
public import ModeStability.Frozen.InfinityCondition
public import ModeStability.Frozen.ComplementaryBandExclusion
public import ModeStability.Main.Conjugation

/-!
# Theorem 1.1 from the separation at corotation

the spherical research notes in preparation, p. 1, Theorem 1.1, reduced to Proposition 2.3
(p. 3). The argument is the one of the introduction. By complex conjugation (`Conjugation`)
it suffices to treat `ω > 0`. In the band `2Mω − e ≥ 0` the Appendix A trust boundary
`ComplementaryBandExclusion` applies. In the complementary band `r₀ = e/ω > 2M`, and
Proposition 2.3 applied to the single mode `R = RH = RI` gives the two contradictory
inequalities (2.16) for `Re (R'/R)(r₀)`.

The statement `mode_exclusion_of_separation` is conditional on the statement of
Proposition 2.3 (the frozen `ModeStability.separation_at_corotation`), which it takes as a
hypothesis.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.Main

/-- **Theorem 1.1**, assuming the statement of Proposition 2.3 (separation at corotation). -/
theorem mode_exclusion_of_separation
    (hsep : ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → 0 < ω →
      ∀ (r₀ : ℝ), r₀ = q * Q / ω → 2 * M < r₀ →
        ∀ (RH RI : ℝ → ℂ) (BH BI : ℂ),
          IsRadialSolution M Q q ω RH → HorizonCondition M Q q ω RH BH →
          ¬ EqOn RH 0 (Ioi (outerHorizon M Q)) →
          IsRadialSolution M Q q ω RI → InfinityCondition M Q q ω RI BI →
          ¬ EqOn RI 0 (Ioi (outerHorizon M Q)) →
            RH r₀ ≠ 0 ∧ RI r₀ ≠ 0 ∧
              -1 / (delta M Q r₀ * staticSolution M Q r₀) < (deriv RH r₀ / RH r₀).re ∧
              (deriv RI r₀ / RI r₀).re < -1 / (delta M Q r₀ * staticSolution M Q r₀) ∧
              delta M Q r₀ * (RH r₀ * deriv RI r₀ - deriv RH r₀ * RI r₀) ≠ 0) :
    ComplementaryBandExclusion →
      ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → ω ≠ 0 →
        ∀ (R : ℝ → ℂ) (BH BI : ℂ), IsRadialSolution M Q q ω R →
          HorizonCondition M Q q ω R BH → InfinityCondition M Q q ω R BI →
            EqOn R 0 (Ioi (outerHorizon M Q)) := by
  intro hband
  -- the case `ω > 0`
  have pos : ∀ (M Q q ω : ℝ), 0 < M → |Q| < M → 0 < ω →
      ∀ (R : ℝ → ℂ) (BH BI : ℂ), IsRadialSolution M Q q ω R →
        HorizonCondition M Q q ω R BH → InfinityCondition M Q q ω R BI →
          EqOn R 0 (Ioi (outerHorizon M Q)) := by
    intro M Q q ω hM hQ hω R BH BI hR hH hI
    by_cases hb : 0 ≤ 2 * M * ω - q * Q
    · exact hband M Q q ω hM hQ hω hb R BH BI hR hH hI
    · by_contra hne
      have h2M : 2 * M < q * Q / ω := by
        rw [lt_div_iff₀ hω]
        linarith
      obtain ⟨-, -, h3, h4, -⟩ := hsep M Q q ω hM hQ hω (q * Q / ω) rfl h2M R R BH BI
        hR hH hne hR hI hne
      exact lt_asymm h3 h4
  intro M Q q ω hM hQ hω0 R BH BI hR hH hI
  rcases lt_or_gt_of_ne hω0 with hω | hω
  · -- `ω < 0`: conjugate to `(−q, −ω)`
    have h := pos M Q (-q) (-ω) hM hQ (neg_pos.2 hω) _ _ _ (isRadialSolution_conj hR)
      (horizonCondition_conj hH) (infinityCondition_conj hI)
    intro r hr
    have hr' := h hr
    simpa using hr'
  · exact pos M Q q ω hM hQ hω R BH BI hR hH hI

end ModeStability.Main

end
