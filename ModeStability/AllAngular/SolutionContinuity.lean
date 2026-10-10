module

public import Mathlib
public import ModeStability.Frozen.AllAngular.IsRadialSolutionL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL
public import ModeStability.AllAngular.SolutionContinuityHorizon
public import ModeStability.AllAngular.SolutionContinuityInfinity

/-!
# Continuity in the frequency of the normalized solutions `R_H`, `R_I`

Source: the all-angular research notes in preparation, p. 10.

For fixed `M > 0`, `|Q| ≤ M`, real `e` and `L ≥ 0`:

* `horizon_solution_continuous_aux`: there is a family `R_H(ω, ·)` which, for every real `ω` with
  `K(a) ≠ 0`, solves the radial equation (`IsRadialSolutionL`) and satisfies the horizon
  condition (1.4) with leading coefficient `1` (`HorizonConditionL`, phase `Θ = radialPhase`),
  such that `(ω, r) ↦ R_H(ω, r)` and `(ω, r) ↦ ∂_r R_H(ω, r)` are jointly continuous on
  `{K(a) ≠ 0} × (a, ∞)`.

* `infinity_solution_continuous_aux`: the normalized outgoing family and its radial derivative
  are jointly continuous on `{ω ≠ 0} × (a, ∞)`.

## Proof

The family is the construction of `ModeStability.AllAngular.exists_horizon_solution` with `ω` as
a parameter (`ModeStability.AllAngular.SolutionContinuityHorizon`): `κ = K + c(ω)Δ` with the
continuous choice `c(ω) = (|K(a)ω| + K'(a)²)/K(a)`, the Volterra solutions `(A, B)` of the
amplitude system with data `(0, −2iK(a))` at `a⁺`, jointly continuous by
`ModeStability.ODE.continuousOn_of_nhdsGT`, and `R_H = (e^{iΘ}A − e^{−iΘ}B)/(2iκ)`,
`ΔR_H' = (e^{iΘ}A + e^{−iΘ}B)/2`. Both are jointly continuous since `Θ = radialPhase` is
(`sc_continuousOn_radialPhase`).

For infinity, near each nonzero frequency the outgoing amplitude system has a common
`C/r²` majorant (`sc_infinity_patch`). Dominated convergence and
`ODE.continuousOn_of_atTop` give amplitude continuity on this tail. Recovering radial
Cauchy data and applying `sc_continuousOn_of_interior` gives continuity throughout the
exterior. This applies to any normalized outgoing family, including one chosen using
`exists_infinity_solution`; no dependence on auxiliary construction choices is assumed.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

open InfinityUniqueness

/-- **ω-continuity of the normalized ingoing solutions.** For fixed `M > 0`, `|Q| ≤ M`, real
`e` and `L ≥ 0`, there is a family `RH ω` which, for every real `ω` with `K(a) ≠ 0`, solves the
radial equation (1.2) on `r > a` and satisfies the horizon condition (1.4) with leading
coefficient `1`, such that `(ω, r) ↦ R_H(ω, r)` and `(ω, r) ↦ ∂_r R_H(ω, r)` are jointly
continuous on `{K(a) ≠ 0} × (a, ∞)`. The premises `M > 0`, `|Q| ≤ M`, `L ≥ 0` of the source are
kept but not used here. -/
theorem horizon_solution_continuous_aux :
    ∀ (M Q e L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L →
      ∃ RH : ℝ → ℝ → ℂ,
        (∀ ω : ℝ, radialK e ω (outerHorizon M Q) ≠ 0 →
          IsRadialSolutionL M Q e ω L (RH ω) ∧ HorizonConditionL M Q e ω (RH ω) 1) ∧
        ContinuousOn (fun p : ℝ × ℝ => RH p.1 p.2)
          ({ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ Ioi (outerHorizon M Q)) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (RH p.1) p.2)
          ({ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ Ioi (outerHorizon M Q)) := by
  intro M Q e L _ _ _
  obtain ⟨v, hv⟩ := sc_exists_horizon_amp M Q e L
  set a := outerHorizon M Q with ha
  set S := {ω : ℝ | radialK e ω a ≠ 0} with hS
  set T := S ×ˢ Ioi a with hT
  -- the system for the components
  have hsys : ∀ ω ∈ S, ∀ r ∈ Ioi a,
      HasDerivAt (fun t => (v ω t).1)
        (hs_m11 M Q e ω L (sc_cH M Q e ω) r * (v ω r).1 +
          hs_m12 M Q e ω L (sc_cH M Q e ω) (radialPhase M Q e ω) r * (v ω r).2) r ∧
      HasDerivAt (fun t => (v ω t).2)
        (hs_m21 M Q e ω L (sc_cH M Q e ω) (radialPhase M Q e ω) r * (v ω r).1 +
          hs_m22 M Q e ω L (sc_cH M Q e ω) r * (v ω r).2) r := by
    intro ω hω r hr
    have h := (hv ω hω).1 r hr
    simp only [sc_MH, ModeStability.ODE.mat2_apply] at h
    exact ⟨(ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r h,
      (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r h⟩
  have hκ : ∀ ω ∈ S, ∀ r ∈ Ioi a, hs_kap M Q e ω (sc_cH M Q e ω) r ≠ 0 :=
    fun ω hω r hr => sc_kap_ne hω (le_of_lt hr)
  have hΘ : ∀ ω, ∀ r ∈ Ioi a, HasDerivAt (radialPhase M Q e ω)
      (radialK e ω r / delta M Q r) r := fun ω r hr => sc_hasDerivAt_radialPhase M Q e ω hr
  have hder : ∀ ω ∈ S, ∀ r ∈ Ioi a,
      deriv (hs_sysR M Q e ω (sc_cH M Q e ω) (radialPhase M Q e ω) (fun t => (v ω t).1)
        (fun t => (v ω t).2)) r =
      hs_sysP (radialPhase M Q e ω) (fun t => (v ω t).1) (fun t => (v ω t).2) r /
        delta M Q r :=
    fun ω hω => (hs_radial_of_system (hκ ω hω) (hΘ ω) (hsys ω hω)).1
  -- joint continuity of the ingredients
  have hvc := sc_continuousOn_horizon_amp hv
  have hA : ContinuousOn (fun p : ℝ × ℝ => (v p.1 p.2).1) T := continuous_fst.comp_continuousOn hvc
  have hB : ContinuousOn (fun p : ℝ × ℝ => (v p.1 p.2).2) T := continuous_snd.comp_continuousOn hvc
  have hΘc : ContinuousOn (fun p : ℝ × ℝ => (radialPhase M Q e p.1 p.2 : ℂ)) T :=
    continuous_ofReal.comp_continuousOn
      ((sc_continuousOn_radialPhase M Q e).mono (prod_mono (subset_univ _) subset_rfl))
  have hE : ContinuousOn (fun p : ℝ × ℝ => exp (I * (radialPhase M Q e p.1 p.2 : ℂ))) T :=
    (continuousOn_const.mul hΘc).cexp
  have hEi : ContinuousOn (fun p : ℝ × ℝ => exp (-(I * (radialPhase M Q e p.1 p.2 : ℂ)))) T :=
    (continuousOn_const.mul hΘc).neg.cexp
  refine ⟨fun ω => hs_sysR M Q e ω (sc_cH M Q e ω) (radialPhase M Q e ω) (fun t => (v ω t).1)
    (fun t => (v ω t).2), fun ω hω => ?_, ?_, ?_⟩
  · -- the normalization
    have hA0 : Tendsto (fun t => (v ω t).1) (𝓝[>] a) (𝓝 0) :=
      (continuous_fst.tendsto _).comp (hv ω hω).2
    have hB0 : Tendsto (fun t => (v ω t).2) (𝓝[>] a) (𝓝 (-(2 * I * radialK e ω a))) :=
      (continuous_snd.tendsto _).comp (hv ω hω).2
    obtain ⟨hR, h1, h2⟩ := sc_horizon_condition_sysR hω (hκ ω hω) (hΘ ω) (hsys ω hω) hA0 hB0
    refine ⟨hR, ?_⟩
    unfold HorizonConditionL
    rw [ite_eq_right fun h => hω h.2]
    exact ⟨h1, h2⟩
  · -- continuity of `R_H`
    have hk : ContinuousOn (fun p : ℝ × ℝ =>
        2 * I * (hs_kap M Q e p.1 (sc_cH M Q e p.1) p.2 : ℂ)) T :=
      continuousOn_const.mul (continuous_ofReal.comp_continuousOn
        ((sc_continuousOn_kapH M Q e).mono fun p hp => ⟨hp.1, mem_univ _⟩))
    exact ((hE.mul hA).sub (hEi.mul hB)).div hk fun p hp =>
      hs_two_I_mul_ne_zero (hκ p.1 hp.1 p.2 hp.2)
  · -- continuity of `∂_r R_H = (e^{iΘ}A + e^{−iΘ}B)/(2Δ)`
    have hd : ContinuousOn (fun p : ℝ × ℝ => (delta M Q p.2 : ℂ)) T :=
      (continuous_ofReal.comp ((continuous_delta M Q).comp continuous_snd)).continuousOn
    have h := (((hE.mul hA).add (hEi.mul hB)).div_const 2).div hd fun p hp =>
      ofReal_ne_zero.2 (delta_pos_of_lt hp.2).ne'
    exact h.congr fun p hp => hder p.1 hp.1 p.2 hp.2

/-- **ω-continuity of the normalized outgoing solutions.** Both the solution and its radial
 derivative are jointly continuous on `{ω ≠ 0} × (a, ∞)`. -/
theorem infinity_solution_continuous_aux :
    ∀ (M Q e L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L →
      ∃ RI : ℝ → ℝ → ℂ,
        (∀ ω : ℝ, ω ≠ 0 →
          IsRadialSolutionL M Q e ω L (RI ω) ∧ InfinityConditionL M Q e ω (RI ω) 1) ∧
        ContinuousOn (fun p : ℝ × ℝ => RI p.1 p.2)
          ({ω : ℝ | ω ≠ 0} ×ˢ Ioi (outerHorizon M Q)) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (RI p.1) p.2)
          ({ω : ℝ | ω ≠ 0} ×ˢ Ioi (outerHorizon M Q)) :=
  sc_exists_infinity_continuous

end ModeStability.AllAngular

end
