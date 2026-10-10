module

public import Mathlib
public import ModeStability.Frozen.AllAngular.IsRadialSolutionWithSourceL
public import ModeStability.Frozen.AllAngular.HorizonConditionL
public import ModeStability.Frozen.AllAngular.InfinityConditionL
public import ModeStability.Frozen.AllAngular.NormalizationG
public import ModeStability.Frozen.AllAngular.XDeriv
public import ModeStability.Frozen.AllAngular.EffectiveK

/-!
# Shared interface for the proof of Proposition 6.1 

Internal helper definitions (not source-facing anchors) fixing the exact `r`-form of the
quantities
in the frozen `ModeStability.AllAngular.inhomogeneous_estimate`
(`ModeStability/Frozen/AllAngular/InhomogeneousEstimate.lean`), so that the proof modules
establish
pieces against one statement:

* `bulkR`: `𝓑[U]`, the sum of the three nonnegative integrals of (5.3) over the horizon-side
  allowed set, the forbidden set and the infinity-side allowed set, copied verbatim from the
  frozen
  statement;
* `multR`: the multiplier `𝓜U` of the proof of Prop. 6.1 (p. 8): `U + 2γ(U_x + ik̂U)` on the
  horizon-side allowed set, `U` on the forbidden set, `U + 2γ(U_x − ik̂U)` on the infinity-side
  allowed set, `γ = k̂/k̂_x`;
* `SourceIdentityR`: the `r`-form of (6.3), `𝓑[U] < ∞` and
  `𝓑[U] = −Re ∫_{[ρ₁, ρ₂]} F conj(𝓜U) dx` with `F = Δg³S`, `dx = dr/(Δg²)`;
* `SourceIdentityAll`: (6.3) for every solution of the source problem in the range (1.7) (proved
  by
  case split over the four coordinate systems);
* `BoundedLR`: the bounded-`L` estimate in `r`-form, uniform in `0 ≤ L ≤ L₀`.

Source: the all-angular research notes in preparation, pp. 7–8 (Prop. 6.1 and its proof).
-/

@[expose] public section

open Complex Set Filter MeasureTheory

namespace ModeStability.AllAngular.P61

/-- `U = R/g`. -/
noncomputable def uR (M Q e ω : ℝ) (R : ℝ → ℂ) : ℝ → ℂ :=
  fun s => R s / (normalizationG M Q e ω s : ℂ)

/-- `U_x = Δg² ∂_r U`. -/
noncomputable def uxR (M Q e ω : ℝ) (R : ℝ → ℂ) : ℝ → ℂ :=
  fun s => ((delta M Q s * normalizationG M Q e ω s ^ 2 : ℝ) : ℂ) * deriv (uR M Q e ω R) s

/-- `k̂_x`. -/
noncomputable def khxR (M Q e ω L : ℝ) : ℝ → ℝ :=
  xDeriv M Q (normalizationG M Q e ω) (effectiveK M Q e ω L)

/-- `a_{k̂} = E_{k̂}/k̂_x²`. -/
noncomputable def akR (M Q e ω L : ℝ) : ℝ → ℝ := fun s =>
  (2 * khxR M Q e ω L s ^ 2 - effectiveK M Q e ω L s *
    xDeriv M Q (normalizationG M Q e ω) (khxR M Q e ω L) s) / khxR M Q e ω L s ^ 2

/-- `dx/dr = 1/(Δg²)`. -/
noncomputable def wR (M Q e ω : ℝ) : ℝ → ℝ := fun s =>
  1 / (delta M Q s * normalizationG M Q e ω s ^ 2)

/-- The horizon-side allowed set. -/
def setAH (M Q e ω L : ℝ) : Set ℝ :=
  {s | outerHorizon M Q < s ∧ s < e / ω ∧ L * delta M Q s < radialK e ω s ^ 2}

/-- The forbidden set. -/
def setFb (M Q e ω L : ℝ) : Set ℝ :=
  {s | outerHorizon M Q < s ∧ radialK e ω s ^ 2 ≤ L * delta M Q s}

/-- The infinity-side allowed set. -/
def setAI (M Q e ω L : ℝ) : Set ℝ :=
  {s | e / ω < s ∧ L * delta M Q s < radialK e ω s ^ 2}

/-- `𝓑[U]`, verbatim the first three terms of the frozen `inhomogeneous_estimate`. -/
noncomputable def bulkR (M Q e ω L : ℝ) (R : ℝ → ℂ) : ENNReal :=
  (∫⁻ s in setAH M Q e ω L, ENNReal.ofReal (akR M Q e ω L s *
      ‖uxR M Q e ω R s + (effectiveK M Q e ω L s : ℂ) * I * uR M Q e ω R s‖ ^ 2 * wR M Q e ω s)) +
    (∫⁻ s in setFb M Q e ω L, ENNReal.ofReal ((‖uxR M Q e ω R s‖ ^ 2 +
      normalizationG M Q e ω s ^ 4 * (L * delta M Q s - radialK e ω s ^ 2) *
        ‖uR M Q e ω R s‖ ^ 2) * wR M Q e ω s)) +
    (∫⁻ s in setAI M Q e ω L, ENNReal.ofReal (akR M Q e ω L s *
      ‖uxR M Q e ω R s - (effectiveK M Q e ω L s : ℂ) * I * uR M Q e ω R s‖ ^ 2 * wR M Q e ω s))

open Classical in
/-- The multiplier `𝓜U`, `γ = k̂/k̂_x`. -/
noncomputable def multR (M Q e ω L : ℝ) (R : ℝ → ℂ) : ℝ → ℂ := fun s =>
  if s ∈ setAH M Q e ω L then
    uR M Q e ω R s + 2 * ((effectiveK M Q e ω L s / khxR M Q e ω L s : ℝ) : ℂ) *
      (uxR M Q e ω R s + (effectiveK M Q e ω L s : ℂ) * I * uR M Q e ω R s)
  else if s ∈ setAI M Q e ω L then
    uR M Q e ω R s + 2 * ((effectiveK M Q e ω L s / khxR M Q e ω L s : ℝ) : ℂ) *
      (uxR M Q e ω R s - (effectiveK M Q e ω L s : ℂ) * I * uR M Q e ω R s)
  else uR M Q e ω R s

/-- `F = Δg³S`. -/
noncomputable def srcR (M Q e ω : ℝ) (S : ℝ → ℂ) : ℝ → ℂ := fun s =>
  ((delta M Q s * normalizationG M Q e ω s ^ 3 : ℝ) : ℂ) * S s

/-- (6.3) in `r`-form for one solution. -/
def SourceIdentityR (M Q e ω L ρ₁ ρ₂ : ℝ) (R S : ℝ → ℂ) : Prop :=
  bulkR M Q e ω L R < ⊤ ∧
    (bulkR M Q e ω L R).toReal =
      -(∫ s in Icc ρ₁ ρ₂, srcR M Q e ω S s * (starRingEnd ℂ) (multR M Q e ω L R s) *
          (wR M Q e ω s : ℂ)).re

/-- The hypotheses of the frozen `inhomogeneous_estimate` on one solution. -/
def SourceProblem (M Q e ω L ρ₁ ρ₂ : ℝ) (R S : ℝ → ℂ) (BH BI : ℂ) : Prop :=
  (∀ r, r ∉ Icc ρ₁ ρ₂ → S r = 0) ∧ MemLp S 2 (volume.restrict (Icc ρ₁ ρ₂)) ∧
    IsRadialSolutionWithSourceL M Q e ω L R S ∧
      HorizonConditionL M Q e ω R BH ∧ InfinityConditionL M Q e ω R BI

/-- The range (1.7) with a compact source interval. -/
def Range17 (M Q e ω ρ₁ ρ₂ : ℝ) : Prop :=
  0 < M ∧ |Q| ≤ M ∧ 0 < e ∧ 0 < ω ∧ ω < e / outerHorizon M Q ∧
    outerHorizon M Q < ρ₁ ∧ ρ₁ < ρ₂

/-- (6.3) for every solution of the source problem in the range (1.7). -/
def SourceIdentityAll : Prop :=
  ∀ (M Q e ω ρ₁ ρ₂ L : ℝ), Range17 M Q e ω ρ₁ ρ₂ → 0 ≤ L →
    ∀ (S R : ℝ → ℂ) (BH BI : ℂ), SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI →
      SourceIdentityR M Q e ω L ρ₁ ρ₂ R S

/-- The left-hand side of (6.2): `𝓑[U] + ‖U_x‖²_{L²(I)} + (1 + L)‖U‖²_{L²(I)}`. -/
noncomputable def lhsR (M Q e ω L ρ₁ ρ₂ : ℝ) (R : ℝ → ℂ) : ENNReal :=
  bulkR M Q e ω L R +
    (∫⁻ s in Icc ρ₁ ρ₂, ENNReal.ofReal (‖uxR M Q e ω R s‖ ^ 2 * wR M Q e ω s)) +
    ENNReal.ofReal (1 + L) *
      (∫⁻ s in Icc ρ₁ ρ₂, ENNReal.ofReal (‖uR M Q e ω R s‖ ^ 2 * wR M Q e ω s))

/-- `‖F‖²_{L²(I)}`. -/
noncomputable def srcNormR (M Q e ω ρ₁ ρ₂ : ℝ) (S : ℝ → ℂ) : ENNReal :=
  ∫⁻ s in Icc ρ₁ ρ₂, ENNReal.ofReal (‖srcR M Q e ω S s‖ ^ 2 * wR M Q e ω s)

/-- The bounded-`L` estimate in `r`-form: for every `L₀ ≥ 0` a constant uniform in `0 ≤ L ≤ L₀`,
for solutions satisfying (6.3). -/
def BoundedLR : Prop :=
  ∀ (M Q e ω ρ₁ ρ₂ L₀ : ℝ), Range17 M Q e ω ρ₁ ρ₂ → 0 ≤ L₀ →
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 0 ≤ L → L ≤ L₀ →
      ∀ (S R : ℝ → ℂ) (BH BI : ℂ), SourceProblem M Q e ω L ρ₁ ρ₂ R S BH BI →
        SourceIdentityR M Q e ω L ρ₁ ρ₂ R S →
          lhsR M Q e ω L ρ₁ ρ₂ R ≤ ENNReal.ofReal C * srcNormR M Q e ω ρ₁ ρ₂ S

end ModeStability.AllAngular.P61

end
