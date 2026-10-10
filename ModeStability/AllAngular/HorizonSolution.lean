module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.AllAngular.HorizonUniqueness
public import ModeStability.AllAngular.HorizonSolutionAsymp
public import ModeStability.AllAngular.HorizonSolutionSystem
public import ModeStability.ODE.LinearVolterra

/-!
# The normalized horizon solution `R_H`

Source: the all-angular research notes in preparation, (1.2)–(1.4) and Sections 6, 8. The paper
takes `R_H` from the Frobenius construction at the
nondegenerate horizon.

For `M > 0`, `|Q| ≤ M` and real `e, ω, L` with `K(a) ≠ 0` (non-synchronized horizon, subextremal
or extremal) and `Θ' = K/Δ` on `r > a`, this file proves:

* `exists_horizon_solution`: there is a solution `R` of `(ΔR')' + (K²/Δ − L)R = 0` on `r > a`
  satisfying the horizon condition (1.4) with leading coefficient `1`, i.e.
  `e^{iΘ}R − 1 = O(r − a)` and `(e^{iΘ}R)' = O(1)` as `r ↓ a`;
* `eqOn_of_horizon_solution`: two such solutions agree on `r > a`;
* `existsUnique_horizon_solution`: both together.

## Proof

Existence: choose `c` with `κ = K + cΔ ≠ 0` on `[a, ∞)` (`hs_exists_kap_ne`). The amplitudes
`A = e^{−iΘ}(ΔR' + iκR)`, `B = e^{iΘ}(ΔR' − iκR)` turn the radial equation into a linear system
`(A, B)' = M(r)(A, B)` whose coefficient `M` is continuous on `r > a` and bounded on `(a, a + 1]`
(`HorizonSolutionSystem`). The Volterra existence theorem
`ModeStability.ODE.linear_exists_nhdsGT` gives a solution on `r > a` with `(A, B) → (0, −2iK(a))`
as `r ↓ a`. Then `R = (e^{iΘ}A − e^{−iΘ}B)/(2iκ)` solves the radial equation on `r > a`, and its
horizon amplitudes `e^{∓iΘ}(ΔR' ± iKR)` tend to `0` and `−2iK(a)`, which gives (1.4) with
leading coefficient `1` (`hs_horizon_condition_of_tendsto_amps`; at the extremal horizon via an
integration by parts against `e^{−2iΘ}`).

Uniqueness: the difference of two such solutions satisfies (1.4) with leading coefficient `0`,
so it vanishes by `eqOn_zero_of_horizon_coefficient_zero`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

open InfinityUniqueness

/-- **Uniqueness of the normalized horizon solution.** For `M > 0`, `|Q| ≤ M` and real
`e, ω, L` with `K(a) ≠ 0` (sub- or extremal), any two solutions of the radial equation
`(ΔR')' + (K²/Δ − L)R = 0` on `r > a` satisfying the ingoing horizon condition (1.4) with
leading coefficient `B_H = 1` (`e^{iΘ}R − 1 = O(r − a)`, `(e^{iΘ}R)' = O(1)`, `Θ' = K/Δ`)
agree on `r > a`. -/
theorem eqOn_of_horizon_solution {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hK : radialK e ω (outerHorizon M Q) ≠ 0) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R₁ R₂ : ℝ → ℂ}
    (hR₁ : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R₁ r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R₁ s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R₁ r) r)
    (hH₁ : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R₁ r - 1) =O[𝓝[>] (outerHorizon M Q)]
      (fun r => r - outerHorizon M Q))
    (hH₁' : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R₁ r) =O[𝓝[>] (outerHorizon M Q)]
      (fun _ => (1 : ℝ)))
    (hR₂ : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R₂ r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R₂ s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R₂ r) r)
    (hH₂ : (fun r : ℝ => exp (I * (Θ r : ℂ)) * R₂ r - 1) =O[𝓝[>] (outerHorizon M Q)]
      (fun r => r - outerHorizon M Q))
    (hH₂' : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R₂ r) =O[𝓝[>] (outerHorizon M Q)]
      (fun _ => (1 : ℝ))) :
    EqOn R₁ R₂ (Ioi (outerHorizon M Q)) := by
  set a := outerHorizon M Q with ha
  have hD : ∀ r ∈ Ioi a, DifferentiableAt ℝ (fun s => R₁ s - R₂ s) r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv (fun s => R₁ s - R₂ s) s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * (R₁ r - R₂ r)) r := by
    intro r hr
    refine ⟨(hR₁ r hr).1.sub (hR₂ r hr).1, ?_⟩
    have h := (hR₁ r hr).2.sub (hR₂ r hr).2
    refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
    filter_upwards [Ioi_mem_nhds hr] with s hs
    simp only [Pi.sub_apply]
    rw [deriv_fun_sub (hR₁ s hs).1 (hR₂ s hs).1]
    ring
  have hdiff : ∀ {R : ℝ → ℂ}, (∀ r ∈ Ioi a, DifferentiableAt ℝ R r) → ∀ r ∈ Ioi a,
      DifferentiableAt ℝ (fun s : ℝ => exp (I * (Θ s : ℂ)) * R s) r := fun hR r hr =>
    ((hasDerivAt_exp_phase (M := M) (Q := Q) (hΘ r hr)).mul (hR r hr).hasDerivAt).differentiableAt
  have h1 : (fun r : ℝ => exp (I * (Θ r : ℂ)) * (R₁ r - R₂ r)) =O[𝓝[>] a] (fun r => r - a) :=
    (hH₁.sub hH₂).congr_left fun r => by ring
  have h2 : deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * (R₁ r - R₂ r)) =O[𝓝[>] a]
      (fun _ => (1 : ℝ)) := by
    refine (hH₁'.sub hH₂').congr' ?_ EventuallyEq.rfl
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hfun : (fun r : ℝ => exp (I * (Θ r : ℂ)) * (R₁ r - R₂ r)) =
        fun s => exp (I * (Θ s : ℂ)) * R₁ s - exp (I * (Θ s : ℂ)) * R₂ s := by
      funext s
      ring
    rw [hfun, deriv_fun_sub (hdiff (fun s hs => (hR₁ s hs).1) r hr)
      (hdiff (fun s hs => (hR₂ s hs).1) r hr)]
  have h0 := eqOn_zero_of_horizon_coefficient_zero hM hQ hK hΘ hD h1 h2
  intro r hr
  exact sub_eq_zero.1 (h0 hr)

/-- **Existence of the normalized horizon solution `R_H`.** For `M > 0`, `|Q| ≤ M` and real
`e, ω, L` with `K(a) ≠ 0` (sub- or extremal), and `Θ' = K/Δ` on `r > a`, there is a solution of the
radial equation `(ΔR')' + (K²/Δ − L)R = 0` on `r > a` satisfying the ingoing horizon condition
(1.4) with leading coefficient `B_H = 1`: `e^{iΘ}R − 1 = O(r − a)` and `(e^{iΘ}R)' = O(1)` as
`r ↓ a`. The premises `M > 0`, `|Q| ≤ M` of the source are kept but not used here. -/
theorem exists_horizon_solution {M Q e ω L : ℝ} (_hM : 0 < M) (_hQ : |Q| ≤ M)
    (hK : radialK e ω (outerHorizon M Q) ≠ 0) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r) :
    ∃ R : ℝ → ℂ, (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) ∧
      (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - 1) =O[𝓝[>] (outerHorizon M Q)]
        (fun r => r - outerHorizon M Q) ∧
      deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) =O[𝓝[>] (outerHorizon M Q)]
        (fun _ => (1 : ℝ)) := by
  obtain ⟨c, hc⟩ := hs_exists_kap_ne hK
  set a := outerHorizon M Q with ha
  have hκ : ∀ r ∈ Ioi a, hs_kap M Q e ω c r ≠ 0 := fun r hr => hc r (le_of_lt hr)
  obtain ⟨h11, h12, h21, h22⟩ := hs_continuousOn_coeffs (L := L) hκ hΘ
  obtain ⟨C, hC⟩ := hs_bound_coeffs (L := L) Θ (fun r hr => hc r hr.1)
  have hMc := ModeStability.ODE.continuousOn_mat2 h11 h12 h21 h22
  have hMb : ∀ t ∈ Ioc a (a + 1), ‖ModeStability.ODE.mat2 (hs_m11 M Q e ω L c t)
      (hs_m12 M Q e ω L c Θ t) (hs_m21 M Q e ω L c Θ t) (hs_m22 M Q e ω L c t)‖ ≤ C :=
    fun t ht => (ModeStability.ODE.norm_mat2_le _ _ _ _).trans (hC t ht)
  obtain ⟨v, hv, hvlim, -⟩ := ModeStability.ODE.linear_exists_nhdsGT hMc hMb
    ((0 : ℂ), -(2 * I * (radialK e ω a : ℂ)))
  have hsys : ∀ r ∈ Ioi a,
      HasDerivAt (fun t => (v t).1)
        (hs_m11 M Q e ω L c r * (v r).1 + hs_m12 M Q e ω L c Θ r * (v r).2) r ∧
      HasDerivAt (fun t => (v t).2)
        (hs_m21 M Q e ω L c Θ r * (v r).1 + hs_m22 M Q e ω L c r * (v r).2) r := by
    intro r hr
    have h := hv r hr
    simp only [ModeStability.ODE.mat2_apply] at h
    exact ⟨(ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r h,
      (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r h⟩
  have hA : Tendsto (fun t => (v t).1) (𝓝[>] a) (𝓝 0) :=
    (continuous_fst.tendsto _).comp hvlim
  have hB : Tendsto (fun t => (v t).2) (𝓝[>] a) (𝓝 (-(2 * I * radialK e ω a))) :=
    (continuous_snd.tendsto _).comp hvlim
  exact hs_exists_horizon_solution_of_system hK hκ hΘ hsys hA hB

/-- **Existence and uniqueness of the normalized horizon solution `R_H`.** For `M > 0`,
`|Q| ≤ M` and real `e, ω, L` with `K(a) ≠ 0` (sub- or extremal), and `Θ' = K/Δ` on `r > a`,
there is a solution of `(ΔR')' + (K²/Δ − L)R = 0` on `r > a` satisfying (1.4) with leading
coefficient `1` (`e^{iΘ}R − 1 = O(r − a)`, `(e^{iΘ}R)' = O(1)`), and every other such solution
agrees with it on `r > a`. -/
theorem existsUnique_horizon_solution {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hK : radialK e ω (outerHorizon M Q) ≠ 0) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r) :
    ∃ R : ℝ → ℂ, ((∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) ∧
      (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r - 1) =O[𝓝[>] (outerHorizon M Q)]
        (fun r => r - outerHorizon M Q) ∧
      deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R r) =O[𝓝[>] (outerHorizon M Q)]
        (fun _ => (1 : ℝ))) ∧
      ∀ R' : ℝ → ℂ, ((∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R' r ∧
        HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R' s)
          (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R' r) r) ∧
        (fun r : ℝ => exp (I * (Θ r : ℂ)) * R' r - 1) =O[𝓝[>] (outerHorizon M Q)]
          (fun r => r - outerHorizon M Q) ∧
        deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * R' r) =O[𝓝[>] (outerHorizon M Q)]
          (fun _ => (1 : ℝ))) → EqOn R' R (Ioi (outerHorizon M Q)) := by
  obtain ⟨R, hR, h1, h2⟩ := exists_horizon_solution (L := L) hM hQ hK hΘ
  exact ⟨R, ⟨hR, h1, h2⟩, fun R' ⟨hR', h1', h2'⟩ =>
    eqOn_of_horizon_solution hM hQ hK hΘ hR' h1' h2' hR h1 h2⟩

end ModeStability.AllAngular

end
