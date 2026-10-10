module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityExtReciprocalAux
public import ModeStability.AllAngular.CoordinateCoefficientsAux

/-!
# The extremal reciprocal reduction with an `L²` source

Source: the all-angular research notes in preparation, (6.1) and (6.3),
and the `r` form after Proposition 6.1. The integrated radial equation gives
`U = R/g`, `Ux = Δg² ∂ᵣU`, and
`∂ᵣUx = w(-g⁴(K²-LΔ)U + Δg³S)` almost everywhere. The transformed flux
is locally absolutely continuous, as required to integrate the current.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

private theorem ser_reduced_derivative {M Q : ℝ} (hQ : |Q| = M) {R : ℝ → ℂ}
    {r : ℝ} (hr : outerHorizon M Q < r) (hR : DifferentiableAt ℝ R r) :
    (delta M Q r * ser_g M r ^ 2 : ℂ) *
        deriv (fun s => R s / (ser_g M s : ℂ)) r =
      (ser_g M r : ℂ) * ((delta M Q r : ℂ) * deriv R r) + R r := by
  have hg := ser_g_derivative hQ hr
  have hg0 : (ser_g M r : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ser_g_pos hQ hr).ne'
  have hp0 : (delta M Q r : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (NormalizationFacts.delta_pos_of_outerHorizon_lt hr).ne'
  rw [(hR.hasDerivAt.fun_div hg.ofReal_comp hg0).deriv]
  push_cast
  field_simp
  ring

/-- The integrated reciprocal source reduction, with the exact frozen `g`, the estimate's
`Ux`, and the physical source `Δg³S`. No pointwise second derivative is assumed. -/
theorem ser_reduction {M Q e ω L : ℝ}
    (hQ : |Q| = M) (hN : 2 * M ≤ e / ω) {R S : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    (hS : ∀ b ∈ Ioi (outerHorizon M Q), ∀ c ∈ Ioi (outerHorizon M Q),
      IntervalIntegrable S volume b c)
    (hint : ∀ b ∈ Ioi (outerHorizon M Q), ∀ c ∈ Ioi (outerHorizon M Q),
      (delta M Q c : ℂ) * deriv R c - (delta M Q b : ℂ) * deriv R b =
        ∫ r in b..c, S r - (((radialK e ω r ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r)) :
    let g := normalizationG M Q e ω
    let U := fun r => R r / (g r : ℂ)
    let Ux := fun r => ((delta M Q r * g r ^ 2 : ℝ) : ℂ) * deriv U r
    ContDiffOn ℝ 1 U (Ioi (outerHorizon M Q)) ∧
      ∀ b ∈ Ioi (outerHorizon M Q), ∀ c ∈ Ioi (outerHorizon M Q),
        AbsolutelyContinuousOnInterval Ux b c ∧
          ∀ᵐ r, r ∈ uIcc b c → HasDerivAt Ux
            (((1 / (delta M Q r * g r ^ 2) : ℝ) : ℂ) *
              (-((g r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r) : ℝ) : ℂ) * U r +
                ((delta M Q r * g r ^ 3 : ℝ) : ℂ) * S r)) r := by
  rw [ser_normalization hQ hN]
  dsimp only
  let q : ℝ → ℝ := fun r => radialK e ω r ^ 2 / delta M Q r - L
  have hp : ContinuousOn (delta M Q) (Ioi (outerHorizon M Q)) := by
    unfold delta
    fun_prop
  have hp0 : ∀ r ∈ Ioi (outerHorizon M Q), delta M Q r ≠ 0 :=
    fun r hr => (NormalizationFacts.delta_pos_of_outerHorizon_lt hr).ne'
  have hq : ContinuousOn q (Ioi (outerHorizon M Q)) := by
    have hk : Continuous (radialK e ω) := by unfold radialK; fun_prop
    exact ((hk.pow 2).continuousOn.div hp hp0).sub continuousOn_const
  have hRC : ContDiffOn ℝ 1 R (Ioi (outerHorizon M Q)) :=
    source_solution_contDiffOn_one hp hp0 hq hR hS hint
  have hgC : ContDiffOn ℝ 1 (ser_g M) (Ioi (outerHorizon M Q)) :=
    fun r hr => ((ser_g_smooth hQ hr).of_le
      (by norm_num)).contDiffWithinAt
  have hgcC : ContDiffOn ℝ 1 (fun r => (ser_g M r : ℂ))
      (Ioi (outerHorizon M Q)) :=
    Complex.ofRealCLM.contDiff.contDiffOn.comp hgC (fun _ _ => mem_univ _)
  have hUC : ContDiffOn ℝ 1 (fun r => R r / (ser_g M r : ℂ))
      (Ioi (outerHorizon M Q)) := by
    have hInv := hgcC.inv (fun r hr =>
      ofReal_ne_zero.mpr (ser_g_pos hQ hr).ne')
    apply (hRC.mul hInv).congr
    intro r hr
    simp only [Pi.inv_apply, div_eq_mul_inv]
  refine ⟨hUC, ?_⟩
  intro b hb c hc
  have hsub : uIcc b c ⊆ Ioi (outerHorizon M Q) :=
    fun r hr => (lt_min hb hc).trans_le hr.1
  let V : ℝ → ℂ := fun r => (ser_g M r : ℂ) * ((delta M Q r : ℂ) * deriv R r) + R r
  have hVeq : EqOn (fun r => ((delta M Q r * ser_g M r ^ 2 : ℝ) : ℂ) *
      deriv (fun s => R s / (ser_g M s : ℂ)) r) V
      (Ioi (outerHorizon M Q)) :=
    fun r hr => by
      simpa only [ofReal_mul, ofReal_pow] using ser_reduced_derivative hQ hr (hR r hr)
  have hVac : AbsolutelyContinuousOnInterval V b c :=
    ((hgcC.mono hsub).absolutelyContinuousOnInterval.smul
      (source_complex_flux_absolutelyContinuous hq hR hS hint hb hc)).add
        (hRC.mono hsub).absolutelyContinuousOnInterval
  refine ⟨hVac.congr (fun r hr => (hVeq (hsub hr)).symm), ?_⟩
  filter_upwards [source_flux_hasDerivAt_ae hq hR hS hint hb hc] with r hr hmem
  have hra := hsub hmem
  have hg := ser_g_derivative hQ hra
  have hd := (source_reduction_at (hp0 r hra) (ser_g_pos hQ hra).ne'
    hg (hR r hra) (hr hmem)).2
  have hdV : HasDerivAt V
      (((1 / (delta M Q r * ser_g M r ^ 2) : ℝ) : ℂ) *
        (-((ser_g M r ^ 4 * delta M Q r * q r : ℝ) : ℂ) *
            (R r / (ser_g M r : ℂ)) +
          ((delta M Q r * ser_g M r ^ 3 : ℝ) : ℂ) * S r)) r := by
    simpa only [ofReal_neg, ofReal_one, neg_one_mul, sub_neg_eq_add] using hd
  have hcoeff : ser_g M r ^ 4 * delta M Q r * q r =
      ser_g M r ^ 4 * (radialK e ω r ^ 2 - L * delta M Q r) := by
    dsimp [q]
    field_simp [hp0 r hra]
  rw [hcoeff] at hdV
  apply hdV.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hra] with s hs
  exact hVeq hs

end ModeStability.AllAngular

end
