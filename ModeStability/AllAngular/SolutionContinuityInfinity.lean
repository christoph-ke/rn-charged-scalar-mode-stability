module

public import Mathlib
public import ModeStability.AllAngular.SolutionContinuityInfinityInterior

/-!
# Joint frequency continuity of normalized outgoing solutions

Source: the all-angular research notes in preparation, p. 10, Proposition 6.1.
For any family satisfying the normalized infinity condition, dominated convergence
and stability of the outgoing amplitude system give continuity on a uniform tail
near each nonzero frequency. Interior stability propagates this to the exterior.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

open InfinityUniqueness InfinitySolution

/-- Every normalized outgoing family has jointly continuous radial Cauchy data. -/
theorem sc_continuousOn_infinity_family {M Q e L : ℝ} (hQ : |Q| ≤ M)
    {R : ℝ → ℝ → ℂ}
    (hR : ∀ ω : ℝ, ω ≠ 0 → IsRadialSolutionL M Q e ω L (R ω))
    (hI : ∀ ω : ℝ, ω ≠ 0 → InfinityConditionL M Q e ω (R ω) 1) :
    ContinuousOn (fun p : ℝ × ℝ => sc_radialPair M Q (R p.1) p.2)
      ({ω : ℝ | ω ≠ 0} ×ˢ Ioi (outerHorizon M Q)) := by
  rintro ⟨ω₀, r₀⟩ ⟨hω₀, hr₀⟩
  obtain ⟨S, hSo, hωS, b, C, hab, hb, hpatch⟩ := sc_infinity_patch (e := e) (L := L) hQ hω₀
  have hθ : ∀ ω ∈ S, ∀ r ∈ Ioi b, phaseRate M Q e ω r ≠ 0 :=
    fun ω hω r hr => ((hpatch ω hω).2 r hr).1
  have hMc := sc_continuousOn_MI (L := L) hab hb hθ
  have hMt : ∀ ω ∈ S, ContinuousOn (sc_MI M Q e L ω) (Ioi b) := fun ω hω =>
    hMc.comp (f := fun r : ℝ => (ω, r))
      (continuous_const.prodMk continuous_id).continuousOn (fun r hr => ⟨hω, hr⟩)
  obtain ⟨hMi, hMlim⟩ := sc_tail_stability_data hab hb (fun ω hω => (hpatch ω hω).2)
  have hvc := ODE.continuousOn_of_atTop hMt
    (fun ω hω r hr => sc_hasDerivAt_amps hQ (hab.trans_lt hr) (hb.trans hr)
      (hθ ω hω r hr) (hR ω (hpatch ω hω).1))
    (fun ω hω => sc_tendsto_amps_one hQ (hR ω (hpatch ω hω).1) (hI ω (hpatch ω hω).1))
    hMi (by
      have h : Continuous (fun ω : ℝ => ((2 * I * ω, 0) : ℂ × ℂ)) := by fun_prop
      exact h.continuousOn) hMlim
  have htail := sc_continuousOn_radialPair_tail hb hθ hvc hab
  have hNc := sc_continuousOn_NI M Q e L
  have hNt : ∀ ω ∈ S, ContinuousOn (sc_NI M Q e L ω) (Ioi (outerHorizon M Q)) :=
    fun ω _ => hNc.comp (f := fun r : ℝ => (ω, r))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun r hr => ⟨mem_univ _, hr⟩)
  have hNlim : ∀ ω₁ ∈ S, ∀ s T, outerHorizon M Q < s → s ≤ T →
      Tendsto (fun ω => ∫ x in s..T, ‖sc_NI M Q e L ω x - sc_NI M Q e L ω₁ x‖)
        (𝓝[S] ω₁) (𝓝 0) := by
    intro ω₁ hω₁ s T hs hsT
    exact sc_tendsto_intervalIntegral hSo hsT
      (fun ω hω => (hNt ω hω).mono (fun x hx => hs.trans hx.1))
      (fun ω _ x _ => le_rfl)
      (hNc.norm.mono (fun p hp => ⟨mem_univ _, hs.trans_le hp.2.1⟩))
      (fun x hx => hNc.comp (f := fun ω : ℝ => (ω, x))
        (continuous_id.prodMk continuous_const).continuousOn
        (fun ω _ => ⟨mem_univ _, hs.trans hx.1⟩)) hω₁
  have hglob := sc_continuousOn_of_interior (hab.trans_lt (lt_add_one b)) hNt
    (fun ω hω r hr => sc_hasDerivAt_radialPair (hR ω (hpatch ω hω).1) hr)
    (htail.comp (f := fun ω : ℝ => (ω, b + 1)) (continuous_id.prodMk continuous_const).continuousOn
      (fun ω hω => ⟨hω, lt_add_one b⟩)) hNlim
  exact (hglob.continuousAt ((hSo.prod isOpen_Ioi).mem_nhds ⟨hωS, hr₀⟩)).continuousWithinAt

/-- Existence of a normalized outgoing family, jointly continuous with its radial derivative. -/
theorem sc_exists_infinity_continuous :
    ∀ (M Q e L : ℝ), 0 < M → |Q| ≤ M → 0 ≤ L →
      ∃ RI : ℝ → ℝ → ℂ,
        (∀ ω : ℝ, ω ≠ 0 →
          IsRadialSolutionL M Q e ω L (RI ω) ∧ InfinityConditionL M Q e ω (RI ω) 1) ∧
        ContinuousOn (fun p : ℝ × ℝ => RI p.1 p.2)
          ({ω : ℝ | ω ≠ 0} ×ˢ Ioi (outerHorizon M Q)) ∧
        ContinuousOn (fun p : ℝ × ℝ => deriv (RI p.1) p.2)
          ({ω : ℝ | ω ≠ 0} ×ˢ Ioi (outerHorizon M Q)) := by
  intro M Q e L hM hQ _
  classical
  have hex : ∀ ω : ℝ, ∃ R : ℝ → ℂ, ω ≠ 0 →
      IsRadialSolutionL M Q e ω L R ∧ InfinityConditionL M Q e ω R 1 := by
    intro ω
    by_cases hω : ω ≠ 0
    · obtain ⟨R, hR, h1, h2⟩ := exists_infinity_solution (L := L) hM hQ hω
        (fun r hr => sc_hasDerivAt_radialPhase M Q e ω hr)
      exact ⟨R, fun _ => ⟨hR, h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h => (hω h).elim⟩
  choose RI hRI using hex
  have hc := sc_continuousOn_infinity_family hQ (fun ω hω => (hRI ω hω).1)
    (fun ω hω => (hRI ω hω).2)
  refine ⟨RI, hRI, continuous_fst.comp_continuousOn hc, ?_⟩
  have hd : Continuous (fun p : ℝ × ℝ => (delta M Q p.2 : ℂ)) :=
    continuous_ofReal.comp ((continuous_delta M Q).comp continuous_snd)
  have h := (continuous_snd.comp_continuousOn hc).div hd.continuousOn
    (fun p hp => ofReal_ne_zero.2 (delta_pos_of_lt hp.2).ne')
  exact h.congr (fun p hp => (mul_div_cancel_left₀ _
    (ofReal_ne_zero.2 (delta_pos_of_lt hp.2).ne')).symm)

end ModeStability.AllAngular

end
