module

public import Mathlib
public import ModeStability.Frozen.AllAngular.RadialPhase
public import ModeStability.AllAngular.InfinityUniqueness
public import ModeStability.ODE.LinearStability

/-!
# Continuity in the frequency: the phase and generic parameter estimates

Source: the all-angular research notes in preparation, p. 10. This file collects the
parameter-independent
ingredients of the ω-continuity of the normalized solutions `R_H`, `R_I`
(`ModeStability.AllAngular.horizon_solution_continuous_aux`,
`ModeStability.AllAngular.infinity_solution_continuous_aux`):

* the phase `Θ = radialPhase` of (1.3) has `Θ' = K/Δ` on `r > a`
  (`sc_hasDerivAt_radialPhase`) and is linear in `ω`,
  `Θ(ω, r) = ω ∫_{a+1}^r ρ²/Δ − e ∫_{a+1}^r ρ/Δ` (`sc_radialPhase_eq`), hence jointly continuous
  on `ℝ × (a, ∞)` (`sc_continuousOn_radialPhase`);
* `sc_tendsto_intervalIntegral`: if `‖N ω x‖ ≤ g(ω, x)` on `(s, T]` with `g` jointly continuous on
  `S × [s, T]`, `S` open, and `N ω x` is continuous in `ω`, then
  `∫_s^T ‖N ω − N ω₀‖ → 0` as `ω → ω₀` (dominated convergence with a bound from compactness);
* `sc_continuousOn_of_interior`: continuity in a parameter of solutions of `w' = N(ω, t) w` on
  `(a, ∞)` with data at an interior point `t₀` continuous in `ω` (Grönwall on compact intervals,
  `ModeStability.ODE.norm_sub_le_of_Icc` and `ModeStability.ODE.norm_sub_le_of_Icc_backward`).
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

open InfinityUniqueness

/-! ### The phase `Θ = radialPhase` -/

/-- A primitive from `a + 1` of a function continuous on `r > a` has derivative `f` there. -/
theorem sc_hasDerivAt_primitive {a : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi a)) {r : ℝ}
    (hr : a < r) : HasDerivAt (fun r => ∫ ρ in (a + 1)..r, f ρ) (f r) r := by
  have ha1 : a + 1 ∈ Ioi a := by
    rw [mem_Ioi]
    linarith
  have hsub : uIcc (a + 1) r ⊆ Ioi a := ordConnected_Ioi.uIcc_subset ha1 hr
  exact intervalIntegral.integral_hasDerivAt_right ((hf.mono hsub).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter isOpen_Ioi r hr) (hf.continuousAt (Ioi_mem_nhds hr))

/-- `g/Δ` is continuous on the exterior for continuous `g`. -/
theorem sc_continuousOn_div_delta (M Q : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ContinuousOn (fun ρ => g ρ / delta M Q ρ) (Ioi (outerHorizon M Q)) :=
  hg.continuousOn.div (continuous_delta M Q).continuousOn fun _ hρ => (delta_pos_of_lt hρ).ne'

/-- `Θ' = K/Δ` on the exterior. -/
theorem sc_hasDerivAt_radialPhase (M Q e ω : ℝ) {r : ℝ} (hr : outerHorizon M Q < r) :
    HasDerivAt (radialPhase M Q e ω) (radialK e ω r / delta M Q r) r :=
  sc_hasDerivAt_primitive (sc_continuousOn_div_delta M Q (by unfold radialK; fun_prop)) hr

/-- `∫_{a+1}^r ρ²/Δ`. -/
@[expose] noncomputable def sc_phF (M Q r : ℝ) : ℝ :=
  ∫ ρ in (outerHorizon M Q + 1)..r, ρ ^ 2 / delta M Q ρ

/-- `∫_{a+1}^r ρ/Δ`. -/
@[expose] noncomputable def sc_phG (M Q r : ℝ) : ℝ :=
  ∫ ρ in (outerHorizon M Q + 1)..r, ρ / delta M Q ρ

/-- The phase is linear in `ω`: `Θ(ω, r) = ω ∫_{a+1}^r ρ²/Δ − e ∫_{a+1}^r ρ/Δ` for `r > a`. -/
theorem sc_radialPhase_eq (M Q e ω : ℝ) {r : ℝ} (hr : outerHorizon M Q < r) :
    radialPhase M Q e ω r = ω * sc_phF M Q r - e * sc_phG M Q r := by
  have ha1 : outerHorizon M Q + 1 ∈ Ioi (outerHorizon M Q) := by
    rw [mem_Ioi]
    linarith
  have hsub := ordConnected_Ioi.uIcc_subset ha1 hr
  have hF : IntervalIntegrable (fun ρ => ρ ^ 2 / delta M Q ρ) volume (outerHorizon M Q + 1) r :=
    ((sc_continuousOn_div_delta M Q (continuous_pow 2)).mono hsub).intervalIntegrable
  have hG : IntervalIntegrable (fun ρ => ρ / delta M Q ρ) volume (outerHorizon M Q + 1) r :=
    ((sc_continuousOn_div_delta M Q continuous_id).mono hsub).intervalIntegrable
  unfold radialPhase sc_phF sc_phG
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hF.const_mul ω) (hG.const_mul e)]
  congr 1
  funext ρ
  unfold radialK
  ring

/-- The phase is jointly continuous in `(ω, r)` on `ℝ × (a, ∞)`. -/
theorem sc_continuousOn_radialPhase (M Q e : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => radialPhase M Q e p.1 p.2) (univ ×ˢ Ioi (outerHorizon M Q)) := by
  have hF : ContinuousOn (sc_phF M Q) (Ioi (outerHorizon M Q)) := fun r hr =>
    (sc_hasDerivAt_primitive (sc_continuousOn_div_delta M Q (continuous_pow 2))
      hr).continuousAt.continuousWithinAt
  have hG : ContinuousOn (sc_phG M Q) (Ioi (outerHorizon M Q)) := fun r hr =>
    (sc_hasDerivAt_primitive (sc_continuousOn_div_delta M Q continuous_id)
      hr).continuousAt.continuousWithinAt
  have h : ContinuousOn (fun p : ℝ × ℝ => p.1 * sc_phF M Q p.2 - e * sc_phG M Q p.2)
      (univ ×ˢ Ioi (outerHorizon M Q)) :=
    (continuous_fst.continuousOn.mul (hF.comp continuous_snd.continuousOn fun p hp => hp.2)).sub
      (continuousOn_const.mul (hG.comp continuous_snd.continuousOn fun p hp => hp.2))
  exact h.congr fun p hp => sc_radialPhase_eq M Q e p.1 hp.2

/-- For fixed `r > a`, the phase is continuous in `ω`. -/
theorem sc_continuous_radialPhase_omega (M Q e : ℝ) {r : ℝ} (hr : outerHorizon M Q < r) :
    Continuous (fun ω => radialPhase M Q e ω r) := by
  have h : Continuous (fun ω : ℝ => ω * sc_phF M Q r - e * sc_phG M Q r) := by fun_prop
  exact h.congr fun ω => (sc_radialPhase_eq M Q e ω hr).symm

/-! ### Generic parameter estimates -/

/-- A closed ball around a point of an open subset of `ℝ` inside it. -/
theorem sc_exists_closedBall_subset {S : Set ℝ} (hS : IsOpen S) {ω₀ : ℝ} (hω₀ : ω₀ ∈ S) :
    ∃ η > 0, Metric.closedBall ω₀ η ⊆ S := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hS ω₀ hω₀
  exact ⟨ε / 2, half_pos hε, (Metric.closedBall_subset_ball (half_lt_self hε)).trans hsub⟩

/-- **`∫ ‖N ω − N ω₀‖ → 0` from a jointly continuous majorant.** Let `S ⊆ ℝ` be open, `N ω`
continuous on `(s, T]` for `ω ∈ S`, `‖N ω x‖ ≤ g(ω, x)` there with `g` jointly continuous on
`S × [s, T]`, and `ω ↦ N ω x` continuous on `S` for each `x ∈ (s, T]`. Then
`∫_s^T ‖N ω − N ω₀‖ → 0` as `ω → ω₀` in `S`. -/
theorem sc_tendsto_intervalIntegral {F : Type*} [NormedAddCommGroup F] {S : Set ℝ}
    (hS : IsOpen S) {s T : ℝ} (hsT : s ≤ T) {Nf : ℝ → ℝ → F} {g : ℝ → ℝ → ℝ}
    (hc : ∀ ω ∈ S, ContinuousOn (Nf ω) (Ioc s T))
    (hbd : ∀ ω ∈ S, ∀ x ∈ Ioc s T, ‖Nf ω x‖ ≤ g ω x)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (S ×ˢ Icc s T))
    (hlim : ∀ x ∈ Ioc s T, ContinuousOn (fun ω => Nf ω x) S) {ω₀ : ℝ} (hω₀ : ω₀ ∈ S) :
    Tendsto (fun ω => ∫ x in s..T, ‖Nf ω x - Nf ω₀ x‖) (𝓝[S] ω₀) (𝓝 0) := by
  obtain ⟨η, hη, hsub⟩ := sc_exists_closedBall_subset hS hω₀
  have hK : IsCompact (Metric.closedBall ω₀ η ×ˢ Icc s T) :=
    (isCompact_closedBall ω₀ η).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hg.mono (prod_mono hsub subset_rfl))
  have hgC : ∀ ω ∈ Metric.closedBall ω₀ η, ∀ x ∈ Ioc s T, ‖Nf ω x‖ ≤ C := fun ω hω x hx =>
    (hbd ω (hsub hω) x hx).trans ((le_abs_self _).trans
      (by simpa [Real.norm_eq_abs] using hC (ω, x) ⟨hω, Ioc_subset_Icc_self hx⟩))
  have hball : ∀ᶠ ω in 𝓝[S] ω₀, ω ∈ Metric.closedBall ω₀ η :=
    nhdsWithin_le_nhds (Metric.closedBall_mem_nhds ω₀ hη)
  refine ODE.tendsto_intervalIntegral_norm_sub_of_dominated hsT ?_
    (((hc ω₀ hω₀).aestronglyMeasurable measurableSet_Ioc)) ?_
    (fun x hx => hgC ω₀ (Metric.mem_closedBall_self hη.le) x hx)
    (integrableOn_const (C := C) measure_Ioc_lt_top.ne) fun x hx => ?_
  · filter_upwards [self_mem_nhdsWithin] with ω hω
    exact (hc ω hω).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [hball] with ω hω using hgC ω hω
  · exact ((hlim x hx) ω₀ hω₀).tendsto

/-- Grönwall estimate on `[s, T]` for the difference of two solutions, with a data point
`t₀ ∈ [s, T]`: for `t ∈ [s, T]`,
`‖w t − w₀ t‖ ≤ (‖w t₀ − w₀ t₀‖ + (∫_s^T ‖N − N₀‖) B) exp (∫_s^T ‖N₀‖ + ∫_s^T ‖N − N₀‖)`. -/
theorem sc_norm_sub_le_of_mem_Icc {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] {N N₀ : ℝ → E →L[𝕜] E}
    {w w₀ : ℝ → E} {s T t₀ t B : ℝ} (ht₀ : t₀ ∈ Icc s T) (ht : t ∈ Icc s T)
    (hN : ContinuousOn N (Icc s T)) (hN₀ : ContinuousOn N₀ (Icc s T))
    (hw : ∀ x ∈ Icc s T, HasDerivAt w (N x (w x)) x)
    (hw₀ : ∀ x ∈ Icc s T, HasDerivAt w₀ (N₀ x (w₀ x)) x) (hB : ∀ x ∈ Icc s T, ‖w₀ x‖ ≤ B) :
    ‖w t - w₀ t‖ ≤ (‖w t₀ - w₀ t₀‖ + (∫ x in s..T, ‖N x - N₀ x‖) * B) *
      Real.exp ((∫ x in s..T, ‖N₀ x‖) + ∫ x in s..T, ‖N x - N₀ x‖) := by
  have hsT : s ≤ T := ht.1.trans ht.2
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB t ht)
  have hi : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc s T) → IntervalIntegrable f volume s T :=
    fun hf => (hf.mono (by rw [uIcc_of_le hsT])).intervalIntegrable
  have hNi := hi hN.norm
  have hN₀i := hi hN₀.norm
  have hDi := hi (hN.sub hN₀).norm
  have hnn : ∀ f : ℝ → ℝ, (∀ x, 0 ≤ f x) → ∀ c d, s ≤ c → c ≤ d → d ≤ T →
      IntervalIntegrable f volume s T → ∫ x in c..d, f x ≤ ∫ x in s..T, f x :=
    fun f hf c d hc hcd hd hfi => intervalIntegral.integral_mono_interval hc hcd hd
      (Eventually.of_forall hf) hfi
  have hsub : ∀ c d, s ≤ c → d ≤ T → Icc c d ⊆ Icc s T := fun c d hc hd x hx =>
    ⟨hc.trans hx.1, hx.2.trans hd⟩
  -- the two Grönwall estimates
  have key : ∀ c d, s ≤ c → c ≤ d → d ≤ T → ‖w t - w₀ t‖ ≤
      (‖w t₀ - w₀ t₀‖ + (∫ x in c..d, ‖N x - N₀ x‖) * B) * Real.exp (∫ x in c..d, ‖N x‖) →
      ‖w t - w₀ t‖ ≤ (‖w t₀ - w₀ t₀‖ + (∫ x in s..T, ‖N x - N₀ x‖) * B) *
        Real.exp ((∫ x in s..T, ‖N₀ x‖) + ∫ x in s..T, ‖N x - N₀ x‖) := by
    intro c d hc hcd hd h
    refine h.trans ?_
    have hI := hnn (fun x => ‖N x - N₀ x‖) (fun _ => norm_nonneg _) c d hc hcd hd hDi
    have hK : ∫ x in c..d, ‖N x‖ ≤ (∫ x in s..T, ‖N₀ x‖) + ∫ x in s..T, ‖N x - N₀ x‖ := by
      calc ∫ x in c..d, ‖N x‖ ≤ ∫ x in s..T, ‖N x‖ :=
            hnn (fun x => ‖N x‖) (fun _ => norm_nonneg _) c d hc hcd hd hNi
        _ ≤ ∫ x in s..T, (‖N₀ x‖ + ‖N x - N₀ x‖) :=
            intervalIntegral.integral_mono_on hsT hNi (hN₀i.add hDi)
              fun x _ => norm_le_norm_add_norm_sub' _ _
        _ = _ := intervalIntegral.integral_add hN₀i hDi
    have hI0 : 0 ≤ ∫ x in c..d, ‖N x - N₀ x‖ :=
      intervalIntegral.integral_nonneg hcd fun _ _ => norm_nonneg _
    have hpos : 0 ≤ ‖w t₀ - w₀ t₀‖ + (∫ x in s..T, ‖N x - N₀ x‖) * B :=
      add_nonneg (norm_nonneg _) (mul_nonneg (hI0.trans hI) hB0)
    gcongr
  rcases le_total t₀ t with h | h
  · refine key t₀ t ht₀.1 h ht.2 ?_
    have hs' := hsub t₀ t ht₀.1 ht.2
    exact ODE.norm_sub_le_of_Icc h (hN.mono hs') (hN₀.mono hs') (fun x hx => hw x (hs' hx))
      (fun x hx => hw₀ x (hs' hx)) fun x hx => hB x (hs' hx)
  · refine key t t₀ ht.1 h ht₀.2 ?_
    have hs' := hsub t t₀ ht.1 ht₀.2
    exact ODE.norm_sub_le_of_Icc_backward h (hN.mono hs') (hN₀.mono hs')
      (fun x hx => hw x (hs' hx)) (fun x hx => hw₀ x (hs' hx)) fun x hx => hB x (hs' hx)

/-- **Continuity in a parameter, interior data.** Let `wf ω` (for `ω ∈ S`) solve
`w' = Nf ω w` on `(a, ∞)`, with `Nf ω` continuous there and the data `wf ω t₀` at a fixed
`t₀ > a` continuous in `ω`. If `∫_s^T ‖Nf ω − Nf ω₀‖ → 0` as `ω → ω₀` in `S` for all
`a < s ≤ T`, then `(ω, t) ↦ wf ω t` is continuous on `S ×ˢ (a, ∞)`. -/
theorem sc_continuousOn_of_interior {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] {Λ : Type*} [TopologicalSpace Λ]
    {S : Set Λ} {a t₀ : ℝ} (ht₀ : a < t₀) {Nf : Λ → ℝ → E →L[𝕜] E} {wf : Λ → ℝ → E}
    (hN : ∀ ω ∈ S, ContinuousOn (Nf ω) (Ioi a))
    (hw : ∀ ω ∈ S, ∀ t ∈ Ioi a, HasDerivAt (wf ω) (Nf ω t (wf ω t)) t)
    (hw0 : ContinuousOn (fun ω => wf ω t₀) S)
    (hNc : ∀ ω₀ ∈ S, ∀ s T, a < s → s ≤ T →
      Tendsto (fun ω => ∫ x in s..T, ‖Nf ω x - Nf ω₀ x‖) (𝓝[S] ω₀) (𝓝 0)) :
    ContinuousOn (fun p : Λ × ℝ => wf p.1 p.2) (S ×ˢ Ioi a) := by
  rintro ⟨ω₀, t'⟩ ⟨hω₀, ht'⟩
  have ht'a : a < t' := ht'
  set s := (a + min t' t₀) / 2 with hs_def
  set T := max t' t₀ + 1 with hT_def
  have hm1 : min t' t₀ ≤ t' := min_le_left _ _
  have hm2 : min t' t₀ ≤ t₀ := min_le_right _ _
  have hm3 : a < min t' t₀ := lt_min ht'a ht₀
  have hM1 : t' ≤ max t' t₀ := le_max_left _ _
  have hM2 : t₀ ≤ max t' t₀ := le_max_right _ _
  have has : a < s := by linarith
  have hst' : s < t' := by linarith
  have hst₀ : s < t₀ := by linarith
  have ht'T : t' < T := by linarith
  have ht₀T : t₀ < T := by linarith
  have hsT : s ≤ T := by linarith
  have hsub : Icc s T ⊆ Ioi a := fun x hx => has.trans_le hx.1
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun x hx => (hw ω₀ hω₀ x (hsub hx)).continuousAt.continuousWithinAt :
      ContinuousOn (wf ω₀) (Icc s T))
  refine ODE.ls_continuousWithinAt_of_uniform (Ioo_mem_nhds hst' ht'T)
    (δ := fun ω => (‖wf ω t₀ - wf ω₀ t₀‖ + (∫ x in s..T, ‖Nf ω x - Nf ω₀ x‖) * B) *
      Real.exp ((∫ x in s..T, ‖Nf ω₀ x‖) + ∫ x in s..T, ‖Nf ω x - Nf ω₀ x‖))
    (fun ω hω t _ htU => ?_) ?_ (hw ω₀ hω₀ t' ht').continuousAt
  · exact sc_norm_sub_le_of_mem_Icc ⟨hst₀.le, ht₀T.le⟩ ⟨htU.1.le, htU.2.le⟩
      ((hN ω hω).mono hsub) ((hN ω₀ hω₀).mono hsub) (fun x hx => hw ω hω x (hsub hx))
      (fun x hx => hw ω₀ hω₀ x (hsub hx)) hB
  · have h1 : Tendsto (fun ω => ‖wf ω t₀ - wf ω₀ t₀‖) (𝓝[S] ω₀) (𝓝 0) := by
      simpa using ((hw0 ω₀ hω₀).tendsto.sub_const (wf ω₀ t₀)).norm
    have h2 := hNc ω₀ hω₀ s T has hsT
    simpa using (h1.add (h2.mul_const B)).mul (h2.const_add _).rexp

end ModeStability.AllAngular

end
