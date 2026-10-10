module

public import Mathlib
public import ModeStability.Frozen.AllAngular.RadialPhase
public import ModeStability.AllAngular.HorizonSolution
public import ModeStability.AllAngular.SolutionContinuityAux

/-!
# Continuity in the frequency of the horizon amplitude family

Source: the all-angular research notes in preparation, p. 10. This file carries out the horizon
half for the
construction of `ModeStability.AllAngular.exists_horizon_solution`, with `ω` as a parameter on the
open set `S = {ω | K(a) ≠ 0}`.

The construction uses `κ = K + cΔ` with `c(ω) = (|K(a)ω| + K'(a)²)/K(a)` (`sc_cH`, the choice of
`hs_exists_kap_ne`, continuous on `S`; `sc_kap_ne`), the phase `Θ = radialPhase`, and the
amplitude system `sc_MH` of `ModeStability.AllAngular.HorizonSolutionSystem`. Its coefficients are
bounded by `sc_gH`, jointly continuous on `S × [a, ∞)`, so dominated convergence gives
`∫_a^t ‖M_ω − M_ω₀‖ → 0` (`sc_tendsto_MH`), and `ModeStability.ODE.continuousOn_of_nhdsGT` gives
the
joint continuity of the Volterra solutions with data `(0, −2iK(a))` at `a⁺`
(`sc_continuousOn_horizon_amp`). Finally `sc_horizon_condition_sysR` is the horizon asymptotics of
`hs_exists_horizon_solution_of_system` for the explicit solution
`R = (e^{iΘ}A − e^{−iΘ}B)/(2iκ)`.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

open InfinityUniqueness

/-! ### The choice of `c` -/

/-- `c(ω) = (|K(a)ω| + K'(a)²)/K(a)`, the choice of `hs_exists_kap_ne`. -/
@[expose] noncomputable def sc_cH (M Q e ω : ℝ) : ℝ :=
  (|radialK e ω (outerHorizon M Q) * ω| + (2 * ω * outerHorizon M Q - e) ^ 2) /
    radialK e ω (outerHorizon M Q)

/-- `κ = K + c(ω)Δ ≠ 0` on `[a, ∞)` when `K(a) ≠ 0`. -/
theorem sc_kap_ne {M Q e ω : ℝ} (hK : radialK e ω (outerHorizon M Q) ≠ 0) {r : ℝ}
    (hr : outerHorizon M Q ≤ r) : hs_kap M Q e ω (sc_cH M Q e ω) r ≠ 0 := by
  set a := outerHorizon M Q with ha
  set k₀ := radialK e ω a with hk₀
  set k₁ := 2 * ω * a - e with hk₁
  have hc : sc_cH M Q e ω = (|k₀ * ω| + k₁ ^ 2) / k₀ := rfl
  rw [hc]
  have hba := hs_innerHorizon_le M Q
  set x := r - a with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  have hKr : radialK e ω r = k₀ + k₁ * x + ω * x ^ 2 := by
    rw [hk₀, hk₁, hx]
    unfold radialK
    ring
  have hΔ : x ^ 2 ≤ delta M Q r := by
    have hd : delta M Q r = x * (x + (a - innerHorizon M Q)) := by
      rw [hx]
      unfold delta
      ring
    rw [hd]
    nlinarith [mul_nonneg hx0 (show 0 ≤ a - innerHorizon M Q by linarith)]
  have hmul : k₀ * hs_kap M Q e ω ((|k₀ * ω| + k₁ ^ 2) / k₀) r =
      k₀ * radialK e ω r + (|k₀ * ω| + k₁ ^ 2) * delta M Q r := by
    unfold hs_kap
    field_simp
  have hpos : 0 < k₀ * hs_kap M Q e ω ((|k₀ * ω| + k₁ ^ 2) / k₀) r := by
    rw [hmul, hKr]
    have h1 : (|k₀ * ω| + k₁ ^ 2) * x ^ 2 ≤ (|k₀ * ω| + k₁ ^ 2) * delta M Q r :=
      mul_le_mul_of_nonneg_left hΔ (by positivity)
    have h2 : -(k₀ * ω) ≤ |k₀ * ω| := neg_le_abs _
    have h3 : 0 < k₀ ^ 2 := by positivity
    nlinarith [sq_nonneg (k₀ + 2 * k₁ * x), mul_le_mul_of_nonneg_right h2 (sq_nonneg x)]
  intro h0
  rw [h0, mul_zero] at hpos
  exact lt_irrefl 0 hpos

/-- `ω ↦ K(a)` is continuous. -/
theorem sc_continuous_radialK_omega (e r : ℝ) : Continuous (fun ω => radialK e ω r) := by
  unfold radialK
  fun_prop

/-- `S = {ω | K(a) ≠ 0}` is open. -/
theorem sc_isOpen_horizonSet (M Q e : ℝ) :
    IsOpen {ω : ℝ | radialK e ω (outerHorizon M Q) ≠ 0} :=
  isOpen_ne_fun (sc_continuous_radialK_omega e _) continuous_const

/-- `c(ω)` is continuous on `S`. -/
theorem sc_continuousOn_cH (M Q e : ℝ) :
    ContinuousOn (sc_cH M Q e) {ω | radialK e ω (outerHorizon M Q) ≠ 0} := by
  have hK := sc_continuous_radialK_omega e (outerHorizon M Q)
  have hN : Continuous (fun ω => |radialK e ω (outerHorizon M Q) * ω| +
      (2 * ω * outerHorizon M Q - e) ^ 2) := by
    unfold radialK
    fun_prop
  exact hN.continuousOn.div hK.continuousOn fun ω hω => hω

/-! ### Joint continuity of the coefficients -/

/-- `κ(ω, r) = K + c(ω)Δ` is jointly continuous on `S × ℝ`. -/
theorem sc_continuousOn_kapH (M Q e : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => hs_kap M Q e p.1 (sc_cH M Q e p.1) p.2)
      ({ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ univ) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => sc_cH M Q e p.1)
      ({ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ univ) :=
    (sc_continuousOn_cH M Q e).comp continuous_fst.continuousOn fun p hp => hp.1
  have hK : Continuous (fun p : ℝ × ℝ => radialK e p.1 p.2) := by
    unfold radialK
    fun_prop
  exact hK.continuousOn.add (hc.mul ((continuous_delta M Q).comp continuous_snd).continuousOn)

/-- `α₊`, `α₋` are jointly continuous on `S × [a, ∞)`. -/
theorem sc_continuousOn_alphaH (M Q e L : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => hs_alphaP M Q e p.1 L (sc_cH M Q e p.1) p.2)
      ({ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ Ici (outerHorizon M Q)) ∧
    ContinuousOn (fun p : ℝ × ℝ => hs_alphaM M Q e p.1 L (sc_cH M Q e p.1) p.2)
      ({ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ Ici (outerHorizon M Q)) := by
  set T := {ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ Ici (outerHorizon M Q) with hT
  have hc : ContinuousOn (fun p : ℝ × ℝ => sc_cH M Q e p.1) T :=
    (sc_continuousOn_cH M Q e).comp continuous_fst.continuousOn fun p hp => hp.1
  have hK : Continuous (fun p : ℝ × ℝ => radialK e p.1 p.2) := by
    unfold radialK
    fun_prop
  have hN : ContinuousOn (fun p : ℝ × ℝ => ((L + sc_cH M Q e p.1 * radialK e p.1 p.2 : ℝ) : ℂ))
      T := continuous_ofReal.comp_continuousOn (continuousOn_const.add (hc.mul hK.continuousOn))
  have hD : ContinuousOn (fun p : ℝ × ℝ => (hs_kapD M e p.1 (sc_cH M Q e p.1) p.2 : ℂ)) T := by
    refine continuous_ofReal.comp_continuousOn ?_
    have h1 : Continuous (fun p : ℝ × ℝ => 2 * p.1 * p.2 - e) := by fun_prop
    have h2 : Continuous (fun p : ℝ × ℝ => 2 * p.2 - 2 * M) := by fun_prop
    exact h1.continuousOn.add (hc.mul h2.continuousOn)
  have hk : ContinuousOn (fun p : ℝ × ℝ => 2 * I * (hs_kap M Q e p.1 (sc_cH M Q e p.1) p.2 : ℂ))
      T := continuousOn_const.mul (continuous_ofReal.comp_continuousOn
        ((sc_continuousOn_kapH M Q e).mono fun p hp => ⟨hp.1, mem_univ _⟩))
  have hne : ∀ p ∈ T, 2 * I * (hs_kap M Q e p.1 (sc_cH M Q e p.1) p.2 : ℂ) ≠ 0 :=
    fun p hp => hs_two_I_mul_ne_zero (sc_kap_ne hp.1 hp.2)
  exact ⟨(hN.add (continuousOn_const.mul hD)).div hk hne,
    (hN.sub (continuousOn_const.mul hD)).div hk hne⟩

/-! ### The amplitude system with `ω` as a parameter -/

/-- The coefficient of the horizon amplitude system (`hs_m11`, …, `hs_m22`) with `c = c(ω)` and
`Θ = radialPhase`. -/
@[expose] noncomputable def sc_MH (M Q e L ω t : ℝ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  ODE.mat2 (hs_m11 M Q e ω L (sc_cH M Q e ω) t)
    (hs_m12 M Q e ω L (sc_cH M Q e ω) (radialPhase M Q e ω) t)
    (hs_m21 M Q e ω L (sc_cH M Q e ω) (radialPhase M Q e ω) t)
    (hs_m22 M Q e ω L (sc_cH M Q e ω) t)

/-- The majorant `‖m₁₁‖ + ‖m₁₂‖ + ‖m₂₁‖ + ‖m₂₂‖` without the unimodular phases. -/
@[expose] noncomputable def sc_gH (M Q e L ω r : ℝ) : ℝ :=
  ‖hs_alphaP M Q e ω L (sc_cH M Q e ω) r + I * (sc_cH M Q e ω : ℂ) / 2‖ +
    ‖I * (sc_cH M Q e ω : ℂ) / 2 - hs_alphaP M Q e ω L (sc_cH M Q e ω) r‖ +
    ‖hs_alphaM M Q e ω L (sc_cH M Q e ω) r - I * (sc_cH M Q e ω : ℂ) / 2‖ +
    ‖hs_alphaM M Q e ω L (sc_cH M Q e ω) r + I * (sc_cH M Q e ω : ℂ) / 2‖

theorem sc_norm_MH_le (M Q e L ω t : ℝ) : ‖sc_MH M Q e L ω t‖ ≤ sc_gH M Q e L ω t := by
  refine (ODE.norm_mat2_le _ _ _ _).trans (le_of_eq ?_)
  have e12 : ‖hs_m12 M Q e ω L (sc_cH M Q e ω) (radialPhase M Q e ω) t‖ =
      ‖I * (sc_cH M Q e ω : ℂ) / 2 - hs_alphaP M Q e ω L (sc_cH M Q e ω) t‖ := by
    simp only [hs_m12, norm_mul, norm_exp_neg_I_mul, mul_one]
  have e21 : ‖hs_m21 M Q e ω L (sc_cH M Q e ω) (radialPhase M Q e ω) t‖ =
      ‖hs_alphaM M Q e ω L (sc_cH M Q e ω) t - I * (sc_cH M Q e ω : ℂ) / 2‖ := by
    simp only [hs_m21, norm_mul, norm_exp_I_mul, mul_one]
  have e22 : ‖hs_m22 M Q e ω L (sc_cH M Q e ω) t‖ =
      ‖hs_alphaM M Q e ω L (sc_cH M Q e ω) t + I * (sc_cH M Q e ω : ℂ) / 2‖ := by
    simp only [hs_m22, norm_neg]
  rw [e12, e21, e22]
  rfl

/-- The majorant is jointly continuous on `S × [a, ∞)`. -/
theorem sc_continuousOn_gH (M Q e L : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => sc_gH M Q e L p.1 p.2)
      ({ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ Ici (outerHorizon M Q)) := by
  obtain ⟨hP, hM⟩ := sc_continuousOn_alphaH M Q e L
  have hc : ContinuousOn (fun p : ℝ × ℝ => I * (sc_cH M Q e p.1 : ℂ) / 2)
      ({ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ Ici (outerHorizon M Q)) :=
    (continuousOn_const.mul (continuous_ofReal.comp_continuousOn
      ((sc_continuousOn_cH M Q e).comp continuous_fst.continuousOn fun p hp => hp.1))).div_const 2
  exact ((((hP.add hc).norm.add (hc.sub hP).norm).add (hM.sub hc).norm).add (hM.add hc).norm)

/-- For fixed `x > a`, `ω ↦ M(ω, x)` is continuous on `S`. -/
theorem sc_continuousOn_MH_omega (M Q e L : ℝ) {x : ℝ} (hx : outerHorizon M Q < x) :
    ContinuousOn (fun ω => sc_MH M Q e L ω x) {ω | radialK e ω (outerHorizon M Q) ≠ 0} := by
  set S := {ω | radialK e ω (outerHorizon M Q) ≠ 0}
  obtain ⟨hP, hM⟩ := sc_continuousOn_alphaH M Q e L
  have hmap : MapsTo (fun ω : ℝ => (ω, x)) S (S ×ˢ Ici (outerHorizon M Q)) :=
    fun ω hω => ⟨hω, le_of_lt hx⟩
  have hpx : ContinuousOn (fun ω : ℝ => (ω, x)) S :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hP' := hP.comp hpx hmap
  have hM' := hM.comp hpx hmap
  have hc : ContinuousOn (fun ω => I * (sc_cH M Q e ω : ℂ) / 2) S :=
    (continuousOn_const.mul (continuous_ofReal.comp_continuousOn
      (sc_continuousOn_cH M Q e))).div_const 2
  have hΘ : Continuous (fun ω => (radialPhase M Q e ω x : ℂ)) :=
    continuous_ofReal.comp (sc_continuous_radialPhase_omega M Q e hx)
  have hE : Continuous (fun ω => exp (I * (radialPhase M Q e ω x : ℂ))) := by fun_prop
  have hEi : Continuous (fun ω => exp (-(I * (radialPhase M Q e ω x : ℂ)))) := by fun_prop
  exact ODE.continuousOn_mat2 (hP'.add hc) ((hc.sub hP').mul (hEi.mul hEi).continuousOn)
    ((hM'.sub hc).mul (hE.mul hE).continuousOn) (hM'.add hc).neg

/-- For `ω ∈ S`, the coefficient is continuous on `r > a`. -/
theorem sc_continuousOn_MH {M Q e L ω : ℝ} (hK : radialK e ω (outerHorizon M Q) ≠ 0) :
    ContinuousOn (sc_MH M Q e L ω) (Ioi (outerHorizon M Q)) := by
  obtain ⟨h11, h12, h21, h22⟩ := hs_continuousOn_coeffs (L := L)
    (fun r hr => sc_kap_ne hK (le_of_lt hr)) (fun r hr => sc_hasDerivAt_radialPhase M Q e ω hr)
  exact ODE.continuousOn_mat2 h11 h12 h21 h22

/-- For `ω ∈ S`, the coefficient is bounded on `(a, a + 1]`. -/
theorem sc_bound_MH {M Q e L ω : ℝ} (hK : radialK e ω (outerHorizon M Q) ≠ 0) :
    ∃ C, ∀ t ∈ Ioc (outerHorizon M Q) (outerHorizon M Q + 1), ‖sc_MH M Q e L ω t‖ ≤ C := by
  obtain ⟨C, hC⟩ := hs_bound_coeffs (L := L) (radialPhase M Q e ω)
    (fun r hr => sc_kap_ne hK hr.1)
  exact ⟨C, fun t ht => (ODE.norm_mat2_le _ _ _ _).trans (hC t ht)⟩

/-- `∫_a^t ‖M_ω − M_ω₀‖ → 0` as `ω → ω₀` in `S`. -/
theorem sc_tendsto_MH (M Q e L : ℝ) :
    ∀ ω₀ ∈ {ω : ℝ | radialK e ω (outerHorizon M Q) ≠ 0}, ∀ t ∈ Ioi (outerHorizon M Q),
      Tendsto (fun ω => ∫ x in (outerHorizon M Q)..t, ‖sc_MH M Q e L ω x - sc_MH M Q e L ω₀ x‖)
        (𝓝[{ω : ℝ | radialK e ω (outerHorizon M Q) ≠ 0}] ω₀) (𝓝 0) := by
  intro ω₀ hω₀ t ht
  exact sc_tendsto_intervalIntegral (sc_isOpen_horizonSet M Q e) (le_of_lt ht)
    (fun ω hω => (sc_continuousOn_MH hω).mono Ioc_subset_Ioi_self)
    (fun ω _ x _ => sc_norm_MH_le M Q e L ω x)
    ((sc_continuousOn_gH M Q e L).mono (prod_mono subset_rfl fun x hx => hx.1))
    (fun x hx => sc_continuousOn_MH_omega M Q e L hx.1) hω₀

/-- The Volterra solutions of the amplitude system with data `(0, −2iK(a))` at `a⁺`, for all
`ω ∈ S` at once. -/
theorem sc_exists_horizon_amp (M Q e L : ℝ) :
    ∃ v : ℝ → ℝ → ℂ × ℂ, ∀ ω, radialK e ω (outerHorizon M Q) ≠ 0 →
      (∀ t ∈ Ioi (outerHorizon M Q), HasDerivAt (v ω) (sc_MH M Q e L ω t (v ω t)) t) ∧
        Tendsto (v ω) (𝓝[>] (outerHorizon M Q))
          (𝓝 ((0 : ℂ), -(2 * I * (radialK e ω (outerHorizon M Q) : ℂ)))) := by
  have h : ∀ ω, ∃ w : ℝ → ℂ × ℂ, radialK e ω (outerHorizon M Q) ≠ 0 →
      (∀ t ∈ Ioi (outerHorizon M Q), HasDerivAt w (sc_MH M Q e L ω t (w t)) t) ∧
        Tendsto w (𝓝[>] (outerHorizon M Q))
          (𝓝 ((0 : ℂ), -(2 * I * (radialK e ω (outerHorizon M Q) : ℂ)))) := by
    intro ω
    by_cases hK : radialK e ω (outerHorizon M Q) ≠ 0
    · obtain ⟨C, hC⟩ := sc_bound_MH (L := L) hK
      obtain ⟨w, hw, hwl, -⟩ := ODE.linear_exists_nhdsGT (sc_continuousOn_MH hK) hC
        ((0 : ℂ), -(2 * I * (radialK e ω (outerHorizon M Q) : ℂ)))
      exact ⟨w, fun _ => ⟨hw, hwl⟩⟩
    · exact ⟨0, fun h => absurd h hK⟩
  choose v hv using h
  exact ⟨v, hv⟩

/-- **Joint continuity of the horizon amplitudes** on `S × (a, ∞)`. -/
theorem sc_continuousOn_horizon_amp {M Q e L : ℝ} {v : ℝ → ℝ → ℂ × ℂ}
    (hv : ∀ ω, radialK e ω (outerHorizon M Q) ≠ 0 →
      (∀ t ∈ Ioi (outerHorizon M Q), HasDerivAt (v ω) (sc_MH M Q e L ω t (v ω t)) t) ∧
        Tendsto (v ω) (𝓝[>] (outerHorizon M Q))
          (𝓝 ((0 : ℂ), -(2 * I * (radialK e ω (outerHorizon M Q) : ℂ))))) :
    ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2)
      ({ω | radialK e ω (outerHorizon M Q) ≠ 0} ×ˢ Ioi (outerHorizon M Q)) := by
  have hv0 : ContinuousOn (fun ω : ℝ => ((0 : ℂ), -(2 * I * (radialK e ω (outerHorizon M Q) : ℂ))))
      {ω | radialK e ω (outerHorizon M Q) ≠ 0} := by
    have h := sc_continuous_radialK_omega e (outerHorizon M Q)
    exact (continuous_const.prodMk (continuous_const.mul
      (continuous_ofReal.comp h)).neg).continuousOn
  refine ODE.continuousOn_of_nhdsGT (fun ω hω => sc_continuousOn_MH hω) (fun ω hω => (hv ω hω).1)
    (fun ω hω => (hv ω hω).2) (fun ω hω t _ => ?_) hv0 (sc_tendsto_MH M Q e L)
  obtain ⟨C, hC⟩ := sc_bound_MH (L := L) hω
  exact ODE.lv_integrableOn_Ioc_of_bdd (sc_continuousOn_MH hω) hC t

/-! ### The horizon asymptotics of the explicit solution -/

/-- **The horizon condition for `R = (e^{iΘ}A − e^{−iΘ}B)/(2iκ)`.** The explicit form of
`hs_exists_horizon_solution_of_system`: if `κ ≠ 0` on `r > a` and `(A, B)` solves the system on
`r > a` with `A → 0`, `B → −2iK(a)`, then `hs_sysR` solves the radial equation on `r > a` and
satisfies (1.4) with leading coefficient `1`. -/
theorem sc_horizon_condition_sysR {M Q e ω L c : ℝ}
    (hK : radialK e ω (outerHorizon M Q) ≠ 0)
    (hκ : ∀ r ∈ Ioi (outerHorizon M Q), hs_kap M Q e ω c r ≠ 0) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {A B : ℝ → ℂ}
    (hsys : ∀ r ∈ Ioi (outerHorizon M Q),
      HasDerivAt A (hs_m11 M Q e ω L c r * A r + hs_m12 M Q e ω L c Θ r * B r) r ∧
        HasDerivAt B (hs_m21 M Q e ω L c Θ r * A r + hs_m22 M Q e ω L c r * B r) r)
    (hA : Tendsto A (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (hB : Tendsto B (𝓝[>] (outerHorizon M Q)) (𝓝 (-(2 * I * radialK e ω (outerHorizon M Q))))) :
    (∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ (hs_sysR M Q e ω c Θ A B) r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv (hs_sysR M Q e ω c Θ A B) s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * hs_sysR M Q e ω c Θ A B r) r) ∧
      (fun r : ℝ => exp (I * (Θ r : ℂ)) * hs_sysR M Q e ω c Θ A B r - 1)
          =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q) ∧
      deriv (fun r : ℝ => exp (I * (Θ r : ℂ)) * hs_sysR M Q e ω c Θ A B r)
          =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)) := by
  obtain ⟨hder, hR⟩ := hs_radial_of_system hκ hΘ hsys
  refine ⟨hR, ?_⟩
  set a := outerHorizon M Q with ha
  have hev : ∀ᶠ r in 𝓝[>] a, r ∈ Ioi a := self_mem_nhdsWithin
  have hκa : (2 * I * (hs_kap M Q e ω c a : ℂ)) ≠ 0 := by
    rw [hs_kap_outerHorizon]
    exact hs_two_I_mul_ne_zero hK
  have hinv : (fun r => (2 * I * (hs_kap M Q e ω c r : ℂ))⁻¹) =O[𝓝[>] a]
      (fun _ => (1 : ℝ)) := by
    refine hs_isBigO_one_of_continuousAt (ContinuousAt.inv₀ ?_ hκa)
    exact (continuous_const.mul
      (Complex.continuous_ofReal.comp (hs_continuous_kap M Q e ω c))).continuousAt
  have hEA : (fun r => exp (I * (Θ r : ℂ)) * A r) =O[𝓝[>] a] (fun _ => (1 : ℝ)) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => by
      simp only [norm_mul, norm_exp_I_mul, one_mul]) (hA.isBigO_one ℝ)
  have hEB : (fun r => exp (-(I * (Θ r : ℂ))) * B r) =O[𝓝[>] a] (fun _ => (1 : ℝ)) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => by
      simp only [norm_mul, norm_exp_neg_I_mul, one_mul]) (hB.isBigO_one ℝ)
  have hR1 : hs_sysR M Q e ω c Θ A B =O[𝓝[>] a] (fun _ => (1 : ℝ)) := by
    have h := (hEA.sub hEB).mul hinv
    simp only [mul_one] at h
    refine h.congr_left fun r => ?_
    simp only [hs_sysR, div_eq_mul_inv]
  have hΔΔ : (fun r => (delta M Q r : ℂ)) =O[𝓝[>] a] (delta M Q) :=
    hs_isBigO_of_norm_eq (Eventually.of_forall fun r => Complex.norm_real _) (isBigO_refl _ _)
  have hΔR := hΔΔ.mul (hR1.const_mul_left (c : ℂ))
  simp only [mul_one] at hΔR
  have hlim0 := hΔR.trans_tendsto (hu_tendsto_delta M Q)
  have hcorr₁ : Tendsto (fun r => I * c * delta M Q r * exp (-(I * (Θ r : ℂ))) *
      hs_sysR M Q e ω c Θ A B r) (𝓝[>] a) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := hlim0.norm
    rw [norm_zero] at h
    refine h.congr' (Eventually.of_forall fun r => ?_)
    simp only [norm_mul, norm_exp_neg_I_mul, Complex.norm_I]
    ring
  have hcorr₂ : Tendsto (fun r => I * c * delta M Q r * exp (I * (Θ r : ℂ)) *
      hs_sysR M Q e ω c Θ A B r) (𝓝[>] a) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := hlim0.norm
    rw [norm_zero] at h
    refine h.congr' (Eventually.of_forall fun r => ?_)
    simp only [norm_mul, norm_exp_I_mul, Complex.norm_I]
    ring
  have hamps : ∀ᶠ r in 𝓝[>] a, _ := hev.mono fun r hr =>
    hs_amps_sysR (hκ r hr) (hder r hr) (delta_pos_of_lt hr).ne'
  have hAo : Tendsto (hu_ampOut M Q e ω Θ (hs_sysR M Q e ω c Θ A B)) (𝓝[>] a) (𝓝 0) := by
    have h := hA.sub hcorr₁
    rw [sub_zero] at h
    exact h.congr' (hamps.mono fun r hr => hr.1.symm)
  have hBi : Tendsto (hu_ampIn M Q e ω Θ (hs_sysR M Q e ω c Θ A B)) (𝓝[>] a)
      (𝓝 (-(2 * I * radialK e ω a))) := by
    have h := hB.add hcorr₂
    rw [add_zero] at h
    exact h.congr' (hamps.mono fun r hr => hr.2.symm)
  exact hs_horizon_condition_of_tendsto_amps hK hΘ hR hAo hBi

end ModeStability.AllAngular

end
