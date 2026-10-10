module

public import Mathlib

/-!
# Linear Volterra equations with locally integrable coefficients: the core

This file is the generic core of `ModeStability.ODE.LinearVolterra`. For a complete normed space
`E` and a coefficient `M : ℝ → E →L[𝕜] E`, we solve the linear Volterra equation
`v t = v₀ + ∫ s in c..t, M s (v s)` by successive approximations

`v₀(t) = v₀`, `v_{n+1}(t) = v₀ + ∫ s in c..t, M s (v_n s)`,

with the classical bound `‖v_{n+1} t − v_n t‖ ≤ ‖v₀‖ μ(t)^{n+1}/(n+1)!` in terms of the mass
`μ(t) = ∫ s in Ι c t, ‖M s‖`. No continuity of `M` at the base point `c` is needed: only
continuity on `Ι c t` and integrability of `‖M‖` there. This covers a bounded but oscillating
coefficient at a singular endpoint, and (after the substitution `s = 1/(t − a)`) an integrable
coefficient at `+∞`.

Main statements:

* `linear_exists_of_integrableOn`: on an open set `J` with `Ι c t ⊆ J` for `t ∈ J`, a continuous
  coefficient with `‖M‖` integrable on every `Ι c t`, `t ∈ J`, has a solution of `v' = M v` on `J`
  with `v c = v₀`, the integral equation, continuity on `[[c, t]]`, and the bound
  `‖v t − v₀‖ ≤ (exp μ(t) − 1) ‖v₀‖`;
* `volterra_eq_zero`: a bounded continuous solution of the homogeneous Volterra equation
  vanishes;
* `linear_eqOn_of_hasDerivAt`, `linear_exists_of_ordConnected`: uniqueness and global existence
  on an order-connected set from data at an interior point;
* `linear_eqOn_of_tendsto_nhdsGT`: uniqueness at a singular left endpoint, from the limit there.

The key identity is `|∫ s in c..t, ‖M s‖ μ(s)^k| = μ(t)^{k+1}/(k+1)`
(`lv_abs_integral_mul_mass_pow`), proved by the fundamental theorem of calculus on each side of
`c`. Helpers carry the prefix `lv_`.
-/

public section

namespace ModeStability.ODE

open Set Filter MeasureTheory Topology intervalIntegral
open scoped Interval Nat

section Mass

variable {m : ℝ → ℝ} {c t s : ℝ}

/-- The mass `∫_{Ι c t} m` of a weight `m` between the base point `c` and `t`. -/
noncomputable def lv_mass (m : ℝ → ℝ) (c t : ℝ) : ℝ := ∫ x in Ι c t, m x

theorem lv_uIoc_subset (hs : s ∈ [[c, t]]) : Ι c s ⊆ Ι c t := by
  rcases le_total c t with h | h
  · rw [uIcc_of_le h] at hs
    rw [uIoc_of_le hs.1, uIoc_of_le h]
    exact Ioc_subset_Ioc_right hs.2
  · rw [uIcc_of_ge h] at hs
    rw [uIoc_of_ge hs.2, uIoc_of_ge h]
    exact Ioc_subset_Ioc_left hs.1

theorem lv_mass_nonneg (hm0 : ∀ x, 0 ≤ m x) : 0 ≤ lv_mass m c t :=
  setIntegral_nonneg measurableSet_uIoc fun x _ => hm0 x

theorem lv_mass_mono (hm0 : ∀ x, 0 ≤ m x) (hmi : IntegrableOn m (Ι c t)) (hs : s ∈ [[c, t]]) :
    lv_mass m c s ≤ lv_mass m c t :=
  setIntegral_mono_set hmi (Eventually.of_forall fun x => hm0 x) (lv_uIoc_subset hs).eventuallyLE

theorem lv_mass_eq_abs (hm0 : ∀ x, 0 ≤ m x) : lv_mass m c t = |∫ x in c..t, m x| := by
  rw [abs_integral_eq_abs_integral_uIoc, lv_mass,
    abs_of_nonneg (setIntegral_nonneg measurableSet_uIoc fun x _ => hm0 x)]

theorem lv_mass_continuousOn (hm0 : ∀ x, 0 ≤ m x) (hmi : IntervalIntegrable m volume c t) :
    ContinuousOn (lv_mass m c) [[c, t]] :=
  (continuousOn_primitive_interval' hmi left_mem_uIcc).abs.congr fun _ _ => lv_mass_eq_abs hm0

/-- `m` has derivative `m x` at interior points of `[[c, t]]`. -/
theorem lv_hasDerivAt_primitive (hmc : ContinuousOn m (Ι c t)) (hmi : IntegrableOn m (Ι c t))
    {x : ℝ} (hx : x ∈ Ioo (min c t) (max c t)) :
    HasDerivAt (fun y => ∫ z in c..y, m z) (m x) x := by
  have hxs : x ∈ Ι c t := Ioo_subset_Ioc_self hx
  have hint : IntervalIntegrable m volume c x :=
    intervalIntegrable_iff.2 (hmi.mono_set (lv_uIoc_subset (uIoc_subset_uIcc hxs)))
  have hmo : ContinuousOn m (Ioo (min c t) (max c t)) := hmc.mono Ioo_subset_Ioc_self
  exact integral_hasDerivAt_right hint (hmo.stronglyMeasurableAtFilter isOpen_Ioo x hx)
    (hmo.continuousAt (isOpen_Ioo.mem_nhds hx))

/-- The key identity `|∫ s in c..t, m s μ(s)^k| = μ(t)^{k+1}/(k+1)`. -/
theorem lv_abs_integral_mul_mass_pow (hm0 : ∀ x, 0 ≤ m x) (hmc : ContinuousOn m (Ι c t))
    (hmi : IntegrableOn m (Ι c t)) (k : ℕ) :
    |∫ x in c..t, m x * lv_mass m c x ^ k| = lv_mass m c t ^ (k + 1) / (k + 1) := by
  have hmi' : IntervalIntegrable m volume c t := intervalIntegrable_iff.2 hmi
  have hPc : ContinuousOn (fun y => ∫ z in c..y, m z) [[c, t]] :=
    continuousOn_primitive_interval' hmi' left_mem_uIcc
  have hk : (0 : ℝ) < k + 1 := by positivity
  rcases le_total c t with hct | htc
  · have hmass : ∀ x ∈ Icc c t, lv_mass m c x = ∫ z in c..x, m z := fun x hx => by
      rw [lv_mass_eq_abs hm0, abs_of_nonneg (integral_nonneg hx.1 fun y _ => hm0 y)]
    rw [uIcc_of_le hct] at hPc
    have hcongr : ∫ x in c..t, m x * lv_mass m c x ^ k =
        ∫ x in c..t, m x * (∫ z in c..x, m z) ^ k :=
      integral_congr fun x hx => by
        rw [uIcc_of_le hct] at hx
        simp only [hmass x hx]
    have hderiv : ∀ x ∈ Ioo c t, HasDerivAt (fun y => (∫ z in c..y, m z) ^ (k + 1) / (k + 1))
        (m x * (∫ z in c..x, m z) ^ k) x := fun x hx => by
      have h := ((lv_hasDerivAt_primitive hmc hmi (x := x)
        (by rwa [min_eq_left hct, max_eq_right hct])).pow (k + 1)).div_const ((k : ℝ) + 1)
      convert h using 1
      push_cast
      field_simp
    have hint : IntervalIntegrable (fun x => m x * (∫ z in c..x, m z) ^ k) volume c t :=
      hmi'.mul_continuousOn (by rw [uIcc_of_le hct]; exact hPc.pow k)
    have hftc := integral_eq_sub_of_hasDerivAt_of_le
      (f := fun y => (∫ z in c..y, m z) ^ (k + 1) / (k + 1)) hct
      ((hPc.pow (k + 1)).div_const _) hderiv hint
    rw [hcongr, hftc, hmass t ⟨hct, le_rfl⟩]
    rw [integral_same, zero_pow (Nat.succ_ne_zero k), zero_div, sub_zero,
      abs_of_nonneg (by have := integral_nonneg (μ := volume) hct fun y _ => hm0 y; positivity)]
  · have hmass : ∀ x ∈ Icc t c, lv_mass m c x = -∫ z in c..x, m z := fun x hx => by
      rw [lv_mass_eq_abs hm0, abs_of_nonpos]
      rw [integral_symm, neg_nonpos]
      exact integral_nonneg hx.2 fun y _ => hm0 y
    rw [uIcc_of_ge htc] at hPc
    have hcongr : ∫ x in t..c, m x * lv_mass m c x ^ k =
        ∫ x in t..c, m x * (-∫ z in c..x, m z) ^ k :=
      integral_congr fun x hx => by
        rw [uIcc_of_le htc] at hx
        simp only [hmass x hx]
    have hderiv : ∀ x ∈ Ioo t c,
        HasDerivAt (fun y => -((-∫ z in c..y, m z) ^ (k + 1) / (k + 1)))
        (m x * (-∫ z in c..x, m z) ^ k) x := fun x hx => by
      have hG : HasDerivAt (fun y => -∫ z in c..y, m z) (-m x) x :=
        (lv_hasDerivAt_primitive hmc hmi (x := x)
          (by rwa [min_eq_right htc, max_eq_left htc])).neg
      have h := ((hG.pow (k + 1)).div_const ((k : ℝ) + 1)).neg
      convert h using 1
      push_cast
      field_simp
    have hint : IntervalIntegrable (fun x => m x * (-∫ z in c..x, m z) ^ k) volume t c :=
      hmi'.symm.mul_continuousOn (by rw [uIcc_of_le htc]; exact hPc.neg.pow k)
    have hftc := integral_eq_sub_of_hasDerivAt_of_le
      (f := fun y => -((-∫ z in c..y, m z) ^ (k + 1) / (k + 1))) htc
      (((hPc.neg).pow (k + 1)).div_const _).neg hderiv hint
    rw [integral_symm, abs_neg, hcongr, hftc, hmass t ⟨le_rfl, htc⟩]
    have h0 : 0 ≤ -∫ z in c..t, m z := by
      rw [integral_symm, neg_neg]
      exact integral_nonneg htc fun y _ => hm0 y
    rw [integral_same, neg_zero, zero_pow (Nat.succ_ne_zero k), zero_div, neg_zero, zero_sub,
      neg_neg, abs_of_nonneg (by positivity)]

end Mass

section Iterates

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] {M : ℝ → E →L[𝕜] E} {c t : ℝ}

omit [NormedSpace ℝ E] in
theorem lv_intervalIntegrable_apply {g : ℝ → E} {B : ℝ}
    (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t))
    (hmeas : AEStronglyMeasurable (fun s => M s (g s)) (volume.restrict (Ι c t)))
    (hB : ∀ s ∈ Ι c t, ‖g s‖ ≤ B) : IntervalIntegrable (fun s => M s (g s)) volume c t := by
  rw [intervalIntegrable_iff]
  refine Integrable.mono' (hMi.mul_const B) hmeas ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun s hs => ?_)
  calc ‖M s (g s)‖ ≤ ‖M s‖ * ‖g s‖ := (M s).le_opNorm _
    _ ≤ ‖M s‖ * B := mul_le_mul_of_nonneg_left (hB s hs) (norm_nonneg _)

omit [NormedSpace ℝ E] in
theorem lv_aestronglyMeasurable_apply {g : ℝ → E} (hMc : ContinuousOn M (Ι c t))
    (hg : ContinuousOn g (Ι c t)) :
    AEStronglyMeasurable (fun s => M s (g s)) (volume.restrict (Ι c t)) :=
  (hMc.clm_apply hg).aestronglyMeasurable measurableSet_uIoc

omit [NormedSpace ℝ E] in
theorem lv_intervalIntegrable_apply_of_continuousOn {g : ℝ → E} (hMc : ContinuousOn M (Ι c t))
    (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t)) (hg : ContinuousOn g [[c, t]]) :
    IntervalIntegrable (fun s => M s (g s)) volume c t := by
  obtain ⟨B, hB⟩ := isCompact_uIcc.exists_bound_of_continuousOn hg
  exact lv_intervalIntegrable_apply hMi
    (lv_aestronglyMeasurable_apply hMc (hg.mono uIoc_subset_uIcc))
    fun s hs => hB s (uIoc_subset_uIcc hs)

/-- One step of the Picard estimate: a bound `K μ^k/k!` on `u` gives `K μ^{k+1}/(k+1)!` on
`∫ M u`. -/
theorem lv_norm_integral_le {u : ℝ → E} {K : ℝ} {k : ℕ} (hMc : ContinuousOn M (Ι c t))
    (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t)) (hK : 0 ≤ K)
    (hub : ∀ x ∈ Ι c t, ‖u x‖ ≤ K * lv_mass (fun s => ‖M s‖) c x ^ k / k !) {s : ℝ}
    (hs : s ∈ [[c, t]]) :
    ‖∫ x in c..s, M x (u x)‖ ≤ K * lv_mass (fun s => ‖M s‖) c s ^ (k + 1) / (k + 1)! := by
  set m : ℝ → ℝ := fun s => ‖M s‖
  have hm0 : ∀ x, 0 ≤ m x := fun x => norm_nonneg _
  have hsub : Ι c s ⊆ Ι c t := lv_uIoc_subset hs
  have hmi : IntegrableOn m (Ι c s) := hMi.mono_set hsub
  have hmi' : IntervalIntegrable m volume c s := intervalIntegrable_iff.2 hmi
  have hmc : ContinuousOn m (Ι c s) := (hMc.mono hsub).norm
  have hcm : ContinuousOn (fun x => K * lv_mass m c x ^ k / k !) [[c, s]] :=
    (continuousOn_const.mul ((lv_mass_continuousOn hm0 hmi').pow k)).div_const _
  have hgi : IntervalIntegrable (fun x => m x * (K * lv_mass m c x ^ k / k !)) volume c s :=
    hmi'.mul_continuousOn hcm
  have hbound : ∀ᵐ x ∂volume.restrict (Ι c s),
      ‖M x (u x)‖ ≤ m x * (K * lv_mass m c x ^ k / k !) :=
    (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx =>
      ((M x).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hub x (hsub hx)) (norm_nonneg _)))
  have hk : (0 : ℝ) < (k ! : ℝ) := by positivity
  calc ‖∫ x in c..s, M x (u x)‖ ≤ |∫ x in c..s, m x * (K * lv_mass m c x ^ k / k !)| :=
        norm_integral_le_abs_of_norm_le hbound hgi
    _ = K / k ! * |∫ x in c..s, m x * lv_mass m c x ^ k| := by
        rw [← abs_of_nonneg (div_nonneg hK hk.le), ← abs_mul, ← intervalIntegral.integral_const_mul]
        congr 1
        refine integral_congr fun x _ => ?_
        ring
    _ = K / k ! * (lv_mass m c s ^ (k + 1) / (k + 1)) := by
        rw [lv_abs_integral_mul_mass_pow hm0 hmc hmi k]
    _ = K * lv_mass m c s ^ (k + 1) / (k + 1)! := by
        rw [Nat.factorial_succ]
        push_cast
        field_simp

/-- The Picard iterates `v₀`, `v₀ + ∫ s in c..t, M s (v_n s)`. -/
noncomputable def lv_iter (M : ℝ → E →L[𝕜] E) (c : ℝ) (v₀ : E) : ℕ → ℝ → E
  | 0 => fun _ => v₀
  | n + 1 => fun t => v₀ + ∫ s in c..t, M s (lv_iter M c v₀ n s)

theorem lv_iter_zero (v₀ : E) (t : ℝ) : lv_iter M c v₀ 0 t = v₀ := by
  simp [lv_iter]

theorem lv_iter_succ (v₀ : E) (n : ℕ) (t : ℝ) :
    lv_iter M c v₀ (n + 1) t = v₀ + ∫ s in c..t, M s (lv_iter M c v₀ n s) := by
  simp [lv_iter]

theorem lv_iter_continuousOn (hMc : ContinuousOn M (Ι c t))
    (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t)) (v₀ : E) :
    ∀ n, ContinuousOn (lv_iter M c v₀ n) [[c, t]]
  | 0 => continuousOn_const.congr fun x _ => lv_iter_zero v₀ x
  | n + 1 => by
    have h := continuousOn_primitive_interval' (lv_intervalIntegrable_apply_of_continuousOn hMc
      hMi (lv_iter_continuousOn hMc hMi v₀ n)) left_mem_uIcc
    exact (continuousOn_const.add h).congr fun x _ => lv_iter_succ v₀ n x

theorem lv_iter_one_sub (v₀ : E) (s : ℝ) :
    lv_iter M c v₀ 1 s - lv_iter M c v₀ 0 s = ∫ x in c..s, M x v₀ := by
  rw [lv_iter_succ, lv_iter_zero]
  simp only [lv_iter_zero, add_sub_cancel_left]

theorem lv_iter_succ_sub (hMc : ContinuousOn M (Ι c t))
    (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t)) (v₀ : E) (n : ℕ) {s : ℝ} (hs : s ∈ [[c, t]]) :
    lv_iter M c v₀ (n + 2) s - lv_iter M c v₀ (n + 1) s =
      ∫ x in c..s, M x (lv_iter M c v₀ (n + 1) x - lv_iter M c v₀ n x) := by
  have hsub := lv_uIoc_subset hs
  have hcs : [[c, s]] ⊆ [[c, t]] := uIcc_subset_uIcc_left hs
  rw [lv_iter_succ, lv_iter_succ v₀ n s, add_sub_add_left_eq_sub,
    ← integral_sub (lv_intervalIntegrable_apply_of_continuousOn (hMc.mono hsub)
      (hMi.mono_set hsub) ((lv_iter_continuousOn hMc hMi v₀ (n + 1)).mono hcs))
      (lv_intervalIntegrable_apply_of_continuousOn (hMc.mono hsub) (hMi.mono_set hsub)
        ((lv_iter_continuousOn hMc hMi v₀ n).mono hcs))]
  simp only [map_sub]

theorem lv_iter_dist_le (hMc : ContinuousOn M (Ι c t))
    (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t)) (v₀ : E) :
    ∀ n, ∀ s ∈ [[c, t]], ‖lv_iter M c v₀ (n + 1) s - lv_iter M c v₀ n s‖ ≤
      ‖v₀‖ * lv_mass (fun s => ‖M s‖) c s ^ (n + 1) / (n + 1)!
  | 0, s, hs => by
    rw [lv_iter_one_sub]
    simpa using lv_norm_integral_le (u := fun _ => v₀) (K := ‖v₀‖) (k := 0) hMc hMi
      (norm_nonneg _) (fun x _ => by simp) hs
  | n + 1, s, hs => by
    rw [lv_iter_succ_sub hMc hMi v₀ n hs]
    exact lv_norm_integral_le hMc hMi (norm_nonneg _)
      (fun x hx => lv_iter_dist_le hMc hMi v₀ n x (uIoc_subset_uIcc hx)) hs

theorem lv_hasSum_exp_sub_one (x : ℝ) :
    HasSum (fun n : ℕ => x ^ (n + 1) / (n + 1)!) (Real.exp x - 1) := by
  have h := NormedSpace.expSeries_div_hasSum_exp x
  rw [← Real.exp_eq_exp_ℝ] at h
  simpa using (hasSum_nat_add_iff' 1).2 h

omit [NormedSpace ℝ E] in
theorem lv_hasSum_dist (v₀ : E) (s : ℝ) :
    HasSum (fun n : ℕ => ‖v₀‖ * lv_mass (fun s => ‖M s‖) c s ^ (n + 1) / (n + 1)!)
      ((Real.exp (lv_mass (fun s => ‖M s‖) c s) - 1) * ‖v₀‖) := by
  have h := (lv_hasSum_exp_sub_one (lv_mass (fun s => ‖M s‖) c s)).mul_left ‖v₀‖
  convert h using 1
  · funext n
    ring
  · ring

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
theorem lv_norm_le_of_sub_le {x v₀ : E} {μs μt : ℝ} (h : ‖x - v₀‖ ≤ (Real.exp μs - 1) * ‖v₀‖)
    (hst : μs ≤ μt) : ‖x‖ ≤ Real.exp μt * ‖v₀‖ := by
  have h1 := norm_sub_norm_le x v₀
  have h2 : Real.exp μs * ‖v₀‖ ≤ Real.exp μt * ‖v₀‖ :=
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hst) (norm_nonneg _)
  linarith

theorem lv_iter_sub_le (hMc : ContinuousOn M (Ι c t))
    (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t)) (v₀ : E) (n : ℕ) {s : ℝ} (hs : s ∈ [[c, t]]) :
    ‖lv_iter M c v₀ n s - v₀‖ ≤ (Real.exp (lv_mass (fun s => ‖M s‖) c s) - 1) * ‖v₀‖ := by
  have h := dist_le_range_sum_dist (fun n => lv_iter M c v₀ n s) n
  simp only [lv_iter_zero] at h
  rw [dist_comm, dist_eq_norm] at h
  refine h.trans ((Finset.sum_le_sum fun i _ => ?_).trans
    (sum_le_hasSum _ (fun i _ => ?_) (lv_hasSum_dist v₀ s)))
  · rw [dist_comm, dist_eq_norm]
    exact lv_iter_dist_le hMc hMi v₀ i s hs
  · have := lv_mass_nonneg (m := fun s => ‖M s‖) (c := c) (t := s) fun _ => norm_nonneg _
    positivity

variable [CompleteSpace E]

/-- The limit of the Picard iterates. -/
noncomputable def lv_sol (M : ℝ → E →L[𝕜] E) (c : ℝ) (v₀ : E) (t : ℝ) : E :=
  limUnder atTop fun n => lv_iter M c v₀ n t

theorem lv_tendsto_iter (hMc : ContinuousOn M (Ι c t))
    (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t)) (v₀ : E) {s : ℝ} (hs : s ∈ [[c, t]]) :
    Tendsto (fun n => lv_iter M c v₀ n s) atTop (𝓝 (lv_sol M c v₀ s)) := by
  have hc : CauchySeq fun n => lv_iter M c v₀ n s :=
    cauchySeq_of_dist_le_of_summable _ (fun n => by
      rw [dist_comm, dist_eq_norm]
      exact lv_iter_dist_le hMc hMi v₀ n s hs) (lv_hasSum_dist v₀ s).summable
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  exact tendsto_nhds_limUnder ⟨L, hL⟩

theorem lv_sol_sub_le (hMc : ContinuousOn M (Ι c t))
    (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t)) (v₀ : E) {s : ℝ} (hs : s ∈ [[c, t]]) :
    ‖lv_sol M c v₀ s - v₀‖ ≤ (Real.exp (lv_mass (fun s => ‖M s‖) c s) - 1) * ‖v₀‖ := by
  have h := dist_le_tsum_of_dist_le_of_tendsto₀ _ (fun n => by
      rw [dist_comm, dist_eq_norm]
      exact lv_iter_dist_le hMc hMi v₀ n s hs) (lv_hasSum_dist v₀ s).summable
    (lv_tendsto_iter hMc hMi v₀ hs)
  rwa [(lv_hasSum_dist v₀ s).tsum_eq, lv_iter_zero, dist_comm, dist_eq_norm] at h

theorem lv_sol_eq (hMc : ContinuousOn M (Ι c t)) (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t))
    (v₀ : E) : lv_sol M c v₀ t = v₀ + ∫ x in c..t, M x (lv_sol M c v₀ x) := by
  set μt := lv_mass (fun s => ‖M s‖) c t
  have hb : ∀ n, ∀ x ∈ [[c, t]], ‖lv_iter M c v₀ n x‖ ≤ Real.exp μt * ‖v₀‖ := fun n x hx =>
    lv_norm_le_of_sub_le (lv_iter_sub_le hMc hMi v₀ n hx)
      (lv_mass_mono (fun _ => norm_nonneg _) hMi hx)
  have h1 : Tendsto (fun n => lv_iter M c v₀ (n + 1) t) atTop (𝓝 (lv_sol M c v₀ t)) :=
    (lv_tendsto_iter hMc hMi v₀ right_mem_uIcc).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n => lv_iter M c v₀ (n + 1) t) atTop
      (𝓝 (v₀ + ∫ x in c..t, M x (lv_sol M c v₀ x))) := by
    simp only [lv_iter_succ]
    refine tendsto_const_nhds.add (tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖M x‖ * (Real.exp μt * ‖v₀‖))
      (Eventually.of_forall fun n => lv_aestronglyMeasurable_apply hMc
        ((lv_iter_continuousOn hMc hMi v₀ n).mono uIoc_subset_uIcc))
      (Eventually.of_forall fun n => Eventually.of_forall fun x hx =>
        ((M x).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb n x (uIoc_subset_uIcc hx))
          (norm_nonneg _)))
      ((intervalIntegrable_iff.2 hMi).mul_const _)
      (Eventually.of_forall fun x hx => ((M x).continuous.tendsto _).comp
        (lv_tendsto_iter hMc hMi v₀ (uIoc_subset_uIcc hx))))
  exact tendsto_nhds_unique h1 h2

theorem lv_sol_intervalIntegrable (hMc : ContinuousOn M (Ι c t))
    (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t)) (v₀ : E) :
    IntervalIntegrable (fun x => M x (lv_sol M c v₀ x)) volume c t := by
  refine lv_intervalIntegrable_apply hMi ?_
    (B := Real.exp (lv_mass (fun s => ‖M s‖) c t) * ‖v₀‖) fun x hx =>
    lv_norm_le_of_sub_le (lv_sol_sub_le hMc hMi v₀ (uIoc_subset_uIcc hx))
      (lv_mass_mono (fun _ => norm_nonneg _) hMi (uIoc_subset_uIcc hx))
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun n => lv_aestronglyMeasurable_apply hMc
      ((lv_iter_continuousOn hMc hMi v₀ n).mono uIoc_subset_uIcc))
    ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx =>
      ((M x).continuous.tendsto _).comp (lv_tendsto_iter hMc hMi v₀ (uIoc_subset_uIcc hx))))

theorem lv_sol_self (v₀ : E) : lv_sol M c v₀ c = v₀ := by
  have hiter : ∀ n, lv_iter M c v₀ n c = v₀ := fun n => by
    cases n with
    | zero => exact lv_iter_zero v₀ c
    | succ n => rw [lv_iter_succ, integral_same, add_zero]
  have hMc : ContinuousOn M (Ι c c) := by simp
  have hMi : IntegrableOn (fun s => ‖M s‖) (Ι c c) := by simp
  have h := lv_tendsto_iter hMc hMi v₀ (left_mem_uIcc (a := c) (b := c))
  simp only [hiter] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end Iterates

section Core

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E] {M : ℝ → E →L[𝕜] E}

/-- **Linear Volterra existence with an integrable coefficient.** Let `J` be open with
`Ι c t ⊆ J` for every `t ∈ J` (for instance `J = Ioi c`, or an open interval containing `c`), let
`M` be continuous on `J` and `‖M‖` integrable on every `Ι c t`, `t ∈ J`. Then the successive
approximations converge to a solution of `v' = M v` on `J` with `v c = v₀`, which satisfies the
integral equation, is continuous on every `[[c, t]]`, and obeys the Grönwall bound. Continuity of
`M` at `c` is not required. -/
theorem linear_exists_of_integrableOn {J : Set ℝ} {c : ℝ} (hJo : IsOpen J)
    (hJc : ∀ t ∈ J, Ι c t ⊆ J) (hM : ContinuousOn M J)
    (hint : ∀ t ∈ J, IntegrableOn (fun s => ‖M s‖) (Ι c t)) (v₀ : E) :
    ∃ v : ℝ → E, v c = v₀ ∧ (∀ t ∈ J, HasDerivAt v (M t (v t)) t) ∧
      (∀ t ∈ J, v t = v₀ + ∫ s in c..t, M s (v s)) ∧ (∀ t ∈ J, ContinuousOn v [[c, t]]) ∧
      ∀ t ∈ J, ‖v t - v₀‖ ≤ (Real.exp (∫ s in Ι c t, ‖M s‖) - 1) * ‖v₀‖ := by
  set v := lv_sol M c v₀
  have hMc : ∀ t ∈ J, ContinuousOn M (Ι c t) := fun t ht => hM.mono (hJc t ht)
  have heq' : ∀ t ∈ J, ∀ x ∈ [[c, t]], v x = v₀ + ∫ s in c..x, M s (v s) := fun t ht x hx =>
    lv_sol_eq ((hMc t ht).mono (lv_uIoc_subset hx)) ((hint t ht).mono_set (lv_uIoc_subset hx)) v₀
  have heq : ∀ t ∈ J, v t = v₀ + ∫ s in c..t, M s (v s) := fun t ht =>
    heq' t ht t right_mem_uIcc
  have hgi : ∀ t ∈ J, IntervalIntegrable (fun s => M s (v s)) volume c t := fun t ht =>
    lv_sol_intervalIntegrable (hMc t ht) (hint t ht) v₀
  have hcont : ∀ t ∈ J, ContinuousOn v [[c, t]] := fun t ht =>
    ((continuousOn_primitive_interval' (hgi t ht) left_mem_uIcc).const_add v₀).congr (heq' t ht)
  have hcontJ : ContinuousOn v J := by
    intro t ht
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hJo t ht
    have hmem : ∀ x, |x - t| < ε → x ∈ J := fun x hx =>
      hball (by rwa [Metric.mem_ball, Real.dist_eq])
    have h₁ : t - ε / 2 ∈ J := hmem _ (by rw [abs_lt]; constructor <;> linarith)
    have h₂ : t + ε / 2 ∈ J := hmem _ (by rw [abs_lt]; constructor <;> linarith)
    have hle : t - ε / 2 ≤ t + ε / 2 := by linarith
    have hsub : [[t - ε / 2, t + ε / 2]] ⊆ J := fun x hx => by
      rw [uIcc_of_le hle] at hx
      exact hmem x (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
    have hI : IntervalIntegrable (fun s => M s (v s)) volume (t - ε / 2) (t + ε / 2) :=
      (hgi _ h₁).symm.trans (hgi _ h₂)
    have hcon : ContinuousOn v [[t - ε / 2, t + ε / 2]] := by
      refine ((continuousOn_primitive_interval' hI left_mem_uIcc).const_add
        (v₀ + ∫ s in c..t - ε / 2, M s (v s))).congr fun x hx => ?_
      beta_reduce
      rw [heq x (hsub hx), add_assoc, integral_add_adjacent_intervals (hgi _ h₁)
        ((hgi _ h₁).symm.trans (hgi x (hsub hx)))]
    have hnhds : [[t - ε / 2, t + ε / 2]] ∈ 𝓝 t := by
      rw [uIcc_of_le hle]
      exact Icc_mem_nhds (by linarith) (by linarith)
    exact (hcon.continuousAt hnhds).continuousWithinAt
  have hgc : ContinuousOn (fun s => M s (v s)) J := hM.clm_apply hcontJ
  refine ⟨v, lv_sol_self v₀, fun t ht => ?_, heq, hcont, fun t ht =>
    lv_sol_sub_le (hMc t ht) (hint t ht) v₀ right_mem_uIcc⟩
  have hF := (integral_hasDerivAt_right (hgi t ht) (hgc.stronglyMeasurableAtFilter hJo t ht)
    (hgc.continuousAt (hJo.mem_nhds ht))).const_add v₀
  exact hF.congr_of_eventuallyEq (Filter.eventually_of_mem (hJo.mem_nhds ht) fun x hx => heq x hx)

omit [CompleteSpace E] in
/-- **Volterra uniqueness.** A bounded solution of the homogeneous equation
`w s = ∫ x in c..s, M x (w x)` on `Ι c t` (and at `t`) vanishes at `t`. -/
theorem volterra_eq_zero {c t B : ℝ} {w : ℝ → E} (hMc : ContinuousOn M (Ι c t))
    (hMi : IntegrableOn (fun s => ‖M s‖) (Ι c t)) (hB : ∀ s ∈ Ι c t, ‖w s‖ ≤ B)
    (hweq : ∀ s ∈ Ι c t, w s = ∫ x in c..s, M x (w x)) (hwt : w t = ∫ x in c..t, M x (w x)) :
    w t = 0 := by
  set B' := max B 0
  have hB' : 0 ≤ B' := le_max_right _ _
  have claim : ∀ n : ℕ, ∀ s ∈ Ι c t, ‖w s‖ ≤ B' * lv_mass (fun s => ‖M s‖) c s ^ n / n ! := by
    intro n
    induction n with
    | zero =>
      intro s hs
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      exact (hB s hs).trans (le_max_left _ _)
    | succ n ih =>
      intro s hs
      rw [hweq s hs]
      exact lv_norm_integral_le hMc hMi hB' ih (uIoc_subset_uIcc hs)
  have hfin : ∀ n : ℕ, ‖w t‖ ≤ B' * lv_mass (fun s => ‖M s‖) c t ^ (n + 1) / (n + 1)! :=
    fun n => by
      rw [hwt]
      exact lv_norm_integral_le hMc hMi hB' (claim n) right_mem_uIcc
  have hlim : Tendsto (fun n : ℕ => B' * lv_mass (fun s => ‖M s‖) c t ^ (n + 1) / (n + 1)!)
      atTop (𝓝 0) := by
    have h := ((FloorSemiring.tendsto_pow_div_factorial_atTop
      (lv_mass (fun s => ‖M s‖) c t)).comp (tendsto_add_atTop_nat 1)).const_mul B'
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, mul_div_assoc]
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim hfin)

/-- **Uniqueness** for `v' = M v` on an order-connected set, from data at one point. -/
theorem linear_eqOn_of_hasDerivAt {J : Set ℝ} (hJ : J.OrdConnected) (hM : ContinuousOn M J)
    {u w : ℝ → E} (hu : ∀ t ∈ J, HasDerivAt u (M t (u t)) t)
    (hw : ∀ t ∈ J, HasDerivAt w (M t (w t)) t) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (h : u t₀ = w t₀) :
    EqOn u w J := by
  intro t ht
  have hd : ∀ s ∈ J, HasDerivAt (fun x => u x - w x) (M s (u s - w s)) s := fun s hs => by
    rw [map_sub]
    exact (hu s hs).sub (hw s hs)
  have hsub : [[t₀, t]] ⊆ J := hJ.uIcc_subset ht₀ ht
  have hdc : ContinuousOn (fun x => u x - w x) [[t₀, t]] := fun s hs =>
    (hd s (hsub hs)).continuousAt.continuousWithinAt
  have hMc : ContinuousOn M [[t₀, t]] := hM.mono hsub
  have hMi : IntegrableOn (fun s => ‖M s‖) (Ι t₀ t) :=
    (hMc.norm.integrableOn_compact isCompact_uIcc).mono_set uIoc_subset_uIcc
  obtain ⟨B, hB⟩ := isCompact_uIcc.exists_bound_of_continuousOn hdc
  have heq : ∀ s ∈ [[t₀, t]], u s - w s = ∫ x in t₀..s, M x (u x - w x) := fun s hs => by
    have hcs : [[t₀, s]] ⊆ [[t₀, t]] := uIcc_subset_uIcc_left hs
    rw [integral_eq_sub_of_hasDerivAt (fun x hx => hd x (hsub (hcs hx)))
      ((hMc.clm_apply hdc).mono hcs).intervalIntegrable, h, sub_self, sub_zero]
  exact sub_eq_zero.1 (volterra_eq_zero (hMc.mono uIoc_subset_uIcc) hMi
    (fun s hs => hB s (uIoc_subset_uIcc hs)) (fun s hs => heq s (uIoc_subset_uIcc hs))
    (heq t right_mem_uIcc))

/-- **Global existence** for `v' = M v` on an open order-connected set with continuous `M`, from
data at an interior point. -/
theorem linear_exists_of_ordConnected {J : Set ℝ} (hJo : IsOpen J) (hJ : J.OrdConnected)
    (hM : ContinuousOn M J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (v₁ : E) :
    ∃ v : ℝ → E, v t₀ = v₁ ∧ ∀ t ∈ J, HasDerivAt v (M t (v t)) t := by
  obtain ⟨v, hv0, hvd, -⟩ := linear_exists_of_integrableOn hJo
    (fun t ht => uIoc_subset_uIcc.trans (hJ.uIcc_subset ht₀ ht)) hM
    (fun t ht => ((hM.mono (hJ.uIcc_subset ht₀ ht)).norm.integrableOn_compact
      isCompact_uIcc).mono_set uIoc_subset_uIcc) v₁
  exact ⟨v, hv0, hvd⟩

/-- **Uniqueness at a singular left endpoint.** Let `J ⊆ (a, ∞)` with `(a, t] ⊆ J` for
`t ∈ J`, `M` continuous on `J` and `‖M‖` integrable on every `(a, t]`, `t ∈ J`. Two solutions of
`v' = M v` on `J` with the same limit as `t ↓ a` agree on `J`. -/
theorem linear_eqOn_of_tendsto_nhdsGT {J : Set ℝ} {a : ℝ} (hJa : J ⊆ Ioi a)
    (hJc : ∀ t ∈ J, Ioc a t ⊆ J) (hM : ContinuousOn M J)
    (hint : ∀ t ∈ J, IntegrableOn (fun s => ‖M s‖) (Ioc a t)) {u w : ℝ → E}
    (hu : ∀ t ∈ J, HasDerivAt u (M t (u t)) t) (hw : ∀ t ∈ J, HasDerivAt w (M t (w t)) t)
    {L : E} (hu0 : Tendsto u (𝓝[>] a) (𝓝 L)) (hw0 : Tendsto w (𝓝[>] a) (𝓝 L)) :
    EqOn u w J := by
  intro t ht
  have hat : a < t := hJa ht
  set d : ℝ → E := fun x => u x - w x with hd_def
  have hd : ∀ s ∈ J, HasDerivAt d (M s (d s)) s := fun s hs => by
    simp only [hd_def, map_sub]
    exact (hu s hs).sub (hw s hs)
  have hd0 : Tendsto d (𝓝[>] a) (𝓝 0) := by
    simpa [hd_def] using hu0.sub hw0
  set d' := Function.update d a 0 with hd'_def
  have hd'eq : ∀ x, x ≠ a → d' x = d x := fun x hx => Function.update_of_ne hx _ _
  have hd'c : ContinuousOn d' (Icc a t) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hax
    · rw [hd'_def, continuousWithinAt_update_same]
      exact hd0.mono_left (nhdsWithin_mono _ fun y hy => lt_of_le_of_ne hy.1.1 (Ne.symm hy.2))
    · refine ((hd x (hJc t ht ⟨hax, hx.2⟩)).continuousAt.congr ?_).continuousWithinAt
      filter_upwards [eventually_ne_nhds hax.ne'] with y hy using (hd'eq y hy).symm
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hd'c
  have hBd : ∀ s ∈ Ioc a t, ‖d s‖ ≤ B := fun s hs => by
    rw [← hd'eq s hs.1.ne']
    exact hB s ⟨hs.1.le, hs.2⟩
  have heq : ∀ s ∈ Ioc a t, d s = ∫ x in a..s, M x (d x) := fun s hs => by
    have hsJ : s ∈ J := hJc t ht hs
    have hsub : Ioc a s ⊆ J := hJc s hsJ
    have hint_s : IntervalIntegrable (fun x => M x (d x)) volume a s := by
      refine lv_intervalIntegrable_apply (B := B) (by rw [uIoc_of_le hs.1.le]; exact hint s hsJ)
        ?_ fun x hx => ?_
      · rw [uIoc_of_le hs.1.le]
        exact ((hM.mono hsub).clm_apply fun x hx =>
          (hd x (hsub hx)).continuousAt.continuousWithinAt).aestronglyMeasurable
          measurableSet_Ioc
      · rw [uIoc_of_le hs.1.le] at hx
        exact hBd x ⟨hx.1, hx.2.trans hs.2⟩
    have hderiv : ∀ x ∈ Ioo a s, HasDerivAt d' (M x (d x)) x := fun x hx =>
      (hd x (hsub ⟨hx.1, hx.2.le⟩)).congr_of_eventuallyEq
        (by filter_upwards [eventually_ne_nhds hx.1.ne'] with y hy using hd'eq y hy)
    rw [integral_eq_sub_of_hasDerivAt_of_le hs.1.le (hd'c.mono (Icc_subset_Icc_right hs.2))
      hderiv hint_s, hd'eq s hs.1.ne', hd'_def, Function.update_self, sub_zero]
  have hMc : ContinuousOn M (Ι a t) := by
    rw [uIoc_of_le hat.le]
    exact hM.mono (hJc t ht)
  have hMi : IntegrableOn (fun s => ‖M s‖) (Ι a t) := by
    rw [uIoc_of_le hat.le]
    exact hint t ht
  have h := volterra_eq_zero hMc hMi (B := B) (fun s hs => hBd s (by rwa [uIoc_of_le hat.le] at hs))
    (fun s hs => heq s (by rwa [uIoc_of_le hat.le] at hs)) (heq t ⟨hat, le_rfl⟩)
  exact sub_eq_zero.1 h

end Core

end ModeStability.ODE
