module

public import Mathlib
public import ModeStability.ODE.LinearStabilityAux

/-!
# Stability of linear systems with a singular or an infinite endpoint

Quantitative stability estimates for first-order linear systems `v' = M(t) v`, `w' = N(t) w`,
independent of how the solutions are constructed, and the resulting continuity of solutions in a
parameter. They are used for the continuity in the frequency `ω` of the normalized solutions
`R_H`, `R_I` of Prop. 6.1 of the all-angular paper (`horizon_solution_continuous`,
`infinity_solution_continuous` in the Proposition 6.1 interface), built by
`ModeStability.ODE.LinearVolterra`.

The statements are generic: `E` is a real normed space which is also a normed space over a field
`𝕜`, and the coefficients are `M N : ℝ → E →L[𝕜] E`. With `E = ℂ × ℂ` (sup norm) and `𝕜 = ℂ`
this is the coefficient type `ℝ → ℂ × ℂ →L[ℂ] ℂ × ℂ` of `ModeStability.ODE.LinearVolterra`.
Completeness of `E` is not needed. Writing `u = v − w`,
`u' = M u + (M − N) w`, and Grönwall's inequality with variable coefficients
(`ls_norm_le_of_norm_deriv_le`) gives, on a compact interval,
`‖u t‖ ≤ (‖u s‖ + ∫ ‖(M − N) w‖) exp (∫ ‖M‖)`, forwards and backwards; the endpoint versions are
its limits as the base point tends to the endpoint.

Main statements:

* interior, on `[s, t]` with continuous coefficients: `norm_sub_le_of_Icc` (from `s` to `t`) and
  `norm_sub_le_of_Icc_backward` (from `t` to `s`);
* horizon side, at a singular left endpoint `a` where the coefficient is bounded or only
  integrable: `norm_sub_le_of_nhdsGT` (`‖M‖ ≤ C`, factor `exp (C (t − a))`) and
  `norm_sub_le_of_nhdsGT_integral` (factor `exp (∫ x in a..t, ‖M x‖)`);
* infinity side, with `‖M‖` integrable at `+∞`: `norm_sub_le_of_atTop`;
* the `_of_le` variants with a general continuous majorant `g ≥ ‖(M − N) w‖`;
* parameter dependence: for a family of solutions `v ω` of `v' = M ω v` with data `v₀ ω` at `a⁺`
  (resp. `vI ω` at `+∞`), continuous data and `∫ ‖M ω − M ω₀‖ → 0` as `ω → ω₀`,
  `(ω, t) ↦ v ω t` is continuous on `S ×ˢ (a, ∞)`: `continuousOn_of_nhdsGT`,
  `continuousOn_of_atTop`; `continuousOn_deriv_of_continuousOn` gives the joint continuity of the
  derivative, and `tendsto_integral_norm_sub_of_dominated` (on a measurable set `A`) and
  `tendsto_intervalIntegral_norm_sub_of_dominated` (on `(a, t]`) give the hypothesis
  `∫ ‖M ω − M ω₀‖ → 0` from pointwise convergence in `ω` and a dominating function.

No equicontinuity in `t` is needed for the joint continuity: the estimates are uniform in `t` on
`(a, T]` (resp. `[T, ∞)`), and uniform convergence to a continuous limit gives joint continuity.
-/

public section

namespace ModeStability.ODE

open Set Filter Topology MeasureTheory

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] {M N : ℝ → E →L[𝕜] E} {v w : ℝ → E}

section Interior

/-- The difference of two solutions satisfies `‖u'‖ ≤ ‖M‖ ‖u‖ + g`. -/
theorem ls_hasDerivAt_sub {g : ℝ → ℝ} {S : Set ℝ} (hv : ∀ x ∈ S, HasDerivAt v (M x (v x)) x)
    (hw : ∀ x ∈ S, HasDerivAt w (N x (w x)) x) (hgb : ∀ x ∈ S, ‖(M x - N x) (w x)‖ ≤ g x) :
    ∀ x ∈ S, HasDerivAt (fun y => v y - w y) (M x (v x) - N x (w x)) x ∧
      ‖M x (v x) - N x (w x)‖ ≤ ‖M x‖ * ‖v x - w x‖ + g x := fun x hx =>
  ⟨(hv x hx).sub (hw x hx), (ls_norm_apply_sub_le _ _ _ _).trans (by gcongr; exact hgb x hx)⟩

/-- **Interior stability, forwards**, with a continuous majorant `g ≥ ‖(M − N) w‖`. -/
theorem norm_sub_le_of_Icc_of_le {g : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hM : ContinuousOn M (Icc s t)) (hv : ∀ x ∈ Icc s t, HasDerivAt v (M x (v x)) x)
    (hw : ∀ x ∈ Icc s t, HasDerivAt w (N x (w x)) x) (hg : ContinuousOn g (Icc s t))
    (hgb : ∀ x ∈ Icc s t, ‖(M x - N x) (w x)‖ ≤ g x) :
    ‖v t - w t‖ ≤ (‖v s - w s‖ + ∫ x in s..t, g x) * Real.exp (∫ x in s..t, ‖M x‖) := by
  have hd := ls_hasDerivAt_sub hv hw hgb
  exact ls_norm_le_of_norm_deriv_le hst (fun x hx => (hd x hx).1.continuousAt.continuousWithinAt)
    (fun x hx => (hd x (Ico_subset_Icc_self hx)).1.hasDerivWithinAt) hM.norm hg
    (fun _ _ => norm_nonneg _) (fun x hx => (norm_nonneg _).trans (hgb x hx))
    (fun x hx => (hd x (Ico_subset_Icc_self hx)).2)

/-- **Interior stability, backwards**, with a continuous majorant `g ≥ ‖(M − N) w‖`. -/
theorem norm_sub_le_of_Icc_backward_of_le {g : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hM : ContinuousOn M (Icc s t)) (hv : ∀ x ∈ Icc s t, HasDerivAt v (M x (v x)) x)
    (hw : ∀ x ∈ Icc s t, HasDerivAt w (N x (w x)) x) (hg : ContinuousOn g (Icc s t))
    (hgb : ∀ x ∈ Icc s t, ‖(M x - N x) (w x)‖ ≤ g x) :
    ‖v s - w s‖ ≤ (‖v t - w t‖ + ∫ x in s..t, g x) * Real.exp (∫ x in s..t, ‖M x‖) := by
  have hd := ls_hasDerivAt_sub hv hw hgb
  exact ls_norm_le_of_norm_deriv_le_backward hst (fun x hx => (hd x hx).1) hM.norm hg
    (fun _ _ => norm_nonneg _) (fun x hx => (norm_nonneg _).trans (hgb x hx))
    (fun x hx => (hd x hx).2)

/-- **Interior stability, forwards.** For solutions of `v' = M v`, `w' = N w` on `[s, t]` with
continuous coefficients and `‖w‖ ≤ W`:
`‖v t − w t‖ ≤ (‖v s − w s‖ + (∫ ‖M − N‖) W) exp (∫ ‖M‖)`. -/
theorem norm_sub_le_of_Icc {s t W : ℝ} (hst : s ≤ t) (hM : ContinuousOn M (Icc s t))
    (hN : ContinuousOn N (Icc s t)) (hv : ∀ x ∈ Icc s t, HasDerivAt v (M x (v x)) x)
    (hw : ∀ x ∈ Icc s t, HasDerivAt w (N x (w x)) x) (hW : ∀ x ∈ Icc s t, ‖w x‖ ≤ W) :
    ‖v t - w t‖ ≤
      (‖v s - w s‖ + (∫ x in s..t, ‖M x - N x‖) * W) * Real.exp (∫ x in s..t, ‖M x‖) := by
  rw [← intervalIntegral.integral_mul_const]
  exact norm_sub_le_of_Icc_of_le hst hM hv hw ((hM.sub hN).norm.mul continuousOn_const)
    fun x hx => ls_norm_apply_le_of_le (hW x hx)

/-- **Interior stability, backwards.** For solutions of `v' = M v`, `w' = N w` on `[s, t]` with
continuous coefficients and `‖w‖ ≤ W`:
`‖v s − w s‖ ≤ (‖v t − w t‖ + (∫ ‖M − N‖) W) exp (∫ ‖M‖)`. -/
theorem norm_sub_le_of_Icc_backward {s t W : ℝ} (hst : s ≤ t) (hM : ContinuousOn M (Icc s t))
    (hN : ContinuousOn N (Icc s t)) (hv : ∀ x ∈ Icc s t, HasDerivAt v (M x (v x)) x)
    (hw : ∀ x ∈ Icc s t, HasDerivAt w (N x (w x)) x) (hW : ∀ x ∈ Icc s t, ‖w x‖ ≤ W) :
    ‖v s - w s‖ ≤
      (‖v t - w t‖ + (∫ x in s..t, ‖M x - N x‖) * W) * Real.exp (∫ x in s..t, ‖M x‖) := by
  rw [← intervalIntegral.integral_mul_const]
  exact norm_sub_le_of_Icc_backward_of_le hst hM hv hw ((hM.sub hN).norm.mul continuousOn_const)
    fun x hx => ls_norm_apply_le_of_le (hW x hx)

end Interior

section Horizon

/-- **Stability at a singular left endpoint**, with a continuous integrable majorant
`g ≥ ‖(M − N) w‖`: if `v → v₀`, `w → w₀` as `t ↓ a` and `‖M‖` is integrable on `(a, t]`, then
`‖v t − w t‖ ≤ (‖v₀ − w₀‖ + ∫ x in a..t, g x) * exp (∫ x in a..t, ‖M x‖)`. -/
theorem norm_sub_le_of_nhdsGT_of_le {g : ℝ → ℝ} {a t : ℝ} {v₀ w₀ : E} (hat : a < t)
    (hM : ContinuousOn M (Ioc a t)) (hv : ∀ x ∈ Ioc a t, HasDerivAt v (M x (v x)) x)
    (hw : ∀ x ∈ Ioc a t, HasDerivAt w (N x (w x)) x)
    (hv0 : Tendsto v (𝓝[>] a) (𝓝 v₀)) (hw0 : Tendsto w (𝓝[>] a) (𝓝 w₀))
    (hMi : IntegrableOn (fun x => ‖M x‖) (Ioc a t))
    (hg : ContinuousOn g (Ioc a t)) (hgi : IntegrableOn g (Ioc a t))
    (hgb : ∀ x ∈ Ioc a t, ‖(M x - N x) (w x)‖ ≤ g x) :
    ‖v t - w t‖ ≤ (‖v₀ - w₀‖ + ∫ x in a..t, g x) * Real.exp (∫ x in a..t, ‖M x‖) := by
  have hsub : ∀ s ∈ Ioo a t, Icc s t ⊆ Ioc a t := fun s hs x hx => ⟨hs.1.trans_le hx.1, hx.2⟩
  have hev : ∀ᶠ s in 𝓝[>] a, ‖v t - w t‖ ≤
      (‖v s - w s‖ + ∫ x in s..t, g x) * Real.exp (∫ x in s..t, ‖M x‖) := by
    filter_upwards [Ioo_mem_nhdsGT hat] with s hs
    exact norm_sub_le_of_Icc_of_le hs.2.le (hM.mono (hsub s hs))
      (fun x hx => hv x (hsub s hs hx)) (fun x hx => hw x (hsub s hs hx)) (hg.mono (hsub s hs))
      (fun x hx => hgb x (hsub s hs hx))
  have hlim : Tendsto (fun s => (‖v s - w s‖ + ∫ x in s..t, g x) *
      Real.exp (∫ x in s..t, ‖M x‖)) (𝓝[>] a)
      (𝓝 ((‖v₀ - w₀‖ + ∫ x in a..t, g x) * Real.exp (∫ x in a..t, ‖M x‖))) :=
    ((hv0.sub hw0).norm.add (ls_tendsto_integral_nhdsGT hat hgi)).mul
      (ls_tendsto_integral_nhdsGT hat hMi).rexp
  exact ge_of_tendsto hlim hev

/-- **Stability at a singular left endpoint.** For solutions of `v' = M v`, `w' = N w` on
`(a, t]` with `v → v₀`, `w → w₀` as `t ↓ a`, `‖M‖` and `‖M − N‖` integrable on `(a, t]` and
`‖w‖ ≤ W` there:
`‖v t − w t‖ ≤ (‖v₀ − w₀‖ + (∫ x in a..t, ‖M x − N x‖) W) exp (∫ x in a..t, ‖M x‖)`. -/
theorem norm_sub_le_of_nhdsGT_integral {a t W : ℝ} {v₀ w₀ : E} (hat : a < t)
    (hM : ContinuousOn M (Ioc a t)) (hN : ContinuousOn N (Ioc a t))
    (hv : ∀ x ∈ Ioc a t, HasDerivAt v (M x (v x)) x)
    (hw : ∀ x ∈ Ioc a t, HasDerivAt w (N x (w x)) x)
    (hv0 : Tendsto v (𝓝[>] a) (𝓝 v₀)) (hw0 : Tendsto w (𝓝[>] a) (𝓝 w₀))
    (hMi : IntegrableOn (fun x => ‖M x‖) (Ioc a t))
    (hMN : IntegrableOn (fun x => ‖M x - N x‖) (Ioc a t)) (hW : ∀ x ∈ Ioc a t, ‖w x‖ ≤ W) :
    ‖v t - w t‖ ≤
      (‖v₀ - w₀‖ + (∫ x in a..t, ‖M x - N x‖) * W) * Real.exp (∫ x in a..t, ‖M x‖) := by
  rw [← intervalIntegral.integral_mul_const]
  exact norm_sub_le_of_nhdsGT_of_le hat hM hv hw hv0 hw0 hMi
    ((hM.sub hN).norm.mul continuousOn_const) (hMN.mul_const W)
    fun x hx => ls_norm_apply_le_of_le (hW x hx)

/-- **Stability at a singular left endpoint with a bounded coefficient.** For solutions of
`v' = M v`, `w' = N w` on `(a, t]` with `v → v₀`, `w → w₀` as `t ↓ a`, `‖M‖ ≤ C` and `‖w‖ ≤ W`
on `(a, t]`, and `‖M − N‖` integrable there:
`‖v t − w t‖ ≤ (‖v₀ − w₀‖ + (∫ x in a..t, ‖M x − N x‖) W) exp (C (t − a))`. -/
theorem norm_sub_le_of_nhdsGT {a t C W : ℝ} {v₀ w₀ : E} (hat : a < t)
    (hM : ContinuousOn M (Ioc a t)) (hN : ContinuousOn N (Ioc a t))
    (hv : ∀ x ∈ Ioc a t, HasDerivAt v (M x (v x)) x)
    (hw : ∀ x ∈ Ioc a t, HasDerivAt w (N x (w x)) x)
    (hv0 : Tendsto v (𝓝[>] a) (𝓝 v₀)) (hw0 : Tendsto w (𝓝[>] a) (𝓝 w₀))
    (hC : ∀ x ∈ Ioc a t, ‖M x‖ ≤ C)
    (hMN : IntegrableOn (fun x => ‖M x - N x‖) (Ioc a t)) (hW : ∀ x ∈ Ioc a t, ‖w x‖ ≤ W) :
    ‖v t - w t‖ ≤
      (‖v₀ - w₀‖ + (∫ x in a..t, ‖M x - N x‖) * W) * Real.exp (C * (t - a)) := by
  have hMi : IntegrableOn (fun x => ‖M x‖) (Ioc a t) :=
    ls_integrableOn_norm_of_le measurableSet_Ioc measure_Ioc_lt_top.ne hM hC
  have hK : ∫ x in a..t, ‖M x‖ ≤ C * (t - a) := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hat.le
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat.le).2 hMi) intervalIntegrable_const
      fun x hx => hC x (Ioo_subset_Ioc_self hx)
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW t ⟨hat, le_rfl⟩)
  have hI0 : 0 ≤ ∫ x in a..t, ‖M x - N x‖ :=
    intervalIntegral.integral_nonneg hat.le fun _ _ => norm_nonneg _
  refine (norm_sub_le_of_nhdsGT_integral hat hM hN hv hw hv0 hw0 hMi hMN hW).trans ?_
  gcongr

end Horizon

section Infinity

/-- **Stability at `+∞`**, with a continuous integrable majorant `g ≥ ‖(M − N) w‖`: if `v → vI`,
`w → wI` at `+∞` and `‖M‖` is integrable on `(t, ∞)`, then
`‖v t − w t‖ ≤ (‖vI − wI‖ + ∫ x in Ioi t, g x) * exp (∫ x in Ioi t, ‖M x‖)`. -/
theorem norm_sub_le_of_atTop_of_le {g : ℝ → ℝ} {t : ℝ} {vI wI : E}
    (hM : ContinuousOn M (Ici t)) (hv : ∀ x ∈ Ici t, HasDerivAt v (M x (v x)) x)
    (hw : ∀ x ∈ Ici t, HasDerivAt w (N x (w x)) x)
    (hvI : Tendsto v atTop (𝓝 vI)) (hwI : Tendsto w atTop (𝓝 wI))
    (hMi : IntegrableOn (fun x => ‖M x‖) (Ioi t))
    (hg : ContinuousOn g (Ici t)) (hgi : IntegrableOn g (Ioi t))
    (hgb : ∀ x ∈ Ici t, ‖(M x - N x) (w x)‖ ≤ g x) :
    ‖v t - w t‖ ≤ (‖vI - wI‖ + ∫ x in Ioi t, g x) * Real.exp (∫ x in Ioi t, ‖M x‖) := by
  have hev : ∀ᶠ T in atTop, ‖v t - w t‖ ≤
      (‖v T - w T‖ + ∫ x in t..T, g x) * Real.exp (∫ x in t..T, ‖M x‖) := by
    filter_upwards [eventually_ge_atTop t] with T hT
    exact norm_sub_le_of_Icc_backward_of_le hT (hM.mono Icc_subset_Ici_self)
      (fun x hx => hv x hx.1) (fun x hx => hw x hx.1) (hg.mono Icc_subset_Ici_self)
      (fun x hx => hgb x hx.1)
  have hlim : Tendsto (fun T => (‖v T - w T‖ + ∫ x in t..T, g x) *
      Real.exp (∫ x in t..T, ‖M x‖)) atTop
      (𝓝 ((‖vI - wI‖ + ∫ x in Ioi t, g x) * Real.exp (∫ x in Ioi t, ‖M x‖))) :=
    ((hvI.sub hwI).norm.add (intervalIntegral_tendsto_integral_Ioi t hgi tendsto_id)).mul
      (intervalIntegral_tendsto_integral_Ioi t hMi tendsto_id).rexp
  exact ge_of_tendsto hlim hev

/-- **Stability at `+∞`.** For solutions of `v' = M v`, `w' = N w` on `[t, ∞)` with `v → vI`,
`w → wI` at `+∞`, `‖M‖` and `‖M − N‖` integrable on `(t, ∞)` and `‖w‖ ≤ W` on `[t, ∞)`:
`‖v t − w t‖ ≤ (‖vI − wI‖ + (∫ x in Ioi t, ‖M x − N x‖) W) exp (∫ x in Ioi t, ‖M x‖)`. -/
theorem norm_sub_le_of_atTop {t W : ℝ} {vI wI : E} (hM : ContinuousOn M (Ici t))
    (hN : ContinuousOn N (Ici t)) (hv : ∀ x ∈ Ici t, HasDerivAt v (M x (v x)) x)
    (hw : ∀ x ∈ Ici t, HasDerivAt w (N x (w x)) x)
    (hvI : Tendsto v atTop (𝓝 vI)) (hwI : Tendsto w atTop (𝓝 wI))
    (hMi : IntegrableOn (fun x => ‖M x‖) (Ioi t))
    (hMN : IntegrableOn (fun x => ‖M x - N x‖) (Ioi t)) (hW : ∀ x ∈ Ici t, ‖w x‖ ≤ W) :
    ‖v t - w t‖ ≤
      (‖vI - wI‖ + (∫ x in Ioi t, ‖M x - N x‖) * W) * Real.exp (∫ x in Ioi t, ‖M x‖) := by
  rw [← integral_mul_const]
  exact norm_sub_le_of_atTop_of_le hM hv hw hvI hwI hMi
    ((hM.sub hN).norm.mul continuousOn_const) (hMN.mul_const W)
    fun x hx => ls_norm_apply_le_of_le (hW x hx)

end Infinity

section Parametric

variable {Λ : Type*} [TopologicalSpace Λ] {S : Set Λ} {Mf : Λ → ℝ → E →L[𝕜] E}
  {vf : Λ → ℝ → E}

/-- **Continuity in a parameter, horizon side.** Let `vf ω` (for `ω ∈ S`) solve
`v' = Mf ω v` on `(a, ∞)`, with `Mf ω` continuous there, `‖Mf ω‖` integrable on every `(a, t]`,
and `vf ω → v₀ ω` as `t ↓ a`. If `v₀` is continuous on `S` and
`∫ x in a..t, ‖Mf ω x − Mf ω₀ x‖ → 0` as `ω → ω₀` in `S`, for every `ω₀ ∈ S` and `t > a`, then
`(ω, t) ↦ vf ω t` is continuous on `S ×ˢ (a, ∞)`. -/
theorem continuousOn_of_nhdsGT {a : ℝ} {v₀ : Λ → E}
    (hM : ∀ ω ∈ S, ContinuousOn (Mf ω) (Ioi a))
    (hv : ∀ ω ∈ S, ∀ t ∈ Ioi a, HasDerivAt (vf ω) (Mf ω t (vf ω t)) t)
    (hv0 : ∀ ω ∈ S, Tendsto (vf ω) (𝓝[>] a) (𝓝 (v₀ ω)))
    (hMi : ∀ ω ∈ S, ∀ t ∈ Ioi a, IntegrableOn (fun x => ‖Mf ω x‖) (Ioc a t))
    (hv0c : ContinuousOn v₀ S)
    (hMc : ∀ ω₀ ∈ S, ∀ t ∈ Ioi a,
      Tendsto (fun ω => ∫ x in a..t, ‖Mf ω x - Mf ω₀ x‖) (𝓝[S] ω₀) (𝓝 0)) :
    ContinuousOn (fun p : Λ × ℝ => vf p.1 p.2) (S ×ˢ Ioi a) := by
  rintro ⟨ω₀, t₀⟩ ⟨hω₀, ht₀⟩
  have ht₀' : a < t₀ := ht₀
  have haT : a < t₀ + 1 := by linarith
  obtain ⟨B, hB⟩ := ls_exists_bound_nhdsGT (v := vf ω₀) (T := t₀ + 1)
    (fun x hx => (hv ω₀ hω₀ x hx.1).continuousAt.continuousWithinAt) (hv0 ω₀ hω₀)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ ⟨haT, le_rfl⟩)
  have hMi' : ∀ ω ∈ S, IntervalIntegrable (fun x => ‖Mf ω x‖) volume a (t₀ + 1) :=
    fun ω hω => (intervalIntegrable_iff_integrableOn_Ioc_of_le haT.le).2 (hMi ω hω _ haT)
  have hMNi : ∀ ω ∈ S, IntegrableOn (fun x => ‖Mf ω x - Mf ω₀ x‖) (Ioc a (t₀ + 1)) :=
    fun ω hω => ls_integrableOn_norm_sub measurableSet_Ioc ((hM ω hω).mono Ioc_subset_Ioi_self)
      ((hM ω₀ hω₀).mono Ioc_subset_Ioi_self) (hMi ω hω _ haT) (hMi ω₀ hω₀ _ haT)
  have hMNi' : ∀ ω ∈ S, IntervalIntegrable (fun x => ‖Mf ω x - Mf ω₀ x‖) volume a (t₀ + 1) :=
    fun ω hω => (intervalIntegrable_iff_integrableOn_Ioc_of_le haT.le).2 (hMNi ω hω)
  refine ls_continuousWithinAt_of_uniform (Iio_mem_nhds (lt_add_one t₀))
    (δ := fun ω => (‖v₀ ω - v₀ ω₀‖ + (∫ x in a..t₀ + 1, ‖Mf ω x - Mf ω₀ x‖) * B) *
      Real.exp ((∫ x in a..t₀ + 1, ‖Mf ω₀ x‖) + ∫ x in a..t₀ + 1, ‖Mf ω x - Mf ω₀ x‖))
    (fun ω hω t ht htT => ?_) ?_ (hv ω₀ hω₀ t₀ ht₀).continuousAt
  · have ht : t ∈ Ioc a (t₀ + 1) := ⟨ht, le_of_lt htT⟩
    have hsub : Ioc a t ⊆ Ioc a (t₀ + 1) := Ioc_subset_Ioc_right ht.2
    have h := norm_sub_le_of_nhdsGT_integral ht.1 ((hM ω hω).mono Ioc_subset_Ioi_self)
      ((hM ω₀ hω₀).mono Ioc_subset_Ioi_self) (fun x hx => hv ω hω x hx.1)
      (fun x hx => hv ω₀ hω₀ x hx.1) (hv0 ω hω) (hv0 ω₀ hω₀) (hMi ω hω t ht.1)
      ((hMNi ω hω).mono_set hsub) (fun x hx => hB x (hsub hx))
    refine h.trans ?_
    have hI : ∫ x in a..t, ‖Mf ω x - Mf ω₀ x‖ ≤ ∫ x in a..t₀ + 1, ‖Mf ω x - Mf ω₀ x‖ :=
      intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2
        (Eventually.of_forall fun _ => norm_nonneg _) (hMNi' ω hω)
    have hK : ∫ x in a..t, ‖Mf ω x‖ ≤
        (∫ x in a..t₀ + 1, ‖Mf ω₀ x‖) + ∫ x in a..t₀ + 1, ‖Mf ω x - Mf ω₀ x‖ := by
      calc ∫ x in a..t, ‖Mf ω x‖ ≤ ∫ x in a..t₀ + 1, ‖Mf ω x‖ :=
            intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2
              (Eventually.of_forall fun _ => norm_nonneg _) (hMi' ω hω)
        _ ≤ ∫ x in a..t₀ + 1, (‖Mf ω₀ x‖ + ‖Mf ω x - Mf ω₀ x‖) :=
            intervalIntegral.integral_mono_on haT.le (hMi' ω hω)
              ((hMi' ω₀ hω₀).add (hMNi' ω hω)) fun x _ => norm_le_norm_add_norm_sub' _ _
        _ = _ := intervalIntegral.integral_add (hMi' ω₀ hω₀) (hMNi' ω hω)
    have hI0 : 0 ≤ ∫ x in a..t, ‖Mf ω x - Mf ω₀ x‖ :=
      intervalIntegral.integral_nonneg ht.1.le fun _ _ => norm_nonneg _
    have hpos : 0 ≤ ‖v₀ ω - v₀ ω₀‖ + (∫ x in a..t₀ + 1, ‖Mf ω x - Mf ω₀ x‖) * B :=
      add_nonneg (norm_nonneg _) (mul_nonneg (hI0.trans hI) hB0)
    gcongr
  · have h1 : Tendsto (fun ω => ‖v₀ ω - v₀ ω₀‖) (𝓝[S] ω₀) (𝓝 0) := by
      simpa using ((hv0c ω₀ hω₀).tendsto.sub_const (v₀ ω₀)).norm
    have h2 := hMc ω₀ hω₀ _ haT
    simpa using (h1.add (h2.mul_const B)).mul (h2.const_add _).rexp

/-- **Continuity in a parameter, infinity side.** Let `vf ω` (for `ω ∈ S`) solve `v' = Mf ω v`
on `(a, ∞)`, with `Mf ω` continuous there, `‖Mf ω‖` integrable on every `(t, ∞)`, `t > a`, and
`vf ω → vI ω` at `+∞`. If `vI` is continuous on `S` and
`∫ x in Ioi t, ‖Mf ω x − Mf ω₀ x‖ → 0` as `ω → ω₀` in `S`, for every `ω₀ ∈ S` and `t > a`, then
`(ω, t) ↦ vf ω t` is continuous on `S ×ˢ (a, ∞)`. -/
theorem continuousOn_of_atTop {a : ℝ} {vI : Λ → E}
    (hM : ∀ ω ∈ S, ContinuousOn (Mf ω) (Ioi a))
    (hv : ∀ ω ∈ S, ∀ t ∈ Ioi a, HasDerivAt (vf ω) (Mf ω t (vf ω t)) t)
    (hvI : ∀ ω ∈ S, Tendsto (vf ω) atTop (𝓝 (vI ω)))
    (hMi : ∀ ω ∈ S, ∀ t ∈ Ioi a, IntegrableOn (fun x => ‖Mf ω x‖) (Ioi t))
    (hvIc : ContinuousOn vI S)
    (hMc : ∀ ω₀ ∈ S, ∀ t ∈ Ioi a,
      Tendsto (fun ω => ∫ x in Ioi t, ‖Mf ω x - Mf ω₀ x‖) (𝓝[S] ω₀) (𝓝 0)) :
    ContinuousOn (fun p : Λ × ℝ => vf p.1 p.2) (S ×ˢ Ioi a) := by
  rintro ⟨ω₀, t₀⟩ ⟨hω₀, ht₀⟩
  have ht₀' : a < t₀ := ht₀
  set T := (a + t₀) / 2 with hT_def
  have haT : a < T := by linarith
  have hTt : T < t₀ := by linarith
  have hsubT : Ici T ⊆ Ioi a := fun x hx => haT.trans_le hx
  obtain ⟨B, hB⟩ := ls_exists_bound_atTop (v := vf ω₀) (T := T)
    (fun x hx => (hv ω₀ hω₀ x (hsubT hx)).continuousAt.continuousWithinAt) (hvI ω₀ hω₀)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB T le_rfl)
  have hMNi : ∀ ω ∈ S, IntegrableOn (fun x => ‖Mf ω x - Mf ω₀ x‖) (Ioi T) :=
    fun ω hω => ls_integrableOn_norm_sub measurableSet_Ioi
      ((hM ω hω).mono fun x hx => haT.trans hx) ((hM ω₀ hω₀).mono fun x hx => haT.trans hx)
      (hMi ω hω T haT) (hMi ω₀ hω₀ T haT)
  refine ls_continuousWithinAt_of_uniform (Ioi_mem_nhds hTt)
    (δ := fun ω => (‖vI ω - vI ω₀‖ + (∫ x in Ioi T, ‖Mf ω x - Mf ω₀ x‖) * B) *
      Real.exp ((∫ x in Ioi T, ‖Mf ω₀ x‖) + ∫ x in Ioi T, ‖Mf ω x - Mf ω₀ x‖))
    (fun ω hω t ht hTt' => ?_) ?_ (hv ω₀ hω₀ t₀ ht₀).continuousAt
  · have hTt'' : T < t := hTt'
    have hsub : Ici t ⊆ Ioi a := fun x hx => ht.trans_le hx
    have hsub' : Ioi t ⊆ Ioi T := Ioi_subset_Ioi hTt''.le
    have h := norm_sub_le_of_atTop ((hM ω hω).mono hsub) ((hM ω₀ hω₀).mono hsub)
      (fun x hx => hv ω hω x (hsub hx)) (fun x hx => hv ω₀ hω₀ x (hsub hx)) (hvI ω hω)
      (hvI ω₀ hω₀) (hMi ω hω t ht) ((hMNi ω hω).mono_set hsub')
      (fun x hx => hB x (hTt''.le.trans hx))
    refine h.trans ?_
    have hI : ∫ x in Ioi t, ‖Mf ω x - Mf ω₀ x‖ ≤ ∫ x in Ioi T, ‖Mf ω x - Mf ω₀ x‖ :=
      setIntegral_mono_set (hMNi ω hω) (Eventually.of_forall fun _ => norm_nonneg _)
        hsub'.eventuallyLE
    have hK : ∫ x in Ioi t, ‖Mf ω x‖ ≤
        (∫ x in Ioi T, ‖Mf ω₀ x‖) + ∫ x in Ioi T, ‖Mf ω x - Mf ω₀ x‖ := by
      calc ∫ x in Ioi t, ‖Mf ω x‖ ≤ ∫ x in Ioi T, ‖Mf ω x‖ :=
            setIntegral_mono_set (hMi ω hω T haT) (Eventually.of_forall fun _ => norm_nonneg _)
              hsub'.eventuallyLE
        _ ≤ ∫ x in Ioi T, (‖Mf ω₀ x‖ + ‖Mf ω x - Mf ω₀ x‖) :=
            setIntegral_mono (hMi ω hω T haT) ((hMi ω₀ hω₀ T haT).add (hMNi ω hω))
              fun x => norm_le_norm_add_norm_sub' _ _
        _ = _ := integral_add (hMi ω₀ hω₀ T haT) (hMNi ω hω)
    have hI0 : 0 ≤ ∫ x in Ioi t, ‖Mf ω x - Mf ω₀ x‖ :=
      setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _
    have hpos : 0 ≤ ‖vI ω - vI ω₀‖ + (∫ x in Ioi T, ‖Mf ω x - Mf ω₀ x‖) * B :=
      add_nonneg (norm_nonneg _) (mul_nonneg (hI0.trans hI) hB0)
    gcongr
  · have h1 : Tendsto (fun ω => ‖vI ω - vI ω₀‖) (𝓝[S] ω₀) (𝓝 0) := by
      simpa using ((hvIc ω₀ hω₀).tendsto.sub_const (vI ω₀)).norm
    have h2 := hMc ω₀ hω₀ T haT
    simpa using (h1.add (h2.mul_const B)).mul (h2.const_add _).rexp

/-- **Joint continuity of the derivative.** If `(ω, t) ↦ vf ω t` and `(ω, t) ↦ Mf ω t` are
continuous on `S ×ˢ D` and `vf ω' = Mf ω (vf ω)` on `D`, then `(ω, t) ↦ deriv (vf ω) t` is
continuous on `S ×ˢ D`. -/
theorem continuousOn_deriv_of_continuousOn {D : Set ℝ}
    (hv : ∀ ω ∈ S, ∀ t ∈ D, HasDerivAt (vf ω) (Mf ω t (vf ω t)) t)
    (hMc : ContinuousOn (fun p : Λ × ℝ => Mf p.1 p.2) (S ×ˢ D))
    (hvc : ContinuousOn (fun p : Λ × ℝ => vf p.1 p.2) (S ×ˢ D)) :
    ContinuousOn (fun p : Λ × ℝ => deriv (vf p.1) p.2) (S ×ˢ D) :=
  (hMc.clm_apply hvc).congr fun p hp => (hv p.1 hp.1 p.2 hp.2).deriv

end Parametric

section Dominated

variable {ι F : Type*} [NormedAddCommGroup F] {l : Filter ι} [l.IsCountablyGenerated]

/-- **The hypothesis `∫ ‖M ω − M₀‖ → 0` by dominated convergence.** If `M ω x → M₀ x` for every
`x ∈ A` and `‖M ω‖`, `‖M₀‖` are dominated on `A` by an integrable function, then
`∫ x in A, ‖M ω x − M₀ x‖ → 0`. -/
theorem tendsto_integral_norm_sub_of_dominated {A : Set ℝ} (hA : MeasurableSet A)
    {Mf : ι → ℝ → F} {M₀ : ℝ → F} {bound : ℝ → ℝ}
    (hmeas : ∀ᶠ ω in l, AEStronglyMeasurable (Mf ω) (volume.restrict A))
    (hM₀ : AEStronglyMeasurable M₀ (volume.restrict A))
    (hbd : ∀ᶠ ω in l, ∀ x ∈ A, ‖Mf ω x‖ ≤ bound x) (hbd₀ : ∀ x ∈ A, ‖M₀ x‖ ≤ bound x)
    (hint : IntegrableOn bound A) (hlim : ∀ x ∈ A, Tendsto (fun ω => Mf ω x) l (𝓝 (M₀ x))) :
    Tendsto (fun ω => ∫ x in A, ‖Mf ω x - M₀ x‖) l (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (l := l) (μ := volume.restrict A)
    (F := fun ω x => ‖Mf ω x - M₀ x‖) (f := fun _ => (0 : ℝ)) (fun x => 2 * bound x) ?_ ?_
    (hint.const_mul 2) ?_
  · simpa using h
  · filter_upwards [hmeas] with ω hω using (hω.sub hM₀).norm
  · filter_upwards [hbd] with ω hω
    refine (ae_restrict_iff' hA).2 (Eventually.of_forall fun x hx => ?_)
    rw [norm_norm, two_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hω x hx) (hbd₀ x hx))
  · refine (ae_restrict_iff' hA).2 (Eventually.of_forall fun x hx => ?_)
    simpa using ((hlim x hx).sub_const (M₀ x)).norm

/-- The interval-integral form of `tendsto_integral_norm_sub_of_dominated` on `(a, t]`. -/
theorem tendsto_intervalIntegral_norm_sub_of_dominated {a t : ℝ} (hat : a ≤ t)
    {Mf : ι → ℝ → F} {M₀ : ℝ → F} {bound : ℝ → ℝ}
    (hmeas : ∀ᶠ ω in l, AEStronglyMeasurable (Mf ω) (volume.restrict (Ioc a t)))
    (hM₀ : AEStronglyMeasurable M₀ (volume.restrict (Ioc a t)))
    (hbd : ∀ᶠ ω in l, ∀ x ∈ Ioc a t, ‖Mf ω x‖ ≤ bound x)
    (hbd₀ : ∀ x ∈ Ioc a t, ‖M₀ x‖ ≤ bound x) (hint : IntegrableOn bound (Ioc a t))
    (hlim : ∀ x ∈ Ioc a t, Tendsto (fun ω => Mf ω x) l (𝓝 (M₀ x))) :
    Tendsto (fun ω => ∫ x in a..t, ‖Mf ω x - M₀ x‖) l (𝓝 0) := by
  simp_rw [intervalIntegral.integral_of_le hat]
  exact tendsto_integral_norm_sub_of_dominated measurableSet_Ioc hmeas hM₀ hbd hbd₀ hint hlim

end Dominated

end ModeStability.ODE
