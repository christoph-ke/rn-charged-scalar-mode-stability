module

public import Mathlib

/-!
# Stability of linear systems: the analytic core

This file is the generic core of `ModeStability.ODE.LinearStability`.

* `ls_norm_le_of_norm_deriv_le`: **Grönwall's inequality with variable coefficients.** If
  `‖u'‖ ≤ m ‖u‖ + g` on `[s, t]` with continuous `m, g ≥ 0`, then
  `‖u t‖ ≤ (‖u s‖ + ∫ x in s..t, g x) * exp (∫ x in s..t, m x)`;
  `ls_norm_le_of_norm_deriv_le_backward` is the same estimate from `t` back to `s`.
  Mathlib's `norm_le_gronwallBound_of_norm_deriv_right_le` has constant `m` and `g` only; the
  proof follows it, through the fencing theorem
  `image_norm_le_of_norm_deriv_right_lt_deriv_boundary'`, with the barrier
  `(‖u s‖ + ε + ∫ g + ε (x − s)) exp (∫ m)`, and lets `ε → 0`.
* `ls_norm_apply_sub_le`: `‖A x − B y‖ ≤ ‖A‖ ‖x − y‖ + ‖(A − B) y‖` for continuous linear maps.
* endpoint helpers: limits of `∫ x in s..t, f x` as `s ↓ a`, boundedness of a function with a
  limit at a singular left endpoint or at `+∞`, integrability of `‖M − N‖`;
* `ls_continuousWithinAt_of_uniform`: joint continuity of `(ω, t) ↦ f ω t` at `(ω₀, t₀)` from an
  estimate `‖f ω t − f ω₀ t‖ ≤ δ ω` uniform in `t` near `t₀`, with `δ ω → 0`, and continuity of
  `f ω₀` at `t₀`.

Helpers carry the prefix `ls_`.
-/

public section

namespace ModeStability.ODE

open Set Filter Topology MeasureTheory

section Gronwall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The primitive `y ↦ ∫ τ in s..y, f τ` of a function continuous on `[s, t]` has right
derivative `f x` at every `x ∈ [s, t)`. -/
theorem ls_hasDerivWithinAt_primitive {f : ℝ → ℝ} {s t x : ℝ}
    (hf : ContinuousOn f (Icc s t)) (hx : x ∈ Ico s t) :
    HasDerivWithinAt (fun y => ∫ τ in s..y, f τ) (f x) (Ici x) x := by
  have hxI : x ∈ Icc s t := Ico_subset_Icc_self hx
  have : Fact (x ∈ Icc s t) := ⟨hxI⟩
  have hsub : uIcc s x ⊆ Icc s t := by
    rw [uIcc_of_le hx.1]
    exact Icc_subset_Icc_right hx.2.le
  have h := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc s t) (t := Icc s t)
    ((hf.mono hsub).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hf x hxI)
  exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)

/-- The primitive of a function continuous on `[s, t]` is continuous on `[s, t]`. -/
theorem ls_continuousOn_primitive {f : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hf : ContinuousOn f (Icc s t)) :
    ContinuousOn (fun y => ∫ τ in s..y, f τ) (Icc s t) := by
  have h := intervalIntegral.continuousOn_primitive_interval (a := s) (b := t) (μ := volume)
    (f := f) (by rw [uIcc_of_le hst]; exact hf.integrableOn_Icc)
  rwa [uIcc_of_le hst] at h

/-- **Grönwall's inequality with variable coefficients.** Let `u` be continuous on `[s, t]` with
right derivative `u'` on `[s, t)`, and `‖u'‖ ≤ m ‖u‖ + g` there, with `m, g ≥ 0` continuous on
`[s, t]`. Then `‖u t‖ ≤ (‖u s‖ + ∫ x in s..t, g x) * exp (∫ x in s..t, m x)`. -/
theorem ls_norm_le_of_norm_deriv_le {u u' : ℝ → E} {m g : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hu : ContinuousOn u (Icc s t)) (hu' : ∀ x ∈ Ico s t, HasDerivWithinAt u (u' x) (Ici x) x)
    (hm : ContinuousOn m (Icc s t)) (hg : ContinuousOn g (Icc s t))
    (hm0 : ∀ x ∈ Icc s t, 0 ≤ m x) (hg0 : ∀ x ∈ Icc s t, 0 ≤ g x)
    (hb : ∀ x ∈ Ico s t, ‖u' x‖ ≤ m x * ‖u x‖ + g x) :
    ‖u t‖ ≤ (‖u s‖ + ∫ x in s..t, g x) * Real.exp (∫ x in s..t, m x) := by
  set G : ℝ → ℝ := fun y => ∫ x in s..y, g x with hG_def
  set K : ℝ → ℝ := fun y => ∫ x in s..y, m x with hK_def
  have hGc := ls_continuousOn_primitive hst hg
  have hKc := ls_continuousOn_primitive hst hm
  have hK0 : ∀ y ∈ Icc s t, 0 ≤ K y := fun y hy =>
    intervalIntegral.integral_nonneg hy.1 fun x hx => hm0 x ⟨hx.1, hx.2.trans hy.2⟩
  have key : ∀ ε > 0, ‖u t‖ ≤ (‖u s‖ + ε + G t + ε * (t - s)) * Real.exp (K t) := by
    intro ε hε
    refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hu hu'
      (B := fun y => (‖u s‖ + ε + G y + ε * (y - s)) * Real.exp (K y))
      (B' := fun y => (g y + ε * 1) * Real.exp (K y) +
        (‖u s‖ + ε + G y + ε * (y - s)) * (Real.exp (K y) * m y)) ?_ ?_ ?_ ?_
      (right_mem_Icc.2 hst)
    · simp [G, K, hε.le]
    · exact ((((hGc.const_add _).add (continuousOn_const.mul
        (continuousOn_id.sub continuousOn_const)))).mul (hKc.rexp))
    · intro y hy
      exact (((ls_hasDerivWithinAt_primitive hg hy).const_add (‖u s‖ + ε)).add
        (((hasDerivWithinAt_id y (Ici y)).sub_const s).const_mul ε)).mul
        (ls_hasDerivWithinAt_primitive hm hy).exp
    · intro y hy hEq
      have hyI : y ∈ Icc s t := Ico_subset_Icc_self hy
      have he : 1 ≤ Real.exp (K y) := Real.one_le_exp (hK0 y hyI)
      have hgy := hg0 y hyI
      calc ‖u' y‖ ≤ m y * ‖u y‖ + g y := hb y hy
        _ < m y * ‖u y‖ + (g y + ε * 1) * 1 := by linarith
        _ ≤ m y * ‖u y‖ + (g y + ε * 1) * Real.exp (K y) := by gcongr
        _ = _ := by rw [hEq]; ring
  have hlim : Tendsto (fun ε : ℝ => (‖u s‖ + ε + G t + ε * (t - s)) * Real.exp (K t))
      (𝓝[>] 0) (𝓝 ((‖u s‖ + 0 + G t + 0 * (t - s)) * Real.exp (K t))) :=
    ((Continuous.tendsto (by fun_prop) 0)).mono_left nhdsWithin_le_nhds
  have := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)
  simpa using this

/-- **Grönwall's inequality backwards in time.** If `u` is differentiable on `[s, t]` with
`‖u'‖ ≤ m ‖u‖ + g` there, `m, g ≥ 0` continuous on `[s, t]`, then
`‖u s‖ ≤ (‖u t‖ + ∫ x in s..t, g x) * exp (∫ x in s..t, m x)`. -/
theorem ls_norm_le_of_norm_deriv_le_backward {u u' : ℝ → E} {m g : ℝ → ℝ} {s t : ℝ}
    (hst : s ≤ t) (hu : ∀ x ∈ Icc s t, HasDerivAt u (u' x) x)
    (hm : ContinuousOn m (Icc s t)) (hg : ContinuousOn g (Icc s t))
    (hm0 : ∀ x ∈ Icc s t, 0 ≤ m x) (hg0 : ∀ x ∈ Icc s t, 0 ≤ g x)
    (hb : ∀ x ∈ Icc s t, ‖u' x‖ ≤ m x * ‖u x‖ + g x) :
    ‖u s‖ ≤ (‖u t‖ + ∫ x in s..t, g x) * Real.exp (∫ x in s..t, m x) := by
  have hneg : ∀ x ∈ Icc (-t) (-s), -x ∈ Icc s t := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hmaps : MapsTo (fun x : ℝ => -x) (Icc (-t) (-s)) (Icc s t) := hneg
  have hd : ∀ x ∈ Icc (-t) (-s), HasDerivAt (fun y => u (-y)) (-u' (-x)) x := fun x hx => by
    have h := (hu (-x) (hneg x hx)).scomp x (hasDerivAt_neg x)
    rwa [neg_one_smul] at h
  have h := ls_norm_le_of_norm_deriv_le (u := fun y => u (-y)) (u' := fun y => -u' (-y))
    (m := fun y => m (-y)) (g := fun y => g (-y)) (s := -t) (t := -s) (by linarith)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (hm.comp continuousOn_neg hmaps) (hg.comp continuousOn_neg hmaps)
    (fun x hx => hm0 _ (hneg x hx)) (fun x hx => hg0 _ (hneg x hx))
    (fun x hx => by
      rw [norm_neg]
      exact hb _ (hneg x (Ico_subset_Icc_self hx)))
  simpa only [neg_neg, intervalIntegral.integral_comp_neg] using h

end Gronwall

section Helpers

/-- `‖A x − B y‖ ≤ ‖A‖ ‖x − y‖ + ‖(A − B) y‖` for continuous linear maps `A`, `B`. -/
theorem ls_norm_apply_sub_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A B : E →L[𝕜] E) (x y : E) :
    ‖A x - B y‖ ≤ ‖A‖ * ‖x - y‖ + ‖(A - B) y‖ := by
  have h : A x - B y = A (x - y) + (A - B) y := by
    rw [map_sub, sub_apply]
    abel
  rw [h]
  exact (norm_add_le _ _).trans (by gcongr; exact A.le_opNorm _)

/-- The majorant `‖A‖ W` for `‖A y‖` when `‖y‖ ≤ W`. -/
theorem ls_norm_apply_le_of_le {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {A : E →L[𝕜] E} {y : E} {W : ℝ} (hW : ‖y‖ ≤ W) :
    ‖A y‖ ≤ ‖A‖ * W :=
  (A.le_opNorm y).trans (mul_le_mul_of_nonneg_left hW (norm_nonneg _))

/-- `∫ x in s..t, f x → ∫ x in a..t, f x` as `s ↓ a`, for `f` integrable on `(a, t]`. -/
theorem ls_tendsto_integral_nhdsGT {f : ℝ → ℝ} {a t : ℝ} (hat : a < t)
    (hf : IntegrableOn f (Ioc a t)) :
    Tendsto (fun s => ∫ x in s..t, f x) (𝓝[>] a) (𝓝 (∫ x in a..t, f x)) := by
  have hc := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) (f := f)
    (a := a) (b := t) (by
      rw [uIcc_of_le hat.le]
      exact (integrableOn_Icc_iff_integrableOn_Ioc enorm_ne_top).2 hf)
  have hw : ContinuousWithinAt (fun s => ∫ x in s..t, f x) (Icc a t) a := by
    have := hc a left_mem_uIcc
    rwa [uIcc_of_le hat.le] at this
  exact (hw.mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hat)).tendsto

variable {E : Type*} [NormedAddCommGroup E]

/-- A function continuous on `(a, T]` with a limit as `t ↓ a` is bounded on `(a, T]`. -/
theorem ls_exists_bound_nhdsGT {v : ℝ → E} {a T : ℝ} {v₀ : E} (hv : ContinuousOn v (Ioc a T))
    (hv0 : Tendsto v (𝓝[>] a) (𝓝 v₀)) : ∃ B, ∀ t ∈ Ioc a T, ‖v t‖ ≤ B := by
  have hev : ∀ᶠ t in 𝓝[>] a, ‖v t‖ < ‖v₀‖ + 1 :=
    hv0.norm.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hau : a < u := hu
  have hac : a < (a + u) / 2 := by linarith
  have hcu : (a + u) / 2 < u := by linarith
  obtain ⟨B', hB'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hv.mono (t := Icc ((a + u) / 2) T) fun x hx => ⟨hac.trans_le hx.1, hx.2⟩)
  refine ⟨max (‖v₀‖ + 1) B', fun t ht => ?_⟩
  rcases lt_or_ge t ((a + u) / 2) with h | h
  · have h1 : ‖v t‖ < ‖v₀‖ + 1 := hsub ⟨ht.1, h.trans hcu⟩
    exact h1.le.trans (le_max_left _ _)
  · exact (hB' t ⟨h, ht.2⟩).trans (le_max_right _ _)

/-- A function continuous on `[T, ∞)` with a limit at `+∞` is bounded on `[T, ∞)`. -/
theorem ls_exists_bound_atTop {v : ℝ → E} {T : ℝ} {vI : E} (hv : ContinuousOn v (Ici T))
    (hvI : Tendsto v atTop (𝓝 vI)) : ∃ B, ∀ t ∈ Ici T, ‖v t‖ ≤ B := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 (hvI.norm.eventually (gt_mem_nhds (lt_add_one ‖vI‖)))
  obtain ⟨B', hB'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hv.mono (t := Icc T R) Icc_subset_Ici_self)
  refine ⟨max (‖vI‖ + 1) B', fun t ht => ?_⟩
  rcases le_total t R with h | h
  · exact (hB' t ⟨ht, h⟩).trans (le_max_right _ _)
  · exact (hR t h).le.trans (le_max_left _ _)

/-- A bounded function continuous on a measurable set of finite measure has integrable norm. -/
theorem ls_integrableOn_norm_of_le {M : ℝ → E} {A : Set ℝ} {C : ℝ} (hA : MeasurableSet A)
    (hAf : volume A ≠ ⊤) (hM : ContinuousOn M A) (hC : ∀ x ∈ A, ‖M x‖ ≤ C) :
    IntegrableOn (fun x => ‖M x‖) A :=
  Integrable.mono' (integrableOn_const (C := C) hAf) (hM.norm.aestronglyMeasurable hA)
    ((ae_restrict_iff' hA).2 (Eventually.of_forall fun x hx => by
      rw [norm_norm]
      exact hC x hx))

/-- `‖M − N‖` is integrable on `A` if `‖M‖` and `‖N‖` are and `M`, `N` are continuous on `A`. -/
theorem ls_integrableOn_norm_sub {M N : ℝ → E} {A : Set ℝ} (hA : MeasurableSet A)
    (hM : ContinuousOn M A) (hN : ContinuousOn N A) (hMi : IntegrableOn (fun x => ‖M x‖) A)
    (hNi : IntegrableOn (fun x => ‖N x‖) A) : IntegrableOn (fun x => ‖M x - N x‖) A :=
  Integrable.mono' (hMi.add hNi) ((hM.sub hN).norm.aestronglyMeasurable hA)
    (Eventually.of_forall fun x => by
      rw [norm_norm]
      exact norm_sub_le _ _)

end Helpers

section Joint

variable {Λ : Type*} [TopologicalSpace Λ] {E : Type*} [NormedAddCommGroup E]

/-- **Joint continuity from a uniform estimate.** If `‖f ω t − f ω₀ t‖ ≤ δ ω` for `ω ∈ S` and
`t ∈ D` near `t₀`, with `δ ω → 0` as `ω → ω₀` in `S`, and `f ω₀` is continuous at `t₀`, then
`(ω, t) ↦ f ω t` is continuous at `(ω₀, t₀)` within `S ×ˢ D`. -/
theorem ls_continuousWithinAt_of_uniform {S : Set Λ} {D U : Set ℝ} {f : Λ → ℝ → E}
    {δ : Λ → ℝ} {ω₀ : Λ} {t₀ : ℝ} (hU : U ∈ 𝓝 t₀)
    (hδ : ∀ ω ∈ S, ∀ t ∈ D, t ∈ U → ‖f ω t - f ω₀ t‖ ≤ δ ω)
    (hδlim : Tendsto δ (𝓝[S] ω₀) (𝓝 0)) (hc : ContinuousAt (f ω₀) t₀) :
    ContinuousWithinAt (fun p : Λ × ℝ => f p.1 p.2) (S ×ˢ D) (ω₀, t₀) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  change Tendsto (fun p : Λ × ℝ => ‖f p.1 p.2 - f ω₀ t₀‖) (𝓝[S ×ˢ D] (ω₀, t₀)) (𝓝 0)
  have hfst : Tendsto Prod.fst (𝓝[S ×ˢ D] (ω₀, t₀)) (𝓝[S] ω₀) := by
    rw [nhdsWithin_prod_eq]
    exact tendsto_fst
  have hsnd : Tendsto Prod.snd (𝓝[S ×ˢ D] (ω₀, t₀)) (𝓝 t₀) := by
    rw [nhdsWithin_prod_eq]
    exact tendsto_snd.mono_right nhdsWithin_le_nhds
  have h3 : Tendsto (fun p : Λ × ℝ => ‖f ω₀ p.2 - f ω₀ t₀‖) (𝓝[S ×ˢ D] (ω₀, t₀)) (𝓝 0) := by
    simpa using ((hc.tendsto.comp hsnd).sub_const (f ω₀ t₀)).norm
  have h4 : Tendsto (fun p : Λ × ℝ => δ p.1 + ‖f ω₀ p.2 - f ω₀ t₀‖) (𝓝[S ×ˢ D] (ω₀, t₀))
      (𝓝 0) := by
    simpa using (hδlim.comp hfst).add h3
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h4
  filter_upwards [self_mem_nhdsWithin, hsnd.eventually hU] with p hp hpU
  calc ‖f p.1 p.2 - f ω₀ t₀‖ ≤ ‖f p.1 p.2 - f ω₀ p.2‖ + ‖f ω₀ p.2 - f ω₀ t₀‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ p.1 + ‖f ω₀ p.2 - f ω₀ t₀‖ := by
        gcongr
        exact hδ p.1 hp.1 p.2 hp.2 hpU

end Joint

end ModeStability.ODE
