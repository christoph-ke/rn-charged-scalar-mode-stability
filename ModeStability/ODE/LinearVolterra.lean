module

public import Mathlib
public import ModeStability.ODE.LinearVolterraAux

/-!
# Linear systems on `ℂ × ℂ` with a singular or an infinite endpoint

Existence (and uniqueness) for first-order linear systems `v' = M(t) v` on `(a, ∞)` for two
complex amplitudes, `v : ℝ → ℂ × ℂ` (sup norm) and `M : ℝ → ℂ × ℂ →L[ℂ] ℂ × ℂ` continuous on
`Ioi a`, in the two situations needed for the normalized solutions `R_H`, `R_I` of Prop. 6.1 of
the all-angular paper:

* `linear_exists_nhdsGT`: `M` is bounded (but possibly discontinuous, e.g. oscillating) as
  `t ↓ a`; the solution tends to prescribed data `v₀` at `a`, with `‖v t − v₀‖ ≤ C' (t − a)`;
* `linear_exists_atTop`: `‖M‖` is integrable at `+∞`; the solution tends to prescribed data
  `vI` at `+∞`, with the tail bound `‖v t − vI‖ ≤ (exp (∫ s in Ioi t, ‖M s‖) − 1) ‖vI‖`;
* uniqueness: `linear_eqOn_nhdsGT`, `linear_eqOn_atTop` (same limit at the endpoint), and
  `linear_eqOn_Ioi` (same value at an interior point).

Mathlib's Picard–Lindelöf theorem needs time-continuity on a closed interval and is local, so it
does not apply at these endpoints. Both results come from the Carathéodory/Volterra theory of
`ModeStability.ODE.LinearVolterraAux` (successive approximations with an integrable coefficient,
`linear_exists_of_integrableOn`); the infinite endpoint is reduced to a finite one by the
substitution `s = 1/(t − a)`, and the solution is extended to all of `(a, ∞)` by the global
existence and uniqueness theorems for continuous coefficients (`linear_exists_Ioi`,
`linear_eqOn_Ioi`).

The coefficient is built from four scalar entries by `mat2`, with `‖mat2 …‖ ≤` the sum of the
absolute values of the entries (`norm_mat2_le`) and continuity in the entries
(`continuousOn_mat2`).

Interface note (relative to `volterra-interface.md`): the coefficient is `ℂ`-linear,
`Mx : ℝ → ℂ × ℂ →L[ℂ] ℂ × ℂ`. The bound hypothesis of `linear_exists_nhdsGT` is taken with an
explicit constant `C` (`∀ t ∈ Ioc a (a + 1), ‖Mx t‖ ≤ C`, the `C` of `∃ C, …`), and the
explicit constant is `C' = C * exp C * ‖v₀‖`. The conclusions of `linear_exists_nhdsGT` and
`linear_exists_atTop` have exactly the three conjuncts of the interface; the primed variant
`linear_exists_nhdsGT'` also exports the integral equation and the Grönwall bound. `v∞` is
spelled `vI`. Interior existence is `linear_exists_Ioi` (data at `t₀ > a`); the generic versions
over any complete normed space are in `ModeStability.ODE.LinearVolterraAux`.
-/

public section

namespace ModeStability.ODE

open Set Filter MeasureTheory Topology intervalIntegral
open scoped Interval

section Mat2

/-- The `2 × 2` complex matrix `[[m₁₁, m₁₂], [m₂₁, m₂₂]]` acting on `ℂ × ℂ`:
`(x, y) ↦ (m₁₁ x + m₁₂ y, m₂₁ x + m₂₂ y)`. -/
noncomputable def mat2 (m₁₁ m₁₂ m₂₁ m₂₂ : ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  m₁₁ • (ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ ℂ ℂ) +
    m₁₂ • (ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ ℂ) +
    m₂₁ • (ContinuousLinearMap.inr ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ ℂ ℂ) +
    m₂₂ • (ContinuousLinearMap.inr ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ ℂ)

@[simp]
theorem mat2_apply (m₁₁ m₁₂ m₂₁ m₂₂ : ℂ) (z : ℂ × ℂ) :
    mat2 m₁₁ m₁₂ m₂₁ m₂₂ z = (m₁₁ * z.1 + m₁₂ * z.2, m₂₁ * z.1 + m₂₂ * z.2) := by
  ext <;> simp [mat2]

theorem mat2_apply_fst (m₁₁ m₁₂ m₂₁ m₂₂ : ℂ) (z : ℂ × ℂ) :
    (mat2 m₁₁ m₁₂ m₂₁ m₂₂ z).1 = m₁₁ * z.1 + m₁₂ * z.2 := by
  rw [mat2_apply]

theorem mat2_apply_snd (m₁₁ m₁₂ m₂₁ m₂₂ : ℂ) (z : ℂ × ℂ) :
    (mat2 m₁₁ m₁₂ m₂₁ m₂₂ z).2 = m₂₁ * z.1 + m₂₂ * z.2 := by
  rw [mat2_apply]

theorem norm_mat2_le (m₁₁ m₁₂ m₂₁ m₂₂ : ℂ) :
    ‖mat2 m₁₁ m₁₂ m₂₁ m₂₂‖ ≤ ‖m₁₁‖ + ‖m₁₂‖ + ‖m₂₁‖ + ‖m₂₂‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have h1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have h2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  have hrow : ∀ p q : ℂ, ‖p * z.1 + q * z.2‖ ≤ ‖p‖ * ‖z‖ + ‖q‖ * ‖z‖ := fun p q => by
    calc ‖p * z.1 + q * z.2‖ ≤ ‖p * z.1‖ + ‖q * z.2‖ := norm_add_le _ _
      _ = ‖p‖ * ‖z.1‖ + ‖q‖ * ‖z.2‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖p‖ * ‖z‖ + ‖q‖ * ‖z‖ := by gcongr
  have n₁₁ := mul_nonneg (norm_nonneg m₁₁) (norm_nonneg z)
  have n₁₂ := mul_nonneg (norm_nonneg m₁₂) (norm_nonneg z)
  have n₂₁ := mul_nonneg (norm_nonneg m₂₁) (norm_nonneg z)
  have n₂₂ := mul_nonneg (norm_nonneg m₂₂) (norm_nonneg z)
  rw [mat2_apply, Prod.norm_def, add_mul, add_mul, add_mul]
  refine max_le ?_ ?_
  · linarith [hrow m₁₁ m₁₂]
  · linarith [hrow m₂₁ m₂₂]

theorem continuousOn_mat2 {S : Set ℝ} {f₁₁ f₁₂ f₂₁ f₂₂ : ℝ → ℂ} (h₁₁ : ContinuousOn f₁₁ S)
    (h₁₂ : ContinuousOn f₁₂ S) (h₂₁ : ContinuousOn f₂₁ S) (h₂₂ : ContinuousOn f₂₂ S) :
    ContinuousOn (fun t => mat2 (f₁₁ t) (f₁₂ t) (f₂₁ t) (f₂₂ t)) S := by
  simp only [mat2]
  exact (((h₁₁.smul continuousOn_const).add (h₁₂.smul continuousOn_const)).add
    (h₂₁.smul continuousOn_const)).add (h₂₂.smul continuousOn_const)

theorem continuous_mat2 {f₁₁ f₁₂ f₂₁ f₂₂ : ℝ → ℂ} (h₁₁ : Continuous f₁₁) (h₁₂ : Continuous f₁₂)
    (h₂₁ : Continuous f₂₁) (h₂₂ : Continuous f₂₂) :
    Continuous (fun t => mat2 (f₁₁ t) (f₁₂ t) (f₂₁ t) (f₂₂ t)) :=
  continuousOn_univ.1 (continuousOn_mat2 h₁₁.continuousOn h₁₂.continuousOn h₂₁.continuousOn
    h₂₂.continuousOn)

end Mat2

variable {a : ℝ} {Mx : ℝ → ℂ × ℂ →L[ℂ] ℂ × ℂ}

section Interior

/-- **Global existence** on `(a, ∞)` for a continuous coefficient, from data at `t₀ > a`. -/
theorem linear_exists_Ioi (hM : ContinuousOn Mx (Ioi a)) {t₀ : ℝ} (ht₀ : a < t₀)
    (v₁ : ℂ × ℂ) : ∃ v : ℝ → ℂ × ℂ, v t₀ = v₁ ∧ ∀ t ∈ Ioi a, HasDerivAt v (Mx t (v t)) t :=
  linear_exists_of_ordConnected isOpen_Ioi ordConnected_Ioi hM ht₀ v₁

/-- **Uniqueness** on `(a, ∞)` for a continuous coefficient: two solutions agreeing at one
point `t₀ > a` agree on `(a, ∞)`. -/
theorem linear_eqOn_Ioi (hM : ContinuousOn Mx (Ioi a)) {u w : ℝ → ℂ × ℂ}
    (hu : ∀ t ∈ Ioi a, HasDerivAt u (Mx t (u t)) t) (hw : ∀ t ∈ Ioi a, HasDerivAt w (Mx t (w t)) t)
    {t₀ : ℝ} (ht₀ : a < t₀) (h : u t₀ = w t₀) : EqOn u w (Ioi a) :=
  linear_eqOn_of_hasDerivAt ordConnected_Ioi hM hu hw ht₀ h

end Interior

section Horizon

theorem lv_exp_sub_one_le (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  calc Real.exp x - 1 = Real.exp x * (1 - Real.exp (-x)) := by
        rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    _ ≤ Real.exp x * x :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (-x)]) (Real.exp_pos x).le
    _ = x * Real.exp x := mul_comm _ _

theorem lv_integrableOn_Ioc_of_bdd {C : ℝ} (hM : ContinuousOn Mx (Ioi a))
    (hC : ∀ t ∈ Ioc a (a + 1), ‖Mx t‖ ≤ C) (t : ℝ) :
    IntegrableOn (fun s => ‖Mx s‖) (Ioc a t) := by
  have h₁ : IntegrableOn (fun s => ‖Mx s‖) (Ioc a (a + 1)) :=
    Integrable.mono' (integrableOn_const (C := C) measure_Ioc_lt_top.ne)
      ((hM.mono Ioc_subset_Ioi_self).norm.aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => by
        rw [norm_norm]
        exact hC s hs))
  have h₂ : IntegrableOn (fun s => ‖Mx s‖) (Icc (a + 1) (max t (a + 1))) :=
    (hM.mono fun s hs => (show a < s by linarith [hs.1])).norm.integrableOn_compact
      isCompact_Icc
  refine (h₁.union h₂).mono_set fun s hs => ?_
  rcases le_or_gt s (a + 1) with h | h
  · exact Or.inl ⟨hs.1, h⟩
  · exact Or.inr ⟨h.le, hs.2.trans (le_max_left _ _)⟩

/-- `linear_exists_nhdsGT` together with the integral equation and the Grönwall bound. -/
theorem linear_exists_nhdsGT' {C : ℝ} (hM : ContinuousOn Mx (Ioi a))
    (hC : ∀ t ∈ Ioc a (a + 1), ‖Mx t‖ ≤ C) (v₀ : ℂ × ℂ) :
    ∃ v : ℝ → ℂ × ℂ, (∀ t ∈ Ioi a, HasDerivAt v (Mx t (v t)) t) ∧ Tendsto v (𝓝[>] a) (𝓝 v₀) ∧
      (∀ t ∈ Ioc a (a + 1), ‖v t - v₀‖ ≤ C * Real.exp C * ‖v₀‖ * (t - a)) ∧
      (∀ t ∈ Ioi a, v t = v₀ + ∫ s in a..t, Mx s (v s)) ∧
      ∀ t ∈ Ioi a, ‖v t - v₀‖ ≤ (Real.exp (∫ s in Ioc a t, ‖Mx s‖) - 1) * ‖v₀‖ := by
  have hint : ∀ t ∈ Ioi a, IntegrableOn (fun s => ‖Mx s‖) (Ι a t) := fun t ht => by
    rw [uIoc_of_le (le_of_lt ht)]
    exact lv_integrableOn_Ioc_of_bdd hM hC t
  obtain ⟨v, hva, hvd, hveq, hvc, hvb⟩ := linear_exists_of_integrableOn isOpen_Ioi
    (fun t ht => by rw [uIoc_of_le (le_of_lt ht)]; exact Ioc_subset_Ioi_self) hM hint v₀
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (a + 1) ⟨by linarith, le_rfl⟩)
  have hvb' : ∀ t ∈ Ioi a, ‖v t - v₀‖ ≤ (Real.exp (∫ s in Ioc a t, ‖Mx s‖) - 1) * ‖v₀‖ :=
    fun t ht => by
      have h := hvb t ht
      rwa [uIoc_of_le (le_of_lt ht)] at h
  refine ⟨v, hvd, ?_, fun t ht => ?_, hveq, hvb'⟩
  · have hc := hvc (a + 1) (show a < a + 1 by linarith)
    rw [uIcc_of_le (by linarith)] at hc
    have hcw := (hc a ⟨le_rfl, by linarith⟩).tendsto
    rw [hva] at hcw
    exact hcw.mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT (by linarith)))
  · set m := ∫ s in Ioc a t, ‖Mx s‖
    have hm : m ≤ C * (t - a) := by
      calc m ≤ ∫ _ in Ioc a t, C := setIntegral_mono_on (lv_integrableOn_Ioc_of_bdd hM hC t)
            (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc
            fun s hs => hC s ⟨hs.1, hs.2.trans ht.2⟩
        _ = C * (t - a) := by
            rw [setIntegral_const, Real.volume_real_Ioc_of_le ht.1.le, smul_eq_mul, mul_comm]
    have hm0 : 0 ≤ m := setIntegral_nonneg measurableSet_Ioc fun _ _ => norm_nonneg _
    have hmC : m ≤ C := hm.trans (by nlinarith [ht.1, ht.2])
    calc ‖v t - v₀‖ ≤ (Real.exp m - 1) * ‖v₀‖ := hvb' t ht.1
      _ ≤ (m * Real.exp m) * ‖v₀‖ :=
          mul_le_mul_of_nonneg_right (lv_exp_sub_one_le m) (norm_nonneg _)
      _ ≤ (C * (t - a) * Real.exp C) * ‖v₀‖ := by
          gcongr
          · nlinarith [ht.1]
      _ = C * Real.exp C * ‖v₀‖ * (t - a) := by ring

/-- **Existence at a singular left endpoint with a bounded coefficient.** If `M` is continuous on
`(a, ∞)` and bounded by `C` on `(a, a + 1]` (it may oscillate as `t ↓ a`), then for every `v₀`
there is a solution of `v' = M v` on `(a, ∞)` with `v → v₀` as `t ↓ a`, and
`‖v t − v₀‖ ≤ C e^C ‖v₀‖ (t − a)` on `(a, a + 1]`. -/
theorem linear_exists_nhdsGT {C : ℝ} (hM : ContinuousOn Mx (Ioi a))
    (hC : ∀ t ∈ Ioc a (a + 1), ‖Mx t‖ ≤ C) (v₀ : ℂ × ℂ) :
    ∃ v : ℝ → ℂ × ℂ, (∀ t ∈ Ioi a, HasDerivAt v (Mx t (v t)) t) ∧ Tendsto v (𝓝[>] a) (𝓝 v₀) ∧
      ∀ t ∈ Ioc a (a + 1), ‖v t - v₀‖ ≤ C * Real.exp C * ‖v₀‖ * (t - a) := by
  obtain ⟨v, h₁, h₂, h₃, -⟩ := linear_exists_nhdsGT' hM hC v₀
  exact ⟨v, h₁, h₂, h₃⟩

/-- **Uniqueness at the singular left endpoint** (bounded coefficient): two solutions of
`v' = M v` on `(a, ∞)` with the same limit as `t ↓ a` agree. -/
theorem linear_eqOn_nhdsGT {C : ℝ} (hM : ContinuousOn Mx (Ioi a))
    (hC : ∀ t ∈ Ioc a (a + 1), ‖Mx t‖ ≤ C) {u w : ℝ → ℂ × ℂ}
    (hu : ∀ t ∈ Ioi a, HasDerivAt u (Mx t (u t)) t) (hw : ∀ t ∈ Ioi a, HasDerivAt w (Mx t (w t)) t)
    {L : ℂ × ℂ} (hu0 : Tendsto u (𝓝[>] a) (𝓝 L)) (hw0 : Tendsto w (𝓝[>] a) (𝓝 L)) :
    EqOn u w (Ioi a) :=
  linear_eqOn_of_tendsto_nhdsGT subset_rfl (fun _ _ => Ioc_subset_Ioi_self) hM
    (fun t _ => lv_integrableOn_Ioc_of_bdd hM hC t) hu hw hu0 hw0

end Horizon

section Infinity

/-- The image of `(0, s]` under `x ↦ a + x⁻¹` is `[a + s⁻¹, ∞)`. -/
theorem lv_image_inv_Ioc {s : ℝ} (hs : 0 < s) :
    (fun x : ℝ => a + x⁻¹) '' Ioc 0 s = Ici (a + s⁻¹) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Ici]
    linarith [inv_anti₀ hx.1 hx.2]
  · intro hy
    have hy' : s⁻¹ ≤ y - a := by
      rw [mem_Ici] at hy
      linarith
    have hpos : 0 < y - a := lt_of_lt_of_le (inv_pos.2 hs) hy'
    refine ⟨(y - a)⁻¹, ⟨inv_pos.2 hpos, (inv_le_comm₀ hpos hs).2 hy'⟩, ?_⟩
    simp only [inv_inv]
    ring

/-- The substitution `s = (t − a)⁻¹` maps `t ∈ (r₁, ∞)` to `s ∈ (0, (r₁ − a)⁻¹)` and the system
`v' = M v` to `w' = N w` with `N s = −s⁻² M (a + s⁻¹)`, whose mass on `(0, s]` is the tail
`∫ t in Ioi (a + s⁻¹), ‖M t‖`. -/
theorem lv_inversion (hM : ContinuousOn Mx (Ioi a)) {r₁ : ℝ} (ha1 : a < r₁)
    (hint₁ : IntegrableOn (fun t => ‖Mx t‖) (Ioi r₁)) :
    ∃ N : ℝ → ℂ × ℂ →L[ℂ] ℂ × ℂ, (∀ s, N s = (-(s ^ 2)⁻¹ : ℝ) • Mx (a + s⁻¹)) ∧
      ContinuousOn N (Ioo 0 (r₁ - a)⁻¹) ∧
      (∀ s ∈ Ioo 0 (r₁ - a)⁻¹, IntegrableOn (fun x => ‖N x‖) (Ioc 0 s)) ∧
      ∀ s ∈ Ioo 0 (r₁ - a)⁻¹, ∫ x in Ioc 0 s, ‖N x‖ = ∫ t in Ioi (a + s⁻¹), ‖Mx t‖ := by
  have hφ : ∀ s ∈ Ioo 0 (r₁ - a)⁻¹, r₁ < a + s⁻¹ := fun s hs => by
    have : r₁ - a < s⁻¹ := (lt_inv_comm₀ (by linarith) hs.1).2 hs.2
    linarith
  obtain ⟨N, hN⟩ : ∃ N : ℝ → ℂ × ℂ →L[ℂ] ℂ × ℂ,
      ∀ s, N s = (-(s ^ 2)⁻¹ : ℝ) • Mx (a + s⁻¹) := ⟨_, fun _ => rfl⟩
  have hNnorm : ∀ s, ‖N s‖ = |-(s ^ 2)⁻¹| • ‖Mx (a + s⁻¹)‖ := fun s => by
    rw [hN, norm_smul, Real.norm_eq_abs, smul_eq_mul]
  have hderiv : ∀ s, ∀ x ∈ Ioc 0 s,
      HasDerivWithinAt (fun x : ℝ => a + x⁻¹) (-(x ^ 2)⁻¹) (Ioc 0 s) x := fun s x hx =>
    ((hasDerivAt_inv (ne_of_gt hx.1)).const_add a).hasDerivWithinAt
  have hinj : ∀ s, InjOn (fun x : ℝ => a + x⁻¹) (Ioc 0 s) := fun s x _ y _ h =>
    inv_injective (add_left_cancel h)
  refine ⟨N, hN, ?_, fun s hs => ?_, fun s hs => ?_⟩
  · have hinv : ContinuousOn (fun s : ℝ => s⁻¹) (Ioo 0 (r₁ - a)⁻¹) :=
      continuousOn_inv₀.mono fun s hs => ne_of_gt hs.1
    have h := ContinuousOn.smul ((continuousOn_pow (s := Ioo (0 : ℝ) (r₁ - a)⁻¹) 2).inv₀
      (fun s hs => pow_ne_zero 2 (ne_of_gt hs.1))).neg
      (hM.comp (continuousOn_const.add hinv) fun s hs => show a < a + s⁻¹ by linarith [hφ s hs])
    exact h.congr fun s _ => hN s
  · have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc
      (hderiv s) (hinj s) (fun t => ‖Mx t‖)).1
      (by rw [lv_image_inv_Ioc hs.1]; exact hint₁.mono_set (Ici_subset_Ioi.2 (hφ s hs)))
    exact h.congr_fun (fun x _ => (hNnorm x).symm) measurableSet_Ioc
  · rw [← integral_Ici_eq_integral_Ioi, ← lv_image_inv_Ioc hs.1,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc (hderiv s) (hinj s)]
    exact setIntegral_congr_fun measurableSet_Ioc fun x _ => hNnorm x

theorem lv_hasDerivAt_comp_inv {N : ℝ → ℂ × ℂ →L[ℂ] ℂ × ℂ}
    (hN : ∀ s, N s = (-(s ^ 2)⁻¹ : ℝ) • Mx (a + s⁻¹)) {w : ℝ → ℂ × ℂ} {t : ℝ} (hta : t - a ≠ 0)
    (hw : HasDerivAt w (N (t - a)⁻¹ (w (t - a)⁻¹)) (t - a)⁻¹) :
    HasDerivAt (fun t => w (t - a)⁻¹) (Mx t (w (t - a)⁻¹)) t := by
  have hd : HasDerivAt (fun t => (t - a)⁻¹) (-((t - a) ^ 2)⁻¹) t := by
    have h0 := (hasDerivAt_inv hta).comp t ((hasDerivAt_id' t).sub_const a)
    rw [mul_one] at h0
    exact h0
  have h : HasDerivAt (fun t => w (t - a)⁻¹)
      (-((t - a) ^ 2)⁻¹ • N (t - a)⁻¹ (w (t - a)⁻¹)) t := hw.scomp t hd
  convert h using 1
  rw [hN, smul_apply, smul_smul, inv_inv, add_sub_cancel]
  have hc : -((t - a) ^ 2)⁻¹ * -(((t - a)⁻¹) ^ 2)⁻¹ = 1 := by
    field_simp
  rw [hc, one_smul]

theorem lv_hasDerivAt_comp_add_inv {N : ℝ → ℂ × ℂ →L[ℂ] ℂ × ℂ}
    (hN : ∀ s, N s = (-(s ^ 2)⁻¹ : ℝ) • Mx (a + s⁻¹)) {v : ℝ → ℂ × ℂ} {s : ℝ} (hs : s ≠ 0)
    (hv : HasDerivAt v (Mx (a + s⁻¹) (v (a + s⁻¹))) (a + s⁻¹)) :
    HasDerivAt (fun s => v (a + s⁻¹)) (N s (v (a + s⁻¹))) s := by
  have h : HasDerivAt (fun s => v (a + s⁻¹)) ((-(s ^ 2)⁻¹) • Mx (a + s⁻¹) (v (a + s⁻¹))) s :=
    hv.scomp s ((hasDerivAt_inv hs).const_add a)
  rwa [hN, smul_apply]

/-- **Existence at `+∞` with an integrable coefficient.** If `M` is continuous on `(a, ∞)` and
`‖M‖` is integrable on `(r₀, ∞)` for some `r₀ > a`, then for every `vI` there is a solution of
`v' = M v` on `(a, ∞)` with `v → vI` as `t → ∞`, and
`‖v t − vI‖ ≤ (exp (∫ s in Ioi t, ‖M s‖) − 1) ‖vI‖` for `t ≥ r₀`. -/
theorem linear_exists_atTop {r₀ : ℝ} (hM : ContinuousOn Mx (Ioi a)) (hr₀ : a < r₀)
    (hint : IntegrableOn (fun t => ‖Mx t‖) (Ioi r₀)) (vI : ℂ × ℂ) :
    ∃ v : ℝ → ℂ × ℂ, (∀ t ∈ Ioi a, HasDerivAt v (Mx t (v t)) t) ∧ Tendsto v atTop (𝓝 vI) ∧
      ∀ t ≥ r₀, ‖v t - vI‖ ≤ (Real.exp (∫ s in Ioi t, ‖Mx s‖) - 1) * ‖vI‖ := by
  set r₁ := (a + r₀) / 2 with hr₁
  have ha1 : a < r₁ := by linarith
  have h1r : r₁ < r₀ := by linarith
  have hint₁ : IntegrableOn (fun t => ‖Mx t‖) (Ioi r₁) := by
    rw [← Ioc_union_Ioi_eq_Ioi h1r.le]
    exact (((hM.mono fun s hs => lt_of_lt_of_le ha1 hs.1).norm.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self).union hint
  set S := (r₁ - a)⁻¹
  have hS0 : 0 < S := inv_pos.2 (by linarith)
  obtain ⟨N, hN, hNc, hNi, hmassN⟩ := lv_inversion hM ha1 hint₁
  have hJc : ∀ s ∈ Ioo 0 S, Ι 0 s ⊆ Ioo 0 S := fun s hs => by
    rw [uIoc_of_le hs.1.le]
    exact fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hs.2⟩
  obtain ⟨w, hw0, hwd, -, hwc, hwb⟩ := linear_exists_of_integrableOn isOpen_Ioo hJc hNc
    (fun s hs => by rw [uIoc_of_le hs.1.le]; exact hNi s hs) vI
  -- back to the variable `t = a + 1/s`
  have hσ : ∀ t ∈ Ioi r₁, (t - a)⁻¹ ∈ Ioo 0 S := fun t ht =>
    ⟨inv_pos.2 (by linarith [mem_Ioi.1 ht]),
      inv_strictAnti₀ (by linarith) (by linarith [mem_Ioi.1 ht])⟩
  have hv₁d : ∀ t ∈ Ioi r₁, HasDerivAt (fun t => w (t - a)⁻¹) (Mx t (w (t - a)⁻¹)) t :=
    fun t ht => lv_hasDerivAt_comp_inv hN (ne_of_gt (by linarith [mem_Ioi.1 ht]))
      (hwd _ (hσ t ht))
  have hwlim : Tendsto w (𝓝[>] 0) (𝓝 vI) := by
    have hc := hwc (S / 2) ⟨by linarith, by linarith⟩
    rw [uIcc_of_le (by linarith)] at hc
    have h := (hc 0 ⟨le_rfl, by linarith⟩).tendsto
    rw [hw0] at h
    exact h.mono_left (nhdsWithin_le_of_mem (Icc_mem_nhdsGT (by linarith)))
  have hsub : Tendsto (fun t : ℝ => t - a) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-a) tendsto_id
  have hv₁lim : Tendsto (fun t => w (t - a)⁻¹) atTop (𝓝 vI) :=
    hwlim.comp (tendsto_inv_atTop_nhdsGT_zero.comp hsub)
  have hv₁b : ∀ t ∈ Ioi r₁,
      ‖w (t - a)⁻¹ - vI‖ ≤ (Real.exp (∫ s in Ioi t, ‖Mx s‖) - 1) * ‖vI‖ := fun t ht => by
    have h := hwb _ (hσ t ht)
    rwa [uIoc_of_le (hσ t ht).1.le, hmassN _ (hσ t ht), inv_inv, add_sub_cancel] at h
  -- extension to `(a, ∞)`
  obtain ⟨v, hv0, hvd⟩ := linear_exists_Ioi hM hr₀ (w (r₀ - a)⁻¹)
  have heq : EqOn v (fun t => w (t - a)⁻¹) (Ioi r₁) :=
    linear_eqOn_of_hasDerivAt ordConnected_Ioi (hM.mono (Ioi_subset_Ioi ha1.le))
      (fun t ht => hvd t (lt_trans ha1 ht)) hv₁d (show r₀ ∈ Ioi r₁ from h1r) hv0
  refine ⟨v, hvd, hv₁lim.congr' ?_, fun t ht => ?_⟩
  · filter_upwards [eventually_gt_atTop r₁] with t ht using (heq ht).symm
  · rw [heq (lt_of_lt_of_le h1r ht)]
    exact hv₁b t (lt_of_lt_of_le h1r ht)

/-- **Uniqueness at `+∞`** (integrable coefficient): two solutions of `v' = M v` on `(a, ∞)` with
the same limit as `t → ∞` agree. -/
theorem linear_eqOn_atTop {r₀ : ℝ} (hM : ContinuousOn Mx (Ioi a)) (hr₀ : a < r₀)
    (hint : IntegrableOn (fun t => ‖Mx t‖) (Ioi r₀)) {u w : ℝ → ℂ × ℂ}
    (hu : ∀ t ∈ Ioi a, HasDerivAt u (Mx t (u t)) t) (hw : ∀ t ∈ Ioi a, HasDerivAt w (Mx t (w t)) t)
    {L : ℂ × ℂ} (huL : Tendsto u atTop (𝓝 L)) (hwL : Tendsto w atTop (𝓝 L)) :
    EqOn u w (Ioi a) := by
  set S := (r₀ - a)⁻¹
  obtain ⟨N, hN, hNc, hNi, -⟩ := lv_inversion hM hr₀ hint
  have hpos : ∀ s ∈ Ioo 0 S, a < a + s⁻¹ := fun s hs => by
    linarith [inv_pos.2 hs.1]
  have hinvlim : Tendsto (fun s : ℝ => a + s⁻¹) (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_left _ a tendsto_inv_nhdsGT_zero
  have hhat := linear_eqOn_of_tendsto_nhdsGT (J := Ioo 0 S) (a := 0) Ioo_subset_Ioi_self
    (fun s hs x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hs.2⟩) hNc hNi
    (u := fun s => u (a + s⁻¹)) (w := fun s => w (a + s⁻¹))
    (fun s hs => lv_hasDerivAt_comp_add_inv hN (ne_of_gt hs.1) (hu _ (hpos s hs)))
    (fun s hs => lv_hasDerivAt_comp_add_inv hN (ne_of_gt hs.1) (hw _ (hpos s hs)))
    (huL.comp hinvlim) (hwL.comp hinvlim)
  have hmem : (r₀ + 1 - a)⁻¹ ∈ Ioo 0 S :=
    ⟨inv_pos.2 (by linarith), inv_strictAnti₀ (by linarith) (by linarith)⟩
  have h1 := hhat hmem
  simp only [inv_inv, add_sub_cancel] at h1
  exact linear_eqOn_Ioi hM hu hw (show a < r₀ + 1 by linarith) h1

end Infinity

end ModeStability.ODE
