module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
import ModeStability.AllAngular.FluxL

/-!
# Zero frequency, neutral case `e = 0`

Source: the all-angular research notes in preparation, p. 9, Proposition 7.1, the case `e = 0`.
At `ω = 0`, `e = 0` the radial
equation (7.2) is the positive static equation `(ΔR')' − LR = 0` on `(a, ∞)`, and the horizon
condition is the regular one (`Θ ≡ 0`): `R − B = O(r − a)`, `R' = O(1)` as `r ↓ a`; at an extremal
horizon (`|Q| = M`) the bounded-mode condition `R = O(1)` is used instead. Under the finite-energy
condition (7.1), `∫_a^∞ |R|² dr < ∞`, the mode vanishes.

The proof avoids the Frobenius analysis at infinity and the case distinction `L > 0` / `L = 0` of
the paper. With `P = ΔR'` and `G = Re(P R̄) = (Δ/2)(|R|²)'`,
`G' = Δ|R'|² + L|R|² ≥ 0`, so `G` is nondecreasing on `(a, ∞)`. At the horizon `P → 0` (for the
regular branch since `Δ → 0` and `R' = O(1)`; for a bounded extremal mode by
`fl_norm_le_of_bounded`, since `‖P'‖ = L‖R‖` is bounded near `a`) and `R` is bounded, so `G → 0`.
Hence `G ≥ 0`, `|R|²` is nondecreasing, and a nonzero value `R(r₁)` would give
`|R|² ≥ |R(r₁)|² > 0` on `(r₁, ∞)`, contradicting integrability.

* `zero_frequency_neutral`: regular horizon condition, static form of the equation.
* `zero_frequency_neutral_extremal`: bounded mode at an extremal horizon, static form.
* `zero_frequency_neutral_of_radial`, `zero_frequency_neutral_extremal_of_radial`: the same with
  the
  radial equation in the form `(ΔR')' + (K²/Δ − L)R = 0` at `e = 0`, `ω = 0` (where `K ≡ 0`).

The clause of Proposition 7.1 on Gajic's weighted energy `𝓔_p` is not encoded.
-/

public section

open Complex Set Filter Asymptotics Topology MeasureTheory

namespace ModeStability.AllAngular

/-! ### The monotone current -/

/-- `G = Re(Δ R' R̄)` has derivative `Δ‖R'‖² + L‖R‖²` for a solution of `(ΔR')' = LR`. -/
private theorem zn_hasDerivAt_current {M Q L : ℝ} {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s) ((L : ℂ) * R r) r)
    {r : ℝ} (hr : r ∈ Ioi (outerHorizon M Q)) :
    HasDerivAt (fun s => ((delta M Q s : ℂ) * deriv R s * (starRingEnd ℂ) (R s)).re)
      (delta M Q r * ‖deriv R r‖ ^ 2 + L * ‖R r‖ ^ 2) r := by
  obtain ⟨hd, hP⟩ := hR r hr
  have hc : HasDerivAt (fun s => (starRingEnd ℂ) (R s)) ((starRingEnd ℂ) (deriv R r)) r :=
    hd.hasDerivAt.star
  have hG := hP.mul hc
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r hG
  have hfun : (fun s => ((delta M Q s : ℂ) * deriv R s * (starRingEnd ℂ) (R s)).re) =
      Complex.reCLM ∘ fun s => (delta M Q s : ℂ) * deriv R s * (starRingEnd ℂ) (R s) := by
    funext s
    simp
  rw [hfun]
  refine hRe.congr_deriv ?_
  rw [Complex.reCLM_apply, mul_assoc, mul_assoc, Complex.mul_conj, Complex.mul_conj,
    Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  ring

/-- `‖R‖²` has derivative `2 Re(R' R̄)`. -/
private theorem zn_hasDerivAt_normSq {R : ℝ → ℂ} {r : ℝ} (hd : DifferentiableAt ℝ R r) :
    HasDerivAt (fun s => ‖R s‖ ^ 2) (2 * (deriv R r * (starRingEnd ℂ) (R r)).re) r := by
  have hc : HasDerivAt (fun s => (starRingEnd ℂ) (R s)) ((starRingEnd ℂ) (deriv R r)) r :=
    hd.hasDerivAt.star
  have hG := hd.hasDerivAt.mul hc
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r hG
  have hfun : (fun s => ‖R s‖ ^ 2) =
      Complex.reCLM ∘ fun s => R s * (starRingEnd ℂ) (R s) := by
    funext s
    rw [Function.comp_apply, Complex.reCLM_apply, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  rw [hfun]
  refine hRe.congr_deriv ?_
  have h2 : (R r * (starRingEnd ℂ) (deriv R r)).re = (deriv R r * (starRingEnd ℂ) (R r)).re := by
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
  rw [Complex.reCLM_apply, Complex.add_re, h2]
  ring

/-- Core argument: if `(ΔR')' = LR` with `L ≥ 0`, `R` is bounded near `a`, `ΔR' → 0` as `r ↓ a`,
and `|R|²` is integrable on `(a, ∞)`, then `R = 0` on `(a, ∞)`. -/
private theorem zn_eqOn_zero {M Q L : ℝ} (hL : 0 ≤ L) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s) ((L : ℂ) * R r) r)
    (hbdd : R =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))
    (hP : Tendsto (fun r => (delta M Q r : ℂ) * deriv R r) (𝓝[>] (outerHorizon M Q)) (𝓝 0))
    (hint : IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi (outerHorizon M Q))) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  set a := outerHorizon M Q with ha
  set G : ℝ → ℝ := fun s => ((delta M Q s : ℂ) * deriv R s * (starRingEnd ℂ) (R s)).re with hGdef
  -- `G` is nondecreasing on `(a, ∞)`
  have hGd : ∀ r ∈ Ioi a, HasDerivAt G (delta M Q r * ‖deriv R r‖ ^ 2 + L * ‖R r‖ ^ 2) r :=
    fun r hr => zn_hasDerivAt_current hR hr
  have hGmono : MonotoneOn G (Ioi a) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi a)
      (f' := fun r => delta M Q r * ‖deriv R r‖ ^ 2 + L * ‖R r‖ ^ 2)
      (fun r hr => (hGd r hr).continuousAt.continuousWithinAt) ?_ ?_
    · intro r hr
      rw [interior_Ioi] at hr ⊢
      exact (hGd r hr).hasDerivWithinAt
    · intro r hr
      rw [interior_Ioi] at hr
      have hΔ := fl_delta_pos (show a < r from hr)
      positivity
  -- `G → 0` at the horizon
  obtain ⟨C, hC⟩ := hbdd.bound
  have hG0 : Tendsto G (𝓝[>] a) (𝓝 0) := by
    have hlim : Tendsto (fun r => ‖(delta M Q r : ℂ) * deriv R r‖ * C) (𝓝[>] a) (𝓝 0) := by
      have := hP.norm.mul_const C
      rwa [norm_zero, zero_mul] at this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hC] with r hr
    rw [norm_one, mul_one] at hr
    rw [hGdef, Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul _ ((starRingEnd ℂ) (R r)), Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)
  -- hence `G ≥ 0` on `(a, ∞)`
  have hGnn : ∀ r ∈ Ioi a, 0 ≤ G r := by
    intro r hr
    refine le_of_tendsto hG0 ?_
    filter_upwards [Ioo_mem_nhdsGT (show a < r from hr)] with s hs
    exact hGmono hs.1 hr hs.2.le
  -- `‖R‖²` is nondecreasing on `(a, ∞)`
  have hNmono : MonotoneOn (fun s => ‖R s‖ ^ 2) (Ioi a) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi a)
      (f' := fun r => 2 * (deriv R r * (starRingEnd ℂ) (R r)).re)
      (fun r hr => (zn_hasDerivAt_normSq (hR r hr).1).continuousAt.continuousWithinAt) ?_ ?_
    · intro r hr
      rw [interior_Ioi] at hr ⊢
      exact (zn_hasDerivAt_normSq (hR r hr).1).hasDerivWithinAt
    · intro r hr
      rw [interior_Ioi] at hr
      have hΔ := fl_delta_pos (show a < r from hr)
      have h := hGnn r hr
      rw [hGdef] at h
      simp only at h
      rw [mul_assoc, Complex.re_ofReal_mul] at h
      have := (mul_nonneg_iff_of_pos_left hΔ).1 h
      positivity
  -- a nonzero value contradicts integrability
  intro r₁ hr₁
  by_contra hne
  have hpos : 0 < ‖R r₁‖ ^ 2 := by
    have : R r₁ ≠ 0 := hne
    positivity
  have hint1 : IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi r₁) :=
    hint.mono_set (Ioi_subset_Ioi (le_of_lt hr₁))
  have hconst : IntegrableOn (fun _ : ℝ => ‖R r₁‖ ^ 2) (Ioi r₁) := by
    refine Integrable.mono' hint1 aestronglyMeasurable_const ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact hNmono hr₁ (lt_trans hr₁ hr) (le_of_lt hr)
  rcases (integrableOn_const_iff).1 hconst with h0 | hfin
  · rw [enorm_eq_zero] at h0
    exact hpos.ne' h0
  · rw [Real.volume_Ioi] at hfin
    exact lt_irrefl _ hfin

/-! ### The horizon limits of `ΔR'` -/

/-- Regular horizon: `R − B = O(r − a)` gives `R = O(1)`. -/
private theorem zn_bdd_of_regular {M Q : ℝ} {R : ℝ → ℂ} {B : ℂ}
    (hH1 : (fun r => R r - B) =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q)) :
    R =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)) := by
  have h1 : (fun r : ℝ => r - outerHorizon M Q) =O[𝓝[>] (outerHorizon M Q)]
      (fun _ => (1 : ℝ)) :=
    (((continuous_sub_right (outerHorizon M Q)).tendsto (outerHorizon M Q)).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  have h2 := (hH1.trans h1).add (isBigO_const_one ℝ B (𝓝[>] (outerHorizon M Q)))
  refine h2.congr_left fun r => ?_
  exact sub_add_cancel _ _

/-- Regular horizon: `R' = O(1)` gives `ΔR' → 0`. -/
private theorem zn_tendsto_of_regular {M Q : ℝ} {R : ℝ → ℂ}
    (hH2 : deriv R =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))) :
    Tendsto (fun r => (delta M Q r : ℂ) * deriv R r) (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hH2.bound
  have hΔa : delta M Q (outerHorizon M Q) = 0 := by
    unfold delta
    rw [sub_self, zero_mul]
  have hlim : Tendsto (fun r => |delta M Q r| * C) (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
    have hc : Continuous (fun r => |delta M Q r| * C) :=
      (continuous_abs.comp (fl_continuous_delta M Q)).mul continuous_const
    have := (hc.tendsto (outerHorizon M Q)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (outerHorizon M Q)))
    rwa [hΔa, abs_zero, zero_mul] at this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hC] with r hr
  rw [norm_one, mul_one] at hr
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hr (abs_nonneg _)

/-- Extremal horizon (`b = a`): a bounded solution of `(ΔR')' = LR` has `ΔR' → 0`
(via `fl_norm_le_of_bounded`: `‖ΔR'(s)‖ ≤ |L| C (s − a)`). -/
private theorem zn_tendsto_of_bounded {M Q L : ℝ}
    (hab : innerHorizon M Q = outerHorizon M Q) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s) ((L : ℂ) * R r) r)
    (hbdd : R =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ))) :
    Tendsto (fun r => (delta M Q r : ℂ) * deriv R r) (𝓝[>] (outerHorizon M Q)) (𝓝 0) := by
  have hΔ : ∀ r, delta M Q r = (r - outerHorizon M Q) ^ 2 := by
    intro r
    unfold delta
    rw [hab]
    ring
  set a := outerHorizon M Q with ha
  obtain ⟨C, hC⟩ := hbdd.bound
  obtain ⟨ρ, hρ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hC
  have hRb : ∀ t ∈ Ioo a ρ, ‖R t‖ ≤ C := by
    intro t ht
    have h := hsub ht
    simpa using h
  set P : ℝ → ℂ := fun t => (delta M Q t : ℂ) * deriv R t with hP
  have hRd : ∀ t ∈ Ioo a ρ, HasDerivAt R (P t / ((t - a : ℝ) : ℂ) ^ 2) t := by
    intro t ht
    refine ((hR t ht.1).1.hasDerivAt).congr_deriv ?_
    have hta : (t : ℂ) - (a : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.2 (sub_pos.2 ht.1).ne'
    rw [hP]
    simp only [hΔ t]
    push_cast
    field_simp
  have hPd : ∀ t ∈ Ioo a ρ, HasDerivAt P ((L : ℂ) * R t) t := fun t ht => (hR t ht.1).2
  have hPb : ∀ t ∈ Ioo a ρ, ‖(L : ℂ) * R t‖ ≤ |L| * C := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hRb t ht) (abs_nonneg _)
  have hPs := fl_norm_le_of_bounded hRd hPd hRb hPb
  have hlim : Tendsto (fun r : ℝ => |L| * C * (r - a)) (𝓝[>] a) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => |L| * C * (r - a)) := by fun_prop
    have := (hc.tendsto a).mono_left (nhdsWithin_le_nhds (s := Ioi a))
    rwa [sub_self, mul_zero] at this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT hρ] with t ht
  exact hPs t ht

/-! ### Proposition 7.1 at `e = 0` -/

/-- Proposition 7.1 (p. 9), case `e = 0`, regular horizon: a solution of the static equation
`(ΔR')' − LR = 0` ((7.2) at `e = 0`) with `L ≥ 0`, the regular horizon condition `R − B = O(r − a)`,
`R' = O(1)`, and finite energy (7.1) `∫_a^∞ |R|² dr < ∞` vanishes on `(a, ∞)`. -/
theorem zero_frequency_neutral {M Q L : ℝ} (_hM : 0 < M) (_hQ : |Q| ≤ M) (hL : 0 ≤ L)
    {R : ℝ → ℂ} {B : ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s) (((L : ℝ) : ℂ) * R r) r)
    (hH1 : (fun r => R r - B) =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q))
    (hH2 : deriv R =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))
    (hint : IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi (outerHorizon M Q))) :
    EqOn R 0 (Ioi (outerHorizon M Q)) :=
  zn_eqOn_zero hL hR (zn_bdd_of_regular hH1) (zn_tendsto_of_regular hH2) hint

/-- Proposition 7.1 (p. 9), case `e = 0`, extremal horizon (`|Q| = M`): a solution of the static
equation `(ΔR')' − LR = 0` with `L ≥ 0` that is bounded near `a = M` and has finite energy (7.1)
vanishes on `(a, ∞)`. -/
theorem zero_frequency_neutral_extremal {M Q L : ℝ} (_hM : 0 < M) (hQ : |Q| = M) (hL : 0 ≤ L)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s) (((L : ℝ) : ℂ) * R r) r)
    (hbdd : R =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))
    (hint : IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi (outerHorizon M Q))) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  have hab : innerHorizon M Q = outerHorizon M Q :=
    (fl_innerHorizon_of_abs_eq hQ).trans (fl_outerHorizon_of_abs_eq hQ).symm
  exact zn_eqOn_zero hL hR hbdd (zn_tendsto_of_bounded hab hR hbdd) hint

/-- The radial equation `(ΔR')' + (K²/Δ − L)R = 0` at `e = 0`, `ω = 0` is `(ΔR')' = LR`. -/
private theorem zn_static_of_radial {M Q L : ℝ} {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK 0 0 r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s) (((L : ℝ) : ℂ) * R r) r := by
  intro r hr
  refine ⟨(hR r hr).1, (hR r hr).2.congr_deriv ?_⟩
  have hK : radialK 0 0 r = 0 := by
    unfold radialK
    ring
  rw [hK]
  push_cast
  ring

/-- Proposition 7.1 (p. 9), case `e = 0`, regular horizon, with the radial equation (1.2) at
`e = 0`, `ω = 0`. -/
theorem zero_frequency_neutral_of_radial {M Q L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M) (hL : 0 ≤ L)
    {R : ℝ → ℂ} {B : ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK 0 0 r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hH1 : (fun r => R r - B) =O[𝓝[>] (outerHorizon M Q)] (fun r => r - outerHorizon M Q))
    (hH2 : deriv R =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))
    (hint : IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi (outerHorizon M Q))) :
    EqOn R 0 (Ioi (outerHorizon M Q)) :=
  zero_frequency_neutral hM hQ hL (zn_static_of_radial hR) hH1 hH2 hint

/-- Proposition 7.1 (p. 9), case `e = 0`, extremal horizon (`|Q| = M`), bounded mode, with the
radial equation (1.2) at `e = 0`, `ω = 0`. -/
theorem zero_frequency_neutral_extremal_of_radial {M Q L : ℝ} (hM : 0 < M) (hQ : |Q| = M)
    (hL : 0 ≤ L) {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK 0 0 r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (hbdd : R =O[𝓝[>] (outerHorizon M Q)] (fun _ => (1 : ℝ)))
    (hint : IntegrableOn (fun r => ‖R r‖ ^ 2) (Ioi (outerHorizon M Q))) :
    EqOn R 0 (Ioi (outerHorizon M Q)) :=
  zero_frequency_neutral_extremal hM hQ hL (zn_static_of_radial hR) hbdd hint

end ModeStability.AllAngular

end
