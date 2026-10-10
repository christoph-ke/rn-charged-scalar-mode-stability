module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityRAux

/-!
# Improper integration for the integrated source identity (6.3)

Source: the all-angular research notes in preparation (pp. 7–8).
These versions of the improper current integration lemmas take an integrated
current equation on compact intervals. They apply to the absolutely continuous
currents of the Green solution for an `L²` source, without pointwise second derivatives.
-/

public section

open Complex Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

/-- **Improper integration, abstract form.** Let `S ⊆ ℝ` be measurable and covered (in the sense
of `MeasureTheory.AECover` for `volume` restricted to `S`) by the intervals `[a i, b i]` along a
countably generated filter `l`, eventually contained in `S`. Assume the integrated current equation
on compact subintervals of `S`. The bulk
`b` is continuous and nonnegative on `S`, the source term `g` is integrable on `S`, and
`φ(a i) → A`, `φ(b i) → B`, then `b` is integrable on `S` and `∫_S b = A − B − ∫_S g`. -/
theorem source_integrableOn_bulk_of_aecover {ι : Type*} {l : Filter ι} [l.NeBot]
    [l.IsCountablyGenerated] {S : Set ℝ} (hS : MeasurableSet S) {a b : ι → ℝ}
    (hcov : AECover (volume.restrict S) l fun i => Icc (a i) (b i))
    (hab : ∀ᶠ i in l, a i ≤ b i ∧ Icc (a i) (b i) ⊆ S)
    {φ bulk src : ℝ → ℝ} {A B : ℝ}
    (hφ : ∀ u v, u ≤ v → Icc u v ⊆ S →
      (∫ x in u..v, -bulk x - src x) = φ v - φ u)
    (hbc : ContinuousOn bulk S) (hb0 : ∀ x ∈ S, 0 ≤ bulk x) (hsrc : IntegrableOn src S)
    (hA : Tendsto (fun i => φ (a i)) l (𝓝 A)) (hB : Tendsto (fun i => φ (b i)) l (𝓝 B)) :
    IntegrableOn bulk S ∧ ∫ x in S, bulk x = A - B - ∫ x in S, src x := by
  have hres : ∀ {i}, Icc (a i) (b i) ⊆ S →
      (volume.restrict S).restrict (Icc (a i) (b i)) = volume.restrict (Icc (a i) (b i)) := by
    intro i hsub
    rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.2 hsub]
  -- the fundamental theorem of calculus on the truncated intervals
  have hftc : ∀ᶠ i in l, ∫ x in Icc (a i) (b i), bulk x ∂(volume.restrict S) =
      φ (a i) - φ (b i) - ∫ x in Icc (a i) (b i), src x ∂(volume.restrict S) := by
    filter_upwards [hab] with i ⟨hle, hsub⟩
    rw [hres hsub, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle]
    have hsub' : uIcc (a i) (b i) ⊆ S := by rwa [uIcc_of_le hle]
    have hbi : IntervalIntegrable bulk volume (a i) (b i) :=
      (hbc.mono hsub').intervalIntegrable
    have hsi : IntervalIntegrable src volume (a i) (b i) :=
      (hsrc.mono_set hsub').intervalIntegrable
    have h := hφ (a i) (b i) hle hsub
    rw [intervalIntegral.integral_sub (f := fun y => -bulk y) hbi.neg hsi,
      intervalIntegral.integral_neg] at h
    linarith
  have hsrcT := hcov.integral_tendsto_of_countably_generated hsrc
  have hlim : Tendsto (fun i => ∫ x in Icc (a i) (b i), bulk x ∂(volume.restrict S)) l
      (𝓝 (A - B - ∫ x in S, src x)) :=
    ((hA.sub hB).sub hsrcT).congr' (hftc.mono fun i hi => hi.symm)
  have hmeas : AEStronglyMeasurable bulk (volume.restrict S) := hbc.aestronglyMeasurable hS
  have hint : Integrable bulk (volume.restrict S) := by
    refine hcov.integrable_of_lintegral_enorm_tendsto (A - B - ∫ x in S, src x) hmeas ?_
    refine ((ENNReal.continuous_ofReal.tendsto _).comp hlim).congr' ?_
    filter_upwards [hab] with i hi
    have hsub := hi.2
    rw [Function.comp_apply, hres hsub, ofReal_integral_eq_lintegral_ofReal]
    · exact setLIntegral_congr_fun measurableSet_Icc fun x hx =>
        (Real.enorm_eq_ofReal (hb0 x (hsub hx))).symm
    · exact (hbc.mono hsub).integrableOn_compact isCompact_Icc
    · exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun x hx => hb0 x (hsub hx))
  exact ⟨hint, hcov.integral_eq_of_tendsto _ hint hlim⟩

/-- **Improper integration on a bounded open interval.** Assume the integrated current equation
on `(α, β)`. If `b` is
continuous and nonnegative there, `g` is integrable on `(α, β)`, `φ → A` at `α⁺` and `φ → B` at
`β⁻`, then `b` is integrable on `(α, β)` and `∫_{(α,β)} b = A − B − ∫_{(α,β)} g`. -/
theorem source_integral_Ioo_bulk_eq {α β : ℝ} (hαβ : α < β) {φ bulk src : ℝ → ℝ} {A B : ℝ}
    (hφ : ∀ u v, u ≤ v → Icc u v ⊆ Ioo α β →
      (∫ x in u..v, -bulk x - src x) = φ v - φ u)
    (hbc : ContinuousOn bulk (Ioo α β)) (hb0 : ∀ x ∈ Ioo α β, 0 ≤ bulk x)
    (hsrc : IntegrableOn src (Ioo α β))
    (hA : Tendsto φ (𝓝[>] α) (𝓝 A)) (hB : Tendsto φ (𝓝[<] β) (𝓝 B)) :
    IntegrableOn bulk (Ioo α β) ∧ ∫ x in Ioo α β, bulk x = A - B - ∫ x in Ioo α β, src x := by
  have hαc : α < (α + β) / 2 := by linarith
  have hcβ : (α + β) / 2 < β := by linarith
  have hfst : Tendsto Prod.fst (𝓝[>] α ×ˢ 𝓝[<] β) (𝓝[>] α) := tendsto_fst
  have hsnd : Tendsto Prod.snd (𝓝[>] α ×ˢ 𝓝[<] β) (𝓝[<] β) := tendsto_snd
  refine source_integrableOn_bulk_of_aecover measurableSet_Ioo
    (aecover_Ioo_of_Icc (hfst.mono_right nhdsWithin_le_nhds)
      (hsnd.mono_right nhdsWithin_le_nhds)) ?_ hφ hbc hb0 hsrc (hA.comp hfst) (hB.comp hsnd)
  filter_upwards [hfst.eventually (Ioo_mem_nhdsGT hαc), hsnd.eventually (Ioo_mem_nhdsLT hcβ)]
    with i h1 h2
  exact ⟨h1.2.le.trans h2.1.le, Icc_subset_Ioo h1.1 h2.2⟩

/-- **Improper integration on a half-line.** Assume the integrated current equation on `(α, ∞)`.
If `b` is continuous and
nonnegative there, `g` is integrable on `(α, ∞)`, `φ → A` at `α⁺` and `φ → B` at `+∞`, then `b`
is integrable on `(α, ∞)` and `∫_{(α,∞)} b = A − B − ∫_{(α,∞)} g`. -/
theorem source_integral_Ioi_bulk_eq {α : ℝ} {φ bulk src : ℝ → ℝ} {A B : ℝ}
    (hφ : ∀ u v, u ≤ v → Icc u v ⊆ Ioi α →
      (∫ x in u..v, -bulk x - src x) = φ v - φ u)
    (hbc : ContinuousOn bulk (Ioi α)) (hb0 : ∀ x ∈ Ioi α, 0 ≤ bulk x)
    (hsrc : IntegrableOn src (Ioi α))
    (hA : Tendsto φ (𝓝[>] α) (𝓝 A)) (hB : Tendsto φ atTop (𝓝 B)) :
    IntegrableOn bulk (Ioi α) ∧ ∫ x in Ioi α, bulk x = A - B - ∫ x in Ioi α, src x := by
  have hfst : Tendsto Prod.fst (𝓝[>] α ×ˢ (atTop : Filter ℝ)) (𝓝[>] α) := tendsto_fst
  have hsnd : Tendsto Prod.snd (𝓝[>] α ×ˢ (atTop : Filter ℝ)) atTop := tendsto_snd
  have hcov : AECover (volume.restrict (Ioi α)) (𝓝[>] α ×ˢ (atTop : Filter ℝ))
      fun i => Icc i.1 i.2 :=
    ((aecover_Ioi_of_Ioi (hfst.mono_right nhdsWithin_le_nhds)).inter (aecover_Iic hsnd)).superset
      (fun _ _ hx => ⟨hx.1.le, hx.2⟩) fun _ => measurableSet_Icc
  refine source_integrableOn_bulk_of_aecover measurableSet_Ioi hcov ?_ hφ hbc hb0 hsrc
    (hA.comp hfst) (hB.comp hsnd)
  filter_upwards [hfst.eventually (Ioo_mem_nhdsGT (lt_add_one α)),
    hsnd.eventually (eventually_ge_atTop (α + 1))] with i h1 h2
  exact ⟨h1.2.le.trans h2, fun x hx => lt_of_lt_of_le h1.1 hx.1⟩

end ModeStability.AllAngular

end
