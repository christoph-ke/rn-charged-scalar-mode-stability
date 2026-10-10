module

public import Mathlib
public import ModeStability.AllAngular.SourceIdentityRImproper

/-!
# Gluing the integrated currents in (6.3)

Source: the all-angular research notes in preparation (pp. 7–8).
This integrated version of the abstract identity permits locally absolutely
continuous currents and therefore `L²` sources. The turning points may coincide,
so the same gluing lemma covers `L > 0` and `L = 0`. Its lower Lebesgue integrals
are finite as a consequence, rather than an additional hypothesis.
-/

public section

open Set Filter Topology MeasureTheory

namespace ModeStability.AllAngular

private theorem sr_nonnegative_lintegral {s : Set ℝ} (hs : MeasurableSet s)
    {b : ℝ → ℝ} (hi : IntegrableOn b s) (h0 : ∀ r ∈ s, 0 ≤ b r) :
    (∫⁻ r in s, ENNReal.ofReal (b r)) = ENNReal.ofReal (∫ r in s, b r) ∧
      0 ≤ ∫ r in s, b r :=
  ⟨(ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_iff' hs).mpr (ae_of_all _ h0))).symm,
    setIntegral_nonneg hs h0⟩

/-- The three-region source identity from integrated currents. The two outer currents
vanish at the physical endpoints and match the middle current at the turning points.
The source density `src` includes the real part and, in `r`, the Jacobian weight. -/
theorem source_three_region_identity {a r₁ r₂ : ℝ} (ha : a < r₁) (h₁₂ : r₁ ≤ r₂)
    {J₁ Jm J₂ b₁ bm b₂ src : ℝ → ℝ}
    (h₁ : ∀ u v, u ≤ v → Icc u v ⊆ Ioo a r₁ →
      (∫ r in u..v, -b₁ r - src r) = J₁ v - J₁ u)
    (hm : (∫ r in r₁..r₂, -bm r - src r) = Jm r₂ - Jm r₁)
    (h₂ : ∀ u v, u ≤ v → Icc u v ⊆ Ioi r₂ →
      (∫ r in u..v, -b₂ r - src r) = J₂ v - J₂ u)
    (hb₁ : ContinuousOn b₁ (Ioo a r₁)) (hbm : ContinuousOn bm (Icc r₁ r₂))
    (hb₂ : ContinuousOn b₂ (Ioi r₂))
    (hp₁ : ∀ r ∈ Ioo a r₁, 0 ≤ b₁ r) (hpm : ∀ r ∈ Icc r₁ r₂, 0 ≤ bm r)
    (hp₂ : ∀ r ∈ Ioi r₂, 0 ≤ b₂ r)
    (hsrc : Integrable src) (hsrc0 : ∀ r ∉ Ioi a, src r = 0)
    (hH : Tendsto J₁ (𝓝[>] a) (𝓝 0))
    (hT₁ : Tendsto J₁ (𝓝[<] r₁) (𝓝 (Jm r₁)))
    (hT₂ : Tendsto J₂ (𝓝[>] r₂) (𝓝 (Jm r₂)))
    (hI : Tendsto J₂ atTop (𝓝 0)) :
    let B := (∫⁻ r in Ioo a r₁, ENNReal.ofReal (b₁ r)) +
      (∫⁻ r in Icc r₁ r₂, ENNReal.ofReal (bm r)) +
      (∫⁻ r in Ioi r₂, ENNReal.ofReal (b₂ r))
    B < ⊤ ∧ B.toReal = -(∫ r, src r) := by
  obtain ⟨hi₁, he₁⟩ := source_integral_Ioo_bulk_eq ha h₁ hb₁ hp₁ hsrc.integrableOn hH hT₁
  obtain ⟨hi₂, he₂⟩ := source_integral_Ioi_bulk_eq h₂ hb₂ hp₂ hsrc.integrableOn hT₂ hI
  have him : IntegrableOn bm (Icc r₁ r₂) := hbm.integrableOn_compact isCompact_Icc
  have hbmi : IntervalIntegrable bm volume r₁ r₂ :=
    (hbm.mono (by rw [uIcc_of_le h₁₂])).intervalIntegrable
  have hem : (∫ r in Icc r₁ r₂, bm r) = Jm r₁ - Jm r₂ - ∫ r in Icc r₁ r₂, src r := by
    rw [intervalIntegral.integral_sub (f := fun r => -bm r) hbmi.neg hsrc.intervalIntegrable,
      intervalIntegral.integral_neg, intervalIntegral.integral_of_le h₁₂,
      intervalIntegral.integral_of_le h₁₂, ← integral_Icc_eq_integral_Ioc,
      ← integral_Icc_eq_integral_Ioc] at hm
    linarith
  have hsplit : (∫ r in Ioo a r₁, src r) + (∫ r in Icc r₁ r₂, src r) +
      (∫ r in Ioi r₂, src r) = ∫ r in Ioi a, src r := by
    rw [← setIntegral_union
      (Set.disjoint_left.mpr fun r hleft hright => absurd hright.1 (not_le.mpr hleft.2))
      measurableSet_Icc hsrc.integrableOn hsrc.integrableOn,
      Ioo_union_Icc_eq_Ioc ha h₁₂,
      ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        hsrc.integrableOn hsrc.integrableOn,
      Ioc_union_Ioi_eq_Ioi (ha.le.trans h₁₂)]
  have htotal : (∫ r in Ioo a r₁, b₁ r) + (∫ r in Icc r₁ r₂, bm r) +
      (∫ r in Ioi r₂, b₂ r) = -(∫ r, src r) := by
    have hs : (∫ r in Ioi a, src r) = ∫ r, src r :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hsrc0
    linarith
  obtain ⟨hl₁, hn₁⟩ := sr_nonnegative_lintegral measurableSet_Ioo hi₁ hp₁
  obtain ⟨hlm, hnm⟩ := sr_nonnegative_lintegral measurableSet_Icc him hpm
  obtain ⟨hl₂, hn₂⟩ := sr_nonnegative_lintegral measurableSet_Ioi hi₂ hp₂
  dsimp only
  rw [hl₁, hlm, hl₂, ← ENNReal.ofReal_add hn₁ hnm,
    ← ENNReal.ofReal_add (add_nonneg hn₁ hnm) hn₂, htotal]
  exact ⟨ENNReal.ofReal_lt_top,
    ENNReal.toReal_ofReal (htotal ▸ add_nonneg (add_nonneg hn₁ hnm) hn₂)⟩

end ModeStability.AllAngular

end
