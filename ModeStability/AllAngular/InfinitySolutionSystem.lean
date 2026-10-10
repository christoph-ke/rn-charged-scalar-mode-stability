module

public import Mathlib
public import ModeStability.AllAngular.InfinitySolutionAux

/-!
# The outgoing solution at infinity: from the amplitude system back to the radial equation

Part of the construction of the outgoing solution `R_I` of
the all-angular research notes in preparation, (1.5) (normalized with leading coefficient `1`
in Sections 6 and 8). Given a solution `(A, B)` of the amplitude system of
`ModeStability.AllAngular.InfinitySolutionAux` on `(r₁, ∞)` (where `Θ' ≠ 0`), set

`u = (e^{iΘ}A − e^{−iΘ}B)/(2iΘ')`,  `v = (e^{iΘ}A + e^{−iΘ}B)/2`,  `R = u/r`.

Then `u' = v` (`hasDerivAt_ampU`) and `v' = −αv − (Θ'² + γ)u` (`hasDerivAt_ampV`), so `R`
solves the radial equation `(ΔR')' + (K²/Δ − L)R = 0` on `(r₁, ∞)` (`ampSol_radial`). Its
outgoing profile is `R̃ = r e^{−iΘ}R = (A − e^{−2iΘ}B)/(2iΘ')` (`profile_ampSol`) with
`R̃' = e^{−2iΘ}B` (`hasDerivAt_profile_ampSol`).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

namespace InfinitySolution

open InfinityUniqueness

/-- `u = (e^{iΘ}A − e^{−iΘ}B)/(2iΘ')`. -/
@[expose] noncomputable def ampU (M Q e ω : ℝ) (Θ : ℝ → ℝ) (A B : ℝ → ℂ) (r : ℝ) : ℂ :=
  (exp (I * Θ r) * A r - exp (-(I * Θ r)) * B r) / (2 * I * phaseRate M Q e ω r)

/-- `v = (e^{iΘ}A + e^{−iΘ}B)/2`, which is `u'`. -/
@[expose] noncomputable def ampV (Θ : ℝ → ℝ) (A B : ℝ → ℂ) (r : ℝ) : ℂ :=
  (exp (I * Θ r) * A r + exp (-(I * Θ r)) * B r) / 2

/-- The solution `R = u/r` of the radial equation defined by the amplitudes `(A, B)`. -/
@[expose] noncomputable def ampSol (M Q e ω : ℝ) (Θ : ℝ → ℝ) (A B : ℝ → ℂ) (r : ℝ) : ℂ :=
  ampU M Q e ω Θ A B r / r

variable {M Q e ω L : ℝ} {Θ : ℝ → ℝ} {A B : ℝ → ℂ}

theorem two_I_mul_ne_zero {x : ℝ} (hx : x ≠ 0) : (2 * I * (x : ℂ)) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (ofReal_ne_zero.2 hx)

/-- `u' = v`. -/
theorem hasDerivAt_ampU {t : ℝ} (hΔ : delta M Q t ≠ 0) (hθ : phaseRate M Q e ω t ≠ 0)
    (hΘ : HasDerivAt Θ (phaseRate M Q e ω t) t)
    (hA : HasDerivAt A (ampCoeffAA M Q e ω L t * A t + ampCoeffAB M Q e ω L Θ t * B t) t)
    (hB : HasDerivAt B (ampCoeffBA M Q e ω L Θ t * A t + ampCoeffBB M Q e ω L t * B t) t) :
    HasDerivAt (ampU M Q e ω Θ A B) (ampV Θ A B t) t := by
  have hE := hasDerivAt_exp_phase (M := M) (Q := Q) hΘ
  have hEi := hasDerivAt_exp_neg_phase (M := M) (Q := Q) hΘ
  have hθc : HasDerivAt (fun s => (phaseRate M Q e ω s : ℂ)) (phaseAccel M Q e ω t : ℂ) t :=
    (hasDerivAt_phaseRate hΔ).ofReal_comp
  have h := ((hE.mul hA).sub (hEi.mul hB)).div (hθc.const_mul (2 * I)) (two_I_mul_ne_zero hθ)
  refine h.congr_deriv ?_
  have hθ' : (phaseRate M Q e ω t : ℂ) ≠ 0 := ofReal_ne_zero.2 hθ
  have hE0 : exp (I * Θ t) ≠ 0 := exp_ne_zero _
  simp only [Pi.mul_apply, Pi.sub_apply]
  unfold ampV ampCoeffAA ampCoeffAB ampCoeffBA ampCoeffBB ampRhoP ampRhoM ampSigma
  push_cast
  rw [Complex.exp_neg]
  generalize exp (I * Θ t) = E at hE0 ⊢
  generalize (phaseRate M Q e ω t : ℂ) = θ at hθ' ⊢
  field_simp
  ring

/-- `v' = −αv − (Θ'² + γ)u`. -/
theorem hasDerivAt_ampV {t : ℝ} (hθ : phaseRate M Q e ω t ≠ 0)
    (hΘ : HasDerivAt Θ (phaseRate M Q e ω t) t)
    (hA : HasDerivAt A (ampCoeffAA M Q e ω L t * A t + ampCoeffAB M Q e ω L Θ t * B t) t)
    (hB : HasDerivAt B (ampCoeffBA M Q e ω L Θ t * A t + ampCoeffBB M Q e ω L t * B t) t) :
    HasDerivAt (ampV Θ A B)
      (-(dampCoeff M Q t : ℂ) * ampV Θ A B t -
        ((phaseRate M Q e ω t : ℂ) ^ 2 + potCoeff M Q L t) * ampU M Q e ω Θ A B t) t := by
  have hE := hasDerivAt_exp_phase (M := M) (Q := Q) hΘ
  have hEi := hasDerivAt_exp_neg_phase (M := M) (Q := Q) hΘ
  have h := ((hE.mul hA).add (hEi.mul hB)).div_const 2
  refine h.congr_deriv ?_
  have hθ' : (phaseRate M Q e ω t : ℂ) ≠ 0 := ofReal_ne_zero.2 hθ
  have hE0 : exp (I * Θ t) ≠ 0 := exp_ne_zero _
  unfold ampU ampV ampCoeffAA ampCoeffAB ampCoeffBA ampCoeffBB ampRhoP ampRhoM ampSigma
  push_cast
  rw [Complex.exp_neg]
  generalize exp (I * Θ t) = E at hE0 ⊢
  generalize (phaseRate M Q e ω t : ℂ) = θ at hθ' ⊢
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- `R' = (vr − u)/r²`. -/
theorem hasDerivAt_ampSol {t : ℝ} (ht : t ≠ 0) (hu : HasDerivAt (ampU M Q e ω Θ A B)
    (ampV Θ A B t) t) :
    HasDerivAt (ampSol M Q e ω Θ A B)
      ((ampV Θ A B t * t - ampU M Q e ω Θ A B t) / (t : ℂ) ^ 2) t := by
  have h := hu.div (hasDerivAt_ofReal_id t) (ofReal_ne_zero.2 ht)
  refine h.congr_deriv ?_
  ring

/-- The algebraic identity behind `ampSol_radial`. -/
theorem ampSol_radial_identity {t D K a g θ : ℝ} (ht : t ≠ 0) (hD : D ≠ 0)
    (hDe : D = t ^ 2 - 2 * M * t + Q ^ 2) (ha : a = (2 * M * t - 2 * Q ^ 2) / (t * D))
    (hg : g = (-2 * M * t + 2 * Q ^ 2 - L * t ^ 2) / (t ^ 2 * D)) (hθ : θ = K / D) (U V : ℂ) :
    ((2 * t - 2 * M : ℝ) : ℂ) * ((V * t - U) / (t : ℂ) ^ 2) +
        (D : ℂ) * ((((-(a : ℂ) * V - ((θ : ℂ) ^ 2 + g) * U) * t + V * 1 - V) * (t : ℂ) ^ 2 -
          (V * t - U) * (2 * (t : ℂ))) / ((t : ℂ) ^ 2) ^ 2) =
      -(((K ^ 2 / D - L : ℝ) : ℂ)) * (U / t) := by
  have hQ2 : (Q : ℂ) ^ 2 = D - t ^ 2 + 2 * M * t := by
    have : Q ^ 2 = D - t ^ 2 + 2 * M * t := by linarith
    exact_mod_cast this
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  have hDc : (D : ℂ) ≠ 0 := ofReal_ne_zero.2 hD
  subst ha hg hθ
  push_cast
  rw [hQ2]
  field_simp
  ring

/-- **The radial equation for `R = u/r`.** If `(A, B)` solves the amplitude system on `(r₁, ∞)`,
`r₁ ≥ a`, `r₁ > 0`, where `Θ' ≠ 0`, then `R = u/r` solves `(ΔR')' + (K²/Δ − L)R = 0` there. -/
theorem ampSol_radial (hQ : |Q| ≤ M) {r₁ : ℝ} (ha : outerHorizon M Q ≤ r₁) (h0 : 0 < r₁)
    (hθ : ∀ t ∈ Ioi r₁, phaseRate M Q e ω t ≠ 0)
    (hΘ : ∀ t ∈ Ioi r₁, HasDerivAt Θ (radialK e ω t / delta M Q t) t)
    (hA : ∀ t ∈ Ioi r₁,
      HasDerivAt A (ampCoeffAA M Q e ω L t * A t + ampCoeffAB M Q e ω L Θ t * B t) t)
    (hB : ∀ t ∈ Ioi r₁,
      HasDerivAt B (ampCoeffBA M Q e ω L Θ t * A t + ampCoeffBB M Q e ω L t * B t) t) :
    ∀ t ∈ Ioi r₁, DifferentiableAt ℝ (ampSol M Q e ω Θ A B) t ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv (ampSol M Q e ω Θ A B) s)
        (-(((radialK e ω t) ^ 2 / delta M Q t - L : ℝ) : ℂ) * ampSol M Q e ω Θ A B t) t := by
  have hΔ : ∀ t ∈ Ioi r₁, delta M Q t ≠ 0 := fun t ht => (delta_pos_of_lt (ha.trans_lt ht)).ne'
  have hu : ∀ t ∈ Ioi r₁, HasDerivAt (ampU M Q e ω Θ A B) (ampV Θ A B t) t := fun t ht =>
    hasDerivAt_ampU (hΔ t ht) (hθ t ht) (hΘ t ht) (hA t ht) (hB t ht)
  have hR : ∀ t ∈ Ioi r₁, HasDerivAt (ampSol M Q e ω Θ A B)
      ((ampV Θ A B t * t - ampU M Q e ω Θ A B t) / (t : ℂ) ^ 2) t := fun t ht =>
    hasDerivAt_ampSol (h0.trans ht).ne' (hu t ht)
  intro t ht
  refine ⟨(hR t ht).differentiableAt, ?_⟩
  have hev : (fun s => (delta M Q s : ℂ) * deriv (ampSol M Q e ω Θ A B) s) =ᶠ[𝓝 t]
      (fun s => (delta M Q s : ℂ) *
        ((ampV Θ A B s * s - ampU M Q e ω Θ A B s) / (s : ℂ) ^ 2)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    rw [(hR s hs).deriv]
  have hv := hasDerivAt_ampV (hθ t ht) (hΘ t ht) (hA t ht) (hB t ht)
  have hid := hasDerivAt_ofReal_id t
  have hd : HasDerivAt (fun s => (delta M Q s : ℂ)) ((2 * t - 2 * M : ℝ) : ℂ) t :=
    (hasDerivAt_delta M Q t).ofReal_comp
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 (h0.trans ht).ne'
  have h := hd.mul ((((hv.mul hid).sub (hu t ht)).div (hid.pow 2) (pow_ne_zero 2 ht0)))
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  have key := ampSol_radial_identity (t := t) (D := delta M Q t) (K := radialK e ω t)
    (a := dampCoeff M Q t) (g := potCoeff M Q L t) (θ := phaseRate M Q e ω t) (L := L)
    (h0.trans ht).ne' (hΔ t ht) (delta_eq hQ t) rfl rfl rfl (ampU M Q e ω Θ A B t)
    (ampV Θ A B t)
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one, mul_one] at key ⊢
  exact key

/-- The outgoing profile of `R = u/r`: `r e^{−iΘ}R = (A − e^{−2iΘ}B)/(2iΘ')`. -/
theorem profile_ampSol {t : ℝ} (ht : t ≠ 0) :
    (t : ℂ) * exp (-(I * (Θ t : ℂ))) * ampSol M Q e ω Θ A B t =
      (A t - exp (-(I * (Θ t : ℂ))) ^ 2 * B t) / (2 * I * phaseRate M Q e ω t) := by
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  have hE0 : exp (I * Θ t) ≠ 0 := exp_ne_zero _
  unfold ampSol ampU
  rw [Complex.exp_neg]
  generalize exp (I * Θ t) = E at hE0 ⊢
  generalize (phaseRate M Q e ω t : ℂ) = θ
  rcases eq_or_ne θ 0 with hθ0 | hθ0
  · simp [hθ0]
  field_simp

/-- The derivative of the outgoing profile of `R = u/r`: `R̃' = e^{−2iΘ}B`. -/
theorem hasDerivAt_profile_ampSol {t : ℝ} (ht : t ≠ 0) (hΘ : HasDerivAt Θ (phaseRate M Q e ω t) t)
    (hθ : phaseRate M Q e ω t ≠ 0) (hu : HasDerivAt (ampU M Q e ω Θ A B) (ampV Θ A B t) t) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * exp (-(I * (Θ s : ℂ))) * ampSol M Q e ω Θ A B s)
      (exp (-(I * (Θ t : ℂ))) ^ 2 * B t) t := by
  have hR := hasDerivAt_ampSol ht hu
  have h := hasDerivAt_profile hΘ hR.differentiableAt
  refine h.congr_deriv ?_
  rw [hR.deriv]
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  have hθ' : (phaseRate M Q e ω t : ℂ) ≠ 0 := ofReal_ne_zero.2 hθ
  have hE0 : exp (I * Θ t) ≠ 0 := exp_ne_zero _
  unfold ampSol ampU ampV
  rw [Complex.exp_neg]
  generalize exp (I * Θ t) = E at hE0 ⊢
  generalize (phaseRate M Q e ω t : ℂ) = θ at hθ' ⊢
  field_simp
  ring

end InfinitySolution

end ModeStability.AllAngular

end
