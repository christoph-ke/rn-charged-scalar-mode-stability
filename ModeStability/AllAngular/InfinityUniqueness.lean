module

public import Mathlib
public import ModeStability.Frozen.OuterHorizon
public import ModeStability.Frozen.InnerHorizon
public import ModeStability.Frozen.Delta
public import ModeStability.Frozen.RadialK
public import ModeStability.ODE.Uniqueness
public import ModeStability.AllAngular.InfinityUniquenessAux

/-!
# Uniqueness at the irregular singular point at infinity

Source: the all-angular research notes in preparation, p. 1. The paper asserts this without proof;
it is needed for the flux band `K(a) ≥ 0`. Here it is proved at infinity: a solution of the radial
equation `(ΔR')' + (K²/Δ − L)R = 0` on `r > a` whose outgoing profile `R̃ = r e^{−iΘ} R`
(`Θ' = K/Δ`) satisfies `R̃ = O(r⁻¹)` and `R̃' = O(r⁻²)`, i.e. the outgoing condition with
vanishing leading coefficient `B_I = 0`, vanishes identically
(`eqOn_zero_of_outgoing_coefficient_zero`).

## Proof

With `u = rR` the equation becomes `u'' + αu' + (Θ'² + γ)u = 0` with `α, γ = O(r⁻²)`
(`radial_core_identity`). The outgoing and ingoing amplitudes
`A = e^{−iΘ}(u' + iΘ'u)` and `B = e^{iΘ}(u' − iΘ'u)` satisfy
`A' = e^{−iΘ}(−αu' + (−γ + iΘ'')u)` and `B' = e^{iΘ}(−αu' + (−γ − iΘ'')u)`, and since
`u' = (e^{iΘ}A + e^{−iΘ}B)/2`, `u = (e^{iΘ}A − e^{−iΘ}B)/(2iΘ')`, with `Θ' → ω ≠ 0` and
`Θ'' = O(r⁻²)`, one gets `|A'|, |B'| ≤ C r⁻² (|A| + |B|)` for large `r`. The hypotheses give
`A = R̃' + 2iΘ'R̃ → 0` and `|B| = |R̃'| → 0`. The backward Grönwall argument from infinity
(`eq_zero_of_norm_deriv_le`) gives `A = B = 0` at a large `r₁`, so `R(r₁) = R'(r₁) = 0`, and
interior uniqueness (`ModeStability.ODE.eqOn_zero_of_linear_ode`) gives `R ≡ 0` on `r > a`.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

namespace InfinityUniqueness

/-! ### Algebra -/

/-- The equation for `u = rR`: with `R'' = (−(K²/Δ − L)R − Δ'R')/Δ`,
`u'' + Θ'²u = −αu' − γu`, where `u' = R + rR'`, `u'' = 2R' + rR''`. -/
theorem radial_core_identity {r M Q D K L : ℝ} (hr : r ≠ 0) (hD : D ≠ 0)
    (hrel : D = r ^ 2 - 2 * M * r + Q ^ 2) (R R1 : ℂ) :
    2 * R1 + (r : ℂ) * ((-((K : ℂ) ^ 2 / D - L) * R - (2 * r - 2 * M) * R1) / D) +
        ((K : ℂ) / D) ^ 2 * (r * R) +
      ((2 * M * r - 2 * Q ^ 2) / (r * D)) * (R + r * R1) +
      ((-2 * M * r + 2 * Q ^ 2 - L * r ^ 2) / (r ^ 2 * D)) * (r * R) = 0 := by
  have hQ2 : (Q : ℂ) ^ 2 = D - r ^ 2 + 2 * M * r := by
    have : Q ^ 2 = D - r ^ 2 + 2 * M * r := by linarith
    exact_mod_cast this
  have hrc : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr
  have hDc : (D : ℂ) ≠ 0 := ofReal_ne_zero.2 hD
  rw [hQ2]
  field_simp
  ring

/-- `‖e^{−ix}‖ = 1`. -/
theorem norm_exp_neg_I_mul (x : ℝ) : ‖exp (-(I * x))‖ = 1 := by
  rw [show -(I * (x : ℂ)) = ((-x : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

/-- `‖e^{ix}‖ = 1`. -/
theorem norm_exp_I_mul (x : ℝ) : ‖exp (I * x)‖ = 1 := by
  rw [mul_comm]
  exact norm_exp_ofReal_mul_I _

/-- `e^{−ix} e^{ix} = 1`. -/
theorem exp_neg_I_mul_mul_exp_I_mul (x : ℝ) : exp (-(I * x)) * exp (I * x) = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- The amplitude bound: with `A = E(u' + iθu)`, `B = E⁻¹(u' − iθu)`, `|E| = 1`,
`‖F(−αu' + ζu)‖ ≤ (|α|/2 + c/(2|θ|))(‖A‖ + ‖B‖)` whenever `|F| = 1`, `‖ζ‖ ≤ c`. -/
theorem norm_amp_deriv_le {E Ei F up uu ζ : ℂ} {θ α c : ℝ} (hE : ‖E‖ = 1) (hEi : ‖Ei‖ = 1)
    (hEEi : E * Ei = 1) (hF : ‖F‖ = 1) (hθ : θ ≠ 0) (hζ : ‖ζ‖ ≤ c) :
    ‖F * (-(α : ℂ) * up + ζ * uu)‖ ≤
      (|α| / 2 + c / (2 * |θ|)) * (‖E * (up + I * θ * uu)‖ + ‖Ei * (up - I * θ * uu)‖) := by
  set A := E * (up + I * θ * uu) with hA
  set B := Ei * (up - I * θ * uu) with hB
  have hθ0 : 0 < |θ| := abs_pos.2 hθ
  have hc : 0 ≤ c := (norm_nonneg _).trans hζ
  have h2up : (2 : ℂ) * up = Ei * A + E * B := by
    rw [hA, hB]
    linear_combination (-2 * up) * hEEi
  have h2uu : (2 * I * θ : ℂ) * uu = Ei * A - E * B := by
    rw [hA, hB]
    linear_combination (-2 * I * θ * uu) * hEEi
  have hup : ‖up‖ ≤ (‖A‖ + ‖B‖) / 2 := by
    have h := congrArg norm h2up
    rw [norm_mul, Complex.norm_two] at h
    have h' : ‖Ei * A + E * B‖ ≤ ‖A‖ + ‖B‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul Ei A, norm_mul E B, hE, hEi, one_mul, one_mul]
    linarith
  have huu : ‖uu‖ ≤ (‖A‖ + ‖B‖) / (2 * |θ|) := by
    have h := congrArg norm h2uu
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_two, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs] at h
    have h' : ‖Ei * A - E * B‖ ≤ ‖A‖ + ‖B‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul Ei A, norm_mul E B, hE, hEi, one_mul, one_mul]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hN : 0 ≤ ‖A‖ + ‖B‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ‖F * (-(α : ℂ) * up + ζ * uu)‖ = ‖-(α : ℂ) * up + ζ * uu‖ := by rw [norm_mul, hF, one_mul]
    _ ≤ |α| * ‖up‖ + c * ‖uu‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hζ (norm_nonneg _)
    _ ≤ |α| * ((‖A‖ + ‖B‖) / 2) + c * ((‖A‖ + ‖B‖) / (2 * |θ|)) :=
        add_le_add (mul_le_mul_of_nonneg_left hup (abs_nonneg _))
          (mul_le_mul_of_nonneg_left huu hc)
    _ = (|α| / 2 + c / (2 * |θ|)) * (‖A‖ + ‖B‖) := by ring

/-- If both amplitudes vanish, so do `u'` and `u`. -/
theorem eq_zero_of_amps_eq_zero {E Ei up uu : ℂ} {θ : ℝ} (hEEi : E * Ei = 1) (hθ : θ ≠ 0)
    (hA : E * (up + I * θ * uu) = 0) (hB : Ei * (up - I * θ * uu) = 0) : up = 0 ∧ uu = 0 := by
  have hE : E ≠ 0 := left_ne_zero_of_mul_eq_one hEEi
  have hEi : Ei ≠ 0 := right_ne_zero_of_mul_eq_one hEEi
  have h1 := (mul_eq_zero.1 hA).resolve_left hE
  have h2 := (mul_eq_zero.1 hB).resolve_left hEi
  have h3 : (2 * I * θ : ℂ) * uu = 0 := by linear_combination h1 - h2
  have h4 : (2 * I * θ : ℂ) ≠ 0 := by
    have : (θ : ℂ) ≠ 0 := ofReal_ne_zero.2 hθ
    simp [this, I_ne_zero]
  have huu : uu = 0 := (mul_eq_zero.1 h3).resolve_left h4
  refine ⟨?_, huu⟩
  rw [huu, mul_zero, add_zero] at h1
  exact h1

/-! ### The amplitudes and their derivatives -/

/-- The outgoing amplitude `A = e^{−iΘ}(u' + iΘ'u)`, `u = rR`, `u' = R + rR'`. -/
@[expose] noncomputable def outAmp (M Q e ω : ℝ) (Θ : ℝ → ℝ) (R : ℝ → ℂ) (r : ℝ) : ℂ :=
  exp (-(I * Θ r)) * ((R r + r * deriv R r) + I * phaseRate M Q e ω r * (r * R r))

/-- The ingoing amplitude `B = e^{iΘ}(u' − iΘ'u)`, `u = rR`, `u' = R + rR'`. -/
@[expose] noncomputable def inAmp (M Q e ω : ℝ) (Θ : ℝ → ℝ) (R : ℝ → ℂ) (r : ℝ) : ℂ :=
  exp (I * Θ r) * ((R r + r * deriv R r) - I * phaseRate M Q e ω r * (r * R r))

variable {M Q e ω L : ℝ} {Θ : ℝ → ℝ} {R : ℝ → ℂ}

/-- `(e^{−iΘ})' = e^{−iΘ}(−iΘ')`. -/
theorem hasDerivAt_exp_neg_phase {r : ℝ} (hΘ : HasDerivAt Θ (phaseRate M Q e ω r) r) :
    HasDerivAt (fun s => exp (-(I * Θ s))) (exp (-(I * Θ r)) * (-(I * phaseRate M Q e ω r))) r :=
  ((hΘ.ofReal_comp.const_mul I).neg).cexp

/-- `(e^{iΘ})' = e^{iΘ}(iΘ')`. -/
theorem hasDerivAt_exp_phase {r : ℝ} (hΘ : HasDerivAt Θ (phaseRate M Q e ω r) r) :
    HasDerivAt (fun s => exp (I * Θ s)) (exp (I * Θ r) * (I * phaseRate M Q e ω r)) r :=
  (hΘ.ofReal_comp.const_mul I).cexp

/-- `(s ↦ (s : ℂ))' = 1`. -/
theorem hasDerivAt_ofReal_id (r : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 r := by
  simpa using (hasDerivAt_id r).ofReal_comp

/-- `R'' = (P' − Δ'R')/Δ` from `(ΔR')' = P'`, where `Δ ≠ 0`. -/
theorem hasDerivAt_deriv_of_hasDerivAt_mul {r : ℝ} (hΔ : delta M Q r ≠ 0) {P' : ℂ}
    (hP : HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s) P' r) :
    HasDerivAt (deriv R) ((P' - (2 * r - 2 * M) * deriv R r) / delta M Q r) r := by
  have hd : HasDerivAt (fun s => (delta M Q s : ℂ)) ((2 * r - 2 * M : ℝ) : ℂ) r :=
    (hasDerivAt_delta M Q r).ofReal_comp
  have hΔc : (delta M Q r : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ
  have h := hP.div hd hΔc
  have hev : deriv R =ᶠ[𝓝 r]
      (fun s => (delta M Q s : ℂ) * deriv R s) / (fun s => (delta M Q s : ℂ)) := by
    filter_upwards [(continuous_delta M Q).continuousAt.eventually_ne hΔ] with s hs
    simp only [Pi.div_apply]
    rw [mul_div_cancel_left₀ _ (ofReal_ne_zero.2 hs)]
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  push_cast
  field_simp

/-- `‖−γ + iθ₂‖ ≤ |γ| + |θ₂|`. -/
theorem norm_neg_add_I_mul_le (γ θ₂ : ℝ) : ‖-(γ : ℂ) + I * θ₂‖ ≤ |γ| + |θ₂| := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

/-- `‖−γ − iθ₂‖ ≤ |γ| + |θ₂|`. -/
theorem norm_neg_sub_I_mul_le (γ θ₂ : ℝ) : ‖-(γ : ℂ) - I * θ₂‖ ≤ |γ| + |θ₂| := by
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

/-- The derivative of the outgoing amplitude: `A' = e^{−iΘ}(−αu' + (−γ + iΘ'')u)`. -/
theorem hasDerivAt_outAmp (hQ : |Q| ≤ M) {r : ℝ} (hr : outerHorizon M Q < r) (hr0 : 0 < r)
    (hΘ : HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : DifferentiableAt ℝ R r ∧ HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    HasDerivAt (outAmp M Q e ω Θ R)
      (exp (-(I * Θ r)) * (-(dampCoeff M Q r : ℂ) * (R r + r * deriv R r) +
        (-(potCoeff M Q L r : ℂ) + I * phaseAccel M Q e ω r) * (r * R r))) r := by
  have hΔ : delta M Q r ≠ 0 := (delta_pos_of_lt hr).ne'
  have hE := hasDerivAt_exp_neg_phase (M := M) (Q := Q) hΘ
  have hR1 : HasDerivAt R (deriv R r) r := hR.1.hasDerivAt
  have hR2 := hasDerivAt_deriv_of_hasDerivAt_mul hΔ hR.2
  have hid := hasDerivAt_ofReal_id r
  have hθ : HasDerivAt (fun s => (phaseRate M Q e ω s : ℂ)) (phaseAccel M Q e ω r : ℂ) r :=
    (hasDerivAt_phaseRate hΔ).ofReal_comp
  have h := hE.mul ((hR1.add (hid.mul hR2)).add ((hθ.const_mul I).mul (hid.mul hR1)))
  refine h.congr_deriv ?_
  have core := radial_core_identity (K := radialK e ω r) (L := L) hr0.ne' hΔ (delta_eq hQ r)
    (R r) (deriv R r)
  simp only [Pi.mul_apply, Pi.add_apply, phaseRate, dampCoeff, potCoeff]
  push_cast
  linear_combination exp (-(I * Θ r)) * core -
    exp (-(I * Θ r)) * ((radialK e ω r : ℂ) / delta M Q r) ^ 2 * (r * R r) * I_sq

/-- The derivative of the ingoing amplitude: `B' = e^{iΘ}(−αu' + (−γ − iΘ'')u)`. -/
theorem hasDerivAt_inAmp (hQ : |Q| ≤ M) {r : ℝ} (hr : outerHorizon M Q < r) (hr0 : 0 < r)
    (hΘ : HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : DifferentiableAt ℝ R r ∧ HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r) :
    HasDerivAt (inAmp M Q e ω Θ R)
      (exp (I * Θ r) * (-(dampCoeff M Q r : ℂ) * (R r + r * deriv R r) +
        (-(potCoeff M Q L r : ℂ) - I * phaseAccel M Q e ω r) * (r * R r))) r := by
  have hΔ : delta M Q r ≠ 0 := (delta_pos_of_lt hr).ne'
  have hE := hasDerivAt_exp_phase (M := M) (Q := Q) hΘ
  have hR1 : HasDerivAt R (deriv R r) r := hR.1.hasDerivAt
  have hR2 := hasDerivAt_deriv_of_hasDerivAt_mul hΔ hR.2
  have hid := hasDerivAt_ofReal_id r
  have hθ : HasDerivAt (fun s => (phaseRate M Q e ω s : ℂ)) (phaseAccel M Q e ω r : ℂ) r :=
    (hasDerivAt_phaseRate hΔ).ofReal_comp
  have h := hE.mul ((hR1.add (hid.mul hR2)).sub ((hθ.const_mul I).mul (hid.mul hR1)))
  refine h.congr_deriv ?_
  have core := radial_core_identity (K := radialK e ω r) (L := L) hr0.ne' hΔ (delta_eq hQ r)
    (R r) (deriv R r)
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, phaseRate, dampCoeff, potCoeff]
  push_cast
  linear_combination exp (I * Θ r) * core -
    exp (I * Θ r) * ((radialK e ω r : ℂ) / delta M Q r) ^ 2 * (r * R r) * I_sq

/-- The outgoing profile `R̃ = r e^{−iΘ}R` has derivative `R̃' = e^{−iΘ}(u' − iΘ'u)`. -/
theorem hasDerivAt_profile {r : ℝ} (hΘ : HasDerivAt Θ (phaseRate M Q e ω r) r)
    (hR : DifferentiableAt ℝ R r) :
    HasDerivAt (fun s : ℝ => (s : ℂ) * exp (-(I * Θ s)) * R s)
      (exp (-(I * Θ r)) * ((R r + r * deriv R r) - I * phaseRate M Q e ω r * (r * R r))) r := by
  have h := ((hasDerivAt_ofReal_id r).mul (hasDerivAt_exp_neg_phase hΘ)).mul hR.hasDerivAt
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

/-- Under the outgoing condition with vanishing leading coefficient, both amplitudes tend to `0`:
`A = R̃' + 2iΘ'R̃` and `|B| = |R̃'|`. -/
theorem tendsto_amps (hQ : |Q| ≤ M)
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r)
    (h1 : (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) =O[atTop] (fun r : ℝ => r⁻¹))
    (h2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹)) :
    Tendsto (outAmp M Q e ω Θ R) atTop (𝓝 0) ∧ Tendsto (inAmp M Q e ω Θ R) atTop (𝓝 0) := by
  have hP0 : Tendsto (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) atTop (𝓝 0) :=
    h1.trans_tendsto tendsto_inv_atTop_zero
  have hW0 : Tendsto (deriv (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r)) atTop (𝓝 0) :=
    h2.trans_tendsto (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero))
  have hderiv : ∀ r ∈ Ioi (outerHorizon M Q),
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) r =
        exp (-(I * Θ r)) * ((R r + r * deriv R r) - I * phaseRate M Q e ω r * (r * R r)) :=
    fun r hr => (hasDerivAt_profile (hΘ r hr) (hR r hr)).deriv
  have hθ : Tendsto (fun r => (phaseRate M Q e ω r : ℂ)) atTop (𝓝 (ω : ℂ)) :=
    (continuous_ofReal.tendsto ω).comp (tendsto_phaseRate hQ e ω)
  constructor
  · have h := hW0.add (((tendsto_const_nhds (x := 2 * I)).mul hθ).mul hP0)
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
    rw [hderiv r hr]
    simp only [outAmp]
    ring
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := hW0.norm
    rw [norm_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (outerHorizon M Q)] with r hr
    rw [hderiv r hr]
    simp only [inAmp, norm_mul, norm_exp_neg_I_mul, norm_exp_I_mul]

end InfinityUniqueness

open InfinityUniqueness in
/-- **Uniqueness at infinity.** A solution of the radial equation `(ΔR')' + (K²/Δ − L)R = 0` on
`r > a` (`|Q| ≤ M`, `ω ≠ 0`, `Θ' = K/Δ`) satisfying the outgoing condition with vanishing
leading coefficient, `R̃ = r e^{−iΘ}R = O(r⁻¹)` and `R̃' = O(r⁻²)`, vanishes identically.
(the all-angular research notes in preparation, p. 1; asserted there without proof.) -/
theorem eqOn_zero_of_outgoing_coefficient_zero {M Q e ω L : ℝ} (hM : 0 < M) (hQ : |Q| ≤ M)
    (hω : ω ≠ 0) {Θ : ℝ → ℝ}
    (hΘ : ∀ r ∈ Ioi (outerHorizon M Q), HasDerivAt Θ (radialK e ω r / delta M Q r) r)
    {R : ℝ → ℂ}
    (hR : ∀ r ∈ Ioi (outerHorizon M Q), DifferentiableAt ℝ R r ∧
      HasDerivAt (fun s => (delta M Q s : ℂ) * deriv R s)
        (-(((radialK e ω r) ^ 2 / delta M Q r - L : ℝ) : ℂ) * R r) r)
    (h1 : (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) =O[atTop] (fun r : ℝ => r⁻¹))
    (h2 : deriv (fun r : ℝ => (r : ℂ) * exp (-(I * Θ r)) * R r) =O[atTop]
      (fun r : ℝ => (r ^ 2)⁻¹)) :
    EqOn R 0 (Ioi (outerHorizon M Q)) := by
  have ha0 : 0 < outerHorizon M Q := outerHorizon_pos hM
  obtain ⟨hlo, hli⟩ := tendsto_amps hQ hΘ (fun r hr => (hR r hr).1) h1 h2
  obtain ⟨C, hC0, hCev⟩ := exists_errCoeff_le hQ e L hω
  have hθev : ∀ᶠ r in atTop, phaseRate M Q e ω r ≠ 0 := (tendsto_phaseRate hQ e ω).eventually_ne hω
  have hNev : ∀ᶠ r in atTop, ‖outAmp M Q e ω Θ R r‖ + ‖inAmp M Q e ω Θ R r‖ ≤ 1 := by
    have h := hlo.norm.add hli.norm
    rw [norm_zero, add_zero] at h
    exact h.eventually_le_const zero_lt_one
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1
    (hCev.and (hθev.and (hNev.and (eventually_gt_atTop (max (outerHorizon M Q) (4 * C))))))
  have hgood : ∀ t, s₀ ≤ t → outerHorizon M Q < t ∧ 0 < t ∧ 4 * C ≤ t := by
    intro t ht
    have h := (hs₀ t ht).2.2.2
    exact ⟨lt_of_le_of_lt (le_max_left _ _) h, ha0.trans (lt_of_le_of_lt (le_max_left _ _) h),
      ((le_max_right _ _).trans_lt h).le⟩
  -- the derivative bounds
  have hbound : ∀ t, s₀ ≤ t → ∀ F ζ : ℂ, ‖F‖ = 1 →
      ‖ζ‖ ≤ |potCoeff M Q L t| + |phaseAccel M Q e ω t| →
      ‖F * (-(dampCoeff M Q t : ℂ) * (R t + t * deriv R t) + ζ * (t * R t))‖ ≤
        C / t ^ 2 * (‖outAmp M Q e ω Θ R t‖ + ‖inAmp M Q e ω Θ R t‖) := by
    intro t ht F ζ hF hζ
    have h := norm_amp_deriv_le (norm_exp_neg_I_mul (Θ t)) (norm_exp_I_mul (Θ t))
      (exp_neg_I_mul_mul_exp_I_mul (Θ t)) hF (hs₀ t ht).2.1 hζ (α := dampCoeff M Q t)
      (up := R t + t * deriv R t) (uu := t * R t)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    exact (hs₀ t ht).1
  obtain ⟨hA, hB⟩ := eq_zero_of_norm_deriv_le (a₁ := outAmp M Q e ω Θ R)
    (a₂ := inAmp M Q e ω Θ R) (hgood s₀ le_rfl).2.1 hC0 (hgood s₀ le_rfl).2.2
    (fun t ht => hasDerivAt_outAmp hQ (hgood t ht).1 (hgood t ht).2.1 (hΘ t (hgood t ht).1)
      (hR t (hgood t ht).1))
    (fun t ht => hasDerivAt_inAmp hQ (hgood t ht).1 (hgood t ht).2.1 (hΘ t (hgood t ht).1)
      (hR t (hgood t ht).1))
    (fun t ht => hbound t ht _ _ (norm_exp_neg_I_mul (Θ t)) (norm_neg_add_I_mul_le _ _))
    (fun t ht => hbound t ht _ _ (norm_exp_I_mul (Θ t)) (norm_neg_sub_I_mul_le _ _))
    hlo hli (fun t ht => (hs₀ t ht).2.2.1)
  obtain ⟨hup, huu⟩ := eq_zero_of_amps_eq_zero (exp_neg_I_mul_mul_exp_I_mul (Θ s₀))
    (hs₀ s₀ le_rfl).2.1 hA hB
  have hs0 : (s₀ : ℂ) ≠ 0 := ofReal_ne_zero.2 (hgood s₀ le_rfl).2.1.ne'
  have hR0 : R s₀ = 0 := (mul_eq_zero.1 huu).resolve_left hs0
  have hR1 : deriv R s₀ = 0 := by
    rw [hR0, zero_add] at hup
    exact (mul_eq_zero.1 hup).resolve_left hs0
  have hp0 : ∀ r ∈ Ioi (outerHorizon M Q), 0 < delta M Q r := fun r hr => delta_pos_of_lt hr
  have hw : ContinuousOn (fun r => radialK e ω r ^ 2 / delta M Q r - L)
      (Ioi (outerHorizon M Q)) := by
    refine ContinuousOn.sub (ContinuousOn.div ?_ (continuous_delta M Q).continuousOn
      (fun r hr => (hp0 r hr).ne')) continuousOn_const
    unfold radialK
    fun_prop
  exact ModeStability.ODE.eqOn_zero_of_linear_ode (continuous_delta M Q).continuousOn hp0 hw hR
    (hgood s₀ le_rfl).1 hR0 hR1

end ModeStability.AllAngular

end
