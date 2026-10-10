module

public import Mathlib
public import ModeStability.AllAngular.InfinitySolutionSystem

/-!
# The outgoing solution at infinity: asymptotics of the profile

Part of the construction of the outgoing solution `R_I` of
the all-angular research notes in preparation, (1.5), normalized with leading coefficient `1`
(Sections 6 and 8). Let `(A, B)` solve the amplitude system of
`ModeStability.AllAngular.InfinitySolutionAux` on `(r₁, ∞)` with `A → 2iω` and `B → 0`, and
let `R = u/r` be the solution of the radial equation of
`ModeStability.AllAngular.InfinitySolutionSystem`.
Then the outgoing profile `R̃ = r e^{−iΘ}R = (A − e^{−2iΘ}B)/(2iΘ')` satisfies
`R̃ − 1 = O(r⁻¹)` and `R̃' = e^{−2iΘ}B = O(r⁻²)` (`outgoing_ampSol`).

## Proof

Since all coefficients are `O(r⁻²)`, `A' , B' = O(r⁻²)`, and the tail estimate gives
`A − 2iω, B = O(r⁻¹)` (`amp_tail_bounds`). For `B = O(r⁻²)` the oscillation of the coefficient
`e^{2iΘ}(ρ₋ + iσ)` of `A` in `B'` is used: `ρ₋ + iσ = 2iκΘ'/r² + O(r⁻³)` with
`κ = −(e + iL)/(4iω²)`, and `(e^{2iΘ})' = 2iΘ'e^{2iΘ}`, so the corrected amplitude
`B − κe^{2iΘ}A/r²` has derivative `O(r⁻³)` and tends to `0`; the cubic tail estimate gives
`B = O(r⁻²)` (`norm_inAmp_le_sq`).
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

namespace InfinitySolution

open InfinityUniqueness

variable {M Q e ω L : ℝ} {Θ : ℝ → ℝ} {A B : ℝ → ℂ}

/-- `‖ax + by‖ ≤ E(‖x‖ + ‖y‖)` for `‖a‖, ‖b‖ ≤ E`. -/
theorem norm_mul_add_mul_le {a b x y : ℂ} {E : ℝ} (ha : ‖a‖ ≤ E) (hb : ‖b‖ ≤ E) :
    ‖a * x + b * y‖ ≤ E * (‖x‖ + ‖y‖) := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- First-order tail bounds: `A', B' = O(r⁻²)`, `A − Ainf = O(r⁻¹)` and `B = O(r⁻¹)`. -/
theorem amp_tail_bounds {s₀ C N : ℝ} {Ainf : ℂ} (hs₀ : 0 < s₀)
    (hA : ∀ t, s₀ ≤ t →
      HasDerivAt A (ampCoeffAA M Q e ω L t * A t + ampCoeffAB M Q e ω L Θ t * B t) t)
    (hB : ∀ t, s₀ ≤ t →
      HasDerivAt B (ampCoeffBA M Q e ω L Θ t * A t + ampCoeffBB M Q e ω L t * B t) t)
    (herr : ∀ t, s₀ ≤ t → errCoeff M Q e ω L t ≤ C / t ^ 2)
    (hN : ∀ t, s₀ ≤ t → ‖A t‖ + ‖B t‖ ≤ N)
    (hlA : Tendsto A atTop (𝓝 Ainf)) (hlB : Tendsto B atTop (𝓝 0)) :
    (∀ t, s₀ ≤ t →
      ‖ampCoeffAA M Q e ω L t * A t + ampCoeffAB M Q e ω L Θ t * B t‖ ≤ C * N / t ^ 2) ∧
    (∀ t, s₀ ≤ t →
      ‖ampCoeffBA M Q e ω L Θ t * A t + ampCoeffBB M Q e ω L t * B t‖ ≤ C * N / t ^ 2) ∧
    (∀ t, s₀ ≤ t → ‖A t - Ainf‖ ≤ C * N / t) ∧ (∀ t, s₀ ≤ t → ‖B t‖ ≤ C * N / t) := by
  have key : ∀ t, s₀ ≤ t → ∀ a b : ℂ, ‖a‖ ≤ errCoeff M Q e ω L t →
      ‖b‖ ≤ errCoeff M Q e ω L t → ‖a * A t + b * B t‖ ≤ C * N / t ^ 2 := by
    intro t ht a b ha hb
    have hE0 : 0 ≤ errCoeff M Q e ω L t := (norm_nonneg _).trans ha
    calc ‖a * A t + b * B t‖ ≤ errCoeff M Q e ω L t * (‖A t‖ + ‖B t‖) :=
          norm_mul_add_mul_le ha hb
      _ ≤ C / t ^ 2 * N :=
          mul_le_mul (herr t ht) (hN t ht) (add_nonneg (norm_nonneg _) (norm_nonneg _))
            (hE0.trans (herr t ht))
      _ = C * N / t ^ 2 := by ring
  have hdA : ∀ t, s₀ ≤ t →
      ‖ampCoeffAA M Q e ω L t * A t + ampCoeffAB M Q e ω L Θ t * B t‖ ≤ C * N / t ^ 2 :=
    fun t ht => key t ht _ _ (norm_ampCoeffAA_le M Q e ω L t) (norm_ampCoeffAB_le M Q e ω L Θ t)
  have hdB : ∀ t, s₀ ≤ t →
      ‖ampCoeffBA M Q e ω L Θ t * A t + ampCoeffBB M Q e ω L t * B t‖ ≤ C * N / t ^ 2 :=
    fun t ht => key t ht _ _ (norm_ampCoeffBA_le M Q e ω L Θ t) (norm_ampCoeffBB_le M Q e ω L t)
  refine ⟨hdA, hdB, fun t ht => ?_, fun t ht => ?_⟩
  · have hlim : Tendsto (fun x => A x - Ainf) atTop (𝓝 0) := by
      simpa using hlA.sub_const Ainf
    exact norm_le_of_tendsto_zero_of_norm_deriv_le (hs₀.trans_le ht)
      (fun x hx => (hA x (ht.trans hx)).sub_const Ainf) (fun x hx => hdA x (ht.trans hx)) hlim
  · exact norm_le_of_tendsto_zero_of_norm_deriv_le (hs₀.trans_le ht)
      (fun x hx => hB x (ht.trans hx)) (fun x hx => hdB x (ht.trans hx)) hlB

/-- The constant `κ = −(e + iL)/(4iω²)`, written as `(c_σ − i c_ρ)/2` with `c_ρ = −e/(2ω²)`,
`c_σ = −L/(2ω²)`, so that `2iκ = c_ρ + i c_σ`. -/
@[expose] noncomputable def ampKappa (e ω L : ℝ) : ℂ :=
  (((-L / (2 * ω ^ 2) : ℝ) : ℂ) - I * ((-e / (2 * ω ^ 2) : ℝ) : ℂ)) / 2

/-- The derivative of the corrected amplitude `B − κe^{2iΘ}A/r²`. -/
theorem hasDerivAt_corrected {t : ℝ} {A' : ℂ} (ht : t ≠ 0)
    (hΘ : HasDerivAt Θ (phaseRate M Q e ω t) t) (hA : HasDerivAt A A' t)
    (hB : HasDerivAt B (ampCoeffBA M Q e ω L Θ t * A t + ampCoeffBB M Q e ω L t * B t) t) :
    HasDerivAt (fun s => B s - ampKappa e ω L * (exp (I * Θ s) ^ 2 * A s / (s : ℂ) ^ 2))
      (exp (I * Θ t) ^ 2 * A t * (((ampRhoM M Q e ω t -
          (-e / (2 * ω ^ 2)) * phaseRate M Q e ω t / t ^ 2 : ℝ) : ℂ) +
          I * ((ampSigma M Q e ω L t - (-L / (2 * ω ^ 2)) * phaseRate M Q e ω t / t ^ 2 : ℝ) : ℂ)) +
        ampCoeffBB M Q e ω L t * B t - ampKappa e ω L * exp (I * Θ t) ^ 2 * A' / (t : ℂ) ^ 2 +
        2 * ampKappa e ω L * exp (I * Θ t) ^ 2 * A t / (t : ℂ) ^ 3) t := by
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  have hE := (hasDerivAt_exp_phase (M := M) (Q := Q) hΘ).fun_pow 2
  have hq := ((hE.mul hA).div ((hasDerivAt_ofReal_id t).fun_pow 2) (pow_ne_zero 2 htc)).const_mul
    (ampKappa e ω L)
  refine (hB.sub hq).congr_deriv ?_
  simp only [Pi.mul_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
  unfold ampCoeffBA ampKappa
  push_cast
  generalize exp (I * Θ t) = E
  generalize (phaseRate M Q e ω t : ℂ) = θ
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- `‖e^{2iΘ}‖ = 1`. -/
theorem norm_exp_I_mul_sq (x : ℝ) : ‖exp (I * x) ^ 2‖ = 1 := by
  rw [norm_pow, norm_exp_I_mul, one_pow]

/-- **`B = O(r⁻²)`.** Under first-order bounds `‖A‖ ≤ N`, `‖B‖ ≤ C_B/t`, `‖A'‖ ≤ C_A/t²`,
`‖ρ₊ − iσ‖ ≤ C/t²` and the rates `|ρ₋ − c_ρΘ'/t²| ≤ c_ρ'/t³`, `|σ − c_σΘ'/t²| ≤ c_σ'/t³`
on `[s₀, ∞)`, `s₀ ≥ 1`, and `B → 0`, the ingoing amplitude is `O(t⁻²)`. -/
theorem norm_inAmp_le_sq {s₀ C N CB CA cρ cσ : ℝ} {A' : ℝ → ℂ} (hs₀ : 1 ≤ s₀)
    (hΘ : ∀ t, s₀ ≤ t → HasDerivAt Θ (phaseRate M Q e ω t) t)
    (hA : ∀ t, s₀ ≤ t → HasDerivAt A (A' t) t)
    (hB : ∀ t, s₀ ≤ t →
      HasDerivAt B (ampCoeffBA M Q e ω L Θ t * A t + ampCoeffBB M Q e ω L t * B t) t)
    (hAN : ∀ t, s₀ ≤ t → ‖A t‖ ≤ N) (hBb : ∀ t, s₀ ≤ t → ‖B t‖ ≤ CB / t)
    (hA'b : ∀ t, s₀ ≤ t → ‖A' t‖ ≤ CA / t ^ 2)
    (hbb : ∀ t, s₀ ≤ t → ‖ampCoeffBB M Q e ω L t‖ ≤ C / t ^ 2)
    (hρ : ∀ t, s₀ ≤ t →
      |ampRhoM M Q e ω t - (-e / (2 * ω ^ 2)) * phaseRate M Q e ω t / t ^ 2| ≤ cρ / t ^ 3)
    (hσ : ∀ t, s₀ ≤ t →
      |ampSigma M Q e ω L t - (-L / (2 * ω ^ 2)) * phaseRate M Q e ω t / t ^ 2| ≤ cσ / t ^ 3)
    (hlB : Tendsto B atTop (𝓝 0)) :
    ∀ t, s₀ ≤ t → ‖B t‖ ≤
      (N * (cρ + cσ) + C * CB + ‖ampKappa e ω L‖ * CA + 2 * ‖ampKappa e ω L‖ * N) /
          (2 * t ^ 2) + ‖ampKappa e ω L‖ * N / t ^ 2 := by
  set κ := ampKappa e ω L with hκ
  set D := N * (cρ + cσ) + C * CB + ‖κ‖ * CA + 2 * ‖κ‖ * N with hD
  have hpos : ∀ t, s₀ ≤ t → 0 < t := fun t ht => zero_lt_one.trans_le (hs₀.trans ht)
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hAN s₀ le_rfl)
  -- the correction term
  have hcorr : ∀ t, s₀ ≤ t → ‖κ * (exp (I * Θ t) ^ 2 * A t / (t : ℂ) ^ 2)‖ ≤ ‖κ‖ * N / t ^ 2 := by
    intro t ht
    have ht0 := hpos t ht
    rw [norm_mul, norm_div, norm_mul, norm_exp_I_mul_sq, one_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht0, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hAN t ht) (by positivity))
      (norm_nonneg _)
  -- the derivative bound for the corrected amplitude
  have hderiv : ∀ t, s₀ ≤ t →
      ‖exp (I * Θ t) ^ 2 * A t * (((ampRhoM M Q e ω t -
          (-e / (2 * ω ^ 2)) * phaseRate M Q e ω t / t ^ 2 : ℝ) : ℂ) +
          I * ((ampSigma M Q e ω L t - (-L / (2 * ω ^ 2)) * phaseRate M Q e ω t / t ^ 2 : ℝ) : ℂ)) +
        ampCoeffBB M Q e ω L t * B t - κ * exp (I * Θ t) ^ 2 * A' t / (t : ℂ) ^ 2 +
        2 * κ * exp (I * Θ t) ^ 2 * A t / (t : ℂ) ^ 3‖ ≤ D / t ^ 3 := by
    intro t ht
    have ht0 := hpos t ht
    have ht1 : 1 ≤ t := hs₀.trans ht
    have hnt : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have h1 : ‖exp (I * Θ t) ^ 2 * A t * (((ampRhoM M Q e ω t -
          (-e / (2 * ω ^ 2)) * phaseRate M Q e ω t / t ^ 2 : ℝ) : ℂ) +
          I * ((ampSigma M Q e ω L t - (-L / (2 * ω ^ 2)) * phaseRate M Q e ω t / t ^ 2 : ℝ) :
            ℂ))‖ ≤ N * (cρ + cσ) / t ^ 3 := by
      rw [norm_mul, norm_mul, norm_exp_I_mul_sq, one_mul]
      calc _ ≤ N * ((cρ + cσ) / t ^ 3) := by
            refine mul_le_mul (hAN t ht) ((norm_ofReal_add_I_mul_le _ _).trans ?_)
              (norm_nonneg _) hN0
            rw [add_div]
            exact add_le_add (hρ t ht) (hσ t ht)
        _ = N * (cρ + cσ) / t ^ 3 := by ring
    have h2 : ‖ampCoeffBB M Q e ω L t * B t‖ ≤ C * CB / t ^ 3 := by
      rw [norm_mul]
      have hC : 0 ≤ C / t ^ 2 := (norm_nonneg _).trans (hbb t ht)
      calc ‖ampCoeffBB M Q e ω L t‖ * ‖B t‖ ≤ C / t ^ 2 * (CB / t) :=
            mul_le_mul (hbb t ht) (hBb t ht) (norm_nonneg _) hC
        _ = C * CB / t ^ 3 := by field_simp
    have h3 : ‖κ * exp (I * Θ t) ^ 2 * A' t / (t : ℂ) ^ 2‖ ≤ ‖κ‖ * CA / t ^ 3 := by
      rw [norm_div, norm_mul, norm_mul, norm_exp_I_mul_sq, mul_one, norm_pow, hnt]
      have hCA : 0 ≤ CA := by
        have := (norm_nonneg _).trans (hA'b t ht)
        rwa [le_div_iff₀ (by positivity), zero_mul] at this
      calc ‖κ‖ * ‖A' t‖ / t ^ 2 ≤ ‖κ‖ * (CA / t ^ 2) / t ^ 2 := by
            gcongr
            exact hA'b t ht
        _ = ‖κ‖ * CA / t ^ 3 / t := by field_simp
        _ ≤ ‖κ‖ * CA / t ^ 3 := div_le_self (by positivity) ht1
    have h4 : ‖2 * κ * exp (I * Θ t) ^ 2 * A t / (t : ℂ) ^ 3‖ ≤ 2 * ‖κ‖ * N / t ^ 3 := by
      rw [norm_div, norm_mul, norm_mul, norm_mul, norm_exp_I_mul_sq, mul_one, norm_pow, hnt,
        Complex.norm_two]
      gcongr
      exact hAN t ht
    calc _ ≤ ‖exp (I * Θ t) ^ 2 * A t * (((ampRhoM M Q e ω t -
          (-e / (2 * ω ^ 2)) * phaseRate M Q e ω t / t ^ 2 : ℝ) : ℂ) +
          I * ((ampSigma M Q e ω L t - (-L / (2 * ω ^ 2)) * phaseRate M Q e ω t / t ^ 2 : ℝ) :
            ℂ))‖ + ‖ampCoeffBB M Q e ω L t * B t‖ +
          ‖κ * exp (I * Θ t) ^ 2 * A' t / (t : ℂ) ^ 2‖ +
          ‖2 * κ * exp (I * Θ t) ^ 2 * A t / (t : ℂ) ^ 3‖ :=
          (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ N * (cρ + cσ) / t ^ 3 + C * CB / t ^ 3 + ‖κ‖ * CA / t ^ 3 + 2 * ‖κ‖ * N / t ^ 3 := by
          gcongr
      _ = D / t ^ 3 := by rw [hD]; ring
  -- the corrected amplitude tends to zero
  have hlim : Tendsto (fun s => B s - κ * (exp (I * Θ s) ^ 2 * A s / (s : ℂ) ^ 2)) atTop
      (𝓝 0) := by
    have hc : Tendsto (fun s => κ * (exp (I * Θ s) ^ 2 * A s / (s : ℂ) ^ 2)) atTop (𝓝 0) := by
      have hg : Tendsto (fun s : ℝ => ‖κ‖ * N / s ^ 2) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)).const_mul (‖κ‖ * N)
      refine squeeze_zero_norm' ?_ hg
      filter_upwards [eventually_ge_atTop s₀] with s hs
      exact hcorr s hs
    simpa using hlB.sub hc
  intro t ht
  have hc := norm_le_of_tendsto_zero_of_norm_deriv_le_cube (hpos t ht)
    (fun x hx => hasDerivAt_corrected (hpos x (ht.trans hx)).ne' (hΘ x (ht.trans hx))
      (hA x (ht.trans hx)) (hB x (ht.trans hx)))
    (fun x hx => hderiv x (ht.trans hx)) hlim
  calc ‖B t‖ = ‖(B t - κ * (exp (I * Θ t) ^ 2 * A t / (t : ℂ) ^ 2)) +
        κ * (exp (I * Θ t) ^ 2 * A t / (t : ℂ) ^ 2)‖ := by rw [sub_add_cancel]
    _ ≤ D / (2 * t ^ 2) + ‖κ‖ * N / t ^ 2 := (norm_add_le _ _).trans (add_le_add hc (hcorr t ht))

/-- `|t²x − y| ≤ c t⁻¹` gives `|x − y/t²| ≤ c/t³` for `t > 0`. -/
theorem abs_sub_div_sq_le {x y c t : ℝ} (ht : 0 < t) (h : ‖t ^ 2 * x - y‖ ≤ c * ‖t⁻¹‖) :
    |x - y / t ^ 2| ≤ c / t ^ 3 := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos ht] at h
  have ht2 : 0 < t ^ 2 := by positivity
  have he : x - y / t ^ 2 = (t ^ 2 * x - y) / t ^ 2 := by field_simp
  rw [he, abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
  calc |t ^ 2 * x - y| ≤ c * t⁻¹ := h
    _ = c / t ^ 3 * t ^ 2 := by field_simp

/-- **Outgoing asymptotics of `R = u/r`.** If `(A, B)` solves the amplitude system on `(r₁, ∞)`
(`r₁ ≥ a`, `Θ' ≠ 0` there) with `A → 2iω` and `B → 0`, then the outgoing profile
`R̃ = r e^{−iΘ}R` of `R = u/r` satisfies `R̃ − 1 = O(r⁻¹)` and `R̃' = O(r⁻²)`. -/
theorem outgoing_ampSol (hQ : |Q| ≤ M) (hω : ω ≠ 0) {r₁ : ℝ} (ha : outerHorizon M Q ≤ r₁)
    (hθ : ∀ t ∈ Ioi r₁, phaseRate M Q e ω t ≠ 0)
    (hΘ : ∀ t ∈ Ioi r₁, HasDerivAt Θ (radialK e ω t / delta M Q t) t)
    (hA : ∀ t ∈ Ioi r₁,
      HasDerivAt A (ampCoeffAA M Q e ω L t * A t + ampCoeffAB M Q e ω L Θ t * B t) t)
    (hB : ∀ t ∈ Ioi r₁,
      HasDerivAt B (ampCoeffBA M Q e ω L Θ t * A t + ampCoeffBB M Q e ω L t * B t) t)
    (hlA : Tendsto A atTop (𝓝 (2 * I * ω))) (hlB : Tendsto B atTop (𝓝 0)) :
    (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * ampSol M Q e ω Θ A B r - 1)
        =O[atTop] (fun r : ℝ => r⁻¹) ∧
      deriv (fun r : ℝ => (r : ℂ) * exp (-(I * (Θ r : ℂ))) * ampSol M Q e ω Θ A B r)
        =O[atTop] (fun r : ℝ => (r ^ 2)⁻¹) := by
  obtain ⟨C, -, hCev⟩ := exists_errCoeff_le hQ e L hω
  obtain ⟨cθ, hcθ⟩ := (isBigO_phaseRate_sub hQ e hω).bound
  obtain ⟨cρ, hcρ⟩ := (isBigO_ampRhoM_sub hQ e hω).bound
  obtain ⟨cσ, hcσ⟩ := (isBigO_ampSigma_sub hQ e L hω).bound
  set N : ℝ := ‖2 * I * (ω : ℂ)‖ + 1 with hNdef
  have hNev : ∀ᶠ t in atTop, ‖A t‖ + ‖B t‖ ≤ N := by
    have h := hlA.norm.add hlB.norm
    rw [norm_zero, add_zero] at h
    exact (h.eventually_le_const (lt_add_one _))
  have hω2 : |ω| / 2 < |ω| := half_lt_self (abs_pos.2 hω)
  have hθev : ∀ᶠ t in atTop, |ω| / 2 < |phaseRate M Q e ω t| :=
    (tendsto_phaseRate hQ e ω).abs.eventually_const_lt hω2
  obtain ⟨s₀, hs₀⟩ := eventually_atTop.1 (hCev.and (hcθ.and (hcρ.and (hcσ.and
    (hNev.and (hθev.and (eventually_gt_atTop (max r₁ 1))))))))
  have hgood : ∀ t, s₀ ≤ t → t ∈ Ioi r₁ ∧ 1 < t := fun t ht =>
    ⟨(le_max_left _ _).trans_lt (hs₀ t ht).2.2.2.2.2.2,
      (le_max_right _ _).trans_lt (hs₀ t ht).2.2.2.2.2.2⟩
  have hpos : ∀ t, s₀ ≤ t → 0 < t := fun t ht => zero_lt_one.trans (hgood t ht).2
  have hs1 : 1 ≤ s₀ := (hgood s₀ le_rfl).2.le
  obtain ⟨hdA, -, hAt, hBt⟩ := amp_tail_bounds (Ainf := 2 * I * ω) (hpos s₀ le_rfl)
    (fun t ht => hA t (hgood t ht).1) (fun t ht => hB t (hgood t ht).1)
    (fun t ht => (hs₀ t ht).1) (fun t ht => (hs₀ t ht).2.2.2.2.1) hlA hlB
  have hBsq := norm_inAmp_le_sq (C := C) (N := N) (CB := C * N) (CA := C * N) (cρ := cρ)
    (cσ := cσ) hs1 (fun t ht => hΘ t (hgood t ht).1) (fun t ht => hA t (hgood t ht).1)
    (fun t ht => hB t (hgood t ht).1)
    (fun t ht => le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hs₀ t ht).2.2.2.2.1) hBt hdA
    (fun t ht => (norm_ampCoeffBB_le M Q e ω L t).trans (hs₀ t ht).1)
    (fun t ht => abs_sub_div_sq_le (hpos t ht) (hs₀ t ht).2.2.1)
    (fun t ht => abs_sub_div_sq_le (hpos t ht) (hs₀ t ht).2.2.2.1) hlB
  set κn : ℝ := ‖ampKappa e ω L‖
  set D : ℝ := N * (cρ + cσ) + C * (C * N) + κn * (C * N) + 2 * κn * N
  have hu : ∀ t ∈ Ioi r₁, HasDerivAt (ampU M Q e ω Θ A B) (ampV Θ A B t) t := fun t ht =>
    hasDerivAt_ampU (delta_pos_of_lt (ha.trans_lt ht)).ne' (hθ t ht) (hΘ t ht) (hA t ht) (hB t ht)
  constructor
  · refine IsBigO.of_bound ((2 * (C * N) + 2 * cθ) / |ω|) ?_
    filter_upwards [eventually_ge_atTop s₀] with t ht
    have ht0 := hpos t ht
    have htr := (hgood t ht).1
    have hθt := (hs₀ t ht).2.2.2.2.2.1
    have hθ0 : 0 < |phaseRate M Q e ω t| := (half_pos (abs_pos.2 hω)).trans hθt
    rw [profile_ampSol ht0.ne', Real.norm_eq_abs, abs_inv, abs_of_pos ht0]
    have hden : (2 * I * (phaseRate M Q e ω t : ℂ)) ≠ 0 := two_I_mul_ne_zero (hθ t htr)
    have hnd : ‖2 * I * (phaseRate M Q e ω t : ℂ)‖ = 2 * |phaseRate M Q e ω t| := by
      rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
    have hsplit : (A t - exp (-(I * (Θ t : ℂ))) ^ 2 * B t) / (2 * I * phaseRate M Q e ω t) - 1 =
        ((A t - 2 * I * ω) + 2 * I * ((ω : ℂ) - phaseRate M Q e ω t) -
          exp (-(I * (Θ t : ℂ))) ^ 2 * B t) / (2 * I * phaseRate M Q e ω t) := by
      rw [div_sub_one hden]
      congr 1
      ring
    have hθω : ‖2 * I * ((ω : ℂ) - phaseRate M Q e ω t)‖ ≤ 2 * cθ / t := by
      have h := (hs₀ t ht).2.1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos ht0] at h
      rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_I, mul_one, ← ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      calc 2 * |phaseRate M Q e ω t - ω| ≤ 2 * (cθ * t⁻¹) := by gcongr
        _ = 2 * cθ / t := by ring
    have hnum : ‖(A t - 2 * I * ω) + 2 * I * ((ω : ℂ) - phaseRate M Q e ω t) -
        exp (-(I * (Θ t : ℂ))) ^ 2 * B t‖ ≤ (2 * (C * N) + 2 * cθ) / t := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_pow, norm_exp_neg_I_mul, one_pow, one_mul]
      calc _ ≤ C * N / t + 2 * cθ / t + C * N / t :=
            add_le_add ((norm_add_le _ _).trans (add_le_add (hAt t ht) hθω)) (hBt t ht)
        _ = (2 * (C * N) + 2 * cθ) / t := by ring
    rw [hsplit, norm_div, hnd, div_le_iff₀ (by positivity)]
    have hK0 : 0 ≤ (2 * (C * N) + 2 * cθ) / t := (norm_nonneg _).trans hnum
    calc _ ≤ (2 * (C * N) + 2 * cθ) / t := hnum
      _ ≤ (2 * (C * N) + 2 * cθ) / t * (|phaseRate M Q e ω t| * 2 / |ω|) := by
          refine le_mul_of_one_le_right hK0 ?_
          rw [le_div_iff₀ (abs_pos.2 hω)]
          linarith
      _ = (2 * (C * N) + 2 * cθ) / |ω| * t⁻¹ * (2 * |phaseRate M Q e ω t|) := by
          field_simp
  · refine IsBigO.of_bound (D / 2 + κn * N) ?_
    filter_upwards [eventually_ge_atTop s₀] with t ht
    have ht0 := hpos t ht
    have htr := (hgood t ht).1
    rw [(hasDerivAt_profile_ampSol ht0.ne' (hΘ t htr) (hθ t htr) (hu t htr)).deriv, norm_mul,
      norm_pow, norm_exp_neg_I_mul, one_pow, one_mul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (by positivity)]
    calc ‖B t‖ ≤ D / (2 * t ^ 2) + κn * N / t ^ 2 := hBsq t ht
      _ = (D / 2 + κn * N) * (t ^ 2)⁻¹ := by field_simp

end InfinitySolution

end ModeStability.AllAngular

end
