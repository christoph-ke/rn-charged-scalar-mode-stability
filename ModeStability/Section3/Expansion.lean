module

public import Mathlib
public import ModeStability.Section3.Numerators

/-!
# Section 3: the representation of `k` and the expansion (3.4)

Calculus identities behind (3.2)–(3.4) of the spherical research notes in preparation.
The paper writes `f(t) = csch² t − ν(1 + coth t) − χ`. We use the equivalent form in the variable
`u = e^{2t}` (`csch² t = 4u/(u−1)²` and `1 + coth t = 2u/(u−1)` for `t > 0`), which keeps all
expressions rational in `u`. We record the derivatives `f'`, `f''`, the quantity
`𝓔 = 2f² + 2t f f' + t²(2f'² − f f'')` of (3.3), its exact expansion (3.4) as a polynomial in `ν`
and `χ` with explicit numerators, and the derivative formulas for `F = t² f`.
-/

@[expose] public section

namespace ModeStability.Section3

/-- `f(t) = csch² t − ν(1 + coth t) − χ` of (3.2), written with `u = e^{2t}`. -/
noncomputable def sec3f (ν χ t : ℝ) : ℝ :=
  4 * Real.exp (2 * t) / (Real.exp (2 * t) - 1) ^ 2 -
    ν * (2 * Real.exp (2 * t) / (Real.exp (2 * t) - 1)) - χ

/-- `f'(t)`. -/
noncomputable def sec3f1 (ν t : ℝ) : ℝ :=
  -(8 * Real.exp (2 * t) * (Real.exp (2 * t) + 1) / (Real.exp (2 * t) - 1) ^ 3) +
    ν * (4 * Real.exp (2 * t) / (Real.exp (2 * t) - 1) ^ 2)

/-- `f''(t)`. -/
noncomputable def sec3f2 (ν t : ℝ) : ℝ :=
  16 * Real.exp (2 * t) * (Real.exp (2 * t) ^ 2 + 4 * Real.exp (2 * t) + 1) /
      (Real.exp (2 * t) - 1) ^ 4 -
    ν * (8 * Real.exp (2 * t) * (Real.exp (2 * t) + 1) / (Real.exp (2 * t) - 1) ^ 3)

/-- `𝓔 = 2f² + 2t f f' + t²(2 f'² − f f'')` of (3.3). -/
noncomputable def sec3E (ν χ t : ℝ) : ℝ :=
  2 * sec3f ν χ t ^ 2 + 2 * t * sec3f ν χ t * sec3f1 ν t +
    t ^ 2 * (2 * sec3f1 ν t ^ 2 - sec3f ν χ t * sec3f2 ν t)

/-- For `t > 0` we have `e^{2t} − 1 ≠ 0`. -/
theorem exp_two_mul_sub_one_ne_zero {t : ℝ} (ht : 0 < t) : Real.exp (2 * t) - 1 ≠ 0 :=
  (sub_pos.mpr (one_lt_exp_two_mul ht)).ne'

/-- Derivative of `s ↦ e^{2s}`. -/
theorem hasDerivAt_exp_two_mul (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (2 * s)) (2 * Real.exp (2 * t)) t := by
  have h := ((hasDerivAt_id t).const_mul (2 : ℝ)).exp
  simpa [mul_comm] using h

theorem hasDerivAt_sec3f (ν χ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (sec3f ν χ) (sec3f1 ν t) t := by
  have hne := exp_two_mul_sub_one_ne_zero ht
  have hu := hasDerivAt_exp_two_mul t
  have hm : HasDerivAt (fun s : ℝ => Real.exp (2 * s) - 1) (2 * Real.exp (2 * t)) t := by
    simpa using hu.sub_const 1
  have h1 : HasDerivAt (fun s : ℝ => 4 * Real.exp (2 * s) / (Real.exp (2 * s) - 1) ^ 2)
      ((4 * (2 * Real.exp (2 * t)) * (Real.exp (2 * t) - 1) ^ 2 -
        4 * Real.exp (2 * t) * (2 * (Real.exp (2 * t) - 1) ^ (2 - 1) * (2 * Real.exp (2 * t)))) /
        ((Real.exp (2 * t) - 1) ^ 2) ^ 2) t :=
    (hu.const_mul 4).div (hm.pow 2) (pow_ne_zero 2 hne)
  have h2 : HasDerivAt (fun s : ℝ => 2 * Real.exp (2 * s) / (Real.exp (2 * s) - 1))
      ((2 * (2 * Real.exp (2 * t)) * (Real.exp (2 * t) - 1) -
        2 * Real.exp (2 * t) * (2 * Real.exp (2 * t))) / (Real.exp (2 * t) - 1) ^ 2) t :=
    (hu.const_mul 2).div hm hne
  have h := (h1.sub (h2.const_mul ν)).sub_const χ
  unfold sec3f sec3f1
  convert h using 1
  field_simp
  ring

theorem hasDerivAt_sec3f1 (ν : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (sec3f1 ν) (sec3f2 ν t) t := by
  have hne := exp_two_mul_sub_one_ne_zero ht
  have hu := hasDerivAt_exp_two_mul t
  have hm : HasDerivAt (fun s : ℝ => Real.exp (2 * s) - 1) (2 * Real.exp (2 * t)) t := by
    simpa using hu.sub_const 1
  have hp : HasDerivAt (fun s : ℝ => Real.exp (2 * s) + 1) (2 * Real.exp (2 * t)) t := by
    simpa using hu.add_const 1
  have h1 : HasDerivAt
      (fun s : ℝ => 8 * Real.exp (2 * s) * (Real.exp (2 * s) + 1) / (Real.exp (2 * s) - 1) ^ 3)
      ((((8 * (2 * Real.exp (2 * t))) * (Real.exp (2 * t) + 1) +
          8 * Real.exp (2 * t) * (2 * Real.exp (2 * t))) * (Real.exp (2 * t) - 1) ^ 3 -
        8 * Real.exp (2 * t) * (Real.exp (2 * t) + 1) *
          (3 * (Real.exp (2 * t) - 1) ^ (3 - 1) * (2 * Real.exp (2 * t)))) /
        ((Real.exp (2 * t) - 1) ^ 3) ^ 2) t :=
    (((hu.const_mul 8).mul hp).div (hm.pow 3) (pow_ne_zero 3 hne))
  have h2 : HasDerivAt (fun s : ℝ => 4 * Real.exp (2 * s) / (Real.exp (2 * s) - 1) ^ 2)
      ((4 * (2 * Real.exp (2 * t)) * (Real.exp (2 * t) - 1) ^ 2 -
        4 * Real.exp (2 * t) * (2 * (Real.exp (2 * t) - 1) ^ (2 - 1) * (2 * Real.exp (2 * t)))) /
        ((Real.exp (2 * t) - 1) ^ 2) ^ 2) t :=
    (hu.const_mul 4).div (hm.pow 2) (pow_ne_zero 2 hne)
  have h := h1.neg.add (h2.const_mul ν)
  unfold sec3f1 sec3f2
  convert h using 1
  field_simp
  ring

/-- The exact expansion (3.4). With `u = e^{2t}`, the numerators are
`A = u − 1 − 2t − 2t²`, `B = (u−1)² − t(u−1) − t²(u+1)`, `C = (t²+t−1)u + 2t² + 2t + 1`,
`D = (t²+t−1)u² + (4t²+2)u + t² − t − 1`, `H = (2t²−2t+1)u² − 2u + 2t² + 2t + 1`. -/
theorem sec3E_eq (ν χ : ℝ) {t : ℝ} (ht : 0 < t) :
    sec3E ν χ t =
      8 * Real.exp (2 * t) ^ 2 * (Real.exp (2 * t) - 1 - 2 * t - 2 * t ^ 2) /
        (Real.exp (2 * t) - 1) ^ 3 * ν ^ 2 +
      8 * Real.exp (2 * t) * ((Real.exp (2 * t) - 1) ^ 2 - t * (Real.exp (2 * t) - 1) -
        t ^ 2 * (Real.exp (2 * t) + 1)) / (Real.exp (2 * t) - 1) ^ 3 * (ν * χ) +
      32 * Real.exp (2 * t) ^ 2 * ((t ^ 2 + t - 1) * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1) /
        (Real.exp (2 * t) - 1) ^ 4 * ν +
      2 * χ ^ 2 +
      16 * Real.exp (2 * t) * ((t ^ 2 + t - 1) * Real.exp (2 * t) ^ 2 +
        (4 * t ^ 2 + 2) * Real.exp (2 * t) + t ^ 2 - t - 1) / (Real.exp (2 * t) - 1) ^ 4 * χ +
      32 * Real.exp (2 * t) ^ 2 * ((2 * t ^ 2 - 2 * t + 1) * Real.exp (2 * t) ^ 2 -
        2 * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1) / (Real.exp (2 * t) - 1) ^ 6 := by
  have hne := exp_two_mul_sub_one_ne_zero ht
  unfold sec3E sec3f sec3f1 sec3f2
  generalize Real.exp (2 * t) = u at hne ⊢
  field_simp
  ring

/-- `(t² f)' = 2t f + t² f'` in the sign-revealing form used for `k_x > 0`. -/
theorem two_mul_sec3f_add_eq (ν χ : ℝ) {t : ℝ} (ht : 0 < t) :
    2 * t * sec3f ν χ t + t ^ 2 * sec3f1 ν t =
      8 * t * Real.exp (2 * t) * ((Real.exp (2 * t) - 1) - t * (Real.exp (2 * t) + 1)) /
          (Real.exp (2 * t) - 1) ^ 3 -
        ν * (4 * t * Real.exp (2 * t) * ((Real.exp (2 * t) - 1) - t) /
          (Real.exp (2 * t) - 1) ^ 2) - 2 * χ * t := by
  have hne := exp_two_mul_sub_one_ne_zero ht
  unfold sec3f sec3f1
  generalize Real.exp (2 * t) = u at hne ⊢
  field_simp
  ring

/-- The algebra behind (3.3): with `F = t² f`, `F' = 2tf + t²f'`, `F'' = 2f + 4tf' + t²f''`,
`2t F'² − t F F'' − 2 F F' = t³ 𝓔`. -/
theorem sec3_chain_identity (f f1 f2 t : ℝ) :
    2 * t * (2 * t * f + t ^ 2 * f1) ^ 2 - t * (t ^ 2 * f) * (2 * f + 4 * t * f1 + t ^ 2 * f2) -
        2 * (t ^ 2 * f) * (2 * t * f + t ^ 2 * f1) =
      t ^ 3 * (2 * f ^ 2 + 2 * t * f * f1 + t ^ 2 * (2 * f1 ^ 2 - f * f2)) := by
  ring

/-- `F = t² f` has derivative `2 t f + t² f'` and second derivative `2f + 4tf' + t²f''`. -/
theorem hasDerivAt_sq_mul_sec3f (ν χ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => s ^ 2 * sec3f ν χ s) (2 * t * sec3f ν χ t + t ^ 2 * sec3f1 ν t) t := by
  have h := (hasDerivAt_pow 2 t).mul (hasDerivAt_sec3f ν χ ht)
  convert h using 1
  simp

theorem hasDerivAt_sq_mul_sec3f_deriv (ν χ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => 2 * s * sec3f ν χ s + s ^ 2 * sec3f1 ν s)
      (2 * sec3f ν χ t + 4 * t * sec3f1 ν t + t ^ 2 * sec3f2 ν t) t := by
  have h1 := ((hasDerivAt_id t).const_mul (2 : ℝ)).mul (hasDerivAt_sec3f ν χ ht)
  have h2 := (hasDerivAt_pow 2 t).mul (hasDerivAt_sec3f1 ν ht)
  refine (h1.add h2).congr_deriv ?_
  simp only [id, mul_one, Nat.cast_ofNat]
  ring

end ModeStability.Section3

end
