module

public import Mathlib

/-!
# Section 3: positivity of the numerators (3.5)

With `u = e^{2t}`, the five numerators `A, B, C, D, H` of (3.5) of the source paper
(the spherical research notes in preparation, Section 3) are strictly positive for `t > 0`.
We also record `u - 1 < t (u + 1)` (that is, `t coth t > 1`) and `u - 1 - t > 0`.

The proofs are by repeated differentiation. Each numerator vanishes at `t = 0` together with
enough derivatives, and a higher derivative is manifestly positive on `t > 0`. The basic tool is
`pos_of_hasDerivAt`: if `f 0 ≥ 0` and `f' > 0` on `(0, ∞)`, then `f > 0` on `(0, ∞)`.
-/

@[expose] public section

namespace ModeStability.Section3

open Real

/-- `A(t) = u − 1 − 2t − 2t²` with `u = e^{2t}`, (3.5). -/
noncomputable def numA (t : ℝ) : ℝ := Real.exp (2 * t) - 1 - 2 * t - 2 * t ^ 2
/-- `B(t) = (u − 1)² − t(u − 1) − t²(u + 1)`, (3.5). -/
noncomputable def numB (t : ℝ) : ℝ :=
  (Real.exp (2 * t) - 1) ^ 2 - t * (Real.exp (2 * t) - 1) - t ^ 2 * (Real.exp (2 * t) + 1)
/-- `C(t) = (t² + t − 1)u + 2t² + 2t + 1`, (3.5). -/
noncomputable def numC (t : ℝ) : ℝ := (t ^ 2 + t - 1) * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1
/-- `D(t) = (t² + t − 1)u² + (4t² + 2)u + t² − t − 1`, (3.5). -/
noncomputable def numD (t : ℝ) : ℝ :=
  (t ^ 2 + t - 1) * Real.exp (2 * t) ^ 2 + (4 * t ^ 2 + 2) * Real.exp (2 * t) + t ^ 2 - t - 1
/-- `H(t) = (2t² − 2t + 1)u² − 2u + 2t² + 2t + 1`, (3.5). -/
noncomputable def numH (t : ℝ) : ℝ :=
  (2 * t ^ 2 - 2 * t + 1) * Real.exp (2 * t) ^ 2 - 2 * Real.exp (2 * t) + 2 * t ^ 2 + 2 * t + 1

/-! ### The monotonicity tool -/

/-- If `f' = (f)'` everywhere, `f 0 ≥ 0` and `f' > 0` on `t > 0`, then `f > 0` on `t > 0`. -/
theorem pos_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) (h0 : 0 ≤ f 0)
    (h : ∀ t, 0 < t → 0 < f' t) {t : ℝ} (ht : 0 < t) : 0 < f t := by
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · exact fun x _ => (hf x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hf x).deriv]
      exact h x hx
  exact lt_of_le_of_lt h0 (hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht.le) ht)

/-- Package for computing a derivative via `deriv`. -/
theorem hasDerivAt_of_deriv_eq {f : ℝ → ℝ} {f' t : ℝ} (hd : DifferentiableAt ℝ f t)
    (h : deriv f t = f') : HasDerivAt f f' t :=
  h ▸ hd.hasDerivAt

/-! ### Elementary facts on `u = e^{2t}` -/

theorem one_add_two_mul_add_two_mul_sq_le_exp {t : ℝ} (ht : 0 ≤ t) :
    1 + 2 * t + 2 * t ^ 2 ≤ Real.exp (2 * t) := by
  have := Real.quadratic_le_exp_of_nonneg (x := 2 * t) (by linarith)
  nlinarith

theorem one_lt_exp_two_mul {t : ℝ} (ht : 0 < t) : 1 < Real.exp (2 * t) :=
  Real.one_lt_exp_iff.2 (by linarith)

/-- `u - 1 - t > 0`. -/
theorem exp_two_mul_sub_one_sub_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp (2 * t) - 1 - t := by
  have := Real.add_one_lt_exp (x := 2 * t) (by linarith)
  linarith

/-! ### `A` -/

/-- Derivative of `numA`. -/
noncomputable def numA₁ (t : ℝ) : ℝ := 2 * Real.exp (2 * t) - 2 - 4 * t
/-- Second derivative of `numA`. -/
noncomputable def numA₂ (t : ℝ) : ℝ := 4 * Real.exp (2 * t) - 4

theorem hasDerivAt_numA (t : ℝ) : HasDerivAt numA (numA₁ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numA; fun_prop) ?_
  unfold numA numA₁
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_numA₁ (t : ℝ) : HasDerivAt numA₁ (numA₂ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numA₁; fun_prop) ?_
  unfold numA₁ numA₂
  simp (disch := fun_prop)
  ring

theorem numA_pos {t : ℝ} (ht : 0 < t) : 0 < numA t := by
  refine pos_of_hasDerivAt hasDerivAt_numA (by norm_num [numA]) ?_ ht
  refine fun s hs => pos_of_hasDerivAt hasDerivAt_numA₁ (by norm_num [numA₁]) ?_ hs
  intro r hr
  have := one_lt_exp_two_mul hr
  unfold numA₂
  linarith

/-! ### `B` -/

/-- Derivative of `numB`. -/
noncomputable def numB₁ (t : ℝ) : ℝ :=
  4 * Real.exp (2 * t) ^ 2 - (5 + 4 * t + 2 * t ^ 2) * Real.exp (2 * t) + 1 - 2 * t
/-- Second derivative of `numB`. -/
noncomputable def numB₂ (t : ℝ) : ℝ :=
  16 * Real.exp (2 * t) ^ 2 - (14 + 12 * t + 4 * t ^ 2) * Real.exp (2 * t) - 2
/-- Third derivative of `numB`. -/
noncomputable def numB₃ (t : ℝ) : ℝ :=
  Real.exp (2 * t) * (64 * Real.exp (2 * t) - 40 - 32 * t - 8 * t ^ 2)

theorem hasDerivAt_numB (t : ℝ) : HasDerivAt numB (numB₁ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numB; fun_prop) ?_
  unfold numB numB₁
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_numB₁ (t : ℝ) : HasDerivAt numB₁ (numB₂ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numB₁; fun_prop) ?_
  unfold numB₁ numB₂
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_numB₂ (t : ℝ) : HasDerivAt numB₂ (numB₃ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numB₂; fun_prop) ?_
  unfold numB₂ numB₃
  simp (disch := fun_prop)
  ring

theorem numB_pos {t : ℝ} (ht : 0 < t) : 0 < numB t := by
  refine pos_of_hasDerivAt hasDerivAt_numB (by norm_num [numB]) ?_ ht
  refine fun s hs => pos_of_hasDerivAt hasDerivAt_numB₁ (by norm_num [numB₁]) ?_ hs
  refine fun r hr => pos_of_hasDerivAt hasDerivAt_numB₂ (by norm_num [numB₂]) ?_ hr
  intro q hq
  have h1 := one_add_two_mul_add_two_mul_sq_le_exp hq.le
  unfold numB₃
  have : 0 < 64 * Real.exp (2 * q) - 40 - 32 * q - 8 * q ^ 2 := by nlinarith
  positivity

/-! ### `C` -/

/-- Derivative of `numC`. -/
noncomputable def numC₁ (t : ℝ) : ℝ := (2 * t ^ 2 + 4 * t - 1) * Real.exp (2 * t) + 4 * t + 2
/-- Second derivative of `numC`. -/
noncomputable def numC₂ (t : ℝ) : ℝ := (4 * t ^ 2 + 12 * t + 2) * Real.exp (2 * t) + 4

theorem hasDerivAt_numC (t : ℝ) : HasDerivAt numC (numC₁ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numC; fun_prop) ?_
  unfold numC numC₁
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_numC₁ (t : ℝ) : HasDerivAt numC₁ (numC₂ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numC₁; fun_prop) ?_
  unfold numC₁ numC₂
  simp (disch := fun_prop)
  ring

theorem numC_pos {t : ℝ} (ht : 0 < t) : 0 < numC t := by
  refine pos_of_hasDerivAt hasDerivAt_numC (by norm_num [numC]) ?_ ht
  refine fun s hs => pos_of_hasDerivAt hasDerivAt_numC₁ (by norm_num [numC₁]) ?_ hs
  intro r hr
  unfold numC₂
  positivity

/-! ### `D` -/

/-- Derivative of `numD`. -/
noncomputable def numD₁ (t : ℝ) : ℝ :=
  (4 * t ^ 2 + 6 * t - 3) * Real.exp (2 * t) ^ 2 + (8 * t ^ 2 + 8 * t + 4) * Real.exp (2 * t)
    + 2 * t - 1
/-- Second derivative of `numD`. -/
noncomputable def numD₂ (t : ℝ) : ℝ :=
  (16 * t ^ 2 + 32 * t - 6) * Real.exp (2 * t) ^ 2
    + (16 * t ^ 2 + 32 * t + 16) * Real.exp (2 * t) + 2
/-- Third derivative of `numD`. -/
noncomputable def numD₃ (t : ℝ) : ℝ :=
  (64 * t ^ 2 + 160 * t + 8) * Real.exp (2 * t) ^ 2
    + (32 * t ^ 2 + 96 * t + 64) * Real.exp (2 * t)

theorem hasDerivAt_numD (t : ℝ) : HasDerivAt numD (numD₁ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numD; fun_prop) ?_
  unfold numD numD₁
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_numD₁ (t : ℝ) : HasDerivAt numD₁ (numD₂ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numD₁; fun_prop) ?_
  unfold numD₁ numD₂
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_numD₂ (t : ℝ) : HasDerivAt numD₂ (numD₃ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numD₂; fun_prop) ?_
  unfold numD₂ numD₃
  simp (disch := fun_prop)
  ring

theorem numD_pos {t : ℝ} (ht : 0 < t) : 0 < numD t := by
  refine pos_of_hasDerivAt hasDerivAt_numD (by norm_num [numD]) ?_ ht
  refine fun s hs => pos_of_hasDerivAt hasDerivAt_numD₁ (by norm_num [numD₁]) ?_ hs
  refine fun r hr => pos_of_hasDerivAt hasDerivAt_numD₂ (by norm_num [numD₂]) ?_ hr
  intro q hq
  unfold numD₃
  positivity

/-! ### `H` -/

/-- Derivative of `numH`. -/
noncomputable def numH₁ (t : ℝ) : ℝ :=
  (8 * t ^ 2 - 4 * t + 2) * Real.exp (2 * t) ^ 2 - 4 * Real.exp (2 * t) + 4 * t + 2
/-- Second derivative of `numH`. -/
noncomputable def numH₂ (t : ℝ) : ℝ :=
  (32 * t ^ 2 + 4) * Real.exp (2 * t) ^ 2 - 8 * Real.exp (2 * t) + 4
/-- Third derivative of `numH`. -/
noncomputable def numH₃ (t : ℝ) : ℝ :=
  16 * Real.exp (2 * t) * ((8 * t ^ 2 + 4 * t + 1) * Real.exp (2 * t) - 1)

theorem hasDerivAt_numH (t : ℝ) : HasDerivAt numH (numH₁ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numH; fun_prop) ?_
  unfold numH numH₁
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_numH₁ (t : ℝ) : HasDerivAt numH₁ (numH₂ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numH₁; fun_prop) ?_
  unfold numH₁ numH₂
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_numH₂ (t : ℝ) : HasDerivAt numH₂ (numH₃ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold numH₂; fun_prop) ?_
  unfold numH₂ numH₃
  simp (disch := fun_prop)
  ring

theorem numH_pos {t : ℝ} (ht : 0 < t) : 0 < numH t := by
  refine pos_of_hasDerivAt hasDerivAt_numH (by norm_num [numH]) ?_ ht
  refine fun s hs => pos_of_hasDerivAt hasDerivAt_numH₁ (by norm_num [numH₁]) ?_ hs
  refine fun r hr => pos_of_hasDerivAt hasDerivAt_numH₂ (by norm_num [numH₂]) ?_ hr
  intro q hq
  have h1 := one_lt_exp_two_mul hq
  have : 0 < (8 * q ^ 2 + 4 * q + 1) * Real.exp (2 * q) - 1 := by nlinarith [sq_nonneg q]
  unfold numH₃
  positivity

/-! ### `t coth t > 1` -/

/-- Auxiliary function `g(t) = t (u + 1) - (u - 1)`. -/
noncomputable def cothAux (t : ℝ) : ℝ := t * (Real.exp (2 * t) + 1) - (Real.exp (2 * t) - 1)
/-- Derivative of `cothAux`. -/
noncomputable def cothAux₁ (t : ℝ) : ℝ := (2 * t - 1) * Real.exp (2 * t) + 1
/-- Second derivative of `cothAux`. -/
noncomputable def cothAux₂ (t : ℝ) : ℝ := 4 * t * Real.exp (2 * t)

theorem hasDerivAt_cothAux (t : ℝ) : HasDerivAt cothAux (cothAux₁ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold cothAux; fun_prop) ?_
  unfold cothAux cothAux₁
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_cothAux₁ (t : ℝ) : HasDerivAt cothAux₁ (cothAux₂ t) t := by
  refine hasDerivAt_of_deriv_eq (by unfold cothAux₁; fun_prop) ?_
  unfold cothAux₁ cothAux₂
  simp (disch := fun_prop)
  ring

/-- `t coth t > 1`, in the form `u − 1 < t (u + 1)`. -/
theorem exp_two_mul_sub_one_lt {t : ℝ} (ht : 0 < t) :
    Real.exp (2 * t) - 1 < t * (Real.exp (2 * t) + 1) := by
  have h : 0 < cothAux t := by
    refine pos_of_hasDerivAt hasDerivAt_cothAux (by norm_num [cothAux]) ?_ ht
    refine fun s hs => pos_of_hasDerivAt hasDerivAt_cothAux₁ (by norm_num [cothAux₁]) ?_ hs
    intro r hr
    unfold cothAux₂
    positivity
  unfold cothAux at h
  linarith

end ModeStability.Section3

end
