module

public import Mathlib

/-!
# `ModeStability.dephasedCurrent`

Spherical research notes in preparation, p. 2, (2.6).
Author: Christoph Kehle. This source-facing definition has been reviewed.
-/

@[expose] public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability

/-- The current `J[v] = −(k/k_x)|v_x|² − Re(v_x v̄)` of (2.6). -/
noncomputable def dephasedCurrent (k : ℝ → ℝ) (v : ℝ → ℂ) (x : ℝ) : ℝ :=
  -(k x / deriv k x) * ‖deriv v x‖ ^ 2 - (deriv v x * (starRingEnd ℂ) (v x)).re

end ModeStability

end
