module

public import Mathlib
public import ModeStability.Frozen.ComplementaryBandExclusion
public import ModeStability.Provider.AllAngular.ComplementaryBandExclusionHolds

/-!
# `ModeStability.AllAngular.complementaryBandExclusion_holds`

All-angular research notes in preparation, p. 2, Theorem 1.1, case L = 0, e = qQ, |Q| < M, ω >
0, 2Mω − e ≥ 0 (bridge corollary), stated in the encodings of the spherical research notes, pp.
1–2 (Section 1) and Appendix A.
Author: Christoph Kehle. This source-facing declaration has been reviewed and proved
using the accompanying provider.
-/

public section

open Complex Set Filter Asymptotics Topology

namespace ModeStability.AllAngular

/-- The `L = 0`, `e = qQ`, subextremal case of Theorem 1.1, in the encodings of the spherical
paper: it discharges the trust boundary `ComplementaryBandExclusion` of the spherical Theorem 1.1. -/
theorem complementaryBandExclusion_holds : ModeStability.ComplementaryBandExclusion :=
  by exact ModeStability.Provider.AllAngular.complementaryBandExclusion_holds

end ModeStability.AllAngular

end
