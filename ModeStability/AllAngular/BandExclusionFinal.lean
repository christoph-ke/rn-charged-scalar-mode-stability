module

public import Mathlib
public import ModeStability.Frozen.ComplementaryBandExclusion
public import ModeStability.AllAngular.BandExclusion
public import ModeStability.AllAngular.InfinityUniqueness
public import ModeStability.AllAngular.ConstantEndpoints
public import ModeStability.AllAngular.InterfaceEndpoint

/-!
# The complementary-band exclusion, proved

Source: the all-angular research notes in preparation, pp. 1–6, for `L = 0`, applied to the
trust boundary `ModeStability.ComplementaryBandExclusion` of
the spherical research notes in preparation (Section 1, Appendix A).

`complementaryBandExclusion_proved` instantiates the conditional assembly
`complementaryBandExclusion_of_parts` with the four landed parts: uniqueness at infinity
(`eqOn_zero_of_outgoing_coefficient_zero`), the horizon and infinity limits of the current in the
constant normalization (`constant_horizon_current_tendsto`, `constant_infinity_current_tendsto`),
and the infinity limit at the interface `r₀ = 2M` (`interface_infinity_current_tendsto`).
-/

public section

namespace ModeStability.AllAngular

/-- **The complementary-band exclusion** (`ModeStability.ComplementaryBandExclusion`): for
`0 < M`, `|Q| < M`, `ω > 0` and `2Mω − e ≥ 0`, every solution of (1.2) with (1.3) and (1.4)
vanishes on the exterior. -/
theorem complementaryBandExclusion_proved : ModeStability.ComplementaryBandExclusion :=
  complementaryBandExclusion_of_parts eqOn_zero_of_outgoing_coefficient_zero
    constant_horizon_current_tendsto constant_infinity_current_tendsto
    interface_infinity_current_tendsto

end ModeStability.AllAngular

end
