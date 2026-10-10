module

public import Mathlib
public import ModeStability.Frozen.ComplementaryBandExclusion
public import ModeStability.AllAngular.BandExclusionFinal

/-!
# Proof implementation

`ModeStability.Provider.AllAngular.ComplementaryBandExclusionHolds` supplies the proof of the
corresponding source-facing theorem in
`ModeStability.Frozen`. Author: Christoph Kehle.
-/

public section

namespace ModeStability.Provider.AllAngular

theorem complementaryBandExclusion_holds : ModeStability.ComplementaryBandExclusion :=
  ModeStability.AllAngular.complementaryBandExclusion_proved

end ModeStability.Provider.AllAngular

end
