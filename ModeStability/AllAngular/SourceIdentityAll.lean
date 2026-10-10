module

public import Mathlib
public import ModeStability.AllAngular.Prop61Interface
public import ModeStability.AllAngular.SourceIdentitySubReciprocal
public import ModeStability.AllAngular.SourceIdentitySubConstant
public import ModeStability.AllAngular.SourceIdentityExtReciprocal
public import ModeStability.AllAngular.SourceIdentityExtConstant

/-!
# The source identity in all four coordinate systems

Source: the all-angular research notes in preparation, all-angular paper
p. 8, Proposition 6.1, (6.3). The subextremal and extremal identities in the
constant and reciprocal normalizations cover the full range (1.7).
-/

public section

namespace ModeStability.AllAngular

/-- Identity (6.3), including finiteness of the bulk, throughout the range (1.7). -/
theorem sourceIdentityAll_holds : P61.SourceIdentityAll := by
  intro M Q e ω ρ₁ ρ₂ L hrange hL S R BH BI hproblem
  rcases lt_or_eq_of_le hrange.2.1 with hQ | hQ
  · rcases lt_or_ge (e / ω) (2 * M) with hnormalization | hnormalization
    · exact sourceIdentity_subConstant M Q e ω ρ₁ ρ₂ L hrange
        ⟨hQ, hnormalization⟩ hL S R BH BI hproblem
    · exact sourceIdentity_subReciprocal M Q e ω ρ₁ ρ₂ L hrange
        ⟨hQ, hnormalization⟩ hL S R BH BI hproblem
  · rcases lt_or_ge (e / ω) (2 * M) with hnormalization | hnormalization
    · exact sourceIdentity_extConstant M Q e ω ρ₁ ρ₂ L hrange
        ⟨hQ, hnormalization⟩ hL S R BH BI hproblem
    · exact sourceIdentity_extReciprocal M Q e ω ρ₁ ρ₂ L hrange
        ⟨hQ, hnormalization⟩ hL S R BH BI hproblem

end ModeStability.AllAngular

end
