module

public import Mathlib
public import ModeStability.AllAngular.BoundedLAux

/-!
# Abstract bounded-L resolvent estimate, Proposition 6.1

Source: the all-angular research notes in preparation (paper p. 8).
The larger coordinate interval is `[a,b]`, the source interval is `[i₁,i₂]`,
and the source-free allowed test interval is `[j₁,j₂]`. The signed effective
frequency on the latter is `k`. A fixed C¹ cutoff vanishing at both endpoints
suffices for (6.4); a smooth compactly supported cutoff is a special case.

The coefficient hypotheses are uniform constants `cStar, Γ, K₀, K₁, κ, L₀`.
`Z` denotes the phase-free derivative: `U_x ± i k̂ U` on the allowed pieces,
`U_x` on the forbidden piece. `γ` is extended by zero on the forbidden piece.
The local bulk coefficient `weight` is `a_k̂` on allowed pieces and `1` on
forbidden pieces. It is at least `min(cStar,1)` and the density
dominates this coefficient times `|Z|²`; its integral is bounded
by the global bulk `B`. The phase relations are supplied as their pointwise
norm identities/inequality, so the theorem does not depend on a choice of
primitive for `W = sqrt(max(k² - V,0))`. The ODE and source identity are
explicit hypotheses; (6.4), the supremum estimate, all local energy estimates,
and absorption are proved, rather than assumed.

The constants in `boundedLConstant` depend only on the displayed uniform
bounds, interval length, and the fixed cutoff, and not on `L` or the solution.
Concrete coefficient compactness and the phase construction are separate
application obligations.
-/

public section

open Set MeasureTheory Complex

namespace ModeStability.AllAngular

end ModeStability.AllAngular

end
