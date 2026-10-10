# Source gaps resolved during formalization

This file records missing arguments and ambiguities encountered in Christoph
Kehle's research notes in preparation dated 8 October 2026 (spherical) and
9 October 2026 (all-angular). It describes the adopted mathematical readings
and their Lean resolutions. It does not reproduce the notes. Unless a scope
restriction is explicitly stated below, the resolutions are proved rather than
assumed. Lean names have the prefix `ModeStability.`.

## Spherical notes

| Gap or ambiguity | Resolution |
|---|---|
| A nonzero solution was asserted to have nonzero leading coefficients at both endpoints, without the singular-endpoint uniqueness arguments. | Proposition 2.3 is proved using current monotonicity, endpoint limits, current rigidity, and interior ODE uniqueness, without a nonzero-coefficient hypothesis. The all-angular development also proves zero-coefficient uniqueness at infinity when `ω≠0` and at the horizon when `K(a)≠0`; see `AllAngular.eqOn_zero_of_outgoing_coefficient_zero` and `AllAngular.eqOn_zero_of_horizon_coefficient_zero`. Synchronization is handled separately by the flux and current arguments. |
| The differentiated endpoint expansions allowed different interpretations. | The adopted predicates include an explicit complex leading coefficient and bound the derivative of the remainder after removal of the oscillation. At the horizon the bounds are `O(r-a)` and `O(1)`; at infinity they are `O(1/r)` and `O(r⁻²)`. This stronger, literal reading is needed for the logarithmic factor in the horizon current limit. See `HorizonCondition` and `InfinityCondition`. |
| The endpoint flux values in (1.5) were stated without derivation. | `flux_identity` and the proofs in `Flux/Basic.lean` derive both limits from the differentiated endpoint conditions. |
| Smoothness of the transformed coefficient, endpoint asymptotics of the coefficient and its derivatives and derivative ratio, and convergence of the bulk integrals were used without full proofs. | `coefficient_inequalities` and the `Endpoint` modules prove the coefficient and endpoint facts. The `Corotation` modules assemble `separation_at_corotation` using monotonicity, endpoint limits, current rigidity, and interior ODE uniqueness. This proof avoids the notes' improper-integral argument; no improper-integrability theorem for those bulk integrals is claimed. |
| The algebraic identity (3.4) and power-series expansions (3.6) were not derived. | The `Section3` modules prove the polynomial identity (3.4). They prove the positivity needed for the coefficient inequalities by repeated differentiation and algebra, without formalizing the power-series identity (3.6). |
| Appendix A outlined a transform without establishing the regularized oscillatory integrals, special-function asymptotics, and endpoint smoothness needed for it. | That transform is not formalized. Its intended exclusion conclusion is proved by `AllAngular.complementaryBandExclusion_holds`, which discharges the explicit premise of the original spherical theorem. `AllAngular.spherical_real_mode_exclusion_unconditional` gives the resulting theorem without that premise. |

## All-angular notes

| Gap or ambiguity | Resolution |
|---|---|
| Nonvanishing of an endpoint leading coefficient for a nonzero solution was asserted without proof. | `AllAngular.eqOn_zero_of_outgoing_coefficient_zero` proves uniqueness at infinity when `ω≠0`. `AllAngular.eqOn_zero_of_horizon_coefficient_zero` proves uniqueness at the horizon when `K(a)≠0`, including subextremal and extremal backgrounds. These results do not assert coefficient uniqueness at synchronization: the extremal synchronized condition is boundedness and does not use the horizon coefficient. Separate flux and current arguments cover synchronization in the exclusion theorem. |
| Zero flux for a bounded solution at the extremal synchronized horizon was attributed to an unstated Frobenius argument. | `AllAngular/FluxL.lean` proves the vanishing horizon flux directly from the radial equation and boundedness, without Frobenius theory. |
| The phase was introduced away from synchronization but also used at synchronization. | The same interval-integral phase `AllAngular.radialPhase` is used throughout the exterior. The author adopted this interpretation; the subextremal synchronized horizon flux is proved to vanish under it. |
| The extremal boundedness requirement did not identify the frequencies to which it applied. | The author restricted that branch to `K(a)=0`, as encoded in `AllAngular.HorizonConditionL`. Away from synchronization, including zero frequency with nonzero charge coefficient, boundedness alone would not justify Proposition 7.1. The differentiated ingoing condition is retained there. |
| Existence of the normalized horizon solution at an extremal, irregular singular endpoint was not established. | `AllAngular.horizon_solution_existsUnique` and the `AllAngular/HorizonSolution` modules establish existence and uniqueness when `K(a)≠0`, for both subextremal and extremal backgrounds. |
| Proposition 7.1 did not explain how finite weighted energy implies the required horizon behavior. | The author omitted that implication from the formalized result. `AllAngular.zero_frequency_exclusion` proves the square-integrable version with the horizon condition stated explicitly. The weighted-energy extension remains outside the formalization. |
| Endpoint asymptotics and the estimates (4.5) and (4.6) were used without complete derivations. | The endpoint, coordinate, and superradiant modules prove the needed asymptotics and estimates. Where appropriate, asymptotic assertions are expressed as filter limits rather than full series expansions. These proofs feed `AllAngular.real_mode_exclusion`. |

## Results outside the release

Corollary 8.1 is not proved here. Its external analytic input needs clarification,
and its compact-parameter argument requires continuity in background parameters.
The proved solution-continuity anchors give joint continuity in frequency and
radius with the background parameters fixed. No corollary draft is distributed.

The all-angular appendix has not been formalized because none of the listed
anchors requires it. The spherical extremal low-frequency conclusion is already
covered by `AllAngular.real_mode_exclusion` at `L=0` and `|Q|=M`; there is no
separate theorem in the spherical encoding for that case.
