# Charged scalar mode stability on Reissner–Nordström

A Lean 4 formalization by Christoph Kehle of radial real-frequency mode exclusion
for the massless charged scalar equation on Reissner–Nordström. It covers the
spherical problem on subextremal exteriors and the all-angular problem on both
subextremal and extremal exteriors.

The mathematical sources are Christoph Kehle's **research notes in preparation**,
dated 8 October 2026 (spherical) and 9 October 2026 (all-angular). The original
spherical notes were prompted by Ryan Unger. The notes are unpublished and are
not distributed here. The result numbers below refer to
those two sets of notes. [SOURCE_GAPS.md](SOURCE_GAPS.md) describes the missing
arguments and ambiguities resolved during formalization.

## Results and Lean declarations

All 20 theorem anchors below are proved. Their statements are in
[`ModeStability/Frozen/`](ModeStability/Frozen); the implementation is in the
remaining library modules. Every declaration in this table has the prefix
`ModeStability.`; `AllAngular.` identifies the all-angular namespace.

| Notes | Result | Lean declaration after `ModeStability.` |
|---|---|---|
| Spherical | Inverse radial coordinate, (2.2), (2.11) | `radiusOf_spec` |
| Spherical | Lemma 2.1: transformed equation (2.3) | `exact_reduction` |
| Spherical | Lemma 2.1: coefficient inequalities (2.4), Section 3 | `coefficient_inequalities` |
| Spherical | Lemma 2.2: dephased current | `dephased_current` |
| Spherical | Proposition 2.3: separation at corotation | `separation_at_corotation` |
| Spherical | Flux identity (1.5) | `flux_identity` |
| Spherical | Theorem 1.1, with the explicit complementary-band premise | `spherical_real_mode_exclusion` |
| Bridge | Proof of that complementary-band premise | `AllAngular.complementaryBandExclusion_holds` |
| Bridge | Spherical Theorem 1.1 with the premise discharged | `AllAngular.spherical_real_mode_exclusion_unconditional` |
| All-angular | Theorem 1.1: real-frequency mode exclusion | `AllAngular.real_mode_exclusion` |
| All-angular | Lemma 2.1: common geometry | `AllAngular.common_geometry` |
| All-angular | Lemma 2.2: scalar positivity | `AllAngular.scalar_positivity` |
| All-angular | Proposition 3.1: angular positivity | `AllAngular.angular_positivity` |
| All-angular | Proposition 6.1: normalized horizon solution, existence and uniqueness | `AllAngular.horizon_solution_existsUnique` |
| All-angular | Proposition 6.1: normalized infinity solution, existence and uniqueness | `AllAngular.infinity_solution_existsUnique` |
| All-angular | Proposition 6.1: joint frequency/radius continuity at the horizon | `AllAngular.horizon_solution_continuous` |
| All-angular | Proposition 6.1: joint frequency/radius continuity at infinity | `AllAngular.infinity_solution_continuous` |
| All-angular | Proposition 6.1: sourced radial solution, existence and uniqueness | `AllAngular.source_solution_existsUnique` |
| All-angular | Proposition 6.1: inhomogeneous estimate (6.2), uniform in angular momentum | `AllAngular.inhomogeneous_estimate` |
| All-angular | Proposition 7.1: zero-frequency exclusion in the square-integrable class | `AllAngular.zero_frequency_exclusion` |

The all-angular exclusion theorem assumes real parameters with $M \gt 0$,
$|Q| \le M$, $L \ge 0$, and $\omega \ne 0$, and proves that a radial solution
satisfying the future-horizon and outgoing-infinity conditions vanishes on the
exterior. The parameter $e$ is an independent real coefficient; the charged
scalar specialization is $e=qQ$. Allowing every real $L \ge 0$ includes the
physical angular eigenvalues $L=\ell(\ell+1)$.

The original spherical theorem uses $|Q| \lt M$ and retains
`ComplementaryBandExclusion` as an explicit premise in its statement. The bridge
theorems prove this proposition and give the unconditional spherical result.
There is no remaining unproved input, custom axiom, `sorry`, or draft theorem.
The audit checks the transitive axiom dependencies of every theorem in the table;
only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

## Radial equation and endpoint conditions

Write $a=M+\sqrt{M^2-Q^2}$, $b=M-\sqrt{M^2-Q^2}$,
$\Delta(r)=r^2-2Mr+Q^2$, and $K(r)=\omega r^2-er$. The exterior is $(a,\infty)$.
`AllAngular.IsRadialSolutionL` encodes the complex-valued equation

$$
(\Delta R')'+(K^2/\Delta-L)R=0.
$$

It requires differentiability of $R$ at every exterior point and gives the
derivative of $\Delta R'$ with `HasDerivAt`. The spherical predicate
`IsRadialSolution` is the $L=0$, $e=qQ$ equation. The sourced equation
`AllAngular.IsRadialSolutionWithSourceL` uses differentiability and an interval
integral identity for $(\Delta R')'+(K^2/\Delta-L)R=S$, so an $L^2$ source need
not be pointwise continuous.

The all-angular phase is the real interval integral

$$
\Theta(r)=\int_{a+1}^{r} K(\rho)/\Delta(\rho)\,d\rho.
$$

`AllAngular.HorizonConditionL` requires
$e^{i\Theta}R-B_H=O(r-a)$ and $(e^{i\Theta}R)'=O(1)$ as $r$ tends to $a$ from
above. At the **extremal synchronized horizon** ($a=b$ and $K(a)=0$), the
condition instead requires boundedness of $R$; the coefficient $B_H$ is unused
in this branch. At a subextremal synchronized horizon the same phase is used,
and the differentiated condition specifies the regular branch.

`AllAngular.InfinityConditionL` requires
$r e^{-i\Theta}R-B_I=O(r^{-1})$ and $(r e^{-i\Theta}R)'=O(r^{-2})$ as
$r\to\infty$. Big-O statements use Mathlib's asymptotic filters, and both
endpoint coefficients are explicit complex numbers. No nonzero-coefficient
hypothesis is imposed on the mode-exclusion theorems.

The spherical endpoint predicates use the explicit horizon factor
$(r-a)^{iK(a)/(a-b)}$ and infinity factor
$r e^{-i\omega r}r^{-i(2M\omega-qQ)}$ to remove the oscillation, with the same
remainder and derivative bounds. The bridge proofs relate these predicates to
the integral-phase formulation.

## Scope

Proposition 6.1 gives normalized horizon solutions when $K(a)\ne0$ and normalized
infinity solutions when $\omega\ne0$, including extremal backgrounds. Uniqueness
is stated for functions on the exterior, allowing arbitrary extensions outside
it. Continuity is joint in $(\omega,r)$ for fixed $(M,Q,e,L)$, on the respective
non-synchronized or nonzero-frequency domains. The sourced solution and the
estimate are proved for $e \gt 0$, $0 \lt \omega \lt e/a$ and compactly supported
$L^2$ sources in an exterior interval. The estimate's constant is chosen before
$L$, so it is uniform in $L \ge 0$.

Proposition 7.1 assumes the horizon condition and
$\int_a^{\infty} |R|^2\,dr \lt \infty$. The additional weighted-energy clause of the
notes is omitted because the implied horizon conditions were not specified.
The boundedness branch at an extremal horizon applies only at synchronization;
boundedness alone is insufficient away from synchronization.

Corollary 8.1 is not formalized: its external analytic input and continuity in
background parameters require further clarification. Its draft is not included.
Neither appendix transform is formalized. The spherical Appendix A assumption
is discharged by the all-angular proof, and the all-angular appendix is not
needed for the listed results. The spherical extremal low-frequency conclusion
is covered by the all-angular theorem at $L=0$, without a separate spherical
anchor. Spherical harmonic decomposition, the spacetime PDE, and time-dependent
decay estimates are outside this radial formalization.

Mathlib supplies the underlying calculus, measure theory, asymptotics, algebra,
and general mathematical APIs; the mode-stability results in the table are
proved in this library. No manuscript text, figures, or third-party source
files are distributed. This is a one-time export, not a mirror of a development
repository.

## Build and audit

Use Lean **4.35.0-rc3**, pinned by `lean-toolchain`, and Mathlib revision
**`7d6757bc18680044fc0ff6efc8ee20494b408556`**, pinned by `lakefile.toml` and
`lake-manifest.json`. The manifest also pins Mathlib's transitive dependencies.
With an existing [elan installation](https://github.com/leanprover/elan) and
Python 3, run these commands from the repository root:

```sh
lake exe cache get
lake build
python3 scripts/audit_axioms.py
```

The first command obtains Mathlib build artifacts for the pinned revision.
The build compiles the library from its sources. The audit prints Lean's axiom
list for all 20 theorem anchors and exits unsuccessfully if Lean fails, an
anchor result is missing, or an axiom outside the three permitted names appears.
Its temporary probe is removed after execution. No CI is included.

## License, citation, and acknowledgement

The formalization and release documentation are licensed under
[Apache-2.0](LICENSE). Dependencies retain their own licenses; the code license
does not license the unpublished research notes. Citation metadata is provided
in [CITATION.cff](CITATION.cff).

This formalization was produced by Christoph Kehle with assistance from Claude Code and OpenAI Codex, using source-first statement review, frozen declarations, independent audits, and Lean kernel checking.
