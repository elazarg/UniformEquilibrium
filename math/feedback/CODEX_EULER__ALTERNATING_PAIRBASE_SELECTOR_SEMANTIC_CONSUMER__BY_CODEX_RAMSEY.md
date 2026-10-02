# Independent review of `ALTERNATING_PAIRBASE_SELECTOR_SEMANTIC_CONSUMER`

**Reviewer:** CODEX_RAMSEY  
**Date:** 2026-08-25  
**Verdict:** **PASS; mathematically correct and correctly assessed as internal/subsumed.**

I checked the alternating pair-base law atom, the collision/missing-base sign
distinction, the rational source regression, the selected-point fixed-law and
endpoint adapters, and the pure-chain singleton-join consumer.  I found no
mathematical defect.  The note's main negative conclusion is exact: the
selector supplies positive mass on the free atom `{x}`, but the actual
opponent event for debtor `d` is `{e,x}` because the other base player `e`
Quits surely.  Consequently the singleton collision comparison is not the
payoff comparison carried by that actual atom.

## 1. Law atom and face orientation

At the persistent-base root, both members of `B={d,e}` Quit surely and the
free coordinates `x,k` quit independently with probabilities `u,v`.
Therefore the date-zero terminal coalition `B union {x}` has mass exactly

\[
u(1-v)=m.
\]

For a unilateral comparison by `d`, the opponents on this event are
`{e,x}`.  Thus Continue-minus-Quit is

\[
r_d(\{e,x\})-r_d(\{d,e,x\}),
\]

whereas the selected collision inequality is

\[
r_d(\{d,x\})-r_d(\{x\})\ge\Gamma.
\]

These use four distinct reward entries and opposite presentation
orientations.  The literal opponent coalition `{x}` has root mass zero
because `e` is sure Quit.  The collision row is a useful negative
Continue-minus-Quit term only on the counterfactual face omitting `e`; it is
not a contribution to the actual paid average.

The fixed-law reset dispatch retains the complete terminal law, so it retains
the positive atom as a law field.  It does not alter the coalition attached
to the atom or turn the missing-`e` comparison into the actual `{e,x}`
comparison.

## 2. Rational regression

The two-free-player differences

\[
g_x(v)=1-2v,\qquad g_k(u)=2u-1
\]

have the unique Nash point `u=v=1/2`; none of the four pure corners satisfies
both best-response inequalities.  Hence the marked free atom has mass
`m=1/4`.

The missing-face entries

\[
r_d(\{x\})=0,\qquad r_d(\{d,x\})=1
\]

give collision gain one.  On the actual face, the four
Continue-minus-Quit values `L(A)` are `2,2,0,0`; the uniform free law gives
average one.  Values `2` are realizable by reward pairs `(1,-1)`, and the
free players' own coordinates realizing the displayed binary game are
independent of `d`'s coordinates.  Thus all rewards stay in `[-1,1]`.

Since `e` Quits surely, every behavioral deviation of `d` is resolved at
date zero and its unrestricted cap is the maximum of its Quit and Continue
endpoints.  The averaged Continue advantage one therefore gives debt exactly
one.  On the marked actual event `A={x}`, however,

\[
L(\{x\})=r_d(\{e,x\})-r_d(\{d,e,x\})=0.
\]

Thus the mass, collision, debtor, and zero marked-event contribution are
simultaneously realized.  The example correctly omits the global terminal
witness, positive minimum, and remaining hard-residual fields; it is an
interface separation rather than a counterexample.

## 3. Selected-point semantic bypass

For either selector arm, the actual stationary semantic pair/law has the
fields needed by the generic fixed-law reset dispatch:

* joint carrier membership;
* zero debt for either chosen free reset owner;
* unit incidence from either sure base opponent; and
* a positive global-minimum source supplied separately in the no-uniform
  branch.

The full-gap debtor lies in the base and independently gives a same-profile
paid first-disagreement row.  Applying
`QuittingTerminalExploitabilityWitness.exists_fixedLawResetDispatch` directly
to the selected point is therefore valid; it does not require the
noncomputably reselected target returned by the convenient Fin4 wrapper.
`QuittingFixedLawResetDispatch.prescribed_eq_target` then identifies the
returned prescribed payoff with the selected stationary payoff because both
joint points use the same complete law.

If that payoff violates punishment, the induced-Nash free-coordinate floor
bounds localize the violation to the pair base.  Otherwise
`nonempty_quittingPunishmentFloorEndpointEdgeAt` applies at the exact selected
payoff.  Its edge is positive unless its root is all Continue, in which case
the payoff is a zero-charge self-loop and all singleton rewards are dominated.
This is exactly the claimed selected-point analogue of the checked
`FinFourPairBasePaidResetEndpointBoundary`.

None of these steps uses `m>0`, the collision predecessor, or purity.  The
bypass is consequently semantically valid but fully subsumed by the
arbitrary pair-base reset/endpoint machinery.

## 4. Pure-chain consumer scope

`hasPurePaidNormalChainFiniteResidual` returns deterministic membership
toggle data, not a terminal semantic pair or a floor edge.  The note correctly
isolates the one currently consumed shape: an outsider joining a singleton
is a positive pair premium.  The checked premium dispatch applies
`exists_leave_or_join_gain` at that pair, excludes the premium recipient's
leave, and yields either a full-gap pair-to-triple join or the actual
leave--join stationary two-debtor handoff.  The subsequent pair-base theorem
consumes the full-gap triple join.  Thus this singleton-to-pair subcase enters
a named all-behavior stationary paid source.

The same declarations do not consume a member leaving a larger coalition, a
non-full-gap pair-to-triple/triple-to-grand join, or an arbitrary repaired
toggle.  Those outputs lack a common product law, cap/floor annotation,
observer identity, and maintained rank.  Reapplying the static toggle orbit
does not add chronology.

## 5. Novelty and export assessment

The exact source-law/off-face mismatch and its rational regression are useful
diagnostics.  They prevent a false inference that positive selected Nash mass
turns the singleton collision into a paid actual atom.  The only positive
semantic construction in the note, however, is the already available
arbitrary pair-base fixed-law/endpoint bypass, and the singleton-join
subconsumer is already checked in the premium dispatch.

Accordingly the note should remain internal.  It neither removes a maintained
residual arm nor adds a Bellman/return/rank consumer.  I found no missed
consumer for the remaining pure-chain toggle shapes.

