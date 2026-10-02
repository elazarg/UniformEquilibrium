# Adversarial review: deleted bubble, descaling, paid port, regression

Identity: `CODEX_CURVATURE_REVIEW`  
Date: 2026-08-31  
Recommendation: mathematically sound after two scope clarifications. The new
deleted-survival estimate, full-chord descaling, and exact all-proper
regression are suitable for an export-boundary packet after the author makes
the provenance/redundancy qualifications below. This is not a Fin4 chamber
consumer.

## Claim reviewed

I checked the following four claims in
`CODEX_STRENGTHEN__CAP_SWITCHING_DELETED_BUBBLE_AND_REPLAY_CONTRACT.md`.

1. A stopping-law mixture edge changes the observer's two-pure-time gap by at
   most the mixture amplitude times a mover-deleted survival probability.
2. A first-order reset rectangle descales to one actual full-chord endpoint
   carrying a fixed positive paid pure-time edge.
3. That endpoint can instantiate the existing positive-minimum paid-cap
   trichotomy.
4. The Fin4 finite-support example has the asserted cap square, vanishing
   fixed-witness curvature, escaping first disagreement, and zero actual
   cemetery factors.

The review was mathematical and declaration-facing; I did not implement new
Lean.

## 1. Theorem 4.1 passes

Let

```text
G(P) = V_P(q+) - V_P(q-),
```

where the two pure-time plans first disagree at `r`, and let mover `e` be
distinct from the observer. If the law of `e` changes from `mu` to
`(1-alpha) mu + alpha nu`, separate affinity gives exactly

```text
G(P')-G(P) = alpha (G(P[e<-nu])-G(P[e<-mu])).
```

Condition on all opponents other than the observer and `e`. If any such
opponent stops strictly before `r`, the two observer plans have been identical
up to absorption, so each endpoint gap is zero. On the complementary event,
each endpoint gap lies in `[-2M,2M]`. Therefore their difference is at most
`4M`, which proves

```text
|G(P')-G(P)| <= 4 M alpha H_{-i,-e}(P,r).
```

The event must mean survival *to the live history at `r`*, i.e. no stop
strictly before `r`; a simultaneous stop at `r` is not screened. This is also
the convention of the first-disagreement survival weight in
`QuittingPaidFirstDisagreementRow`.

The reverse edge orientation is harmless because the deleted event omits
`e`, hence its probability is identical at the two edge endpoints. It would
help to state this invariance explicitly in the paper proof.

The refinement (7.10) also passes. Conditional on the other opponents
surviving to `r`, an endpoint gap vanishes when `e` stops before `r` and has
absolute value at most `2M` otherwise. Applying the triangle inequality to
the two endpoint laws gives the sum of their inclusive tail masses and the
constant `2M`.

Consequently the two-edge rectangle estimate, the `gamma/(8MC)` face bound,
and its eventual transfer to `gamma/(16MC)` at the empty-face source are
valid. The transfer uses only the elementary telescoping total-variation
bound for finitely many `O(lambda)` coordinate mixtures. The weak-limit
argument is also sound: the sets `{stop time > N}`, with `Never` included,
are clopen in the one-point compactification, and decrease to the joint
pair-`Never` event.

This output remains exactly what the note says it is: a pair-deleted limit
atom, not a full terminal-law atom and not full opponent reach at the moving
row.

## 2. Full-chord descaling passes

Along a two-edge path between the selected diagonal vertices,

```text
gamma lambda <= G(R)-G(S)
```

forces one signed edge increment to be at least `gamma lambda/2` (the
absolute-value formulation in the note is weaker and therefore safe). If
that edge has mixture amplitude `0 < alpha <= C lambda`, exact stopping-law
affinity gives

```text
G(mixed)-G(unmixed) = alpha (G(full)-G(unmixed)).
```

Thus the full edge changes `G` by at least `gamma/(2C)`, and at least one of
its two endpoints has `|G| >= gamma/(4C)`. Swapping the two pure-time labels
when needed turns this into a positive edge. The declaration
`exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` then supplies
a literal paid first-disagreement row of gain `gamma/(4C)` at that actual
endpoint. No cap attainment or survival division is used.

For the nested radial construction, the statement that the effective
amplitude is outer radial weight times inner frontier scale agrees with the
definitions and scaling identities in `Frozen/RadialResetCube.lean`.

## 3. The checked paid-cap trichotomy really is instantiable, with a scope
qualification

`QuittingPaidCapLiftedSource` requires only:

- a positive global semantic minimum and its minimum proof;
- one actual behavioral profile;
- an observer;
- a positive gain; and
- a `QuittingPaidFirstDisagreementRow` at that profile.

The full-chord endpoint supplies the last four fields, so
`QuittingPaidCapLiftedSource.nonempty_summablePort` and
`QuittingPaidCapLiftedSource.exactTrichotomy` do apply literally. Under the
no-uniform-payoff/terminal-gap hypothesis, the charged branch is impossible,
leaving quantitative debt descent or inert stall. This part of Section 7.1
is correct.

Two qualifications should be explicit.

1. `QuittingPaidCapLiftedSource` does **not** store the reset cube, original
   minimum chronology, or the full-chord endpoint's ancestry. The endpoint is
   source-constructed in ordinary mathematics, but the checked trichotomy
   forgets that provenance. It cannot by itself return a child attached to
   the original cube/source.
2. Under a terminal exploitability gap, the existing declaration
   `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` constructs
   a paid-cap port at every actual profile. Therefore “the endpoint enters the
   trichotomy” is not, by itself, new counterexample-facing progress. The new
   content is that the *specified cap-curvature witnesses* give a fixed row at
   a specified source-built full endpoint, together with the pair-deleted
   bubble. The trichotomy still ends in its known inert arm, and its debt
   descent is real-valued rather than a renewable rank.

These are scope corrections, not failures of the construction.

## 4. The Fin4 all-proper regression passes exactly

The stated reward table is independent of `n`, and all strategies used have
finite-support stopping laws. Direct conditioning gives the complete pure-time
menu claimed in the note:

```text
quit at r_n:                         x
quit between r_n and L_n, or Never: y
quit in a's source window:          y + (1-x)(1-y) delta_n.
```

All other pure times are dominated by one of these. Hence

```text
B_i(x,y) = max{x, y+(1-x)(1-y)delta_n}.
```

At the four corners `x,y in {0,lambda_n}`, with
`delta_n < lambda_n`, this yields exactly

```text
B00 = delta_n,
B10 = lambda_n,
B01 = lambda_n + (1-lambda_n)delta_n,
B11 = lambda_n + (1-lambda_n)^2 delta_n,
```

and therefore

```text
Sq(B_i)/lambda_n -> -1.
```

For a fixed pure time, the square is zero except inside `a`'s moving source
window, where it is `delta_n lambda_n^2`; this is uniformly
`o(lambda_n)`. The active witnesses are `r_n` and a date in the late window,
so their first disagreement escapes. “Survival to `r_n`” is one because it
means survival strictly before the live row; target clocks may stop at the row
itself.

Every source, target, cube face, and full endpoint has zero `Never` mass for
`a,b,c`. Thus every relevant terminal pair-deleted product has a zero factor,
and the finite-splice error lies in the zero/cap-tight arm despite the
first-order cap square and its weak pair-`Never` limit. Affinity of `Never`
mass also proves the stated invariance under any finite sequence of proper-law
mixtures. The example is a valid exact quitting-game regression and is
properly disclaimed as having no positive global minimum.

## 5. Lean interfaces checked

The narrow declaration audit covered:

- `QuittingPaidFirstDisagreementRow` and
  `exists_quittingPaidFirstDisagreementRow_of_pureTimePayoff_sub` in
  `TerminalSemanticPaidFirstDisagreement.lean`;
- `QuittingPureTimeWitnessSwitchCertificate` and
  `exists_pureTimeWitnessSwitchCertificate_of_abs_envelopeCurvature` in
  `TerminalSemanticPositiveSlopeRectangle.lean`;
- `exists_resetCubePureTimeSquareEdgeWitnessSwitch_of_abs_debtCurvature` in
  `TerminalSemanticStoppingLawResetCubeOrientation.lean`;
- `QuittingPaidCapLiftedSource` and `nonempty_summablePort` in
  `Endpoint/PaidCapLiftedSummablePort.lean`;
- `QuittingPaidCapLiftedSource.exactTrichotomy` in
  `Endpoint/PaidCapPortExactTrichotomy.lean`;
- `HasTerminalExploitabilityGap.nonempty_actualProfilePaidCapPort` in
  `Endpoint/ActualProfileTerminalGapPaidCap.lean`; and
- the finite-splice limit/product declarations in
  `TerminalSemanticStoppingLawFiniteCapClock.lean`.

No inspected declaration contradicts the note's mathematical identities.

## Final verdict

There is no substantive mathematical objection to Theorem 4.1, Corollary
4.2, the full-chord descaling, or the all-proper Fin4 regression. The note is
export-worthy as a **boundary/no-go packet** after it clearly says that the
checked paid-cap adapter forgets original source ancestry and that entry into
the trichotomy is redundant under a global terminal gap. It is not
export-worthy as a claimed consumption of cap switching, since the inert
stall remains and the pair-deleted bubble has no replay/terminal consumer.
