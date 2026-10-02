# Review of the AGKRS nonpositive-endpoint consumer

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Verdict:** **REVISE.**  The one-player `S.2` no-go and the logical audit of
prioritized residuals pass, but the proposed nonpositive-endpoint consumer
has a false key implication.  It is not export-ready and currently closes no
AGKRS subbranch.

## 1. The central closure step is false

The proof asserts that, for every literal behavioral profile `sigma`, player
`i` can deviate to Always Quit and thereby guarantee

\[
r_i(\{i\})\le B_i(\sigma).
\]

This is false in a quitting game.  If an opponent Quits at date zero, then an
Always-Quit deviation by `i` absorbs on a coalition containing that opponent;
it need not produce the singleton `{i}`.  Consequently the halfspace

```text
reward (quittingSingletonTerminal i) i <= pair.2 i
```

does not contain all literal terminal-semantic pairs and cannot be extended
to `quittingTerminalSemanticCarrier reward` by closure.

### Exact two-player endpoint countermodel

Take players `i,j` and define the relevant rewards by

\[
r_i(\{i\})=1,qquad r_i(\{j\})=r_i(\{i,j\})=0,
\]

with every reward coordinate of `j` equal to zero.  At the literal profile
where `j` Quits surely at date zero and `i` Continues, the prescribed payoff
is `(0,0)`.  Both unrestricted envelopes are also zero:

- every deviation of `i` faces the sure date-zero Quit of `j`, so its payoff
  is either `r_i({j})=0` or `r_i({i,j})=0`;
- every payoff and every deviation payoff of `j` is zero.

Thus the actual semantic pair is

\[
(U,B)=((0,0),(0,0)).
\]

It lies in the carrier and has zero debt.  Choose `j` as the punished label.
Because all of `j`'s rewards vanish, its punishment value and endpoint cap
are both zero.  These fields define a literal
`QuittingPositiveJointPrefixReachPunishmentEndpoint` whose prescribed
coordinates are all nonpositive.  Nevertheless

\[
r_i(\{i\})=1>0,
\]

so `IsQuittingZeroSolo reward` fails, and all-Continue is not an exact Nash
profile.  (This particular table has another stationary equilibrium; the
point is that it directly refutes the claimed zero-solo implication and the
advertised all-Continue witness.)

The endpoint definition stores carrier membership, nonpositive debt, and one
punished-coordinate cap.  It does not store the positive-joint source that
produced it, and its fields do not exclude this example.  More importantly,
the positive-joint construction only controls survival through the preceding
stationary prefix; it supplies no date-zero opponent-survival property for
the reached punishment suffix.  Hence the omitted provenance does not repair
the written argument.

## 2. Strongest immediate repair

The following strengthened statement is valid:

> If `endpoint.endpoint.1 i <= 0` and
> `reward (quittingSingletonTerminal i) i <= endpoint.endpoint.2 i` for every
> `i`, then the endpoint equality `U_i=B_i` implies
> `IsQuittingZeroSolo reward`, and the checked zero-solo theorem supplies the
> exact all-Continue stationary branch.

Equivalently, one may assume that the all-Continue root is exact Nash against
the endpoint payoff.  But neither singleton domination nor an executable
all-Continue root is a field of
`QuittingPositiveJointPrefixReachNoSureExitResidual`.  Adding it therefore
creates a new residual condition rather than consuming the currently named
nonpositive-endpoint subcase.

The source-level corollary in Section 2 must consequently be removed or
restated with this additional hypothesis.  With that repair it is essentially
the checked zero-solo consumer, not yet a novel source-closure theorem.

## 3. One-player positive-source residual

The Section 3 construction otherwise passes.

For the one-player table `r({*})=-1`, Never has payoff zero and every
behavioral strategy has payoff `-a`, where `a` is its total probability of
ever quitting.  Hence its unrestricted best-response value and punishment
value are both zero.

Choose:

- `error n=1/(n+1)`;
- the prefix root and every punishment row pure Continue;
- horizon two and punished label `*`.

Then the error is positive and tends to zero, the horizon is greater than
one, the stationary live mass is one, the full prefix/punishment profile is
all-Continue and exact Nash, and the punishment is within every positive
error of the min-max value zero.  With `selected=id`, whole-prefix joint
survival is constantly one, so this supplies all fields of
`QuittingPositiveJointPrefixReachSource`.

Every literal semantic pair has `U=-a<=0` and `B=0`; these statements persist
under closure.  An eligible endpoint has debt `B-U<=0`, while carrier debt is
nonnegative, so `U=B=0`.  Its punishment cap is exact.  A root with a sure
quitter is necessarily pure Quit; against tail zero it prescribes payoff
`-1`, while Continue yields zero.  Therefore no eligible endpoint has
`HasSureExitNashPrefix`, and the source indeed defines
`QuittingPositiveJointPrefixReachNoSureExitResidual`.

Finally, every instant-punishment profile surely Quits at the first stage and
pays `-1`; replacing the whole behavioral strategy by Always Continue pays
zero.  The gain is one independently of the punishment row, so
`QuittingInstantPunishmentεEquilibriumExistence` fails by taking any
`0<epsilon<1`.  This verifies global failure of `S.2`, not merely failure of
one endpoint root.  The exact all-Continue stationary branch `S.1` holds.

Thus the no-go

```text
positive-joint no-sure-exit residual -> S.2
```

is correct and source-native.

## 4. Prioritized versus nonprioritized logic

The note's priority analysis is correct.  At a fixed positive `delta`, a
`QuittingPrioritizedRefinedSourceResidualAt` explicitly negates the
stationary, instant, well-supported, and generated pointwise branches.
Any global branch-existence output specializes at that same `delta` and
contradicts the corresponding field.  Hence a capstone consumer on an
inhabited prioritized residual is logically an exclusion of that residual,
unlike the positive-joint and negative-owner obligations.

The raw corrected residual regressions do not alter this: without the
priority fields they can coexist with an already available global branch.
The distinction made in Sections 1 and 4 is sound.

## 5. Export assessment

The surviving one-player theorem is a useful boundary showing that the
positive residual cannot be routed to `S.2` alone, but it does not close a
branch.  The only proposed positive consumer fails, and its direct repair
requires singleton domination—essentially the zero-solo hypothesis itself—which
the source does not produce.

Accordingly the current note should remain internal with status **REVISE**.
It is not suitable for export or formalization as a named AGKRS source
closure.  A genuinely exportable result would need to derive singleton
domination (or another stationary/well-supported consumer) from the actual
positive-joint source, rather than assume it at the endpoint.

