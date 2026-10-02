# Review of the AGKRS positive-endpoint full-support stationary no-go

**Reviewer:** CODEX_RAMSEY  
**Date:** 2026-08-25  
**Verdict:** **REVISE → PASS** after one mandatory opening-scope repair

## Claim reviewed

I independently checked the two-player reward table in
[`CODEX_MINER__AGKRS_POSITIVE_ENDPOINT_FULL_SUPPORT_STATIONARY_NOGO.md`](../notes/CODEX_MINER__AGKRS_POSITIVE_ENDPOINT_FULL_SUPPORT_STATIONARY_NOGO.md).
The note claims that the unprioritized
`QuittingPositiveJointPrefixReachNoSureExitResidual` interface, even together
with positivity of a prescribed coordinate at every eligible endpoint, does
not force AGKRS branch S.2.  The displayed table instead already has an exact
full-support stationary equilibrium, hence branch S.1.

The S.2 no-go and all source calculations pass.  A second review identified
one scope sentence that my first pass missed: the displayed table also has a
literal S.3 witness, so the opening question cannot answer negatively whether
positivity forces “S.2 or S.3.”  Repeat the solo-`q` row with any positive
hazard `h≤1/2`.  Every tail payoff is `r({q})=(0,2)`; `q`'s two endpoints are
both `2`, while `p`'s used Continue action has value `0` and its Quit endpoint
is `-1+2h≤0`.  This is an exact well-supported completely absorbing sequence.

Accordingly, Section 1 must say only that endpoint positivity does not force
S.2 or define a decreasing endpoint rank.  Section 8 already states that
narrow conclusion correctly.  Subject to that literal repair, I found no
mathematical or source-scope objection.

## Direct arithmetic and unrestricted-deviation check

For the rows

\[
 r(\{p\})=(-1,1),\qquad r(\{q\})=(0,2),\qquad
 r(\{p,q\})=(1,0),
\]

and independent Quit probabilities `1/2,1/2`, the proposed continuation
value `U=(0,1)` is exact.  Player `p`'s Quit and Continue endpoints are both
zero; player `q`'s are both one.  The one-row absorption contributions are
respectively `0` and `3/4`, and the common survival mass is `1/4`, so the
stationary Bellman values are indeed `(0,1)`.

This equality upgrades to arbitrary behavioral deviations.  Against `q`'s
independent half hazard, every deterministic pure Quit time of `p` has equal
positive and negative terminal contributions and value zero; Never also has
value zero.  Against `p`'s independent half hazard, every deterministic pure
Quit time of `q` has value one, as does Never.  The checked pure-time
extremality/optimal-stopping reduction therefore gives unrestricted caps
`0,1`, not merely stationary best responses.  Equivalently, the conditional
Bellman value after every live history is unchanged and the opponent hazard
makes absorption almost sure.

The punishment values are also exact:

* `P_p=0`: Never guarantees zero against every opponent plan, while an
  always-Continue opponent makes every `p` reply worth at most zero.
* `P_q=1`: for an arbitrary `p` plan, let `A` be the probability of a finite
  `p` exit when `q` always Continues.  Never gives `A`; deterministic times
  tending to infinity have payoffs tending to `2-A`, because the tie atom at
  the chosen time tends to zero.  Thus the best reply is at least
  `max(A,2-A)\ge1`.  If `p` Quits surely at date zero, every `q` strategy is
  worth at most one, giving the matching upper bound.

These calculations explicitly include date zero, ties, Never, and arbitrary
history-dependent mixtures.  I also tested the four pure endpoint replies:
none produces a hidden value above the claimed caps.

## Source, endpoint, and no-sure-exit fields

The constant family with error `1/(n+1)`, horizon `2`, stationary root and
punishment both equal to the half--half row, and punished label `p` satisfies
the fields of `QuittingDiffuseStationaryPrefixFamily`:

* horizon `2` satisfies `1<horizon`;
* the full prefix/punishment plan is the same exact stationary profile;
* the punished-player continuation cap equals `P_p=0`; and
* one-row live mass is `1/4>0`.

The implementation repeats the prefix row through indices `0,1,2`, so the
whole-prefix survival is exactly `(1/4)^3=1/64`.  With `selected=id` this is a
literal positive-joint source.

For any eligible punishment endpoint, not merely the displayed one,
`quittingPunishmentValue_le_terminalSemanticEnvelope_of_mem_carrier` gives
`B_p\ge0` and `B_q\ge1`.  The endpoint debt theorem makes `U=B`, hence every
such endpoint has `U_q\ge1>0`, independently of its recorded punished label.

Let `x,y` be the one-stage Quit probabilities over such a continuation `U`.
If `x=1`, player `q` strictly prefers Continue, so `y=0`; then `p` strictly
prefers Continue because Quit pays `-1` and continuation pays at least zero.
If `y=1`, player `p` strictly prefers Quit, forcing `x=1`, after which `q`
strictly prefers Continue.  Thus no eligible endpoint has a sure-quitter exact
root, and the source really yields the claimed no-sure-exit residual.

## Sharp S.2 obstruction

The two possible sure labels exhaust an S.2 witness.

* If `p` is sure and `q` Quits with probability `y`, prescribed payoffs are
  `(-1+2y,1-y)`.  `q`'s Continue deviation gives `y\le\varepsilon`; `p`'s
  Continue-then-near-best-reply deviation has value at least zero, giving
  `y\ge(1-\varepsilon)/2`.
* If `q` is sure and `p` Quits with probability `x`, prescribed payoffs are
  `(x,2(1-x))`.  `p`'s Quit deviation gives `x\ge1-\varepsilon`; `q`'s
  Continue-then-near-best-reply deviation has value at least one, giving
  `x\le(1+\varepsilon)/2`.

Either pair requires `\varepsilon\ge1/3`.  Approximate attainment of a
punishment best reply is enough; the proof does not assume that the supremum
is attained.  Hence the global S.2 predicate fails.

## Source and novelty audit

The note's uses of
`QuittingPositiveJointPrefixReachPunishmentEndpoint.debt_eq_zero`,
`payoff_eq_envelope`, the carrier punishment-floor theorem,
`HasSureExitNashPrefix`, and
`QuittingPositiveJointPrefixReachNoSureExitResidual` agree with
`PositiveJointPrefixReachEndpoint.lean`.  The family and source quantifiers
agree with `StationarilyGeneratedWitnessRegimes.lean` and
`DiffuseStationaryPrefixSourceAttachments.lean`.  I found no checked theorem
already packaging this exact positive-endpoint/full-support regression.

The novelty and conclusion must remain narrow.  The example is in both S.1
and S.3 and is therefore not a counterexample to AGKRS Theorem 3.4.  It only
refutes an S.2-only consumer based on positivity plus the unprioritized
no-sure-exit residual.
After global failure of S.1 is imposed, this table is unavailable.  The note
states that branch-priority limitation correctly, so I recommend retaining it
internally and not exporting it as a conjecture-closing result.
