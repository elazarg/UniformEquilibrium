# Review of `CODEX_MINER__AGKRS_POSITIVE_ENDPOINT_FULL_SUPPORT_STATIONARY_NOGO`

**Reviewer:** CODEX_EULER  
**Date:** 2026-08-25  
**Verdict:** **REVISE** (core regression and S.2 no-go pass; the opening
S.2-or-S.3 scope is false because the displayed table also has S.3)

## Claim audited

The note gives the two-player zero-Never table

\[
\begin{array}{c|cc}
S&r_p(S)&r_q(S)\\ \hline
\{p\}&-1&1\\
\{q\}&0&2\\
\{p,q\}&1&0
\end{array}
\]

and claims a literal positive-joint/no-sure-exit residual whose every eligible
punishment endpoint has a positive coordinate, while global S.2 fails below
error `1/3` and a full-support stationary S.1 solution exists.

Those listed properties pass.  The required repair concerns the broader
opening question, which asks whether positivity can force “S.2 or S.3” and
then says the example answers no.  It does not: the same table has an exact
support-local absorbing S.3 sequence.

## 1. Full-support stationary equilibrium: PASS

At the half--half product root and tail `U=(0,1)`, the pure endpoint values
are

\[
Q_p=C_p=0,\qquad Q_q=C_q=1.
\]

The successor is therefore `U`.  This is not merely stationary
complementarity.  Conditional on every live history, the opponent continues
and quits with probability one half.  For `p`, either pure action has
continuation value zero; for `q`, either pure action has continuation value
one.  Absorption occurs almost surely because the one-row live mass is
`1/4`.  The usual bounded dynamic stopping recursion therefore gives the same
value against every history-dependent behavioral hazard.  The stationary
profile is exact unrestricted Nash, so S.1 holds.

The alternative absorption-law calculation is also correct: the one-row
terminal charges are `(0,3/4)`, survival is `1/4`, and division by absorbed
mass `3/4` yields `(0,1)`.

## 2. Punishment values: PASS

### Player `p`

Continuing forever guarantees zero against every `q` strategy: a singleton
`q` exit and Never both pay `p` zero.  Against `q` Never, every eventual solo
`p` exit pays `-1`, while Never pays zero.  Hence `P_p=0`.

### Player `q`

Against arbitrary `p`, let `A` be the probability that `p` ever quits when
`q` continues.  Never gives `q` payoff `A`.  Quitting deterministically at
time `T` gives

\[
\Pr(T_p<T)+2\Pr(T_p>T),
\]

with a simultaneous exit paying zero.  Since the point masses
`Pr(T_p=T)` tend to zero, this converges to `2-A`.  Thus the behavioral
best-reply supremum is at least `max(A,2-A)>=1`.  If `p` quits surely at date
zero, every `q` strategy pays at most one, so `P_q=1`.

This correctly handles date-zero ties, Never, and nonattainment of the
best-reply supremum.

## 3. Literal positive-joint source: PASS

The proposed family has positive errors `1/(n+1)` tending to zero, constant
half--half root, horizon `2>1`, punished player `p`, and constant half--half
punishment rows.  Since the entire prefix-then-punishment plan is the exact
stationary profile, the `2*error` Nash field holds.  The punished player's
behavioral punishment cap is exactly `0=P_p`, and the one-stage live mass is
`1/4`.

With `selected=id`, the prefix uses `horizon+1=3` repeated rows, so

\[
\texttt{prefixJointSurvival}=(1/4)^3=1/64.
\]

Thus all fields of `QuittingPositiveJointPrefixReachSource` are present with
positive joint limit `1/64`.  The actual stationary semantic pair
`((0,1),(0,1))`, labelled by `p`, is an explicit punishment endpoint.

## 4. Universal endpoint positivity and no-sure-root: PASS

For any
`QuittingPositiveJointPrefixReachPunishmentEndpoint` of this table, carrier
min-max lower bounds give

\[
B_p\ge0,\qquad B_q\ge1.
\]

The endpoint debt is nonpositive by its field and nonnegative by carrier
membership, hence zero.  Therefore `U=B`, in particular `U_q>=1>0`.  This
argument is independent of which label is stored in `endpoint.punished`.

Let `x,y` be the root Quit probabilities of `p,q`.

- If `x=1`, `q`'s Quit-minus-Continue difference is `-1`, so exact root Nash
  forces `y=0`.  Then `p`'s Quit payoff is `-1` and its Continue payoff is
  `U_p>=0`, contradicting `p`'s sure Quit support condition.
- If `y=1`, `p`'s Quit-minus-Continue difference is `1`, so exact root Nash
  forces `x=1`; `q` then strictly prefers Continue, a contradiction.

Every sure quitter is one of these two players.  Hence no eligible endpoint
has a sure-exit exact Nash prefix, and the source packages a literal
`QuittingPositiveJointPrefixReachNoSureExitResidual`.

## 5. Global S.2 gap: PASS

The proof actually rules out arbitrary executable one-stage profiles with a
sure quitter; it does not need the additional punishment-cap field.

If `p` quits surely and `q` quits with probability `y`, prescribed values are

\[
u_p=-1+2y,\qquad u_q=1-y.
\]

Player `q` can Continue for value one, giving `y<=epsilon`.  Player `p` can
Continue at date zero and, conditional on survival, approximate a punishment
best response of value at least `P_p=0`; the date-zero `q` exit also pays
zero.  Hence `1-2y<=epsilon`, or
`y>=(1-epsilon)/2`.  These are incompatible for `epsilon<1/3`.

If `q` quits surely and `p` quits with probability `x`, prescribed values are

\[
u_p=x,\qquad u_q=2(1-x).
\]

Quitting gives `p` the collision payoff one, hence
`x>=1-epsilon`.  Continuing gives `q` at least one whether `p` quits now or
the punishment suffix is reached, hence
`x<=(1+epsilon)/2`.  Again `epsilon<1/3` is impossible.

Approximate suffix best replies suffice; no attainment is assumed.  Failure
at one positive error proves failure of the global S.2 existence predicate.

## 6. Mandatory scope repair: the table has S.3

Take the constant solo-`q` root in which `q` Quits with any fixed probability

\[
0<h\le1/2
\]

and `p` Continues surely.  This sequence absorbs almost surely and every tail
value is the singleton-`q` vector

\[
r(\{q\})=(0,2).
\]

For `q`, Quit and Continue both yield `2`.  For `p`, Continue yields `0`,
while Quit yields

\[
(1-h)(-1)+h(1)=-1+2h\le0.
\]

Thus the constant sequence is exact support-local Nash and completely
absorbing.  It witnesses `QuittingWellSupportedAbsorbingSequenceExistence`,
hence literal branch S.3.

Accordingly the example proves only

\[
\text{positive-joint no-sure-exit residual}
+\text{ endpoint positivity}
\not\Rightarrow \mathrm{S.2}.
\]

It does **not** prove failure of an `S.2 or S.3` consumer.  Section 8 of the
note already states the correct S.2-only implication, but the question and
verdict in Sections 1 and 10 must be conformed to it.  Add the explicit S.3
boundary above; it is informative rather than fatal to the core regression.

## 7. Implication for the prioritized positive-joint consumer

The checked `theorem3_4_of_prioritizedSourceClosures` asks `hpositive` to map
every unprioritized no-sure-exit residual to `S.1 or S.2 or S.3`.  This table
is therefore not a countermodel to that hypothesis: it supplies S.1 and S.3.
It shows that a universal positive-source consumer must be allowed to return
another branch and cannot select S.2 merely from endpoint positivity.

There is nevertheless a useful architectural sharpening.  In the capstone's
actual proof, the positive residual is reached only after the outer
fixed-branch selector did not return global S.1, S.2, or S.3.  Those negative
facts are not stored in the type passed to `hpositive`, so the hypothesis is
stronger than the proof route conceptually needs.  A priority-safe interface
could bundle

```text
residual : QuittingPositiveJointPrefixReachNoSureExitResidual reward
not_stationary : ¬QuittingStationaryεEquilibriumExistence reward
not_instant : ¬QuittingInstantPunishmentεEquilibriumExistence reward
not_wellSupported : ¬QuittingWellSupportedAbsorbingSequenceExistence reward
```

or the exact fixed-scale/global variants used by the selector.  The present
table would then be excluded twice, by S.1 and S.3.  Constructing that wrapper
and preserving its negations through the existing disjunction proof would
sharpen the source-closure obligation, but it would not itself consume it.

## 8. Required edits and disposition

1. Replace every claim that the table blocks “S.2 or S.3” by the precise
   S.2-only no-go.
2. Add the solo-`q` exact S.3 construction from Section 6 above.
3. Retain the explicit S.1-priority qualification and strengthen it to note
   that S.3 priority also excludes the regression.
4. Do not present endpoint positivity as a failed three-branch consumer; it
   is only a failed S.2 selector and a failed decreasing-rank proposal.

After these repairs, the note is mathematically sound as an internal
interface regression.  It is not export-worthy on its own: it does not close
a source class or produce a maintained rank, and its strongest valid outcome
is a no-go for one proposed S.2-only inference.

