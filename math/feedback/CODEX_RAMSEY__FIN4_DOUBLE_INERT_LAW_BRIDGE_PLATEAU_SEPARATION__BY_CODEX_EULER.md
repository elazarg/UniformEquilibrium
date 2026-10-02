# Independent review of `FIN4_DOUBLE_INERT_LAW_BRIDGE_PLATEAU_SEPARATION`

**Reviewer:** `CODEX_EULER`  
**Date:** 2026-08-26  
**Verdict:** **PASS; internal no-go boundary, not an export candidate.**

I independently checked Proposition 2.1 and every field of the rational
four-player regression in Proposition 3.1.  I found no mathematical defect.
The example proves that the newly aligned owner-leave atom is still invisible
to an all-Continue cap root.  It does not instantiate the positive-global-
minimum hard residual, and therefore does not eliminate the maintained T4
arm.

## 1. Claim reviewed

The note makes two claims.

1. In the leave arm of the reviewed singleton source/repair affine-law
   dichotomy, the repaired-law atom transports back to the literal original
   source law with mass

   \[
   \mu_{\rm src}(A\cup\{e\})
     \ge {\Gamma^2\over 28M(\Gamma+2M)},
   \]

   while retaining the owner leave gain at least `Gamma/2`.

2. There is an exact rational Fin4 table with an original singleton source
   and its literal owner-Continue repair which simultaneously has both paid
   rows, the exact affine law bridge, source-law reset incidence and toggle,
   a common cap tail, and all-Continue as the unique exact product root at
   that tail.  The table has punishment values zero but also has an exact
   terminal equilibrium, so its global semantic-debt minimum is zero.

## 2. Quantitative leave-arm extraction: PASS

The checked source producer gives

\[
a\ge {\Gamma\over\Gamma+2M}>0,
\]

and the reviewed affine-law result supplies a nonempty repaired-law atom
with

\[
\mu_{\rm rep}(A)\ge {\Gamma\over28M}.
\]

For every nonempty free coalition, the exact source/repair identity is

\[
\mu_{\rm src}(A\cup\{e\})=a\mu_{\rm rep}(A).
\]

Multiplication gives precisely the displayed constant.  Positivity of the
denominators follows from the positive gap and the bounded-reward source
data.  The leave comparison is unchanged by this transport.  No conditioning
or extra survival factor is missing: the factor `a` is exactly the total
one-row free absorption probability which converts the normalized repaired
law back to the date-zero source law.

The note also correctly excludes the solo arm from this conclusion.  A
comparison with `r_e({e})` does not itself give a membership toggle on a
source-supported coalition.

## 3. Stationary semantic pairs and unrestricted caps: PASS

For the displayed reward table, `sigma` absorbs at date zero in `{0,1}` and
`tau` absorbs at date zero in `{1}`.  Direct calculation gives

\[
U(\sigma)=(0,0,0,0),\qquad B(\sigma)=(1,0,0,0),
\]

and

\[
U(\tau)=(1,-1,0,0),\qquad B(\tau)=(1,0,0,0).
\]

These are unrestricted behavioral caps.  At `sigma`, sure Quit by player 1
reduces every unilateral stopping law to the convex choice between joining
at date zero and arriving after absorption.  At `tau`, players 0, 2, and 3
are likewise solved immediately, while player 1's only better endpoint is
literal Never.  Thus the debt supports are exactly `{0}` and `{1}`.

The induced free point over base `{0}` is exact: player 1 is indifferent
between tying and leaving, and players 2 and 3 lose by joining.  Sure base
absorption makes these statements valid against arbitrary behavioral
deviations, not just stationary deviations.

## 4. Paid rows, laws, floors, and reset dispatch: PASS

The two paid rows have the stated orientations.

* On `sigma`, player 0 changes from date-zero Quit, receiving zero on
  `{0,1}`, to any later time or Never, receiving one on `{1}`.
* On `tau`, player 1 changes from date-zero Quit, receiving `-1` on `{1}`,
  to Never, receiving zero.  A later finite Quit would still receive `-1`,
  as the note explicitly records.

The complete laws are exactly

\[
\mu_{\rm src}=\delta_{\{0,1\}},\qquad
\mu_{\rm rep}=\delta_{\{1\}},
\]

so `a=1`, the affine bridge is literal, and `A={1}` carries the unit owner
leave gain on the original source law.

Player 2 has zero source debt and unit opponent incidence with player 0.
The source atom `{0,1}` contains player 0 and supports the strict member-leave
toggle

\[
r_0(\{0,1\})=0<1=r_0(\{1\}).
\]

Every punishment value is zero: Never guarantees zero, while opponents all
Never make the best of solo Quit and Never equal zero for player 0 and equal
zero for the other players as well.  Hence the common tail
`V=(1,0,0,0)` is floor safe, and the repaired player-1 coordinate is correctly
classified as the explicit under-floor arm.

Finally, the all-Never semantic pair is a literal carrier point with total
debt zero.  Taking it as `source` in `QuittingFixedLawResetDispatch`, taking
`Sem(sigma)` as both target and returned point, reset label 2, marked opponent
0, and law `mu_src`, verifies all structure fields: joint membership, reset,
the two aggregate debt inequalities, transfer, supported toggle, and the
all-Continue `dynamic_exit` arm.

## 5. Unique common all-Continue cap root: PASS

At tail `V`, player 0's Continue endpoint exceeds its Quit endpoint by one
at every pure opponent corner: at the empty corner this is `V_0=1` versus
the solo value zero, and at a nonempty corner it is the difference between
omitting and inserting player 0.

Therefore every exact product root has `q_0=0`.  Conditional on this, player
1 gets zero from Continue and `-1` from Quit at every opponent corner,
including the empty corner.  Players 2 and 3 have the same strict comparison
globally.  Hence every exact product root is all-Continue.  Conversely
all-Continue is exact, and its semantic prefix fixes either suffix pair.

This sequential argument is exhaustive even when two or more coordinates
initially have positive Quit rates; it does not assume the root is pure or
inspect only singleton deviations.

## 6. Novelty and subsumption audit

The local obstruction is close to, but not identical with, the earlier
`CODEX_MINER__FIN4_SINGLETON_BASE_ALLCONTINUE_RESET_WALL` regression.  That
result already showed that one actual stationary paid/reset law, a heavy
toggle atom, and a unique all-Continue cap root can coexist.  The genuine
delta here is the simultaneous realization of:

* the original source and its literal owner-Continue repair;
* their exact affine law relation;
* paid rows for both resulting debtors; and
* one common cap tail whose exact root is uniquely all-Continue.

The result also sharpens the interface discussion in
`CODEX_MINER__FIN4_MINIMAL_PASSPORT_DOUBLE_INERT_LAW_BRIDGE`: Proposition 2.1
places the favorable leave atom on the original retained law, and Proposition
3.1 shows that even this best-case alignment supplies no cap charge.

It does not supersede or close
`FinFourSingletonBaseResetRepairPaidCapDoublePort.sourceDescent_or_repairedDescent_or_doubleInert`.
The checked double-port object includes the ambient hard residual and a
positive global minimum; this regression deliberately does not.  Nor does it
produce an exact punishment-floor edge, a return, or a maintained rank
decrease.

Accordingly the precise conclusion is:

> the exposed local stationary source/repair, law, atom, paid-row, reset, and
> common-cap fields do not eliminate the double-inert plateau.  Any successful
> maintained theorem must use additional ambient positive-minimum/hard-
> residual provenance in an essential way.

This is a necessity statement, not a claim that positive minimum alone is
sufficient or that it is the only imaginable additional hypothesis.

## 7. Source audit and recommendation

I checked the claims against:

* `QuittingFixedLawResetDispatch` in
  `TerminalSemanticResetIncidenceCapReturn.lean`;
* `FinFourSingletonBaseSameLawResetProducer` in
  `SingletonBaseSameLawResetProducer.lean`;
* `FinFourSingletonBaseResetRepairPaidCapDoublePort` and
  `sourceDescent_or_repairedDescent_or_doubleInert` in
  `SingletonBaseResetRepairPaidCapDoublePort.lean`; and
* the endpoint dispatch
  `QuittingFixedLawResetDispatch.endpointRoot_or_literalDefect_or_stall` in
  `PairBasePaidResetEndpointSeam.lean`.

**Recommendation:** retain the note internally as an exact boundary and
regression target.  It fails the current export significance/consumer gate:
it eliminates no maintained chamber and decreases no accepted complexity.
Its value is to prevent further attempts to convert a suffix-law owner-leave
atom into cap absorption without genuinely using the ambient positive-minimum
provenance.

