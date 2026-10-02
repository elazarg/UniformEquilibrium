# Fin4 late-release rectangles: a sharp three-label dispatch and support-rotation boundary

Author: `CODEX_MINER`

Status: **proved ordinary mathematics; independently reviewed PASS; internal
only.**  Review:
[`CODEX_EULER`](../feedback/CODEX_MINER__FIN4_LATE_RELEASE_RECTANGLE_THREE_LABEL_BOUNDARY__BY_CODEX_EULER.md).
The positive theorem below sharpens the generic endpoint-atom decoder
for the finite-support late release produced in
[`CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md`](CODEX_MINER__FIN4_POSITIVE_NEVER_LATE_RELEASE_CHRONOLOGY.md).
It removes the generic `16`-outcome loss and restricts the cap-side witness to
three terminal labels.  The exact rational Fin4 regression then shows that
even this sharpened, source-matched rectangle need not be an exact root, a
payoff near-return, or a no-new-support minimum-fiber replacement.  The
regression has global debt minimum zero, so it does not refute a theorem that
uses the full positive-global-minimum/hard-residual hypotheses again after
the packet is formed.

## 1. Question

The reviewed positive-Never packet gives, on one literal source chronology,

```text
deep exact cap--Nash prefix
  -> retained early finite atom
  -> late singleton release by a
  -> fixed gain and own-debt drop
  -> fixed recipient b with positive debt rise
  -> prescribed atom or same-deviation rectangle.
```

Can the final decoded atom be fed directly to one of the checked consumers:

1. a punishment-floor exact Nash--Bellman edge or cumulative payoff
   near-return;
2. a minimum-fiber full replacement with no new debt support; or
3. terminal approximate-Nash profiles?

The finite-support provenance yields a useful new localization, but none of
these three conclusions follows from the packet fields alone.

## 2. Exact finite data for a late release

Let `I` be finite and fix distinct players `a,b`.  A literal source consists
of a finite common root word `R`, followed by independent suffix clocks
`T_i` supported on dates `<K` and `Never`.  Let `P` be that profile.  Choose
`N>=K` and form `Q` by changing only `a`: it keeps the same live hazards
before suffix date `N`, Quits surely at `N`, and Continues afterwards.

Write

```text
q = Pr_P(all players survive R and every suffix clock is Never),
Delta = d_b(Q)-d_b(P).
```

Suppose `q>0` and `Delta>0`.  Let

```text
u = r_b({a}),
v = r_b({b}),
w = r_b({a,b}).
```

When `b` is overwritten by a pure stopping time, let `r>0` be the probability
that every opponent of `b` survives the root word, `a`'s source suffix clock
is Never, and every suffix clock other than those of `a,b` is Never.  Thus
`q` is `r` times the probability that prescribed `b` also survives the root
word and has suffix clock Never.  In particular `q<=r`.

## 3. Sharp late-release recipient dispatch

### Theorem 3.1

Under Section 2, at least one of the following two branches can be selected
(choose the first at equality).

#### Prescribed-loss branch

```text
Delta/2 <= -q*u.                                    (3.1)
```

The source-minus-target payoff-difference atom for observer `b` is supported
on `{a}` and is exactly

```text
(Law(P)({a})-Law(Q)({a}))*r_b({a}) = -q*u.          (3.2)
```

Thus the generic prescribed alternative has no outcome-cardinality loss and
its label is forced to be `{a}`.

#### Cap-response branch

There is an unrestricted best response of `b` attained by one pure stopping
time `tau` against `Q`, with `tau` at or after the release, such that

```text
Delta/2 < U_b(Q[b<-tau])-U_b(P[b<-tau]).             (3.3)
```

Moreover precisely one of the following timing formulas applies:

```text
tau=N:              difference = r*(w-v),           (3.4a)
N<tau<Never:        difference = r*(u-v),           (3.4b)
tau=Never:          difference = r*u.               (3.4c)
```

In (3.4a) the two changed terminal labels are `{a,b}` and `{b}`; in
(3.4b) they are `{a}` and `{b}`; in (3.4c) the only nonzero-reward changed
label is `{a}` (the other outcome is `Never`).  Hence the same-deviation
endpoint payoff difference used by the checked rectangle decoder is carried
by at most two nonzero terminal atoms, and one atom has the correct sign and
magnitude strictly greater than `Delta/4`.  This replaces the
generic `Delta/(4*card Outcome)` scale by `Delta/4` and fixes the possible
labels to

```text
{a}, {b}, {a,b}.                                    (3.5)
```

### Proof

The prescribed payoff change of `b` is exactly

```text
U_b(Q)-U_b(P)=q*u.                                  (3.6)
```

Changing only `a` leaves `b`'s prescribed strategy fixed, so

```text
Delta = [B_b(Q)-B_b(P)]-q*u.                        (3.7)
```

If (3.1) holds, (3.2) is immediate: source and target laws differ only by
moving the joint-`Never` mass `q` to singleton `{a}`.

Otherwise `-q*u<Delta/2`.  Equation (3.7) gives

```text
B_b(Q)-B_b(P)=Delta+q*u>Delta/2.                    (3.8)
```

Against either profile, pure-time payoff is eventually constant: all root
dates are finite, all finite suffix atoms lie before `K`, and `a`'s target
clock is capped at `N`.  The checked equality between the unrestricted
behavioral cap and the supremum over pure times and `Never` therefore becomes
a maximum over a finite list.  Choose `tau` attaining `B_b(Q)`.  Then

```text
U_b(Q[b<-tau])-U_b(P[b<-tau])
  >= B_b(Q)-B_b(P)>Delta/2.                         (3.9)
```

The chosen time cannot precede the release: source and target agree there,
whereas the right side of (3.9) is positive.  On the event of probability
`r`, the source has no opponent exit and the target changes only `a`'s
`Never` clock to date `N`.  At `tau=N` the outcomes are `{b}` and `{a,b}`;
after `N` they are `{b}` and `{a}`; at `Never` they are `Never` and `{a}`.
Off that event the outcomes agree.  This proves (3.4a)--(3.4c).  At most two
terminal atoms sum to a number greater than `Delta/2`, so one is greater than
`Delta/4`. `QED`

### Corollary 3.2 (cofinal-source preservation)

The theorem applies after every common root word in the reviewed late-release
chronology.  In the cap-response branch `b`'s maximizing pure time cannot lie
inside the common prefix because the endpoint profiles are identical there.
All prefix, suffix, cutoff, and pure-time data remain attached to the same
literal source.  Passing to a fixed recipient/timing-case/terminal-label
subsequence preserves the cofinal exact cap--Nash depth.  Under the repaired
upstream reindexing convention, write `ell_n` for the actual root-word length;
then `ell_n>=n+1`, and all shifted stage labels use `ell_n`.  Equivalently one
may retain the original indices on an infinite cofinal set.

This is a genuine strengthening of
`HasQuittingEndpointDebtRecipientAtom`: it uses the finite-support cutoff and
the specific `Never -> {a}` move, not merely a positive semantic debt chord.

### Corollary 3.3 (constants for the reviewed Fin4 packet)

For the fixed recipient in the reviewed positive-Never chronology,

```text
Delta >= Gamma*q_min/24,
```

where `q_min` is the positive Never coordinate of the supplied minimum law.
Theorem 3.1 therefore gives either

```text
prescribed `{a}` atom >= Gamma*q_min/48,
```

or a same-deviation atom on one of `{a}`, `{b}`, `{a,b}` strictly larger
than

```text
Gamma*q_min/96.                                     (3.10)
```

The earlier generic decoder guaranteed only `Gamma*q_min/768` and
`Gamma*q_min/1536`, respectively.  The improvement is not a consumer, but it
shows that the remaining obstruction is label/edge compatibility rather than
atom magnitude.

## 4. Exact rational Fin4 regression

The next table realizes the cap-response collision case with every piece of
the strengthened chronology, yet the best-response corner rotates debt
support instead of shrinking it.

Use players `a,b,c,d`.  Rewards not listed below are zero, except for the
punishment rows specified at the end:

```text
r_a({a})       = 1,
r_a({a,b})     = 8,

r_b({a,b})     = 3/4,

r_c({b,c})     = -55/72,
r_c({a,b,c})   = 55/24.
                                                        (4.1)
```

For each `i in {a,b,c}`, also put

```text
r_i({d})=r_i({i,d})=-100,                            (4.2)
```

and let every reward of `d` be zero.  The rows in (4.2) are never reached by
the displayed profiles; they only make punishment-floor safety literal.

At suffix date zero let

```text
a Quit with probability 1/4,
b Quit with probability 1/2,
c,d play Never,
```

and after date zero let every surviving player play Never.  Call this source
`P`.  Its terminal law is

```text
Law_P({a,b})=1/8,  Law_P({a})=1/8,
Law_P({b})=3/8,    Law_P(Never)=3/8.                 (4.3)
```

Thus `{b}` is an early atom of mass `3/8` and the joint-`Never` mass is
`q=3/8`.

Cap `a` at suffix date one, keeping its date-zero hazard.  Call the target
`Q`.  It changes precisely the old joint-`Never` event into singleton `{a}`
at date one, so

```text
Law_Q({a,b})=1/8,  Law_Q({a})=1/2,
Law_Q({b})=3/8.                                     (4.4)
```

## 5. Exact semantic account

Pure-time extremality and the finite displayed clocks give

```text
U(P)=(9/8, 3/32, 0, 0),
B(P)=(9/2, 3/16, 0, 0),
d(P)=(27/8, 3/32, 0, 0),
D(P)=111/32.                                        (5.1)
```

For `c`, immediate Quit has expected payoff

```text
(1/8)*(55/24)+(3/8)*(-55/72)=0,                    (5.2)
```

and every later pure time and `Never` also pay zero.  This verifies its zero
cap in (5.1), including unrestricted behavioral deviations.

At `Q`, player `a` gains exactly `3/8`; its cap is unchanged.  Player `b`'s
best response is to Quit at date one and collide with `a` on the late branch.
Consequently

```text
U(Q)=(3/2, 3/32, 0, 0),
B(Q)=(9/2, 9/16, 0, 0),
d(Q)=(3, 15/32, 0, 0),
D(Q)=111/32.                                        (5.3)
```

Thus the late release has all the quantitative transfer identities

```text
gain_a=3/8,
d_a(P)-d_a(Q)=3/8,
d_b(Q)-d_b(P)=3/8.                                  (5.4)
```

For every depth `L`, prefix both profiles by `L` literal all-Continue roots.
These roots are exact cap--Nash roots against the successive actual caps;
they have zero absorption and change no semantic coordinate.  The early
`{b}` atom remains at stage `L` with mass `3/8`, while the new `{a}` atom
lies at stage `L+1` with mass `3/8`.  Hence the exact source and cofinal stack
provenance are present without asymptotic loss.

In fact this particular source satisfies

```text
r_a({a})=1<9/8=U_a(P),
r_b({b})=0<3/32=U_b(P),
r_c({c})=U_c(P)=0,
r_d({d})=U_d(P)=0.
```

Therefore the same all-Continue roots are also exact Nash--Bellman roots
against the prescribed tail payoff, and Section 7 shows that tail is
punishment-floor safe.  The cofinal word is thus a literal exact admissible
path, but every one of its charges is zero.

## 6. The forced decoded rectangle and exact support rotation

Let `Y` replace `b` in `P` by sure Quit at suffix date one, and let `Z`
make the same replacement in `Q`.  Then

```text
Law_Y({a})=1/4,     Law_Y({b})=3/4,
Law_Z({a})=1/4,     Law_Z({a,b})=3/4.                (6.1)
```

The prescribed source-to-target payoff difference for `b` is zero because
`r_b({a})=0`; every prescribed payoff-difference atom is zero.  The decoder
is therefore forced into its rectangle branch.  Its full rectangle and its
unique positive terminal atom are

```text
U_b(Z)-U_b(Y)-U_b(Q)+U_b(P)=9/16,
(Law_Z({a,b})-Law_Y({a,b}))*r_b({a,b})=9/16.         (6.2)
```

The recipient charge is `Delta=3/8`, so this is the `tau=N` case of Theorem
3.1 with a much larger margin than the generic decoder requires.  The same
pure time attains `B_b(Q)`, and hence

```text
d_b(Z)=0.                                           (6.3)
```

In particular the literal checked interface is satisfied: `Delta>0`, and
with `card (QuittingTerminalOutcome (Fin 4))=16`,

```text
Delta/4=3/32 <= 16*(9/16).
```

Thus this is not merely a positive four-corner scalar; it is an explicit
`HasQuittingEndpointDebtRecipientAtom` rectangle witness on the exact
source--target edge.

However the replacement activates player `c`.  At `Z`, quitting at date one
joins the late pair `{a,b}` and pays `55/24` on its probability-`3/4`
branch.  Equation (5.2) ensured that this cap was zero at both `P` and `Q`.
Directly,

```text
U(Z)=(25/4, 9/16, 0, 0),
d(Z)=(7/4, 0, 55/32, 0),
D(Z)=111/32.                                        (6.4)
```

Therefore

```text
supp+(d(P))=supp+(d(Q))={a,b},
supp+(d(Z))={a,c}.                                  (6.5)
```

All three displayed total debts are equal, but the exact recipient best
response replaces debtor `b` by a new debtor `c`.  It does not produce the
`no new support` premise of
`positiveDebtSupport_ssubset_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber`.

## 7. Floor, edge, return, and approximation audit

The displayed prescribed payoff vectors are punishment-floor safe.  To
punish any `i in {a,b,c}`, have opponent `d` Quit surely at date zero while
the other opponents Continue.  Both Continue and joining by `i` pay `-100`,
so its punishment value is at most `-100`.  Player `d` has punishment value
zero.  Thus floor failure is not the obstruction.

The late singleton row `{a}` is not an exact Nash root: `b` gains `3/4` by
joining it.  The resulting pair row `{a,b}` is also not an exact Nash root:
`c` gains `55/24` by joining it.  Thus neither positive row is a checked
punishment-floor Nash--Bellman edge, despite the floor-safe endpoint payoffs.

The cofinal source roots are all Continue and have cumulative absorption
zero.  The source-to-release payoff displacement in coordinate `a` is the
fixed number `3/8`, not an arbitrarily small seam.  Hence this displayed
chronology is not a
`QuittingPositiveCumulativeAdmissiblePayoffNearReturnFamily`.  Finally the
three semantic debts in (5.1), (5.3), and (6.4) stay at `111/32`; none of the
displayed sequences is a terminal approximate-Nash sequence.

This table is intentionally not a counterexample.  For example the pure
terminal profile `{a,b,c}` has zero debt under the unspecified-zero rows in
(4.1), so the global terminal-semantic debt minimum is zero.  The regression
therefore proves the following exact boundary and no more:

> The full post-minimum output of the reviewed late-release packet—literal
> cofinal cap--Nash source stacks, ordered positive atoms, exact gain and
> transfer, the sharpened same-source rectangle, a best-response endpoint,
> equal displayed total debt, and floor-safe payoffs—does not by itself imply
> an exact Bellman edge, near-return, or no-new-support regeneration.

A positive theorem must use the ambient positive global minimum or another
hard-residual field **again after** the rectangle is formed, to rule out the
support entry exhibited in (6.5) or to consume it.  Reusing only the minimum
transfer inequality is insufficient: (5.4) saturates that transfer and all
three displayed total debts are equal.

## 8. Source and duplicate audit

Checked declarations inspected:

- `HasQuittingEndpointDebtRecipientAtom` and
  `hasQuittingEndpointDebtRecipientAtom_of_pos` in
  `TerminalSemanticCausalCollisionRecipientAtom.lean`;
- `sSup_range_quittingTerminalPayoff_update_eq_pureTime` in
  `BehaviorPureTimeExtremality.lean`;
- the exact pure-time rectangle disintegration and causal stage results in
  `TerminalSemanticPureTimeRectangleDisintegration.lean`;
- `minimumReference_opponentTransfer_of_coordinateDecrease` in
  `TerminalSemanticPlateauPartialResetTransfer.lean`;
- `positiveDebtSupport_ssubset_of_exactDiagonal_of_flat_of_noEntry_of_minimumFiber`
  in `StoppingLaw/Endpoint/MinimumFiberSupportDrop.lean`; and
- the cumulative payoff-near-return consumer in
  `Quitting/Projective/CumulativeChargeNearReturn.lean`.

Closest internal no-go results:

- `CODEX_RAMSEY__RETAINED_RECTANGLE_PLATEAU_CAP_COMPATIBILITY_BARRIER.md`
  shows that a complete response square need not be cap-Nash compatible, but
  it does not retain positive joint Never, the exact late-release law, the
  cofinal source stack, or the three-label formula.
- `CHATGPT_EXTERNAL__FIN4_INERT_PAID_MASS_RECTANGLE.md` gives a stronger
  six-state local best-response cycle, but not this positive-Never
  early-atom/late-singleton chronology.
- `CODEX_EULER__FIN4_INERT_PAID_ROW_FULL_REACH_NONCONVERSION.md` keeps a paid
  row through an inert cap stack, but has neither a positive recipient debt
  transfer nor the exact best-response rectangle/support rotation.

No current declaration gives (3.1)--(3.5).  This sharp dispatch is a
standalone Research formalization candidate.  It is not exportable without a
consumer.

## 9. Exact next question

In the genuine Fin4 hard residual, apply Theorem 3.1 along the reviewed
positive-Never packet.  Can the maintained support-entry consumer accept the
new debtor created by the exact recipient best response, while retaining the
same minimum-law source and the cofinal cap stack?  Equivalently, can global
minimality force the support-entry corner back to the minimum fiber without
losing its late label in `{a},{b},{a,b}`?  The regression shows that this
cannot be proved from equal local debt and floor safety alone.

## Review request

Please check the two-arm inequality (3.7)--(3.9), pure-time attainment and
the three timing formulas, the claimed `Delta/4` atom scale, every rational
cap/debt calculation in (5.1)--(6.4), the punishment-floor construction, and
the exact scope of the zero-global-minimum regression.
