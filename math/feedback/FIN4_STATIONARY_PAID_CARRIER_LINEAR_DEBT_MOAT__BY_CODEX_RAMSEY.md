# Whole-packet gate: `FIN4_STATIONARY_PAID_CARRIER_LINEAR_DEBT_MOAT`

Reviewer: `CODEX_RAMSEY`

## Verdict

**REVISE -> PASS after one literal proof-reference repair.**

The statement, mathematics, actual-data adapter, probability semantics,
boundary tests, source audit, Lean handoff, and nonclaims all pass.  There is
one bounded proof-writing defect in Step 3: replace the invocation of `(8)` at
an arbitrary admitted path node by an invocation of `(13)` together with the
Fin4 defect bound.  Equation `(8)` is stated only for prescribed coordinates
of carrier pairs, whereas intermediate payoff nodes of the successor path are
not asserted to be carrier coordinates.  The required estimate is already
available, without any new lemma, because `(13)` is explicitly quantified over
every payoff vector in `N`.

After this replacement, I recommend **PASS** with no further review.

## Exact statement and stationary source

The packet is literally specialized to `Fin 4`, fixes a reward-coordinate
bound `M>=0`, assumes no uniform-equilibrium payoff, and fixes the terminal
gap and four distinct labels needed by the reviewed Section 16 construction.
The constrained binary Nash selection is exhaustive:

```text
Delta_c(1)<=0,
Delta_c(1)>0 and Delta_t(1)>=0,
Delta_c(1)>0 and Delta_t(1)<0.
```

The resulting roots in the three cases are respectively the appropriate pure
corner, the opposite pure corner, or the two affine interior zeros.  The sign
at zero and the bound on a Quit-minus-Continue payoff difference yield

```text
y >= gamma/(gamma+2M).
```

Independence gives the exact split between `{s,t}` and `{c,s,t}`, so one of
those atoms has mass at least `alpha/2`.  The sure Quit of `s` reduces every
unilateral behavioral deviation of `c,t` to its date-zero action marginal;
hence `B_c=U_c` and `B_t=U_t` are unrestricted-cap equalities, not merely
stationary regret statements.  The checked punishment inequality supplies
their floors.  Terminal exploitability then localizes a debtor to `{s,o}`.
The packet correctly records the required rewrite
`quittingTerminalSemanticPair_stationary_envelope_eq_cap` before applying the
oriented immediate-Quit/Never paid-row decoder.

## Compact carrier moat and factor four

The minimum carrier fiber is compact and nonempty, and its continuous
prescribed-payoff image `K` is compact.  The checked Fin4 isolation theorem
supplies a common positive singleton gap and all-Continue uniqueness on all of
`K`.  Applying the reviewed abstract linear theorem therefore gives an open
bounded `N`, `c_*>0`, and the payoff/reward bound `C>0` with

```text
c_* absorption(r) <= totalRootNashDefect(V,r)
```

for every `V in N`, not merely carrier tails.

The carrier complement

```text
Carrier intersect fst^(-1)(N^c)
```

is compact and disjoint from the entire minimum fiber.  Its minimum debt is
strictly above `D_*`; the displayed half-gap `eta_*` gives the stated weak
alternative, including equality at the off-minimum threshold.  If the
complement is empty, the arbitrary positive choice `eta_*=1` is harmless.

For `Fin 4`, the checked coordinatewise epsilon-root estimate is exactly

```text
totalRootNashDefect <= 4 epsilon,
```

so the packet's `4 epsilon/c_*` bound is correct.  At epsilon zero,
absorption zero forces every independent Boolean Quit marginal to vanish;
the successor is the tail and the edge charge is zero.

## Literal tail, floor, and Bellman orientation

The stationary semantic pair `X_sigma=(U,B)` is an actual carrier point.  The
root alternative is tested against its literal prescribed tail `U`.  Thus a
charged exact edge at that continuation tail forces the off-minimum arm.  If
`U` dominates punishment, all-Continue produces the only exact admissible
identity edge; if `U` does not dominate punishment, it cannot be the tail
state of a floor-admissible edge.  The packet correctly refuses to replace
`U` by the unrestricted cap `B` or by a floor clip.

The successor-linked convention in Part C is also consistent:

```text
V_t = Succ(V_(t+1),r_t),
```

with `r_t` tested at continuation tail `V_(t+1)`.  Backward induction starts
from `V_L` near `K`.  Specializing the reviewed general constants to four
players gives

```text
E < c_*rho/(16C),
sum absorption <= 4E/c_*,
max displacement <= 8CE/c_* < rho/2.
```

No path length enters these estimates.

### Required local repair

The first sentence of Proof Step 3 currently says:

```text
Once V_(t+1),...,V_L have been admitted, (8) ...
```

But `(8)` is the carrier-pair alternative.  Replace it by, for example:

```text
Once V_(t+1),...,V_L have been admitted, (13) and
totalRootNashDefect(V_(t+1),r_t)<=4 epsilon_t give
absorption(r_t)<=4 epsilon_t/c_*.
```

This is the exact proof already intended elsewhere in the packet and removes
the only quantifier mismatch.

## Actual-data adapter and downstream narrowing

The source chain is explicit and same-table:

1. the checked rooted-two owner-leave/third-label-join arm;
2. the reviewed `FIN4_LEAVE_JOIN_STATIONARY_TWO_DEBTOR_HANDOFF` stationary
   source; and
3. the checked whole-minimum-fiber isolation plus reviewed linear-defect
   theorem.

The output strictly narrows the live
`PAID_ADMISSIBLE_PAYOFF_NEAR_RETURN` producer: a charged exactification at the
literal paid tail is possible only in the semantic debt-moat arm, and a path
ending near the minimum fiber cannot hide fixed absorption under vanishing
aggregate root error.  It does not claim that this off-minimum arm is produced
with the floors, root, or return needed by the consumer.

## Boundary, source, and subsumption audit

All five boundary tests are relevant and correct:

- the one-player example realizes the linear defect scale;
- the two-player `1/5` root shows uniqueness is indispensable;
- the fourth coordinate can remain floor-unsafe independently of the solved
  pair;
- a head may lie in `N` while its continuation tail lies outside it; and
- small maximum row error does not replace small aggregate error.

The source audit is honest.  The exact carrier-tail moat is mostly a
composition/rederivation of checked minimum-fiber isolation.  The new packet
content is its alignment with the accepted stationary paid carrier and the
approximate-root/successor-path quantitative strengthening.  No literature
claim is invoked.

The Lean handoff names the correct existing carrier definitions and keeps the
linear theorem as an ordinary-mathematics dependency to formalize.  It does
not place the desired alternative into a source structure.  The listed
nonclaims accurately exclude root production, floor repair, clipping,
descent, conditioned incidence, cyclic return, and uniform payoff.

## Gate checklist

1. Self-contained finite statement and quantifiers: **PASS**.
2. Complete proof: **PASS after the one reference repair above**.
3. Probability/all-behavior audit: **PASS**.
4. Actual-data adapter and named live consumer: **PASS**.
5. Positive/negative boundaries: **PASS**.
6. Source and novelty/subsumption audit: **PASS**.
7. Independent substantive theorem review: **PASS**.
8. Lean handoff without assumed producer fields: **PASS**.
