# Review of Proposition 5 in `CODEX_CEDAR__FOUR_PLAYER_CONJECTURE_CAPSTONE`

Reviewer: `CODEX_RAMSEY`

## Verdict

**REVISE → PASS.**  The mathematics, constants, floor safety, and exact
threshold construction are valid.  One statement-level hypothesis must be
written literally before the proposition is reused:

```text
X_n in quittingTerminalSemanticCarrier reward,
IsεQuittingRootNash reward X_n.1 0 q_n.
```

The prose “carrier tails and exact roots” has this intended meaning and the
proof uses it repeatedly, but (8.1)--(8.2) currently do not display the root's
tail.  With this explicit line, I found no mathematical objection.

## Debt-drop and solo extraction

Let `X'_n=Prefix(q_n,X_n)`.  Carrier debt is coordinatewise nonnegative.  The
checked summed drift/defect account gives

```text
sum_j O_j(q_n)d_j(X_n)
  <= D(X_n)-D(X'_n)+Def(X_n.1,q_n)=Delta_n,
```

where the last equality uses the exact-root hypothesis.  Exact prefixing also
makes each coordinate drift nonnegative.

Every collision event contains an opponent of every player, so
`O_j(q_n)>=collision(q_n)` for all `j`.  Since `D(X_n)>=D_*>0`,

```text
D_* collision(q_n)<=Delta_n.
```

Thus collision tends to zero.  The exact decomposition

```text
absorption = collision + sum_k mass({k})
```

and `absorption>=a` show that, eventually, the singleton sum is at least
`a/2`; one of four singleton masses is at least `a/8`.  Finite pigeonhole
selects one fixed owner `k` on a subsequence.

Compactness of the carrier and product-root cube gives a limit `(X,q)`.  Its
`{k}` mass is at least `a/8` and its collision mass is zero.  Two positive
Quit marginals would give positive collision probability, so every marginal
other than `k` is zero.  Hence `q` is the solo root with hazard
`p=mass_q({k})>=a/8`.

For `j!=k`, apply the coordinate coalition charge to `{k}` with `other=k`:

```text
mass_qn({k}) d_j(X_n)
 <= d_j(X_n)-d_j(X'_n).
```

The right-hand coordinate drifts are nonnegative and their sum is at most
`Delta_n`.  The uniform singleton lower bound therefore sends every
complementary debt to zero.  Closed carrier membership gives
`D(X)>=D_*>0`, so `k` carries all limiting debt.

## Marginal constants and owner equality

Exact Nash is closed under the joint tail/root limit.  Each prescribed tail
is in the terminal payoff box and is above the behavioral punishment floor.
The checked terminal-gap marginal cap therefore gives

```text
p <= 1-Gamma/(4M).
```

Together with `p>=a/8`, this makes both owner actions genuinely supported.
At a solo root the owner's forced-Quit endpoint is `s_k` and its
forced-Continue endpoint is `X.1_k`; exact mixing gives `X.1_k=s_k`.

As a useful scope consequence, this limit cannot itself be a global minimum
pair: reviewed Proposition 4 makes every minimum prescribed coordinate
strictly exceed its singleton payoff.  Proposition 5 is therefore genuinely
an off-minimum gate, consistent with the debt moat.

## Normal blocker and threshold

If the same positive-hazard solo root were exact at the solo reward vector
`r_k`, then
`isUniformEquilibriumPayoff_soloReward_of_endpointNash_of_punishmentIR`
would apply because all-player normality gives `P_k<=s_k`.  This contradicts
the no-uniform branch.  The owner is automatically indifferent at `r_k`, so
failure of exactness is witnessed by a distinct outsider `i` whose immediate
Quit value exceeds its Continue/Never value:

```text
R_i=r_k(i) < Q_i=(1-p)s_i+p r_{ki}(i).
```

Exactness at `X.1`, with `i` purely Continue, gives

```text
Q_i <= p R_i+(1-p)X.1_i.
```

Since `p<1`, the threshold

```text
T_i=(Q_i-pR_i)/(1-p)
```

satisfies `T_i<=X.1_i`, while

```text
T_i-Q_i=p(Q_i-R_i)/(1-p)>0.
```

Against the positive solo hazard, `i`'s unrestricted stationary cap is
exactly `max(Q_i,R_i)=Q_i`; the checked punishment upper leg gives
`P_i<=Q_i`.  Hence

```text
P_i<=Q_i<T_i<=X.1_i.
```

All quantities remain in the reward box: `Q_i` is a convex combination of
reward entries, `T_i>Q_i>=-M`, and `T_i<=X.1_i<=M`.

## Coordinate replacement and scope

A root endpoint condition for player `j` depends on the declared tail only
through coordinate `j`.  Replacing only `X.1_i` by `T_i` leaves every other
condition unchanged.  For `i`,

```text
pR_i+(1-p)T_i=Q_i,
```

so its pure-Continue condition becomes exact equality.  The new tail is
boxed and floor-safe, and the same solo root remains exact with absorption
`p>=a/8`.

The stated dichotomy is consequently correct: a fixed-charge family either
has a subsequence with macroscopic debt drop or a vanishing-drop subsequence
with this two-label activation gate.  The blocker still plays Continue, and
nothing here selects a nearby two-active root, produces a return, or closes
the equilibrium correspondence jump.  Those nonclaims are essential and
correct.
